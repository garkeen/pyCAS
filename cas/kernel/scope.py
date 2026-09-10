# -*- coding: utf-8 -*-
"""作用域树（v4 §6.2）：持久化、带父指针、不可变。

作用域是**上下文**的权威，不是计算的权威——计算不经过它。它只回答：
某个符号在此处如何绑定、有哪些假设可见、局部符号能否逃逸。

结构自始不可变（`Scope` 为 frozen dataclass），改动用新 Scope 表达，故
阶段5 换掉 v3 可变 `Context` 后端时不触及任何消费者。
"""

from dataclasses import dataclass, replace

from cas.kernel.ids import ScopeId
from cas.kernel.model import Assumption, Declaration, Definition


@dataclass(frozen=True, slots=True)
class Scope:
    """持久化作用域（v4 §6.2）：不可变，子作用域带父指针，改动用新 Scope 表达。"""
    id: ScopeId
    parent: ScopeId | None = None
    declarations: tuple[Declaration, ...] = ()
    definitions: tuple[Definition, ...] = ()
    assumptions: tuple[Assumption, ...] = ()


@dataclass(frozen=True, slots=True)
class Assumptions:
    """不可变假设集（v4 §6.2：Scope 链上假设的只读投影）。

    取代 v3 的可变 `Context`：原先的 `clone` + `assume` 变成本对象的 `extended`，
    临时扩充不产生可变状态，也不需要 marks/rollback（那些是为「可变上下文 + 位置
    指针撤销」服务的，持久化 Scope 树不需要）。

    假设的**权威来源是 Scope**（持久化、带父指针）；本对象只是判定层消费的投影，
    不参与记账。所以「撤销」由 revision 指针而非 rollback 完成（§8.9）。
    """
    items: tuple = ()

    @classmethod
    def of(cls, store, scope_id):
        return cls(tuple(a.proposition for a in store.assumptions(scope_id)))

    def extended(self, *terms):
        return Assumptions(self.items + tuple(terms))

    def __iter__(self):
        return iter(self.items)

    def __len__(self):
        return len(self.items)

    def __bool__(self):
        return bool(self.items)


class ScopeStore:
    """作用域存储：发放 id、维护父子树、提供可见性查询。"""

    def __init__(self):
        self._scopes: dict[ScopeId, Scope] = {}
        self._next = 0

    # --- 构造 ---

    def create(self, parent=None, declarations=(), definitions=(),
               assumptions=()) -> Scope:
        if parent is not None and parent not in self._scopes:
            raise KeyError(f"父作用域不存在: {parent}")
        sid = ScopeId(self._next)
        self._next += 1
        s = Scope(id=sid, parent=parent,
                  declarations=tuple(declarations),
                  definitions=tuple(definitions),
                  assumptions=tuple(assumptions))
        self._scopes[sid] = s
        return s

    def child(self, parent: Scope, declarations=(), definitions=(),
              assumptions=()) -> Scope:
        return self.create(parent=parent.id, declarations=declarations,
                           definitions=definitions, assumptions=assumptions)

    def extend(self, scope: Scope, declarations=(), definitions=(),
               assumptions=()) -> Scope:
        """在 scope 之上追加条目，返回**新** Scope（不可变，不就地修改）。"""
        s = replace(scope,
                    declarations=scope.declarations + tuple(declarations),
                    definitions=scope.definitions + tuple(definitions),
                    assumptions=scope.assumptions + tuple(assumptions))
        self._scopes[s.id] = s
        return s

    def get(self, sid: ScopeId) -> Scope:
        return self._scopes[sid]

    # --- 可见性 ---

    def chain(self, sid: ScopeId):
        """自根至本作用域的作用域链。"""
        out = []
        cur = self._scopes[sid]
        while True:
            out.append(cur)
            if cur.parent is None:
                break
            cur = self._scopes[cur.parent]
        return tuple(reversed(out))

    def is_visible(self, ancestor: ScopeId, descendant: ScopeId) -> bool:
        """descendant 是否在 ancestor 之内（含自身）——子作用域结论不得反向
        在父作用域使用（v4 不变量 8）；兄弟分支互不可见（不变量 9）。"""
        return any(s.id == ancestor for s in self.chain(descendant))

    # --- 条目查询 ---

    def declarations(self, sid: ScopeId) -> tuple[Declaration, ...]:
        out = []
        for s in self.chain(sid):
            out.extend(s.declarations)
        return tuple(out)

    def assumptions(self, sid: ScopeId) -> tuple[Assumption, ...]:
        out = []
        for s in self.chain(sid):
            out.extend(s.assumptions)
        return tuple(out)

    def definition_map(self, sid: ScopeId) -> dict:
        """可见定义表：内层覆盖外层。"""
        m = {}
        for s in self.chain(sid):
            for d in s.definitions:
                m[d.symbol] = d.body
        return m

    def lookup_definition(self, sid: ScopeId, symbol):
        return self.definition_map(sid).get(symbol)

    # --- 卫生检查 ---

    def local_symbols(self, sid: ScopeId) -> tuple:
        """本作用域（不含祖先）引入的符号：声明 + 定义左端。"""
        s = self._scopes[sid]
        return tuple([d.symbol for d in s.declarations]
                     + [d.symbol for d in s.definitions])

    def introducers(self, symbol) -> tuple:
        """哪些作用域把该符号作为局部符号引入（声明或定义左端）。"""
        out = []
        for s in self._scopes.values():
            if any(d.symbol is symbol for d in s.declarations) \
                    or any(d.symbol is symbol for d in s.definitions):
                out.append(s.id)
        return tuple(out)

    def escapes(self, sid: ScopeId, term) -> tuple:
        """term 里**逃逸**的局部符号（v4 不变量 15 / §6.2）。

        判据：某自由符号被**不在 sid 祖先链上**的作用域引入，且链上无人引入它。
        在 sid 或其祖先里引入的符号是可见的，不算逃逸（同一符号在链上被遮蔽时
        以外层为准，故只要链上出现过即视为可见）。

        为什么需要它：局部定义（`u := x²`）与被引入的辅助符号只在其作用域内有义，
        一旦出现在父作用域结论里，父作用域的读者会引用一个无定义的符号。
        """
        from cas.syntax.termpath import free_vars
        fv = free_vars(term)
        if not fv:
            return ()
        chain = {s.id for s in self.chain(sid)}
        bad = []
        for f in fv:
            owners = set(self.introducers(f))
            if owners and not (owners & chain):
                bad.append(f)
        return tuple(bad)
