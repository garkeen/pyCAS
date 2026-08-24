# -*- coding: utf-8 -*-
"""命令分发与转录 DSL（自 cas/session.py 拆出）：handle/_dispatch 分发、
命令帮助表、转录保存/回放（回放与 REPL 走同一 handle 路径）。

Mixin：依赖 SessionBase 状态与 kernel/solver 注册表；组装见 cas/session.py。
"""

from cas import term as T
from cas.parser import parse
from cas.pprint import to_str
from cas.errors import BudgetExceeded, ParseError
from cas import loader


class DispatchMixin:
    # ---------------- 转录 DSL（计算可复现/可保存/可回放） ----------------

    # 只读命令不入转录；变更类命令（:rule/:value/:refine/:assume 等）必须入录，
    # 否则回放无法重建推导（转录即 DSL 立场）。
    _NO_RECORD = {":help", ":log", ":steps", ":hist", ":ctx", ":obls", ":defs",
                  ":q", ":quit", ":save", ":replay", ":rules", ":latex", ":tree"}

    def rules_fingerprint(self):
        """规则集指纹：回放确定性校验用（规则变了回放即失效，永不静默错）。

        只覆盖非会话规则：origin='session' 的 :rule 内联定义由转录自身重建，
        不计入指纹（否则保存后回放必被自己的新规则拒死）。
        """
        import hashlib

        h = hashlib.sha1()
        for rid in sorted(self.rules.rules):
            r = self.rules.rules[rid]
            if r.origin == "session":
                continue
            h.update(f"{rid}|{to_str(r.pattern)}|{to_str(r.template)}|{r.priority}".encode())
        return h.hexdigest()[:12]

    def handle(self, line):
        """分发一条命令/表达式，返回输出文本（None = 无输出）。

        REPL 与回放共用同一入口——转录即 DSL，重放转录即重建推导。
        """
        line = line.strip()
        if not line:
            return None
        first = line.split(None, 1)[0]
        try:
            out = self._dispatch(line)
        except (BudgetExceeded, ParseError) as e:
            out = f"error: {e}"
        except Exception as e:
            out = f"error: {e.__class__.__name__}: {e}"
        if first not in self._NO_RECORD:
            self.transcript.append(line)
        return out

    def save_transcript(self, path):
        """保存转录（头部含规则指纹，回放时校验）。"""
        lines = ["# pyCAS transcript v1", f"# rules: {self.rules_fingerprint()}"]
        lines.extend(self.transcript)
        with open(path, "w", encoding="utf-8") as fh:
            fh.write("\n".join(lines) + "\n")
        return f"saved {len(self.transcript)} commands to {path}"

    def replay_file(self, path):
        """回放转录文件：跳注释头，逐条走 handle（与 REPL 完全同路径）。"""
        with open(path, "r", encoding="utf-8") as fh:
            raw = fh.readlines()
        cmds = []
        fp = None
        for ln in raw:
            ln = ln.rstrip("\n")
            if ln.startswith("# rules: "):
                fp = ln.split(": ", 1)[1].strip()
            elif not ln.startswith("#"):
                cmds.append(ln)
        if fp is not None and fp != self.rules_fingerprint():
            return (f"refused: rules fingerprint mismatch "
                    f"(file={fp}, session={self.rules_fingerprint()})")
        outs = []
        for c in cmds:
            if not c.strip():
                continue
            o = self.handle(c)
            if o:
                outs.append(o)
        return f"replayed {len(cmds)} commands\n" + "\n".join(outs)

    def commands(self):
        out = {
            ":s": "suggest [path]",
            ":a": "apply <rule-id> [path]",
            ":u": "undo [n]",
            ":auto": "core simplify",
            ":tree": "show subterm tree with paths (selection for path commands)",
            ":set": "subterm surgery: :set <path> <expr> (equivalent-checked)",
            ":rsub": "structural replace-all: :rsub <old>=<new>",
            ":add_both": "equation: add <t> to both sides",
            ":sub_both": "equation: subtract <t> from both sides",
            ":mul_both": "equation: multiply both sides by <t>",
            ":div_both": "equation: divide both sides by <t> (t != 0 gate)",
            ":neg_both": "equation: negate both sides",
            ":swap": "equation: swap sides",
            ":zero_form": "equation: rewrite L = R as L - R = 0",
            ":apply_both": "equation: apply unary fn to both sides: :apply_both <fn>",
            ":expand": "expand products/powers: :expand [path]",
            ":extract": "factor out common factor: :extract <f> [path]",
            ":separate": "split fraction over sum: (a+b)/c -> a/c+b/c: :separate [path]",
            ":complete_square": "complete square: :complete_square <var> [path]",
            ":usub": "forward substitution on inert integral: :usub t=g(x)",
            ":lhop": "one l'Hopital step on quotient form: :lhop <var> <point>",
            ":intro_eq": "extract chain equation: :intro_eq <lhs|%N> (lhs = current; loop: :intro_eq I)",
            ":fold": "linearity fold: rewrite constant-multiple named integrals (loop setup)",
            ":add_sub": "add-zero borrow: :add_sub <t> (A -> A + t - t, quoted; domain obligation)",
            ":parts": "integration by parts on inert integral: :parts <u> (shows u/dv/du/v)",
            ":subst": "substitute new variable: :subst t=g(x) (handles inert integral dx too)",
            ":solveq": "solve current linear equation for unknown: :solveq <term>",
            ":rule": "define session theorem inline: :rule id = lhs -> rhs [guard ... as ... auto]",
            ":unrule": "remove a session rule",
            ":rules": "list all rules (origin/prio/guard/direction)",
            ":value": "evaluate inert forms (Quote/'integrate/D nouns) in current expr",
            ":refine": "ledger-driven simplification (abs/sqrt/exp-log by assumptions)",
            ":latex": "LaTeX output of current expression",
            ":save": "save command transcript (DSL): :save <path>",
            ":replay": "replay a transcript: :replay <path>",
            ":steps": "explain the derivation (rules step-by-step; algorithms by name)",
            ":hist": "produced expressions (%N to reuse, % = latest)",
            ":defs": "list user definitions (name := expr / f(x) := expr)",
            ":undef": "remove a definition",
            ":assume": "assume <fact>",
            ":ans": "answer <oid> <fact>",
            ":obls": "list obligations",
            ":log": "step log",
            ":ctx": "ledger",
        }
        for name, c in self.kernel.items():
            out[":" + name] = c.help
        for name, c in self.solver.items():
            out["!" + name] = c.help
        out[":load"] = "reload rules dir"
        out[":q"] = "quit"
        return out

    def _dispatch(self, line):
        """全部分支返回文本（不打印）：REPL 与回放共用。分支顺序纪律：
        精确命令 > 内核注册表 > 前缀命令（:steps 被 :s 吞、:save 被 :s 吞的同款 bug 防三次）。"""
        if line == ":help":
            return "\n".join(f"{k:12s} {v}" for k, v in self.commands().items())
        if line == ":steps":
            return "\n".join(self.steps())
        if line == ":hist":
            out = [f"%{i}  {to_str(h)}" for i, h in enumerate(self.history, 1)]
            return "\n".join(out) if out else "(empty)"
        if line == ":defs":
            out = []
            for nm, (ps_, body) in self.defs.items():
                sig = f"{nm}({', '.join(p.name for p in ps_)})" if ps_ else nm
                out.append(f"{sig} := {to_str(body)}")
            return "\n".join(out) if out else "(none)"
        if line.startswith(":save "):
            return self.save_transcript(line[6:].strip())
        if line.startswith(":replay "):
            return self.replay_file(line[8:].strip())
        if line.startswith(":rule "):
            return self.add_rule(line[6:])
        if line.startswith(":unrule "):
            return self.unrule(line[8:].strip())
        if line == ":rules":
            return self.list_rules()
        if line == ":value":
            return self.value()
        if line == ":refine":
            return self.mrefine()
        if line == ":latex":
            return self.mlatex()
        # ! 前缀：自动求解（算法黑盒直出，verify 背书）
        if line.startswith("!") and line.split(None, 1)[0][1:] in self.solver:
            parts = line.split(None, 1)
            name = parts[0][1:]
            rest = self.expand_history(parts[1].strip()) if len(parts) > 1 else ""
            return self.solver[name].fn(self, rest)
        if line.startswith(":") and line.split(None, 1)[0][1:] in self.kernel:
            # 手动算法命令分发（: 前缀；先于前缀匹配，避免 :apart 被 :a 吞掉）
            parts = line.split(None, 1)
            name = parts[0][1:]
            rest = self.expand_history(parts[1].strip()) if len(parts) > 1 else ""
            return self.kernel[name].fn(self, rest)
        # ---- 手动交互扩展（子项手术/等式代数/变形工具箱/微积分战术）----
        # 分支顺序纪律：先于 :s / :u 前缀分支（:set/:swap/:separate 被 :s 吞、
        # :usub 被 :u 吞的同款 bug 防患）
        if line == ":tree":
            return self.tree()
        if line.startswith(":set "):
            parts = line[5:].split(None, 1)
            if len(parts) != 2:
                return "usage: :set <path> <expr>"
            return self.set_at(parts[0], self.expand_history(parts[1]))
        if line.startswith(":rsub "):
            return self.rsub(self.expand_history(line[6:].strip()))
        if line.startswith(":add_both "):
            return self.eq_add_both(line[10:].strip())
        if line.startswith(":sub_both "):
            return self.eq_sub_both(line[10:].strip())
        if line.startswith(":mul_both "):
            return self.eq_mul_both(line[10:].strip())
        if line.startswith(":div_both "):
            return self.eq_div_both(line[10:].strip())
        if line == ":neg_both":
            return self.eq_neg_both()
        if line == ":swap":
            return self.eq_swap()
        if line == ":zero_form":
            return self.eq_zero_form()
        if line.startswith(":apply_both "):
            return self.eq_apply_both(line[12:].strip())
        if line.startswith(":expand"):
            return self.expand_at(line[7:].strip() or None)
        if line.startswith(":extract "):
            parts = line[9:].split()
            path_s = None
            if len(parts) >= 2 and all(seg.isdigit() for seg in parts[-1].split(".")):
                path_s = parts[-1]
                parts = parts[:-1]
            return self.extract(" ".join(parts), path_s)
        if line == ":separate":
            return self.separate_at(None)
        if line.startswith(":separate "):
            return self.separate_at(line[10:].strip() or None)
        if line.startswith(":complete_square "):
            parts = line[17:].split()
            if not parts:
                return "usage: :complete_square <var> [path]"
            return self.complete_square(parts[0], parts[1] if len(parts) > 1 else None)
        if line.startswith(":usub "):
            res = self.usub(line[6:].strip())
            return to_str(res) if isinstance(res, T.Term) else res
        if line.startswith(":lhop "):
            parts = line[6:].split()
            if len(parts) != 2:
                return "usage: :lhop <var> <point>"
            res = self.lhop(parts[0], parts[1])
            return to_str(res) if isinstance(res, T.Term) else res
        if line.startswith(":intro_eq "):
            # %N 先展开：等式链任意节点（历史产出）都可与当前式连等式
            res = self.intro_eq(self.expand_history(line[10:].strip()))
            return to_str(res) if isinstance(res, T.Term) else res
        if line == ":fold":
            return self.fold()
        if line.startswith(":add_sub "):
            res = self.add_sub(line[9:].strip())
            return to_str(res) if isinstance(res, T.Term) else res
        if line.startswith(":parts "):
            res = self.iparts(line[7:].strip(), detail=True)
            return res if isinstance(res, str) else to_str(res)
        if line.startswith(":subst "):
            res = self.subst(line[7:].strip())
            return to_str(res) if isinstance(res, T.Term) else res
        if line.startswith(":solveq "):
            res = self.solveq(line[8:].strip())
            return to_str(res) if isinstance(res, T.Term) else res
        if line.startswith(":s"):
            arg = line[2:].strip()
            path = tuple(int(i) for i in arg.split(".")) if arg else ()
            out = [f"{rid:20s} guard={g:8s} {('dir=' + d) if d else ''}"
                   for rid, g, d in self.suggest(path)]
            return "\n".join(out)
        if line.startswith(":a "):
            parts = line[3:].split()
            rid = parts[0]
            path = tuple(int(i) for i in parts[1].split(".")) if len(parts) > 1 else None
            n0 = len(self.log)
            res = self.apply(rid, path)
            out = [to_str(res) if isinstance(res, T.Term) else res]
            out += ["  " + ln for ln in self.steps()[n0:]]
            return "\n".join(out)
        if line.startswith(":undef "):
            return self.undef(line[7:].strip())
        if line.startswith(":u"):
            n = int(line[2:] or 1)
            return to_str(self.undo(n)) if self.log else "no steps"
        if line == ":auto":
            n0 = len(self.log)
            out = [to_str(self.auto())]
            out += ["  " + ln for ln in self.steps()[n0:]]
            return "\n".join(out)
        if line.startswith(":assume "):
            return self.assume(self.expand_history(line[8:]))
        if line.startswith(":declare "):
            parts = line[9:].split()
            if parts and parts[0] == "principal-branch":
                on = (parts[1].lower() in ("on", "true", "1")
                      if len(parts) > 1 else True)
                # 会话级声明：只写本 Session（互不影响）；全局位留给
                # 程序化调用方经 structure.set_principal_branch 设置
                self._principal_branch = on
                return ("branch policy: principal = "
                        + ("ON (fractional-power identities active "
                           "in verification)" if on else "OFF"))
            if len(parts) == 2:
                return self.declare(parts[0], parts[1])
            return "usage: :declare <var> <property> | principal-branch on/off"
        if line.startswith(":ans "):
            parts = line[5:].split(None, 1)
            oid = int(parts[0])
            return self.answer(oid, self.expand_history(parts[1]))
        if line == ":obls":
            out = [f"#{o.oid}  {to_str(o.question)}   affects steps {o.affects}"
                   for o in self.obligations]
            return "\n".join(out) if out else "(none)"
        if line == ":log":
            out = [f"#{st.sid} {st.rule_id:18s} at {st.path}  {to_str(st.before)}  ->  {to_str(st.after)}"
                   for st in self.log]
            return "\n".join(out) if out else "(no steps)"
        if line == ":ctx":
            out = [f"[{e.kind}:{e.origin}] {to_str(e.fact)}" for e in self.ctx.entries]
            return "\n".join(out) if out else "(empty ledger)"
        if line == ":load":
            import os

            rd = os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), "rules")
            return f"loaded {loader.load_dir(rd, self.rules)} rules"
        if ":=" in line:
            # 用户定义：f(x) := 体（函数）/ a := 体（变量），宏展开语义；右侧支持 % 历史
            lhs, rhs = line.split(":=", 1)
            lhs = lhs.strip()
            rhs = self.expand_history(rhs.strip())
            if "(" in lhs:
                return self.define(lhs, rhs)
            return self.assign(lhs, rhs)
        self.feed(self.expand_history(line))
        return self.show()


    # ---------------- 会话规则管理（:rule/:unrule/:rules） ----------------

    def add_rule(self, text):
        """:rule 内联定理定义（maxima tellsimp 同款）：语法同规则文件行
        （rule id = lhs -> rhs [guard ... as ... prio ... auto]），origin='session'。
        规则库从文件升级为会话参与者；转录自动收录，回放时重建。"""
        self._check_locked()
        body = text.strip()
        if not body.startswith("rule "):
            body = "rule " + body
        r = loader.parse_rule_line(body, origin="session")
        existed = r.id in self.rules.rules
        self.rules.add(r)
        return f"{'redefined' if existed else 'defined'}: {r.id}"

    def unrule(self, rid):
        """删除会话内联规则（文件规则不可删——文件是定理库本体）。"""
        r = self.rules.rules.get(rid)
        if r is None:
            return f"no rule: {rid}"
        if r.origin != "session":
            return f"rule {rid} comes from {r.origin}; only session rules can be removed"
        self.rules.remove(rid)
        return f"removed: {rid}"

    def list_rules(self):
        out = []
        for rid in sorted(self.rules.rules):
            r = self.rules.rules[rid]
            g = f" guard {to_str(r.guard)}" if r.guard is not None else ""
            d = f" as {r.direction}" if r.direction else ""
            a = " auto" if r.auto else ""
            out.append(f"{rid:16s} [{r.origin:10s} prio {r.priority:3d}] "
                       f"{to_str(r.pattern)} -> {to_str(r.template)}{g}{d}{a}")
        return "\n".join(out) if out else "(no rules)"
