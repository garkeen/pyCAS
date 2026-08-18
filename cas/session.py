import os

from dataclasses import dataclass, field

from cas import term as T
from cas import context as context_mod
from cas.decide import (
    eval_guard as _eval_guard,
    decide as _decide_fn,
    contradicted as _contradicted_fn,
    T3,
)
from cas.context import Context
from cas.parser import parse
from cas.pprint import to_str
from cas.rules import Rule, RuleSet, Step, apply_rule
from cas.simplify import simplify, cost
from cas.errors import BudgetExceeded, ParseError
from cas import loader


@dataclass
class Obligation:
    oid: int
    question: T.Term
    affects: list
    note: str = ""
    pending: list = field(default_factory=list)


class Session:
    def __init__(self, budget=100000):
        self.current = None
        self.log = []
        self.obligations = []
        self.ctx = Context()
        self.rules = RuleSet()
        self.budget = budget
        self.locked = None
        self._sid = 0
        self._oid = 0
        rules_dir = os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), "rules")
        if os.path.isdir(rules_dir):
            try:
                loader.load_dir(rules_dir, self.rules)
            except Exception:
                pass

    def feed(self, s):
        self.current = parse(s)
        return self.current

    def _guard_eval(self, guard, sub):
        return _eval_guard(guard, sub, self.ctx)

    def suggest(self, path=None):
        if self.current is None:
            return []
        paths = [tuple(path)] if path is not None else list(T.all_paths(self.current))
        out = []
        for p in paths:
            tgt = T.term_at(self.current, p)
            for r in self.rules.for_term(tgt):
                res = apply_rule(r, self.current, p, self._guard_eval)
                if res.guard in ("YES", "UNKNOWN"):
                    out.append((r.id, res.guard, p))
        return out

    def apply(self, rid, path=()):
        r = self.rules.rules.get(rid)
        if r is None:
            return f"no rule {rid}"
        res = apply_rule(r, self.current, path, self._guard_eval, self.budget)
        if res.guard == "NOMATCH":
            return f"rule {rid} does not match at {path}"
        if res.guard == "UNKNOWN":
            self._oid += 1
            q = T.instantiate(r.guard, res.subst)
            obl = Obligation(self._oid, q, [self._sid + 1], note=f"guard of {rid}")
            obl.pending.append({"rule": rid, "path": tuple(path)})
            self.obligations.append(obl)
            return f"guard UNKNOWN: {to_str(q)}  (obligation #{self._oid} created; answer then :ans {self._oid} <fact>)"
        return self._commit(r, path, res)

    def _commit(self, r, path, res):
        self._sid += 1
        before = self.current
        self.current = res.term
        st = Step(self._sid, r.id, tuple(path), before, self.current, res.guard, cost(res.term) - cost(before))
        self.log.append(st)
        if r.guard is not None:
            g = T.instantiate(r.guard, res.subst)
            cst, _ = self.ctx.check_and_assume(g, origin=f"step{self._sid}", kind="guard")
            if cst is T3.NO:
                self.locked = f"contradiction after step {self._sid}"
        return self.current

    def auto(self):
        if self.current is None:
            return None
        cur = self.current
        auto_rules = [r for r in self.rules.rules.values() if r.auto]
        for _ in range(10):
            nxt = simplify(cur, self.budget)
            changed = False
            for p in T.all_paths(nxt):
                try:
                    tgt = T.term_at(nxt, p)
                except IndexError:
                    continue
                for r in auto_rules:
                    res = apply_rule(r, nxt, p, self._guard_eval, self.budget)
                    if res.guard != "YES":
                        continue
                    if cost(res.term) <= cost(nxt):
                        nxt = res.term
                        changed = True
                        break
            if nxt is cur and not changed:
                break
            cur = nxt
        self.current = cur
        return cur

    def assume(self, s):
        f = parse(s)
        st, why = self.ctx.check_and_assume(f, origin="user")
        if st is T3.NO:
            if why == "domain":
                return f"domain empty: {to_str(f)} is not defined on the real line"
            self.locked = f"contradiction: {to_str(f)} vs ledger"
            return f"CONTRADICTION LOCKED: {self.locked}"
        return f"assumed: {to_str(f)}"

    def answer(self, oid, s):
        f = parse(s)
        obl = next((o for o in self.obligations if o.oid == oid), None)
        if obl is None:
            return f"no obligation #{oid}"
        st, why = self.ctx.check_and_assume(f, origin=f"obl{oid}", kind="answer")
        if st is T3.NO:
            if why == "domain":
                return f"domain empty: {to_str(f)} is not defined on the real line"
            return f"answer rejected: {to_str(f)} contradicts ledger"
        self.obligations.remove(obl)
        if obl.pending:
            for p in obl.pending:
                rid = p["rule"]
                path = p["path"]
                res = apply_rule(self.rules.rules[rid], self.current, path, self._guard_eval)
                if res.guard == "YES":
                    self._commit(self.rules.rules[rid], path, res)
                elif res.guard == "UNKNOWN":
                    return f"still not applicable: {res.guard}"
        return f"answered #{oid}: {to_str(f)}"

    def undo(self, n=1):
        for _ in range(n):
            if not self.log:
                return
            st = self.log.pop()
            self.current = st.before
            self.ctx.drop_origin(f"step{st.sid}")
        return self.current

    def replay(self, from_sid=0):
        steps = [s for s in self.log if s.sid > from_sid]
        base = next((s.before for s in self.log if s.sid == from_sid), None)
        if base is None and from_sid == 0:
            base = self.log[0].before if self.log else None
        if base is None:
            return "nothing to replay"
        self.current = base
        for st in steps:
            r = self.rules.rules.get(st.rule_id)
            if r is None:
                return f"replay stuck at {st.rule_id}"
            res = apply_rule(r, self.current, st.path, self._guard_eval)
            if res.guard != "YES":
                return f"replay diverged at step {st.sid} ({res.guard})"
            self._sid += 1
            self.current = res.term
            if r.guard is not None:
                g = T.instantiate(r.guard, res.subst)
                self.ctx.assume(g, origin=f"step{self._sid}", kind="guard")
        return self.current

    def verify(self, Fs, xs, fs):
        from cas.diff import verify

        F = parse(Fs)
        x = parse(xs)
        f = parse(fs)
        return verify(F, x, f, self.budget)

    def solve(self, fs, vs=None):
        from cas.solve import solve

        f = parse(fs)
        if vs:
            var = T.S(vs)
        else:
            var = None
            for p in T.all_paths(f):
                t = T.term_at(f, p)
                if isinstance(t, T.Sym) and t.name not in ("e", "pi"):
                    var = t
                    break
        if var is None:
            return "no variable to solve for"
        r = solve(f, var, self.budget)
        if r.status == "identity":
            return "identity: 0 = 0 for all " + var.name
        if r.status == "contradiction":
            return "contradiction: no solution"
        if r.status == "unsupported":
            return "unsupported: " + (r.note or "cannot solve")
        out = ", ".join(to_str(s) for s in r.solutions) or "(none)"
        if r.provisos:
            out += "   [proviso: " + " && ".join(to_str(g) for g in r.provisos) + "]"
        return var.name + " = " + out

    def mat(self, spec):
        from cas.matrix import Matrix

        return Matrix.parse(spec).show()

    def mdet(self, spec):
        from cas.matrix import Matrix
        from cas.pprint import to_str

        return to_str(Matrix.parse(spec).det())

    def mrank(self, spec):
        from cas.matrix import Matrix

        return str(Matrix.parse(spec).rank())

    def minv(self, spec):
        from cas.matrix import Matrix

        m = Matrix.parse(spec).inv()
        return m.show() if m is not None else "singular"

    def msolve(self, spec, rhs):
        from cas.matrix import Matrix
        from cas.parser import parse
        from cas.pprint import to_str

        b = [parse(c.strip()) for c in rhs.strip()[1:-1].split(",")]
        r = Matrix.parse(spec).solve(b)
        if r.unique is not None:
            return ", ".join(
                f"x{i + 1} = {to_str(v)}" for i, v in enumerate(r.unique)
            )
        if r.particular is None:
            return "no solution"
        parts = ", ".join(f"x{i + 1} = {to_str(v)}" for i, v in enumerate(r.particular))
        basis = "; ".join(
            "(" + ", ".join(to_str(v) for v in vec) + ")" for vec in r.null_basis
        )
        return f"infinite: {parts}  + t*({basis})"

    def _pick_var(self, t):
        for p in T.all_paths(t):
            v = T.term_at(t, p)
            if isinstance(v, T.Sym) and v.name not in ("e", "pi"):
                return v
        return None

    def factor(self, s):
        from cas.poly import Poly
        from cas.factor import factor as zz_factor

        t = parse(s)
        x = self._pick_var(t)
        if x is None:
            return "no variable"
        f = Poly.from_term(t, (x,))
        c, facs = zz_factor(f)
        parts = []
        if c != 1:
            parts.append(str(c))
        for g, m in facs:
            s_ = str(g)
            if "+" in s_ or "-" in s_[1:]:
                s_ = f"({s_})"
            parts.append(f"{s_}^{m}" if m > 1 else s_)
        return " * ".join(parts) if parts else str(c)

    def apart(self, num_s, den_s):
        from cas.poly import Poly
        from cas.apart import apart as zz_apart

        t1 = parse(num_s)
        t2 = parse(den_s)
        x = self._pick_var(t1) or self._pick_var(t2)
        if x is None:
            return "no variable"
        f = Poly.from_term(t1, (x,))
        g = Poly.from_term(t2, (x,))
        q, terms = zz_apart(f, g)
        out = []
        if not q.is_zero():
            out.append(str(q))
        for nn, dd, k in terms:
            s_ = f"({nn})/({dd})"
            out.append(f"{s_}^{k}" if k > 1 else s_)
        return " + ".join(out) if out else "0"

    def show(self):
        return to_str(self.current) if self.current is not None else "(empty)"

    def commands(self):
        return {
            ":s": "suggest [path]",
            ":a": "apply <rule-id> [path]",
            ":u": "undo [n]",
            ":auto": "core simplify",
            ":assume": "assume <fact>",
            ":ans": "answer <oid> <fact>",
            ":obls": "list obligations",
            ":log": "step log",
            ":ctx": "ledger",
            ":verify": "verify <F> <x> <f>",
            ":solve": "solve <expr> [var]",
            ":factor": "factor <expr>",
            ":apart": "apart <num> <den>",
            ":mat": "show matrix [[a,b],[c,d]]",
            ":mdet": "determinant [[a,b],[c,d]]",
            ":mrank": "rank [[a,b],[c,d]]",
            ":minv": "inverse [[a,b],[c,d]]",
            ":msolve": "solve system: :msolve [[a,b],[c,d]] [e,f]",
            ":load": "reload rules dir",
            ":q": "quit",
        }


def run():
    s = Session()
    print("pyCAS session. :help for commands; expression to make current.")
    while True:
        try:
            line = input(">> ").strip()
        except EOFError:
            break
        if not line:
            continue
        if line in (":q", ":quit"):
            break
        try:
            if line == ":help":
                for k, v in s.commands().items():
                    print(f"{k:10s} {v}")
            elif line.startswith(":s"):
                arg = line[2:].strip()
                path = tuple(int(i) for i in arg.split(".")) if arg else ()
                for rid, g, d in s.suggest(path):
                    print(f"{rid:20s} guard={g:8s} {('dir=' + d) if d else ''}")
            elif line.startswith(":a "):
                parts = line[3:].split()
                rid = parts[0]
                path = tuple(int(i) for i in parts[1].split(".")) if len(parts) > 1 else ()
                print(to_str(s.apply(rid, path)) if s.current is not None else "empty")
            elif line.startswith(":u"):
                n = int(line[2:] or 1)
                print(to_str(s.undo(n)) if s.log else "no steps")
            elif line == ":auto":
                print(to_str(s.auto()))
            elif line.startswith(":assume "):
                print(s.assume(line[8:]))
            elif line.startswith(":ans "):
                parts = line[5:].split(None, 1)
                oid = int(parts[0])
                print(s.answer(oid, parts[1]))
            elif line == ":obls":
                for o in s.obligations:
                    print(f"#{o.oid}  {to_str(o.question)}   affects steps {o.affects}")
                if not s.obligations:
                    print("(none)")
            elif line == ":log":
                for st in s.log:
                    print(f"#{st.sid} {st.rule_id:18s} at {st.path}  {to_str(st.before)}  ->  {to_str(st.after)}")
                if not s.log:
                    print("(no steps)")
            elif line == ":ctx":
                for e in s.ctx.entries:
                    print(f"[{e.kind}:{e.origin}] {to_str(e.fact)}")
                if not s.ctx.entries:
                    print("(empty ledger)")
            elif line.startswith(":verify "):
                a, b, c = line[8:].split()
                print(s.verify(a, b, c))
            elif line.startswith(":solve "):
                parts = line[7:].split()
                expr = parts[0]
                var = parts[1] if len(parts) > 1 else None
                print(s.solve(expr, var))
            elif line.startswith(":factor "):
                print(s.factor(line[8:].strip()))
            elif line.startswith(":apart "):
                args = line[7:].split()
                if len(args) == 2:
                    print(s.apart(args[0], args[1]))
                else:
                    print("usage: :apart <numerator> <denominator>")
            elif line.startswith(":mat "):
                print(s.mat(line[5:].strip()))
            elif line.startswith(":mdet "):
                print(s.mdet(line[6:].strip()))
            elif line.startswith(":mrank "):
                print(s.mrank(line[7:].strip()))
            elif line.startswith(":minv "):
                print(s.minv(line[6:].strip()))
            elif line.startswith(":msolve "):
                rest = line[8:].strip()
                idx = rest.find("]] ")
                if idx >= 0:
                    spec = rest[: idx + 2]
                    rhs = rest[idx + 3 :].strip()
                    if rhs.startswith("[") and rhs.endswith("]"):
                        print(s.msolve(spec, rhs))
                    else:
                        print("usage: :msolve [[a,b],[c,d]] [e,f]")
                else:
                    print("usage: :msolve [[a,b],[c,d]] [e,f]")
            elif line == ":load":
                import os

                rd = os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), "rules")
                print(f"loaded {loader.load_dir(rd, s.rules)} rules")
            else:
                s.feed(line)
                print(s.show())
        except (BudgetExceeded, ParseError) as e:
            print(f"error: {e}")
        except Exception as e:
            print(f"error: {e.__class__.__name__}: {e}")


if __name__ == "__main__":
    run()
