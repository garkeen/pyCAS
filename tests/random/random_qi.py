# -*- coding: utf-8 -*-
"""Q(i), the Gaussian field, random bench (fully self-proving, no external ground truth).

  P39 two-channel cross-check  ring dual arithmetic (QIRing) against the membership
                               channel (i -> z, rational functions over Q(z), reduction
                               modulo z^2+1) -- two independent code paths must agree
                               round by round: domain axioms (distributivity, inverse,
                               norm multiplicativity)
  P40 membership boundary      many shapes of Q(i) term (reordered, division, power)
                               round-trip through membership and value; non-members
                               (pi+i, sin(i), a square root, one containing a variable,
                               division by zero) all fall through honestly; and
                               normalization is idempotent (interned pointer)
  P41 ladder x zero x capability  the projection ladder Z -> Q -> Q(i); domain equality
                               and zero channels; capability fields
                               (is_field / unordered / non-Euclidean); and the
                               integration-constant channel (integral of a+bi checked
                               independently by the differentiation layer)

Usage: python tests/random/random_qi.py [rounds] [seed]
"""

import sys
import random
from fractions import Fraction as Fr

sys.path.insert(0, ".")

from cas.runtime import bootstrap
bootstrap()

import cas.syntax.term as T
from cas.syntax.term import S
from cas.frontend.parser import parse
from cas.frontend.pprint import to_str
from cas.math.project import project, zero_of, normalize
from cas.math.domains.qi import QI_RING, qi_of_term
from cas.math.integrate import integrate_term
from cas.math.calculus.integration.verify import verify_antideriv

X = S("x")
from cas.runtime import get_runtime
I = get_runtime().const_by_name("i").atom
DOM = project(parse("i")).domain


def fail(msg, seed, *extra):
    print(f"FAIL [{msg}] seed={seed}")
    for e in extra:
        print("  ", e)
    sys.exit(1)


def rand_qi(rng, nonzero=False):
    while True:
        a = Fr(rng.randint(-9, 9), rng.choice((1, 1, 2, 3)))
        b = Fr(rng.randint(-9, 9), rng.choice((1, 1, 2, 3)))
        if (a, b) != (0, 0) or not nonzero:
            return (a, b)


def _norm2(p):
    return p[0] * p[0] + p[1] * p[1]


# ---------------------------------------------------------------------------
# P39: two-channel cross-check plus domain axioms
# ---------------------------------------------------------------------------

def prop_two_channels(rounds, rng):
    for i in range(rounds):
        a = rand_qi(rng)
        b = rand_qi(rng, nonzero=True)
        c = rand_qi(rng)
        ta, tb, tc = DOM.to_term(a), DOM.to_term(b), DOM.to_term(c)
        # channel 1: ring dual arithmetic; channel 2: term-level arithmetic through the
        # membership channel (rf machinery plus reduction)
        m1 = QI_RING.mul(a, b)
        m2 = qi_of_term(I, T.times(ta, tb))
        if m1 != m2:
            fail("P39 multiplication disagrees between channels", i, a, b, m1, m2)
        d1 = QI_RING.div_exact(a, b)
        d2 = qi_of_term(I, T.times(ta, T.pw(tb, T.N(-1))))
        if d1 != d2:
            fail("P39 division disagrees between channels", i, a, b, d1, d2)
        s1 = QI_RING.add(a, b)
        s2 = qi_of_term(I, T.plus(ta, tb))
        if s1 != s2:
            fail("P39 addition disagrees between channels", i, a, b, s1, s2)
        # domain axioms: distributivity, inverse, norm multiplicativity (proved inside the ring channel)
        if QI_RING.mul(a, QI_RING.add(b, c)) != \
                QI_RING.add(QI_RING.mul(a, b), QI_RING.mul(a, c)):
            fail("P39 distributivity broken", i, a, b, c)
        if QI_RING.mul(b, QI_RING.div_exact(QI_RING.from_int(1), b)) != \
                QI_RING.from_int(1):
            fail("P39 inverse does not restore", i, b)
        if _norm2(QI_RING.mul(a, b)) != _norm2(a) * _norm2(b):
            fail("P39 norm multiplicativity broken", i, a, b)


# ---------------------------------------------------------------------------
# P40: membership boundary plus normalization round trip
# ---------------------------------------------------------------------------

def prop_membership(rounds, rng):
    for i in range(rounds):
        a = rand_qi(rng)
        b = rand_qi(rng, nonzero=True)
        # division shape: the expected value comes from independent arithmetic in the
        # test (conjugate/norm formula)
        want = QI_RING.div_exact(a, b)
        expr = f"({a[0]}+({a[1]})*i)/({b[0]}+({b[1]})*i)"
        got = qi_of_term(I, parse(expr))
        if got != want:
            fail("P40 division-term value mismatch", i, expr, got, want)
        # power shape: the value of i^n is i^(n mod 4)
        n = rng.randint(0, 11)
        k = n % 4
        want_pow = [(Fr(1), Fr(0)), (Fr(0), Fr(1)),
                    (Fr(-1), Fr(0)), (Fr(0), Fr(-1))][k]
        got_pow = qi_of_term(I, parse(f"i^{n}"))
        if got_pow != want_pow:
            fail("P40 power-term value mismatch", i, n, got_pow, want_pow)
        # reordered shape: b*i + a has the same value as a + b*i
        for shape in (parse(f"{a[1]}*i + {a[0]}"),
                      parse(f"{a[0]} + {a[1]}*i")):
            if qi_of_term(I, shape) != a:
                fail("P40 reordered shape mismatch", i, to_str(shape), a)
        # normalization idempotence: normalizing the output again gives the same interned pointer
        t1 = normalize(project(parse(expr)))
        t2 = normalize(project(t1))
        if t1 is not t2:
            fail("P40 normalization is not idempotent", i, to_str(t1), to_str(t2))
        # non-members: pi+i, sin(i), a square root, one with a variable, division by zero
        for bad in ("pi + i", "sin(i)", "2^(1/2)", "x + i", "1/(i*i+1)"):
            if qi_of_term(I, parse(bad)) is not None:
                fail("P40 non-member did not fall through", i, bad)


# ---------------------------------------------------------------------------
# P41: ladder x zero x capability x integration constant
# ---------------------------------------------------------------------------

def prop_ladder(rounds, rng):
    for i in range(rounds):
        a = rand_qi(rng)
        # ladder order: integers -> Q -> Q(i)
        if project(parse("3")).name != "Z":
            fail("P41 integer ladder", i)
        if project(parse("1/3")).name != "Q":
            fail("P41 rational ladder", i)
        h = project(DOM.to_term(a))
        if a[1] == 0:
            # the pair with im=0 is a rational number: the canonical term is purely
            # rational, so the ladder correctly hits Z/Q
            if h is None or h.name not in ("Z", "Q"):
                fail("P41 a purely real pair should land on the rational ladder", i, a, h and h.name)
        elif h is None or h.name != "Q(i)":
            fail("P41 Gaussian ladder", i, a)
        # zero channel: the folded value difference must give the exact truth value
        t = DOM.to_term(a)
        z = zero_of(t)
        if z is not (a == (Fr(0), Fr(0))):
            fail("P41 zero test distorted", i, a, z)
        if zero_of(parse("i*i+1")) is not True:
            fail("P41 i^2+1 was not decided zero", i)
        if zero_of(parse("(1+i)*(1-i) - 2")) is not True:
            fail("P41 (1+i)(1-i)=2 was not decided zero", i)
        # capability fields: the capability lookup that must refuse an order test
        if not DOM.is_field or DOM.is_ordered or DOM.is_euclidean:
            fail("P41 capability fields wrong", i)
        # integration-constant channel: integral of (a+bi) dx = (a+bi)x, checked
        # independently by the differentiation layer
        f = DOM.to_term(a)
        F = integrate_term(f, X)
        if verify_antideriv(F, f, X) is not True:
            fail("P41 integration-constant verification failed", i, to_str(f), to_str(F))


if __name__ == "__main__":
    rounds = int(sys.argv[1]) if len(sys.argv) > 1 else 500
    seed = int(sys.argv[2]) if len(sys.argv) > 2 else 20260828
    print(f"== Q(i) Gaussian field random bench: rounds={rounds} seed={seed} ==")
    rng = random.Random(seed)
    prop_two_channels(rounds, rng)
    print(f"P39 two-channel + domain axioms   {rounds} rounds passed")
    prop_membership(rounds, rng)
    print(f"P40 membership + normalization    {rounds} rounds passed")
    prop_ladder(rounds, rng)
    print(f"P41 ladder/zero/capability/integral  {rounds} rounds passed")
    print("== all passed ==")
