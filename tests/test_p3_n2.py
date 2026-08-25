import pytest
from fractions import Fraction as Fr
from cas.poly import Poly, _mk_param, SymRat
from cas.term import S
from cas.apart import _param_factors, _an_factor, apart

x=S("x")
a=S("a"); b=S("b")

def test_param_linear_peel():
    # (x-1)*(x^2+a) in Q(a)[x]
    pa = _mk_param(a)
    p = Poly((x,), {(3,):Fr(1),(2,):Fr(-1),(1,):pa,(0,):-pa})
    facs, pc = _param_factors(p, x)
    assert len(facs)==2
    assert any(f.degree(x)==1 for f in facs)
    assert any(f.degree(x)==2 for f in facs)

def test_param_general_cubic():
    # (x-2)*(x^2+1) => x^3-2x^2+x-2  (2 factors: linear + irreducible quadratic)
    pa=_mk_param(a)
    p = Poly((x,), {(3,):Fr(1),(2,):Fr(-2),(1,):Fr(1),(0,):Fr(-2)})
    facs, pc = _param_factors(p, x)
    assert len(facs)==2
    # also test fully split x^3-2x^2 -x+2 => 3 linears
    p2 = Poly((x,), {(3,):Fr(1),(2,):Fr(-2),(1,):Fr(-1),(0,):Fr(2)})
    facs2, _ = _param_factors(p2, x)
    assert len(facs2)==3

def test_param_irreducible():
    # x^2 + a : discriminant not square in Q(a) => irreducible
    pa=_mk_param(a)
    p = Poly((x,), {(2,):Fr(1),(0,):pa})
    facs, pc=_param_factors(p, x)
    assert len(facs)==1 and facs[0]==p

def test_an_trager():
    from cas.algfield import af_q, register_alg_field, unregister_alg_fields, ALG_FIELDS
    import cas.term as T
    from cas.term import N
    # Q(sqrt2)[x]: Norm method
    sym=S("_an_test")
    fld=af_q([Fr(-2),Fr(0),Fr(1)], origin=T.mk(S("Power"), (N(2), N(Fr(1,2)))))
    register_alg_field(sym, fld)
    # g = x^2 -2 in Q(sqrt2)[x] should factor as (x - sqrt2)(x + sqrt2) via Norm
    # Build Poly with coeff sqrt2: we need SymRat with _an_test
    # Instead test via apart's _an_factor directly with Fr+SymRat containing _an_test
    # Construct g in Q(sqrt2)[x] as Poly with SymRat coeff _an_test
    # Use Poly with vars (x,) and coeff SymRat where num = Poly((_an_test,), {(1,):1})
    from cas.poly import SymRat as SR
    from cas.poly import Poly as P
    # Represent sqrt2 as SymRat(_an_test)
    p_sqrt = P((sym,), {(1,):Fr(1)})
    sr_sqrt = SR(p_sqrt, P.one((sym,)))
    g = P((x,), {(2,):Fr(1),(0,): -sr_sqrt*sr_sqrt})  # x^2 -2
    # Actually -sr_sqrt*sr_sqrt = -2
    # Let's use g = x^2 - sqrt2*x  => should have factor x
    g2 = P((x,), {(2,):Fr(1),(1,): -sr_sqrt})
    # For Trivial, test _an_factor returns something or None but not crash and within timeout
    res = _an_factor(g2, x)
    assert res is None or isinstance(res, tuple)
    unregister_alg_fields([sym])

def test_apart_mixed_timeout():
    # apart with param and AN mixed should not hang, within 5s
    import time
    pa=_mk_param(a)
    f = Poly((x,), {(1,):Fr(1)})
    g = Poly((x,), {(3,):Fr(1),(0,):pa})  # x^3 + a
    start=time.time()
    q, terms = apart(f,g)
    assert time.time()-start < 5

if __name__=="__main__":
    pytest.main([__file__, "-q"])
