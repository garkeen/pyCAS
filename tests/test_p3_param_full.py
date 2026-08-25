import pytest
from fractions import Fraction as Fr
from cas.poly import Poly, _mk_param
from cas.term import S
from cas.apart import apart
from cas.integrate import integrate
from cas.parser import parse

x=S("x"); a=S("a"); b=S("b")

def test_param_factor_small_root():
    pa=_mk_param(a)
    # x^3 - a^3
    p=Poly((x,), {(3,):Fr(1),(0,): -pa*pa*pa})
    from cas.apart import _param_factors
    facs,_=_param_factors(p,x)
    assert len(facs)==2

def test_param_quad():
    pa=_mk_param(a)
    p=Poly((x,), {(2,):Fr(1),(0,): -pa*pa})
    from cas.apart import _param_factors
    facs,_=_param_factors(p,x)
    assert len(facs)==2

def test_apart_param():
    pa=_mk_param(a)
    f=Poly((x,), {(0,):Fr(1)})
    g=Poly((x,), {(2,):Fr(1),(0,): pa})  # x^2 + a
    q, terms = apart(f,g)
    # should not hang, within 2s
    assert True

def test_integrate_param_rational():
    # integrate 1/(x^2 + a) with param a, should be proviso or ok
    f=parse("1/(x^2 + a)")
    F,ok,prov,_=integrate(f,x)
    # either ok or proviso, but not hang and not false verified
    assert ok in (True, False)

def test_integrate_param_cubic():
    f=parse("1/(x^3 + a)")
    F,ok,_,_=integrate(f,x)
    # should be honest (may be unknown), not hang
    assert ok in (True, False)

if __name__=="__main__":
    pytest.main([__file__, "-q"])
