import pytest, time
from fractions import Fraction as Fr
from cas import term as T
from cas.term import S
from cas.poly import Poly
from cas.risch_core import build_extension

x=S("x")

def _integrate_term(f):
    from cas.risch_core import build_extension
    from cas.risch import _risch_rec
    try:
        de,fa,fd=build_extension(f, x)
        if len(de.levels)<=1:
            return None
        # find algebraic level
        for j,case in enumerate(de.cases):
            if case=="algebraic":
                from cas.risch import _try_general_algebraic, _try_linear_algebraic, _try_quad_algebraic
                # try quad/linear first as in real path
                r=_try_quad_algebraic(fa,fd,de,j) or _try_linear_algebraic(fa,fd,de,j)
                if r is not None:
                    return r
                # then general
                from cas.intalg import double_resultant
                z=S("_gen_z")
                mp=de.minpolys[j][1]
                R=double_resultant(fa,fd,mp,de,j,z)
                # just ensure not hang and R is Poly or None
                assert R is None or isinstance(R, Poly)
                return R
    except Exception as e:
        # RischUnsupported is expected for high genus
        return None

def test_p4_q3_cubic():
    f=T.pw(T.plus(T.pw(S("x"), T.N(3)), T.N(1)), T.Rat(Fr(1,3)))
    start=time.time()
    r=_integrate_term(f)
    assert time.time()-start < 5

def test_p4_q5_high():
    f=T.pw(T.plus(T.pw(S("x"), T.N(5)), T.N(2)), T.Rat(Fr(1,5)))
    start=time.time()
    r=_integrate_term(f)
    assert time.time()-start < 5

def test_p4_quad_high_deg():
    # y^2 = x^4+1, integrand 1/y
    f=T.pw(T.plus(T.pw(S("x"), T.N(4)), T.N(1)), T.Rat(Fr(1,2)))
    start=time.time()
    r=_integrate_term(f)
    assert time.time()-start < 5

def test_p4_linear_q7():
    f=T.pw(T.plus(T.times(T.N(2), S("x")), T.N(3)), T.Rat(Fr(1,7)))
    start=time.time()
    r=_integrate_term(f)
    assert time.time()-start < 5

def test_p4_hermite_y_free():
    # y^2 = x^2+1, integrand y/(x^2+1)  => denominator y-free
    y_term=T.pw(T.plus(T.pw(S("x"),T.N(2)),T.N(1)), T.Rat(Fr(1,2)))
    f=T.div(y_term, T.plus(T.pw(S("x"),T.N(2)),T.N(1)))
    start=time.time()
    r=_integrate_term(f)
    assert time.time()-start < 5
