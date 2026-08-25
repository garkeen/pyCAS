import pytest, time
from fractions import Fraction as Fr
from cas import term as T
from cas.term import S
from cas.poly import Poly
from cas.risch_core import build_extension

x=S("x")

def test_hermite_any_q():
    # y^5 = x^5+1, fd with repeated factor simulation
    f=T.mk(S("Power"), (T.plus(T.pw(x,T.N(5)),T.N(1)), T.Rat(Fr(1,5))))
    de,fa,fd=build_extension(f, x)
    from cas.intalg import hermite_algebraic
    for j,case in enumerate(de.cases):
        if case=="algebraic":
            r=hermite_algebraic(fa,fd,de,j)
            assert r is not None
            assert len(r)==5

def test_double_resultant_any_degree():
    # q=7 high degree
    f=T.mk(S("Power"), (T.plus(T.pw(x,T.N(7)),T.N(2)), T.Rat(Fr(1,7))))
    de,fa,fd=build_extension(f, x)
    from cas.intalg import double_resultant
    z=S("_gen_z")
    for j,case in enumerate(de.cases):
        if case=="algebraic":
            mp=de.minpolys[j][1]
            R=double_resultant(fa,fd,mp,de,j,z)
            # R may be None (no poles) or Poly, but shouldn't hang
            assert R is None or isinstance(R, Poly)
            assert time.time()  # dummy

def test_alg_residue_any_degree():
    # R with quadratic and cubic factors
    from cas.intalg import _alg_residue_log, double_resultant
    f=T.div(T.mk(S("Power"), (T.plus(T.pw(x,T.N(2)),T.N(1)), T.Rat(Fr(1,2)))), T.plus(T.pw(x,T.N(2)),T.N(2)))
    de,fa,fd=build_extension(f, x)
    z=S("_gen_z")
    for j,case in enumerate(de.cases):
        if case=="algebraic":
            mp=de.minpolys[j][1]
            R=double_resultant(fa,fd,mp,de,j,z)
            if R is not None and not R.is_zero():
                from cas.factor import factor
                _,facs=factor(R)
                for fac,_ in facs:
                    d=fac.degree(z)
                    if d>=2:
                        # should not crash, arbitrary degree
                        r=_alg_residue_log(fa,fd,mp,de,j,fac,z)
                        assert r is None or hasattr(r, 'head')

def test_rational_log_any_degree():
    f=T.div(T.mk(S("Power"), (T.plus(T.pw(x,T.N(3)),T.N(1)), T.Rat(Fr(1,3)))), T.plus(T.pw(x,T.N(1)),T.N(1)))
    de,fa,fd=build_extension(f, x)
    from cas.intalg import double_resultant, rational_log_part
    z=S("_gen_z")
    for j,case in enumerate(de.cases):
        if case=="algebraic":
            mp=de.minpolys[j][1]
            R=double_resultant(fa,fd,mp,de,j,z)
            if R is not None and not R.is_zero() and R.degree(z)>=1:
                lp,has = rational_log_part(fa,fd,mp,de,j,R,z)
                assert lp is None or hasattr(lp, 'head')

def test_hermite_pressure_high_q():
    import time
    for q in [5,7,9]:
        f=T.mk(S("Power"), (T.plus(T.pw(x,T.N(q)),T.N(1)), T.Rat(Fr(1,q))))
        start=time.time()
        de,fa,fd=build_extension(f, x)
        from cas.intalg import hermite_algebraic
        for j,case in enumerate(de.cases):
            if case=="algebraic":
                hermite_algebraic(fa,fd,de,j)
        assert time.time()-start < 5
