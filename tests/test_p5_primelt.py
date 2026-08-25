import pytest
from fractions import Fraction as Fr
from cas.primelt import compress_chain, primitive_pair
from cas.term import S
from cas.poly import Poly

def test_primelt_2():
    # Q(sqrt2, sqrt3) -> Q(beta)
    mA=[Fr(-2),Fr(0),Fr(1)] # x^2-2
    mB=[Fr(-3),Fr(0),Fr(1)] # x^2-3
    res=primitive_pair(mA,mB, cap=12)
    assert res is not None
    Scoefs,c,ma,mb=res
    # deg should be 4
    assert len(Scoefs)-1==4

def test_primelt_3_chain():
    m2=[Fr(-2),Fr(0),Fr(1)]
    m3=[Fr(-3),Fr(0),Fr(1)]
    m5=[Fr(-5),Fr(0),Fr(1)]
    terms=[S("r2"),S("r3"),S("r5")]
    # mock terms as Power(2,1/2) etc. but compress_chain expects terms for origin
    # Use Poly origin directly via af_q, so we supply dummy terms with args
    from cas.term import S as _S
    from cas import term as T
    t2=T.mk(_S("Power"), (T.N(2), T.Rat(Fr(1,2))))
    t3=T.mk(_S("Power"), (T.N(3), T.Rat(Fr(1,2))))
    t5=T.mk(_S("Power"), (T.N(5), T.Rat(Fr(1,2))))
    res=compress_chain([m2,m3,m5],[t2,t3,t5], cap=8)
    assert res is not None
    Scoefs,maps,beta=res
    # 3 quadratics => up to 8 deg
    assert len(Scoefs)-1==8
    # maps length 3
    assert len(maps)==3

def test_primelt_mixed_deg():
    # Q(cuberoot2, sqrt3)
    mA=[Fr(-2),Fr(0),Fr(0),Fr(1)] # x^3-2
    mB=[Fr(-3),Fr(0),Fr(1)] # x^2-3 => deg 6
    res=primitive_pair(mA,mB, cap=12)
    assert res is not None
    Scoefs,_,_,_=res
    assert len(Scoefs)-1==6

def test_primelt_pressure_many():
    # 4 leavs: sqrt2,sqrt3,sqrt5,sqrt7 => deg 16
    ms=[[Fr(-p),Fr(0),Fr(1)] for p in [2,3,5,7]]
    from cas import term as T
    from cas.term import S as _S
    terms=[T.mk(_S("Power"), (T.N(p), T.Rat(Fr(1,2)))) for p in [2,3,5,7]]
    res=compress_chain(ms, terms, cap=8)
    # may be 16 or honest None due to cap, but not hang
    assert res is None or len(res[0])-1==16

def test_p4_strengthen_hermite_contains_y():
    from cas.risch_core import build_extension
    from cas import term as T
    from cas.term import S as _S
    from fractions import Fraction as Fr
    x=_S("x")
    # y^2 = x^2+1, integrand y/(x) with denominator containing y? Actually y in numerator, still test hermite path
    f=T.div(T.mk(_S("Power"), (T.plus(T.pw(x,T.N(2)),T.N(1)), T.Rat(Fr(1,2)))), x)
    from cas.intalg import hermite_algebraic
    de,fa,fd=build_extension(f, x)
    # find algebraic level
    for j,case in enumerate(de.cases):
        if case=="algebraic":
            h=hermite_algebraic(fa,fd,de,j)
            # hermite should not crash, either None or tuple
            assert h is None or isinstance(h, tuple)
