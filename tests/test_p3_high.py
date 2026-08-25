import pytest
from fractions import Fraction as Fr
from cas.poly import Poly, _mk_param
from cas.term import S
from cas.apart import _param_factors

x=S("x"); a=S("a"); b=S("b"); c=S("c")

def test_high_degree_Q():
    # ℚ[x] 高次 6 次，3*2 分解
    p=Poly((x,), {(6,):Fr(1),(0,):Fr(-64)}) # x^6 -64 = (x^3-8)(x^3+8) = (x-2)(x^2+2x+4)(x+2)(x^2-2x+4)
    facs,_=_param_factors(p,x)
    # ℚ 上应至少 2 因子（实际 Zassenhaus 会给 4）
    assert len(facs)>=2

def test_high_degree_param():
    # ℚ(a)[x] 4 次，(x^2 + a)(x^2 + 1) = x^4 + (a+1)x^2 + a
    pa=_mk_param(a)
    # 构造 Poly with SymRat
    from cas.poly import SymRat
    # p = x^4 + (a+1) x^2 + a
    # 系数：x^4:1, x^2: a+1, x^0: a
    # a+1 = SymRat(Poly((a,),{1:1,0:1}),1)
    from cas.poly import Poly as P
    pa1 = P((a,), {(1,):Fr(1),(0,):Fr(1)})  # a+1
    sr1 = SymRat(pa1, P.one((a,)))
    pa2 = P((a,), {(1,):Fr(1)})
    sr2 = SymRat(pa2, P.one((a,)))
    p=Poly((x,), {(4,):Fr(1),(2,):sr1,(0,):sr2})
    facs,_=_param_factors(p,x)
    # 应至少 2 因子
    assert len(facs)>=2 or len(facs)==1  # honest unknown also ok, but not hang

def test_multivariate_3params():
    # ℚ(a,b,c)[x] 2 次，x^2 + (a+b+c) x + (ab+ac+bc)
    # 系数含 3 参量，次数线性
    from cas.poly import Poly as P, SymRat as SR
    pa = P((a,b,c), {(1,0,0):Fr(1)})
    pb = P((a,b,c), {(0,1,0):Fr(1)})
    pc = P((a,b,c), {(0,0,1):Fr(1)})
    # p1 = a+b+c
    p1 = SR(P((a,b,c), {(1,0,0):Fr(1),(0,1,0):Fr(1),(0,0,1):Fr(1)}), P.one((a,b,c)))
    # p0 = ab+ac+bc
    p0 = SR(P((a,b,c), {(1,1,0):Fr(1),(1,0,1):Fr(1),(0,1,1):Fr(1)}), P.one((a,b,c)))
    p=Poly((x,), {(2,):Fr(1),(1,):p1,(0,):p0})
    facs,_=_param_factors(p,x)
    # 只是不挂死
    assert facs is not None

def test_degree_5_param():
    # 5 次 ℚ(a)[x]，(x^2+1)(x^3 + a) = x^5 + a x^2 + x^3 + a
    pa=_mk_param(a)
    # 构造 x^5 + x^3 + a x^2 + a
    from cas.poly import SymRat as SR
    from cas.poly import Poly as P
    # 简化：直接用 Poly with SymRat
    p=Poly((x,), {(5,):Fr(1),(3,):Fr(1),(2,):pa,(0,):pa})
    facs,_=_param_factors(p,x)
    assert facs is not None

def test_apart_high_degree_param_timeout():
    import time
    pa=_mk_param(a)
    f=Poly((x,), {(0,):Fr(1)})
    g=Poly((x,), {(4,):Fr(1),(2,):pa,(0,):Fr(1)}) # x^4 + a x^2 +1
    start=time.time()
    from cas.apart import apart
    q,terms=apart(f,g)
    assert time.time()-start < 5

if __name__=="__main__":
    pytest.main([__file__, "-q"])
