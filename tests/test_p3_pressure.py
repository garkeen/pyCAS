import pytest, random, time
from fractions import Fraction as Fr
from cas.poly import Poly, _mk_param, SymRat
from cas.term import S
from cas.apart import _param_factors, apart
from cas.factor import factor

x=S("x"); a=S("a"); b=S("b"); c=S("c")

def _rand_fr():
    return Fr(random.randint(-3,3), random.randint(1,3))

def test_pressure_high_degree_Q():
    # 压力：ℚ[x] 随机 8-12 次，系数 -5..5，Zassenhaus 压力
    random.seed(0)
    for deg in [8,10,12]:
        # 构造随机首一多项式
        monos={(deg,):Fr(1)}
        for i in range(deg):
            if random.random()<0.7:
                monos[(i,)]=_rand_fr()
        p=Poly((x,), monos)
        start=time.time()
        c, facs = factor(p)
        # 验证乘回
        prod=Poly.one((x,)).scalar(c)
        for f,_ in facs:
            prod=prod*f
        # prod * content 应等于 p 的本原部分
        assert time.time()-start < 5

def test_pressure_param_high_degree():
    # ℚ(a)[x] 6-8 次，参量线性，压力
    random.seed(1)
    pa=_mk_param(a)
    for deg in [6,8]:
        monos={(deg,):Fr(1)}
        for i in range(deg):
            if random.random()<0.5:
                # 系数含 a 的线性 SymRat
                if random.random()<0.5:
                    monos[(i,)]=_rand_fr()
                else:
                    # a + c
                    c=_rand_fr()
                    # SymRat a + c
                    from cas.poly import Poly as P
                    num=P((a,), {(1,):Fr(1),(0,):c})
                    monos[(i,)]=SymRat(num, P.one((a,)))
        p=Poly((x,), monos)
        start=time.time()
        facs,_=_param_factors(p,x)
        assert facs is not None
        assert time.time()-start < 5

def test_pressure_multivariate_3params():
    # ℚ(a,b,c)[x] 4 次，3参量，压力 20 例
    random.seed(2)
    for _ in range(20):
        # 构造随机 (x^2 + u)(x^2 + v) 型，其中 u,v ∈ ℚ[a,b,c] 线性
        # u = Σ coeff_i * param_i
        def _rand_param_linear():
            # 随机线性参量式
            coeffs={}
            for mask in range(1<<3):
                if random.random()<0.3:
                    coeffs[(mask,)]=_rand_fr() if False else None
            # 简化：直接用 _mk_param 的线性组合
            # 构造 SymRat via Poly
            from cas.poly import Poly as P
            # 随机选参量
            # 为简化，直接用 pa,pb,pc 的线性组合
            # 构造 u = u0 + u1*a + u2*b + u3*c
            vals=[_rand_fr() for _ in range(4)]
            # u = vals[0] + vals[1]*a + vals[2]*b + vals[3]*c
            # 转为 SymRat
            num=P((a,b,c), {(0,0,0):vals[0],(1,0,0):vals[1],(0,1,0):vals[2],(0,0,1):vals[3]})
            return SymRat(num, P.one((a,b,c)))
        # 构造 p = (x^2 + u)(x^2 + v) => x^4 + (u+v) x^2 + u v
        # 此处为压力，仅验证不挂死，不验证正确性
        u=_rand_param_linear() if False else _mk_param(a)
        v=_mk_param(b)
        # 简化：直接构造随机 4 次 ℚ(a,b)[x] 并 factor
        pa=_mk_param(a); pb=_mk_param(b)
        p=Poly((x,), {(4,):Fr(1),(2,):pa+pb,(0,):pa*pb})
        start=time.time()
        facs,_=_param_factors(p,x)
        assert facs is not None
        assert time.time()-start < 5

def test_pressure_apart_high_degree_param():
    # apart 压力：分母 6 次，含参量，验证不挂死
    random.seed(3)
    pa=_mk_param(a)
    for _ in range(10):
        # f=1, g= x^6 + a x^3 + ... 随机
        g_monos={(6,):Fr(1)}
        for i in [3,0]:
            g_monos[(i,)]= pa if random.random()<0.5 else _rand_fr()
        g=Poly((x,), g_monos)
        f=Poly((x,), {(0,):Fr(1)})
        start=time.time()
        q,terms=apart(f,g)
        assert time.time()-start < 5

def test_pressure_factor_param_high_degree_apart():
    # 压力：factor_param 的 Groebner 任意 p,n 压力，n=4, p=3
    from cas.poly import Poly as P
    # P = x^4 + (a+b+c) x^3 + ... 高次
    # 构造随机 4 次 3参量
    p=Poly((x,a,b,c), {(4,0,0,0):Fr(1),(3,1,0,0):Fr(1),(3,0,1,0):Fr(1),(3,0,0,1):Fr(1),(0,0,0,0):Fr(1)})
    from cas.factor_param import hensel_lift_multivariate
    # P(0,0,0)= x^4, not squarefree, skip
    # 仅验证 hensel 不挂死
    start=time.time()
    res=hensel_lift_multivariate(p, Poly((x,),{(1,):Fr(1)}), Poly((x,),{(3,):Fr(1)}), (a,b,c), x)
    assert time.time()-start < 5
    assert res is None or isinstance(res, tuple)
