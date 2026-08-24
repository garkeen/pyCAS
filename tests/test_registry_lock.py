# -*- coding: utf-8 -*-
"""M6.5 文档-现实锁定：声明注册表与导出面的一致性测试。

背景：v3 设计文档曾声称 SOLVERS 已实现而代码中并不存在（虚报）。
本文件把"文档声明的面"钉进测试——声明与实现漂移时在此爆红，
而不是在下一次重构时踩空。

锁定对象：
1. cas_v2_arch.md §5 模块清单中列出的每个文件必须真实存在
2. DOMAIN_DECLS 登记的每个模块可导入
3. 四大注册表（SOLVERS / VERIFY_STAGES / PRE_PASSES / _EQ_STAGES）
   的成员、顺序、门控与 arch §1 声明逐项一致
4. scalarutil / univar 两个提取模块的公开函数面完整
"""

import os
import re

import pytest

CAS_DIR = os.path.join(os.path.dirname(os.path.dirname(__file__)), "cas")


# ---------------------------------------------------------------------------
# 1. arch §5 模块清单 <-> 磁盘现实
# ---------------------------------------------------------------------------

def _arch_module_table_tokens():
    """解析 arch §5 模块表第一列 -> 模块名集合（支持斜杠分组行）。"""
    path = os.path.join(os.path.dirname(CAS_DIR), "docs", "cas_v2_arch.md")
    src = open(path, encoding="utf-8").read()
    i = src.find("## 5. 模块清单")
    j = src.find("## 6.", i)
    toks = set()
    nrows = 0
    for ln in src[i:j].splitlines():
        m = re.match(r"\|\s*([\w./]+?)\s*\|", ln)
        if not m or m.group(1) in ("文件", "---", ""):
            continue
        if not re.match(r"[\w./]+$", m.group(1)):
            continue
        nrows += 1
        for tok in m.group(1).split("/"):
            toks.add(tok[:-3] if tok.endswith(".py") else tok)
    assert nrows >= 10, f"模块表解析异常：仅 {nrows} 行"
    return toks


def test_arch_module_table_files_exist():
    for name in _arch_module_table_tokens():
        p = os.path.join(CAS_DIR, name if name.endswith(".py")
                         else name + ".py")
        assert os.path.exists(p), \
            f"arch §5 声明的 {name} 不存在——文档虚报或文件已移"


def test_no_unlisted_py_files():
    """反向锁：cas/ 下的 .py 文件都应在 §5 表中登记（包初始化除外）。"""
    declared = _arch_module_table_tokens()
    actual = {f[:-3] for f in os.listdir(CAS_DIR)
              if f.endswith(".py") and f not in ("__init__.py",
                                                 "__main__.py")}
    unlisted = actual - declared
    assert not unlisted, \
        f"未在 arch §5 登记的新模块：{sorted(unlisted)}——先补文档再合码"


# ---------------------------------------------------------------------------
# 2. DOMAIN_DECLS <-> 可导入性
# ---------------------------------------------------------------------------

def test_domain_decls_shape():
    """DOMAIN_DECLS：声明完整性 + 可导入键必须真实可导入。

    键是能力名（integrate_rational/msolve 等并非模块文件名），
    仅当 cas/<key>.py 存在时才做导入断言。"""
    import cas.domain_decls as dd  # noqa: F401  导入即登记
    from cas.structure import DOMAIN_DECLS

    assert len(DOMAIN_DECLS) >= 13, "域声明登记数量异常缩水"
    for mod, decl in DOMAIN_DECLS.items():
        assert "base" in decl and "layers" in decl, f"{mod} 声明不完整"
        if os.path.exists(os.path.join(CAS_DIR, mod + ".py")):
            __import__(f"cas.{mod}")
    # 裁定档案点名存在的声明不得删除
    for required in ("poly", "risch_tower", "integrate_rational",
                     "defint", "sturm"):
        assert required in DOMAIN_DECLS, f"缺少声明 {required}"


# ---------------------------------------------------------------------------
# 3. 注册表成员/顺序/门控
# ---------------------------------------------------------------------------

def test_solvers_table_shape():
    from cas.structs import (SOLVERS, StructEntry, QxStruct, TanHalfStruct,
                             TowerStruct)

    heads = SOLVERS[:5]
    entries = SOLVERS[5:]
    assert len(SOLVERS) == 8, "SOLVERS 总表形状漂移（五快速通道+三 Struct）"
    for h in heads:
        assert callable(getattr(h, "attempt", None))
    wrapped = [e.st for e in entries]
    assert all(isinstance(e, StructEntry) for e in entries)
    assert isinstance(wrapped[0], QxStruct)
    assert isinstance(wrapped[1], TanHalfStruct)
    assert isinstance(wrapped[2], TowerStruct)


def test_verify_stages_names_and_gates():
    from cas.structure import VERIFY_STAGES

    names = [s.name for s in VERIFY_STAGES]
    assert names == ["tower_zero", "ratpow_merge", "atomize_together"]
    by_name = dict(zip(names, VERIFY_STAGES))
    # principal 承诺位门控：tower 零判定无需假设；ratpow/atomize 需要
    ok, why = by_name["ratpow_merge"].gated(None)
    assert not ok and "principal" in why
    ok, why = by_name["atomize_together"].gated(None)
    assert not ok and "principal" in why
    ok, why = by_name["tower_zero"].gated(None)
    assert ok


def test_pre_passes_order():
    from cas.structure import PRE_PASSES

    assert [p.name for p in PRE_PASSES] == \
        ["num_power_norm", "ef_contract", "ef_expand_trans"]


def test_eq_stages_registration():
    """diff 导入后 tower_zero/ratpow_merge 必须已前插注册（判等视图）。"""
    import cas.diff  # noqa: F401  触发注册副作用
    from cas.decide import _EQ_STAGES

    names = [n for n, _run in _EQ_STAGES]
    assert names[:2] == ["tower_zero", "ratpow_merge"], \
        "diff 的两个判等视图未按 prepend 语义居于队首"
    for tail in ("trig_basis", "ledger_decide", "sampling"):
        assert tail in names


# ---------------------------------------------------------------------------
# 4. 提取模块公开面
# ---------------------------------------------------------------------------

def test_scalarutil_surface():
    import cas.scalarutil as su

    for fn in ("rf_const_ga", "ga_den", "lcm2", "ga_vec_to_ints",
               "mk_zero_like", "leaf_has_ga", "symrat_has_ga",
               "coef_zero", "coef_re_im", "poly_re_im"):
        assert callable(getattr(su, fn, None)), f"scalarutil.{fn} 缺失"
    for legacy in ("_rf_const_ga", "_coef_re_im", "_poly_re_im"):
        assert not hasattr(su, legacy), f"旧私有名 {legacy} 不应存在于新模块"


def test_univar_surface():
    import cas.univar as uv

    fns = ("from_poly", "u_add", "u_sub", "u_mul0", "u_mul", "u_neg",
           "u_pow", "u_deg", "u_trim", "u_divmod", "u_gcd", "u_xgcd",
           "u_inv_mod", "u_inv_mod_t", "u_is_zero", "u_deriv_x",
           "u_formal_deriv", "u_diophantine", "u_gauss_solve_k")
    for fn in fns:
        assert callable(getattr(uv, fn, None)), f"univar.{fn} 缺失"
