# -*- coding: utf-8 -*-
"""REPL 会话（组装门面）：Session = 四个 Mixin 合成。

拆分布局（M6.7）：
    cas/session_core.py      SessionBase——状态/账本/规则应用/撤销重放
    cas/session_cmds.py      模块级内核命令 handler + 惰性求值助手
    cas/session_kernel.py    KernelOpsMixin——! 前缀算法入口与 :value 族
    cas/session_manual.py    ManualOpsMixin——手动结构操作与微积分战术
    cas/session_dispatch.py  DispatchMixin——分发/帮助表/转录 DSL
本文件只做组装并保留历史导入面（Session/Obligation/run 等）。
"""

from cas.session_core import SessionBase, Obligation
from cas.session_kernel import KernelOpsMixin
from cas.session_manual import ManualOpsMixin
from cas.session_dispatch import DispatchMixin

# 兼容面：测试与外部代码曾从本模块引用这些名字
from cas.session_cmds import (
    KernelCmd, _eval_inert, _quotient_cancel,
    _neg_pow_of, _const_exact,
    _k_apart, _k_isteps, _k_bsub, _k_together, _k_collect,
    _k_num_den, _k_mulfrac, _k_coefficient,
    _k_verify, _k_solve, _k_factor, _k_integrate, _k_dsolve,
    _k_limit, _k_series, _k_defint, _k_sum, _k_msolve, _k_gsolve,
    _k_solveineq, _k_solveset,
)


class Session(DispatchMixin, ManualOpsMixin, KernelOpsMixin, SessionBase):
    pass


def run():
    """REPL：表达式即当前式；%N 复用历史产出；命令转录可保存/回放。
    分发全部走 Session.handle（与回放同路径）。"""
    s = Session()
    print("pyCAS session. :help for commands; expression to make current; %N reuses history.")
    if s.load_error:
        print(f"warning: rules load failed: {s.load_error}")
    while True:
        try:
            line = input(">> ")
        except EOFError:
            break
        if line.strip() in (":q", ":quit"):
            break
        out = s.handle(line)
        if out:
            print(out)


if __name__ == "__main__":
    run()
