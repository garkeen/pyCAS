# -*- coding: utf-8 -*-
"""运行期包（v4 §三 `runtime/`）。

    registry.py   装配期注册表（RuntimeBuilder）——唯一写入口
    runtime.py    装配完成的只读查询面（Runtime）
    bootstrap.py  显式装配（bootstrap）——取代 import 期自注册
    dispatch.py   运行期查询入口（get_runtime + 查询函数）

`runtime` 是唯一允许导入全部数学模块的层（v4 §四）；数学模块只依赖
syntax / kernel / workflow / math.domains，**不得反向依赖 runtime**——
所以需要预计算状态的消费方（project 的基域阶梯、decide 的判定阶段）由
bootstrap 从外部绑定，而不是自己去查。
"""

from cas.runtime.bootstrap import bootstrap
from cas.runtime.dispatch import get_runtime, reset_runtime
from cas.runtime.registry import ConstantDecl, FunctionDecl, RuntimeBuilder
from cas.runtime.runtime import (Runtime, new_workflow,
                                 register_math_checkers)

__all__ = ("bootstrap", "get_runtime", "reset_runtime", "RuntimeBuilder",
           "Runtime", "ConstantDecl", "FunctionDecl", "new_workflow",
           "register_math_checkers")
