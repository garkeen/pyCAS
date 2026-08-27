"""常数定义。性质声明是引理（可判定粗界与正性），不是公理废话：
每一条都对应 decide 管线可机械使用的判定素材。

出口为原子（Const 对象），不是 Decl——内核与 parser 直接当项用。
"""

from fractions import Fraction as Fr

import library.api as lib

PI = lib.constant(name="pi", print_name="π", real=True, positive=True,
                  bounds=(3, 4)).atom
E = lib.constant(name="e", print_name="e", real=True, positive=True,
                 bounds=(2, 3)).atom
IU = lib.constant(name="i", print_name="i", real=False).atom
GAMMA = lib.constant(name="gamma", print_name="γ", real=True, positive=True,
                     bounds=(0, 1)).atom
