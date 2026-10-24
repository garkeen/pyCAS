# pyCAS v5 elementary declarations.
#
# This file is data, not a proof. The assembler admits it as a trusted standard
# basis; a law is used automatically only when it is unconditional. Conditional
# laws and their stricter differentiability regions remain visible data and are
# refused until a condition service can discharge them.

constant pi : Real
constant e : Real

function sin : Real -> Real
function cos : Real -> Real
function exp : Real -> Real
function sqrt : Real -> Real on u >= 0
function log : Real -> Real on u > 0

derivative sin(u) = cos(u)
derivative cos(u) = -sin(u)
derivative exp(u) = exp(u)
derivative sqrt(u) = (1/2)*sqrt(u)^(-1) on u > 0
derivative log(u) = u^(-1) on u > 0
