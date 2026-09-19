# pyCAS elementary-module declarations
#
# All mathematical semantics are expressed as **data plus registration**: constants,
# functions, print names, derivative templates, and domain conditions are declared
# here, and the Python side only performs the assembly call. The admission discipline
# is therefore mechanically checkable against this **text** (see
# tests/test_declarations_dsl.py) rather than by reviewing registration statements.
#
# Grammar (cas/math/loader.py):
#   constant <Name> print "<print name>" [real [true|false]] [positive] [bounds <lo> <hi>]
#   function <Head> print "<print name>" arity <n> [real_on_real] [bounds <lo> <hi>]
#                   [zero_iff_arg_zero] [deriv "<template>"] [domain "<condition>"] [note "<text>"]
#   rule <id> = <lhs> -> <rhs> [guard <expr>] [prio N] [auto]
#   alias <surface> = <Head>      # surface notation -> canonical head
#   binder <Head>                 # canonical head whose surface word binds its second argument
#   role <role> = <Head>          # canonical head an algorithm fetches by role
#
# Admission discipline (checkable on the text):
#   * rules admit only **unconditional identities**; a rewrite carrying a domain
#     condition is not admitted and its reason goes into the note.
#   * derivative templates admit only what holds **unconditionally** relative to the
#     function's own domain; a branch-splitting one is left empty with the reason
#     recorded (the Abs derivative is written honestly as a Piecewise, since there is
#     no branch at u=0 and it is not differentiable there).
#   * automatic simplification applies only rules that are auto and **guard-free**.
#   * `@0` is the function argument slot (de Bruijn placeholder), instantiated by the
#     differentiation and domain layers.

# --- constants: the property declarations are lemmas (decidable coarse bounds and
# positivity), not axioms ---
constant pi    print "π" real positive bounds 3 4
constant e     print "e" real positive bounds 2 3
constant i     print "i" real false
constant gamma print "γ" real positive bounds 0 1

# --- functions ---
function Sin  print "sin" arity 1 real_on_real bounds -1 1 deriv "Cos(@0)"
function Cos  print "cos" arity 1 real_on_real bounds -1 1 deriv "-Sin(@0)"
function Tan  print "tan" arity 1 deriv "Cos(@0)^(-2)" note "tan(x) = sin(x)/cos(x), under cos(x) != 0"
function Sinh print "sinh" arity 1 real_on_real deriv "Cosh(@0)"
function Cosh print "cosh" arity 1 real_on_real deriv "Sinh(@0)"
function Tanh print "tanh" arity 1 real_on_real deriv "Cosh(@0)^(-2)"
function Exp  print "exp" arity 1 real_on_real deriv "Exp(@0)" note "the principal-branch identity Exp(Log(u)) is a conditional rewrite, not admitted"
function Log  print "log" arity 1 deriv "@0^(-1)" domain "@0 > 0" note "splitting Log(uv) is a branch-breaking rewrite, not admitted"
function Sqrt print "sqrt" arity 1 deriv "(1/2)*@0^(-1/2)" domain "@0 >= 0" note "principal square root; sqrt(x^2) = +-x breaks branches, not admitted"
function Abs  print "abs" arity 1 real_on_real bounds 0 none zero_iff_arg_zero deriv "Piecewise(1, @0 > 0, -1, @0 < 0)" note "D|x| = piecewise(1 if x>0, -1 if x<0); no branch at x=0 (not differentiable)"
function Atan print "atan" arity 1 real_on_real deriv "(1+@0^2)^(-1)" note "range (-pi/2, pi/2): the exact pi-bearing bounds await a constant-lemma combination"

# --- surface aliases (parser notation -> canonical head) ---
# The parser holds no case convention and no notation of its own: every lowercase
# surface word is an explicit entry here, so the notation of a function is declared
# data and a new notation needs no parser change.
alias sin  = Sin
alias cos  = Cos
alias tan  = Tan
alias sinh = Sinh
alias cosh = Cosh
alias tanh = Tanh
alias exp  = Exp
alias log  = Log
alias abs  = Abs
alias atan = Atan
alias ln   = Log
alias sqrt = Sqrt

# --- binder words: whose surface word binds its second argument ---
# `binder` marks the canonical head; the word itself is an alias entry above.
# The bound form is word(body, var) -> Head(Bound(var, body)), and any further
# argument follows the bound body, so the definite integral prints and parses as
# int(body, var, lo, hi) -> DefIntegrate(Bound(var, body), lo, hi).
alias integrate = Integrate
alias sum       = Sum
alias product   = Product
alias limit     = Limit
alias int       = DefIntegrate
binder Integrate
binder Sum
binder Product
binder Limit
binder DefIntegrate

# --- canonical functions algorithms refer to by role (role -> head, so no algorithm
# hardcodes a function name) ---
role logarithm = Log

# --- rules (unconditional identities; an auto rule must be guard-free) ---
rule exp_add = Exp(?a)*Exp(?b) -> Exp(?a + ?b) auto
