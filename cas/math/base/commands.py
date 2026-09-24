"""User-visible command descriptors.

The frontend consumes these descriptors for dispatch and help; mathematical
modules do not import the frontend and therefore register data only.
"""

COMMANDS = (
    ("help", "show this help", "", "-"),
    ("both", "apply add/sub/mul/div to both sides", "op expr step_ref", "both_sides.operate"),
    ("norm", "rewrite to the domain normal form", "step_ref", "equality.normalize"),
    ("solve", "solve a linear equation", "var step_ref", "solve.back_substitute"),
    ("subst", "substitute a variable", "var=expr step_ref", "substitute"),
    ("split", "split into a branch condition", "condition step_ref", "branch.split"),
    ("use", "use an equality at a target path", "source direction path target", "congruence.lift"),
    ("trans", "compose two equalities", "step_ref step_ref", "equality.trans"),
    ("diff", "differentiate", "var step_ref", "calculus.derivative"),
    ("integrate", "find an antiderivative", "var step_ref", "calculus.antiderivative"),
    ("int", "compute a definite integral", "var lower upper step_ref", "calculus.antiderivative"),
    ("rules", "list declared rules", "", "-"),
    ("apply", "apply a declared rule", "rule step_ref", "rule.instance"),
    ("check", "verify a solution step", "step_ref", "-"),
    ("steps", "list visible steps", "", "-"),
    ("show", "show a step", "step_ref", "-"),
    ("enter", "enter a branch scope", "branch", "-"),
    ("merge", "merge branch results", "step_ref step_ref", "branch.merge"),
    ("focus", "show or set the focus", "step_ref", "-"),
    ("undo", "move one revision back", "", "-"),
    ("quit", "leave the REPL", "", "-"),
)


def install(builder):
    for name, help_text, args, checker_id in COMMANDS:
        builder.register_command(name, help_text, args, checker_id)
