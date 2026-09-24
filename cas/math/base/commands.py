"""Typed user-visible command metadata."""

from cas.math.builder import CommandSpec, MathBuilder

COMMANDS = (
    CommandSpec("help", "show this help", "", None),
    CommandSpec("both", "apply add/sub/mul/div to both sides", "op expr step_ref", "both_sides.operate"),
    CommandSpec("norm", "rewrite to the domain normal form", "step_ref", "equality.normalize"),
    CommandSpec("solve", "solve a linear equation", "var step_ref", "solve.back_substitute"),
    CommandSpec("subst", "substitute a variable", "var=expr step_ref", "substitute"),
    CommandSpec("split", "split into a branch condition", "condition step_ref", "branch.split"),
    CommandSpec("use", "use an equality at a target path", "source direction path target", "congruence.lift"),
    CommandSpec("trans", "compose two equalities", "step_ref step_ref", "equality.trans"),
    CommandSpec("diff", "differentiate", "var step_ref", "calculus.derivative"),
    CommandSpec("integrate", "find an antiderivative", "var step_ref", "calculus.antiderivative"),
    CommandSpec("int", "compute a definite integral", "var lower upper step_ref", "calculus.antiderivative"),
    CommandSpec("rules", "list declared rules", "", None),
    CommandSpec("apply", "apply a declared rule", "rule step_ref", "rule.instance"),
    CommandSpec("check", "verify a solution step", "step_ref", None),
    CommandSpec("steps", "list visible steps", "", None),
    CommandSpec("show", "show a step", "step_ref", None),
    CommandSpec("enter", "enter a branch scope", "branch", None),
    CommandSpec("merge", "merge branch results", "step_ref step_ref", "branch.merge"),
    CommandSpec("focus", "show or set the focus", "step_ref", None),
    CommandSpec("undo", "move one revision back", "", None),
    CommandSpec("quit", "leave the REPL", "", None),
)


def install(builder: MathBuilder) -> None:
    """Register command metadata without importing frontend wiring."""
    for command in COMMANDS:
        builder.register_command(command)
