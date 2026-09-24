import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[2]))

from cas.frontend.parser import parse
from cas.runtime import bootstrap, new_workflow
from cas.workflow.command import Claim, Use


def main() -> None:
    runtime = bootstrap()
    for _ in range(20):
        workflow = new_workflow(runtime)
        source = workflow.add(parse(runtime, "u0 == u1"), Claim())
        target = workflow.add(parse(runtime, "u0 + u2 == u3"), Claim())
        lifted = workflow.add(
            parse(runtime, "u1 + u2 == u3"),
            Use(
                source=source.id,
                direction="->",
                path=(0, 0),
                target=target.id,
                premises=(source.id, target.id),
            ),
        )
        assert lifted.status == "committed"
    print("random congruence passed")


if __name__ == "__main__":
    main()
