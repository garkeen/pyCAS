"""Random equality congruence checks."""

import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[2]))

from cas.frontend.parser import parse
from cas.runtime import bootstrap, new_workflow
from cas.runtime.dispatch import install
from cas.workflow.command import Claim, Use


def main():
    install(bootstrap())
    for _ in range(20):
        wf = new_workflow()
        source = wf.add(parse("u0 == u1"), Claim())
        target = wf.add(parse("u0 + u2 == u3"), Claim())
        lifted = wf.add(parse("u1 + u2 == u3"), Use(
            source=source.id, direction="->", path=(0, 0), target=target.id,
            premises=(source.id, target.id)))
        assert lifted.status == "committed"
    print("random congruence passed")


if __name__ == "__main__":
    main()
