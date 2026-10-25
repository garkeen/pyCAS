# Test taxonomy

Tests are classified by directory; `tests/conftest.py` mirrors the directory
onto a pytest marker so a kind is also selectable with `-m`.

| Directory | Marker | What lives here |
|---|---|---|
| `tests/unit/` | `unit` | One module or a few coupled value objects; deterministic, fixed inputs. |
| `tests/integration/` | `integration` | Several v5 layers exercised together (frontend, workflow, kernel, checker). |
| `tests/property/` | `property` | Randomized self-certifying mathematics with fixed seeds: domain axioms, representation round-trips, algorithm certificates, specialization validity. |

There are no contract or name-scanning gates. Structural invariants are enforced
by construction and checked through behaviour, not by inspecting identifiers,
imports or AST names.

## Naming

- File: `test_<subject>.py` in the directory of its kind.
- Function: `test_<scenario>_<expected_behavior>`. The name states what is under
  test and what the right answer is.
- A regression test names the defect it pins in its module docstring.

## Running

```console
pytest                       # everything
pytest tests/unit            # one kind by path
pytest -m property           # one kind by marker
pytest tests/integration     # end-to-end slices
```

## Where a new test goes

- A module or boundary behaviour with fixed input → `tests/unit/`.
- A cross-layer behaviour (text → object → candidate → verification → history)
  → `tests/integration/`.
- A mathematical property with a randomized generator → `tests/property/`, with
  a fixed seed; sampling can find defects but never proves a general identity.
