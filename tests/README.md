# Test taxonomy

Tests are classified by **kind**, one directory per kind. The directory is the
source of truth; `tests/conftest.py` mirrors it onto a pytest marker so a kind
is also selectable with `-m`.

| Directory | Marker | What lives here |
|---|---|---|
| `tests/unit/` | `unit` | One module, deterministic, isolated behavior. Fixed inputs, known outputs. |
| `tests/contract/` | `contract` | Architecture invariants, dependency-direction gates, DSL admission, the export surface. These fail on structural rot, not on math. |
| `tests/integration/` | `integration` | Several components exercised together (workflow + kernel + checkers, constraint solver + linalg, branch merge). |
| `tests/regression/` | `regression` | A nailed bug: a test that would have failed before the fix and passes after, kept so the same defect cannot return. |
| `tests/random/` | `random` | Randomized self-certifying math property benches. A generator builds expressions with a known answer; the domain decider checks the property. No external oracle. |

## Naming

- File: `test_<subject>.py`, placed in the directory of its kind. A random
  bench is `random_<subject>.py` (collected by `tests/random/test_random.py`).
- Function: `test_<scenario>_<expected_behavior>`. The descriptive name says
  what is under test and what the right answer is; a numbered name
  (`test_invariant1_...`) ties a contract test to a documented invariant.
- One assert per behavior where practical; a regression nail states the bug it
  pins in its module docstring.

## Running

```
pytest                       # everything
pytest tests/unit            # one kind by path
pytest -m contract           # one kind by marker
pytest -m "not random"       # deterministic only (skip the slow random benches)
pytest tests/regression      # the nailed bugs only
```

## Where a new test goes

- A new module behavior with a fixed input → `tests/unit/`.
- A new architecture rule that must not rot → `tests/contract/` (add a gate to
  `test_v4_invariants.py` when it is mechanically checkable).
- A bug you just fixed → `tests/regression/`, with a docstring naming the bug.
- A new math property with a randomized generator → `tests/random/`, named
  `random_<subject>.py` (the `test_random.py` collector picks it up automatically).
