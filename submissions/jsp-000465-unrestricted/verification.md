# Local verification

Verified on 2026-09-17 with Lean 4.34.0 on Windows, using the pinned dependencies in [`lean/lake-manifest.json`](lean/lake-manifest.json).

## Formal proof

- `lake build`: successful; the `Erdos575` target compiled (1,303 jobs including cached dependencies).
- `python verify.py`: successful; it invokes Lean again and checks the final theorem's transitive axiom list.
- Final theorem: `Erdos575.not_unrestrictedCompactness`.
- Reported axioms: `propext`, `Classical.choice`, `Quot.sound`.
- No `sorryAx`, custom axioms, or native-evaluation axiom is present in that dependency list.
- Compiler and audit output: [`verification-output.txt`](verification-output.txt).

SHA-256 of [`lean/Erdos575.lean`](lean/Erdos575.lean):

```text
b6bf41d2b5e5184ca76b2c32f9b385762e664639e718d2eef6aa3830a8c6f8a3
```

SHA-256 of the dependency manifest:

```text
f3c7e65d720b891d6b502ea0175f0e0a56edc105fbe734e26aa2aaff60d7d755
```

The local build reused downloaded mathlib build artifacts and local dependency checkouts. This is a local compilation report, not an independent verifier attestation or a claim that all dependencies were rebuilt from source. The submitted manifest contains public Git URLs and pinned commits; it contains no local dependency paths.

## Repository checks

At base commit `f4e7173d89dfe91022a185427d63452c8ffbf6ae`:

- `python scripts/manage.py validate`: passed.
- `python scripts/manage.py links`: passed.
- `python scripts/manage.py build`: passed; generated data unchanged.
- `python scripts/manage.py check`: passed.
- `git diff --check`: passed.
- `PYTHONUTF8=1 python -m unittest discover -s tests -v`: 20 of 22 tests passed. The same two failures were reproduced in a separate, unmodified worktree of the base commit.

The existing Windows failures are `test_revocation_keeps_original_evidence` and `test_published_statement_immutable_and_superseded`. Both arise where `check_history` constructs Git tree paths using Windows backslashes rather than POSIX separators. No existing scripts or tests were modified by this submission. Without UTF-8 mode, additional pre-existing Windows encoding failures occur.

These checks validate the repository and proof build. Mathematical statement correspondence, novelty, prize scope, and acceptance remain matters for maintainer review. In particular, the connected-graph and forest-free variants are outside this proof's scope.
