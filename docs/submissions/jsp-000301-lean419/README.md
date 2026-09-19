# JSP-000301 — Lean 4.19 source and submission evidence

## English

This is an AI-assisted formalization of the **known** counterexample involving
12167 and 12168. The submitted result is a disproof of the scoped square-implication
question, not a new discovery and not a solution to the counting problem in Erdős #365.
See the [statement and definition correspondence](FORMAL_STATEMENT.md).

**Submission state:** source and local verification evidence prepared for review.
No official verification, recipient confirmation, first-formalization priority,
award decision, or payment is asserted. Related public submissions are disclosed
in [PROVENANCE.md](PROVENANCE.md).

## Main files

- `JSP301.lean`: definitions, all proofs, and both `#print axioms` commands.
- `lean-toolchain`, `lakefile.lean`, `lake-manifest.json`: pinned project configuration.
- `scripts/verify.py`: checks versions and dependency commits, compiles the actual
  source, audits the final theorem axioms, and checks that a false statement fails.
- `evidence/submission_check/`: logs from this exact submission package.
- `evidence/prior_check/`: earlier actual check of the original comment variant.
- [VERIFICATION.md](VERIFICATION.md): results and trust limitations.

The project has no `sorry`, `admit`, custom axioms, or `native_decide` in its proof.
The deliberately false file in `tests/NegativeControl.lean` is not part of the Lean
library target. Its failure is an expected test result.

## Pinned environment

Lean `4.19.0`; Lake `5.0.0-6caaee8`; Mathlib `v4.19.0`, commit `c44e0c8ee63ca166450922a373c7409c5d26b00b`.
All nine dependency revisions are in `lake-manifest.json`.
The actual submission check ran on Linux x86_64. Other operating systems were
not tested in this submission check.

## Reproduction from publicly obtainable dependencies

Use an existing Lean installation that can select the version in `lean-toolchain`.
Run the following **from this project directory**, not from the awards repository root:

```sh
lean --version
lake exe cache get
python3 scripts/verify.py --also-lake-build
```

The dependency-preparation command may use the network. It is not an offline test.
Preserve `lake-manifest.json`; do not upgrade the project or run an unpinned dependency
update. The verification script requires every dependency HEAD to match the lockfile
and rejects modified tracked dependency source files.

Once the exact dependencies and caches are already installed, the actual checks are:

```sh
lake build JSP301
lake env lean tests/SmokeTest.lean
mkdir -p .verification
lake env lean -o .verification/JSP301.olean JSP301.lean
lake env lean tests/NegativeControl.lean
```

The final command must return exit code 1 with an unsolved `False` goal. All preceding
commands must return 0. Prefer `scripts/verify.py`, which handles output directories
and validates the results automatically. Its logs go to `.verification/` by default.

On Linux x86_64, the optional process-level network guard can be used after the
pinned dependencies are present:

```sh
python3 scripts/seccomp_no_network_exec.py python3 scripts/verify.py --also-lake-build
```

The guard requires seccomp support and verifies that IPv4/IPv6 socket creation
returns EPERM. It does not create a network namespace or recheck imported Mathlib
artifacts with an independent proof checker.

## Source identity and review

Submitted `JSP301.lean` SHA-256:

```text
20c09dc7edfefb64634da5f17962fd9c528662c615538400ad1bd744686f53dc
```

Both `JSP301.known_counterexample` and `JSP301.catalog_statement_false` report exactly
`propext`, `Classical.choice`, and `Quot.sound`. No `sorryAx` is present in either
transitive axiom set. These are not axiom-free proofs.

The proposed contribution directory is `docs/submissions/jsp-000301-lean419/`.
That is a proposed placement for this PR, not a directory mandated by the prize.
This submission does not edit the catalog, candidate records, award records, or
recipient profiles. Maintainers may request a different layout or additional checks.

References: [catalog](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0301-0400.md#JSP-000301), [verification guidance](https://github.com/TheJustinSunPrize/awards/blob/main/docs/verification.md),
[contribution guidance](https://github.com/TheJustinSunPrize/awards/blob/main/CONTRIBUTING.md), and
[Lean project setup](https://leanprover-community.github.io/install/project.html).
No Lean compiler, Mathlib source tree, dependency cache, or credentials are included
in this source contribution. No new licensing restrictions are imposed here;
contributions to the target repository remain subject to its published licensing
and contribution terms, which the actual submitter must review before posting.
