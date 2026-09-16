# Local validation and pending review

Execution date: 2026-09-16. Official baseline:
`f4e7173d89dfe91022a185427d63452c8ffbf6ae`.
Public submitter: @linmanshan050813-dotcom. Recipient confirmation: pending.

## Environment and Lean results

Windows x86-64, Lean 4.34.0, Lake 5.0.0-src+293d5d0.
Lean commit: `293d5d0c0c3f3dded4688b3ccd6a33939ac5102b`.
Mathlib commit: `5ed2965256430c3649e86755f9576b54eca72435`.
Python 3.12.10, with repository requirements installed in an isolated
virtual environment: PyYAML 6.0.3, jsonschema 4.26.0, markdown-it-py 3.0.0.

`lean/REPRODUCE.ps1 -SkipCache` completed successfully in this submission's
Lean directory. Its fresh build compiled both proof modules and the root
module. Existing mathlib dependency artifacts were reused via an ignored
local directory junction; this was not an isolated or independent rebuild
of every dependency from source. No toolchain or dependency cache is included.
The default reproduction command fetches the pinned dependency cache itself.
The manifest hash was unchanged before and after reproduction.

| Check | Result | Evidence |
| --- | --- | --- |
| `lake build` | PASS, 8927 jobs in the build graph | [lean-build.log](evidence/lean-build.log) |
| `lake env lean Audit.lean` | PASS, 21 transitive axiom reports | [axioms.log](evidence/axioms.log) |
| Forbidden constructs in project Lean sources | No matches | [source-scan.log](evidence/source-scan.log) |
| Combined reproduction script | PASS | [result.log](evidence/result.log) |

The source scan rejects `sorry`, `admit`, custom `axiom` declarations and
`native_decide`. It is a supplemental text check, not a substitute for kernel
checking. The 21 audited declarations report only `propext`,
`Classical.choice`, and/or `Quot.sound`; none reports `sorryAx` or a custom
axiom. `Audit.lean` lists the declarations explicitly. This audit does not
close the model-to-graph gaps documented in [proof.md](proof.md).

## Repository checks

All commands ran from the repository root using its virtual-environment
Python. The logs below include actual exit codes.

| Command | Result | Evidence |
| --- | --- | --- |
| `python scripts/manage.py validate` | PASS, exit 0 | [validate log](evidence/repository-validate.log) |
| `python scripts/manage.py links` | PASS, exit 0 | [links log](evidence/repository-links.log) |
| `python scripts/manage.py build` | PASS, exit 0; generated JSON unchanged | [build log](evidence/repository-build.log) |
| `python scripts/manage.py check` | PASS, exit 0 | [check log](evidence/repository-check.log) |
| `python -m unittest discover -s tests -v` | FAIL, exit 1; 22 tests, 19 passed, 1 failure, 2 errors | [test log](evidence/repository-unittest.log) |
| `python scripts/manage.py history --base f4e7173d89dfe91022a185427d63452c8ffbf6ae` | PASS, exit 0 | [history log](evidence/repository-history.log) |

The same test command in a separate, unmodified checkout of the official
baseline produced the same three affected tests: [baseline log](evidence/baseline-unittest.log).
The submission does not modify the repository scripts, tests, or data indexes.

| Affected test | Observed cause on Windows |
| --- | --- |
| `test_published_statement_immutable_and_superseded` | Expected `InvalidRecord` was not raised. `check_history` compares a Windows backslash path to Git paths using forward slashes, bypassing the expected statement check. |
| `test_revocation_keeps_original_evidence` | `git show` cannot find the record at the Windows backslash path constructed by `check_history`. |
| `test_symlinks_and_misplaced_records_rejected` | Creating the test symlink raises Windows error 1314 (required privilege unavailable). |

No tests were skipped or patched to obtain a passing result. A Linux test
run and independent reproduction remain pending. The passing `history`
command on the present records does not establish that these failing test
scenarios work on Windows.

The repository's `links` command checks its configured directories and does
not include this new `submissions/` tree. Repository validation and generated
indexes likewise do not register it as a formal candidate. Additional package
checks are recorded in [package-checks.log](evidence/package-checks.log).
External URL availability is not certified by the offline link checker.

## Evidence handling

Small local build and audit logs accompany the source to support intake.
Test-log machine paths are replaced with `<REPOSITORY>`,
`<BASELINE_REPOSITORY>` and `<USER_HOME>`; diagnostics, test outcomes and
exit status are retained. Raw local-path logs are not submitted.

`SHA256SUMS` lists the exact bytes of every submitted file except itself.
`ARTIFACTS.tsv` records file sizes and SHA-256 values, excluding itself and
`SHA256SUMS` to avoid circular manifests. The attributes file disables
Git line-ending conversion for this evidence directory.

No permanent external archive has been created: archive ID and public
archive URL are pending. These local manifests are not external archival
attestations. The repository's record guide calls for permanent external
artifacts when completing formal verification records.

## Still pending

Maintainer acceptance, permanent archive, independent proof reproduction,
graph-path and cost correspondence formalization/review, full statement
comparison to the original conjecture, authorized review signatures,
contribution/novelty/conflict review, and recipient confirmation are pending.
The submitter's GitHub account is a public submission identity only.

This package neither announces an award nor asserts payment eligibility.
Passing local checks is not official mathematical verification.
