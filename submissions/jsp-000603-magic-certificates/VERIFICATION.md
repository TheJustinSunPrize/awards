# Observed local verification (2026-09-17)

All commands in `verification/verification.json` exited zero.

| Check | Observed result |
| --- | --- |
| Compiler and dependency pins | Lean 4.34.0; all nine pinned dependency checkouts verified |
| Proof build | Passed, no warnings or errors |
| Named theorem audit | 36 reports, each limited to propext, Classical.choice, Quot.sound |
| Executable examples | Five-point table false; failed-Fano table true |
| Independent rational arithmetic | 916 point configurations checked against exact Gaussian elimination |
| Official Lean fresh kernel replay | Exit 0; 77.137 seconds |
| Repository checks | validate, links, build, check, history: exit 0; 22 unit tests passed |

Proof source SHA-256: `c6ce3da8284a1379c42db9338213397328d3296a2f2fc60b226e42bcfcd49fb7`.

`SHA256SUMS` covers the packaged source, documentation, scripts and logs. Input
hashes inside `verification.json` additionally tie the proof and verification
scripts to these observations. Dependency source files were not edited.

Limitations: cached dependency builds were used; no independent kernel or human
referee audit is claimed. Python geometry extraction and Gaussian elimination are
supplementary implementations, not Lean-verified software. The Lean geometry
bridge handles arbitrary real coordinates propositionally, while the executable
checker consumes finite incidence tables. The historical geometric classification
is outside the package. Organizer review and award eligibility remain unconfirmed.
