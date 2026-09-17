# Verification results

The complete eventual theorem and the distinct-witness bridge passed local
verification on 2026-09-16T17:40:22.857337+00:00 (UTC), using Lean (version 4.33.0, x86_64-w64-windows-gnu, commit d8b18978322de05a8f3dba51ef03cf5461676c17, Release).

| Check | Result |
| --- | --- |
| Complete pinned upstream source build | Passed; 126 external proof modules |
| Final statement bridge and distinct witnesses | Passed |
| Transitive axiom audit | Six declarations; only `propext`, `Classical.choice`, `Quot.sound` |
| `leanchecker --fresh JSP331.Proof` | Passed; same Lean kernel |
| Source bootstrap in an empty directory | Passed; all 126 hashes matched |
| Verification-tool regression checks | 5 passed |
| Repository schema, links, data generation and history | Passed |
| Repository validator tests on Linux | 22 passed |

The [machine-readable summary](verification-summary.json) records the Git file
hashes, the raw byte hashes captured during verification, actual command exit
codes, durations, log hashes, and axiom lists. Staged file bytes were compared
with the verified files: only CRLF-to-LF normalization differs for the listed
configuration files. The package's `.gitattributes` preserves LF on checkout.
The upstream proof emits style warnings; its build succeeds. The eventual
theorem does not transitively depend on the `native_decide` certificates that
occur elsewhere in the full imported file.

## Archived verification artifact

- ID: `github:LenChild/awards:jsp-000331-verification-20260917:jsp-000331-verification.zip`
- Download: [jsp-000331-verification.zip](https://github.com/LenChild/awards/releases/download/jsp-000331-verification-20260917/jsp-000331-verification.zip)
- SHA-256: `09c1fdc74d3536b9575942f456d409052e1fce70cf4c79e4910f0f3d8dc8db80`
- Bytes: `16956`

The archive contains public module-completion events, full axiom output,
the kernel-replay log, source integrity metadata, attribution, and repository
check results. Its internal manifest hashes every evidence file. Machine-local
raw build logs stay local; the summary records their hashes and sizes. The
published build events are explicitly an excerpt. The empty successful
kernel-replay log is accompanied by its recorded zero exit code.

This is automated local verification using Lean's kernel, not an independent
checker or substantive external review. The result covers sufficiently large
sets, without an effective cutoff; it does not cover every cardinality or
classify equality. Windows repository tests exposed existing path and symlink
limitations; the unmodified tests passed under WSL Ubuntu with Python 3.12.
