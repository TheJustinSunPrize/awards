# Local verification record — submitted source

## English

This report summarizes the actual run in `evidence/submission_check/report.json`.
It is a submitter-side technical record, not the prize's completed official
`verification/record.yaml` and not an independent review signature.

Run started: `2026-09-17T10:22:42.409789+00:00`.  
Run completed: `2026-09-17T10:23:03.289878+00:00`.  
Submitted source SHA-256: `20c09dc7edfefb64634da5f17962fd9c528662c615538400ad1bd744686f53dc`.  
Environment: Linux x86_64, Lean 4.19.0, Lake 5.0.0-6caaee8.  
Mathlib commit: `c44e0c8ee63ca166450922a373c7409c5d26b00b`.

## Actual results

| Test | Actual exit code | Expected outcome achieved |
| --- | ---: | --- |
| `01_lean_version` | 0 | Pass |
| `02_lake_version` | 0 | Pass |
| `03_lake_build` | 0 | Pass |
| `04_smoke_test` | 0 | Pass |
| `05_source_compilation` | 0 | Pass |
| `06_negative_control` | 1 | Pass |

The negative control is deliberately false and must fail. The overall verification
script exited 0. The named Lake target was built and the submitted source was also
compiled explicitly to a new `.olean`. No existing project `.olean` was substituted
for this compilation. Compiled output is not required in the public source PR;
reviewers should regenerate it.

All nine dependency Git HEADs matched the manifest, and tracked dependency source
was clean at the time of the submitted run. Archive-induced executable-mode changes
were restored only after comparing the affected file bytes against the corresponding
Git HEAD content. That is not an independent authenticity certification of the
compiler distribution or its precompiled libraries.

## Axiom output

```text
'JSP301.known_counterexample' depends on axioms: [propext, Classical.choice, Quot.sound]
'JSP301.catalog_statement_false' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The script requires exactly those axiom sets. The deliberately false control is
rejected with `unsolved goals` and `False`.

## Isolation and limits

The local launcher used a newly created HOME and a process-inherited Linux x86_64
seccomp filter. The guard checked that creation of IPv4 and IPv6 sockets returned
EPERM. See `launcher.json` and `launcher.log`. The local tests did not download
dependencies. This is process-level filtering, not a network namespace or physical
network disconnection.

The check uses Lean's normal import-trust settings and the prepared dependency
artifacts. It does not independently recheck every imported declaration, provide
two separate proof-checker implementations, establish an approved minimum safe
version, or supply an external statement-review signature. The false-control test
is a sanity check, not a proof of compiler soundness.

For that reason, no official completed-verification record, reviewer identities,
review signatures, awarded status, or recipient confirmation is fabricated here.
Those matters remain for maintainers and designated reviewers. The project's
[verification guidance](https://github.com/TheJustinSunPrize/awards/blob/main/docs/verification.md) distinguishes a build
from a completed verification record.

## Earlier check

`evidence/prior_check/` preserves the earlier check of the original source with
its then-current warning output. It is historical evidence, not a replacement for
the submitted-source run. No logs are edited to remove a failure or warning.
