# JSP-000070 Submission Bundle — README

This bundle contains everything needed to claim the prize for Erdős problem 42
(Sidon-type two-element sums) via the formal-verification route.

## Contents

```
jsp-000070-submission/
├── candidates/verified-pending/jsp-000070/     # four-piece record set (schema-validated)
│   ├── award.yaml                              # status: pending-recipient-confirmation
│   ├── citation.md                             # English + 中文
│   ├── recipients.md                           # RECIPIENT-JSP-000070-A placeholder
│   └── verification/
│       ├── record.yaml                         # checkers: Lean 4.34.0 kernel + lake build (current_release)
│       ├── statement.yaml                      # STMT-jsp-000070-v2 (mathlib pinned 5ed29652…)
│       ├── statements/STMT-jsp-000070-v1.yaml  # superseded v1 (retained)
│       ├── current-release-v4.34.log           # build + axiom audit log
│       └── independent-verification.md         # hashes, reproduction steps, sandbox attestation
├── people/curators/                            # signatory identity profiles (jsp070-verifier,
│                                               #   pawan-sasanka-ammanamanchi)
├── people/verifiers/                           # verifying-agent profile (jsp070-verifier)
├── PR.md                                       # upstream PR draft (recipient placeholder)
├── verify-current/                             # reproducible verification project
│   ├── Erdos42.lean                            # v4.34-adapted source (SHA-256 749BC7F7…A5446)
│   ├── lakefile.lean                           # mathlib @ v4.34.0
│   ├── lean-toolchain                          # leanprover/lean4:v4.34.0
│   ├── lake-manifest.json                      # pinned dependency manifest
│   └── ScratchTC.lean                          # typeclass sanity checks
└── state/                                      # driver log, final report, blockers
```

## Key facts (for reviewers)

- Upstream proof source: `github.com/plby/lean-proofs` @ `1268917deaaaa0d674f651287027baa26cea9920`
- Current-release re-verification: Lean `v4.34.0`, mathlib @ `5ed2965256430c3649e86755f9576b54eca72435` (v4.34.0)
- Axiom audit (`#print axioms`), all 5 entry points:
  `[propext, Classical.choice, Quot.sound]` only — no `sorry`, no new axioms
- `python scripts/manage.py validate` (records repository): **OK**
- Sandbox attestation: non-elevated process token, offline verification,
  source-built mathlib (no prebuilt artifacts)

## Recipient placeholder

`RECIPIENT-JSP-000070-A` must be replaced with the confirmed recipient
identity (written confirmation) before the award is announced.

## Reproduce

```
cd verify-current
lake build          # or: lake env lean Erdos42.lean
# axiom audit is printed at the end of Erdos42.lean (#print axioms …)
```
