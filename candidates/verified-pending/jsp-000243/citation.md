# Candidate citation: 000243

## English

Shortest interval with distinct denominators whose reciprocals sum to one (catalog 000243; [Cr01] On unit fractions with denominators in short intervals (2001)).

Status of this candidate record:

- Mathematical status: solved.
- Lean formalization: available (formalization contributor: Shiqiang Chen,
  independent researcher) in the public repository
  `github.com/shunfeng8421/jsp301-lean` at commit `7449d2ce2917b32d678213c577bd90dd3237d9be`.
- Eligible to claim: yes, subject to independent verification and review.

Scoped constructive component (2026-09-18):

1. Theorems Jsp243.one_rep_in_interval, Jsp243.denominators_distinct, Jsp243.denominators_in_interval are provided.
2. Axiom audit reports exactly `[propext, Classical.choice, Quot.sound]`; no
   `sorry`/`admit`/`axiom`.

Explicit constructive component: the interval [2,6] (length 4) contains distinct denominators 2,3,6 whose reciprocals sum to 1. Verified by norm_num/native_decide. scoped component.

See `verification/record.yaml`, `verification/statement.yaml`, and
`verification/build-current-release.log`.
