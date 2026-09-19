# Candidate citation: 000363

## English

Proportion of integers with a divisor in a short interval (catalog 000363; [Be34] On the density of certain sequences of integers (1934)).

Status of this candidate record:

- Mathematical status: solved.
- Lean formalization: available (formalization contributor: Shiqiang Chen,
  independent researcher) in the public repository
  `github.com/shunfeng8421/jsp301-lean` at commit `a22bba54c15ce98d336c0fb8401c3f295eb30641`.
- Eligible to claim: yes, subject to independent verification and review.

Scoped constructive component (2026-09-18):

1. Theorems Jsp363.has_divisor24_iff_23, Jsp363.no_divisor24_iff, Jsp363.concrete_no_divisor are provided.
2. Axiom audit reports exactly `[propext, Classical.choice, Quot.sound]`; no
   `sorry`/`admit`/`axiom`.

Explicit constructive component: an integer has no divisor in [2,4] iff it is not divisible by 2 and not by 3, verified by direct divisibility reasoning. scoped component.

See `verification/record.yaml`, `verification/statement.yaml`, and
`verification/build-current-release.log`.
