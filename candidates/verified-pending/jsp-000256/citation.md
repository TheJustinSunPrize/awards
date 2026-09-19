# Candidate citation: 000256

## English

Smallest largest denominator in a distinct unit-fraction representation (catalog 000256; [BlEr76] Denominators of unit fractions (1976)).

Status of this candidate record:

- Mathematical status: solved.
- Lean formalization: available (formalization contributor: Shiqiang Chen,
  independent researcher) in the public repository
  `github.com/shunfeng8421/jsp301-lean` at commit `4535c638ad67cde6c353c31df6d26ec336d3a80f`.
- Eligible to claim: yes, subject to independent verification and review.

Scoped constructive component (2026-09-18):

1. Theorems Jsp256.one_rep, Jsp256.five_fourths_rep, Jsp256.four_thirds_rep, Jsp256.three_halves_rep are provided.
2. Axiom audit reports exactly `[propext, Classical.choice, Quot.sound]`; no
   `sorry`/`admit`/`axiom`.

Explicit distinct unit-fraction representations with recorded largest denominators (1: max 6, 5/4: max 6, 4/3: max 12, 3/2: max 15), verified by norm_num/native_decide. scoped constructive component.

See `verification/record.yaml`, `verification/statement.yaml`, and
`verification/build-current-release.log`.
