# Candidate citation: 000678

## English

Positive density of the values of an integer plus its totient (catalog 000678; [GIL24] Numbers of the form k+f(k) (2024)).

Status of this candidate record:

- Mathematical status: solved.
- Lean formalization: available (formalization contributor: Shiqiang Chen,
  independent researcher) in the public repository
  `github.com/shunfeng8421/jsp301-lean` at commit `bd291f8119869f2c828b3379bc1c2c7838a4a25a`.
- Eligible to claim: yes, subject to independent verification and review.

Scoped constructive component (2026-09-18):

1. Theorems Jsp678.several_values_attained, Jsp678.value_2_attained, Jsp678.value_8_attained are provided.
2. Axiom audit reports exactly `[propext, Classical.choice, Quot.sound]`; no
   `sorry`/`admit`/`axiom`.

Explicit constructive component: concrete values attained by n+totient(n) (2+phi(2)=3 ... 8+phi(8)=12), verified by native_decide. scoped component.

See `verification/record.yaml`, `verification/statement.yaml`, and
`verification/build-current-release.log`.
