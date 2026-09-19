# Candidate citation: 000428

## English

Large pairwise noncoprime subsets of an integer interval (catalog 000428; [Er73] Problems and results in combinatorial number theory (1973)).

Status of this candidate record:

- Mathematical status: solved.
- Lean formalization: available (formalization contributor: Shiqiang Chen,
  independent researcher) in the public repository
  `github.com/shunfeng8421/jsp301-lean` at commit `1d8400035add9dde8f80dff09a487590f1e977d4`.
- Eligible to claim: yes, subject to independent verification and review.

Scoped constructive component (2026-09-18):

1. Theorems Jsp428.evens20_pairwise_noncoprime, Jsp428.pair_gcd_div_two, Jsp428.two_divides_all are provided.
2. Axiom audit reports exactly `[propext, Classical.choice, Quot.sound]`; no
   `sorry`/`admit`/`axiom`.

Explicit constructive component: the ten even numbers {2,4,...,20} are pairwise non-coprime (shared divisor 2), verified via Nat.dvd_gcd. scoped component.

See `verification/record.yaml`, `verification/statement.yaml`, and
`verification/build-current-release.log`.
