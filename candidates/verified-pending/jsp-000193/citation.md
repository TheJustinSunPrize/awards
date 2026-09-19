# Candidate citation: 000193

## English

Gaps between consecutive squarefree integers (catalog 000193; catalog JSP-000193).

Status of this candidate record:

- Mathematical status: open (complete resolution not recorded in the catalog).
- Lean formalization: available (formalization contributor: Shiqiang Chen,
  independent researcher) in the public repository
  `github.com/shunfeng8421/jsp301-lean` at commit `0c8eeae13a2e2d9d66827fb4743eb87867e66447`.
- Eligible to claim: pending, subject to independent verification and review.

Scoped constructive component (2026-09-19): an explicit witness of 8 consecutive
positive integers that are all non-squarefree, placed at
`Q = 65335225716547` with

    Q+1 = 65335225716548 = 4 · 16333806429137      (4  | Q+1)
    Q+2 = 65335225716549 = 9 · 7259469524061       (9  | Q+2)
    Q+3 = 65335225716550 = 25 · 2613409028662      (25 | Q+3)
    Q+4 = 65335225716551 = 49 · 1333371953399      (49 | Q+4)
    Q+5 = 65335225716552 = 121 · 539960543112      (121 | Q+5)
    Q+6 = 65335225716553 = 169 · 386599942110      (169 | Q+6)
    Q+7 = 65335225716554 = 289 · 226072421164      (289 | Q+7)
    Q+8 = 65335225716555 = 361 · 180987677060      (361 | Q+8)

These square divisors are the squares of the primes 2,3,5,7,11,13,17,19 with
pairwise disjoint prime factors, so each `Q+i` is divisible by a square and
hence is not squarefree.  The witness is formalized as the theorem
`JSP193Scoped.exists_8_consecutive_nonsquarefree`
(`∃ N, ∀ i, 1 ≤ i → i ≤ 8 → ¬ Squarefree (N + i)`), all divisibility checked
by `norm_num` on the numeral `N`, kernel-verified with axiom closure `[propext,
Classical.choice, Quot.sound]`, 0 sorry/admit.

This demonstrates that the gap between consecutive squarefree integers is at
least 9.  It does not claim the full-resolution bound that the gaps are
unbounded (which the catalog records as open); that is the subject of the full
proof complement.