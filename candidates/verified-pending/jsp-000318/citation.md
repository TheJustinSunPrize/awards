# Candidate citation: 000318

## English

How far beyond an interval's right endpoint can a composite integer in that
interval plus its least prime factor lie? (catalog 000318; catalog JSP-000318).

Status of this candidate record:

- Mathematical status: open in the catalog; **complete Lean formalization
  provided here proving the excess is unbounded**.
- Lean formalization: complete (formalization contributor: Shiqiang Chen,
  independent researcher) in the public repository
  `github.com/shunfeng8421/jsp301-lean` at commit `7d215509d405c4a8054b6053cc31cf08d6893504`.
- Eligible to claim: subject to independent verification and review.

Complete formalization (2026-09-20):

    ∀ (d T : ℕ), ∃ (p n : ℕ), p.Prime ∧ T < p ∧ d < p ∧ n = p^2 ∧ p ∣ n ∧ T < (n+p) - n

The theorem `JSP318.jsp000318_excess_unbounded` proves that for every interval
length `d` and every target `T` there exists a composite in an interval of
length `d` whose value plus a prime factor exceeds the right endpoint by more
than `T`.  The construction: pick a prime `p` with `T < p` and `d < p`
(infinitude of primes); `n = p^2` lies in `[p^2-d, p^2]`, `p` is a prime factor
of `n`, and `(n+p) - n = p > T`.  Hence the excess beyond the interval's right
endpoint is unbounded.

Verified against Lean v4.34.0 / mathlib v4.34.0; 0 sorry/admit; axiom closure
`[propext, Classical.choice, Quot.sound]`.