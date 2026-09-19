# Candidate citation: 000193

## English

Gaps between consecutive squarefree integers (catalog 000193; catalog JSP-000193).

Status of this candidate record:

- Mathematical status: open in the catalog; **complete Lean formalization provided
  here proving the gaps are unbounded**.
- Lean formalization: complete (formalization contributor: Shiqiang Chen,
  independent researcher) in the public repository
  `github.com/shunfeng8421/jsp301-lean` at commit `5009cb72248985bb9fe4063394f68e53e635e520`.
- Eligible to claim: subject to independent verification and review.

Complete formalization (2026-09-19):

    ∀ n, 1 ≤ n → ∃ N : ℕ, ∀ i, 1 ≤ i → i ≤ n → ¬ Squarefree (N + i)

The theorem `JSP193Full.jsp000193_squarefree_gaps_unbounded` constructs, for
every `n`, `n` consecutive positive integers none of which is squarefree.  It
uses a strictly-increasing prime sequence `primeSeq` (infinitude of primes) and
`Nat.chineseRemainderOfList`: the squares of the first `n` primes are pairwise
coprime, so there is `N` with `N + i ≡ 0 (mod pᵢ²)`; then `pᵢ² ∣ N+i`, so each
`N+i` is non-squarefree.  Hence the gaps between consecutive squarefree
integers are unbounded.

Verified against Lean v4.34.0 / mathlib v4.34.0; 0 sorry/admit; axiom closure
`[propext, Classical.choice, Quot.sound]`.