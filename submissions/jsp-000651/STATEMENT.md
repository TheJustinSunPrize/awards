# Statement fidelity and attribution

## Target and precise scope

[JSP-000651](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0601-0700.md#JSP-000651)
corresponds to [Erdős Problem 792](https://www.erdosproblems.com/792): how
large a sum-free subset is guaranteed in a finite integer set?

The submitted result is the classical one-third lower bound credited to
Paul Erdős, *Extremal problems in number theory*, Proc. Sympos. Pure Math.
VIII (1965), 181–189, as referenced by the problem page and prize catalog.
No improvement to that mathematical bound is claimed.

| Mathematical concept | Formal statement |
| --- | --- |
| Finite set of integers | `a : Finset ℤ`; both signs are allowed |
| Sum-free | `SumFree b := ∀ x ∈ b, ∀ y ∈ b, x + y ∉ b` |
| Nonzero, nonempty domain | `a.Nonempty` and `0 ∉ a` |
| Strict nonzero bound | `∃ b ⊆ a, SumFree b ∧ a.card < 3 * b.card` |
| Domain allowing zero | `2 ≤ a.card` |
| Classical weak bound | `∃ b ⊆ a, SumFree b ∧ a.card ≤ 3 * b.card` |

The use of `Finset` means elements are distinct; the sum-free condition
still allows `x = y`. It is not the weaker condition that forbids only
equations with three distinct terms.

The unrestricted wording “every finite integer set has a sum-free subset
of size at least one third” needs a small boundary qualification:
`{0}` has no nonempty sum-free subset because `0 + 0 = 0`.
`singleton_zero_exception` proves this obstruction. The submitted weak
theorem covers all integer sets of size at least two. The strict theorem
covers every nonempty zero-free set, including singletons. No false
universal claim about `{0}` is made.

## Proof correspondence

1. Mathlib's `Nat.forall_exists_prime_gt_and_modEq` supplies a prime
   `p = 3k + 2` greater than all absolute values in the input. This is
   Dirichlet's theorem already proved in the pinned Mathlib version.
2. The interval from `k+1` through `2k+1` in `ZMod p` has `k+1` elements
   and is sum-free. Both properties are proved in this package.
3. Every nonzero input integer remains nonzero modulo `p`, and multiplying
   by it permutes `ZMod p`. Each input element therefore has exactly
   `k+1` multiplier preimages in the interval.
4. Double counting over all `p` multipliers shows that one pullback has
   strictly more than one third of the input elements. Pullback preserves
   the sum-free property by additivity.
5. For a set possibly containing zero, erase zero, apply the strict bound,
   and use integral cardinalities to obtain `|A| ≤ 3|B|` when `|A| ≥ 2`.

The result is universal over its stated domain; it is not a check of a
particular finite example or conditional on an unproved extremal theorem.
The stronger Alon–Kleitman, Bourgain and Bedert results and the optimal
asymptotic question on the source page are outside this contribution.

## Credit, assistance and prior-art limits

The mathematics is credited to Erdős and the existing library authors.
OpenAI Codex assisted the implementation, verification and preparation.
The applicant requests consideration for formalization only.

A bounded search of the official repository's public issues/PRs, selected
GitHub Lean sources and the relevant Mathlib names found no complete
formal proof of this precise bound. The inspected LeanGenius
`Erdos792Problem.lean` derives its lower bound from a declared Bourgain
axiom; it was neither imported nor used as proof evidence here. Its code
was not copied. That limited search does not establish global novelty,
exclusive priority or prize entitlement.

No candidate eligibility, confirmed recipient identity or award record
is changed by this package. Organizer verification and assessment remain
necessary before any claim of an award.

## Documentation attribution

Catalog context is credited to **The Justin Sun Prize contributors**,
[source revision `f4e7173d89dfe91022a185427d63452c8ffbf6ae`](https://github.com/TheJustinSunPrize/awards/blob/f4e7173d89dfe91022a185427d63452c8ffbf6ae/problems/catalog-0601-0700.md#JSP-000651),
under [CC BY 4.0](https://creativecommons.org/licenses/by/4.0/).
Changes: new formalization documentation, explicit theorem scope, proof
correspondence and reproducibility instructions; the catalog is unchanged.
Mathematical attribution and third-party rights remain as stated above.
