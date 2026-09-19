# Statement and scope

Problem: [JSP-000603](https://github.com/TheJustinSunPrize/awards/blob/f4e7173d89dfe91022a185427d63452c8ffbf6ae/problems/catalog-0601-0700.md#jsp-000603),
corresponding to [Erdős 735](https://www.erdosproblems.com/735).
The catalog currently records the mathematical problem as solved, Lean proof as
“No”, and eligibility as “No”. This submission does not alter those fields.

## Quantified geometric theorem

Let `ι` be any finite type and `p : ι → (Fin 2 → ℝ)` be injective. For distinct
indices `a,b`, `lineBlock p a b` is **all** indices `c` for which `p c` belongs to
Mathlib's affine line through `p a,p b`. `determinedLines p` is the deduplicated
collection of all such blocks. It is constructed from every ordered pair of
distinct indices, with no omitted line or presumed incidence hypothesis.

`geometric_accepts_iff_common_sum` proves:

```
accepts (determinedLines p) = true
  iff there exist w : ι → ℝ and C : ℝ such that
    (∀ a, 0 < w a), 0 < C, and
    (∀ a b, a ≠ b → sum_{c in lineBlock p a b} w(c) = C).
```

The Lean theorem actually applies to any real vector space. Specialization to
`Fin 2 → ℝ` gives the plane. Injectivity prevents duplicate indices from being
mistaken for distinct geometric points.

## Abstract checker

For a finite set `L` of finite blocks, `LinearSpace L` requires every block to have
at least two points and every pair of distinct points to occur in exactly one
block. If this condition holds, `accepts L = true` is equivalent to existence of
positive real weights whose sum on every block is one. Its `false` output is
equivalent to nonexistence. Correctness is not claimed for malformed incidence
systems that fail `LinearSpace`.

The Boolean checker computes:

1. cardinality at most one; or
2. the whole point set is a determined line; or
3. every point degree exceeds one and the two rational conditions in the README hold.

The first two branches handle degenerate cases directly; the degree formula's
zero denominators are never used to justify those cases. In the third branch,
every normalized weak magic weighting is unique, and the explicit formula is
rational. Uniqueness is not asserted in the collinear case or without fixing the
common line sum to one.

## Relation to the historical solution

The ABKPR classification identifies the possible geometric forms (general position,
collinear/near-pencil, and projective images of the failed-Fano configuration).
That classification is outside this package. Our result is a finite incidence
criterion derived from their already-known weight formula; it retains arbitrary
cardinality and arbitrary real coordinates in its geometric theorem. It does not
supply a new mathematical classification, new extremal bound, or priority claim.

The two finite Lean example tables are not substituted for the universal theorem.
Python checks of explicit coordinate realizations and 916 test configurations are
supplementary regression evidence, not the proof of the general statement.
