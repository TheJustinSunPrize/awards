# Statement correspondence

The catalog asks the sufficiently-large-cardinality inequality. The positive
natural numbers are represented as `ℕ` with `0 ∉ A`; `A` is a `Finset`, so
elements are distinct and `A.card` counts those elements exactly. `A.Nonempty`
makes the denominator positive. The numerator and denominator are cast to `ℚ`
before division; this is not truncated natural-number division.

The existential threshold precedes the quantifier over sets, so it is uniform
over all admissible sets. There is no bound on the largest element. No gcd
normalization, squarefree condition, prime-cardinality assumption, or unproved
analytic hypothesis appears in the final exported statement. Gcd normalization
is an internal step in the upstream proof and is removed in its final theorem.

Both witnesses belong to `A`. The statement allows them to be equal, as in the
upstream statement. For a cardinality greater than one the positive-element
inequality itself rules out equality. `JSP331.distinct_of_gcd_bound` proves
this implication. `JSP331.sufficiently_large_distinct_gcd_bound` raises the
threshold to `max N 2` and explicitly supplies distinct witnesses.
The threshold is existential and non-effective; this package provides no
computable universal cutoff.

The upstream bounded-existential notation `∃ᵉ (a ∈ A) (b ∈ A)` elaborates to
the same nested existential/membership expression used in this package.
The direct `exact Erdos402.erdos_402` bridge makes Lean check that correspondence.
`Audit.lean` also prints the expanded final type for inspection.

## Limits

This is not the stronger inequality for every cardinality, nor an equality
classification. The upstream source records a gap from cardinality 7001 to
its non-effective analytic threshold for that stronger theorem. The similarly
named declaration in Formal Conjectures has stronger quantifiers and is not
imported or claimed here.

The full upstream file also contains finite certificates using `native_decide`.
The final theorem's **transitive** axiom list, not a file-wide text search, is
the acceptance test for whether those certificates are used in this result.
The verifier rejects `Lean.ofReduceBool`, `sorryAx`, and every other axiom
outside its three-axiom allowlist. The completed audit found only the three
standard axioms in all six declarations; see [VERIFICATION.md](VERIFICATION.md).
