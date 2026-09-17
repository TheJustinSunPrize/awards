# Statement fidelity and attribution

## Target and precise scope

[JSP-000478](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0401-0500.md#JSP-000478)
corresponds to [Erdős Problem 589](https://www.erdosproblems.com/589): how
large a subset with no three collinear points is guaranteed in a planar
point set with no four collinear?

The submitted result is the classical greedy lower bound recorded on
that page. It proves an exact finite counting inequality, which implies
the square-root guarantee, for all finite real planar point sets. No
new mathematical improvement or solution of the optimal growth problem
is claimed. The sharper results of Füredi and of Balogh–Solymosi are
outside this package.

| Mathematical concept | Formal statement |
| --- | --- |
| A real planar point | `Point := ℝ × ℝ` |
| Finite distinct points | `a : Finset Point` |
| At most `m` collinear points | `BoundedLines a m`: every collinear finite subset of `a` has cardinality at most `m` |
| No four collinear | `NoFour a := BoundedLines a 3` |
| No three collinear | `NoThree b := BoundedLines b 2` |
| Exact counting guarantee | `∃ b ⊆ a, NoThree b ∧ a.card ≤ b.card + Nat.choose b.card 2` |
| Quadratic consequence | `∃ b ⊆ a, NoThree b ∧ 2 * a.card ≤ b.card * (b.card + 1)` |
| Square-root consequence | `∃ b ⊆ a, NoThree b ∧ a.card ≤ b.card ^ 2` |

All three conclusions assume `NoFour a`. The theorem `boundedLines_iff`
proves that `BoundedLines a m` is equivalent to there being no collinear
subset of `a` of cardinality `m+1`. Thus the definitions match the usual
distinct-points conditions rather than weakening the premise or changing
the geometry. Empty sets and all small cardinalities are included.

Collinearity and lines use Mathlib's `Collinear ℝ` and `affineSpan ℝ`.
There is no restriction to integer/rational coordinates and no abstract
incidence axiom replacing the real-plane statement. The final square-root
guarantee is expressed by the exact natural-number inequality `n ≤ m²`;
no separate real-square-root theorem is claimed as a formal declaration.

## Proof correspondence

1. Within the finite powerset, choose a maximum-cardinality subset `B`
   with no three collinear. The empty subset proves this collection is
   nonempty.
2. Adding any excluded point `x` must violate that property. Extract two
   distinct points of `B` whose affine span contains `x`.
3. A fixed pair in `B` can have at most one excluded point on its line;
   two would give four collinear points of `A`.
4. Cover `A \ B` by those blocked-point sets and bound the cardinality
   of their union by the sum of their cardinalities. There are
   `choose(|B|,2)` pairs.
5. Add `|B|`, then use the binomial identity to obtain the quadratic and
   square bounds.

The conclusion does not assume the greedy bound, an unproved extremal
estimate or a finite enumeration certificate. It is a universal theorem
about the full stated domain.

## Credit, assistance and prior-art limits

The submission credits the classical greedy argument and the existing
Mathlib authors. OpenAI Codex assisted the implementation, verification
and preparation. The applicant requests consideration for formalization
only, not mathematical solver credit.

A bounded search of the official repository's public issues/PRs, selected
GitHub Lean sources and relevant Mathlib names found no complete proof
of this precise bound. The inspected LeanGenius `Erdos589Problem.lean`
declares its greedy lower bound as an axiom; it was neither imported nor
used as proof evidence here, and its code was not copied. This limited
search does not establish global novelty, exclusive priority or prize
entitlement.

No candidate eligibility, confirmed recipient identity or award record
is changed by this package. Organizer verification and assessment remain
necessary before any claim of an award.

## Documentation attribution

Catalog context is credited to **The Justin Sun Prize contributors**,
[source revision `f4e7173d89dfe91022a185427d63452c8ffbf6ae`](https://github.com/TheJustinSunPrize/awards/blob/f4e7173d89dfe91022a185427d63452c8ffbf6ae/problems/catalog-0401-0500.md#JSP-000478),
under [CC BY 4.0](https://creativecommons.org/licenses/by/4.0/).
Changes: new formalization documentation, explicit theorem scope, proof
correspondence and reproducibility instructions; the catalog is unchanged.
Mathematical attribution and third-party rights remain as stated above.
