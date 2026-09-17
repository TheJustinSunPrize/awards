# Statement correspondence

## Catalogue identity

The official catalogue records JSP-000108 as **Solved**, with **Lean proof: No**
and **Eligible to claim: No**, and gives the natural-language question about
planar point sets whose points have many equidistant companions.

Catalogue snapshot: [awards commit
`f4e7173d89dfe91022a185427d63452c8ffbf6ae`](https://github.com/TheJustinSunPrize/awards/blob/f4e7173d89dfe91022a185427d63452c8ffbf6ae/problems/catalog-0101-0200.md#JSP-000108).

## Formal statement

The public Formal Conjectures source for Erdős Problem 92 defines
`maxEquidistantPointsAt`, `hasMinEquidistantProperty`, `possible_f_values`, and
`f`. The submitted target is the strong fixed-constant question:

```lean
∃ c > (0 : ℝ), ∀ᶠ n in Filter.atTop,
  (Erdos92.f n : ℝ) ≤ (n : ℝ) ^ (c / (n : ℝ).log.log)
```

This says that the guaranteed local equidistance count is eventually bounded
by the displayed subpolynomial power with one fixed positive constant `c`.
The theorem `Erdos92.erdos_92.variants.not_erdos_92`, copied from the pinned
public proof source, proves the negation. `JSP000108.not_jsp_000108` is a
statement-preserving wrapper around that theorem; it does not replace the
quantified target by a finite example or an assumed proposition.

The Formal Conjectures file also records a weaker `n^(o(1))` formulation as a
separate variant. This submission identifies the fixed-constant formulation
above as the exact target corresponding to the JSP catalogue's “every fixed
positive power” clause; it does not silently claim that the separate weak
variant has been proved by the wrapper.

## Mathematical provenance

The JSP catalogue lists:

- Erdős--Fishburn, *Minimum planar sets with maximum equidistance counts*,
  Computational Geometry 7 (1997), 207--218,
  [DOI](https://doi.org/10.1016/0925-7721%2895%2900050-x);
- Pach--Sharir, *Repeated angles in the plane and related problems*,
  J. Combin. Theory Ser. A 59 (1992), 12--22,
  [DOI](https://doi.org/10.1016/0097-3165%2892%2990094-b);
- Janzer--Janzer--Methuku--Tardos, *Tight bounds for intersection-reverse
  sequences, edge-ordered graphs and applications*,
  [arXiv:2411.07188](https://arxiv.org/abs/2411.07188).

The proof source explains that the negative formal result is obtained from the
strong unit-distance construction associated with Erdős Problem 90. The
source proof and its dependency files retain their original public headers and
attributions; this package does not claim authorship of those mathematics.
