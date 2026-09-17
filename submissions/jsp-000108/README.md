# JSP-000108: equidistant neighbors in planar point sets

This package formalizes the negative answer to the fixed-constant version of
JSP-000108. The catalogue wording is:

> If every point has many neighbors at one common distance from it, how large a
> count can be guaranteed at every point? Is it smaller than every fixed
> positive power of the number of points?

The exact Lean target in this submission is

```lean
∃ c > (0 : ℝ), ∀ᶠ n in atTop,
  (Erdos92.f n : ℝ) ≤ (n : ℝ) ^ (c / (n : ℝ).log.log)
```

`JSP000108.not_jsp_000108` proves its negation, and
`JSP000108.answer_false_iff` packages the answer as `False ↔ target_statement`.
The definition of `f` counts, for each planar point set, the largest number of
other points at one distance from each point, with the distance allowed to
depend on the point.

This is a formalization of known mathematics. It is not a claim of a new
solution, award, eligibility, recipient confirmation, or independent review.
The source problem and formal statement are credited to their original authors.

## Provenance and attribution

- JSP catalogue entry: [JSP-000108](https://github.com/TheJustinSunPrize/awards/blob/f4e7173d89dfe91022a185427d63452c8ffbf6ae/problems/catalog-0101-0200.md#JSP-000108).
- The catalogue cites Erdős--Fishburn, [*Minimum planar sets with maximum
equidistance counts*](https://doi.org/10.1016/0925-7721%2895%2900050-x),
Pach--Sharir, [*Repeated angles in the plane and related
problems*](https://doi.org/10.1016/0097-3165%2892%2990094-b), and Janzer--Janzer--Methuku--Tardos,
[*Tight bounds for intersection-reverse sequences, edge-ordered graphs and
applications*](https://arxiv.org/abs/2411.07188).
- The formal statement source is [Formal Conjectures Problem
92](https://github.com/google-deepmind/formal-conjectures/blob/40e7c98697de6f66b8cbdbf641749ab39ed9c152/FormalConjectures/ErdosProblems/92.lean).
- The proof source is `ErdosProblems/Erdos92.lean` from the immutable
[plby/lean-proofs commit
`8822f7ddef30fadbd92e1c6ab4ed897af356af5e`](https://github.com/plby/lean-proofs/tree/8822f7ddef30fadbd92e1c6ab4ed897af356af5e).
Its public authorship header is preserved. The supporting unit-distance
formalization is attributed there to L. Alpöge, Kim Morrison, and Tau Ceti
contributors, with the Formal Conjectures statement authors and the listed
formal authors.

The source proof is copied byte-for-byte; this submission adds only the
JSP-specific wrapper and reproducibility/documentation files. Source files are
distributed under the applicable Apache-2.0 notice in this directory.

## Reproduction

With the pinned Lean toolchain and Mathlib revision recorded in
`lean-toolchain`, `lakefile.toml`, and `lake-manifest.json`:

```sh
./verify.sh
```

The script checks forbidden proof escapes, builds the package, checks both the
source theorem and JSP wrapper, and prints the axiom reports. Generated `.lake/`
files are build products and are not part of the submission.
