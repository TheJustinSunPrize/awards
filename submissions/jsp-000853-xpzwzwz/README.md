# JSP-000853 / Erdős Problem #1025

This repository contains a complete Lean 4 formalization of the result
`g(n) = Θ(√n)` for free sets of pair mappings.  The main theorem is
`JSP000853.erdos1025`.

This is a formalization of known mathematics, not a claim of mathematical
discovery. Local compilation and the axiom audit pass; organizer review,
priority, eligibility, and any award remain pending.

The formalization and its local verification were developed with OpenAI Codex
assistance. The public applicant and proposed formalization representative is
the GitHub account `xpzwzwz`; final attribution remains subject to organizer
review and recipient confirmation.

Immutable public source snapshot:
[`xpzwzwz/jsp-000853-lean@62ac8c0`](https://github.com/xpzwzwz/jsp-000853-lean/tree/62ac8c0e182e3304066a23511871b804746d059c).

The source problem asks about symmetric maps on distinct pairs of an `n`-element
set, where the image of a pair differs from both endpoints. A set is free when no
pair inside it maps back into it.

## Formal target

The asymptotic statement is encoded without real square roots:

- **lower bound:** one universal natural constant `C` makes
  `n ≤ C * |S|²` for some free set `S` of every admissible mapping;
- **upper bound:** one universal natural constant `C` and, for every `n ≥ 3`,
  an admissible mapping make `|S|² ≤ C * n` for every free set `S`.

The checked constants are explicit:

- the lower-bound theorem uses `C = 512`;
- the upper-bound theorem uses `C = 16`.

These constants are not optimized; they are sufficient for the asymptotic
statement.

## Proof architecture

- `Definitions.lean` states admissible pair mappings, free sets, and the final
  square-root-free asymptotic target.
- `Deletion.lean`, `ExtensionCounting.lean`, and `Sampling.lean` implement the
  lower-bound argument.  A uniformly counted finite colouring supplies a sparse
  sample, and deleting the output of every bad pair leaves a free set.
- `UpperBound.lean` defines the Conlon--Fox--Sudakov grid mapping.
- `GridGraph.lean` identifies a free grid set with a forest in its row--column
  incidence graph, giving the linear grid bound.
- `ArbitraryUpper.lean` embeds an arbitrary `N`-element type into a square grid
  and restricts the mapping back to it.
- `LowerBound.lean` closes the lower bound and combines both halves into
  `erdos1025`.

## Build

```sh
lake exe cache get
lake build -KwarningAsError=true
lake env lean Audit.lean
```

The repository contains no `sorry`, `admit`, custom `axiom`, or `unsafe`
declaration. `Audit.lean` prints the axioms of the main theorem for independent
checking. The latest local build output, axiom result, and source hashes are
summarized in [`evidence/`](evidence/README.md); this is not a substitute for
independent review.

## Primary sources

- P. Erdős and A. Hajnal, [*On the structure of set mappings*](https://doi.org/10.1007/BF02023868)
  (1958).
- J. Spencer, *Turán's theorem for k-graphs* (1972).
- D. Conlon, J. Fox, and B. Sudakov,
  [*Short proofs of some extremal results II*](https://doi.org/10.1016/j.jctb.2016.03.005)
  (2016), Section 2.
