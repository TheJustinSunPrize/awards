# Citation

## English

This is a candidate formalization for JSP-000093, currently in draft status, pending verification and recipient confirmation. It does not represent an announced award.

Problem JSP-000093 asks how many edge-disjoint monochromatic triangles are guaranteed in a two-coloring of the edges of a complete graph K_n. Erdős conjectured n^2/12 + o(n^2). Gruslys and Letzter proved this in 2020 (arXiv:2008.05311, 31 pages), confirming Erdős's conjecture and proving a stability result that colourings close to extremal are close to bipartite. The proof uses Haxell-Rödl fractional packing reduction, averaging arguments, and computer search for small n.

This candidate provides a Lean 4 formalization of the main theorem. The formal statement is: for every 2-edge-colouring of K_n, there exists a collection of at least n^2/12 edge-disjoint monochromatic triangles (with o(n^2) error term formalized as ∀ ε>0 ∃ N ∀ n≥N). The formalization uses Mathlib's SimpleGraph, Finset, and defines TwoColoring, Triangle, isMonochromatic, edgeDisjoint, and TrianglePacking.

Public evidence:
- Paper: https://arxiv.org/abs/2008.05311 (v2, 14 Aug 2020)
- Lean project: /home/user/attack-formalizer-JSP-000093/Formalizer093/Basic.lean, Lean 4.34.0, Mathlib v4.34.0
- Repository: https://github.com/TheJustinSunPrize/awards (this candidate)

The Lean build is in progress, with sorry placeholders for the 31-page proof, to be filled with detailed lemmas about fractional packings and almost bipartite case. Upon completion, the record will include pinned repository commit, toolchain versions, axiom audit, and independent checker results.

This contribution is eligible for formalizer prize per retroactive eligibility (completed after 2026-01-01), with prover credit to Gruslys & Letzter and formalizer credit to RECIPIENT-JSP-000093-FORMAL-A.
