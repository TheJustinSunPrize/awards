# Citation

Candidate review narrative. This entry is a preliminary public candidate under verification. It does not constitute an award, a formal nomination, or a published decision.

## English

JSP-000690 asked whether there exists a 3-uniform, 3-chromatic-critical hypergraph with minimum degree at least seven. The problem bank records the question as posed no later than 1974, originating from P. Erdos and L. Lovasz, "Problems and results on 3-chromatic hypergraphs and some related questions" (1975), 609--627.

The problem bank records the problem as solved, citing the 2025 preprint "On an Erdos-Lovasz problem: 3-critical 3-graphs of minimum degree 7" ([arXiv:2512.24850](https://arxiv.org/abs/2512.24850)), with the solution year recorded as 2026. The solver is recorded under a placeholder pending written confirmation.

Formalization evidence, published for substantive review:

- A Lean 4 formalization of the result is publicly available at <https://github.com/klat58688-ui/jsp-000690-proof>, pinned at commit `570b8588d3ca7ede72357a5a4317f88acb285fba`. The proof constructs an explicit 3-uniform hypergraph on 9 vertices and 22 edges with minimum degree 7 that is 3-colorable, not 2-colorable, and critical under removal of any single edge or vertex, with all finite checks decided by computation.
- Toolchain: Lean v4.15.0 with mathlib pinned at commit `9837ca9d65d9de6fad1ef4381750ca688774e608`.
- The axiom audit of the top-level theorem reports the standard Lean axioms (propext, Classical.choice, Quot.sound) plus Lean.ofReduceBool, reflecting the use of native_decide for the finite enumerations; no sorry placeholders are present.
- Two independent checks passed: the Lean kernel itself during a clean build, and the independent lean4checker re-checking tool run in both of its modes across all four modules of the proof.
- The clean build log (SHA-256 `5725b26137eea93c1c15ab59ca99640d801287b8ab41ab2d617c505b9479c9cc`, 1097 bytes) is retained for permanent external archiving.
- Formalization attribution: the formalization and its local verification were prepared with AI coding-assistant sessions (TRAE agent) under the direction of the account holder. Mathematical discovery credit remains with the preprint authors.

A structured verification record and a signed formal statement require registered curator and verifier profiles in this repository. Those role directories are not yet populated, so `verification/record.yaml` is null and this candidate remains under verification. No award is claimed or announced by this record.
