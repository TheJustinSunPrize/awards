# Citation — JSP-000177 (Erdős problem 183)

## English

This citation records the solved Erdős problem, its pinned Lean formalization,
and the independent current-release verification described below.

## The problem

Erdős problem 183 (JSP catalog entry JSP-000177,
https://www.erdosproblems.com/183,
problems/catalog-0101-0200.md):

> What is the exponential growth rate of the number of vertices needed to
> force a monochromatic triangle as the number of edge colors increases?

Posed: ~1981. Area: graph theory / Ramsey theory (multicolor triangle Ramsey
numbers). Historical bounty: $250. Status: resolved.

## The answer (as formalized)

Let $R_k(3)$ denote the least $N$ such that every $k$-coloring of the edges
of the complete graph $K_N$ contains a monochromatic triangle. Then the $k$-th
root $R_k(3)^{1/k}$ tends to infinity as $k \to \infty$ (so the growth is
faster than every fixed-base exponential), and quantitatively

$$R_k(3) \ge \left(\frac{1}{6 e^{38}} \cdot \frac{k^{1/3}}{\log k}\right)^k \qquad (k \ge 2).$$

## Lean formalization

- Repository: https://github.com/plby/lean-proofs
- Pinned commit: `1268917deaaaa0d674f651287027baa26cea9920`
- Files: `src/latest/ErdosProblems/Erdos183.lean` (entry point),
  `src/latest/ErdosProblems/Erdos183/Proof.lean` (proof body, 3046 lines)
- Entry theorems: `Erdos183.erdos_183`,
  `Erdos183.erdos_problem_183_explicit`
- Mathematical proof and formalization: OpenAI ten-proofs project,
  *MulticolorTriangleRamsey*; ported into the pinned repository by plby.

## Verification (this submission)

Independent re-verification of the pinned formalization against the current
release (Lean v4.34.0, mathlib v4.34.0 @
`5ed2965256430c3649e86755f9576b54eca72435`) by shiqiang-chen
(independent verification worker jsp177-verifier, 2026-09-18):
full rebuild exit 0 with zero source modifications; axiom audit on both entry
theorems reports exactly `[propext, Classical.choice, Quot.sound]` (no `sorry`,
no user axioms). Full evidence: `verification/record.yaml`,
`verification/current-release-v4.34.log`,
`verification/independent-verification.md`.

## Contributors

- Solution + formalization: OpenAI ten-proofs (credited, not claimed by this
  recommendation).
- Port/maintenance of the pinned repo state: plby (credited).
- Independent verification + submission record: shiqiang-chen
  (claiming only the verification work).