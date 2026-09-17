# Verification record

Checked on 2026-09-17 UTC.

- Lean 4.33.1 build of both modules: passed (2486 dependency/package jobs).
- Exact Formal Conjectures target and independent nonzero-scale interpretation: passed.
- Axiom audits of all five named results: only `propext`, `Classical.choice`, and `Quot.sound`.
- `lean -E warning` statement/axiom check: passed with exit status 0.
- Fresh replay of the complete imported environment through bundled `leanchecker --fresh -v Erdos120FinitePatterns.Audit`: passed with exit status 0. This uses Lean’s own kernel; it is not an independent verifier implementation.
- Submitted source audit: no placeholders, custom axioms, `native_decide`, unsafe declarations, implementation substitutions, or kernel-check bypasses.
- Repository schema validation, local Markdown links, generated data consistency, and all 22 existing tests: passed.
- All nine dependency Git HEADs and tracked trees match the manifest pins.

The build also passed using the normal manifest, with warnings treated as errors by Lake. The initial build and the full kernel replay reused the same pinned local dependencies through Lake package overrides, after cloud-offloaded files were restored. Local path overrides are not part of this package. The public checking script uses the normal pinned manifest.

Environment: Lean 4.33.1, compiler revision `819816b2e0a3bf405af45ae5c7af2491d8f5bee6`; mathlib `0df444a360eaa60ab8c11dca51a86af692955474`. The official Lean release archive was checksum-verified. Formal Conjectures statement: `40e7c98697de6f66b8cbdbf641749ab39ed9c152`. Prize repository baseline: `f4e7173d89dfe91022a185427d63452c8ffbf6ae`.

Public prior-art screening included prize entries through #434, the pinned Formal Conjectures statement, public proof repositories, mathlib sources, and web searches for this target. No matching finished Lean proof was found in that search. This is not an exhaustive priority claim. Erdős 213's seven-point target was excluded because PR #279 already covers it.

This is a formalization of the known finite-set theorem. It does not solve the infinite-set conjecture, establish eligibility, or constitute an award. Repository checks do not certify mathematical correctness.
