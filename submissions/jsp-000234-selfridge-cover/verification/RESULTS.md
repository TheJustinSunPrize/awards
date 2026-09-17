# Verification record

Verified on 2026-09-16 UTC (2026-09-17 Hong Kong time).

- `lake build Erdos273Selfridge Erdos273Selfridge.Audit`: passed, 1112 dependency/package jobs completed or up to date.
- Exact Formal Conjectures statement, including finite strict covering-system fields: passed.
- Separate all-integer arithmetic interpretation, including negative inputs: passed.
- Axiom audits of the final theorem, exact restatement, and integer interpretation: only `propext`, `Classical.choice`, and `Quot.sound`.
- `lake env leanchecker --fresh -v Erdos273Selfridge.Audit`: passed, exit status 0, replaying the full imported environment. This is the bundled Lean implementation, not an independent checker implementation.
- Every residue modulo 360 is covered; all moduli divide 360, are distinct, and equal p-1 for primes p >= 3. The bridge to unbounded inputs is formally proved.
- A checked scope example shows the certificate cannot cover 0 after its modulus 2 is removed. No claim about nonexistence of other p >= 5 covers follows.
- All three Lean sources passed the source audit. The covering-system structure file is byte-identical to the cited original.

Environment: Lean 4.33.1, compiler revision `819816b2e0a3bf405af45ae5c7af2491d8f5bee6`; mathlib `0df444a360eaa60ab8c11dca51a86af692955474`. The official Lean archive checksum matches its release API digest; see `toolchain.txt`.

Formal Conjectures: `40e7c98697de6f66b8cbdbf641749ab39ed9c152`. Numerical-certificate source: `9d81d4ba5dea78fa66a2fb8ae21212fe5a8a7760` in idealombrer/erdos-273-covering-pm1. Prize baseline: `f4e7173d89dfe91022a185427d63452c8ffbf6ae`.

The prior-art check included public prize issues/PRs through #275, the Formal Conjectures snapshot, the plby proof collection, and the reconstruction repository linked in the README. That repository has a related parity-reduction proof. No matching completed formalization of the p >= 3 covering variant was found in this search; this is not an exhaustive priority claim.

This formalizes an existing construction. It does not solve the open p >= 5 problem, establish eligibility, or replace organizer review. Prize repository checks are reported separately; they do not certify mathematical truth.

## Verification-command correction, 2026-09-17 UTC

The script now uses `lean -E warning` instead of the unsupported `lean --wfail` flag. The corrected exact-statement/axiom command was run successfully (exit status 0); see `command-fix-audit.txt`. The Lean proof sources are unchanged. Their previously recorded full kernel replay remains the proof verification evidence.
