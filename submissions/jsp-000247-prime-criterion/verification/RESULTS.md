# Verification record

Verified on 2026-09-16 UTC (2026-09-17 Hong Kong time).

- `lake build Erdos291Criterion Erdos291Criterion.Audit`: passed, 2760 dependency/package jobs completed or up to date.
- Exact public statement, with repeated definitions and original hypotheses: passed.
- Axiom audit of the final theorem and exact restatement: only `propext`, `Classical.choice`, and `Quot.sound`.
- `lake env leanchecker --fresh -v Erdos291Criterion.Audit`: passed, exit status 0, replaying the entire imported environment into a fresh environment. This is the bundled Lean implementation, not an independent checker implementation.
- Boundary checks passed: prime 2; prime 11 with leading digit 3; failure of the unrestricted equivalence when n=2 and p=3.
- Neither Lean proof file contains a placeholder, custom axiom, native-decide shortcut, unsafe declaration, or kernel-check bypass.

Environment: Lean 4.33.1, compiler revision `819816b2e0a3bf405af45ae5c7af2491d8f5bee6`; mathlib `0df444a360eaa60ab8c11dca51a86af692955474`. The official Lean archive checksum was matched against its release API digest; see `toolchain.txt`.

Formal Conjectures source: `40e7c98697de6f66b8cbdbf641749ab39ed9c152`. Prize repository baseline: `f4e7173d89dfe91022a185427d63452c8ffbf6ae`.

The prior-art check included current prize issues/PRs through #275, the pinned Formal Conjectures source, plby/lean-proofs at `8822f7ddef30fadbd92e1c6ab4ed897af356af5e`, and the related public developments linked in the README. No matching all-prime necessary-and-sufficient formalization was found in this search; this is not an exhaustive priority claim.

This formalizes Steinerberger's existing criterion. It does not solve the remaining open parts of Erdős 291, establish eligibility, or replace organizer review. Prize repository checks are reported separately; they do not verify mathematical truth.

## Verification-command correction, 2026-09-17 UTC

The script now uses `lean -E warning` instead of the unsupported `lean --wfail` flag. The corrected exact-statement/axiom command was run successfully (exit status 0); see `command-fix-audit.txt`. The Lean proof sources are unchanged. Their previously recorded full kernel replay remains the proof verification evidence.
