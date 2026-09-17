# Verification record

Status: the full theorem compiled successfully and passed the exact-statement audit, transitive axiom audit, and fresh bundled kernel replay. Checks performed on 2026-09-16 UTC (2026-09-17 Hong Kong time).

## Scope

The final theorem asserts exactly the positive-input finite bound, with an injective map from `Fin t`, `t ≥ 2`, and every exponent at least one. It does not assert the unbounded conjecture.

## Environment

- Lean 4.33.1, official arm64 macOS release, compiler revision `819816b2e0a3bf405af45ae5c7af2491d8f5bee6`.
- mathlib `0df444a360eaa60ab8c11dca51a86af692955474`; complete dependencies in `lake-manifest.json`.
- Formal Conjectures statement snapshot `40e7c98697de6f66b8cbdbf641749ab39ed9c152`.
- Prize repository baseline `f4e7173d89dfe91022a185427d63452c8ffbf6ae`.

## Completed checks

- Fresh kernel replay: `lake env leanchecker --fresh -v Erdos261Finite.FiniteBound` exited 0, replaying the complete imported environment into a fresh environment.
- Toolchain integrity: the downloaded official Lean release archive SHA-256 matches the official release API digest.
- Full build: `lake build Erdos261Finite.FiniteBound` exited 0; 997 dependency/package jobs were up to date or completed successfully.
- Exact statement: `lake env lean Erdos261Finite/Audit.lean` exited 0 against an independently restated public theorem type.
- Transitive axiom audit: the final theorem and semantic bridge lemmas depend only on `propext`, `Classical.choice`, and `Quot.sound`. No `sorryAx` or additional axiom appears.

- Regeneration: all 47 generated Lean files reproduced byte for byte from the C++/Python tooling.
- Negative control: replacing the true next state `(3,1)` of `(2,2)` with `(3,2)` caused `rfl` to fail, as expected.
- Source review: all 49 Lean proof/audit files have no `sorry`, custom `axiom`, `native_decide`, `unsafe` declaration, `implemented_by`, `ofReduceBool`, or kernel-check bypass.
- Prior-art search: the current public prize submissions and `plby/lean-proofs` snapshot `8822f7ddef30fadbd92e1c6ab4ed897af356af5e` contained no matching finite-bound formalization found in this search. This is not a proof of priority.

- Prize repository validation, Markdown link checks, generated-data consistency, and all 22 existing tests pass.

## Limits

The formalized finite theorem is previously published mathematics. Certificate generation is not a mathematical novelty claim. A Lean kernel build and bundled replay use the same Lean implementation; they are not an independent verifier implementation. Committee verification, eligibility, attribution, and any award remain outstanding.
