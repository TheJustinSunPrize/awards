# Local verification evidence

Date: 2026-09-16 (Asia/Shanghai).

- Compiler: Lean 4.34.0, arm64-apple-darwin24.6.0, Release.
- Compiler commit: `293d5d0c0c3f3dded4688b3ccd6a33939ac5102b`.
- Library: bundled Std, same release; no external dependencies.
- Source compilation and object generation: passed, exit code 0.
- `leanchecker -v Proof`: passed, exit code 0.
- `#print axioms` for both final declarations: `[propext, Quot.sound]`.
- No custom axioms, `sorry`, `admit`, `native_decide` or unsafe proof code.

The official compiler archive SHA-256 was checked against the GitHub release API:
`69f263fa6e21bbc2466bbfb1affcd92479ee2714c883a07de548e099a5922932`.

[Compiler release](https://github.com/leanprover/lean4/releases/tag/v4.34.0).

`leanchecker` replays declarations with the same Lean kernel. It is not an
independently implemented checker. No independent verifier attestation, curator
signature, approved minimum-safe-version determination, permanent archive DOI,
official sandbox verification, or award decision is asserted.

The recorded log is local evidence. Reproduce it with `sh verify.sh` rather than
treating a saved log as proof of a fresh run. The proof source is pinned by the
repository commit; `SHA256SUMS` gives the corresponding source-file hashes.
