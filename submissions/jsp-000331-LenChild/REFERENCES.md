# Sources and contribution attribution

## Existing mathematical and formal work

- R. Balasubramanian and K. Soundararajan, *On a conjecture of R. L. Graham*,
  Acta Arithmetica 75 (1996), 1–38, as cited by the upstream formalization.
- [Erdős problem 402](https://www.erdosproblems.com/402) and the
  [discussion](https://www.erdosproblems.com/forum/thread/402).
- [plby/lean-proofs, Erdos402.lean](https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos402.lean),
  commit `8822f7ddef30fadbd92e1c6ab4ed897af356af5e`. The file credits the
  informal authors above, Formal Conjectures authors for the statement,
  and Codex / GPT-5.6 Sol for the formalization. Boris Alexeev publishes the
  repository. These are source attributions, not prize-recipient nominations.
- [MediumPNT.lean](https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/PrimeNumberTheoremAnd/MediumPNT.lean)
  from the same commit supplies the analytic interface.
- [FormalPantheon / BoundedGaps](https://github.com/frenzymath/FormalPantheon/tree/ffbb65c21afc8a36ace67720f1b0df1c63d26bd1/BoundedGaps),
  commit `ffbb65c21afc8a36ace67720f1b0df1c63d26bd1`, supplies the strong
  Chebyshev estimate and its supporting proofs. Its repository includes an
  [Apache-2.0 license](https://github.com/frenzymath/FormalPantheon/blob/ffbb65c21afc8a36ace67720f1b0df1c63d26bd1/LICENSE).
- [mathlib](https://github.com/leanprover-community/mathlib4/tree/db584cd6d46c92f209a44c0f1c829460d327499d),
  commit `db584cd6d46c92f209a44c0f1c829460d327499d`, and Lean 4.33.0.

The bootstrap applies three compatibility patches from the pinned
`plby/lean-proofs/src/latest/patches` directory: `formalpantheon-v4.33.0.patch`,
`formalpantheon-v4.33.0-s2.patch`, and `boundedgaps-linter-v4.33.0.patch`.
They are upstream adaptations, not our contributions. The first two touch
no module in this theorem's import closure; the third touches eleven.
The three main proof files are used byte-for-byte as downloaded. All
downloaded assets and the resulting source closure are hashed in
`source-lock.json`.

## License boundary

At the pinned commit, plby/lean-proofs has no root blanket license. Its
[`src/latest/LICENSE`](https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/LICENSE)
says that **some files** from external sources are Apache-2.0 licensed.
That notice does not establish an Apache-2.0 license for the entire
Erdos402 formalization. We do not assert such a license or sublicense it.

This package contains source URLs, hashes, original wrappers, and original
verification tooling. Upstream sources, notices, and compatibility patches
are fetched into an ignored local directory instead of redistributed in
the submission. Attribution and a download mechanism do not themselves
resolve any upstream reuse-rights question.

## This package's contribution

- An explicit JSP catalog statement, direct bridge to the existing theorem,
  and a proof that the witnesses can be chosen distinct for sufficiently large sets.
- A minimal reproduction configuration that imports the necessary analytic
  dependency rather than all unrelated developments in the upstream repository.
- Pinned downloads, post-patch integrity checks, a reproducible build procedure,
  a final-declaration axiom allowlist, and Lean kernel replay tooling.
- Scope and attribution documentation separating existing proof work from
  our verification work. Actual successful checks must be supported by the
  generated verification report; writing a verifier is not proof of a passed run.
