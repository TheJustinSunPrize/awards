# Verification record

## English

The proof package was checked locally with the pinned public package files.

- Lean toolchain: `leanprover/lean4:v4.33.1` (compiler commit
  `819816b2e0a3bf405af45ae5c7af2491d8f5bee6`).
- Mathlib: revision
  `0df444a360eaa60ab8c11dca51a86af692955474`, with the transitive revisions
  recorded in `lake-manifest.json`.
- Proof source: `Erdos1077.lean`, SHA-256
  `badfcef2b725bb6ea72d752f8d661c1991db9ba6bb1ae692c40c860504f84c93`, copied
  byte-for-byte from the pinned public `plby/lean-proofs` source commit
  `dfe2d78128b493c572cf525b1b8edf4897fb7664`.
- JSP adapter: `JSP000660.lean`, which defines the exact target proposition and
  proves both its negation and the corresponding `False` equivalence.

The following commands completed successfully:

```sh
./verify.sh
lake build
lake env lean Erdos1077.lean
lake env lean JSP000660.lean
```

The audited declarations report only the standard Lean axioms
`[propext, Classical.choice, Quot.sound]`:

- `Erdos1077.not_erdos_1077`
- `JSP000660.not_jsp_000660`
- `JSP000660.answer_false_iff`

The source tree contains no `sorry`, `admit`, `sorryAx`, `native_decide`, or
`unsafe` proof escape. The build uses ordinary Mathlib imports and the proof's
explicit complete-bipartite counterexample; no custom axiom is added.

This is a local Lean kernel check using pinned dependencies, not an
independently implemented checker, independent mathematical review, award
decision, or recipient confirmation. The source paper and formal-statement
correspondence are documented in `STATEMENT.md`.
