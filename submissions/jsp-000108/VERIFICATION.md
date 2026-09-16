# Verification record

This package was checked locally from the package directory using the pinned
public files.

- Lean toolchain: `leanprover/lean4:v4.33.1` (compiler commit
  `819816b2e0a3bf405af45ae5c7af2491d8f5bee6`).
- Mathlib: revision
  `0df444a360eaa60ab8c11dca51a86af692955474`; transitive revisions are pinned
  in `lake-manifest.json`.
- Public source commit: `plby/lean-proofs`
  `8822f7ddef30fadbd92e1c6ab4ed897af356af5e`.
- The copied `ErdosProblems/Erdos92.lean` SHA-256 is
  `f87842ac1e3d6641d6bdc376b8c74b3380b34ceb36e27eb68285dadc1230238d`.

The following commands completed successfully:

```sh
./verify.sh
lake build
lake env lean ErdosProblems/Erdos92.lean
lake env lean JSP000108.lean
```

The pinned build completed **8740 jobs**. The source and wrapper axiom reports
use only the standard Lean foundations:

- `Erdos90b.not_erdos_90`: `[propext, Classical.choice, Quot.sound]`;
- `JSP000108.not_jsp_000108`: `[propext, Classical.choice, Quot.sound]`;
- `JSP000108.answer_false_iff`: `[propext, Classical.choice, Quot.sound]`.

The forbidden-escape scan in `verify.sh` found no `sorry`, `admit`, `sorryAx`,
`native_decide`, or `unsafe` token in any Lean source. The source proof is a
pinned public formalization; this package does not add a custom axiom or an
external oracle.

This is a local Lean kernel build and axiom report. It is not an independent
mathematical review, an independently implemented checker, an official JSP
verification decision, an award decision, or recipient confirmation.
