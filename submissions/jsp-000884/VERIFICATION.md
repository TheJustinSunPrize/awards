# Verification record

This package was checked locally from its package directory.

- Lean: `leanprover/lean4:v4.33.0`, compiler commit
  `d8b18978322de05a8f3dba51ef03cf5461676c17`.
- Mathlib: `db584cd6d46c92f209a44c0f1c829460d327499d`; all transitive revisions
  are pinned in `lake-manifest.json`.
- Proof source: `plby/lean-proofs` commit
  `8822f7ddef30fadbd92e1c6ab4ed897af356af5e`.
- The copied `ErdosProblems/Erdos1064.lean` and its copied project-local
  dependencies were compared against that commit; the source files are
  byte-identical to the corresponding `src/latest` files.

The following commands completed successfully:

```sh
lake update
./verify.sh
lake build
lake env lean JSP000884.lean
```

The pinned build completed **8729 jobs**.  The wrapper and all three exported
source theorems report only the standard Lean foundations:

```text
[propext, Classical.choice, Quot.sound]
```

The `verify.sh` escape scan found no `sorry`, `admit`, `sorryAx`,
`native_decide`, or `unsafe` token in any copied Lean source, and its axiom
report found no proof-hole or evaluator escape.  The wrapper applies the exact
source theorem declarations; it does not add assumptions or replace the
quantified statements with finite computation.

This is a local Lean kernel elaboration/build and an auditable source/hash
reproduction.  It is not an independently implemented checker, an independent
mathematical review, an official JSP verification decision, an award decision,
or recipient confirmation.  The candidate remains under verification.
