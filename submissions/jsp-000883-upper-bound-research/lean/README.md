# Target-only Lean starting point

`JSP000883/Targets.lean` defines the construction and four propositions to prove.
No theorem proving these propositions is supplied. Missing proofs are not
disguised by placeholders or custom axioms.

The definitions were checked with Lean 4.33.0 and Mathlib
`db584cd6d46c92f209a44c0f1c829460d327499d` in an existing pinned environment,
with exit code 0. A declaration audit confirmed the four claims have type
`Prop`; it did not supply proofs of them.

A developer can prepare a standalone environment here with:

```sh
lake update
lake exe cache get
lake build
```

Success checks definitions only. The
[formalization plan](../docs/FORMALIZATION_PLAN.md) lists the remaining work.
There is no completed final-theorem axiom audit or kernel replay.
