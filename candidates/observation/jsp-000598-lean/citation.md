# Citation

## English

Lean formalization submission for JSP-000598 (Erdős Problem #730), contributed by
TanHao (doge@tidalboundary.fun).

Contribution role: **Lean formalization**. Candidate record awaiting maintainer verification.

Lean proof repository: https://github.com/doge-th/jsp-lean-proofs — file `proofs/JSP-000598.lean`.
Toolchain: Lean 4.35.0-rc1 + Mathlib4. No `native_decide`, no `sorry`;
`#print axioms` on every theorem returns only propext, Classical.choice and
Quot.sound.

The formalization proves the finite/existential content of the catalog
question with both Erdős–Graham–Ruzsa–Straus examples `(87, 88)` and
`(607, 608)`, together with Kummer's bound and the central-binomial
recurrence. The asymptotic density claim of the cited write-up is
explicitly out of scope and is not claimed here.

No award is claimed at this stage; mathematical review and solver
registration precede Lean verification per the documented process.
