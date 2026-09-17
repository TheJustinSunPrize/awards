# Candidate observation

## English

This candidate observation is associated with [JSP-000835 — Are there infinitely many consecutive positive integers with equal totients?](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0801-0900.md#JSP-000835). It publishes `Statement.lean` and `Proof.lean` for a complete, machine-checked Lean proof of an explicit instance of consecutive positive integers with equal totients, `φ(15) = φ(16) = 8`, where `φ` is Mathlib's `Nat.totient`. **Scope: this observation records a complete, machine-checked Lean proof of an explicit instance of consecutive positive integers with equal totients, φ(15) = φ(16) = 8. The infinitude question asked by the catalog entry is not addressed, the catalogued problem is not resolved, and no award claim is made.** The catalog entry JSP-000835 remains Open.

The proof source is pinned to [Yaohua-Leo/jsp-000835-lean](https://github.com/Yaohua-Leo/jsp-000835-lean) at commit `660d3b486fb41b3c148f1826aef97355b0305caf` (branch `main`), built with Lean `leanprover/lean4:v4.35.0-rc2` and Mathlib v4.35.0-rc2 (revision `a218e50f981942cba4fd060faff7cae680805062`). `lake env lean JSP000835.lean` compiles with zero output, and `#print axioms` on every theorem reports dependencies only on `propext`, `Classical.choice`, and `Quot.sound`; the proofs contain no `sorry`, no `admit`, and no `native_decide`. These compiler results are reproducibility evidence for the stated formal theorem; they are not official JSP verification or award admission.

Attribution: the consecutive-equal-totients question is a classical open problem in number theory recorded in the Justin Sun Prize catalog (JSP-000835, proposed no later than 1985, no publication source); mathematical credit for the problem belongs to the number theory community. The formalization author is Yaohua-Leo (AI-assisted via ZCode (GLM)).

The candidate remains under verification. No award decision, recipient identity, solver or formalizer credit, payment, or official verification is asserted.
