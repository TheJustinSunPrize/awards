/-
Copyright 2026 The Formal Conjectures Authors.
Licensed under the Apache License, Version 2.0.

The definition below is reproduced from FormalConjectures/ErdosProblems/1063.lean
at 40e7c98697de6f66b8cbdbf641749ab39ed9c152.
-/
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Order.Lattice.Nat

namespace Erdos1063

/-- The least n ≥ 2k for which exactly one of n, …, n-k+1 fails to divide C(n,k). -/
noncomputable def n (k : ℕ) : ℕ :=
  sInf {m | 2 * k ≤ m ∧
    ∃ i0 < k, ¬ (m - i0) ∣ m.choose k ∧
      ∀ i < k, i ≠ i0 → (m - i) ∣ m.choose k}

end Erdos1063
