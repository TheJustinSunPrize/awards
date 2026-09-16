/-
Copyright 2026 The Formal Conjectures Authors (definition `Erdos1063.n`).
Copyright 2026 inoader (new Lean proof implementation, with ChatGPT assistance).
Licensed under the Apache License, Version 2.0; see LICENSE and NOTICE.
-/

import Mathlib.Algebra.BigOperators.ModEq
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

open Finset
open scoped BigOperators Nat

/-!
# Monier's factorial upper bound for Erdős problem 1063

This is a new Lean formalization of Monier's known 1985 bound, not a solution
of the open growth-rate problem. Mathematical credit remains with Monier.
The definition `n` is reproduced from Formal Conjectures at revision
40e7c98697de6f66b8cbdbf641749ab39ed9c152. No unproved declarations are imported.
-/

namespace Erdos1063

noncomputable def n (k : ℕ) : ℕ :=
  sInf {m | 2 * k ≤ m ∧ ∃ i0 < k, ¬ (m - i0) ∣ m.choose k ∧
    ∀ i < k, i ≠ i0 → (m - i) ∣ m.choose k}

lemma factorial_choose (k : ℕ) (hk : 1 ≤ k) :
    (k.factorial).choose k = (k.factorial - 1).descFactorial (k - 1) := by
  have h := Nat.descFactorial_mul_descFactorial (n := k.factorial) hk
  rw [Nat.descFactorial_one] at h
  have h2 := Nat.descFactorial_eq_factorial_mul_choose k.factorial k
  exact Nat.eq_of_mul_eq_mul_left (Nat.factorial_pos k) (by simpa only [mul_comm] using h2.symm.trans h.symm)

lemma desc_mod (N j : ℕ) (hj : j < N) :
    ((N - 1).descFactorial j : ℤ) ≡ (-1 : ℤ)^j * (j ! : ℤ) [ZMOD (N : ℤ)] := by
  rw [Nat.descFactorial_eq_prod_range, Nat.cast_prod]
  have h : (∏ i ∈ range j, ((N - 1 - i : ℕ) : ℤ)) ≡
      (∏ i ∈ range j, -((i + 1 : ℕ) : ℤ)) [ZMOD (N : ℤ)] := by
    apply Int.ModEq.prod
    intro i hi
    have hi' := mem_range.mp hi
    have heq : ((N - 1 - i : ℕ) : ℤ) = (N : ℤ) - (i + 1) := by omega
    rw [heq]
    simpa using ((dvd_refl (N : ℤ)).modEq_zero_int.sub_right ((i : ℤ) + 1))
  convert h using 1
  simp only [Finset.prod_neg, Finset.card_range, ← Nat.cast_prod,
    Finset.prod_range_add_one_eq_factorial]

lemma factorial_not_dvd_choose (k : ℕ) (hk : 2 ≤ k) :
    ¬ k.factorial ∣ (k.factorial).choose k := by
  rw [factorial_choose k (by omega)]
  intro h
  have hj : k - 1 < k.factorial := lt_of_lt_of_le (by omega) (Nat.self_le_factorial k)
  have hm := (desc_mod (k.factorial) (k - 1) hj).dvd_iff.mp (Int.natCast_dvd_natCast.mpr h)
  have hm' : (k.factorial : ℤ) ∣ ((k - 1)! : ℤ) := by
    have hu : IsUnit ((-1 : ℤ) ^ (k - 1)) := (isUnit_neg_one).pow _
    exact (hu.dvd_mul_left).mp hm
  have hd := Int.natCast_dvd_natCast.mp hm'
  have hl := Nat.le_of_dvd (Nat.factorial_pos (k - 1)) hd
  have ht := Nat.factorial_lt_of_lt (n := k - 1) (m := k) (by omega) (by omega)
  omega

lemma factorial_witness (k : ℕ) (hk : 3 ≤ k) :
    2 * k ≤ k.factorial ∧ ¬ k.factorial ∣ (k.factorial).choose k ∧
      ∀ i < k, i ≠ 0 → (k.factorial - i) ∣ (k.factorial).choose k := by
  refine ⟨?_, factorial_not_dvd_choose k (by omega), ?_⟩
  · have h : 2 ≤ (k - 1)! := by simpa using Nat.factorial_le (show 2 ≤ k - 1 by omega)
    rw [← Nat.mul_factorial_pred (show k ≠ 0 by omega)]
    simpa [mul_comm] using Nat.mul_le_mul_left k h
  · intro i hi hi0
    rw [factorial_choose k (by omega), Nat.descFactorial_eq_prod_range]
    have hi' : i - 1 ∈ range (k - 1) := mem_range.mpr (by omega)
    have h := Finset.dvd_prod_of_mem (fun j => k.factorial - 1 - j) hi'
    have heq : k.factorial - 1 - (i - 1) = k.factorial - i := by omega
    simpa only [heq] using h

theorem monier_upper_bound (k : ℕ) (hk : 3 ≤ k) : n k ≤ k.factorial := by
  apply Nat.sInf_le
  obtain ⟨hsize, hno, hall⟩ := factorial_witness k hk
  exact ⟨hsize, 0, by omega, by simpa using hno, hall⟩

/-- The exact threshold is well-defined for every parameter in the original problem. -/
theorem threshold_spec (k : ℕ) (hk : 2 ≤ k) :
    2 * k ≤ n k ∧ ∃ i0 < k, ¬ (n k - i0) ∣ (n k).choose k ∧
      ∀ i < k, i ≠ i0 → (n k - i) ∣ (n k).choose k := by
  apply Nat.sInf_mem (s := {m | 2 * k ≤ m ∧ ∃ i0 < k, ¬ (m - i0) ∣ m.choose k ∧
    ∀ i < k, i ≠ i0 → (m - i) ∣ m.choose k})
  by_cases h3 : 3 ≤ k
  · obtain ⟨hsize, hno, hall⟩ := factorial_witness k h3
    exact ⟨k.factorial, hsize, 0, by omega, by simpa using hno, hall⟩
  · have heq : k = 2 := by omega
    subst k
    exact ⟨4, by decide⟩

#print axioms monier_upper_bound
#print axioms factorial_witness
#print axioms threshold_spec
end Erdos1063
