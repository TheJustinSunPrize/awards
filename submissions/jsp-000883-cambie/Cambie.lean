import Statement
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Nat.GCD.BigOperators

/-!
Cambie's least-common-multiple upper bound. Mathematical credit: Stijn Cambie.
This file uses Mathlib without importing unproved Formal Conjectures declarations.
-/

namespace Erdos1063

/-- Derive the finite product formula by binomial recurrence and positive-factor cancellation. -/
theorem choose_pred_eq_prod (N m : ℕ) (q : ℕ → ℕ)
    (h : ∀ j ∈ Finset.Icc 1 m, N - j = j * q j) :
    (N - 1).choose m = ∏ j ∈ Finset.Icc 1 m, q j := by
  revert h
  induction m with
  | zero => intro h; simp
  | succ m ih =>
    intro h
    have hprev : ∀ j ∈ Finset.Icc 1 m, N - j = j * q j := by
      intro j hj
      exact h j (Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hj).1,
        (Finset.mem_Icc.mp hj).2.trans (Nat.le_succ m)⟩)
    have hlast : N - (m + 1) = (m + 1) * q (m + 1) :=
      h (m + 1) (Finset.mem_Icc.mpr ⟨by omega, le_rfl⟩)
    apply Nat.mul_right_cancel (Nat.succ_pos m)
    calc
      (N - 1).choose (m + 1) * (m + 1) =
          (N - 1).choose m * (N - 1 - m) := Nat.choose_succ_right_eq _ _
      _ = (∏ j ∈ Finset.Icc 1 m, q j) * ((m + 1) * q (m + 1)) := by
        rw [ih hprev, show N - 1 - m = N - (m + 1) by omega, hlast]
      _ = (∏ j ∈ Finset.Icc 1 (m + 1), q j) * (m + 1) := by
        rw [Finset.prod_Icc_succ_top (by omega : 1 ≤ m + 1)]
        ac_rfl

/-- `k * lcm(1,...,k-1)` belongs to the defining set, with unique exceptional offset `0`. -/
theorem cambie_witness {k : ℕ} (hk : 3 ≤ k) :
    let N := k * (Finset.Icc 1 (k - 1)).lcm id
    2 * k ≤ N ∧
      ∃ i0 < k, ¬ (N - i0) ∣ N.choose k ∧
        ∀ i < k, i ≠ i0 → (N - i) ∣ N.choose k := by
  let L : ℕ := (Finset.Icc 1 (k - 1)).lcm id
  let q : ℕ → ℕ := fun j => k * (L / j) - 1
  have hkpos : 0 < k := by omega
  have hLpos : 0 < L := by
    apply Nat.pos_of_ne_zero
    apply Finset.lcm_ne_zero_iff.mpr
    intro j hj
    have hjpos := (Finset.mem_Icc.mp hj).1
    change j ≠ 0
    omega
  have hdvd : ∀ j ∈ Finset.Icc 1 (k - 1), j ∣ L := by
    intro j hj
    exact Finset.dvd_lcm hj
  have hLtwo : 2 ≤ L := by
    apply Nat.le_of_dvd hLpos
    exact hdvd 2 (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
  have hq : ∀ j ∈ Finset.Icc 1 (k - 1), k * L - j = j * q j := by
    intro j hj
    dsimp [q]
    rw [Nat.mul_sub_left_distrib, Nat.mul_one]
    congr 1
    calc
      k * L = k * (j * (L / j)) := by rw [Nat.mul_div_cancel' (hdvd j hj)]
      _ = j * (k * (L / j)) := by ac_rfl
  have hchoose : (k * L).choose k = L * ∏ j ∈ Finset.Icc 1 (k - 1), q j := by
    calc
      (k * L).choose k = L * (k * L - 1).choose (k - 1) := by
        simpa only [Nat.mul_comm L k] using
          (Nat.choose_mul_right (m := L) (n := k) (Nat.ne_of_gt hkpos))
      _ = L * ∏ j ∈ Finset.Icc 1 (k - 1), q j := by
        rw [choose_pred_eq_prod (k * L) (k - 1) q hq]
  have hcop : Nat.Coprime k (∏ j ∈ Finset.Icc 1 (k - 1), q j) := by
    apply Nat.coprime_prod_right_iff.mpr
    intro j hj
    have hjpos : 0 < j := by have := (Finset.mem_Icc.mp hj).1; omega
    have hdivpos : 0 < L / j := Nat.div_pos (Nat.le_of_dvd hLpos (hdvd j hj)) hjpos
    have hmulpos : 1 ≤ k * (L / j) := Nat.mul_pos hkpos hdivpos
    have hconsecutive : Nat.Coprime (k * (L / j)) (k * (L / j) - 1) :=
      (Nat.coprime_self_sub_right hmulpos).mpr (Nat.coprime_one_right _)
    exact hconsecutive.coprime_dvd_left (dvd_mul_right k (L / j))
  have hnot : ¬ k * L ∣ (k * L).choose k := by
    intro h
    rw [hchoose] at h
    have hkp : k ∣ ∏ j ∈ Finset.Icc 1 (k - 1), q j := by
      apply (Nat.mul_dvd_mul_iff_left hLpos).mp
      simpa only [Nat.mul_comm k L] using h
    have : k = 1 := Nat.eq_one_of_dvd_coprimes hcop (dvd_refl k) hkp
    omega
  change 2 * k ≤ k * L ∧
    ∃ i0 < k, ¬ (k * L - i0) ∣ (k * L).choose k ∧
      ∀ i < k, i ≠ i0 → (k * L - i) ∣ (k * L).choose k
  refine ⟨?_, 0, hkpos, ?_, ?_⟩
  · simpa only [Nat.mul_comm 2 k] using Nat.mul_le_mul_left k hLtwo
  · simpa only [Nat.sub_zero] using hnot
  · intro i hi hi0
    have himem : i ∈ Finset.Icc 1 (k - 1) := Finset.mem_Icc.mpr ⟨by omega, by omega⟩
    rw [hq i himem, hchoose]
    exact Nat.mul_dvd_mul (hdvd i himem) (Finset.dvd_prod_of_mem q himem)

/-- Cambie's known least-common-multiple upper bound for every natural number `k ≥ 3`. -/
theorem erdos_1063.variants.cambie_upper_bound {k : ℕ} (hk : 3 ≤ k) :
    n k ≤ k * (Finset.Icc 1 (k - 1)).lcm id := by
  apply Nat.sInf_le
  exact cambie_witness hk

end Erdos1063
