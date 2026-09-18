import JSP000853.ArbitraryUpper
import JSP000853.Sampling

/-!
# The universal lower bound

This is a finite-counting version of the standard random-sampling proof.
Colour the vertices with `q` colours, retain one colour class, and delete the
output of every bad internal pair.  Exact double counts replace probability.
-/

namespace JSP000853

open scoped BigOperators

set_option linter.style.haveILetI false

namespace PairMapping

theorem exists_colorClass_scaled_bound {n q : ℕ} (hn : 3 ≤ n) (hqpos : 0 < q)
    (hq : 2 * n ≤ q ^ 2) (f : PairMapping (Fin n)) :
    ∃ c : Fin n → Fin q,
      q ^ 3 * (f.badPairs (colorClass ⟨0, hqpos⟩ c)).card + n ^ 2 ≤
        q ^ 3 * (colorClass ⟨0, hqpos⟩ c).card := by
  letI : Nonempty (Fin q) := ⟨⟨0, hqpos⟩⟩
  let b : Fin q := ⟨0, hqpos⟩
  apply exists_scaled_bad_add_le_good
    (fun c : Fin n → Fin q ↦ (colorClass b c).card)
    (fun c : Fin n → Fin q ↦ (f.badPairs (colorClass b c)).card)
    (q ^ 3) (n ^ 2)
  rw [f.sum_card_badPairs_colorClass, sum_card_colorClass,
    Fintype.card_fun, Fintype.card_fin]
  simp only [Fintype.card_fin]
  have hbase : n * (n - 1) + n ^ 2 ≤ n * q ^ 2 := by
    calc
      n * (n - 1) + n ^ 2 ≤ n * n + n ^ 2 := by
        exact Nat.add_le_add_right (Nat.mul_le_mul_left n (Nat.sub_le n 1)) _
      _ = n * (2 * n) := by
        simp only [pow_two]
        rw [← Nat.mul_add, two_mul]
      _ ≤ n * q ^ 2 := Nat.mul_le_mul_left n hq
  have hn_decomp : n - 3 + 3 = n := Nat.sub_add_cancel hn
  have hnm1_decomp : n - 1 = (n - 3) + 2 := by
    rw [← hn_decomp]
    simp
  have hpow_n : q ^ n = q ^ (n - 3) * q ^ 3 := by
    calc
      q ^ n = q ^ ((n - 3) + 3) := congrArg (q ^ ·) hn_decomp.symm
      _ = q ^ (n - 3) * q ^ 3 := pow_add q (n - 3) 3
  have hpow_nm1 : q ^ (n - 1) = q ^ (n - 3) * q ^ 2 := by
    calc
      q ^ (n - 1) = q ^ ((n - 3) + 2) := congrArg (q ^ ·) hnm1_decomp
      _ = q ^ (n - 3) * q ^ 2 := pow_add q (n - 3) 2
  let factor := q ^ 3 * q ^ (n - 3)
  calc
    q ^ 3 * ((n * (n - 1)) * q ^ (n - 3)) + q ^ n * n ^ 2 =
        factor * (n * (n - 1)) + factor * n ^ 2 := by
      rw [hpow_n]
      dsimp [factor]
      congr 1 <;> ac_rfl
    _ = factor * (n * (n - 1) + n ^ 2) := by rw [Nat.mul_add]
    _ ≤ factor * (n * q ^ 2) := Nat.mul_le_mul_left factor hbase
    _ = q ^ 3 * (n * q ^ (n - 1)) := by
      rw [hpow_nm1]
      dsimp [factor]
      ac_rfl

/-- Every admissible mapping on at least three vertices has a free set `S`
with `n ≤ 512 |S|²`. -/
theorem exists_large_free_set {n : ℕ} (hn : 3 ≤ n) (f : PairMapping (Fin n)) :
    ∃ S : Finset (Fin n), f.IsFree S ∧ n ≤ 512 * S.card ^ 2 := by
  let q : ℕ := gridSide (2 * n)
  have hnpos : 0 < n := lt_of_lt_of_le (by decide : 0 < 3) hn
  have htwonpos : 0 < 2 * n := Nat.mul_pos (by decide) hnpos
  have hqpos : 0 < q := by
    dsimp [q, gridSide]
    exact Nat.zero_lt_succ _
  have hqlower : 2 * n ≤ q ^ 2 := by
    exact le_gridSide_sq (2 * n)
  have hqupper : q ^ 2 ≤ 8 * n := by
    have h := gridSide_sq_le_four_mul htwonpos
    dsimp [q]
    calc
      gridSide (2 * n) ^ 2 ≤ 4 * (2 * n) := h
      _ = 8 * n := by ac_rfl
  obtain ⟨c, hc⟩ := f.exists_colorClass_scaled_bound hn hqpos hqlower
  let b : Fin q := ⟨0, hqpos⟩
  let R : Finset (Fin n) := colorClass b c
  let S : Finset (Fin n) := f.cleaned R
  refine ⟨S, f.cleaned_isFree R, ?_⟩
  have hcover : R.card ≤ S.card + (f.badPairs R).card := by
    exact f.card_le_cleaned_add_badPairs R
  have hmul : q ^ 3 * R.card ≤
      q ^ 3 * S.card + q ^ 3 * (f.badPairs R).card := by
    have := Nat.mul_le_mul_left (q ^ 3) hcover
    simpa only [Nat.mul_add] using this
  have hscaled : q ^ 3 * (f.badPairs R).card + n ^ 2 ≤
      q ^ 3 * S.card + q ^ 3 * (f.badPairs R).card := by
    exact hc.trans hmul
  have hn2 : n ^ 2 ≤ q ^ 3 * S.card := by
    apply Nat.le_of_add_le_add_left
    calc
      q ^ 3 * (f.badPairs R).card + n ^ 2 ≤
          q ^ 3 * S.card + q ^ 3 * (f.badPairs R).card := hscaled
      _ = q ^ 3 * (f.badPairs R).card + q ^ 3 * S.card := Nat.add_comm _ _
  have hn4 : n ^ 4 ≤ q ^ 6 * S.card ^ 2 := by
    have hsquare := Nat.pow_le_pow_left hn2 2
    calc
      n ^ 4 = (n ^ 2) ^ 2 := by rw [← pow_mul]
      _ ≤ (q ^ 3 * S.card) ^ 2 := hsquare
      _ = q ^ 6 * S.card ^ 2 := by
        rw [mul_pow, ← pow_mul]
  have hq6 : q ^ 6 ≤ 512 * n ^ 3 := by
    have hcube := Nat.pow_le_pow_left hqupper 3
    calc
      q ^ 6 = (q ^ 2) ^ 3 := by rw [← pow_mul]
      _ ≤ (8 * n) ^ 3 := hcube
      _ = 512 * n ^ 3 := by rw [mul_pow]; rfl
  have hbound : n ^ 4 ≤ (512 * n ^ 3) * S.card ^ 2 :=
    hn4.trans (Nat.mul_le_mul_right (S.card ^ 2) hq6)
  have hcancel : n ^ 3 * n ≤ n ^ 3 * (512 * S.card ^ 2) := by
    calc
      n ^ 3 * n = n ^ 4 := (pow_succ n 3).symm
      _ ≤ (512 * n ^ 3) * S.card ^ 2 := hbound
      _ = n ^ 3 * (512 * S.card ^ 2) := by ac_rfl
  exact Nat.le_of_mul_le_mul_left hcancel (pow_pos hnpos 3)

end PairMapping

/-- The lower-bound half of Erdős Problem #1025, with an explicit constant. -/
theorem erdos1025_lowerBound : LowerBoundTarget := by
  refine ⟨512, by decide, ?_⟩
  intro n f
  by_cases hn : 3 ≤ n
  · exact f.exists_large_free_set hn
  · have hnle : n ≤ 2 := Nat.le_of_lt_succ (Nat.lt_of_not_ge hn)
    by_cases hnzero : n = 0
    · subst n
      exact ⟨∅, f.isFree_empty, by simp⟩
    · have hnpos : 0 < n := Nat.pos_of_ne_zero hnzero
      let x : Fin n := ⟨0, hnpos⟩
      refine ⟨{x}, f.isFree_singleton x, ?_⟩
      simpa using hnle.trans (by decide : 2 ≤ 512)

/-- Complete formal statement: `g(n) = Θ(√n)`. -/
theorem erdos1025 : Erdos1025Target :=
  ⟨erdos1025_lowerBound, erdos1025_upperBound⟩

end JSP000853
