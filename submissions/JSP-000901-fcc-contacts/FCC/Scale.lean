import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Find
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

namespace FCC

theorem exists_box_scale (n : ℕ) (hn : 4 ≤ n) :
    ∃ m : ℕ, 1 ≤ m ∧ 4*m^3 ≤ n ∧ n < 4*(m+1)^3 := by
  have hex : ∃ k : ℕ, n < 4*k^3 := by
    refine ⟨n+1, ?_⟩
    nlinarith [Nat.zero_le (n^3), Nat.zero_le (n^2)]
  let k := Nat.find hex
  have hk : n < 4*k^3 := Nat.find_spec hex
  have hkpos : 1 ≤ k := by
    by_contra h
    have : k = 0 := by omega
    simp [this] at hk
  have hklarge : 2 ≤ k := by
    by_contra h
    have : k = 1 := by omega
    simp [this] at hk
    omega
  refine ⟨k-1, by omega, ?_, ?_⟩
  · have hmin := Nat.find_min hex (show k-1 < k by omega)
    omega
  · simpa [Nat.sub_add_cancel hkpos] using hk

theorem scale_square_le_rpow {m n : ℕ} (h : 4*m^3 ≤ n) :
    (m : ℝ)^2 ≤ (n : ℝ)^(2/3 : ℝ) := by
  have h' : (m : ℝ)^3 ≤ n := by
    have hm : m^3 ≤ n := by omega
    exact_mod_cast hm
  calc
    (m : ℝ)^2 = ((m : ℝ)^3)^(2/3 : ℝ) := by
      rw [← Real.rpow_natCast (m : ℝ) 3,
        ← Real.rpow_mul (Nat.cast_nonneg m)]
      norm_num
    _ ≤ (n : ℝ)^(2/3 : ℝ) :=
      Real.rpow_le_rpow (by positivity) h' (by norm_num)

theorem contact_count_lower_bound {m n : ℕ} (hm : 1 ≤ m)
    (hlo : 4*m^3 ≤ n) (hhi : n < 4*(m+1)^3) :
    6*(n : ℝ) - 200*(n : ℝ)^(2/3 : ℝ) ≤
      (6*m*(2*m-1)^2 : ℕ) := by
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hn' : (n : ℝ) < 4*((m : ℝ)+1)^3 := by exact_mod_cast hhi
  have hs := scale_square_le_rpow hlo
  have hsquare : (m : ℝ) ≤ (m : ℝ)^2 := by nlinarith
  have htwo : 1 ≤ 2*m := by omega
  have hc : ((6*m*(2*m-1)^2 : ℕ) : ℝ) =
      24*(m : ℝ)^3 - 24*(m : ℝ)^2 + 6*(m : ℝ) := by
    rw [Nat.cast_mul, Nat.cast_pow, Nat.cast_sub htwo]
    push_cast
    ring
  rw [hc]
  nlinarith [sq_nonneg ((m : ℝ)-1)]

end FCC
