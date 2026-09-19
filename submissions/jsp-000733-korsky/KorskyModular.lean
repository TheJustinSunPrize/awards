import KorskyDefs
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
Finite modular form of Korsky's ordered ternary packing argument.
The two collision lemmas are supplied by KorskyInject in the final assembly.
-/
namespace Erdos882Korsky

theorem total_pos {k : ℕ} (hk : 0 < k) (a : Fin k → ℕ)
    (ha : ∀ i, 0 < a i) : 0 < total a := by
  unfold total
  let : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
  exact Finset.sum_pos (fun i _ => ha i) Finset.univ_nonempty

theorem value_pos {k : ℕ} (a : Fin k → ℕ) (ha : ∀ i, 0 < a i)
    (w : Word k) (hw : Good w) : 0 < value a w := by
  classical
  obtain ⟨i, hi⟩ := hw.2
  have hnonneg : ∀ j ∈ (Finset.univ : Finset (Fin k)),
      0 ≤ (w j : ℤ) * (a j : ℤ) := by
    intro j _
    positivity
  have hle := Finset.single_le_sum hnonneg (Finset.mem_univ i)
  have hp : 0 < (w i : ℤ) * (a i : ℤ) := by
    rw [hi]
    have : (0 : ℤ) < a i := by exact_mod_cast ha i
    norm_num
    omega
  exact lt_of_lt_of_le hp hle

theorem value_le_twice_total {k : ℕ} (a : Fin k → ℕ) (w : Word k) :
    value a w ≤ 2 * (total a : ℤ) := by
  unfold value total
  rw [Nat.cast_sum, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  have hw : (w i : ℤ) ≤ 2 := by
    have := (w i).isLt
    omega
  exact mul_le_mul_of_nonneg_right hw (by positivity)

theorem good_card_le_total {k : ℕ} (hk : 0 < k) (a : Fin k → ℕ)
    (ha : ∀ i, 0 < a i)
    (hzero : ∀ u v : Word k, Good u → Good v → value a u = value a v → u = v)
    (hstep : ∀ u v : Word k, Good u → Good v →
      value a u ≠ value a v + (total a : ℤ)) :
    Fintype.card {w : Word k // Good w} ≤ total a := by
  classical
  have hS : 0 < total a := total_pos hk a ha
  have hSz : (0 : ℤ) < total a := by exact_mod_cast hS
  let : NeZero (total a) := ⟨ne_of_gt hS⟩
  let f : {w : Word k // Good w} → ZMod (total a) := fun w => (value a w.1 : ZMod _)
  have hf : Function.Injective f := by
    intro u v huv
    have hd : (total a : ℤ) ∣ value a v.1 - value a u.1 :=
      (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mp huv
    obtain ⟨z, hz⟩ := hd
    have hu0 := value_pos a ha u.1 u.2
    have hv0 := value_pos a ha v.1 v.2
    have hu2 := value_le_twice_total a u.1
    have hv2 := value_le_twice_total a v.1
    have hzlo : -2 < z := by
      by_contra h
      have hmul := mul_le_mul_of_nonneg_left (show z ≤ (-2 : ℤ) by omega) (le_of_lt hSz)
      nlinarith
    have hzhi : z < 2 := by
      by_contra h
      have hmul := mul_le_mul_of_nonneg_left (show (2 : ℤ) ≤ z by omega) (le_of_lt hSz)
      nlinarith
    have hz_cases : z = -1 ∨ z = 0 ∨ z = 1 := by omega
    rcases hz_cases with hz1 | hz0 | hz1
    · subst z
      exact False.elim (hstep u.1 v.1 u.2 v.2 (by linarith))
    · subst z
      apply Subtype.ext
      exact hzero u.1 v.1 u.2 v.2 (by linarith)
    · subst z
      exact False.elim (hstep v.1 u.1 v.2 u.2 (by linarith))
  simpa only [ZMod.card] using Fintype.card_le_of_injective f hf

end Erdos882Korsky
