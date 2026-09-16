import KorskyBalancedDefs
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fin.Rev

/-!
The upper end of the balanced-word interval in Korsky's Section 3.
This proof budgets the reversed coordinate ranks directly, without sorting
individual selected subsets or introducing the author's intermediate R.
-/

namespace Erdos882Korsky

private lemma cutoff_sum (k t : ℕ) (ht : t ≤ k) :
    2 * (∑ i : Fin k, (t - i.val)) = t * (t + 1) := by
  induction k generalizing t with
  | zero =>
      have : t = 0 := by omega
      simp [this]
  | succ k ih =>
      by_cases htk : t ≤ k
      · rw [Fin.sum_univ_castSucc]
        simp only [Fin.val_castSucc, Fin.val_last]
        have hz : t - k = 0 := by omega
        rw [hz, add_zero]
        exact ih t htk
      · have he : t = k + 1 := by omega
        subst t
        rw [Fin.sum_univ_succ]
        simp only [Fin.val_zero, Nat.sub_zero, Fin.val_succ, Nat.add_sub_add_right]
        have h := ih k le_rfl
        nlinarith

private lemma reversed_cutoff_sum (k t : ℕ) (ht : t ≤ k) :
    2 * (∑ i : Fin k, (t - (k - 1 - i.val))) = t * (t + 1) := by
  have hs : (∑ i : Fin k, (t - (k - 1 - i.val))) = ∑ i : Fin k, (t - i.val) := by
    calc
      _ = ∑ i : Fin k, (t - ((Fin.revPerm : Equiv.Perm (Fin k)) i).val) := by
        apply Finset.sum_congr rfl
        intro i _
        congr 1
        change k - 1 - i.val = k - (i.val + 1)
        omega
      _ = _ := Equiv.sum_comp (Fin.revPerm : Fin k ≃ Fin k) (fun i : Fin k => t - i.val)
  rw [hs]
  exact cutoff_sum k t ht

private lemma quarter_identity (k : ℕ) :
    (k - 1)^2 / 4 + (k / 2) * (k / 2 + 1) = (k / 2) * k := by
  obtain ⟨t, rfl | rfl⟩ := Nat.even_or_odd' k
  · by_cases ht : t = 0
    · simp [ht]
    have ht1 : t - 1 + 1 = t := by omega
    have hs : (2 * t - 1)^2 = 4 * (t * (t - 1)) + 1 := by
      have htwo : 2 * t - 1 + 1 = 2 * t := by omega
      nlinarith
    have hd : (2 * t - 1)^2 / 4 = t * (t - 1) := by rw [hs]; omega
    have hh : 2 * t / 2 = t := by omega
    rw [hd, hh]
    nlinarith
  · have hs : (2 * t + 1 - 1)^2 = 4 * t^2 := by
      have : 2 * t + 1 - 1 = 2 * t := by omega
      rw [this]
      ring
    have hd : (2 * t + 1 - 1)^2 / 4 = t^2 := by rw [hs]; omega
    have hh : (2 * t + 1) / 2 = t := by omega
    rw [hd, hh]
    ring

/-- A rank budget valid for every bounded word with total coordinate weight k.
The order condition on the word is not needed for this inequality. -/
lemma rank_weight_floor {k : ℕ} (w : Word k)
    (hw : (∑ i, (w i).val) = k) :
    (k - 1)^2 / 4 ≤ ∑ i, (k - 1 - i.val) * (w i).val := by
  let t := k / 2
  have hp (i : Fin k) :
      t * (w i).val ≤ (k - 1 - i.val) * (w i).val + 2 * (t - (k - 1 - i.val)) := by
    have hwi : (w i).val ≤ 2 := by have := (w i).isLt; omega
    by_cases hr : k - 1 - i.val ≤ t
    · have he : k - 1 - i.val + (t - (k - 1 - i.val)) = t := by omega
      have hm := Nat.mul_le_mul_left (t - (k - 1 - i.val)) hwi
      nlinarith
    · have he : t - (k - 1 - i.val) = 0 := by omega
      rw [he, mul_zero, add_zero]
      exact Nat.mul_le_mul_right _ (by omega)
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin k))) => hp i)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hsum
  rw [hw] at hsum
  have hcut := reversed_cutoff_sum k t (by dsimp [t]; omega)
  rw [hcut] at hsum
  have hq := quarter_identity k
  change (k - 1)^2 / 4 + t * (t + 1) = t * k at hq
  omega

/-- Strictly increasing integer weights leave at least their reverse rank
below the common endpoint. -/
lemma strictMono_rank_gap {k n : ℕ} {a : Fin k → ℕ}
    (ha : StrictMono a) (hmax : ∀ i, a i ≤ n) (i : Fin k) :
    a i + (k - 1 - i.val) ≤ n := by
  induction k generalizing n with
  | zero => exact Fin.elim0 i
  | succ k ih =>
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simpa using hmax (Fin.last k)
      · have ha' : StrictMono (fun j : Fin k => a j.castSucc) := by
          intro j l hjl
          exact ha (by simpa using hjl)
        have hm' : ∀ j : Fin k, a j.castSucc ≤ n - 1 := by
          intro j
          have hj : j.castSucc < Fin.last k := by exact j.isLt
          have hh := ha hj
          have hn := hmax (Fin.last k)
          omega
        have h := ih ha' hm' j
        simp only [Fin.val_castSucc]
        have hj := j.isLt
        have hh := ha (show j.castSucc < Fin.last k from j.isLt)
        have hn := hmax (Fin.last k)
        omega

/-- The upper endpoint of the balanced-word interval. -/
lemma balanced_value_upper {k n : ℕ} {a : Fin k → ℕ}
    (ha : StrictMono a) (hmax : ∀ i, a i ≤ n)
    {w : Word k} (hw : Balanced w) :
    value a w + (((k - 1)^2 / 4 : ℕ) : ℤ) ≤ (k * n : ℕ) := by
  have hpoint (i : Fin k) :
      (w i).val * a i + (k - 1 - i.val) * (w i).val ≤ (w i).val * n := by
    have h := Nat.mul_le_mul_left (w i).val (strictMono_rank_gap ha hmax i)
    nlinarith
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin k))) => hpoint i)
  simp only [Finset.sum_add_distrib, ← Finset.sum_mul] at hsum
  rw [hw.2] at hsum
  have hr := rank_weight_floor w hw.2
  have hnat : (∑ i, (w i).val * a i) + (k - 1)^2 / 4 ≤ k * n := by omega
  have hcast : ((∑ i, (w i).val * a i : ℕ) : ℤ) +
      (((k - 1)^2 / 4 : ℕ) : ℤ) ≤ ((k * n : ℕ) : ℤ) := by exact_mod_cast hnat
  simpa [value] using hcast

end Erdos882Korsky
