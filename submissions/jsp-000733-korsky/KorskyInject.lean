import KorskyDefs
import Mathlib.Algebra.BigOperators.Ring.Finset

/-! The finite cancellation and packing lemmas behind Korsky's bound. -/
namespace Erdos882Korsky

lemma noDouble_eq_imp_empty {k : ℕ} {a : Fin k → ℕ}
    (ha : ∀ i, 0 < a i) (hn : NoDouble a)
    (I J : Finset (Fin k)) (heq : (∑ i ∈ I, a i) = 2 * ∑ i ∈ J, a i) :
    I = ∅ ∧ J = ∅ := by
  have hI : I = ∅ := by
    by_contra hi
    have hi' : I.Nonempty := Finset.nonempty_iff_ne_empty.mpr hi
    have hp : 0 < ∑ i ∈ I, a i := Finset.sum_pos (fun i _ => ha i) hi'
    have hj : J.Nonempty := by
      by_contra hj
      have hj' : J = ∅ := Finset.not_nonempty_iff_eq_empty.mp hj
      rw [hj', Finset.sum_empty, mul_zero] at heq
      omega
    exact hn I J hi' hj heq
  refine ⟨hI, ?_⟩
  by_contra hj
  have hj' : J.Nonempty := Finset.nonempty_iff_ne_empty.mpr hj
  have hp : 0 < ∑ i ∈ J, a i := Finset.sum_pos (fun i _ => ha i) hj'
  rw [hI, Finset.sum_empty] at heq
  omega

lemma coefficient_cancel {k : ℕ} {a : Fin k → ℕ}
    (ha : ∀ i, 0 < a i) (hn : NoDouble a) (d : Fin k → ℤ)
    (hd : ∀ i, -2 ≤ d i ∧ d i ≤ 1)
    (hz : ∑ i, d i * (a i : ℤ) = 0) : ∀ i, d i = 0 := by
  classical
  let I : Finset (Fin k) := Finset.univ.filter (fun i => d i = -1 ∨ d i = 1)
  let J : Finset (Fin k) := Finset.univ.filter (fun i => d i = -2 ∨ d i = -1)
  have hsum : (∑ i ∈ I, (a i : ℤ)) - 2 * (∑ i ∈ J, (a i : ℤ)) = 0 := by
    rw [Finset.mul_sum]
    simp only [I, J, Finset.sum_filter]
    rw [← Finset.sum_sub_distrib]
    apply Eq.trans ?_ hz
    apply Finset.sum_congr rfl
    intro i _
    have hdi := hd i
    by_cases hm2 : d i = -2
    · simp [hm2]
    by_cases hm1 : d i = -1
    · simp [hm1]
      ring
    by_cases h0 : d i = 0
    · simp [h0]
    have h1 : d i = 1 := by omega
    simp [h1]
  have hEq : (∑ i ∈ I, a i) = 2 * ∑ i ∈ J, a i := by
    have heq := sub_eq_zero.mp hsum
    exact_mod_cast heq
  obtain ⟨hI, hJ⟩ := noDouble_eq_imp_empty ha hn I J hEq
  intro i
  have hi : ¬ (d i = -1 ∨ d i = 1) := by
    intro hi
    have : i ∈ I := Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩
    simp [hI] at this
  have hj : ¬ (d i = -2 ∨ d i = -1) := by
    intro hj
    have : i ∈ J := Finset.mem_filter.mpr ⟨Finset.mem_univ i, hj⟩
    simp [hJ] at this
  have := hd i
  omega

lemma ordered_no_cross {k : ℕ} {u v : Word k}
    (hu : Ordered u) (hv : Ordered v) {i j : Fin k}
    (hui : u i = 2) (hvi : v i = 0) (huj : u j = 0) (hvj : v j = 2) : False := by
  by_cases hij : i = j
  · subst j
    simp [hui] at huj
  rcases lt_or_gt_of_ne hij with hij | hji
  · exact hu i j hij hui huj
  · exact hv j i hji hvj hvi

lemma ordered_value_injective {k : ℕ} {a : Fin k → ℕ}
    (ha : ∀ i, 0 < a i) (hn : NoDouble a) {u v : Word k}
    (hu : Ordered u) (hv : Ordered v) (h : value a u = value a v) : u = v := by
  classical
  have cancel_one (u v : Word k) (he : value a u = value a v)
      (hb : ∀ i, ¬ (u i = 2 ∧ v i = 0)) : u = v := by
    have hd : ∀ i, -2 ≤ (u i : ℤ) - (v i : ℤ) ∧ (u i : ℤ) - (v i : ℤ) ≤ 1 := by
      intro i
      have hui := (u i).isLt
      have hvi := (v i).isLt
      have hbi := hb i
      have : ¬ ((u i).val = 2 ∧ (v i).val = 0) := by
        intro hh
        apply hbi
        exact ⟨Fin.ext hh.1, Fin.ext hh.2⟩
      change -2 ≤ (↑(u i).val : ℤ) - ↑(v i).val ∧
        (↑(u i).val : ℤ) - ↑(v i).val ≤ 1
      omega
    have hz : ∑ i, ((u i : ℤ) - (v i : ℤ)) * (a i : ℤ) = 0 := by
      simp only [sub_mul, Finset.sum_sub_distrib]
      exact sub_eq_zero.mpr he
    have hd0 := coefficient_cancel ha hn (fun i => (u i : ℤ) - (v i : ℤ)) hd hz
    funext i
    apply Fin.ext
    have := hd0 i
    change (↑(u i).val : ℤ) - ↑(v i).val = 0 at this
    omega
  by_cases hc : ∃ i, u i = 2 ∧ v i = 0
  · obtain ⟨i, hui, hvi⟩ := hc
    symm
    apply cancel_one v u h.symm
    intro j hj
    exact ordered_no_cross hu hv hui hvi hj.2 hj.1
  · apply cancel_one u v h
    simpa only [not_exists] using hc

lemma nonpositive_weighted_sum_zero {k : ℕ} {a : Fin k → ℕ}
    (ha : ∀ i, 0 < a i) (d : Fin k → ℤ) (hd : ∀ i, d i ≤ 0)
    (hz : ∑ i, d i * (a i : ℤ) = 0) : ∀ i, d i = 0 := by
  have hterm : ∀ i, d i * (a i : ℤ) ≤ 0 :=
    fun i => mul_nonpos_of_nonpos_of_nonneg (hd i) (by positivity)
  have he : ∀ i ∈ (Finset.univ : Finset (Fin k)), d i * (a i : ℤ) = 0 :=
    (Finset.sum_eq_zero_iff_of_nonpos (fun i _ => hterm i)).mp hz
  intro i
  have h := he i (Finset.mem_univ i)
  have hai : (0 : ℤ) < a i := by exact_mod_cast ha i
  rcases mul_eq_zero.mp h with h | h
  · exact h
  · omega

lemma good_value_ne_add_total {k : ℕ} {a : Fin k → ℕ}
    (ha : ∀ i, 0 < a i) (hn : NoDouble a) {u v : Word k}
    (hu : Good u) (hv : Good v) : value a u ≠ value a v + (total a : ℤ) := by
  intro h
  let d : Fin k → ℤ := fun i => (u i : ℤ) - (v i : ℤ) - 1
  have hz : ∑ i, d i * (a i : ℤ) = 0 := by
    simp only [d, sub_mul, one_mul, Finset.sum_sub_distrib]
    have ht : (total a : ℤ) = ∑ i, (a i : ℤ) := by simp [total]
    change value a u - value a v - ∑ i, (a i : ℤ) = 0
    rw [← ht]
    omega
  have hd0 : ∀ i, d i = 0 := by
    by_cases hc : ∃ i, u i = 2 ∧ v i = 0
    · obtain ⟨i, hui, hvi⟩ := hc
      apply coefficient_cancel ha hn d ?_ hz
      intro j
      have huj := (u j).isLt
      have hvj := (v j).isLt
      have hbad : ¬ ((u j).val = 0 ∧ (v j).val = 2) := by
        intro hh
        exact ordered_no_cross hu.1 hv.1 hui hvi (Fin.ext hh.1) (Fin.ext hh.2)
      change -2 ≤ (↑(u j).val : ℤ) - ↑(v j).val - 1 ∧
        (↑(u j).val : ℤ) - ↑(v j).val - 1 ≤ 1
      omega
    · apply nonpositive_weighted_sum_zero ha d ?_ hz
      intro i
      have hui := (u i).isLt
      have hvi := (v i).isLt
      have hbad : ¬ ((u i).val = 2 ∧ (v i).val = 0) := by
        intro hh
        exact hc ⟨i, Fin.ext hh.1, Fin.ext hh.2⟩
      change (↑(u i).val : ℤ) - ↑(v i).val - 1 ≤ 0
      omega
  obtain ⟨i, hvi⟩ := hv.2
  have hi := hd0 i
  have hui := (u i).isLt
  simp only [d, hvi] at hi
  change (↑(u i).val : ℤ) - 2 - 1 = 0 at hi
  omega

end Erdos882Korsky
