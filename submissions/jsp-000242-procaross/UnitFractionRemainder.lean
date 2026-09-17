/- Released under the Apache 2.0 license. Prepared with AI assistance. -/
import UnitFractionOptimum
import Mathlib.Data.List.Shortlex
import Mathlib.Data.Nat.Factorial.Basic

namespace UnitFractionBounds

open scoped BigOperators

@[simp] theorem recips_append (l t : List ℕ) : recips (l ++ t) = recips l + recips t := by
  simp [recips]

theorem duplicate_split (l : List ℕ) (h : ¬l.Nodup) :
    ∃ p q t : List ℕ, ∃ a : ℕ, l = p ++ a :: q ++ a :: t := by
  induction l with
  | nil => simp at h
  | cons a l ih =>
    by_cases ha : a ∈ l
    · obtain ⟨q, t, rfl⟩ := List.mem_iff_append.mp ha
      exact ⟨[], q, t, a, rfl⟩
    · have hl : ¬l.Nodup := fun hn => h (List.nodup_cons.mpr ⟨ha, hn⟩)
      obtain ⟨p, q, t, b, hsplit⟩ := ih hl
      exact ⟨a :: p, q, t, b, by simp [hsplit]⟩

/-- Takenouchi-style duplicate removal by well-founded shortlex descent.
The lower bound on the new denominators is derived later from their total sum. -/
theorem remove_repetitions (l : List ℕ) (hp : ∀ a ∈ l, 0 < a)
    (hr : recips l ≤ 1) :
    ∃ t : List ℕ, t.Nodup ∧ (∀ a ∈ t, 0 < a) ∧ recips t = recips l ∧
      t.length ≤ l.length := by
  induction l using (List.Shortlex.wf Nat.lt_wfRel.wf).induction with
  | h l ih =>
    by_cases hn : l.Nodup
    · exact ⟨l, hn, hp, rfl, le_rfl⟩
    obtain ⟨p, q, t, a, rfl⟩ := duplicate_split l hn
    have ha : 0 < a := hp a (by simp)
    have ha2 : 2 ≤ a := by
      by_contra hh
      have he : a = 1 := by omega
      have hpn := recips_nonneg p
      have hqn := recips_nonneg q
      have htn := recips_nonneg t
      simp only [recips_append, recips_cons, he, Nat.cast_one, div_one] at hr
      linarith
    have hpp : ∀ d ∈ p, 0 < d := fun d hd => hp d (by simp [hd])
    have hqp : ∀ d ∈ q, 0 < d := fun d hd => hp d (by simp [hd])
    have htp : ∀ d ∈ t, 0 < d := fun d hd => hp d (by simp [hd])
    by_cases heven : a % 2 = 0
    · let b := a / 2
      have hb : 0 < b := by dsimp [b]; omega
      have heq : 2 * b = a := by dsimp [b]; omega
      have hunit : (1 : ℚ) / b = 1 / a + 1 / a := by
        have haQ : (a : ℚ) = 2 * b := by exact_mod_cast heq.symm
        rw [haQ]
        field_simp
        ring
      let u := p ++ b :: q ++ t
      have hup : ∀ d ∈ u, 0 < d := by
        intro d hd
        simp only [u, List.mem_append, List.mem_cons] at hd
        rcases hd with (hd | rfl | hd) | hd
        · exact hpp d hd
        · exact hb
        · exact hqp d hd
        · exact htp d hd
      have hsum : recips u = recips (p ++ a :: q ++ a :: t) := by
        simp only [u, recips_append, recips_cons]
        linarith
      have hlen : u.length < (p ++ a :: q ++ a :: t).length := by simp [u]
      obtain ⟨v, hv, hvp, hvs, hvl⟩ := ih u (List.Shortlex.of_length_lt hlen) hup (hsum ▸ hr)
      exact ⟨v, hv, hvp, hvs.trans hsum, hvl.trans hlen.le⟩
    · let b := a / 2 + 1
      have hb : 0 < b := by dsimp [b]; omega
      have hba : b < a := by dsimp [b]; omega
      have heq : 2 * b = a + 1 := by dsimp [b]; omega
      have hunit : (1 : ℚ) / b + 1 / (a * b : ℕ) = 1 / a + 1 / a := by
        have haQ : (a : ℚ) + 1 = 2 * b := by exact_mod_cast heq.symm
        have han : (a : ℚ) ≠ 0 := by exact_mod_cast ha.ne'
        have hbn : (b : ℚ) ≠ 0 := by exact_mod_cast hb.ne'
        push_cast
        field_simp
        nlinarith
      let u := p ++ b :: q ++ (a * b) :: t
      have hup : ∀ d ∈ u, 0 < d := by
        intro d hd
        simp only [u, List.mem_append, List.mem_cons] at hd
        rcases hd with (hd | rfl | hd) | rfl | hd
        · exact hpp d hd
        · exact hb
        · exact hqp d hd
        · exact Nat.mul_pos ha hb
        · exact htp d hd
      have hsum : recips u = recips (p ++ a :: q ++ a :: t) := by
        simp only [u, recips_append, recips_cons]
        linarith
      have hlen : u.length = (p ++ a :: q ++ a :: t).length := by simp [u]
      have hlex : List.Lex (· < ·) u (p ++ a :: q ++ a :: t) := by
        simp only [u, List.append_assoc, List.cons_append]
        exact List.Lex.append_left _ (List.Lex.rel hba) p
      obtain ⟨v, hv, hvp, hvs, hvl⟩ := ih u (List.Shortlex.of_lex hlen hlex) hup (hsum ▸ hr)
      exact ⟨v, hv, hvp, hvs.trans hsum, hlen ▸ hvl⟩

theorem factorial_expansion (n a : ℕ) (ha : a < n.factorial) :
    ∃ l : List ℕ, (∀ d ∈ l, 0 < d) ∧ recips l = (a : ℚ) / n.factorial ∧
      l.length ≤ n := by
  induction n generalizing a with
  | zero =>
    have heq : a = 0 := by simpa using ha
    subst a
    exact ⟨[], by simp, by simp, by simp⟩
  | succ n ih =>
    have hq : a / (n + 1) < n.factorial := by
      apply (Nat.div_lt_iff_lt_mul (Nat.succ_pos n)).mpr
      simpa [Nat.factorial_succ, Nat.mul_comm] using ha
    obtain ⟨l, hp, hs, hl⟩ := ih _ hq
    have hnQ : (n.factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
    have hkQ : ((n + 1 : ℕ) : ℚ) ≠ 0 := by exact_mod_cast (Nat.succ_ne_zero n)
    have hdiv := Nat.div_add_mod a (n + 1)
    have hrem := Nat.mod_lt a (Nat.succ_pos n)
    by_cases hz : a % (n + 1) = 0
    · refine ⟨l, hp, ?_, hl.trans (Nat.le_succ n)⟩
      rw [hs, Nat.factorial_succ, Nat.cast_mul]
      have heq : (a : ℚ) = (n + 1 : ℕ) * (a / (n + 1) : ℕ) := by
        exact_mod_cast (by omega : a = (n + 1) * (a / (n + 1)))
      rw [heq]
      field_simp
    · let r := a % (n + 1)
      have hr : 0 < r := by dsimp [r]; omega
      have hrdiv : r ∣ (n + 1).factorial := Nat.dvd_factorial hr hrem.le
      let d := (n + 1).factorial / r
      have hdr : d * r = (n + 1).factorial := Nat.div_mul_cancel hrdiv
      have hd : 0 < d := by have := Nat.factorial_pos (n + 1); nlinarith
      have hdQ : (d : ℚ) ≠ 0 := by exact_mod_cast hd.ne'
      have hsum : (1 : ℚ) / d + (a / (n + 1) : ℕ) / n.factorial = a / (n + 1).factorial := by
        have hdrQ : (d : ℚ) * r = (n + 1 : ℕ) * n.factorial := by
          exact_mod_cast (hdr.trans (Nat.factorial_succ n))
        have hdivQ : ((n + 1 : ℕ) : ℚ) * (a / (n + 1) : ℕ) + r = a := by exact_mod_cast hdiv
        rw [Nat.factorial_succ, Nat.cast_mul]
        field_simp
        nlinarith
      refine ⟨d :: l, ?_, ?_, by simp; omega⟩
      · intro e he
        rcases List.mem_cons.mp he with rfl | he
        · exact hd
        · exact hp e he
      · rw [recips_cons, hs]; exact hsum

theorem recips_map_mul (b : ℕ) (l : List ℕ) :
    recips (l.map (b * ·)) = recips l / b := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, recips_cons, ih, Nat.cast_mul]
    ring

/-- Classical factorial remainder bound (Erdős, 1950).
It applies to an unreduced denominator and eliminates all duplicate terms. -/
theorem egyptian_length_factorial (a b n : ℕ) (hab : a < b) (hbn : b ≤ n.factorial) :
    ∃ A : Finset ℕ, (∀ d ∈ A, 0 < d) ∧
      (∑ d ∈ A, (1 : ℚ) / d) = (a : ℚ) / b ∧ A.card ≤ 2 * n := by
  have hb : 0 < b := by omega
  let f := n.factorial
  let s := a * f / b
  let r := a * f % b
  have hs : s < f := by
    apply (Nat.div_lt_iff_lt_mul hb).mpr
    simpa [f, Nat.mul_comm] using Nat.mul_lt_mul_of_pos_right hab (Nat.factorial_pos n)
  have hr : r < f := (Nat.mod_lt _ hb).trans_le hbn
  obtain ⟨l₁, hp₁, hsum₁, hlen₁⟩ := factorial_expansion n s hs
  obtain ⟨l₂, hp₂, hsum₂, hlen₂⟩ := factorial_expansion n r hr
  let l := l₁ ++ l₂.map (b * ·)
  have hp : ∀ d ∈ l, 0 < d := by
    intro d hd
    rcases List.mem_append.mp hd with hd | hd
    · exact hp₁ d hd
    · obtain ⟨e, he, rfl⟩ := List.mem_map.mp hd
      exact Nat.mul_pos hb (hp₂ e he)
  have hsum : recips l = (a : ℚ) / b := by
    dsimp [l]
    rw [recips_append, recips_map_mul, hsum₁, hsum₂]
    have hfQ : (n.factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
    have hbQ : (b : ℚ) ≠ 0 := by exact_mod_cast hb.ne'
    have hdivQ : (b : ℚ) * s + r = a * n.factorial := by
      exact_mod_cast (Nat.div_add_mod (a * f) b)
    field_simp
    nlinarith
  have hle : recips l ≤ 1 := by
    rw [hsum]
    exact (div_lt_one (by exact_mod_cast hb)).mpr (by exact_mod_cast hab) |>.le
  obtain ⟨t, ht, htp, hts, htl⟩ := remove_repetitions l hp hle
  refine ⟨t.toFinset, fun d hd => htp d (List.mem_toFinset.mp hd), ?_, ?_⟩
  · rw [List.sum_toFinset _ ht]
    exact hts.trans hsum
  · rw [List.toFinset_card_of_nodup ht]
    have hlen : l.length ≤ 2 * n := by simp only [l, List.length_append, List.length_map]; omega
    exact htl.trans hlen

end UnitFractionBounds

#print axioms UnitFractionBounds.remove_repetitions
#print axioms UnitFractionBounds.factorial_expansion
#print axioms UnitFractionBounds.egyptian_length_factorial
