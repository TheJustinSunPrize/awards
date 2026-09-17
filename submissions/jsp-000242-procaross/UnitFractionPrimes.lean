/-
Released under the Apache 2.0 license. Prepared with AI assistance.
-/
import UnitFractionBounds
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Cast.Field
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Powerset

/-!
Explicit finite large-prime obstructions for distinct unit-fraction sums.
The denominator-clearing argument is classical. This is a formal finite lemma
related to the prime-removal obstruction in Croot (2001), not the asymptotic
construction or an assertion of mathematical novelty.
-/

namespace UnitFractionBounds

open scoped BigOperators

/-- An exact natural-number numerator after clearing a common denominator. -/
theorem weighted_reciprocals (S : Finset ℕ) (L : ℕ)
    (hd : ∀ a ∈ S, a ∣ L) :
    ((∑ a ∈ S, L / a : ℕ) : ℚ) = (L : ℚ) * ∑ a ∈ S, (1 : ℚ) / a := by
  rw [Nat.cast_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  rw [Nat.cast_div_charZero (hd a ha)]
  ring

theorem prime_not_dvd_product (S : Finset ℕ) {p : ℕ} (hp : p.Prime)
    (h : ∀ a ∈ S, ¬p ∣ a) : ¬p ∣ ∏ a ∈ S, a := by
  induction S using Finset.induction_on with
  | empty => simpa using hp.not_dvd_one
  | @insert a S ha ih =>
    rw [Finset.prod_insert ha]
    exact hp.not_dvd_mul (h a (by simp)) (ih (fun b hb => h b (by simp [hb])))

/-- Clearing denominators forces divisibility of the numerator of the p-part. -/
theorem prime_dvd_weighted_part (A : Finset ℕ) {p L : ℕ} (hp : p.Prime)
    (hd : ∀ a ∈ A, p ∣ a → a / p ∣ L)
    (hsum : ∑ a ∈ A, (1 : ℚ) / a = 1) :
    p ∣ ∑ a ∈ A.filter (fun a => p ∣ a), L / (a / p) := by
  let D := A.filter (fun a => p ∣ a)
  let E := A.filter (fun a => ¬p ∣ a)
  let W := ∑ a ∈ D, L / (a / p)
  let H := ∏ a ∈ E, a
  let Q := ∑ a ∈ E, H / a
  have hpQ : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hD : (W : ℚ) = (p : ℚ) * L * ∑ a ∈ D, (1 : ℚ) / a := by
    dsimp only [W]
    rw [Nat.cast_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a ha
    obtain ⟨haA, hpa⟩ := Finset.mem_filter.mp ha
    rw [Nat.cast_div_charZero (hd a haA hpa)]
    have hquot : (a : ℚ) = (p : ℚ) * (a / p : ℕ) := by
      exact_mod_cast (Nat.mul_div_cancel' hpa).symm
    rw [hquot]
    field_simp
  have hE : (Q : ℚ) = (H : ℚ) * ∑ a ∈ E, (1 : ℚ) / a :=
    weighted_reciprocals E H (fun a ha => Finset.dvd_prod_of_mem (fun b : ℕ => b) ha)
  have hpart : (∑ a ∈ D, (1 : ℚ) / a) + (∑ a ∈ E, (1 : ℚ) / a) = 1 := by
    rw [Finset.sum_filter_add_sum_filter_not]
    exact hsum
  have hnat : p * L * H = H * W + p * L * Q := by
    have hrat : (p : ℚ) * L * H = H * W + (p : ℚ) * L * Q := by
      rw [hD, hE]
      calc
        (p : ℚ) * L * H = (p : ℚ) * L * H *
            ((∑ a ∈ D, (1 : ℚ) / a) + (∑ a ∈ E, (1 : ℚ) / a)) := by rw [hpart]; ring
        _ = _ := by ring
    exact_mod_cast hrat
  have hdiv : p ∣ H * W := by
    have ht : p ∣ H * W + p * L * Q := by
      rw [← hnat]
      exact dvd_mul_of_dvd_left (dvd_mul_right p L) H
    exact (Nat.dvd_add_iff_right (dvd_mul_right p (L * Q))).mpr
      (by simpa [mul_assoc, Nat.add_comm] using ht)
  have hnot : ¬p ∣ H := prime_not_dvd_product E hp (fun a ha => (Finset.mem_filter.mp ha).2)
  exact (hp.dvd_mul.mp hdiv).resolve_left hnot

/-- Harmonic numerator for an explicit common multiple of the first T integers. -/
def harmonicWeight (T L : ℕ) : ℕ := ∑ j ∈ Finset.Icc 1 T, L / j

/-- A finite, explicit large-prime exclusion with no asymptotic assumptions. -/
theorem prime_exclusion (A : Finset ℕ) {p T L : ℕ} (hp : p.Prime)
    (hL : 0 < L) (hcommon : ∀ j ∈ Finset.Icc 1 T, j ∣ L)
    (hweight : harmonicWeight T L < p)
    (hpos : ∀ a ∈ A, 0 < a) (hmax : ∀ a ∈ A, a ≤ p * T)
    (hsum : ∑ a ∈ A, (1 : ℚ) / a = 1) :
    ∀ a ∈ A, ¬p ∣ a := by
  let D := A.filter (fun a => p ∣ a)
  let C := D.image (fun a => a / p)
  have hquot : ∀ a ∈ D, a / p ∈ Finset.Icc 1 T := by
    intro a ha
    obtain ⟨haA, hpa⟩ := Finset.mem_filter.mp ha
    have hmul : p * (a / p) = a := Nat.mul_div_cancel' hpa
    have ha0 := hpos a haA
    have hab := hmax a haA
    have hp0 := hp.pos
    apply Finset.mem_Icc.mpr
    constructor
    · exact Nat.div_pos (Nat.le_of_dvd ha0 hpa) hp.pos
    · nlinarith
  have hinj : Set.InjOn (fun a => a / p) (↑D : Set ℕ) := by
    intro a ha b hb heq
    have ha' := Nat.mul_div_cancel' (Finset.mem_filter.mp ha).2
    have hb' := Nat.mul_div_cancel' (Finset.mem_filter.mp hb).2
    change a / p = b / p at heq
    rw [heq] at ha'
    omega
  have hsubset : C ⊆ Finset.Icc 1 T := by
    intro j hj
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hj
    exact hquot a ha
  have heq : (∑ j ∈ C, L / j) = ∑ a ∈ D, L / (a / p) := by
    exact Finset.sum_image hinj
  have hd : p ∣ ∑ j ∈ C, L / j := by
    rw [heq]
    exact prime_dvd_weighted_part A hp
      (fun a ha hpa => hcommon (a / p) (hquot a (Finset.mem_filter.mpr ⟨ha, hpa⟩))) hsum
  have hbound : (∑ j ∈ C, L / j) ≤ harmonicWeight T L := Finset.sum_le_sum_of_subset hsubset
  intro a ha hpa
  have haj : a / p ∈ C := Finset.mem_image.mpr ⟨a, Finset.mem_filter.mpr ⟨ha, hpa⟩, rfl⟩
  have hjdiv := hcommon (a / p) (hsubset haj)
  have hj0 : 0 < L / (a / p) := Nat.div_pos (Nat.le_of_dvd hL hjdiv)
    ((Finset.mem_Icc.mp (hsubset haj)).1)
  have hsum0 : 0 < ∑ j ∈ C, L / j :=
    hj0.trans_le (Finset.single_le_sum (fun j _ => Nat.zero_le (L / j)) haj)
  exact (not_le_of_gt (hbound.trans_lt hweight)) (Nat.le_of_dvd hsum0 hd)

/-- No nonempty quotient subset has weighted numerator divisible by p. -/
def primePartFree (p T L : ℕ) : Bool :=
  decide (∀ C ∈ (Finset.Icc 1 T).powerset,
    C.Nonempty → ¬p ∣ ∑ j ∈ C, L / j)

/-- An exact modular certificate can exclude primes below the coarse harmonic threshold. -/
theorem prime_exclusion_by_certificate (A : Finset ℕ) {p T L : ℕ}
    (hp : p.Prime) (hcommon : ∀ j ∈ Finset.Icc 1 T, j ∣ L)
    (hcert : primePartFree p T L = true)
    (hpos : ∀ a ∈ A, 0 < a) (hmax : ∀ a ∈ A, a < p * (T + 1))
    (hsum : ∑ a ∈ A, (1 : ℚ) / a = 1) :
    ∀ a ∈ A, ¬p ∣ a := by
  let D := A.filter (fun a => p ∣ a)
  let C := D.image (fun a => a / p)
  have hquot : ∀ a ∈ D, a / p ∈ Finset.Icc 1 T := by
    intro a ha
    obtain ⟨haA, hpa⟩ := Finset.mem_filter.mp ha
    have hmul : p * (a / p) = a := Nat.mul_div_cancel' hpa
    have hab := hmax a haA
    have hp0 := hp.pos
    exact Finset.mem_Icc.mpr ⟨Nat.div_pos (Nat.le_of_dvd (hpos a haA) hpa) hp.pos,
      by nlinarith⟩
  have hinj : Set.InjOn (fun a => a / p) (↑D : Set ℕ) := by
    intro a ha b hb heq
    have ha' := Nat.mul_div_cancel' (Finset.mem_filter.mp ha).2
    have hb' := Nat.mul_div_cancel' (Finset.mem_filter.mp hb).2
    change a / p = b / p at heq
    rw [heq] at ha'
    omega
  have hsubset : C ⊆ Finset.Icc 1 T := by
    intro j hj
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hj
    exact hquot a ha
  have heq : (∑ j ∈ C, L / j) = ∑ a ∈ D, L / (a / p) := Finset.sum_image hinj
  have hd : p ∣ ∑ j ∈ C, L / j := by
    rw [heq]
    exact prime_dvd_weighted_part A hp
      (fun a ha hpa => hcommon (a / p) (hquot a (Finset.mem_filter.mpr ⟨ha, hpa⟩))) hsum
  have hc : ∀ C ∈ (Finset.Icc 1 T).powerset,
      C.Nonempty → ¬p ∣ ∑ j ∈ C, L / j := of_decide_eq_true hcert
  intro a ha hpa
  have hn : C.Nonempty :=
    ⟨a / p, Finset.mem_image.mpr ⟨a, Finset.mem_filter.mpr ⟨ha, hpa⟩, rfl⟩⟩
  exact hc C (Finset.mem_powerset.mpr hsubset) hn hd

/-- Unlike the harmonic test (weight 11), the modular test excludes 7 through 21. -/
theorem exclude_seven_up_to_twenty_one (A : Finset ℕ)
    (hpos : ∀ a ∈ A, 0 < a) (hmax : ∀ a ∈ A, a ≤ 21)
    (hsum : ∑ a ∈ A, (1 : ℚ) / a = 1) : ∀ a ∈ A, ¬7 ∣ a := by
  exact prime_exclusion_by_certificate A (p := 7) (T := 3) (L := 6)
    (by decide) (by decide) (by decide +kernel) hpos
    (fun a ha => by have := hmax a ha; omega) hsum

/-- A second certificate below the coarse harmonic weight 25. -/
theorem exclude_seventeen_up_to_sixty_eight (A : Finset ℕ)
    (hpos : ∀ a ∈ A, 0 < a) (hmax : ∀ a ∈ A, a ≤ 68)
    (hsum : ∑ a ∈ A, (1 : ℚ) / a = 1) : ∀ a ∈ A, ¬17 ∣ a := by
  exact prime_exclusion_by_certificate A (p := 17) (T := 4) (L := 12)
    (by decide) (by decide) (by decide +kernel) hpos
    (fun a ha => by have := hmax a ha; omega) hsum

/-- Bounds admitting a representation containing a denominator divisible by p. -/
def AdmitsPrimeDivisor (p N : ℕ) : Prop :=
  ∃ A : Finset ℕ, (∀ a ∈ A, 0 < a ∧ a ≤ N) ∧
    (∑ a ∈ A, (1 : ℚ) / a) = 1 ∧ ∃ a ∈ A, p ∣ a

/-- A certificate excludes every smaller bound; a witness attains the threshold. -/
theorem first_prime_threshold_of_certificate (p T L : ℕ) (hp : p.Prime)
    (hcommon : ∀ j ∈ Finset.Icc 1 T, j ∣ L)
    (hcert : primePartFree p T L = true)
    (hw : AdmitsPrimeDivisor p (p * (T + 1))) :
    IsLeast {N | AdmitsPrimeDivisor p N} (p * (T + 1)) := by
  refine ⟨hw, ?_⟩
  intro N hN
  by_contra hlt
  have hNlt : N < p * (T + 1) := by omega
  obtain ⟨A, hA, hsum, a, ha, hpa⟩ := hN
  exact prime_exclusion_by_certificate A hp hcommon hcert
    (fun b hb => (hA b hb).1)
    (fun b hb => ((hA b hb).2).trans_lt hNlt) hsum a ha hpa

/-- The least maximum denominator allowing a multiple of 7 is exactly 28. -/
theorem first_seven_threshold : IsLeast {N | AdmitsPrimeDivisor 7 N} 28 := by
  apply first_prime_threshold_of_certificate 7 3 6 (by decide) (by decide) (by decide +kernel)
  refine ⟨{2, 4, 7, 14, 28}, ?_, ?_, 7, ?_, ?_⟩ <;> norm_num

/-- The least maximum denominator allowing a multiple of 17 is exactly 85. -/
theorem first_seventeen_threshold : IsLeast {N | AdmitsPrimeDivisor 17 N} 85 := by
  apply first_prime_threshold_of_certificate 17 4 12 (by decide) (by decide) (by decide +kernel)
  refine ⟨{2, 3, 15, 17, 34, 85}, ?_, ?_, 17, ?_, ?_⟩ <;> norm_num

end UnitFractionBounds

#print axioms UnitFractionBounds.weighted_reciprocals
#print axioms UnitFractionBounds.prime_dvd_weighted_part
#print axioms UnitFractionBounds.prime_exclusion
#print axioms UnitFractionBounds.prime_exclusion_by_certificate
#print axioms UnitFractionBounds.exclude_seven_up_to_twenty_one
#print axioms UnitFractionBounds.exclude_seventeen_up_to_sixty_eight
#print axioms UnitFractionBounds.first_prime_threshold_of_certificate
#print axioms UnitFractionBounds.first_seven_threshold
#print axioms UnitFractionBounds.first_seventeen_threshold
