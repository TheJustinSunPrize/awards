import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Nat.Sqrt
import Mathlib.Data.Finset.Card
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.Linarith

/-!
# JSP-000359 / Erdos 440: an explicit counting bound

This file addresses ONLY the O(sqrt x) part of the original problem.
It does not establish the sharp liminf or the optimal pointwise constant.
The mathematical bound was previously known (Erdos--Szemeredi 1980;
see also Tao's 2025 comment on https://www.erdosproblems.com/440).
-/

set_option autoImplicit false

namespace JSP000359

/-- A bounded common multiple forces a strict drop in integer quotients. -/
theorem quotient_drop {a b x : ℕ} (ha : 0 < a) (hab : a < b)
    (hl : Nat.lcm a b ≤ x) : x / b < x / a := by
  have hb : 0 < b := by omega
  have hd : Nat.gcd a b ≤ b - a :=
    Nat.le_of_dvd (by omega) (Nat.dvd_sub (Nat.gcd_dvd_right a b) (Nat.gcd_dvd_left a b))
  have hm : Nat.lcm a b / b * b = Nat.lcm a b :=
    Nat.div_mul_cancel (Nat.dvd_lcm_right a b)
  have heq : Nat.gcd a b * (Nat.lcm a b / b) = a := by
    have hprod := Nat.gcd_mul_lcm a b
    nlinarith
  have hq : Nat.lcm a b / b ≤ x / b := Nat.div_le_div_right hl
  have h1 := Nat.mul_le_mul_left (Nat.gcd a b) hq
  have h2 := Nat.mul_le_mul_right (x / b) hd
  have h3 := Nat.div_mul_le_self x b
  have hsub : b - a + a = b := Nat.sub_add_cancel (Nat.le_of_lt hab)
  have hx : (x / b + 1) * a ≤ x := by nlinarith
  exact Nat.lt_of_lt_of_le (Nat.lt_succ_self _) ((Nat.le_div_iff_mul_le ha).2 hx)

/-- Good indices form a finite set; the explicit range will later be justified. -/
def goodIndices (a : ℕ → ℕ) (x : ℕ) : Finset ℕ :=
  (Finset.range (x + 1)).filter (fun i => Nat.lcm (a i) (a (i + 1)) ≤ x)

theorem quotient_injective_on_good (a : ℕ → ℕ) (ha : StrictMono a)
    (hpos : ∀ i, 0 < a i) (x : ℕ) :
    Set.InjOn (fun i => x / a i) (goodIndices a x : Set ℕ) := by
  intro i hi j hj heq
  change x / a i = x / a j at heq
  have drop (k : ℕ) (hk : k ∈ goodIndices a x) :=
    quotient_drop (hpos k) (ha (Nat.lt_succ_self k)) (Finset.mem_filter.mp hk).2
  rcases lt_trichotomy i j with hij | hij | hji
  · have hm : a (i + 1) ≤ a j := ha.monotone (by omega)
    have hdiv : x / a j ≤ x / a (i + 1) := Nat.div_le_div_left hm (hpos (i + 1))
    have hdrop : x / a (i + 1) < x / a i := drop i hi
    omega
  · exact hij
  · have hm : a (j + 1) ≤ a i := ha.monotone (by omega)
    have hdiv : x / a i ≤ x / a (j + 1) := Nat.div_le_div_left hm (hpos (j + 1))
    have hdrop : x / a (j + 1) < x / a j := drop j hj
    omega

theorem left_le_of_lcm_le (a : ℕ → ℕ) (hpos : ∀ i, 0 < a i)
    {i x : ℕ} (h : Nat.lcm (a i) (a (i + 1)) ≤ x) : a i ≤ x := by
  have hp : 0 < Nat.lcm (a i) (a (i + 1)) := Nat.lcm_pos (hpos i) (hpos (i + 1))
  exact (Nat.le_of_dvd hp (Nat.dvd_lcm_left _ _)).trans h

/-- The finite definition counts all good indices, not merely a truncation. -/
theorem mem_goodIndices_iff (a : ℕ → ℕ) (ha : StrictMono a)
    (hpos : ∀ i, 0 < a i) (i x : ℕ) :
    i ∈ goodIndices a x ↔ Nat.lcm (a i) (a (i + 1)) ≤ x := by
  constructor
  · intro h
    exact (Finset.mem_filter.mp h).2
  · intro h
    have hai := ha.add_le_nat i 0
    simp only [Nat.add_zero] at hai
    have hax := left_le_of_lcm_le a hpos h
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_range.mpr (by omega), h⟩

/-- Splitting at any threshold gives a fully explicit finite upper bound. -/
theorem counting_bound (a : ℕ → ℕ) (ha : StrictMono a)
    (hpos : ∀ i, 0 < a i) (x t : ℕ) :
    (goodIndices a x).card ≤ t + x / (t + 1) := by
  let s := goodIndices a x
  have hsmall : (s.filter (fun i => a i ≤ t)).card ≤ t := by
    calc
      _ ≤ (Finset.Icc 1 t).card := by
        apply Finset.card_le_card_of_injOn a
        · intro i hi
          exact Finset.mem_Icc.mpr ⟨hpos i, (Finset.mem_filter.mp hi).2⟩
        · intro i _ j _ hij
          exact ha.injective hij
      _ = t := by simp
  have hlarge : (s.filter (fun i => ¬ a i ≤ t)).card ≤ x / (t + 1) := by
    calc
      _ ≤ (Finset.Icc 1 (x / (t + 1))).card := by
        apply Finset.card_le_card_of_injOn (fun i => x / a i)
        · intro i hi
          obtain ⟨hgood, hbig⟩ := Finset.mem_filter.mp hi
          have hax := left_le_of_lcm_le a hpos (Finset.mem_filter.mp hgood).2
          apply Finset.mem_Icc.mpr
          constructor
          · exact Nat.div_pos hax (hpos i)
          · exact Nat.div_le_div_left (by omega) (by omega)
        · intro i hi j hj hij
          exact quotient_injective_on_good a ha hpos x
            (Finset.mem_filter.mp hi).1 (Finset.mem_filter.mp hj).1 hij
      _ = x / (t + 1) := by simp
  have hsplit := Finset.filter_card_add_filter_neg_card_eq_card
    (s := s) (fun i => a i ≤ t)
  change s.card ≤ _
  omega

/-- An explicit version of the O(sqrt x) assertion, valid at every natural x. -/
theorem counting_bound_sqrt (a : ℕ → ℕ) (ha : StrictMono a)
    (hpos : ∀ i, 0 < a i) (x : ℕ) :
    (goodIndices a x).card ≤ 2 * Nat.sqrt x := by
  have h := counting_bound a ha hpos x (Nat.sqrt x)
  have hdiv : x / (Nat.sqrt x + 1) < Nat.sqrt x + 1 :=
    (Nat.div_lt_iff_lt_mul (by omega)).2 (Nat.lt_succ_sqrt x)
  omega

#print axioms mem_goodIndices_iff
#print axioms counting_bound
#print axioms counting_bound_sqrt

end JSP000359
