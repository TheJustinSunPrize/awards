import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

/-!
The classical middle-third lower bound associated with Erdős 792 / JSP-000651.
This is a formalization of a known bound, not the stronger open extremal problem.
The possible zero element and the exceptional singleton {0} are treated explicitly.
-/

open Finset
open scoped BigOperators

namespace SumFreeBound

def SumFree {R : Type*} [Add R] (s : Finset R) : Prop :=
  ∀ a ∈ s, ∀ b ∈ s, a + b ∉ s

def middle (p k : ℕ) : Finset (ZMod p) :=
  (Finset.Icc (k + 1) (2 * k + 1)).image (fun n : ℕ => (n : ZMod p))

theorem middle_card {p k : ℕ} (hp : p = 3 * k + 2) : (middle p k).card = k + 1 := by
  unfold middle
  rw [Finset.card_image_of_injOn]
  · rw [Nat.card_Icc]
    omega
  · intro a ha b hb h
    have ha' := (Finset.mem_Icc.mp ha).2
    have hb' := (Finset.mem_Icc.mp hb).2
    have hval := congrArg ZMod.val h
    simpa only [ZMod.val_natCast_of_lt (by omega : a < p),
      ZMod.val_natCast_of_lt (by omega : b < p)] using hval

theorem middle_sumFree {p k : ℕ} (hp : p = 3 * k + 2) : SumFree (middle p k) := by
  intro a ha b hb hab
  simp only [middle, Finset.mem_image] at ha hb hab
  obtain ⟨i, hi, rfl⟩ := ha
  obtain ⟨j, hj, rfl⟩ := hb
  obtain ⟨l, hl, heq⟩ := hab
  simp only [Finset.mem_Icc] at hi hj hl
  have hz : ((i + j - l : ℕ) : ZMod p) = 0 := by
    rw [Nat.cast_sub (by omega : l ≤ i + j), Nat.cast_add, ← heq, sub_self]
  have hd : p ∣ i + j - l := (ZMod.natCast_eq_zero_iff _ _).mp hz
  have he := Nat.eq_zero_of_dvd_of_lt hd (by omega : i + j - l < p)
  omega

theorem column_card {p : ℕ} [Fact p.Prime] (t : Finset (ZMod p))
    (a : ZMod p) (ha : a ≠ 0) :
    (Finset.univ.filter (fun x : ZMod p => x * a ∈ t)).card = t.card := by
  apply Finset.card_bij (fun x _ => x * a)
  · intro x hx
    exact (Finset.mem_filter.mp hx).2
  · intro x hx y hy h
    exact mul_right_cancel₀ ha h
  · intro y hy
    refine ⟨y / a, ?_, div_mul_cancel₀ y ha⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    simpa only [div_mul_cancel₀ y ha] using hy

theorem middle_third_nonzero (a : Finset ℤ) (ha : a.Nonempty) (hzero : 0 ∉ a) :
    ∃ b ⊆ a, SumFree b ∧ a.card < 3 * b.card := by
  classical
  obtain ⟨p, hpgt, hp, hpm⟩ := Nat.forall_exists_prime_gt_and_modEq
    (a.sup Int.natAbs) (q := 3) (a := 2) (by decide) (by decide)
  let : Fact p.Prime := ⟨hp⟩
  let : NeZero p := ⟨hp.ne_zero⟩
  have hmod : p % 3 = 2 := by simpa [Nat.ModEq] using hpm
  let k := p / 3
  have hpk : p = 3 * k + 2 := by dsimp [k]; omega
  let t := middle p k
  have htcard : t.card = k + 1 := middle_card hpk
  have htsf : SumFree t := middle_sumFree hpk
  have hcast (x : ℤ) (hx : x ∈ a) : (x : ZMod p) ≠ 0 := by
    intro h
    have hdiv := (ZMod.intCast_zmod_eq_zero_iff_dvd x p).mp h
    have hxne : x ≠ 0 := by intro e; subst x; exact hzero hx
    have habs := Int.natAbs_le_of_dvd_ne_zero hdiv hxne
    have hsup : x.natAbs ≤ a.sup Int.natAbs := Finset.le_sup hx
    simp only [Int.natAbs_natCast] at habs
    omega
  let row := fun q : ZMod p => a.filter (fun x : ℤ => q * (x : ZMod p) ∈ t)
  have hsum : (∑ q : ZMod p, (row q).card) = a.card * t.card := by
    calc
      _ = ∑ x ∈ a, (Finset.univ.filter (fun q : ZMod p => q * (x : ZMod p) ∈ t)).card := by
        simpa only [row, Finset.bipartiteAbove, Finset.bipartiteBelow] using
          (Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
            (s := Finset.univ) (t := a)
            (fun q : ZMod p => fun x : ℤ => q * (x : ZMod p) ∈ t))
      _ = ∑ x ∈ a, t.card := by
        apply Finset.sum_congr rfl
        intro x hx
        exact column_card t (x : ZMod p) (hcast x hx)
      _ = _ := by simp
  have hex : ∃ q : ZMod p, a.card < 3 * (row q).card := by
    by_contra! h
    have hbound : 3 * (∑ q : ZMod p, (row q).card) ≤ p * a.card := by
      calc
        _ = ∑ q : ZMod p, 3 * (row q).card := Finset.mul_sum _ _ _
        _ ≤ ∑ _q : ZMod p, a.card := Finset.sum_le_sum (fun q _ => h q)
        _ = _ := by simp [ZMod.card]
    rw [hsum, htcard] at hbound
    have hpos := Finset.card_pos.mpr ha
    nlinarith
  obtain ⟨q, hq⟩ := hex
  refine ⟨row q, Finset.filter_subset _ _, ?_, hq⟩
  intro x hx y hy hxy
  have hx' := (Finset.mem_filter.mp hx).2
  have hy' := (Finset.mem_filter.mp hy).2
  have hxy' := (Finset.mem_filter.mp hxy).2
  exact htsf _ hx' _ hy' (by simpa only [Int.cast_add, mul_add] using hxy')

/-- The literal integer-set formulation, for every size at least two. -/
theorem erdos_lower_bound (a : Finset ℤ) (ha : 2 ≤ a.card) :
    ∃ b ⊆ a, SumFree b ∧ a.card ≤ 3 * b.card := by
  classical
  have hne : (a.erase 0).Nonempty := by
    apply Finset.card_pos.mp
    by_cases h : 0 ∈ a
    · have he := Finset.card_erase_add_one h
      omega
    · simpa only [Finset.erase_eq_of_notMem h] using (by omega : 0 < a.card)
  obtain ⟨b, hb, hsf, hcard⟩ := middle_third_nonzero (a.erase 0) hne (by simp)
  refine ⟨b, hb.trans (Finset.erase_subset _ _), hsf, ?_⟩
  by_cases h : 0 ∈ a
  · have he := Finset.card_erase_add_one h
    omega
  · simpa only [Finset.erase_eq_of_notMem h] using hcard.le

theorem singleton_zero_exception :
    ¬ ∃ b ⊆ ({0} : Finset ℤ), SumFree b ∧ 1 ≤ 3 * b.card := by
  rintro ⟨b, hb, hsf, hcard⟩
  have hne : b.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨x, hx⟩ := hne
  have hx0 : x = 0 := by simpa using hb hx
  subst x
  exact hsf 0 hx 0 hx (by simpa using hx)

end SumFreeBound
