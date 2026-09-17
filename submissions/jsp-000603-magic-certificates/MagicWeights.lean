import Mathlib.Algebra.BigOperators.Fin
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Data.Rat.BigOperators
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
Degree-based certificates for finite magic configurations (JSP-000603 / Erdős 735).
The mathematical weight formula is from Ackerman, Buchin, Knauer, Pinchasi and Rote,
There are not too many magic configurations, final section on weakly magic configurations.
This file does not prove their geometric classification theorem.
-/
open Finset
namespace MagicWeights
variable {ι K : Type*} [Fintype ι] [DecidableEq ι]
  [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- Every block has at least two points, and two distinct points determine exactly one block. -/
def LinearSpace (L : Finset (Finset ι)) : Prop :=
  (∀ l ∈ L, 2 ≤ l.card) ∧
  ∀ a b : ι, a ≠ b → ∃! l, l ∈ L ∧ a ∈ l ∧ b ∈ l

def pencil (L : Finset (Finset ι)) (a : ι) : Finset (Finset ι) := L.filter (a ∈ ·)
def degree (L : Finset (Finset ι)) (a : ι) : ℕ := (pencil L a).card

def WeakMagic (L : Finset (Finset ι)) (w : ι → K) : Prop :=
  ∀ l ∈ L, ∑ a ∈ l, w a = 1

def Magic (L : Finset (Finset ι)) (w : ι → K) : Prop :=
  (∀ a, 0 < w a) ∧ WeakMagic L w

omit [Fintype ι] in
/-- Off-diagonal incidence counts equal one. -/
theorem pair_pencil (L : Finset (Finset ι)) (hL : LinearSpace L)
    {a b : ι} (hab : a ≠ b) : ∃ l, (pencil L a).filter (b ∈ ·) = {l} := by
  obtain ⟨l, hl, hu⟩ := hL.2 a b hab
  refine ⟨l, ?_⟩
  ext m
  simp only [pencil, mem_filter, mem_singleton]
  constructor
  · rintro ⟨⟨hm, ha⟩, hb⟩
    exact hu m ⟨hm, ha, hb⟩
  · rintro rfl
    exact ⟨⟨hl.1, hl.2.1⟩, hl.2.2⟩

omit [LinearOrder K] [IsStrictOrderedRing K] in
/-- Double counting line sums through a point, without positivity of weights. -/
theorem incidence_sum (L : Finset (Finset ι)) (hL : LinearSpace L)
    (w : ι → K) (a : ι) :
    ∑ l ∈ pencil L a, ∑ b ∈ l, w b =
      (∑ b, w b) + ((degree L a : K) - 1) * w a := by
  have inner (b : ι) :
      (∑ l ∈ pencil L a, if b ∈ l then w b else 0) =
        w b + if b = a then ((degree L a : K) - 1) * w a else 0 := by
    by_cases hba : b = a
    · subst b
      have hh : (∑ l ∈ pencil L a, if a ∈ l then w a else 0) =
          ∑ _l ∈ pencil L a, w a := by
        apply sum_congr rfl
        intro l hl
        simp only [pencil, mem_filter] at hl
        simp only [hl.2, ite_true]
      rw [hh]
      simp only [sum_const, nsmul_eq_mul, degree, ite_true]
      ring
    · obtain ⟨l, hl⟩ := pair_pencil L hL (Ne.symm hba)
      rw [← sum_filter, hl]
      simp [hba]
  calc
    _ = ∑ l ∈ pencil L a, ∑ b : ι, if b ∈ l then w b else 0 := by
      apply sum_congr rfl
      intro l _
      simp
    _ = ∑ b : ι, ∑ l ∈ pencil L a, if b ∈ l then w b else 0 := by rw [sum_comm]
    _ = ∑ b : ι, (w b + if b = a then ((degree L a : K) - 1) * w a else 0) :=
      sum_congr rfl (fun b _ => inner b)
    _ = _ := by simp [sum_add_distrib]

omit [LinearOrder K] [IsStrictOrderedRing K] in
/-- The incidence equation satisfied by every normalized weak magic weighting. -/
theorem weight_equation (L : Finset (Finset ι)) (hL : LinearSpace L)
    (w : ι → K) (hw : WeakMagic L w) (a : ι) :
    (∑ b, w b) + ((degree L a : K) - 1) * w a = degree L a := by
  rw [← incidence_sum L hL w a]
  calc
    _ = ∑ _l ∈ pencil L a, (1 : K) := by
      apply sum_congr rfl
      intro l hl
      exact hw l (mem_filter.mp hl).1
    _ = _ := by simp [degree]

/-- Reciprocal excess-degree sum. -/
def reciprocalSum (L : Finset (Finset ι)) : K :=
  ∑ a, 1 / ((degree L a : K) - 1)
def totalFormula (L : Finset (Finset ι)) : K :=
  ((Fintype.card ι : K) + reciprocalSum L) / (1 + reciprocalSum L)
def weightFormula (L : Finset (Finset ι)) (a : ι) : K :=
  ((degree L a : K) - totalFormula L) / ((degree L a : K) - 1)

omit [Fintype ι] in
theorem degree_sub_pos (L : Finset (Finset ι)) (hd : ∀ a, 1 < degree L a) (a : ι) :
    (0 : K) < (degree L a : K) - 1 := by
  have h : (1 : K) < degree L a := by exact_mod_cast hd a
  linarith

theorem reciprocalSum_nonneg (L : Finset (Finset ι)) (hd : ∀ a, 1 < degree L a) :
    (0 : K) ≤ reciprocalSum L :=
  sum_nonneg fun a _ => le_of_lt (one_div_pos.mpr (degree_sub_pos L hd a))

/-- The total weight is forced entirely by incidence degrees. -/
theorem total_weight (L : Finset (Finset ι)) (hL : LinearSpace L)
    (hd : ∀ a, 1 < degree L a) (w : ι → K) (hw : WeakMagic L w) :
    ∑ a, w a = totalFormula L := by
  let Y : K := ∑ a, w a
  have eqn (a : ι) : w a = 1 + (1 - Y) * (1 / ((degree L a : K) - 1)) := by
    have he := weight_equation L hL w hw a
    have hn := ne_of_gt (degree_sub_pos (K := K) L hd a)
    apply (mul_right_cancel₀ hn)
    dsimp [Y]
    field_simp
    nlinarith only [he]
  have hs : Y = (Fintype.card ι : K) + (1 - Y) * reciprocalSum L := by
    dsimp [Y] at eqn ⊢
    conv_lhs => arg 2; ext a; rw [eqn a]
    simp [sum_add_distrib, mul_sum, reciprocalSum]
  have hn : (1 + reciprocalSum L : K) ≠ 0 := by
    have := reciprocalSum_nonneg (K := K) L hd
    linarith
  apply (eq_div_iff hn).mpr
  dsimp [Y] at hs ⊢
  nlinarith only [hs]

/-- The formula determines every weak magic weighting, including signed weights. -/
theorem weight_eq_formula (L : Finset (Finset ι)) (hL : LinearSpace L)
    (hd : ∀ a, 1 < degree L a) (w : ι → K) (hw : WeakMagic L w) :
    w = weightFormula L := by
  funext a
  apply (eq_div_iff (ne_of_gt (degree_sub_pos (K := K) L hd a))).mpr
  have he := weight_equation L hL w hw a
  rw [total_weight L hL hd w hw] at he
  linarith

/-- Uniqueness holds without requiring positive weights. -/
theorem weakMagic_unique (L : Finset (Finset ι)) (hL : LinearSpace L)
    (hd : ∀ a, 1 < degree L a) (w v : ι → K)
    (hw : WeakMagic L w) (hv : WeakMagic L v) : w = v :=
  (weight_eq_formula L hL hd w hw).trans (weight_eq_formula L hL hd v hv).symm

/-- A finite certificate requiring no search over unknown weights. -/
theorem magic_iff_formula (L : Finset (Finset ι)) (hL : LinearSpace L)
    (hd : ∀ a, 1 < degree L a) :
    (∃ w : ι → K, Magic L w) ↔ Magic L (weightFormula L : ι → K) := by
  constructor
  · rintro ⟨w, hw⟩
    rwa [weight_eq_formula L hL hd w hw.2] at hw
  · exact fun h => ⟨_, h⟩

/-- A purely incidence-numeric criterion, with no unknown point weights. -/
def DegreeCertificate (L : Finset (Finset ι)) : Prop :=
  (∀ a, (Fintype.card ι : K) - 1 <
    (1 + reciprocalSum L) * ((degree L a : K) - 1)) ∧
  ∀ l ∈ L, ((l.card : K) - 1) * (1 + reciprocalSum L) =
    ((Fintype.card ι : K) - 1) * ∑ a ∈ l, 1 / ((degree L a : K) - 1)

theorem weightFormula_alternative (L : Finset (Finset ι))
    (hd : ∀ a, 1 < degree L a) (a : ι) :
    (weightFormula L a : K) = 1 -
      ((Fintype.card ι : K) - 1) / (1 + reciprocalSum L) *
        (1 / ((degree L a : K) - 1)) := by
  have hd0 := ne_of_gt (degree_sub_pos (K := K) L hd a)
  have hr : (1 + reciprocalSum L : K) ≠ 0 := by
    have := reciprocalSum_nonneg (K := K) L hd
    linarith
  unfold weightFormula totalFormula
  field_simp
  ring

theorem formula_pos_iff (L : Finset (Finset ι))
    (hd : ∀ a, 1 < degree L a) (a : ι) :
    (0 : K) < weightFormula L a ↔
      (Fintype.card ι : K) - 1 <
        (1 + reciprocalSum L) * ((degree L a : K) - 1) := by
  have hd0 := degree_sub_pos (K := K) L hd a
  have hr : (0 : K) < 1 + reciprocalSum L := by
    have := reciprocalSum_nonneg (K := K) L hd
    linarith
  rw [weightFormula_alternative L hd a]
  rw [show ((Fintype.card ι : K) - 1) / (1 + reciprocalSum L) *
      (1 / ((degree L a : K) - 1)) =
      ((Fintype.card ι : K) - 1) /
        ((1 + reciprocalSum L) * ((degree L a : K) - 1)) by rw [div_mul_div_comm, mul_one]]
  rw [sub_pos, div_lt_one (mul_pos hr hd0)]

theorem formula_line_iff (L : Finset (Finset ι))
    (hd : ∀ a, 1 < degree L a) (l : Finset ι) :
    (∑ a ∈ l, (weightFormula L a : K)) = 1 ↔
      ((l.card : K) - 1) * (1 + reciprocalSum L) =
        ((Fintype.card ι : K) - 1) * ∑ a ∈ l, 1 / ((degree L a : K) - 1) := by
  have hr : (1 + reciprocalSum L : K) ≠ 0 := by
    have := reciprocalSum_nonneg (K := K) L hd
    linarith
  have hs : (∑ a ∈ l, (weightFormula L a : K)) =
      (l.card : K) - ((Fintype.card ι : K) - 1) / (1 + reciprocalSum L) *
        ∑ a ∈ l, 1 / ((degree L a : K) - 1) := by
    simp_rw [weightFormula_alternative L hd]
    simp [sum_sub_distrib, mul_sum]
  rw [hs]
  constructor <;> intro h
  · field_simp at h
    nlinarith only [h]
  · apply (mul_right_cancel₀ hr)
    field_simp
    nlinarith only [h]

/-- Necessary and sufficient numerical certificate for arbitrary finite linear spaces. -/
theorem magic_iff_degreeCertificate (L : Finset (Finset ι)) (hL : LinearSpace L)
    (hd : ∀ a, 1 < degree L a) :
    (∃ w : ι → K, Magic L w) ↔ DegreeCertificate (K := K) L := by
  rw [magic_iff_formula L hL hd]
  simp only [Magic, WeakMagic, DegreeCertificate, formula_pos_iff L hd,
    formula_line_iff L hd]

/-- Noncollinearity implies every point lies on at least two determined lines. -/
theorem degree_gt_one [Nontrivial ι] (L : Finset (Finset ι)) (hL : LinearSpace L)
    (hn : univ ∉ L) (a : ι) : 1 < degree L a := by
  obtain ⟨b, hab⟩ := exists_ne a
  obtain ⟨l, hl, hu⟩ := hL.2 a b hab.symm
  have hlp : l ∈ pencil L a := mem_filter.mpr ⟨hl.1, hl.2.1⟩
  have hln : l ≠ univ := by rintro rfl; exact hn hl.1
  have hmissing : ∃ c, c ∉ l := by
    by_contra! h
    exact hln (eq_univ_of_forall h)
  obtain ⟨c, hc⟩ := hmissing
  have hac : a ≠ c := by rintro rfl; exact hc hl.2.1
  obtain ⟨m, hm, _⟩ := hL.2 a c hac
  have hmp : m ∈ pencil L a := mem_filter.mpr ⟨hm.1, hm.2.1⟩
  have hml : l ≠ m := by rintro rfl; exact hc hm.2.2
  have hcard := card_le_card (show {l, m} ⊆ pencil L a by
    intro x hx
    simp only [mem_insert, mem_singleton] at hx
    rcases hx with rfl | rfl <;> assumption)
  have hp : ({l, m} : Finset (Finset ι)).card = 2 := by simp [hml]
  rw [hp] at hcard
  exact hcard

omit [DecidableEq ι] in
/-- In the collinear case the only determined line is the whole point set. -/
theorem full_line_unique (L : Finset (Finset ι)) (hL : LinearSpace L)
    (hu : univ ∈ L) : L = {univ} := by
  apply eq_singleton_iff_unique_mem.mpr
  refine ⟨hu, ?_⟩
  intro l hl
  have htwo := hL.1 l hl
  obtain ⟨a, ha, b, hb, hab⟩ := one_lt_card.mp (by omega : 1 < l.card)
  obtain ⟨m, _, hm⟩ := hL.2 a b hab
  exact (hm l ⟨hl, ha, hb⟩).trans (hm univ ⟨hu, mem_univ _, mem_univ _⟩).symm

omit [DecidableEq ι] in
/-- Empty and singleton point sets determine no lines. -/
theorem lines_empty_of_small (L : Finset (Finset ι)) (hL : LinearSpace L)
    (hsmall : Fintype.card ι ≤ 1) : L = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro l hl
  have htwo := hL.1 l hl
  have hle := card_le_card (subset_univ l)
  simp only [card_univ] at hle
  omega

omit [DecidableEq ι] in
/-- All collinear configurations have positive normalized weights. -/
theorem magic_of_full_line (L : Finset (Finset ι)) (hL : LinearSpace L)
    (hu : univ ∈ L) : ∃ w : ι → K, Magic L w := by
  have htwo := hL.1 univ hu
  have hn : (0 : K) < Fintype.card ι := by
    have : 0 < Fintype.card ι := by simpa using lt_of_lt_of_le (by decide : 0 < 2) htwo
    exact_mod_cast this
  refine ⟨fun _ => 1 / Fintype.card ι, (fun _ => one_div_pos.mpr hn), ?_⟩
  rw [full_line_unique L hL hu]
  intro l hl
  have hl' : l = univ := mem_singleton.mp hl
  subst l
  simp [ne_of_gt hn]

/-- Exact finite criterion including empty, singleton and collinear configurations. -/
theorem magic_iff_all_cases (L : Finset (Finset ι)) (hL : LinearSpace L) :
    (∃ w : ι → K, Magic L w) ↔
      Fintype.card ι ≤ 1 ∨ univ ∈ L ∨
        ((∀ a, 1 < degree L a) ∧ DegreeCertificate (K := K) L) := by
  constructor
  · intro hw
    by_cases hs : Fintype.card ι ≤ 1
    · exact Or.inl hs
    right
    by_cases hu : univ ∈ L
    · exact Or.inl hu
    right
    have : Nontrivial ι := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
    have hd := degree_gt_one L hL hu
    exact ⟨hd, (magic_iff_degreeCertificate L hL hd).mp hw⟩
  · rintro (hs | hu | ⟨hd, hc⟩)
    · refine ⟨fun _ => 1, (fun _ => zero_lt_one), ?_⟩
      rw [lines_empty_of_small L hL hs]
      intro l hl
      exact False.elim (notMem_empty l hl)
    · exact magic_of_full_line L hL hu
    · exact (magic_iff_degreeCertificate L hL hd).mpr hc

section Geometry
variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- All indexed points on the genuine affine line through two indexed points. -/
noncomputable def lineBlock (p : ι → V) (a b : ι) : Finset ι := by
  classical
  exact univ.filter fun c => p c ∈ affineSpan ℝ ({p a, p b} : Set V)

/-- The complete collection of lines determined by pairs of distinct points, deduplicated. -/
noncomputable def determinedLines (p : ι → V) : Finset (Finset ι) :=
  (univ.product univ |>.filter fun ab => ab.1 ≠ ab.2).image fun ab => lineBlock p ab.1 ab.2

omit [DecidableEq ι] in
/-- The line-block representation uses Mathlib affine lines, not an abstract collinearity oracle. -/
theorem mem_lineBlock (p : ι → V) (a b c : ι) :
    c ∈ lineBlock p a b ↔ p c ∈ affineSpan ℝ ({p a, p b} : Set V) := by
  classical
  simp [lineBlock]

theorem mem_determinedLines (p : ι → V) (l : Finset ι) :
    l ∈ determinedLines p ↔ ∃ a b, a ≠ b ∧ l = lineBlock p a b := by
  classical
  constructor
  · intro hl
    obtain ⟨⟨a, b⟩, hab, he⟩ := mem_image.mp hl
    exact ⟨a, b, (mem_filter.mp hab).2, he.symm⟩
  · rintro ⟨a, b, hab, rfl⟩
    exact mem_image.mpr ⟨(a, b), mem_filter.mpr ⟨by simp, hab⟩, rfl⟩

/-- Actual finite affine point sets satisfy the two-points/one-line incidence property. -/
theorem determinedLines_linearSpace (p : ι → V) (hp : Function.Injective p) :
    LinearSpace (determinedLines p) := by
  classical
  have ends (a b : ι) : a ∈ lineBlock p a b ∧ b ∈ lineBlock p a b := by
    simp only [mem_lineBlock]
    exact ⟨left_mem_affineSpan_pair _ _ _, right_mem_affineSpan_pair _ _ _⟩
  constructor
  · intro l hl
    obtain ⟨a, b, hab, rfl⟩ := (mem_determinedLines p l).mp hl
    exact one_lt_card.mpr ⟨a, (ends a b).1, b, (ends a b).2, hab⟩
  · intro a b hab
    refine ⟨lineBlock p a b, ⟨(mem_determinedLines p _).mpr ⟨a, b, hab, rfl⟩,
      (ends a b).1, (ends a b).2⟩, ?_⟩
    intro l hl
    obtain ⟨c, d, _, rfl⟩ := (mem_determinedLines p l).mp hl.1
    have he := affineSpan_pair_eq_of_mem_of_mem_of_ne
      ((mem_lineBlock p c d a).mp hl.2.1) ((mem_lineBlock p c d b).mp hl.2.2)
      (fun h => hab (hp h))
    ext x
    simp only [mem_lineBlock, he]

/-- Complete degree-certificate criterion for arbitrary distinct points in a real affine space. -/
theorem geometric_magic_iff (p : ι → V) (hp : Function.Injective p) :
    (∃ w : ι → ℝ, Magic (determinedLines p) w) ↔
      Fintype.card ι ≤ 1 ∨ univ ∈ determinedLines p ∨
        ((∀ a, 1 < degree (determinedLines p) a) ∧
          DegreeCertificate (K := ℝ) (determinedLines p)) :=
  magic_iff_all_cases _ (determinedLines_linearSpace p hp)

end Geometry
/-- The formula produces rational weights even for configurations with irrational coordinates. -/
theorem weightFormula_cast (L : Finset (Finset ι)) (a : ι) :
    ((weightFormula L a : ℚ) : ℝ) = weightFormula L a := by
  unfold weightFormula totalFormula reciprocalSum
  push_cast
  rfl

omit [Fintype ι] [DecidableEq ι] in
theorem magic_cast (L : Finset (Finset ι)) (w : ι → ℚ) :
    Magic L w ↔ Magic L (fun a => (w a : ℝ)) := by
  unfold Magic WeakMagic
  constructor
  · rintro ⟨hp, hs⟩
    constructor
    · intro a
      exact Rat.cast_pos.mpr (hp a)
    · intro l hl
      change (∑ a ∈ l, (w a : ℝ)) = 1
      rw [← Rat.cast_sum, hs l hl, Rat.cast_one]
  · rintro ⟨hp, hs⟩
    constructor
    · intro a
      exact Rat.cast_pos.mp (hp a)
    · intro l hl
      apply Rat.cast_injective (α := ℝ)
      simpa only [Rat.cast_sum, Rat.cast_one] using hs l hl

/-- Real solvability is equivalent to rational solvability, including all degeneracies. -/
theorem real_magic_iff_rational (L : Finset (Finset ι)) (hL : LinearSpace L) :
    (∃ w : ι → ℝ, Magic L w) ↔ ∃ w : ι → ℚ, Magic L w := by
  constructor
  · intro h
    rcases (magic_iff_all_cases L hL).mp h with hs | hu | ⟨hd, hc⟩
    · exact (magic_iff_all_cases L hL).mpr (Or.inl hs)
    · exact magic_of_full_line L hL hu
    · have hm := (magic_iff_formula L hL hd).mp
        ((magic_iff_degreeCertificate L hL hd).mpr hc)
      refine ⟨weightFormula L, (magic_cast L _).mpr ?_⟩
      simpa only [weightFormula_cast] using hm
  · rintro ⟨w, hw⟩
    exact ⟨fun a => (w a : ℝ), (magic_cast L w).mp hw⟩

/-- Executable rational checker once the finite incidence set has been supplied. -/
def accepts (L : Finset (Finset ι)) : Bool := by
  letI : Decidable (DegreeCertificate (K := ℚ) L) := by
    unfold DegreeCertificate
    infer_instance
  exact decide (Fintype.card ι ≤ 1 ∨ univ ∈ L ∨
    ((∀ a, 1 < degree L a) ∧ DegreeCertificate (K := ℚ) L))

/-- The checker accepts exactly the real-solvable incidence systems. -/
theorem accepts_iff (L : Finset (Finset ι)) (hL : LinearSpace L) :
    accepts L = true ↔ ∃ w : ι → ℝ, Magic L w := by
  rw [real_magic_iff_rational L hL, magic_iff_all_cases L hL]
  simp only [accepts, decide_eq_true_eq]

/-- A rejected certificate is a proof that no positive real weighting exists. -/
theorem rejects_iff (L : Finset (Finset ι)) (hL : LinearSpace L) :
    accepts L = false ↔ ¬∃ w : ι → ℝ, Magic L w := by
  rw [← accepts_iff L hL, Bool.eq_false_iff]

/-- Arbitrary planar real point sets, with no rational-coordinate restriction. -/
theorem planar_accepts_iff (p : ι → Fin 2 → ℝ) (hp : Function.Injective p) :
    accepts (determinedLines p) = true ↔ ∃ w : ι → ℝ, Magic (determinedLines p) w :=
  accepts_iff _ (determinedLines_linearSpace p hp)

section DirectGeometry
variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- Direct formulation over every pair of distinct indexed points. -/
theorem magic_determinedLines_iff (p : ι → V) (w : ι → ℝ) :
    Magic (determinedLines p) w ↔ (∀ a, 0 < w a) ∧
      ∀ a b, a ≠ b → ∑ c ∈ lineBlock p a b, w c = 1 := by
  constructor
  · rintro ⟨hp, hl⟩
    exact ⟨hp, fun a b hab => hl _ ((mem_determinedLines p _).mpr ⟨a, b, hab, rfl⟩)⟩
  · rintro ⟨hp, hl⟩
    refine ⟨hp, ?_⟩
    intro l hm
    obtain ⟨a, b, hab, rfl⟩ := (mem_determinedLines p l).mp hm
    exact hl a b hab

/-- The checker matches equal positive line sums after normalization. -/
theorem geometric_accepts_iff_common_sum (p : ι → V) (hp : Function.Injective p) :
    accepts (determinedLines p) = true ↔
      ∃ (w : ι → ℝ) (C : ℝ), (∀ a, 0 < w a) ∧ 0 < C ∧
        ∀ a b, a ≠ b → ∑ c ∈ lineBlock p a b, w c = C := by
  rw [accepts_iff _ (determinedLines_linearSpace p hp)]
  constructor
  · rintro ⟨w, hw⟩
    obtain ⟨hwpos, hsum⟩ := (magic_determinedLines_iff p w).mp hw
    exact ⟨w, 1, hwpos, zero_lt_one, hsum⟩
  · rintro ⟨w, C, hwp, hC, hs⟩
    refine ⟨fun a => w a / C, (magic_determinedLines_iff p _).mpr ?_⟩
    refine ⟨fun a => div_pos (hwp a) hC, ?_⟩
    intro a b hab
    simp_rw [div_eq_mul_inv]
    rw [← sum_mul, hs a b hab, mul_inv_cancel₀ (ne_of_gt hC)]

end DirectGeometry
/-- Incidence table of five planar points with one collinear triple and otherwise ordinary lines. -/
def fivePointLines : Finset (Finset (Fin 5)) :=
  {{0, 1, 2}, {0, 3}, {0, 4}, {1, 3}, {1, 4}, {2, 3}, {2, 4}, {3, 4}}

theorem fivePoint_linearSpace : LinearSpace fivePointLines := by
  simp [LinearSpace, fivePointLines, Fin.forall_fin_succ, ExistsUnique]

theorem fivePoint_rejected : accepts fivePointLines = false := by
  have hd : ∀ a : Fin 5, degree fivePointLines a = if a < 3 then 3 else 4 := by decide
  have hn : (univ : Finset (Fin 5)) ∉ fivePointLines := by decide
  simp only [accepts, decide_eq_false_iff_not, not_or]
  refine ⟨by decide, hn, ?_⟩
  simp only [DegreeCertificate, reciprocalSum, hd]
  norm_num [Fin.forall_fin_succ, Fin.sum_univ_succ, fivePointLines]

theorem fivePoint_no_magic : ¬∃ w : Fin 5 → ℝ, Magic fivePointLines w :=
  (rejects_iff fivePointLines fivePoint_linearSpace).mp fivePoint_rejected

/-- The failed-Fano incidence table: six triples and three ordinary lines. -/
def failedFanoLines : Finset (Finset (Fin 7)) :=
  {{0, 1, 3}, {0, 2, 4}, {1, 2, 5}, {0, 5, 6}, {1, 4, 6}, {2, 3, 6},
    {3, 4}, {3, 5}, {4, 5}}

theorem failedFano_linearSpace : LinearSpace failedFanoLines := by
  simp [LinearSpace, failedFanoLines, Fin.forall_fin_succ, ExistsUnique]

theorem failedFano_accepted : accepts failedFanoLines = true := by
  have hd : ∀ a : Fin 7, degree failedFanoLines a =
      if 3 ≤ a ∧ a ≤ 5 then 4 else 3 := by decide
  simp only [accepts, decide_eq_true_eq]
  right; right
  constructor
  · rw [show (∀ a, 1 < degree failedFanoLines a) ↔ True by decide]
    trivial
  · simp only [DegreeCertificate, reciprocalSum, hd]
    norm_num [Fin.forall_fin_succ, Fin.sum_univ_succ, failedFanoLines]

theorem failedFano_magic : ∃ w : Fin 7 → ℝ, Magic failedFanoLines w :=
  (accepts_iff failedFanoLines failedFano_linearSpace).mp failedFano_accepted

end MagicWeights
