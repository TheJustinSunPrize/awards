import Mathlib.Analysis.Complex.Angle
import Mathlib.Geometry.Euclidean.Angle.Unoriented.Affine
import Mathlib.Geometry.Euclidean.Triangle
import SendovFiveDirections
import Mathlib.Data.Finset.Sort
import Mathlib.Tactic.Linarith

/-! Geometric bridge for direction labels. These lemmas use the standard
Euclidean inner-product angle on the complex plane, not a replacement angle.
Includes a generic projection and the sharp lower bound for five points.
The general Sendov lower bound is not established here. -/
namespace SendovDirectionGeometry
open Real Complex InnerProductGeometry

lemma ne_zero_of_re_pos {z : ℂ} (h : 0 < z.re) : z ≠ 0 := by
  intro hz
  simp [hz] at h

lemma arg_div_eq_sub_of_re_pos {x y : ℂ} (hx : 0 < x.re) (hy : 0 < y.re) :
    (x / y).arg = x.arg - y.arg := by
  have bx := abs_lt.mp (Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hx))
  have by' := abs_lt.mp (Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hy))
  have h := Complex.arg_div_coe_angle (ne_zero_of_re_pos hx) (ne_zero_of_re_pos hy)
  rw [← Real.Angle.coe_sub] at h
  have h' := Complex.arg_coe_angle_eq_iff_eq_toReal.mp h
  rw [Real.Angle.toReal_coe_eq_self_iff.mpr ⟨by linarith, by linarith⟩] at h'
  exact h'

lemma angle_eq_abs_arg_sub_of_re_pos {x y : ℂ} (hx : 0 < x.re) (hy : 0 < y.re) :
    InnerProductGeometry.angle x y = |x.arg-y.arg| := by
  rw [Complex.angle_eq_abs_arg (ne_zero_of_re_pos hx) (ne_zero_of_re_pos hy),
    arg_div_eq_sub_of_re_pos hx hy]

lemma middle_angle_eq {a b c : ℂ} (hab : a.re < b.re) (hbc : b.re < c.re) :
    EuclideanGeometry.angle a b c = π - |(b-a).arg-(c-b).arg| := by
  have hu : 0 < (b-a).re := by simpa using sub_pos.mpr hab
  have hv : 0 < (c-b).re := by simpa using sub_pos.mpr hbc
  change InnerProductGeometry.angle (a-b) (c-b) = _
  rw [show a-b = -(b-a) by abel, InnerProductGeometry.angle_neg_left,
    angle_eq_abs_arg_sub_of_re_pos hu hv]

lemma first_angle_eq {a b c : ℂ} (hab : a.re < b.re) (hbc : b.re < c.re) :
    EuclideanGeometry.angle b a c = |(b-a).arg-(c-a).arg| := by
  apply angle_eq_abs_arg_sub_of_re_pos
  · simpa using sub_pos.mpr hab
  · simpa using sub_pos.mpr (hab.trans hbc)

lemma last_angle_eq {a b c : ℂ} (hab : a.re < b.re) (hbc : b.re < c.re) :
    EuclideanGeometry.angle a c b = |(c-a).arg-(c-b).arg| := by
  change InnerProductGeometry.angle (a-c) (b-c) = _
  rw [show a-c = -(c-a) by abel, show b-c = -(c-b) by abel,
    InnerProductGeometry.angle_neg_neg]
  apply angle_eq_abs_arg_sub_of_re_pos
  · simpa using sub_pos.mpr (hab.trans hbc)
  · simpa using sub_pos.mpr hbc

lemma arg_between {a b c : ℂ} (hab : a.re < b.re) (hbc : b.re < c.re) :
    ((b-a).arg ≤ (c-a).arg ∧ (c-a).arg ≤ (c-b).arg) ∨
    ((c-b).arg ≤ (c-a).arg ∧ (c-a).arg ≤ (b-a).arg) := by
  have hba : b ≠ a := fun h => (ne_of_gt hab) (congrArg Complex.re h)
  have hca : c ≠ a := fun h => (ne_of_gt (hab.trans hbc)) (congrArg Complex.re h)
  have hsum := EuclideanGeometry.angle_add_angle_add_angle_eq_pi c hba
  rw [middle_angle_eq hab hbc, EuclideanGeometry.angle_comm b c a,
    last_angle_eq hab hbc, EuclideanGeometry.angle_comm c a b,
    first_angle_eq hab hbc] at hsum
  have heq : |(b-a).arg-(c-a).arg| + |(c-a).arg-(c-b).arg| =
      |(b-a).arg-(c-b).arg| := by linarith
  rcases le_total (b-a).arg (c-b).arg with h | h
  · left
    rw [abs_of_nonpos (sub_nonpos.mpr h)] at heq
    constructor
    · by_contra hn
      have hn' := lt_of_not_ge hn
      rw [abs_of_pos (sub_pos.mpr hn'),
        abs_of_nonpos (sub_nonpos.mpr (hn'.le.trans h))] at heq
      linarith
    · by_contra hn
      have hn' := lt_of_not_ge hn
      rw [abs_of_nonpos (sub_nonpos.mpr (h.trans hn'.le)),
        abs_of_pos (sub_pos.mpr hn')] at heq
      linarith
  · right
    rw [abs_of_nonneg (sub_nonneg.mpr h)] at heq
    constructor
    · by_contra hn
      have hn' := lt_of_not_ge hn
      rw [abs_of_nonneg (sub_nonneg.mpr (hn'.le.trans h)),
        abs_of_neg (sub_neg.mpr hn')] at heq
      linarith
    · by_contra hn
      have hn' := lt_of_not_ge hn
      rw [abs_of_neg (sub_neg.mpr hn'),
        abs_of_nonneg (sub_nonneg.mpr (h.trans hn'.le))] at heq
      linarith

noncomputable def normalize (lam x : ℝ) : ℝ := (x + π / 2) / lam

lemma normalize_sub (lam x y : ℝ) :
    normalize lam x - normalize lam y = (x-y)/lam := by
  unfold normalize
  ring

lemma normalized_order {lam A B C : ℝ} (hlam : 0 < lam)
    (hAB : A ≤ B) (hBC : B ≤ C) (hAC : lam ≤ C-A)
    (hBA : B-A ≤ π-lam) (hCB : C-B ≤ π-lam) :
    normalize lam A ≤ normalize lam B ∧ normalize lam B ≤ normalize lam C ∧
    1 ≤ normalize lam C - normalize lam A ∧
    normalize lam B - normalize lam A ≤ π/lam-1 ∧
    normalize lam C - normalize lam B ≤ π/lam-1 := by
  have hbudget : π/lam-1 = (π-lam)/lam := by
    rw [sub_div, div_self hlam.ne']
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact div_le_div_of_nonneg_right (by linarith : A + π / 2 ≤ B + π / 2) hlam.le
  · exact div_le_div_of_nonneg_right (by linarith : B + π / 2 ≤ C + π / 2) hlam.le
  · rw [normalize_sub]
    exact (le_div_iff₀ hlam).mpr (by simpa using hAC)
  · rw [normalize_sub, hbudget]
    exact div_le_div_of_nonneg_right hBA hlam.le
  · rw [normalize_sub, hbudget]
    exact div_le_div_of_nonneg_right hCB hlam.le

lemma triangle_labels {a b c : ℂ} {lam : ℝ}
    (hlam : 0 < lam) (hab : a.re < b.re) (hbc : b.re < c.re)
    (ha : EuclideanGeometry.angle b a c ≤ π-lam)
    (hb : EuclideanGeometry.angle a b c ≤ π-lam)
    (hc : EuclideanGeometry.angle a c b ≤ π-lam) :
    SendovFiveDirections.Triangle (π/lam)
      (normalize lam (b-a).arg) (normalize lam (c-a).arg)
      (normalize lam (c-b).arg) := by
  rw [first_angle_eq hab hbc] at ha
  rw [middle_angle_eq hab hbc] at hb
  rw [last_angle_eq hab hbc] at hc
  have hlarge : lam ≤ |(b-a).arg-(c-b).arg| := by linarith
  rcases arg_between hab hbc with ⟨hAB,hBC⟩ | ⟨hCB,hBA⟩
  · left
    apply normalized_order hlam hAB hBC
    · rw [abs_of_nonpos (sub_nonpos.mpr (hAB.trans hBC))] at hlarge
      linarith
    · rw [abs_of_nonpos (sub_nonpos.mpr hAB)] at ha
      linarith
    · rw [abs_of_nonpos (sub_nonpos.mpr hBC)] at hc
      linarith
  · right
    have h := normalized_order hlam hCB hBA
      (by rwa [abs_of_nonneg (sub_nonneg.mpr (hCB.trans hBA))] at hlarge)
      (by rwa [abs_of_nonneg (sub_nonneg.mpr hCB)] at hc)
      (by rwa [abs_of_nonneg (sub_nonneg.mpr hBA)] at ha)
    exact ⟨h.1,h.2.1,h.2.2.1,h.2.2.2.2,h.2.2.2.1⟩

lemma normalized_arg_range {z : ℂ} {lam : ℝ} (hlam : 0 < lam) (hz : 0 < z.re) :
    0 ≤ normalize lam z.arg ∧ normalize lam z.arg < π/lam := by
  have h := abs_lt.mp (Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hz))
  constructor
  · exact div_nonneg (by linarith) hlam.le
  · exact (div_lt_div_iff_of_pos_right hlam).mpr (by linarith)

lemma five_ordered_cap {p : Fin 5 → ℂ} {lam : ℝ} (hlam : 0 < lam)
    (ordered : StrictMono fun i => (p i).re)
    (hangle : ∀ i j k, i ≠ j → i ≠ k → j ≠ k →
      EuclideanGeometry.angle (p i) (p j) (p k) ≤ π-lam) :
    lam ≤ 2*π/5 := by
  let theta (i j : Fin 5) := normalize lam (p j-p i).arg
  have hr (i j : Fin 5) (hij : i < j) :
      0 ≤ theta i j ∧ theta i j < π/lam :=
    normalized_arg_range hlam (by simpa using sub_pos.mpr (ordered hij))
  have ht (i j k : Fin 5) (hij : i < j) (hjk : j < k) :
      SendovFiveDirections.Triangle (π/lam) (theta i j) (theta i k) (theta j k) :=
    triangle_labels hlam (ordered hij) (ordered hjk)
      (hangle j i k (ne_of_gt hij) (ne_of_lt hjk) (ne_of_lt (hij.trans hjk)))
      (hangle i j k (ne_of_lt hij) (ne_of_lt (hij.trans hjk)) (ne_of_lt hjk))
      (hangle i k j (ne_of_lt (hij.trans hjk)) (ne_of_lt hij) (ne_of_gt hjk))
  have hbound := SendovFiveDirections.five_halves_le (π/lam)
    (theta 0 1) (theta 0 2) (theta 0 3) (theta 0 4) (theta 1 2) (theta 1 3) (theta 1 4) (theta 2 3) (theta 2 4) (theta 3 4)
    (hr 0 1 (by decide))
    (hr 0 2 (by decide))
    (hr 0 3 (by decide))
    (hr 0 4 (by decide))
    (hr 1 2 (by decide))
    (hr 1 3 (by decide))
    (hr 1 4 (by decide))
    (hr 2 3 (by decide))
    (hr 2 4 (by decide))
    (hr 3 4 (by decide))
    (ht 0 1 2 (by decide) (by decide))
    (ht 0 1 3 (by decide) (by decide))
    (ht 0 1 4 (by decide) (by decide))
    (ht 0 2 3 (by decide) (by decide))
    (ht 0 2 4 (by decide) (by decide))
    (ht 0 3 4 (by decide) (by decide))
    (ht 1 2 3 (by decide) (by decide))
    (ht 1 2 4 (by decide) (by decide))
    (ht 1 3 4 (by decide) (by decide))
    (ht 2 3 4 (by decide) (by decide))
  have hh := (le_div_iff₀ hlam).mp hbound
  linarith

lemma exists_generic_multiplier {N : ℕ} (p : Fin N → ℂ) (hp : Function.Injective p) :
    ∃ z : ℂ, z ≠ 0 ∧ Function.Injective (fun i => (z*p i).re) := by
  classical
  let bad : Finset ℝ := Finset.univ.image (fun ij : Fin N × Fin N =>
    ((p ij.1).re-(p ij.2).re)/((p ij.1).im-(p ij.2).im))
  obtain ⟨r,hr⟩ := bad.exists_notMem
  refine ⟨1+(r : ℂ)*I, ?_, ?_⟩
  · apply ne_zero_of_re_pos
    simp
  · intro i j heq
    apply hp
    have hlin : (p i).re-r*(p i).im = (p j).re-r*(p j).im := by
      simpa [Complex.mul_re] using heq
    by_cases him : (p i).im = (p j).im
    · apply Complex.ext
      · rw [him] at hlin
        linarith
      · exact him
    · have hden : (p i).im-(p j).im ≠ 0 := sub_ne_zero.mpr him
      have he : r = ((p i).re-(p j).re)/((p i).im-(p j).im) := by
        apply (eq_div_iff hden).mpr
        nlinarith [hlin]
      exact (hr (Finset.mem_image.mpr ⟨(i,j),Finset.mem_univ _,he.symm⟩)).elim

lemma exists_sorted_indices {N : ℕ} (f : Fin N → ℝ) (hf : Function.Injective f) :
    ∃ index : Fin N → Fin N, Function.Injective index ∧ StrictMono (fun i => f (index i)) := by
  classical
  let s := Finset.univ.image f
  have hs : s.card = N := by simp [s, Finset.card_image_of_injective _ hf]
  have hpre (i : Fin N) : ∃ j, f j = s.orderEmbOfFin hs i := by
    obtain ⟨j,_,hj⟩ := Finset.mem_image.mp (s.orderEmbOfFin_mem hs i)
    exact ⟨j,hj⟩
  choose index hi using hpre
  refine ⟨index, ?_, ?_⟩
  · intro i j hij
    apply (s.orderEmbOfFin hs).injective
    rw [← hi i, ← hi j, hij]
  · intro i j hij
    change f (index i) < f (index j)
    rw [hi i,hi j]
    exact (s.orderEmbOfFin hs).strictMono hij

/-- No position or ordering assumption: every five distinct complex-plane points
obey this necessary bound on a common angular cap. -/
theorem five_point_cap {p : Fin 5 → ℂ} {lam : ℝ} (hp : Function.Injective p)
    (hlam : 0 < lam)
    (hangle : ∀ i j k, i ≠ j → i ≠ k → j ≠ k →
      EuclideanGeometry.angle (p i) (p j) (p k) ≤ π-lam) :
    lam ≤ 2*π/5 := by
  obtain ⟨z,hz,hre⟩ := exists_generic_multiplier p hp
  obtain ⟨index,hi,hsort⟩ := exists_sorted_indices (fun i => (z*p i).re) hre
  apply five_ordered_cap hlam hsort
  intro i j k hij hik hjk
  change InnerProductGeometry.angle (z*p (index i)-z*p (index j))
    (z*p (index k)-z*p (index j)) ≤ π-lam
  rw [← mul_sub, ← mul_sub, Complex.angle_mul_left hz]
  exact hangle (index i) (index j) (index k)
    (fun h => hij (hi h)) (fun h => hik (hi h)) (fun h => hjk (hi h))

/-- Every five distinct points in the Euclidean complex plane determine
an angle of at least 108 degrees. No general-position assumption is needed. -/
theorem five_points_large_angle {p : Fin 5 → ℂ} (hp : Function.Injective p) :
    ∃ i j k, i ≠ j ∧ i ≠ k ∧ j ≠ k ∧
      3*π/5 ≤ EuclideanGeometry.angle (p i) (p j) (p k) := by
  classical
  let triples : Finset (Fin 5 × Fin 5 × Fin 5) :=
    Finset.univ.filter (fun v => v.1 ≠ v.2.1 ∧ v.1 ≠ v.2.2 ∧ v.2.1 ≠ v.2.2)
  have hn : triples.Nonempty := by
    refine ⟨(0,1,2), ?_⟩
    simp [triples]
  obtain ⟨v,hv,hmax⟩ := triples.exists_max_image
    (fun v => EuclideanGeometry.angle (p v.1) (p v.2.1) (p v.2.2)) hn
  have hd := (Finset.mem_filter.mp hv).2
  refine ⟨v.1,v.2.1,v.2.2,hd.1,hd.2.1,hd.2.2,?_⟩
  by_contra h
  have hsmall := lt_of_not_ge h
  let M := EuclideanGeometry.angle (p v.1) (p v.2.1) (p v.2.2)
  have hlam : 0 < π-M := by dsimp [M]; linarith [Real.pi_pos]
  have hcap : π-M ≤ 2*π/5 := five_point_cap hp hlam (by
    intro i j k hij hik hjk
    have hm := hmax (i,j,k) (Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, hij,hik,hjk⟩)
    dsimp at hm
    dsimp [M]
    linarith)
  dsimp [M] at hcap
  linarith

#print axioms middle_angle_eq
#print axioms arg_between
#print axioms triangle_labels
#print axioms five_ordered_cap
#print axioms five_point_cap
#print axioms five_points_large_angle
end SendovDirectionGeometry

