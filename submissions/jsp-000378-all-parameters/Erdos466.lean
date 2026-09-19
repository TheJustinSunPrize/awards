/-
JSP-000378 / Erdős 466: full separation-parameter classification.
Canonical self-contained source, assembled from the attributed components.
Graham's construction and the Graham--Rothschild--Straus obstruction are classical.
This artifact contributes a formalization extension; it does not claim new mathematics.
See ATTRIBUTION.md and LICENSE (Apache-2.0).
-/
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.Order.Round
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Algebra.Ring.Int.Parity
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega
import Mathlib.Topology.MetricSpace.ProperSpace

/- Component: Erdos466Definitions -/
/-
Copyright (c) 2026 The Formal Conjectures Authors.
Released under the Apache 2.0 license. This file has been modified.

Definitions and elementary bridges for an all-parameter extension of
Graham's construction for Erdős Problem 466 / JSP-000378.

The nearest-integer convention and the interval bridge follow the public
formalization in plby/lean-proofs, commit
8822f7ddef30fadbd92e1c6ab4ed897af356af5e, ErdosProblems/Erdos466.lean.
That source credits Ronald Graham (mathematics), the Formal Conjectures
Authors, and Codex / GPT-5.6 Sol (formalization).
-/

open Metric Set Filter
open scoped Topology

namespace Erdos466General
noncomputable section

abbrev Plane := EuclideanSpace ℝ (Fin 2)

def distToInt (x : ℝ) : ℝ := |x - (round x : ℝ)|

lemma distToInt_le_half (x : ℝ) : distToInt x ≤ 1 / 2 := abs_sub_round x

lemma distToInt_le (x : ℝ) (z : ℤ) : distToInt x ≤ |x - (z : ℝ)| :=
  round_le x z

lemma distToInt_gt_of_between {x δ : ℝ} (a : ℤ)
    (hleft : (a : ℝ) + δ < x) (hright : x < (a : ℝ) + 1 - δ) :
    δ < distToInt x := by
  rw [distToInt]
  let z : ℤ := round x
  have hz : z ≤ a ∨ a + 1 ≤ z := by omega
  rcases hz with hza | haz
  · have hza' : (z : ℝ) ≤ (a : ℝ) := by exact_mod_cast hza
    calc
      δ < x - (z : ℝ) := by linarith
      _ ≤ |x - (z : ℝ)| := le_abs_self _
  · have haz' : (a : ℝ) + 1 ≤ (z : ℝ) := by exact_mod_cast haz
    calc
      δ < -(x - (z : ℝ)) := by linarith
      _ ≤ |x - (z : ℝ)| := neg_le_abs _

/-- At the endpoint, twice the real number is an odd integer. -/
lemma half_le_distToInt_iff (x : ℝ) :
    1 / 2 ≤ distToInt x ↔ ∃ z : ℤ, 2 * x = (2 * z + 1 : ℤ) := by
  rw [distToInt, abs_sub_round_eq_min, le_min_iff]
  constructor
  · rintro ⟨h₁, h₂⟩
    refine ⟨⌊x⌋, ?_⟩
    simp only [Int.fract] at h₁ h₂
    push_cast
    linarith
  · rintro ⟨z, hz⟩
    have hx : x = (z : ℝ) + 1 / 2 := by push_cast at hz; linarith
    rw [hx, Int.fract_intCast_add]
    norm_num [Int.fract]

def point (q m : ℕ) : Plane := !₂[(q : ℝ) ^ m, ((q : ℝ) ^ m) ^ 2]

@[simp] lemma point_zero (q m : ℕ) : point q m 0 = (q : ℝ) ^ m := by
  simp [point]

@[simp] lemma point_one (q m : ℕ) : point q m 1 = ((q : ℝ) ^ m) ^ 2 := by
  simp [point]

lemma point_injective {q : ℕ} (hq : 2 ≤ q) : Function.Injective (point q) := by
  intro i j hij
  have hqR : (1 : ℝ) < q := by exact_mod_cast (by omega : 1 < q)
  have hc := congrArg (fun p : Plane ↦ p 0) hij
  exact (pow_right_strictMono₀ hqR).injective (by simpa using hc)

lemma point_dist (q i j : ℕ) :
    dist (point q i) (point q j) =
      Real.sqrt ((((q : ℝ) ^ j) ^ 2 - ((q : ℝ) ^ i) ^ 2) ^ 2 +
        ((q : ℝ) ^ j - (q : ℝ) ^ i) ^ 2) := by
  rw [EuclideanSpace.dist_eq]
  simp only [Fin.sum_univ_two, point_zero, point_one, Real.dist_eq]
  rw [sq_abs, sq_abs]
  congr 1
  ring

lemma plane_dist_sq (p r : Plane) :
    dist p r ^ 2 = (p 0 - r 0) ^ 2 + (p 1 - r 1) ^ 2 := by
  rw [EuclideanSpace.dist_sq_eq]
  simp [Fin.sum_univ_two, Real.dist_eq, sq_abs]

end
end Erdos466General


/- Component: Erdos466Arithmetic -/

namespace Erdos466General

/-- Uniform interval estimate for distances between separated points on a parabola.
The integer-base construction can apply this to every pair, without discarding a tail. -/
theorem parabola_distance_interval (δ u v q : ℝ)
    (hd0 : 0 ≤ δ) (hd : δ < 1 / 2) (hu : 1 ≤ u)
    (hq : 4 ≤ q) (hchoose : 4 < (1 - 2 * δ) * q) (hv : q * u ≤ v) :
    let a := v ^ 2 - u ^ 2
    a + δ < Real.sqrt (a ^ 2 + (v - u) ^ 2) ∧
      Real.sqrt (a ^ 2 + (v - u) ^ 2) < a + 1 / 2 := by
  dsimp only
  have hu0 : 0 < u := by linarith
  have hcoef : 0 < 1 - 2 * δ := by linarith
  have hv4 : 4 * u ≤ v :=
    (mul_le_mul_of_nonneg_right hq hu0.le).trans hv
  have hvu : 1 ≤ v - u := by linarith
  have hv0 : 0 < v := by linarith
  have hscaled := mul_le_mul_of_nonneg_left hv hcoef.le
  have hchosen := mul_lt_mul_of_pos_right hchoose hu0
  have hfour : 4 * u < (1 - 2 * δ) * v := by nlinarith only [hscaled, hchosen]
  have hcoefu := mul_pos hcoef hu0
  have hlinear : 1 < (1 - 2 * δ) * v - (1 + 2 * δ) * u := by
    nlinarith only [hfour, hcoefu, hu]
  have hproduct :
      1 < (v - u) * ((1 - 2 * δ) * v - (1 + 2 * δ) * u) := by
    calc
      1 < (1 - 2 * δ) * v - (1 + 2 * δ) * u := hlinear
      _ ≤ (v - u) * ((1 - 2 * δ) * v - (1 + 2 * δ) * u) := by
        nlinarith only [mul_nonneg (sub_nonneg.mpr hvu)
          (show 0 ≤ (1 - 2 * δ) * v - (1 + 2 * δ) * u by linarith)]
  have hδsq : δ ^ 2 < 1 := by nlinarith only [hd0, hd]
  have ha : 0 < v ^ 2 - u ^ 2 := by
    nlinarith only [mul_pos (show 0 < v - u by linarith) (show 0 < v + u by linarith)]
  have hleftsq : (v ^ 2 - u ^ 2 + δ) ^ 2 <
      (v ^ 2 - u ^ 2) ^ 2 + (v - u) ^ 2 := by
    nlinarith only [hproduct, hδsq]
  have hrightsq : (v ^ 2 - u ^ 2) ^ 2 + (v - u) ^ 2 <
      (v ^ 2 - u ^ 2 + 1 / 2) ^ 2 := by
    nlinarith only [mul_pos hu0 (show 0 < v - u by linarith)]
  exact ⟨Real.lt_sqrt_of_sq_lt hleftsq,
    (Real.sqrt_lt' (by linarith : 0 < v ^ 2 - u ^ 2 + 1 / 2)).2 hrightsq⟩

#print axioms parabola_distance_interval

end Erdos466General


/- Component: Erdos466EndpointArithmetic -/

namespace Erdos466General

/-- Determinant of twice the Gram matrix of three vectors, expressed in the
six squared pairwise distances from four points. -/
def sixDistanceGramDet {R : Type*} [CommRing R] (A B C D E F : R) : R :=
  8 * A * B * C + 2 * (A + B - D) * (A + C - E) * (B + C - F)
    - 2 * A * (B + C - F) ^ 2
    - 2 * B * (A + C - E) ^ 2
    - 2 * C * (A + B - D) ^ 2

/-- Every odd integer has square congruent to one modulo eight. -/
theorem odd_sq_emod_eight (n : ℤ) (hn : Odd n) : n ^ 2 % 8 = 1 := by
  obtain ⟨k, hk⟩ := hn
  have hr : n % 8 = 1 ∨ n % 8 = 3 ∨ n % 8 = 5 ∨ n % 8 = 7 := by omega
  rcases hr with hr | hr | hr | hr <;> norm_num [pow_two, Int.mul_emod, hr]

/-- The determinant obstruction when all six squared distances are one modulo eight. -/
theorem sixDistanceGramDet_emod_eight (A B C D E F : ℤ)
    (hA : A % 8 = 1) (hB : B % 8 = 1) (hC : C % 8 = 1)
    (hD : D % 8 = 1) (hE : E % 8 = 1) (hF : F % 8 = 1) :
    sixDistanceGramDet A B C D E F % 8 = 4 := by
  norm_num [sixDistanceGramDet, Int.add_emod, Int.sub_emod, Int.mul_emod,
    pow_two, hA, hB, hC, hD, hE, hF]

theorem sixDistanceGramDet_ne_zero_of_mod_eight (A B C D E F : ℤ)
    (hA : A % 8 = 1) (hB : B % 8 = 1) (hC : C % 8 = 1)
    (hD : D % 8 = 1) (hE : E % 8 = 1) (hF : F % 8 = 1) :
    sixDistanceGramDet A B C D E F ≠ 0 := by
  have h := sixDistanceGramDet_emod_eight A B C D E F hA hB hC hD hE hF
  intro hzero
  rw [hzero] at h
  norm_num at h

/-- Four points with odd integral mutual distances would have a nonzero Gram determinant. -/
theorem sixDistanceGramDet_ne_zero_of_odd (a b c d e f : ℤ)
    (ha : Odd a) (hb : Odd b) (hc : Odd c)
    (hd : Odd d) (he : Odd e) (hf : Odd f) :
    sixDistanceGramDet (a ^ 2) (b ^ 2) (c ^ 2) (d ^ 2) (e ^ 2) (f ^ 2) ≠ 0 :=
  sixDistanceGramDet_ne_zero_of_mod_eight _ _ _ _ _ _
    (odd_sq_emod_eight a ha) (odd_sq_emod_eight b hb) (odd_sq_emod_eight c hc)
    (odd_sq_emod_eight d hd) (odd_sq_emod_eight e he) (odd_sq_emod_eight f hf)

/-- Any three vectors in the real plane have zero Gram determinant.  This is
the coordinate identity needed to exclude four points with odd integral distances. -/
theorem sixDistanceGramDet_plane (u₁ u₂ v₁ v₂ w₁ w₂ : ℝ) :
    sixDistanceGramDet
      (u₁ ^ 2 + u₂ ^ 2) (v₁ ^ 2 + v₂ ^ 2) (w₁ ^ 2 + w₂ ^ 2)
      ((u₁ - v₁) ^ 2 + (u₂ - v₂) ^ 2)
      ((u₁ - w₁) ^ 2 + (u₂ - w₂) ^ 2)
      ((v₁ - w₁) ^ 2 + (v₂ - w₂) ^ 2) = 0 := by
  unfold sixDistanceGramDet
  ring

@[simp] theorem sixDistanceGramDet_intCast (A B C D E F : ℤ) :
    ((sixDistanceGramDet A B C D E F : ℤ) : ℝ) =
      sixDistanceGramDet (A : ℝ) (B : ℝ) (C : ℝ) (D : ℝ) (E : ℝ) (F : ℝ) := by
  simp [sixDistanceGramDet]

#print axioms sixDistanceGramDet_ne_zero_of_odd
#print axioms sixDistanceGramDet_plane

end Erdos466General


/- Component: Erdos466Endpoint -/
/-
Endpoint obstruction for Erdős 466 / JSP-000378.
The odd-distance obstruction is classical; see Graham, Rothschild and
Straus, "Are there n+2 points in E^n with odd integral distances?" (1974).
This file connects the elementary Gram-determinant calculation to the
standard Euclidean metric and the nearest-integer convention.
-/

namespace Erdos466General
noncomputable section

lemma gram_distances_zero (p₀ p₁ p₂ p₃ : Plane) :
    sixDistanceGramDet
      (4 * dist p₀ p₁ ^ 2) (4 * dist p₀ p₂ ^ 2) (4 * dist p₀ p₃ ^ 2)
      (4 * dist p₁ p₂ ^ 2) (4 * dist p₁ p₃ ^ 2) (4 * dist p₂ p₃ ^ 2) = 0 := by
  simp only [plane_dist_sq, sixDistanceGramDet]
  ring

/-- Four planar points cannot have all six distances at least one half away
from the nearest integer. This treats the non-strict endpoint in the original problem. -/
theorem no_four_half (p₀ p₁ p₂ p₃ : Plane)
    (h₀₁ : 1 / 2 ≤ distToInt (dist p₀ p₁))
    (h₀₂ : 1 / 2 ≤ distToInt (dist p₀ p₂))
    (h₀₃ : 1 / 2 ≤ distToInt (dist p₀ p₃))
    (h₁₂ : 1 / 2 ≤ distToInt (dist p₁ p₂))
    (h₁₃ : 1 / 2 ≤ distToInt (dist p₁ p₃))
    (h₂₃ : 1 / 2 ≤ distToInt (dist p₂ p₃)) : False := by
  obtain ⟨a, ha⟩ := (half_le_distToInt_iff _).mp h₀₁
  obtain ⟨b, hb⟩ := (half_le_distToInt_iff _).mp h₀₂
  obtain ⟨c, hc⟩ := (half_le_distToInt_iff _).mp h₀₃
  obtain ⟨d, hd⟩ := (half_le_distToInt_iff _).mp h₁₂
  obtain ⟨e, he⟩ := (half_le_distToInt_iff _).mp h₁₃
  obtain ⟨f, hf⟩ := (half_le_distToInt_iff _).mp h₂₃
  have hsq (x : ℝ) (z : ℤ) (hz : 2 * x = (2 * z + 1 : ℤ)) :
      ((((2 * z + 1) ^ 2 : ℤ)) : ℝ) = 4 * x ^ 2 := by
    rw [Int.cast_pow, ← hz]
    ring
  have hzero :
      sixDistanceGramDet ((2*a+1)^2) ((2*b+1)^2) ((2*c+1)^2)
        ((2*d+1)^2) ((2*e+1)^2) ((2*f+1)^2) = (0 : ℤ) := by
    apply Int.cast_injective (α := ℝ)
    rw [sixDistanceGramDet_intCast]
    rw [hsq _ _ ha, hsq _ _ hb, hsq _ _ hc, hsq _ _ hd, hsq _ _ he, hsq _ _ hf]
    simpa only [Int.cast_zero] using gram_distances_zero p₀ p₁ p₂ p₃
  have hodd (z : ℤ) : Odd (2 * z + 1) := ⟨z, by ring⟩
  exact sixDistanceGramDet_ne_zero_of_odd _ _ _ _ _ _
    (hodd a) (hodd b) (hodd c) (hodd d) (hodd e) (hodd f) hzero

theorem no_four_at_or_above_half {δ : ℝ} (hδ : 1 / 2 ≤ δ)
    (P : Fin 4 → Plane)
    (hP : ∀ i j, i ≠ j → δ ≤ distToInt (dist (P i) (P j))) : False := by
  exact no_four_half (P 0) (P 1) (P 2) (P 3)
    (hδ.trans (hP 0 1 (by decide))) (hδ.trans (hP 0 2 (by decide)))
    (hδ.trans (hP 0 3 (by decide))) (hδ.trans (hP 1 2 (by decide)))
    (hδ.trans (hP 1 3 (by decide))) (hδ.trans (hP 2 3 (by decide)))

end
end Erdos466General


/- Component: Erdos466Construction -/
/-
All-parameter formalization of the parabola construction for Erdős 466.
The construction is based on Ronald Graham's classical argument. The
fixed-parameter public Lean implementation in plby/lean-proofs
8822f7ddef30fadbd92e1c6ab4ed897af356af5e is credited as prior formal work.
Our claimed increment is the uniform parameter theorem and its endpoint bridge,
not first discovery of the mathematical result or first formalization of E466.
Released under the Apache 2.0 license.
-/

open Metric Set Filter
open scoped Topology

namespace Erdos466General
noncomputable section

lemma choose_base {δ : ℝ} (hd0 : 0 ≤ δ) (hd : δ < 1 / 2) :
    ∃ q : ℕ, 4 ≤ q ∧ 4 < (1 - 2 * δ) * (q : ℝ) := by
  have hc : 0 < 1 - 2 * δ := by linarith
  obtain ⟨q, hq⟩ := exists_nat_gt (max (4 : ℝ) (4 / (1 - 2 * δ)))
  have hq4 : (4 : ℝ) < q := (le_max_left _ _).trans_lt hq
  have hdiv : 4 / (1 - 2 * δ) < (q : ℝ) := (le_max_right _ _).trans_lt hq
  refine ⟨q, ?_, ?_⟩
  · exact_mod_cast hq4.le
  · have := (div_lt_iff₀ hc).mp hdiv
    nlinarith

lemma point_away {δ : ℝ} (hd0 : 0 ≤ δ) (hd : δ < 1 / 2)
    {q : ℕ} (hq : 4 ≤ q) (hchoose : 4 < (1 - 2 * δ) * (q : ℝ))
    {i j : ℕ} (hij : i < j) :
    δ < distToInt (dist (point q i) (point q j)) := by
  let u : ℝ := (q : ℝ) ^ i
  let v : ℝ := (q : ℝ) ^ j
  have hqR : (4 : ℝ) ≤ q := by exact_mod_cast hq
  have hu : 1 ≤ u := one_le_pow₀ (by linarith : (1 : ℝ) ≤ q)
  have hv : (q : ℝ) * u ≤ v := by
    dsimp [u, v]
    calc
      (q : ℝ) * (q : ℝ) ^ i = (q : ℝ) ^ (i + 1) := by rw [pow_succ]; ring
      _ ≤ (q : ℝ) ^ j :=
        (pow_right_strictMono₀ (by linarith : (1 : ℝ) < q)).monotone
          (Nat.succ_le_iff.mpr hij)
  let a : ℤ := ((q : ℤ) ^ j) ^ 2 - ((q : ℤ) ^ i) ^ 2
  have ha : (a : ℝ) = v ^ 2 - u ^ 2 := by dsimp [a, u, v]; push_cast; rfl
  have h := parabola_distance_interval δ u v q hd0 hd hu hqR hchoose hv
  rw [point_dist]
  apply distToInt_gt_of_between a
  · simpa [ha, u, v] using h.1
  · have hr := h.2
    change Real.sqrt ((v ^ 2 - u ^ 2) ^ 2 + (v - u) ^ 2) < (a : ℝ) + 1 - δ
    rw [ha]
    linarith

theorem infinite_configuration {δ : ℝ} (hd0 : 0 ≤ δ) (hd : δ < 1 / 2) :
    ∃ P : ℕ → Plane, Function.Injective P ∧
      ∀ i j, i ≠ j → δ < distToInt (dist (P i) (P j)) := by
  obtain ⟨q, hq, hchoose⟩ := choose_base hd0 hd
  refine ⟨point q, point_injective (by omega), ?_⟩
  intro i j hij
  rcases lt_or_gt_of_ne hij with hij | hji
  · exact point_away hd0 hd hq hchoose hij
  · simpa [dist_comm] using point_away hd0 hd hq hchoose hji

/-- The same non-strict distance condition as the original problem. -/
def Realizable (X δ : ℝ) (n : ℕ) : Prop :=
  ∃ (c : Plane) (P : Fin n → Plane), Function.Injective P ∧
    (∀ i, P i ∈ closedBall c X) ∧
    ∀ i j, i ≠ j → δ ≤ distToInt (dist (P i) (P j))

def admissibleSizes (X δ : ℝ) : Set ℕ := {n | Realizable X δ n}

def N (X δ : ℝ) : ℕ := sSup (admissibleSizes X δ)

lemma zero_realizable (X δ : ℝ) : Realizable X δ 0 := by
  refine ⟨0, (fun i ↦ i.elim0), ?_, ?_, ?_⟩
  · intro i; exact i.elim0
  · intro i; exact i.elim0
  · intro i; exact i.elim0

/- This compactness argument is adapted from the attributed prior E466 Lean source. -/
lemma admissibleSizes_bddAbove (X : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    BddAbove (admissibleSizes X δ) := by
  obtain ⟨t, _htsub, htfin, hcover⟩ :=
    finite_cover_balls_of_compact (isCompact_closedBall (0 : Plane) X)
      (by positivity : 0 < δ / 3)
  let _ : Fintype t := htfin.fintype
  refine ⟨Fintype.card t, ?_⟩
  intro n hn
  rcases hn with ⟨c, P, hPinj, hPmem, hsep⟩
  have htranslated (i : Fin n) : P i - c ∈ closedBall (0 : Plane) X := by
    rw [mem_closedBall]
    simpa [dist_eq_norm] using hPmem i
  have hchoice (i : Fin n) : ∃ y ∈ t, dist (P i - c) y < δ / 3 := by
    rcases Set.mem_iUnion.mp (hcover (htranslated i)) with ⟨y, hy⟩
    rcases Set.mem_iUnion.mp hy with ⟨hyt, hyball⟩
    exact ⟨y, hyt, hyball⟩
  choose f hfmem hfclose using hchoice
  let g : Fin n → t := fun i ↦ ⟨f i, hfmem i⟩
  have hginj : Function.Injective g := by
    intro i j hij
    by_contra hne
    have hfij : f i = f j := congrArg Subtype.val hij
    have hdistlt : dist (P i) (P j) < δ := by
      calc
        dist (P i) (P j) = dist (P i - c) (P j - c) := by rw [dist_sub_right]
        _ ≤ dist (P i - c) (f i) + dist (f i) (P j - c) := dist_triangle ..
        _ < δ / 3 + δ / 3 := by
          apply add_lt_add (hfclose i)
          rw [dist_comm, hfij]
          exact hfclose j
        _ < δ := by linarith
    have hdistge : δ ≤ dist (P i) (P j) :=
      (hsep i j hne).trans (by simpa [abs_of_nonneg dist_nonneg] using
        (distToInt_le (dist (P i) (P j)) 0))
    exact (not_lt_of_ge hdistge) hdistlt
  simpa using Fintype.card_le_of_injective g hginj

lemma N_realizable (X : ℝ) {δ : ℝ} (hδ : 0 < δ) : Realizable X δ (N X δ) := by
  exact Nat.sSup_mem ⟨0, zero_realizable X δ⟩ (admissibleSizes_bddAbove X hδ)

lemma Realizable.mono_radius {X Y δ : ℝ} {n : ℕ}
    (h : Realizable X δ n) (hXY : X ≤ Y) : Realizable Y δ n := by
  rcases h with ⟨c, P, hPinj, hPmem, hsep⟩
  exact ⟨c, P, hPinj, fun i ↦ closedBall_subset_closedBall hXY (hPmem i), hsep⟩

/-- Every finite initial segment of the infinite construction fits in a disk. -/
theorem arbitrarily_large_configuration {δ : ℝ} (hd0 : 0 ≤ δ) (hd : δ < 1 / 2)
    (n : ℕ) : ∃ X : ℝ, Realizable X δ n := by
  obtain ⟨P, hPinj, hPsep⟩ := infinite_configuration hd0 hd
  let X : ℝ := ∑ i : Fin n, dist (P i.val) 0
  refine ⟨X, 0, (fun i ↦ P i.val), ?_, ?_, ?_⟩
  · intro i j hij
    exact Fin.ext (hPinj hij)
  · intro i
    rw [mem_closedBall]
    change dist (P i.val) (0 : Plane) ≤ ∑ j : Fin n, dist (P j.val) (0 : Plane)
    exact Finset.single_le_sum (fun (j : Fin n) _ ↦
      (dist_nonneg : 0 ≤ dist (P j.val) (0 : Plane))) (Finset.mem_univ i)
  · intro i j hij
    exact (hPsep _ _ (fun h ↦ hij (Fin.ext h))).le

theorem N_tendsto_infinity {δ : ℝ} (hd0 : 0 < δ) (hd : δ < 1 / 2) :
    Tendsto (fun X : ℝ ↦ N X δ) atTop atTop := by
  refine tendsto_atTop.2 fun n ↦ ?_
  obtain ⟨R, hR⟩ := arbitrarily_large_configuration hd0.le hd n
  filter_upwards [eventually_ge_atTop R] with X hX
  exact le_csSup (admissibleSizes_bddAbove X hd0) (hR.mono_radius hX)


#print axioms infinite_configuration
#print axioms N_tendsto_infinity

end
end Erdos466General


/- Component: Erdos466General -/
/- Full parameter classification for Erdős 466 / JSP-000378.
See Erdos466Construction.lean, README and ATTRIBUTION for prior work and scope.
Released under the Apache 2.0 license. -/

open Metric Set Filter
open scoped Topology
namespace Erdos466General
noncomputable section

lemma realizable_card_le_three {δ X : ℝ} (hδ : 1 / 2 ≤ δ) {n : ℕ}
    (h : Realizable X δ n) : n ≤ 3 := by
  by_contra hn
  have hn4 : 4 ≤ n := by omega
  rcases h with ⟨c, P, hPinj, hPmem, hPsep⟩
  let e : Fin 4 → Fin n := fun i ↦ ⟨i.val, lt_of_lt_of_le i.isLt hn4⟩
  apply no_four_at_or_above_half hδ (P ∘ e)
  intro i j hij
  apply hPsep
  intro he
  apply hij
  exact Fin.ext (congrArg (fun x : Fin n ↦ x.val) he)

theorem N_le_three_at_or_above_half {δ : ℝ} (hδ : 1 / 2 ≤ δ) (X : ℝ) :
    N X δ ≤ 3 := by
  exact realizable_card_le_three hδ (N_realizable X (by linarith))

/-- Full parameter classification for the original non-strict E466 definition. -/
theorem erdos_466_parameter_classification {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun X : ℝ ↦ N X δ) atTop atTop ↔ δ < 1 / 2 := by
  constructor
  · intro ht
    by_contra hn
    have hd : 1 / 2 ≤ δ := le_of_not_gt hn
    obtain ⟨X, hX⟩ := ((tendsto_atTop.1 ht) 4).exists
    have := N_le_three_at_or_above_half hd X
    omega
  · exact N_tendsto_infinity hδ

/-- The original existence question follows from the stronger classification. -/
theorem erdos_466 : ∃ δ : ℝ, 0 < δ ∧
    Tendsto (fun X : ℝ ↦ N X δ) atTop atTop := by
  exact ⟨1 / 10, by norm_num, N_tendsto_infinity (by norm_num) (by norm_num)⟩

#print axioms erdos_466_parameter_classification
#print axioms erdos_466

end
end Erdos466General
