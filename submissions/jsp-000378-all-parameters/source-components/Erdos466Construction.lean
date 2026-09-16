/-
All-parameter formalization of the parabola construction for Erdős 466.
The construction is based on Ronald Graham's classical argument. The
fixed-parameter public Lean implementation in plby/lean-proofs
8822f7ddef30fadbd92e1c6ab4ed897af356af5e is credited as prior formal work.
Our claimed increment is the uniform parameter theorem and its endpoint bridge,
not first discovery of the mathematical result or first formalization of E466.
Released under the Apache 2.0 license.
-/
import Erdos466Definitions
import Erdos466Arithmetic
import Mathlib.Topology.MetricSpace.ProperSpace

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
