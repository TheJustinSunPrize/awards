import Mathlib

/-!
# Erdős's lower bound for distinct distances in the plane (Erdős 1946)

Erdős Problem 89 asks whether every set of `n` points in `ℝ²` determines `≫ n / √(log n)`
distinct distances (Guth and Katz proved `≫ n / log n`). This file proves Erdős's original
elementary lower bound from [Er46]: a set of `n` points in the plane determines `≫ √n` distinct
distances. Precisely, if `A` determines `D` distinct distances then `#A ≤ 2 D² + D + 1`; hence
`√n / 2 ≤ D` whenever `n ≥ 2`, and `√n = O(minimalDistinctDistances ℝ² n)`.

`distanceSet`, `distinctDistances` and `minimalDistinctDistances` are copied verbatim from
Google DeepMind's formal-conjectures project (`FormalConjecturesForMathlib/Geometry/Metric.lean`,
Apache-2.0), which states Erdős Problem 89 (`FormalConjectures/ErdosProblems/89.lean`) in terms of
`minimalDistinctDistances ℝ² n`, where `ℝ²` is notation for `EuclideanSpace ℝ (Fin 2)`.

## Proof

Fix `p ∈ A` and let `D = distinctDistances A`. The `n - 1` points of `A \ {p}` lie on the `D`
circles centred at `p` with radii in the distance set. On any such circle `C`, fix `q ∈ C`; the
other points of `C` lie on `D` circles centred at `q ≠ p`, and each of these meets the circle
around `p` in at most two points. Thus `#C ≤ 2D + 1`, and so `n - 1 ≤ (2D + 1) D`.

## References

- [Er46] Erdős, Paul. On sets of distances of `n` points. Amer. Math. Monthly 53 (1946), 248–250.
- [GuKa15] Guth, Larry and Katz, Nets Hawk. On the Erdős distinct distances problem in the plane.
  Ann. of Math. (2) 181 (2015), 155–190.
- <https://www.erdosproblems.com/89>
-/

open Finset Filter Asymptotics

open scoped Finset

namespace DistinctDistances

section Defs

variable {X : Type*} [MetricSpace X]

/-- The set of distances determined by a finite set of points in a metric space. -/
noncomputable def distanceSet (points : Finset X) : Finset ℝ :=
  points.offDiag.image fun (pair : X × X) => dist pair.1 pair.2

/--
Given a finite set of points in a metric space, we define the number of distinct distances
between pairs of points.
-/
noncomputable def distinctDistances (points : Finset X) : ℕ :=
  #(distanceSet points)

variable (X) in
/-- The minimum number of distinct distances determined by a set of `n` points in `X`. -/
noncomputable def minimalDistinctDistances (n : ℕ) : ℕ :=
  sInf {m : ℕ | ∃ points : Finset X, #points = n ∧ distinctDistances points = m}

end Defs

/-- The Euclidean plane, as in formal-conjectures. -/
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

theorem dist_mem_distanceSet {A : Finset ℝ²} {x y : ℝ²} (hx : x ∈ A) (hy : y ∈ A)
    (hxy : x ≠ y) : dist x y ∈ distanceSet A :=
  mem_image.mpr ⟨(x, y), mem_offDiag.mpr ⟨hx, hy, hxy⟩, rfl⟩

/-- Two circles with distinct centres `p ≠ q` in the plane meet in at most two points. -/
theorem card_le_two_of_dist_eq {p q : ℝ²} (hpq : p ≠ q) {r s : ℝ} (S : Finset ℝ²)
    (hS : ∀ x ∈ S, dist p x = r ∧ dist q x = s) : #S ≤ 2 := by
  by_contra h
  obtain ⟨a, ha, b, hb, c, hc, hab, hac, hbc⟩ := two_lt_card.mp (not_le.mp h)
  have hd : Module.finrank ℝ ℝ² = 2 := finrank_euclideanSpace_fin
  obtain ⟨ha1, ha2⟩ := hS a ha
  obtain ⟨hb1, hb2⟩ := hS b hb
  obtain ⟨hc1, hc2⟩ := hS c hc
  rw [dist_comm] at ha1 ha2 hb1 hb2 hc1 hc2
  rcases EuclideanGeometry.eq_of_dist_eq_of_dist_eq_of_finrank_eq_two hd hpq hab ha1 hb1 hc1
    ha2 hb2 hc2 with h | h
  · exact hac h.symm
  · exact hbc h.symm

/-- A subset of `A \ {p}` lying on a circle centred at `p` has at most `2D + 1` points. -/
theorem card_circle_le {A C : Finset ℝ²} {p : ℝ²} {r : ℝ} (hC : C ⊆ A.erase p)
    (hCr : ∀ x ∈ C, dist p x = r) : #C ≤ 2 * distinctDistances A + 1 := by
  classical
  rcases C.eq_empty_or_nonempty with rfl | ⟨q, hq⟩
  · simp
  have hqA := hC hq
  have hqp : q ≠ p := ne_of_mem_erase hqA
  have hmaps : ∀ x ∈ C.erase q, dist q x ∈ distanceSet A := fun x hx =>
    dist_mem_distanceSet (mem_of_mem_erase hqA) (mem_of_mem_erase (hC (mem_of_mem_erase hx)))
      (ne_of_mem_erase hx).symm
  have hfib : ∀ s ∈ distanceSet A, #{x ∈ C.erase q | dist q x = s} ≤ 2 := fun s _ =>
    card_le_two_of_dist_eq hqp.symm _ fun x hx => by
      obtain ⟨hx, hxs⟩ := mem_filter.mp hx
      exact ⟨hCr x (mem_of_mem_erase hx), hxs⟩
  have := card_le_mul_card_image_of_maps_to hmaps 2 hfib
  rw [card_erase_of_mem hq] at this
  unfold distinctDistances
  omega

/-- **Erdős (1946).** A set of points in the plane determining `D` distinct distances has at
most `2 D² + D + 1` points. -/
theorem card_le_two_mul_sq_add (A : Finset ℝ²) :
    #A ≤ 2 * distinctDistances A ^ 2 + distinctDistances A + 1 := by
  classical
  rcases A.eq_empty_or_nonempty with rfl | ⟨p, hp⟩
  · simp
  have hmaps : ∀ x ∈ A.erase p, dist p x ∈ distanceSet A := fun x hx =>
    dist_mem_distanceSet hp (mem_of_mem_erase hx) (ne_of_mem_erase hx).symm
  have hfib : ∀ r ∈ distanceSet A,
      #{x ∈ A.erase p | dist p x = r} ≤ 2 * distinctDistances A + 1 := fun r _ =>
    card_circle_le (filter_subset _ _) fun x hx => (mem_filter.mp hx).2
  have := card_le_mul_card_image_of_maps_to hmaps _ hfib
  rw [card_erase_of_mem hp] at this
  have h2 : (2 * distinctDistances A + 1) * #(distanceSet A) =
      2 * distinctDistances A ^ 2 + distinctDistances A := by
    unfold distinctDistances; ring
  omega

/-- At least two points determine at least one distance. -/
theorem one_le_distinctDistances {A : Finset ℝ²} (hA : 2 ≤ #A) : 1 ≤ distinctDistances A := by
  obtain ⟨x, hx, y, hy, hxy⟩ := one_lt_card.mp hA
  exact card_pos.mpr ⟨_, dist_mem_distanceSet hx hy hxy⟩

/-- **Erdős (1946).** `n ≥ 2` points in the plane determine at least `√n / 2` distinct
distances; in integer form, `n ≤ 4 D²`. -/
theorem card_le_four_mul_sq {A : Finset ℝ²} (hA : 2 ≤ #A) :
    #A ≤ 4 * distinctDistances A ^ 2 := by
  have h1 := card_le_two_mul_sq_add A
  have h2 := one_le_distinctDistances hA
  nlinarith

/-- **Erdős (1946).** `n ≥ 2` points in the plane determine at least `√n / 2` distinct
distances. -/
theorem sqrt_card_div_two_le {A : Finset ℝ²} (hA : 2 ≤ #A) :
    Real.sqrt #A / 2 ≤ distinctDistances A := by
  have h : ((#A : ℕ) : ℝ) ≤ (2 * (distinctDistances A : ℝ)) ^ 2 := by
    have := card_le_four_mul_sq hA
    rw [mul_pow]; norm_num; exact_mod_cast this
  have := Real.sqrt_le_sqrt h
  rw [Real.sqrt_sq (by positivity)] at this
  linarith

/-- The minimum in `minimalDistinctDistances ℝ² n` is attained: the plane contains `n`-point
sets for every `n`. -/
theorem exists_distinctDistances_eq_minimal (n : ℕ) :
    ∃ A : Finset ℝ², #A = n ∧ distinctDistances A = minimalDistinctDistances ℝ² n := by
  obtain ⟨A, hA⟩ := Infinite.exists_subset_card_eq ℝ² n
  exact Nat.sInf_mem (s := {m : ℕ | ∃ points : Finset ℝ², #points = n ∧
    distinctDistances points = m}) ⟨_, A, hA, rfl⟩

/-- **Erdős (1946).** Every set of `n` points in the plane determines at least
`minimalDistinctDistances ℝ² n` distinct distances, and this number `m` satisfies
`n ≤ 2 m² + m + 1`. -/
theorem le_two_mul_minimalDistinctDistances_sq_add (n : ℕ) :
    n ≤ 2 * minimalDistinctDistances ℝ² n ^ 2 + minimalDistinctDistances ℝ² n + 1 := by
  obtain ⟨A, rfl, hA⟩ := exists_distinctDistances_eq_minimal n
  rw [← hA]
  exact card_le_two_mul_sq_add A

/-- **Erdős (1946).** For `n ≥ 2`, `√n / 2 ≤ minimalDistinctDistances ℝ² n`. -/
theorem sqrt_div_two_le_minimalDistinctDistances {n : ℕ} (hn : 2 ≤ n) :
    Real.sqrt n / 2 ≤ minimalDistinctDistances ℝ² n := by
  obtain ⟨A, rfl, hA⟩ := exists_distinctDistances_eq_minimal n
  rw [← hA]
  exact sqrt_card_div_two_le hn

/-- **Erdős (1946)**, in the asymptotic language of `Erdos89.erdos_89` in formal-conjectures:
`√n = O(minimalDistinctDistances ℝ² n)`. -/
theorem sqrt_isBigO_minimalDistinctDistances :
    (fun (n : ℕ) => Real.sqrt n) =O[atTop] (fun n => (minimalDistinctDistances ℝ² n : ℝ)) := by
  refine IsBigO.of_bound 2 ?_
  filter_upwards [eventually_ge_atTop 2] with n hn
  have := sqrt_div_two_le_minimalDistinctDistances hn
  rw [Real.norm_of_nonneg (Real.sqrt_nonneg _), Real.norm_of_nonneg (Nat.cast_nonneg _)]
  linarith

end DistinctDistances
