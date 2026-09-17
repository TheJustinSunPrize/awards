import Mathlib

/-!
# Erdős Problem 104: Elekes' lower bound `≫ n ^ (3/2)` for unit circles

Erdős Problem 104 asks for the maximum number of distinct unit circles containing at least three
points of an `n`-point set in the plane; the conjecture is that it is `o(n²)` (open). This file
proves the known lower bound of Elekes (1984): there are `n`-point sets with `≫ n ^ (3/2)` such
circles.

`unitCircleCount`, `possibleUnitCircleCounts` and `maxUnitCircleCount` are copied verbatim from
Google DeepMind's formal-conjectures project (`FormalConjectures/ErdosProblems/104.lean`,
Apache-2.0), as is the notation `ℝ²` for `EuclideanSpace ℝ (Fin 2)`
(`FormalConjecturesForMathlib/Geometry/2d.lean`), which is inlined here as a local notation.

## Construction (Elekes)

Take `m` unit vectors `U` whose subset sums are pairwise distinct (such `U` exist since the unit
circle is infinite and each new vector only has to avoid finitely many values). Let
`P = {u + v : u ≠ v ∈ U}` (`m.choose 2` points). For every `3`-subset `{a, b, c} ⊆ U` the unit
circle centred at `a + b + c` passes through the three distinct points `a + b`, `a + c`, `b + c`
of `P`, and distinct `3`-subsets give distinct centres. Hence `P` has at least `m.choose 3`
unit circles through three of its points. With `m = ⌊√n⌋` and padding `P` to exactly `n`
points this gives `n ^ (3/2) ≤ 48 · maxUnitCircleCount n` for `n ≥ 25`.

## Main results

* `Erdos104.exists_card_eq_choose_two_choose_three_le`: for every `m` there is a set of exactly
  `m.choose 2` points with at least `m.choose 3` unit circles through three of its points.
* `Erdos104.choose_three_le_maxUnitCircleCount`:
  `m.choose 2 ≤ n → m.choose 3 ≤ maxUnitCircleCount n`.
* `Erdos104.rpow_le_maxUnitCircleCount`: `25 ≤ n → n ^ (3/2) ≤ 48 * maxUnitCircleCount n`.
* `Erdos104.erdos_104_lower_bound`: `n ^ (3/2) = O(maxUnitCircleCount n)`.
-/

open Filter Asymptotics EuclideanGeometry

namespace Erdos104

/-- The Euclidean plane (notation from formal-conjectures). -/
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

/-- The number of distinct unit circles containing at least three points of `P`. -/
noncomputable def unitCircleCount (P : Finset ℝ²) : ℕ :=
  Set.ncard {s : Sphere ℝ² | s.radius = 1 ∧ 3 ≤ {p ∈ (P : Set ℝ²) | p ∈ s}.ncard}

/-- The set of unit-circle counts attained by configurations of `n` points in the plane. -/
noncomputable def possibleUnitCircleCounts (n : ℕ) : Set ℕ :=
  {k | ∃ P : Finset ℝ², P.card = n ∧ unitCircleCount P = k}

/-- The maximum number of qualifying unit circles attained by a configuration of `n` points. -/
noncomputable def maxUnitCircleCount (n : ℕ) : ℕ :=
  sSup (possibleUnitCircleCounts n)

/-! ### The counted set is finite, monotone in `P`, and bounded -/

/-- Two circles of the same radius sharing three distinct points coincide. -/
theorem sphere_eq_of_three {s t : Sphere ℝ²} (hr : s.radius = t.radius) {a b c : ℝ²}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (has : a ∈ s) (hbs : b ∈ s) (hcs : c ∈ s)
    (hat : a ∈ t) (hbt : b ∈ t) (hct : c ∈ t) : s = t := by
  rw [mem_sphere] at has hbs hcs hat hbt hct
  by_cases hc : s.center = t.center
  · exact Sphere.ext hc hr
  · exfalso
    rcases eq_of_dist_eq_of_dist_eq_of_finrank_eq_two finrank_euclideanSpace_fin hc hab has hbs
      hcs hat hbt hct with h | h
    · exact hac h.symm
    · exact hbc h.symm

open Classical in
/-- The unit circles through at least three points of `P` inject into the subsets of `P`. -/
theorem injOn_filter_mem (P : Finset ℝ²) :
    Set.InjOn (fun s : Sphere ℝ² => P.filter (· ∈ s))
      {s : Sphere ℝ² | s.radius = 1 ∧ 3 ≤ {p ∈ (P : Set ℝ²) | p ∈ s}.ncard} := by
  rintro s ⟨hs1, hs3⟩ t ⟨ht1, -⟩ hst
  have hmem : ∀ p, p ∈ P ∧ p ∈ s ↔ p ∈ P ∧ p ∈ t := fun p => by
    simpa using congrArg (p ∈ ·) hst
  obtain ⟨a, b, c, ha, hb, hc, hab, hac, hbc⟩ :=
    (Set.two_lt_ncard_iff ((P.finite_toSet).subset fun p hp => hp.1)).1 hs3
  exact sphere_eq_of_three (hs1.trans ht1.symm) hab hac hbc ha.2 hb.2 hc.2
    ((hmem a).1 ha).2 ((hmem b).1 hb).2 ((hmem c).1 hc).2

open Classical in
theorem mapsTo_filter_mem (P : Finset ℝ²) :
    Set.MapsTo (fun s : Sphere ℝ² => P.filter (· ∈ s))
      {s : Sphere ℝ² | s.radius = 1 ∧ 3 ≤ {p ∈ (P : Set ℝ²) | p ∈ s}.ncard}
      (P.powerset : Set (Finset ℝ²)) := fun _ _ =>
  Finset.mem_coe.2 (Finset.mem_powerset.2 (Finset.filter_subset _ _))

/-- There are only finitely many unit circles through at least three points of `P`, so
`unitCircleCount` really counts them (`Set.ncard` of an infinite set would be `0`). -/
theorem finite_unitCircles (P : Finset ℝ²) :
    {s : Sphere ℝ² | s.radius = 1 ∧ 3 ≤ {p ∈ (P : Set ℝ²) | p ∈ s}.ncard}.Finite :=
  Set.Finite.of_injOn (mapsTo_filter_mem P) (injOn_filter_mem P) (Finset.finite_toSet _)

theorem unitCircleCount_le_two_pow (P : Finset ℝ²) : unitCircleCount P ≤ 2 ^ P.card := by
  rw [unitCircleCount, ← Finset.card_powerset, ← Set.ncard_coe_finset]
  exact Set.ncard_le_ncard_of_injOn _ (mapsTo_filter_mem P) (injOn_filter_mem P)
    (Finset.finite_toSet _)

theorem unitCircleCount_mono {P Q : Finset ℝ²} (h : P ⊆ Q) :
    unitCircleCount P ≤ unitCircleCount Q := by
  refine Set.ncard_le_ncard ?_ (finite_unitCircles Q)
  rintro s ⟨hs1, hs3⟩
  refine ⟨hs1, hs3.trans (Set.ncard_le_ncard ?_ ((Q.finite_toSet).subset fun p hp => hp.1))⟩
  exact fun p hp => ⟨h hp.1, hp.2⟩

theorem bddAbove_possibleUnitCircleCounts (n : ℕ) : BddAbove (possibleUnitCircleCounts n) := by
  refine ⟨2 ^ n, ?_⟩
  rintro k ⟨P, rfl, rfl⟩
  exact unitCircleCount_le_two_pow P

/-! ### Unit vectors with distinct subset sums -/

/-- The unit circle in `ℝ²` is infinite. -/
theorem infinite_unit_sphere : {x : ℝ² | ‖x‖ = 1}.Infinite := by
  let f : ℝ → ℝ² := fun t => !₂[Real.cos t, Real.sin t]
  have hf : Set.InjOn f (Set.Icc 0 Real.pi) := by
    intro s hs t ht hst
    have h0 := congrArg (fun x : ℝ² => x 0) hst
    exact Real.injOn_cos hs ht (by simpa [f] using h0)
  refine ((Set.Icc_infinite Real.pi_pos).image hf).mono ?_
  rintro _ ⟨t, -, rfl⟩
  simp [f, EuclideanSpace.norm_eq]

/-- For every `m` there are `m` unit vectors in `ℝ²` whose subset sums are pairwise distinct. -/
theorem exists_unit_vectors_injOn_sum (m : ℕ) :
    ∃ U : Finset ℝ², U.card = m ∧ (∀ u ∈ U, ‖u‖ = 1) ∧
      Set.InjOn (fun S : Finset ℝ² => ∑ x ∈ S, x) (U.powerset : Set (Finset ℝ²)) := by
  induction m with
  | zero => exact ⟨∅, by simp, by simp, by simp⟩
  | succ m ih =>
    obtain ⟨U, hcard, hunit, hinj⟩ := ih
    obtain ⟨v, hv1, hvB⟩ := infinite_unit_sphere.exists_notMem_finset
      ((U.powerset ×ˢ U.powerset).image fun ST => ∑ x ∈ ST.2, x - ∑ x ∈ ST.1, x)
    have hbad : ∀ S ⊆ U, ∀ T ⊆ U, v + ∑ x ∈ S, x ≠ ∑ x ∈ T, x := by
      intro S hS T hT h
      refine hvB (Finset.mem_image.2 ⟨(S, T), by simp [hS, hT], ?_⟩)
      simp [← h]
    have hvU : v ∉ U := fun hv => hbad ∅ (Finset.empty_subset _) {v}
      (Finset.singleton_subset_iff.2 hv) (by simp)
    refine ⟨insert v U, by rw [Finset.card_insert_of_notMem hvU, hcard], ?_, ?_⟩
    · intro u hu
      rcases Finset.mem_insert.1 hu with rfl | hu
      · exact hv1
      · exact hunit u hu
    · have hsum : ∀ S ⊆ U, ∑ x ∈ insert v S, x = v + ∑ x ∈ S, x := fun S hS =>
        Finset.sum_insert fun h => hvU (hS h)
      intro S hS T hT hST
      simp only [Finset.mem_coe, Finset.powerset_insert, Finset.mem_union, Finset.mem_image,
        Finset.mem_powerset] at hS hT
      dsimp only at hST
      rcases hS with hS | ⟨S, hS, rfl⟩ <;> rcases hT with hT | ⟨T, hT, rfl⟩
      · exact hinj (by simpa using hS) (by simpa using hT) hST
      · rw [hsum T hT] at hST
        exact absurd hST.symm (hbad T hT S hS)
      · rw [hsum S hS] at hST
        exact absurd hST (hbad S hS T hT)
      · rw [hsum S hS, hsum T hT] at hST
        rw [hinj (by simpa using hS) (by simpa using hT) (add_left_cancel hST)]

/-! ### Elekes' construction -/

/-- **Elekes' construction.** For every `m` there is a set of exactly `m.choose 2` points in the
plane with at least `m.choose 3` distinct unit circles each containing at least three of them. -/
theorem exists_card_eq_choose_two_choose_three_le (m : ℕ) :
    ∃ P : Finset ℝ², P.card = m.choose 2 ∧ m.choose 3 ≤ unitCircleCount P := by
  classical
  obtain ⟨U, hcard, hunit, hinj⟩ := exists_unit_vectors_injOn_sum m
  set σ : Finset ℝ² → ℝ² := fun S => ∑ x ∈ S, x with hσ
  have hinj' : ∀ {k}, Set.InjOn σ (U.powersetCard k : Set (Finset ℝ²)) := fun {k} =>
    hinj.mono fun S hS => by simpa using (Finset.mem_powersetCard.1 hS).1
  -- the point set `P = {u + v : u ≠ v ∈ U}`
  refine ⟨(U.powersetCard 2).image σ, ?_, ?_⟩
  · rw [Finset.card_image_of_injOn hinj', Finset.card_powersetCard, hcard]
  -- the unit circles centred at `a + b + c` for `{a, b, c} ⊆ U`
  rw [unitCircleCount, ← hcard, ← Finset.card_powersetCard, ← Set.ncard_coe_finset]
  refine Set.ncard_le_ncard_of_injOn (fun T => (⟨σ T, 1⟩ : Sphere ℝ²)) ?_ ?_
    (finite_unitCircles _)
  · intro T hT
    have hT' := Finset.mem_powersetCard.1 hT
    refine ⟨rfl, ?_⟩
    -- the three points `σ (T.erase x)`, `x ∈ T`, lie on the circle
    have hsub : ((T.image fun x => σ (T.erase x)) : Set ℝ²) ⊆
        {p ∈ ((U.powersetCard 2).image σ : Set ℝ²) |
          p ∈ (⟨σ T, 1⟩ : Sphere ℝ²)} := by
      intro p hp
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hp
      refine ⟨Finset.mem_image.2 ⟨T.erase x, Finset.mem_powersetCard.2
        ⟨(Finset.erase_subset _ _).trans hT'.1, by rw [Finset.card_erase_of_mem hx, hT'.2]⟩,
          rfl⟩, ?_⟩
      rw [mem_sphere, dist_eq_norm]
      have := Finset.add_sum_erase T (fun y => y) hx
      simp only [hσ, ← this, sub_add_cancel_right, norm_neg]
      exact hunit x (hT'.1 hx)
    have hcard3 : (T.image fun x => σ (T.erase x)).card = 3 := by
      rw [Finset.card_image_of_injOn, hT'.2]
      intro x hx y hy hxy
      have hx' : T.erase x ⊆ U := (Finset.erase_subset _ _).trans hT'.1
      have hy' : T.erase y ⊆ U := (Finset.erase_subset _ _).trans hT'.1
      exact T.erase_injOn hx hy (hinj (Finset.mem_coe.2 (Finset.mem_powerset.2 hx'))
        (Finset.mem_coe.2 (Finset.mem_powerset.2 hy')) hxy)
    rw [← hcard3, ← Set.ncard_coe_finset]
    exact Set.ncard_le_ncard hsub ((Finset.finite_toSet _).subset fun p hp => hp.1)
  · intro S hS T hT hST
    exact hinj' hS hT (congrArg Sphere.center hST)

/-- If `m.choose 2 ≤ n`, some `n`-point configuration has at least `m.choose 3` unit circles
through three of its points. -/
theorem choose_three_le_maxUnitCircleCount {m n : ℕ} (h : m.choose 2 ≤ n) :
    m.choose 3 ≤ maxUnitCircleCount n := by
  obtain ⟨P, hP, hc⟩ := exists_card_eq_choose_two_choose_three_le m
  obtain ⟨Q, hPQ, hQ⟩ := Infinite.exists_superset_card_eq P n (hP ▸ h)
  exact hc.trans ((unitCircleCount_mono hPQ).trans
    (le_csSup (bddAbove_possibleUnitCircleCounts n) ⟨Q, hQ, rfl⟩))

/-! ### The asymptotic lower bound `maxUnitCircleCount n ≫ n ^ (3/2)` -/

theorem succ_pow_three_le_choose_three {m : ℕ} (hm : 5 ≤ m) :
    (m + 1) ^ 3 ≤ 48 * m.choose 3 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hm
  have h := Nat.descFactorial_eq_factorial_mul_choose (k + 5) 3
  simp only [Nat.descFactorial, Nat.factorial, Nat.succ_eq_add_one] at h
  norm_num at h
  nlinarith

/-- **Elekes' bound, explicit form.** For `n ≥ 25` some `n`-point configuration in the plane has
at least `n ^ (3/2) / 48` distinct unit circles each containing at least three of its points. -/
theorem rpow_le_maxUnitCircleCount {n : ℕ} (hn : 25 ≤ n) :
    (n : ℝ) ^ ((3 : ℝ) / 2) ≤ 48 * maxUnitCircleCount n := by
  set m := Nat.sqrt n with hm
  have hm5 : 5 ≤ m := Nat.le_sqrt.2 (by omega)
  have h2 : m.choose 2 ≤ n := (Nat.choose_le_pow m 2).trans (Nat.sqrt_le' n)
  have hlt : (n : ℝ) ≤ ((m : ℝ) + 1) ^ 2 := by exact_mod_cast (Nat.lt_succ_sqrt' n).le
  have hsqrt : √(n : ℝ) ≤ m + 1 := by
    simpa [Real.sqrt_sq (by positivity : (0 : ℝ) ≤ m + 1)] using Real.sqrt_le_sqrt hlt
  have hpow : (n : ℝ) ^ ((3 : ℝ) / 2) = √(n : ℝ) ^ 3 := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _)]
    norm_num
  calc (n : ℝ) ^ ((3 : ℝ) / 2) = √(n : ℝ) ^ 3 := hpow
    _ ≤ ((m : ℝ) + 1) ^ 3 := pow_le_pow_left₀ (Real.sqrt_nonneg _) hsqrt 3
    _ ≤ 48 * (m.choose 3 : ℝ) := by exact_mod_cast succ_pow_three_le_choose_three hm5
    _ ≤ 48 * maxUnitCircleCount n := by
      gcongr
      exact_mod_cast choose_three_le_maxUnitCircleCount h2

/-- **Erdős Problem 104, lower bound (Elekes 1984).** The maximum number of distinct unit circles
containing at least three points of an `n`-point planar set is `≫ n ^ (3/2)`. -/
theorem erdos_104_lower_bound :
    (fun n : ℕ => (n : ℝ) ^ ((3 : ℝ) / 2)) =O[atTop]
      (fun n : ℕ => (maxUnitCircleCount n : ℝ)) :=
  IsBigO.of_bound 48 (eventually_atTop.2 ⟨25, fun n hn => by
    rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity)]
    exact rpow_le_maxUnitCircleCount hn⟩)

end Erdos104
