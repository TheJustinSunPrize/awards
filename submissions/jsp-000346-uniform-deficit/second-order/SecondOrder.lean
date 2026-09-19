/-
Copyright (c) 2026 green3sf. All rights reserved.
Released under the MIT license as described in LICENSE.
Developed with GPT/Codex assistance. See PRIOR_ART.md for scope and attribution.
-/

import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Sqrt
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Order.Monotone.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Algebra.Order.Archimedean.Basic

open Finset
namespace SecondOrder

def DistinctBlocks (a : ℕ → ℕ) : Prop :=
  ∀ u v u' v', u ≤ v → u' ≤ v' →
    (∏ i ∈ Icc u v, a i) = (∏ i ∈ Icc u' v', a i) → u=u' ∧ v=v'

noncomputable def deficit (a : ℕ → ℕ) (N : ℕ) : ℕ := by
  classical
  exact ((Icc 1 N).filter (fun x => x ∉ Set.range a)).card

theorem pair_product (a : ℕ → ℕ) (i : ℕ) :
    (∏ j ∈ Icc i (i+1), a j) = a i*a (i+1) := by
  rw [prod_Icc_succ_top (by omega : i≤i+1)]
  simp

theorem triple_product (a : ℕ → ℕ) (i : ℕ) :
    (∏ j ∈ Icc i (i+2), a j) = a i*a (i+1)*a (i+2) := by
  rw [show i+2=(i+1)+1 by omega,prod_Icc_succ_top (by omega : i≤(i+1)+1),pair_product]

theorem two_le (a : ℕ → ℕ) (hd : DistinctBlocks a) (i : ℕ) : 2≤a i := by
  by_contra h
  have h01 : a i=0 ∨ a i=1 := by omega
  rcases h01 with h0 | h1
  · have heq : (∏ j ∈ Icc i (i+1), a j) = ∏ j ∈ Icc i i, a j := by
      simp [pair_product,h0]
    have := hd i (i+1) i i (by omega) (by omega) heq
    omega
  · have heq : (∏ j ∈ Icc i (i+1), a j) = ∏ j ∈ Icc (i+1) (i+1), a j := by
      simp [pair_product,h1]
    have := hd i (i+1) (i+1) (i+1) (by omega) (by omega) heq
    omega

/-- The number of sequence terms at most N, specified by its first crossing index. -/
def cut (a : ℕ → ℕ) (ha : StrictMono a) (N : ℕ) : ℕ :=
  Nat.find (show ∃ i, N<a i from ⟨N+1,by have : N+1 ≤ a (N+1) := ha.id_le (N+1); omega⟩)

theorem cut_spec (a : ℕ → ℕ) (ha : StrictMono a) (N : ℕ) : N<a (cut a ha N) := by
  unfold cut
  exact Nat.find_spec (p := fun i => N<a i) _

theorem le_iff_lt_cut (a : ℕ → ℕ) (ha : StrictMono a) (N i : ℕ) :
    a i ≤ N ↔ i < cut a ha N := by
  constructor
  · intro h
    by_contra hi
    have := ha.monotone (show cut a ha N ≤ i by omega)
    have := cut_spec a ha N
    omega
  · intro hi
    have h := Nat.find_min (show ∃ i, N<a i from ⟨N+1,by have : N+1 ≤ a (N+1) := ha.id_le (N+1); omega⟩) hi
    omega

theorem deficit_add_cut (a : ℕ → ℕ) (ha : StrictMono a) (hp : ∀ i, 0<a i) (N : ℕ) :
    deficit a N + cut a ha N = N := by
  classical
  let S := (Icc 1 N).filter (fun x => x ∈ Set.range a)
  have heq : (range (cut a ha N)).image a = S := by
    ext x
    simp only [mem_image,mem_range,mem_filter,mem_Icc,Set.mem_range,S]
    constructor
    · rintro ⟨i,hi,rfl⟩
      exact ⟨⟨hp i,(le_iff_lt_cut a ha N i).mpr hi⟩,i,rfl⟩
    · rintro ⟨⟨_,hx⟩,i,rfl⟩
      exact ⟨i,(le_iff_lt_cut a ha N i).mp hx,rfl⟩
  have hc : S.card = cut a ha N := by
    rw [←heq,card_image_of_injective _ ha.injective,card_range]
  have h := card_filter_add_card_filter_not (s := Icc 1 N) (p := fun x => x ∈ Set.range a)
  change S.card + deficit a N = (Icc 1 N).card at h
  simp only [Nat.card_Icc] at h
  omega

/-- Full block uniqueness gives disjoint two-term and three-term omission witnesses. -/
theorem finite_second_order (a : ℕ → ℕ) (ha : StrictMono a) (hd : DistinctBlocks a)
    (N m r t : ℕ) (hm : m*m≤N) (hr : r*r*r≤N)
    (ht : m<(t+1)*(t+1)) :
    m+r ≤ deficit a N + deficit a r + 2*t+3 := by
  classical
  have hp (i : ℕ) : 0<a i := by have := two_le a hd i; omega
  let L := (Icc 1 m).filter (fun x => x ∉ Set.range a)
  let P := Ico (cut a ha t) (cut a ha m-1)
  let T := Ico (cut a ha t) (cut a ha r-2)
  let f (i : ℕ) := a i*a (i+1)
  let g (i : ℕ) := a i*a (i+1)*a (i+2)
  have hf_bounds (i : ℕ) (hi : i∈P) : m<f i ∧ f i≤N := by
    obtain ⟨hi1,hi2⟩ := mem_Ico.mp hi
    have hlow : t<a i := by
      have := (le_iff_lt_cut a ha t i).not
      omega
    have htop : a (i+1)≤m := (le_iff_lt_cut a ha m (i+1)).mpr (by omega)
    have hmono := ha (show i<i+1 by omega)
    have hlo := Nat.mul_le_mul (show t+1≤a i by omega) (show t+1≤a (i+1) by omega)
    have hhi := Nat.mul_le_mul (show a i≤m by omega) htop
    exact ⟨by dsimp [f]; omega,by dsimp [f]; omega⟩
  have hg_bounds (i : ℕ) (hi : i∈T) : m<g i ∧ g i≤N := by
    obtain ⟨hi1,hi2⟩ := mem_Ico.mp hi
    have hlow : t<a i := by
      have := (le_iff_lt_cut a ha t i).not
      omega
    have htop : a (i+2)≤r := (le_iff_lt_cut a ha r (i+2)).mpr (by omega)
    have h01 := ha (show i<i+1 by omega)
    have h12 := ha (show i+1<i+2 by omega)
    have hlo := Nat.mul_le_mul (show t+1≤a i by omega) (show t+1≤a (i+1) by omega)
    have hlo2 := Nat.le_mul_of_pos_right (a i*a (i+1)) (hp (i+2))
    have hhi := Nat.mul_le_mul (Nat.mul_le_mul (show a i≤r by omega) (show a (i+1)≤r by omega)) htop
    exact ⟨by dsimp [g]; omega,by dsimp [g]; omega⟩
  have hf_missing (i : ℕ) : f i ∉ Set.range a := by
    rintro ⟨j,hj⟩
    have heq : (∏ k ∈ Icc i (i+1), a k) = ∏ k ∈ Icc j j, a k := by
      simpa [pair_product] using hj.symm
    have := hd i (i+1) j j (by omega) (by omega) heq
    omega
  have hg_missing (i : ℕ) : g i ∉ Set.range a := by
    rintro ⟨j,hj⟩
    have heq : (∏ k ∈ Icc i (i+2), a k) = ∏ k ∈ Icc j j, a k := by
      simpa [triple_product] using hj.symm
    have := hd i (i+2) j j (by omega) (by omega) heq
    omega
  have hf_inj : Function.Injective f := by
    intro i j heq
    exact (hd i (i+1) j (j+1) (by omega) (by omega) (by simpa [pair_product] using heq)).1
  have hg_inj : Function.Injective g := by
    intro i j heq
    exact (hd i (i+2) j (j+2) (by omega) (by omega) (by simpa [triple_product] using heq)).1
  have hfg : Disjoint (P.image f) (T.image g) := by
    apply disjoint_left.mpr
    intro x hx hy
    obtain ⟨i,_,rfl⟩ := mem_image.mp hx
    obtain ⟨j,_,heq⟩ := mem_image.mp hy
    have h := hd i (i+1) j (j+2) (by omega) (by omega)
      (by simpa [pair_product,triple_product] using heq.symm)
    omega
  have hLP : Disjoint L (P.image f) := by
    apply disjoint_left.mpr
    intro x hx hy
    have hxle := (mem_Icc.mp (mem_filter.mp hx).1).2
    obtain ⟨i,hi,rfl⟩ := mem_image.mp hy
    have := (hf_bounds i hi).1
    omega
  have hLT : Disjoint L (T.image g) := by
    apply disjoint_left.mpr
    intro x hx hy
    have hxle := (mem_Icc.mp (mem_filter.mp hx).1).2
    obtain ⟨i,hi,rfl⟩ := mem_image.mp hy
    have := (hg_bounds i hi).1
    omega
  have hsub : L ∪ (P.image f ∪ T.image g) ⊆
      (Icc 1 N).filter (fun x => x ∉ Set.range a) := by
    intro x hx
    rcases mem_union.mp hx with hx | hx
    · have hxle := mem_Icc.mp (mem_filter.mp hx).1
      have hmle := (Nat.le_mul_self m).trans hm
      exact mem_filter.mpr ⟨mem_Icc.mpr ⟨hxle.1,hxle.2.trans hmle⟩,(mem_filter.mp hx).2⟩
    rcases mem_union.mp hx with hx | hx
    · obtain ⟨i,hi,rfl⟩ := mem_image.mp hx
      have hb := hf_bounds i hi
      exact mem_filter.mpr ⟨mem_Icc.mpr ⟨by omega,hb.2⟩,hf_missing i⟩
    · obtain ⟨i,hi,rfl⟩ := mem_image.mp hx
      have hb := hg_bounds i hi
      exact mem_filter.mpr ⟨mem_Icc.mpr ⟨by omega,hb.2⟩,hg_missing i⟩
  have hc := card_le_card hsub
  rw [card_union_of_disjoint (disjoint_union_right.mpr ⟨hLP,hLT⟩),
    card_union_of_disjoint hfg,card_image_of_injective _ hf_inj,
    card_image_of_injective _ hg_inj] at hc
  change deficit a m + (P.card+T.card) ≤ deficit a N at hc
  have hcm := deficit_add_cut a ha hp m
  have hcr := deficit_add_cut a ha hp r
  have hct := deficit_add_cut a ha hp t
  simp only [P,T,Nat.card_Ico] at hc
  omega

/-- Integer cube root, with an explicit finite witness for the search. -/
def cubeRoot (N : ℕ) : ℕ :=
  Nat.find (show ∃ r, N<(r+1)^3 from ⟨N,by nlinarith [sq_nonneg N]⟩)

theorem cubeRoot_upper (N : ℕ) : N<(cubeRoot N+1)^3 := by
  unfold cubeRoot
  exact Nat.find_spec (p := fun r => N<(r+1)^3) _

theorem cubeRoot_lower (N : ℕ) : (cubeRoot N)^3≤N := by
  by_cases h : cubeRoot N=0
  · simp [h]
  have hmin := Nat.find_min (show ∃ r, N<(r+1)^3 from ⟨N,by nlinarith [sq_nonneg N]⟩)
    (show cubeRoot N-1<cubeRoot N by omega)
  change ¬N<(cubeRoot N-1+1)^3 at hmin
  rw [Nat.sub_add_cancel (by omega : 1≤cubeRoot N)] at hmin
  omega

theorem le_cubeRoot {N r : ℕ} (h : r^3≤N) : r≤cubeRoot N := by
  have hu := cubeRoot_upper N
  by_contra hnot
  have hx := Nat.pow_le_pow_left (show cubeRoot N+1≤r by omega) 3
  omega

/-- A finite two-scale inequality, before imposing any density assumption. -/
theorem sqrt_cubert_bound (a : ℕ → ℕ) (ha : StrictMono a) (hd : DistinctBlocks a)
    (N : ℕ) : N.sqrt+cubeRoot N ≤
      deficit a N+deficit a (cubeRoot N)+2*N.sqrt.sqrt+3 := by
  exact finite_second_order a ha hd N N.sqrt (cubeRoot N) N.sqrt.sqrt
    (Nat.sqrt_le N) (by simpa [pow_succ] using cubeRoot_lower N) (Nat.lt_succ_sqrt _)

/-- Natural density one in a fully quantified reciprocal-integer formulation. -/
def DensityOne (a : ℕ → ℕ) : Prop :=
  ∀ k : ℕ, 1≤k → ∃ R : ℕ, ∀ n : ℕ, R≤n → k*deficit a n≤n

/-- A cube-root scale eventually dominates the fourth-root error by any fixed factor. -/
theorem error_absorbed (k N : ℕ) (hk : 1≤k) (hN : (16*k)^12≤N) :
    2*k*(2*N.sqrt.sqrt+3) ≤ cubeRoot N := by
  let t := N.sqrt.sqrt
  have hsmall : (16*k)^3 ≤ t := by
    apply Nat.le_sqrt'.mpr
    apply Nat.le_sqrt'.mpr
    calc
      (((16*k)^3)^2)^2 = (16*k)^12 := by ring
      _ ≤ N := hN
  have htpos : 1≤t := by
    have hbase : 1≤16*k := by omega
    have hpow := Nat.pow_le_pow_left hbase 3
    norm_num at hpow
    omega
  have h4 : t^4≤N := by
    have h1 : t^2 ≤ N.sqrt := Nat.sqrt_le' _
    have h2 := Nat.pow_le_pow_left h1 2
    have h3 := Nat.sqrt_le' N
    nlinarith
  have hpow : (8*k*(t+1))^3 ≤ N := by
    calc
      (8*k*(t+1))^3 ≤ (16*k*t)^3 :=
        Nat.pow_le_pow_left (by nlinarith) 3
      _ = (16*k)^3*t^3 := by ring
      _ ≤ t*t^3 := Nat.mul_le_mul_right _ hsmall
      _ = t^4 := by ring
      _ ≤ N := h4
  have hr := le_cubeRoot hpow
  change 2*k*(2*t+3) ≤ cubeRoot N
  nlinarith

/-- Quantified second-order obstruction with an explicit threshold from a density modulus. -/
theorem second_order_explicit (a : ℕ → ℕ) (ha : StrictMono a) (hd : DistinctBlocks a)
    (k R N : ℕ) (hk : 1≤k)
    (hR : ∀ n, R≤n → (2*k)*deficit a n≤n)
    (hN : max (R^3) ((16*k)^12) ≤ N) :
    k*N.sqrt+(k-1)*cubeRoot N ≤ k*deficit a N := by
  have hr : R≤cubeRoot N := le_cubeRoot ((le_max_left _ _).trans hN)
  have hdef := hR (cubeRoot N) hr
  have herr := error_absorbed k N hk ((le_max_right _ _).trans hN)
  have hbound := sqrt_cubert_bound a ha hd N
  have hmul := Nat.mul_le_mul_left (2*k) hbound
  have hsub : k-1+1=k := by omega
  nlinarith

/-- For a density-one product-distinct sequence, the second-order coefficient is at least one. -/
theorem second_order (a : ℕ → ℕ) (ha : StrictMono a) (hd : DistinctBlocks a)
    (hden : DensityOne a) :
    ∀ k : ℕ, 1≤k → ∃ N₀ : ℕ, ∀ N : ℕ, N₀≤N →
      k*N.sqrt+(k-1)*cubeRoot N ≤ k*deficit a N := by
  intro k hk
  obtain ⟨R,hR⟩ := hden (2*k) (by omega)
  exact ⟨max (R^3) ((16*k)^12),fun N hN => second_order_explicit a ha hd k R N hk hR hN⟩


/-- The reciprocal-integer density formulation is equivalent to the usual vanishing ratio. -/
theorem densityOne_iff_tendsto (a : ℕ → ℕ) : DensityOne a ↔
    Filter.Tendsto (fun n : ℕ => (deficit a n : ℝ)/(n : ℝ)) Filter.atTop (nhds 0) := by
  constructor
  · intro h
    apply tendsto_order.mpr
    constructor
    · intro b hb
      exact Filter.Eventually.of_forall (fun n => hb.trans_le (by positivity))
    · intro b hb
      obtain ⟨j,hj⟩ := exists_nat_one_div_lt hb
      obtain ⟨R,hR⟩ := h (j+1) (by omega)
      apply Filter.eventually_atTop.mpr
      refine ⟨R+1,fun n hn => ?_⟩
      have hnpos : (0 : ℝ)<n := by exact_mod_cast (show 0<n by omega)
      have hjpos : (0 : ℝ)<j+1 := by positivity
      have hbnd : (deficit a n : ℝ)/(n : ℝ) ≤ 1/((j : ℝ)+1) := by
        apply (div_le_div_iff₀ hnpos hjpos).mpr
        have hnat := hR n (by omega)
        nlinarith [show ((j : ℝ)+1)*(deficit a n : ℝ) ≤ (n : ℝ) by exact_mod_cast hnat]
      exact hbnd.trans_lt hj
  · intro h k hk
    have hkpos : (0 : ℝ)<k := by exact_mod_cast (show 0<k by omega)
    have hevent := (tendsto_order.mp h).2 (1/(k : ℝ)) (by positivity)
    obtain ⟨R,hR⟩ := Filter.eventually_atTop.mp hevent
    refine ⟨R+1,fun n hn => ?_⟩
    have hnpos : (0 : ℝ)<n := by exact_mod_cast (show 0<n by omega)
    have hineq := (div_lt_div_iff₀ hnpos hkpos).mp (hR n (by omega))
    have hreal : (k : ℝ)*(deficit a n : ℝ) ≤ (n : ℝ) := by nlinarith
    exact_mod_cast hreal

/-- Natural density one stated directly as the ratio of retained terms. -/
theorem densityOne_of_retained_ratio (a : ℕ → ℕ) (ha : StrictMono a)
    (hp : ∀ i, 0<a i)
    (h : Filter.Tendsto (fun n : ℕ => (cut a ha n : ℝ)/(n : ℝ))
      Filter.atTop (nhds 1)) : DensityOne a := by
  apply (densityOne_iff_tendsto a).mpr
  have hsub : Filter.Tendsto (fun n : ℕ => 1-(cut a ha n : ℝ)/(n : ℝ))
      Filter.atTop (nhds 0) := by
    simpa using (tendsto_const_nhds.sub h : Filter.Tendsto
      (fun n : ℕ => (1 : ℝ)-(cut a ha n : ℝ)/(n : ℝ)) Filter.atTop (nhds (1-1)))
  apply hsub.congr'
  filter_upwards [Filter.eventually_ge_atTop 1] with n hn
  have hn0 : (n : ℝ)≠0 := by exact_mod_cast (show n≠0 by omega)
  have hcount : (deficit a n : ℝ)+(cut a ha n : ℝ)=(n : ℝ) :=
    by exact_mod_cast deficit_add_cut a ha hp n
  field_simp
  nlinarith

/-- Main result under the usual real-valued natural-density-one hypothesis. -/
theorem second_order_of_natural_density (a : ℕ → ℕ) (ha : StrictMono a)
    (hd : DistinctBlocks a)
    (hden : Filter.Tendsto (fun n : ℕ => (cut a ha n : ℝ)/(n : ℝ))
      Filter.atTop (nhds 1)) :
    ∀ k : ℕ, 1≤k → ∃ N₀ : ℕ, ∀ N : ℕ, N₀≤N →
      k*N.sqrt+(k-1)*cubeRoot N ≤ k*deficit a N :=
  second_order a ha hd (densityOne_of_retained_ratio a ha
    (fun i => by have := two_le a hd i; omega) hden)


end SecondOrder
