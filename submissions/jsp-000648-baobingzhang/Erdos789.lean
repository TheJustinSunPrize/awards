import Mathlib

/-!
# Erdős Problem 789: Straus's upper bound `h(n) = O(√n)`

Let `h(n)` be maximal such that every set `A` of `n` integers contains a subset `B` with
`|B| ≥ h(n)` in which equal subset sums only occur for subsets with the same number of elements.
Erdős asked to estimate `h(n)` (open). Straus (1966) proved `h(n) ≪ √n`; this file proves that
bound, stated without proof as `erdos_789.variants.isBigO_sq` (category "research solved") in
Google DeepMind's formal-conjectures project, `FormalConjectures/ErdosProblems/789.lean`.
The definitions `IsSubsetSumSeparatingCard` and `subsetSumThreshold` and the statement of
`erdos_789.variants.isBigO_sq` are copied verbatim from that project (Apache-2.0).

## Proof

Take `A = {1, …, n}` and let `B ⊆ A` with `m = |B|` have the separating property.

* For every finite `s ⊆ ℤ` and `k ≤ |s|`, the `k`-element subsets of `s` have at least
  `k (|s| - k) + 1` distinct sums (`card_image_sum_powersetCard`, induction on the maximum:
  adding a new maximum `a` above `s` keeps all old sums and creates `k` new ones above the old
  maximum `M = ∑ U`, namely `M - u + a` for `u ∈ U`).
* For `1 ≤ k ≤ m` these value sets are pairwise disjoint (separating property) and contained in
  `[1, m n]`, so `∑_{k=1}^{m} (k (m - k) + 1) ≤ m n`. The left side is `(m³ + 5m) / 6`, so
  `m² ≤ 6n` (`sq_card_le_of_separating`).
* Hence every separating cardinality `m` satisfies `m² ≤ 6n`; the set of them contains `0` and is
  bounded, so its supremum `h(n)` is one of them and `h(n)² ≤ 6n`
  (`subsetSumThreshold_sq_le`). Thus `h(n) ≤ 3 √n`.
-/

open Filter

open scoped Asymptotics Finset

namespace Erdos789

/-- Given a non-negative integer $n$, we say $m$ is a separating cardinality of
subset sums if, for any set $A$ of $n$ integers, there is some $B\subseteq A$ of
size $\geq m$ such that subset sums of $B$ can only ever coincide when the
subsets have the same cardinality. -/
def IsSubsetSumSeparatingCard (n m : ℕ) : Prop :=
  ∀ A : Finset ℤ, #A = n → ∃ B : Finset ℤ, B ⊆ A ∧ m ≤ #B ∧
    (∀ᵉ (T ⊆ B) (S ⊆ B), S.Nonempty → T.Nonempty → ∑ a ∈ T, a = ∑ b ∈ S, b → #T = #S)

/-- The subset sum threshold $h(n)$, for each positive $n$, is the maximal separating
cardinality of subset sums for $n$. -/
noncomputable def subsetSumThreshold (n : ℕ): ℕ :=
  sSup { m | IsSubsetSumSeparatingCard n m }

/-- The `k`-element subsets of a finite set `s` of integers have at least `k (|s| - k) + 1`
distinct sums. -/
theorem card_image_sum_powersetCard (s : Finset ℤ) :
    ∀ k ≤ #s, k * (#s - k) + 1 ≤ #((s.powersetCard k).image fun T => ∑ x ∈ T, x) := by
  induction s using Finset.induction_on_max with
  | empty =>
    intro k hk
    simp only [Finset.card_empty, nonpos_iff_eq_zero] at hk
    subst hk
    simp
  | insert a s ha ih =>
    intro k hk
    have has : a ∉ s := fun h => lt_irrefl a (ha a h)
    rw [Finset.card_insert_of_notMem has] at hk ⊢
    rcases (by omega : k = 0 ∨ k = #s + 1 ∨ (1 ≤ k ∧ k ≤ #s)) with hk0 | hk0 | ⟨hk1, hks⟩
    · have : k * (#s + 1 - k) = 0 := by rw [hk0, zero_mul]
      rw [this, zero_add, Nat.one_le_iff_ne_zero, Ne, Finset.card_eq_zero,
        Finset.image_eq_empty, ← Ne, ← Finset.nonempty_iff_ne_empty, Finset.powersetCard_nonempty,
        Finset.card_insert_of_notMem has]
      exact hk
    · have : k * (#s + 1 - k) = 0 := by rw [hk0, Nat.sub_self, mul_zero]
      rw [this, zero_add, Nat.one_le_iff_ne_zero, Ne, Finset.card_eq_zero,
        Finset.image_eq_empty, ← Ne, ← Finset.nonempty_iff_ne_empty, Finset.powersetCard_nonempty,
        Finset.card_insert_of_notMem has]
      exact hk
    set F := (s.powersetCard k).image fun T => ∑ x ∈ T, x with hF
    have hFne : F.Nonempty := (Finset.powersetCard_nonempty.2 hks).image _
    obtain ⟨U, hU, hUM⟩ := Finset.mem_image.1 (F.max'_mem hFne)
    rw [Finset.mem_powersetCard] at hU
    set M := F.max' hFne with hM
    set G := U.image fun u => M - u + a with hG
    have hGcard : #G = k := by
      rw [hG, Finset.card_image_of_injective _ (fun x y h => by simpa using h)]
      exact hU.2
    have hdisj : Disjoint F G := by
      rw [Finset.disjoint_left]
      intro x hx hxG
      obtain ⟨u, hu, rfl⟩ := Finset.mem_image.1 hxG
      have h1 := F.le_max' _ hx
      have h2 := ha u (hU.1 hu)
      rw [← hM] at h1
      linarith
    have hsub : F ∪ G ⊆ ((insert a s).powersetCard k).image fun T => ∑ x ∈ T, x := by
      intro x hx
      rcases Finset.mem_union.1 hx with hx | hx
      · obtain ⟨T, hT, rfl⟩ := Finset.mem_image.1 hx
        exact Finset.mem_image.2
          ⟨T, Finset.powersetCard_mono (Finset.subset_insert a s) hT, rfl⟩
      · obtain ⟨u, hu, rfl⟩ := Finset.mem_image.1 hx
        have haU : a ∉ U.erase u := fun h => has (hU.1 (Finset.mem_of_mem_erase h))
        refine Finset.mem_image.2 ⟨insert a (U.erase u), ?_, ?_⟩
        · rw [Finset.mem_powersetCard, Finset.card_insert_of_notMem haU,
            Finset.card_erase_of_mem hu, hU.2]
          exact ⟨Finset.insert_subset_insert a ((Finset.erase_subset u U).trans hU.1), by omega⟩
        · rw [Finset.sum_insert haU, ← hUM, ← Finset.add_sum_erase U _ hu]
          ring
    calc k * (#s + 1 - k) + 1 = (k * (#s - k) + 1) + k := by
          rw [show #s + 1 - k = (#s - k) + 1 by omega, mul_add, mul_one]
          ring
      _ ≤ #F + #G := by rw [hGcard]; exact Nat.add_le_add_right (ih k hks) k
      _ = #(F ∪ G) := (Finset.card_union_of_disjoint hdisj).symm
      _ ≤ _ := Finset.card_le_card hsub

/-- `6 ∑_{k=1}^{m} (k (m - k) + 1) = m³ + 5m`. -/
theorem six_mul_sum_eq (m : ℕ) :
    6 * ∑ k ∈ Finset.range m, ((k + 1) * (m - (k + 1)) + 1) = m ^ 3 + 5 * m := by
  have hg : ∀ m : ℕ, 2 * ∑ k ∈ Finset.range m, (k + 1) = m * (m + 1) := by
    intro m
    induction m with
    | zero => simp
    | succ m ih => rw [Finset.sum_range_succ, mul_add, ih]; ring
  induction m with
  | zero => simp
  | succ m ih =>
    have hc : ∑ k ∈ Finset.range m, ((k + 1) * (m + 1 - (k + 1)) + 1) =
        ∑ k ∈ Finset.range m, ((k + 1) * (m - (k + 1)) + 1) + ∑ k ∈ Finset.range m, (k + 1) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun k hk => ?_
      rw [Finset.mem_range] at hk
      rw [show m + 1 - (k + 1) = (m - (k + 1)) + 1 by omega, mul_add, mul_one]
      ring
    rw [Finset.sum_range_succ, Nat.sub_self, mul_zero, zero_add, hc]
    have := hg m
    nlinarith [ih, this]

/-- If `B ⊆ {1, …, n}` has the separating property, then `|B|² ≤ 6n`. -/
theorem sq_card_le_of_separating {n : ℕ} {B : Finset ℤ} (hB : B ⊆ Finset.Icc 1 (n : ℤ))
    (hsep : ∀ᵉ (T ⊆ B) (S ⊆ B), S.Nonempty → T.Nonempty → ∑ a ∈ T, a = ∑ b ∈ S, b → #T = #S) :
    #B ^ 2 ≤ 6 * n := by
  set m := #B with hm
  set F : ℕ → Finset ℤ := fun k => (B.powersetCard (k + 1)).image fun T => ∑ x ∈ T, x with hF
  have hdisj : ((Finset.range m : Set ℕ)).PairwiseDisjoint F := by
    intro i _ j _ hij
    rw [Function.onFun, Finset.disjoint_left]
    intro x hxi hxj
    obtain ⟨T, hT, rfl⟩ := Finset.mem_image.1 hxi
    obtain ⟨S, hS, hST⟩ := Finset.mem_image.1 hxj
    rw [Finset.mem_powersetCard] at hT hS
    have := hsep T hT.1 S hS.1 (Finset.card_pos.1 (by omega)) (Finset.card_pos.1 (by omega))
      hST.symm
    omega
  have hsub : (Finset.range m).biUnion F ⊆ Finset.Icc 1 ((m : ℤ) * n) := by
    intro x hx
    obtain ⟨k, hk, hx⟩ := Finset.mem_biUnion.1 hx
    obtain ⟨T, hT, rfl⟩ := Finset.mem_image.1 hx
    rw [Finset.mem_powersetCard] at hT
    rw [Finset.mem_range] at hk
    have h1 : #T • (1 : ℤ) ≤ ∑ x ∈ T, x :=
      Finset.card_nsmul_le_sum _ _ _ fun x hx => (Finset.mem_Icc.1 (hB (hT.1 hx))).1
    have h2 : ∑ x ∈ T, x ≤ #T • (n : ℤ) :=
      Finset.sum_le_card_nsmul _ _ _ fun x hx => (Finset.mem_Icc.1 (hB (hT.1 hx))).2
    rw [nsmul_eq_mul, hT.2] at h1 h2
    push_cast at h1 h2
    have h3 : ((k : ℤ) + 1) * n ≤ m * n :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hk) (by positivity)
    rw [Finset.mem_Icc]
    constructor <;> linarith
  have hcount : ∑ k ∈ Finset.range m, ((k + 1) * (m - (k + 1)) + 1) ≤ m * n := by
    calc _ ≤ ∑ k ∈ Finset.range m, #(F k) := Finset.sum_le_sum fun k hk =>
            card_image_sum_powersetCard B (k + 1) (by rw [Finset.mem_range] at hk; omega)
      _ = #((Finset.range m).biUnion F) := (Finset.card_biUnion hdisj).symm
      _ ≤ #(Finset.Icc 1 ((m : ℤ) * n)) := Finset.card_le_card hsub
      _ = m * n := by rw [Int.card_Icc, add_sub_cancel_right, ← Nat.cast_mul, Int.toNat_natCast]
  have h6 := six_mul_sum_eq m
  rcases Nat.eq_zero_or_pos m with h0 | h0
  · rw [h0]; simp
  · have h7 : m * (m ^ 2 + 5) ≤ m * (6 * n) := by nlinarith
    have := Nat.le_of_mul_le_mul_left h7 h0
    omega

/-- Every separating cardinality `m` for `n` satisfies `m² ≤ 6n` (test set `A = {1, …, n}`),
and hence so does `h(n)`. -/
theorem subsetSumThreshold_sq_le (n : ℕ) : subsetSumThreshold n ^ 2 ≤ 6 * n := by
  have key : ∀ m, IsSubsetSumSeparatingCard n m → m ^ 2 ≤ 6 * n := by
    intro m hm
    obtain ⟨B, hBA, hmB, hsep⟩ := hm (Finset.Icc 1 (n : ℤ)) (by simp)
    exact (Nat.pow_le_pow_left hmB 2).trans (sq_card_le_of_separating hBA hsep)
  have hne : {m | IsSubsetSumSeparatingCard n m}.Nonempty := by
    refine ⟨0, fun A _ => ⟨∅, Finset.empty_subset A, le_rfl, ?_⟩⟩
    intro T _ S hS hSne _ _
    rw [Finset.subset_empty.1 hS] at hSne
    exact absurd hSne Finset.not_nonempty_empty
  have hbdd : BddAbove {m | IsSubsetSumSeparatingCard n m} :=
    ⟨6 * n, fun m hm => (Nat.le_self_pow two_ne_zero m).trans (key m hm)⟩
  exact key _ (Nat.sSup_mem hne hbdd)

/-- Straus [Str66] proved that $h(n) \ll \sqrt{n}$. -/
theorem erdos_789.variants.isBigO_sq :
    (fun n ↦ (subsetSumThreshold n : ℝ)) =O[atTop] fun n ↦ √n := by
  refine Asymptotics.IsBigO.of_bound 3 (Eventually.of_forall fun n => ?_)
  rw [Real.norm_of_nonneg (Nat.cast_nonneg _), Real.norm_of_nonneg (Real.sqrt_nonneg _)]
  have h : (subsetSumThreshold n : ℝ) ^ 2 ≤ 9 * n := by
    exact_mod_cast (subsetSumThreshold_sq_le n).trans (by omega)
  calc (subsetSumThreshold n : ℝ) ≤ √(9 * n) :=
        (Real.le_sqrt (by positivity) (by positivity)).2 h
    _ = 3 * √n := by
        rw [Real.sqrt_mul (by norm_num), show (9 : ℝ) = 3 ^ 2 by norm_num,
          Real.sqrt_sq (by norm_num)]

end Erdos789
