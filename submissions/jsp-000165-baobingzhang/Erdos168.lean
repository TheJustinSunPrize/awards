import Mathlib

/-!
# Erdős Problem 168: the limit of `F(N)/N` exists

Let `F(N)` be the largest size of a subset of `{1, …, N}` containing no set of the form
`{n, 2n, 3n}`. Erdős asked for the value of `lim F(N)/N` and whether it is irrational; both
questions are still open. Graham, Spencer and Witsenhausen (*On extremal density theorems for
linear forms*, 1977) proved that the limit exists. This file proves that existence result, stated
without proof as `erdos_168.variants.limit_exists` (category "research solved") in Google
DeepMind's formal-conjectures project, `FormalConjectures/ErdosProblems/168.lean`. The
definitions `NonTernary`, `IntervalNonTernarySets`, `F`, the lemmas `F_0`–`F_3` and
`mem_IntervalNonTernarySets_iff` (with their proofs) and the statement of
`erdos_168.variants.limit_exists` are copied verbatim from that project (Apache-2.0); only the
project-specific `@[category …]` attributes are omitted.

## Proof

* `M U` is the largest size of a non-ternary subset of a finite set `U`, and `F N = M [1, N]`
  (`F_eq_M`).
* Write `n = κ(n) τ(n)`, where `κ(n)` is the part of `n` coprime to `6` and
  `τ(n) = 2 ^ v₂(n) * 3 ^ v₃(n)`. As `κ(2n) = κ(3n) = κ(n)`, every triple `{n, 2n, 3n}` lies in a
  single class `{κ = k}`, so `M` is additive when `U` is split by such a class (`M_split`).
  The class `{x ∈ [1, L] : κ x = k}` is `k · {y ∈ [1, L / k] : κ y = 1}`
  (`filter_κ_eq_image`), and `M` is invariant under scaling (`M_image_mul`).
* Going from `[1, m]` to `[1, m + 1]` only changes the class of `m + 1`, hence
  `F(m + 1) - F(m) = G(τ(m + 1)) - G(τ(m + 1) - 1)`, where `G(t)` is the largest size of a
  non-ternary set of `{2,3}`-smooth numbers in `[1, t]` (`F_succ_sub`). So the increment
  `c m = F(m + 1) - F(m)` lies in `[0, 1]` (`F_le_F_succ`, `F_succ_le`) and depends only on
  `v₂(m + 1)` and `v₃(m + 1)`; in particular `c (m + 6 ^ K) = c m` when `2 ^ K ∤ m + 1` and
  `3 ^ K ∤ m + 1` (`c_add`).
* Truncation: `cK K m` equals `c m` if `2 ^ K ∤ m + 1` and `3 ^ K ∤ m + 1`, and `0` otherwise.
  It is `6 ^ K`-periodic (`cK_periodic`), so its Cesàro means converge
  (`tendsto_avg_periodic`). Since `F(N) = ∑_{m < N} c m` and at most `N / 2 ^ K + N / 3 ^ K`
  indices are removed, `|F(N)/N - (∑_{m < N} cK K m)/N| ≤ 2 / 2 ^ K` (`abs_avg_sub_le`).
* Hence `F(N)/N` is a Cauchy sequence, so it converges.

The same decomposition identifies the limit as `(1/3) ∑_d (G(d) - G(d - 1)) / d` over
`{2,3}`-smooth `d`; that series is not formalized here, convergence being obtained from the Cauchy
criterion instead. The value of the limit (`erdos_168.parts.i`) and its irrationality
(`erdos_168.parts.ii`) are not addressed.
-/

open scoped Topology

namespace Erdos168

/-! ## Definitions copied verbatim from formal-conjectures

Source: `FormalConjectures/ErdosProblems/168.lean` (Apache-2.0). -/

/-- Say a finite set of natural numbers is *non ternary* if it contains no
3-term arithmetic progression of the form `n, 2n, 3n`. -/
def NonTernary (S : Finset ℕ) : Prop := ∀ n : ℕ, n ∉ S ∨ 2*n ∉ S ∨ 3*n ∉ S

/--`IntervalNonTernarySets N` is the (fin)set of non ternary subsets of `{1,...,N}`.
The advantage of defining it as below is that some proofs (e.g. that of `F 3 = 2`) become `rfl`. -/
def IntervalNonTernarySets (N : ℕ) : Finset (Finset ℕ) :=
  (Finset.Icc 1 N).powerset.filter
    fun S => ∀ n ∈ Finset.Icc 1 (N / 3 : ℕ), n ∉ S ∨ 2*n ∉ S ∨ 3*n ∉ S

/--`F N` is the size of the largest non ternary subset of `{1,...,N}`. -/
abbrev F (N : ℕ) : ℕ := (IntervalNonTernarySets N).sup Finset.card

lemma F_0 : F 0 = 0 := rfl

lemma F_1 : F 1 = 1 := rfl

lemma F_2 : F 2 = 2 := rfl

lemma F_3 : F 3 = 2 := rfl

/--
Sanity check: elements of `IntervalNonTernarySets N` are precisely non ternary subsets of
`{1,...,N}`
-/
lemma mem_IntervalNonTernarySets_iff (N : ℕ) (S : Finset ℕ) :
    S ∈ IntervalNonTernarySets N ↔ NonTernary S ∧ S ⊆ Finset.Icc 1 N := by
  refine ⟨fun h => ?_, fun h => by simpa [h, IntervalNonTernarySets] using fun _ _ _ => h.1 _⟩
  simp_all [NonTernary, IntervalNonTernarySets, S.subset_iff, Nat.le_div_iff_mul_le, mul_comm,
      or_iff_not_imp_left]
  exact fun n hn₁ hn₂ hn₃ => h.2 n (h.1 hn₁).1 (h.1 hn₃).2 hn₁ hn₂ hn₃

/-! ## Maximal non-ternary subsets of an arbitrary finite set -/

open Classical in
/-- `M U` is the largest size of a non-ternary subset of the finite set `U`. -/
noncomputable def M (U : Finset ℕ) : ℕ := (U.powerset.filter NonTernary).sup Finset.card

theorem NonTernary.mono {S T : Finset ℕ} (h : NonTernary T) (hST : S ⊆ T) : NonTernary S :=
  fun n => (h n).imp (fun h1 h2 => h1 (hST h2))
    (Or.imp (fun h1 h2 => h1 (hST h2)) (fun h1 h2 => h1 (hST h2)))

theorem nonTernary_empty : NonTernary ∅ := fun n => Or.inl (Finset.notMem_empty n)

theorem card_le_M {U S : Finset ℕ} (hS : S ⊆ U) (h : NonTernary S) : S.card ≤ M U := by
  classical
  unfold M
  exact Finset.le_sup (Finset.mem_filter.2 ⟨Finset.mem_powerset.2 hS, h⟩)

theorem exists_M (U : Finset ℕ) : ∃ S ⊆ U, NonTernary S ∧ S.card = M U := by
  classical
  unfold M
  obtain ⟨S, hS, h⟩ := Finset.exists_mem_eq_sup _
    ⟨∅, Finset.mem_filter.2 ⟨Finset.empty_mem_powerset U, nonTernary_empty⟩⟩ Finset.card
  rw [Finset.mem_filter, Finset.mem_powerset] at hS
  exact ⟨S, hS.1, hS.2, h.symm⟩

theorem F_eq_M (N : ℕ) : F N = M (Finset.Icc 1 N) := by
  apply le_antisymm
  · exact Finset.sup_le fun S hS => by
      rw [mem_IntervalNonTernarySets_iff] at hS
      exact card_le_M hS.2 hS.1
  · obtain ⟨S, hS, hN, hc⟩ := exists_M (Finset.Icc 1 N)
    rw [← hc]
    exact Finset.le_sup (f := Finset.card) ((mem_IntervalNonTernarySets_iff N S).2 ⟨hN, hS⟩)

/-- If a predicate `Q` is invariant under `n ↦ 2n` and `n ↦ 3n`, no triple `{n, 2n, 3n}` meets
both `Q` and its complement, so the problem splits into two independent problems. -/
theorem M_split (U : Finset ℕ) (Q : ℕ → Prop) [DecidablePred Q]
    (h2 : ∀ n, Q (2 * n) ↔ Q n) (h3 : ∀ n, Q (3 * n) ↔ Q n) :
    M U = M (U.filter Q) + M (U.filter fun n => ¬ Q n) := by
  apply le_antisymm
  · obtain ⟨S, hS, hN, hc⟩ := exists_M U
    rw [← hc, ← Finset.card_filter_add_card_filter_not Q]
    exact add_le_add
      (card_le_M (Finset.filter_subset_filter _ hS) (hN.mono (Finset.filter_subset _ _)))
      (card_le_M (Finset.filter_subset_filter _ hS) (hN.mono (Finset.filter_subset _ _)))
  · obtain ⟨S₁, hS₁, hN₁, hc₁⟩ := exists_M (U.filter Q)
    obtain ⟨S₂, hS₂, hN₂, hc₂⟩ := exists_M (U.filter fun n => ¬ Q n)
    have hdisj : Disjoint S₁ S₂ := by
      rw [Finset.disjoint_left]
      intro x hx1 hx2
      exact (Finset.mem_filter.1 (hS₂ hx2)).2 (Finset.mem_filter.1 (hS₁ hx1)).2
    rw [← hc₁, ← hc₂, ← Finset.card_union_of_disjoint hdisj]
    refine card_le_M (Finset.union_subset (hS₁.trans (Finset.filter_subset _ _))
      (hS₂.trans (Finset.filter_subset _ _))) ?_
    intro n
    by_cases hq : Q n
    · have a : n ∉ S₂ := fun hx => (Finset.mem_filter.1 (hS₂ hx)).2 hq
      have b : 2 * n ∉ S₂ := fun hx => (Finset.mem_filter.1 (hS₂ hx)).2 ((h2 n).2 hq)
      have c : 3 * n ∉ S₂ := fun hx => (Finset.mem_filter.1 (hS₂ hx)).2 ((h3 n).2 hq)
      simp only [Finset.mem_union, a, b, c, or_false]
      exact hN₁ n
    · have a : n ∉ S₁ := fun hx => hq (Finset.mem_filter.1 (hS₁ hx)).2
      have b : 2 * n ∉ S₁ := fun hx => hq ((h2 n).1 (Finset.mem_filter.1 (hS₁ hx)).2)
      have c : 3 * n ∉ S₁ := fun hx => hq ((h3 n).1 (Finset.mem_filter.1 (hS₁ hx)).2)
      simp only [Finset.mem_union, a, b, c, false_or]
      exact hN₂ n

/-- Scaling by a positive integer does not change the answer. -/
theorem M_image_mul (U : Finset ℕ) {k : ℕ} (hk : 0 < k) : M (U.image (k * ·)) = M U := by
  have hinj : Function.Injective (k * ·) := fun a b h => Nat.eq_of_mul_eq_mul_left hk h
  apply le_antisymm
  · obtain ⟨S, hS, hN, hc⟩ := exists_M (U.image (k * ·))
    set S' := U.filter (fun x => k * x ∈ S) with hS'
    have himg : S'.image (k * ·) = S := by
      ext x
      simp only [Finset.mem_image, hS', Finset.mem_filter]
      constructor
      · rintro ⟨y, ⟨-, hy⟩, rfl⟩
        exact hy
      · intro hx
        obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 (hS hx)
        exact ⟨y, ⟨hy, hx⟩, rfl⟩
    rw [← hc, ← himg, Finset.card_image_of_injective _ hinj]
    refine card_le_M (Finset.filter_subset _ _) ?_
    intro n
    rcases hN (k * n) with h | h | h
    · exact Or.inl fun hn => h (Finset.mem_filter.1 hn).2
    · refine Or.inr (Or.inl fun hn => h ?_)
      have := (Finset.mem_filter.1 hn).2
      rwa [mul_left_comm] at this
    · refine Or.inr (Or.inr fun hn => h ?_)
      have := (Finset.mem_filter.1 hn).2
      rwa [mul_left_comm] at this
  · obtain ⟨S, hS, hN, hc⟩ := exists_M U
    rw [← hc, ← Finset.card_image_of_injective _ hinj]
    refine card_le_M (Finset.image_subset_image hS) ?_
    intro n
    by_contra h
    simp only [not_or, not_not, Finset.mem_image] at h
    obtain ⟨⟨a, ha, rfl⟩, ⟨b, hb, hb'⟩, ⟨c, hc', hc''⟩⟩ := h
    have hb2 : b = 2 * a := hinj (show k * b = k * (2 * a) by rw [hb']; ring)
    have hc3 : c = 3 * a := hinj (show k * c = k * (3 * a) by rw [hc'']; ring)
    subst hb2 hc3
    rcases hN a with h | h | h <;> contradiction

theorem M_mono {U V : Finset ℕ} (h : U ⊆ V) : M U ≤ M V := by
  obtain ⟨S, hS, hN, hc⟩ := exists_M U
  exact hc ▸ card_le_M (hS.trans h) hN

/-! ## The part of `n` coprime to `6` and the `{2,3}`-smooth part -/

/-- `κ n` is the largest divisor of `n` coprime to `6` (and `κ 0 = 0`). -/
def κ (n : ℕ) : ℕ := ordCompl[3] (ordCompl[2] n)

/-- `τ n = n / κ n = 2 ^ v₂(n) * 3 ^ v₃(n)` is the `{2,3}`-smooth part of `n`. -/
def τ (n : ℕ) : ℕ := n / κ n

theorem ordCompl_of_not_dvd {p x : ℕ} (h : ¬ p ∣ x) : ordCompl[p] x = x := by
  rw [Nat.factorization_eq_zero_of_not_dvd h, pow_zero, Nat.div_one]

theorem κ_mul (a b : ℕ) : κ (a * b) = κ a * κ b := by
  simp only [κ, Nat.ordCompl_mul]

theorem κ_two : κ 2 = 1 := by
  simp [κ, Nat.Prime.factorization_self Nat.prime_two]

theorem κ_three : κ 3 = 1 := by
  have h : ordCompl[2] 3 = 3 := ordCompl_of_not_dvd (by norm_num)
  simp [κ, h, Nat.Prime.factorization_self Nat.prime_three]

theorem κ_two_mul (n : ℕ) : κ (2 * n) = κ n := by rw [κ_mul, κ_two, one_mul]

theorem κ_three_mul (n : ℕ) : κ (3 * n) = κ n := by rw [κ_mul, κ_three, one_mul]

theorem κ_pos {n : ℕ} (hn : n ≠ 0) : 0 < κ n :=
  Nat.ordCompl_pos 3 (Nat.ordCompl_pos 2 hn).ne'

theorem κ_dvd (n : ℕ) : κ n ∣ n :=
  (Nat.div_dvd_of_dvd (Nat.ordProj_dvd _ 3)).trans (Nat.div_dvd_of_dvd (Nat.ordProj_dvd n 2))

theorem κ_κ (n : ℕ) : κ (κ n) = κ n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [κ]
  have h3 : ¬ 3 ∣ κ n := Nat.not_dvd_ordCompl Nat.prime_three (Nat.ordCompl_pos 2 hn).ne'
  have h2 : ¬ 2 ∣ κ n := fun h => Nat.not_dvd_ordCompl Nat.prime_two hn
    (h.trans (Nat.div_dvd_of_dvd (Nat.ordProj_dvd _ 3)))
  show ordCompl[3] (ordCompl[2] (κ n)) = κ n
  rw [ordCompl_of_not_dvd h2, ordCompl_of_not_dvd h3]

theorem κ_mul_τ (n : ℕ) : κ n * τ n = n := Nat.mul_div_cancel' (κ_dvd n)

theorem τ_pos {n : ℕ} (hn : n ≠ 0) : 0 < τ n := by
  have := κ_mul_τ n
  rcases Nat.eq_zero_or_pos (τ n) with h | h
  · rw [h, mul_zero] at this
    exact absurd this.symm hn
  · exact h

theorem κ_τ {n : ℕ} (hn : n ≠ 0) : κ (τ n) = 1 := by
  have h := congrArg κ (κ_mul_τ n)
  rw [κ_mul, κ_κ] at h
  exact Nat.eq_of_mul_eq_mul_left (κ_pos hn) (h.trans (mul_one _).symm)

theorem τ_eq {n : ℕ} (hn : n ≠ 0) : τ n = 2 ^ n.factorization 2 * 3 ^ n.factorization 3 := by
  have h1 := Nat.ordProj_mul_ordCompl_eq_self n 2
  have h2 := Nat.ordProj_mul_ordCompl_eq_self (ordCompl[2] n) 3
  have h3 : (ordCompl[2] n).factorization 3 = n.factorization 3 := by
    rw [Nat.factorization_ordCompl]
    exact Finsupp.erase_ne (by norm_num)
  have h : n = (2 ^ n.factorization 2 * 3 ^ n.factorization 3) * κ n := by
    unfold κ
    rw [mul_assoc, ← h3, h2, h1]
  exact Nat.div_eq_of_eq_mul_left (κ_pos hn) h

/-- Adding a multiple of `p ^ K` does not change the `p`-adic valuation of `n` if `p ^ K ∤ n`. -/
theorem factorization_add_eq {p K n d : ℕ} (hp : p.Prime) (hn : n ≠ 0) (hK : ¬ p ^ K ∣ n)
    (hd : p ^ K ∣ d) : (n + d).factorization p = n.factorization p := by
  have hnd : n + d ≠ 0 := by omega
  have he : n.factorization p < K := by
    by_contra h
    exact hK ((pow_dvd_pow p (not_lt.1 h)).trans (Nat.ordProj_dvd n p))
  apply le_antisymm
  · by_contra h
    have h1 : p ^ (n.factorization p + 1) ∣ n + d :=
      (hp.pow_dvd_iff_le_factorization hnd).2 (by omega)
    have h2 : p ^ (n.factorization p + 1) ∣ d := (pow_dvd_pow p (by omega)).trans hd
    have h3 : p ^ (n.factorization p + 1) ∣ n := (Nat.dvd_add_left h2).1 h1
    have := (hp.pow_dvd_iff_le_factorization hn).1 h3
    omega
  · exact (hp.pow_dvd_iff_le_factorization hnd).1
      (dvd_add (Nat.ordProj_dvd n p) ((pow_dvd_pow p he.le).trans hd))

theorem τ_add {n K : ℕ} (hn : n ≠ 0) (h2 : ¬ 2 ^ K ∣ n) (h3 : ¬ 3 ^ K ∣ n) :
    τ (n + 6 ^ K) = τ n := by
  have d2 : 2 ^ K ∣ 6 ^ K := pow_dvd_pow_of_dvd (by norm_num) K
  have d3 : 3 ^ K ∣ 6 ^ K := pow_dvd_pow_of_dvd (by norm_num) K
  rw [τ_eq (by positivity), τ_eq hn, factorization_add_eq Nat.prime_two hn h2 d2,
    factorization_add_eq Nat.prime_three hn h3 d3]

theorem τ_pred (m : ℕ) : m / κ (m + 1) = τ (m + 1) - 1 := by
  have hk := κ_pos (Nat.add_one_ne_zero m)
  have ht := τ_pos (Nat.add_one_ne_zero m)
  have h := κ_mul_τ (m + 1)
  obtain ⟨s, hs⟩ : ∃ s, τ (m + 1) = s + 1 := ⟨τ (m + 1) - 1, by omega⟩
  rw [hs] at h ⊢
  apply Nat.div_eq_of_lt_le
  · simp only [Nat.add_sub_cancel]
    nlinarith
  · simp only [Nat.add_sub_cancel]
    nlinarith

/-! ## The fibre decomposition: increments of `F` depend only on the smooth part -/

/-- The fibre `{x ∈ [1, L] : κ x = k}` is `k` times the set of smooth numbers in `[1, L / k]`. -/
theorem filter_κ_eq_image {k : ℕ} (hk0 : 0 < k) (hk : κ k = k) (L : ℕ) :
    (Finset.Icc 1 L).filter (fun x => κ x = k) =
      ((Finset.Icc 1 (L / k)).filter (fun y => κ y = 1)).image (k * ·) := by
  ext x
  simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_image]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    have hx0 : x ≠ 0 := by omega
    have hx := κ_mul_τ x
    rw [h3] at hx
    refine ⟨τ x, ⟨⟨τ_pos hx0, ?_⟩, κ_τ hx0⟩, hx⟩
    rw [Nat.le_div_iff_mul_le hk0, mul_comm, hx]
    exact h2
  · rintro ⟨y, ⟨⟨h1, h2⟩, h3⟩, rfl⟩
    refine ⟨⟨Nat.mul_pos hk0 h1, ?_⟩, ?_⟩
    · rw [mul_comm]
      exact (Nat.le_div_iff_mul_le hk0).1 h2
    · rw [κ_mul, hk, h3, mul_one]

/-- `G t` is the largest size of a non-ternary set of `{2,3}`-smooth numbers in `[1, t]`. -/
noncomputable def G (t : ℕ) : ℕ := M ((Finset.Icc 1 t).filter fun y => κ y = 1)

/-- The key identity: `F (m + 1) - F m = G (τ (m + 1)) - G (τ (m + 1) - 1)`. -/
theorem F_succ_sub (m : ℕ) :
    (F (m + 1) : ℝ) - F m = G (τ (m + 1)) - G (τ (m + 1) - 1) := by
  have hk0 : 0 < κ (m + 1) := κ_pos (Nat.add_one_ne_zero m)
  have hkk : κ (κ (m + 1)) = κ (m + 1) := κ_κ _
  have hQ2 : ∀ n, κ (2 * n) = κ (m + 1) ↔ κ n = κ (m + 1) := fun n => by rw [κ_two_mul]
  have hQ3 : ∀ n, κ (3 * n) = κ (m + 1) ↔ κ n = κ (m + 1) := fun n => by rw [κ_three_mul]
  have hrest : (Finset.Icc 1 (m + 1)).filter (fun x => ¬ κ x = κ (m + 1)) =
      (Finset.Icc 1 m).filter (fun x => ¬ κ x = κ (m + 1)) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      refine ⟨⟨h1, ?_⟩, h3⟩
      by_contra h4
      exact h3 (by rw [show x = m + 1 by omega])
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨⟨h1, by omega⟩, h3⟩
  have e1 := M_split (Finset.Icc 1 (m + 1)) (fun x => κ x = κ (m + 1)) hQ2 hQ3
  have e0 := M_split (Finset.Icc 1 m) (fun x => κ x = κ (m + 1)) hQ2 hQ3
  rw [hrest, filter_κ_eq_image hk0 hkk, M_image_mul _ hk0] at e1
  rw [filter_κ_eq_image hk0 hkk, M_image_mul _ hk0, τ_pred] at e0
  rw [F_eq_M, F_eq_M, e1, e0]
  unfold G τ
  push_cast
  ring

/-- The increments of `F`. -/
noncomputable def c (m : ℕ) : ℝ := (F (m + 1) : ℝ) - F m

theorem c_add {K m : ℕ} (h2 : ¬ 2 ^ K ∣ m + 1) (h3 : ¬ 3 ^ K ∣ m + 1) :
    c (m + 6 ^ K) = c m := by
  unfold c
  rw [F_succ_sub, F_succ_sub, show m + 6 ^ K + 1 = m + 1 + 6 ^ K by ring,
    τ_add (Nat.add_one_ne_zero m) h2 h3]

theorem F_le_F_succ (m : ℕ) : F m ≤ F (m + 1) := by
  rw [F_eq_M, F_eq_M]
  exact M_mono (Finset.Icc_subset_Icc_right (Nat.le_succ m))

theorem F_succ_le (m : ℕ) : F (m + 1) ≤ F m + 1 := by
  rw [F_eq_M, F_eq_M]
  obtain ⟨S, hS, hN, hc⟩ := exists_M (Finset.Icc 1 (m + 1))
  have h1 : S.erase (m + 1) ⊆ Finset.Icc 1 m := by
    intro x hx
    rw [Finset.mem_erase] at hx
    have := hS hx.2
    simp only [Finset.mem_Icc] at this ⊢
    omega
  have h2 := card_le_M h1 (hN.mono (Finset.erase_subset _ _))
  have h3 := Finset.pred_card_le_card_erase (s := S) (a := m + 1)
  omega

theorem abs_c_le (m : ℕ) : |c m| ≤ 1 := by
  unfold c
  have h1 : (F m : ℝ) ≤ F (m + 1) := by exact_mod_cast F_le_F_succ m
  have h2 : (F (m + 1) : ℝ) ≤ F m + 1 := by exact_mod_cast F_succ_le m
  rw [abs_le]
  constructor <;> linarith

theorem F_eq_sum (N : ℕ) : (F N : ℝ) = ∑ m ∈ Finset.range N, c m := by
  unfold c
  rw [Finset.sum_range_sub (fun m => (F m : ℝ)), F_0, Nat.cast_zero, sub_zero]

/-! ## Cesàro means of periodic sequences -/

theorem sum_range_periodic (g : ℕ → ℝ) (P : ℕ) (hg : ∀ m, g (m + P) = g m) (q r : ℕ) :
    ∑ m ∈ Finset.range (P * q + r), g m =
      q * ∑ m ∈ Finset.range P, g m + ∑ m ∈ Finset.range r, g m := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [show P * (q + 1) + r = P + (P * q + r) by ring, Finset.sum_range_add]
    have h : ∀ x, g (P + x) = g x := fun x => by rw [add_comm]; exact hg x
    simp only [h, ih]
    push_cast
    ring

/-- The Cesàro means of a periodic sequence converge. -/
theorem tendsto_avg_periodic (g : ℕ → ℝ) (P : ℕ) (hP : 0 < P) (hg : ∀ m, g (m + P) = g m) :
    ∃ L, Filter.Tendsto (fun N : ℕ => (∑ m ∈ Finset.range N, g m) / N) Filter.atTop (𝓝 L) := by
  set S := ∑ m ∈ Finset.range P, g m with hS
  set B := ∑ m ∈ Finset.range P, |g m| with hB
  have hPr : (0 : ℝ) < P := by exact_mod_cast hP
  refine ⟨S / P, ?_⟩
  have hbound : ∀ N : ℕ, |∑ m ∈ Finset.range N, g m - N * (S / P)| ≤ 2 * B := by
    intro N
    obtain ⟨q, r, hr, rfl⟩ : ∃ q r, r < P ∧ N = P * q + r :=
      ⟨N / P, N % P, Nat.mod_lt _ hP, (Nat.div_add_mod N P).symm⟩
    rw [sum_range_periodic g P hg]
    have hsr : |∑ m ∈ Finset.range r, g m| ≤ B :=
      (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.range_subset_range.2 hr.le) (fun _ _ _ => abs_nonneg _))
    have hSB : |S| ≤ B := Finset.abs_sum_le_sum_abs _ _
    have e : (q : ℝ) * S + ∑ m ∈ Finset.range r, g m - ((P * q + r : ℕ) : ℝ) * (S / P) =
        ∑ m ∈ Finset.range r, g m - ((r : ℝ) / P) * S := by
      push_cast
      field_simp
      ring
    rw [e]
    have hrP : (r : ℝ) / P ≤ 1 := by
      rw [div_le_one hPr]
      exact_mod_cast hr.le
    have hrP0 : 0 ≤ (r : ℝ) / P := by positivity
    calc |∑ m ∈ Finset.range r, g m - (r : ℝ) / P * S|
        ≤ |∑ m ∈ Finset.range r, g m| + |(r : ℝ) / P * S| := abs_sub _ _
      _ ≤ B + B := by
          gcongr
          rw [abs_mul, abs_of_nonneg hrP0]
          nlinarith [abs_nonneg S]
      _ = 2 * B := by ring
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Filter.Eventually.of_forall fun N => norm_nonneg _) ?_
    (tendsto_const_div_atTop_nhds_zero_nat (2 * B))
  filter_upwards [Filter.eventually_gt_atTop 0] with N hN
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  rw [Real.norm_eq_abs, show (∑ m ∈ Finset.range N, g m) / N - S / P =
      (∑ m ∈ Finset.range N, g m - N * (S / P)) / N by field_simp, abs_div, abs_of_pos hN']
  exact div_le_div_of_nonneg_right (hbound N) hN'.le

/-! ## Truncation and the Cauchy argument -/

/-- The increments `c m`, with the indices `m + 1` divisible by `2 ^ K` or `3 ^ K` removed.
This sequence is periodic with period `6 ^ K`. -/
noncomputable def cK (K m : ℕ) : ℝ := if ¬ 2 ^ K ∣ m + 1 ∧ ¬ 3 ^ K ∣ m + 1 then c m else 0

theorem cK_periodic (K m : ℕ) : cK K (m + 6 ^ K) = cK K m := by
  have d2 : 2 ^ K ∣ 6 ^ K := pow_dvd_pow_of_dvd (by norm_num) K
  have d3 : 3 ^ K ∣ 6 ^ K := pow_dvd_pow_of_dvd (by norm_num) K
  have e : m + 6 ^ K + 1 = m + 1 + 6 ^ K := by ring
  have e2 : 2 ^ K ∣ m + 6 ^ K + 1 ↔ 2 ^ K ∣ m + 1 := by rw [e]; exact Nat.dvd_add_left d2
  have e3 : 3 ^ K ∣ m + 6 ^ K + 1 ↔ 3 ^ K ∣ m + 1 := by rw [e]; exact Nat.dvd_add_left d3
  unfold cK
  simp only [e2, e3]
  split_ifs with h
  · exact c_add h.1 h.2
  · rfl

theorem abs_c_sub_cK (K m : ℕ) :
    |c m - cK K m| ≤ (if 2 ^ K ∣ m + 1 then 1 else 0) + (if 3 ^ K ∣ m + 1 then 1 else 0) := by
  have := abs_c_le m
  unfold cK
  by_cases h2 : 2 ^ K ∣ m + 1 <;> by_cases h3 : 3 ^ K ∣ m + 1 <;> simp [h2, h3] <;> linarith

theorem sum_ite_dvd_le (p N : ℕ) :
    ∑ m ∈ Finset.range N, (if p ∣ m + 1 then (1 : ℝ) else 0) ≤ (N : ℝ) / p := by
  rw [Finset.sum_boole, Nat.card_multiples]
  exact Nat.cast_div_le

theorem abs_avg_sub_le (K N : ℕ) :
    |(F N : ℝ) / N - (∑ m ∈ Finset.range N, cK K m) / N| ≤ 2 / 2 ^ K := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp only [Nat.cast_zero, div_zero, sub_zero, abs_zero]
    positivity
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  rw [F_eq_sum, ← sub_div, abs_div, abs_of_pos hN', div_le_iff₀ hN', ← Finset.sum_sub_distrib]
  have h23 : (N : ℝ) / 3 ^ K ≤ N / 2 ^ K :=
    div_le_div_of_nonneg_left (Nat.cast_nonneg _) (by positivity)
      (pow_le_pow_left₀ (by norm_num) (by norm_num) K)
  calc |∑ m ∈ Finset.range N, (c m - cK K m)|
      ≤ ∑ m ∈ Finset.range N, |c m - cK K m| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ m ∈ Finset.range N,
          ((if 2 ^ K ∣ m + 1 then (1 : ℝ) else 0) + (if 3 ^ K ∣ m + 1 then 1 else 0)) :=
        Finset.sum_le_sum fun m _ => abs_c_sub_cK K m
    _ = ∑ m ∈ Finset.range N, (if 2 ^ K ∣ m + 1 then (1 : ℝ) else 0) +
          ∑ m ∈ Finset.range N, (if 3 ^ K ∣ m + 1 then (1 : ℝ) else 0) :=
        Finset.sum_add_distrib
    _ ≤ (N : ℝ) / (2 ^ K : ℕ) + (N : ℝ) / (3 ^ K : ℕ) :=
        add_le_add (sum_ite_dvd_le _ _) (sum_ite_dvd_le _ _)
    _ ≤ 2 / 2 ^ K * N := by
        push_cast
        rw [div_mul_eq_mul_div]
        linarith [show (N : ℝ) / 2 ^ K + N / 2 ^ K = 2 * N / 2 ^ K by ring]

/-- The limit $F(N)/N$ as $N \to \infty$ exists. (proved by Graham, Spencer, and Witsenhausen) -/
theorem erdos_168.variants.limit_exists :
    ∃ x, Filter.Tendsto (fun N => (F N / N : ℝ)) Filter.atTop (𝓝 x) := by
  apply cauchySeq_tendsto_of_complete
  rw [Metric.cauchySeq_iff']
  intro ε hε
  obtain ⟨K, hK⟩ : ∃ K : ℕ, 2 / 2 ^ K < ε / 4 := by
    obtain ⟨K, hK⟩ := exists_pow_lt_of_lt_one (show 0 < ε / 8 by positivity)
      (show (1 / 2 : ℝ) < 1 by norm_num)
    refine ⟨K, ?_⟩
    rw [one_div_pow] at hK
    calc 2 / 2 ^ K = 2 * (1 / 2 ^ K) := by ring
      _ < 2 * (ε / 8) := by gcongr
      _ = ε / 4 := by ring
  obtain ⟨L, hL⟩ := tendsto_avg_periodic (cK K) (6 ^ K) (by positivity) (cK_periodic K)
  obtain ⟨N₀, hN₀⟩ := Metric.cauchySeq_iff'.1 hL.cauchySeq (ε / 2) (by positivity)
  refine ⟨N₀, fun n hn => ?_⟩
  have h1 := abs_avg_sub_le K n
  have h2 := abs_avg_sub_le K N₀
  have h3 := hN₀ n hn
  simp only [Real.dist_eq] at h3 ⊢
  rw [abs_le] at h1 h2
  rw [abs_lt] at h3 ⊢
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

end Erdos168
