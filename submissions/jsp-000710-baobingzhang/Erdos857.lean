import Mathlib

/-!
# Erdős Problem 857: the Naslund–Sawin bound for `3`-sunflowers

Erdős Problem 857 ([Er70], https://www.erdosproblems.com/857, the "weak sunflower problem") reads:

> Let `m = m(n, k)` be minimal such that in any collection of sets
> `A₁, …, Aₘ ⊆ {1, …, n}` there must exist a sunflower of size `k`, that is, `k` sets which
> pairwise have the same intersection. Estimate `m(n, k)`, or even better, give an asymptotic
> formula.

The problem is open. The progress result recorded on the problem page is due to Naslund and
Sawin [NaSa17, Theorem 3]: every `3`-sunflower-free family of subsets of `{1, …, n}` has at most
`3 (n + 1) ∑_{k ≤ n/3} C(n, k)` members, hence `m(n, 3) ≤ (3 / 2^(2/3))^((1 + o(1)) n)`.
This file proves both statements.

## Main results

* `Erdos857.ncard_le_of_sunflowerFree`: if no `S ⊆ F` with `S.ncard = 3` is a sunflower, then
  `F.ncard ≤ 3 * (n + 1) * ∑ k ∈ range (n / 3 + 1), n.choose k` ([NaSa17, Theorem 3]).
* `Erdos857.erdos_857.variants.naslund_sawin`:
  `m n 3 ≤ 3 * (n + 1) * ∑ k ∈ range (n / 3 + 1), n.choose k + 1`.
* `Erdos857.erdos_857.variants.naslund_sawin_rpow`:
  `(m n 3 : ℝ) ≤ 3 * (n + 1) * (3 / 2 ^ (2 / 3 : ℝ)) ^ n + 1`.
* `Erdos857.erdos_857.variants.naslund_sawin_asymp`: there is `o : ℕ → ℝ` with `o n → 0` and
  `(m n 3 : ℝ) ≤ (3 / 2 ^ (2 / 3 : ℝ)) ^ ((1 + o n) * n)` for all `n ≥ 1`, the bound stated on the
  problem page. (Here `o n = log (7 n) / (n log (3 / 2^(2/3)))`.) The case `n = 0` has to be
  excluded: `m 0 3 = 2` (`m_zero_three`) while the right-hand side is `1`.
* `Erdos857.card_le_of_diagonal`: Tao's slice-rank lemma for diagonal tensors, in the form used.

Only the case `k = 3` of the problem is addressed; the problem for general `k`, and the
asymptotics of `m(n, 3)`, remain open.

## Definitions and faithfulness

`IsSunflowerWithKernel`, `IsSunflower` (from
`FormalConjecturesForMathlib/Combinatorics/SetFamily/Sunflower.lean`) and `Erdos857.m` (from
`FormalConjectures/ErdosProblems/857.lean`) are copied verbatim from Google DeepMind's
formal-conjectures project (Apache-2.0). There, `m n k` is the `sInf` of the thresholds `t` such
that every `F : Set (Set (Fin n))` with `t ≤ F.ncard` has a subfamily `S ⊆ F` with `S.ncard = k`
which is a sunflower (all distinct pairs of members of `S` have the same intersection). Since
`Set (Set (Fin n))` is finite, `ncard` is the true cardinality, and `S.ncard = 3` means that `S`
consists of three distinct sets. formal-conjectures states only the open problem; the names
`erdos_857.variants.*` follow its naming convention.

`sInf ∅ = 0` in `ℕ`, so an upper bound on `m` would be empty if no threshold existed.
`m_three_le_iff` shows that the defining set is nonempty and that `m n 3 ≤ t` holds exactly when
every family of at least `t` subsets of `Fin n` contains a `3`-sunflower. The bound is also
proved directly for families (`ncard_le_of_sunflowerFree`, `exists_sunflower_of_lt_ncard`),
without reference to `m`.

## Proof (following [NaSa17, §2] and [Tao16])

* **Layers.** Split `F` by the size `l` of its members (`n + 1` layers). If `x, y, z` lie in one
  layer and no element belongs to exactly two of them, then `x = y = z`: three distinct such sets
  would be a sunflower with kernel `x ∩ y ∩ z`, and if, say, `x = y ≠ z`, then `x ⊄ z` because
  `|x| = |z|` (`eq_of_T_ne_zero`).
* **The tensor.** `T(x, y, z) = ∏ᵢ (2 - xᵢ - yᵢ - zᵢ)` over `ℚ` vanishes exactly when some
  element lies in exactly two of `x, y, z`, and `T(x, x, x) = ∏ᵢ (2 - 3xᵢ) ≠ 0`. So `T` restricted
  to a layer is diagonal with nonzero diagonal.
* **Slice-rank lower bound** (`card_le_of_diagonal`, [Tao16, Lemma 1], [NaSa17, Lemma 6]).
  Suppose that on `A³`
  `T(x, y, z) = ∑_{a ∈ s₁} f₁ a x g₁ a y z + ∑_{b ∈ s₂} f₂ b y g₂ b x z +
  ∑_{c ∈ s₃} f₃ c z g₃ c x y`. Then `|A| ≤ |s₁| + |s₂| + |s₃|`. The functions `h : A → K`
  orthogonal to all `f₁ a` form a subspace of dimension `≥ |A| - |s₁|`, which contains a vector
  `h` with at least that many nonzero coordinates (`exists_mem_finrank_le_card_support`, by a
  maximal-support argument over the infinite field `ℚ`). Contracting `T` with `h` in the first
  variable gives the diagonal matrix `diag(h(y) T(y, y, y))`. All of its rows lie in a space
  spanned by `|s₂| + |s₃|` vectors, and its nonzero rows are multiples of distinct unit vectors,
  so `h` has at most `|s₂| + |s₃|` nonzero coordinates.
* **Slice-rank upper bound** (`T_expand`, `T_decomp`). Expanding the product, `T` is a sum of
  products `x^I y^J z^K` of multilinear monomials with `I, J, K` disjoint, so one of them has
  degree `≤ n/3`. Grouping each term by such a monomial writes `T` as above with
  `s₁ = s₂ = s₃ = {I : |I| ≤ n/3}`, of size `∑_{k ≤ n/3} C(n, k)` (`card_small`).
* **Conclusion.** Each layer has at most `3 ∑_{k ≤ n/3} C(n, k)` members; sum over the `n + 1`
  layers. For the asymptotic form, `C(n, k) ≤ C(n, k) 3^(-k) (2/3)^(n-k) (3 / 2^(2/3))^n` for
  `k ≤ n/3`, and the binomial theorem gives `∑_{k ≤ n/3} C(n, k) ≤ (3 / 2^(2/3))^n`
  (`sum_choose_le_rpow`).

## References

* [Er70] Erdős, P., _Some extremal problems in combinatorial number theory_. Mathematical Essays
  Dedicated to A. J. Macintyre (1970), 123–133.
* [NaSa17] Naslund, E. and Sawin, W., _Upper bounds for sunflower-free sets_. Forum Math. Sigma 5
  (2017), e15. arXiv:1606.09575.
* [Tao16] Tao, T., _A symmetric formulation of the Croot–Lev–Pach–Ellenberg–Gijswijt capset
  bound_. Blog post, May 18, 2016.
* [erdosproblems.com/857](https://www.erdosproblems.com/857)
-/

open Finset Filter Topology

section FormalConjectures

variable {α : Type*}

/--
A sunflower `F` with kernel `S` is a collection of sets in which all possible distinct pairs of sets
share the same intersection `S`.
-/
def IsSunflowerWithKernel (F : Set (Set α)) (S : Set α) : Prop :=
  F.Pairwise (fun A B => A ∩ B = S)

/--
A sunflower `F` is a collection of sets in which all possible distinct pairs of sets share the
same intersection.
-/
def IsSunflower (F : Set (Set α)) : Prop := ∃ S, IsSunflowerWithKernel F S

end FormalConjectures

namespace Erdos857

/--
`m(n, k)`: minimal sunflower-forcing family size in the non-uniform `[n]` model.
-/
noncomputable def m (n k : ℕ) : ℕ :=
  sInf {t : ℕ | ∀ (F : Set (Set (Fin n))), t ≤ F.ncard →
    ∃ S ⊆ F, S.ncard = k ∧ IsSunflower S}

/-! ### Tao's slice-rank lemma -/

/-- In a subspace `W` of `ι → K` over an infinite field there is a vector with at least
`finrank W` nonzero coordinates. -/
theorem exists_mem_finrank_le_card_support {K ι : Type*} [Field K] [DecidableEq K] [Infinite K]
    [Fintype ι] (W : Submodule K (ι → K)) :
    ∃ h ∈ W, Module.finrank K W ≤ Fintype.card {i // h i ≠ 0} := by
  classical
  let supp : (ι → K) → Finset ι := fun g => univ.filter (fun i => g i ≠ 0)
  let 𝒮 : Finset (Finset ι) := univ.filter (fun s => ∃ g ∈ W, supp g = s)
  have hne : 𝒮.Nonempty := ⟨supp 0, by
    simp only [𝒮, mem_filter, mem_univ, true_and]; exact ⟨0, W.zero_mem, rfl⟩⟩
  obtain ⟨s, hs, hmax⟩ := Finset.exists_max_image 𝒮 Finset.card hne
  obtain ⟨h, hW, rfl⟩ := (by simpa [𝒮] using hs : ∃ g ∈ W, supp g = s)
  have hmax' : ∀ g ∈ W, (supp g).card ≤ (supp h).card := fun g hg =>
    hmax (supp g) (by simp only [𝒮, mem_filter, mem_univ, true_and]; exact ⟨g, hg, rfl⟩)
  -- every vector of `W` is supported inside the support of `h`
  have hsub : ∀ g ∈ W, ∀ i, h i = 0 → g i = 0 := by
    by_contra hcon
    push Not at hcon
    obtain ⟨g, hg, i, hi, hgi⟩ := hcon
    obtain ⟨c, hc⟩ :=
      Infinite.exists_notMem_finset (insert 0 (univ.image (fun j => -h j / g j)))
    have hc0 : c ≠ 0 := fun h0 => hc (by simp [h0])
    have hcj : ∀ j, g j ≠ 0 → c ≠ -h j / g j := fun j _ hj => hc (by
      rw [hj]; exact mem_insert_of_mem (mem_image_of_mem _ (mem_univ j)))
    have hle := hmax' (h + c • g) (W.add_mem hW (W.smul_mem c hg))
    have hlt : (supp h).card < (supp (h + c • g)).card := by
      apply Finset.card_lt_card
      refine Finset.ssubset_iff.mpr ⟨i, by simp [supp, hi], ?_⟩
      intro j hj
      simp only [supp, mem_insert, mem_filter, mem_univ, true_and, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul] at hj ⊢
      rcases hj with rfl | hj
      · simp [hi, hc0, hgi]
      · intro h0
        by_cases hgj : g j = 0
        · simp [hgj] at h0; exact hj h0
        · exact hcj j hgj (by field_simp; linear_combination h0)
    omega
  refine ⟨h, hW, ?_⟩
  let r : W →ₗ[K] ({i // h i ≠ 0} → K) :=
    { toFun := fun v i => (v : ι → K) i
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hr : Function.Injective r := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro v hv
    ext i
    by_cases hi : h i = 0
    · simpa using hsub v v.2 i hi
    · simpa [r] using congrFun hv ⟨i, hi⟩
  simpa using LinearMap.finrank_le_finrank_of_injective hr

/-- **Tao's slice-rank lemma** (diagonal case) [Tao16, Lemma 1]: a function on `ι × ι × ι`
which vanishes off the diagonal and not on it cannot be written as a sum of fewer than
`Fintype.card ι` slices. -/
theorem card_le_of_diagonal {K ι β : Type*} [Field K] [DecidableEq K] [Infinite K] [Fintype ι]
    [DecidableEq ι] (T : ι → ι → ι → K) (hoff : ∀ x y z, T x y z ≠ 0 → x = y ∧ x = z)
    (hdiag : ∀ x, T x x x ≠ 0)
    (s₁ s₂ s₃ : Finset β) (f₁ f₂ f₃ : β → ι → K) (g₁ g₂ g₃ : β → ι → ι → K)
    (hT : ∀ x y z, T x y z = ∑ a ∈ s₁, f₁ a x * g₁ a y z + ∑ b ∈ s₂, f₂ b y * g₂ b x z +
      ∑ c ∈ s₃, f₃ c z * g₃ c x y) :
    Fintype.card ι ≤ #s₁ + #s₂ + #s₃ := by
  classical
  let Φ : (ι → K) →ₗ[K] (s₁ → K) := Matrix.mulVecLin (fun (a : s₁) x => f₁ a x)
  have hker : Fintype.card ι ≤ #s₁ + Module.finrank K (LinearMap.ker Φ) := by
    have h1 := LinearMap.finrank_range_add_finrank_ker Φ
    have h2 := Submodule.finrank_le (LinearMap.range Φ)
    simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_coe] at h1 h2
    omega
  obtain ⟨h, hW, hsupp⟩ := exists_mem_finrank_le_card_support (LinearMap.ker Φ)
  have horth : ∀ a ∈ s₁, ∑ x, f₁ a x * h x = 0 := by
    intro a ha
    have : (Matrix.mulVec (fun (a : s₁) x => f₁ a x) h) ⟨a, ha⟩ = 0 :=
      congrFun (LinearMap.mem_ker.mp hW) ⟨a, ha⟩
    simpa [Matrix.mulVec, dotProduct] using this
  let G₂ : β → ι → K := fun b z => ∑ x, h x * g₂ b x z
  let H₃ : β → ι → K := fun c y => ∑ x, h x * g₃ c x y
  let U : Submodule K (ι → K) :=
    Submodule.span K ((s₂.image G₂ ∪ s₃.image f₃ : Finset (ι → K)) : Set (ι → K))
  have hU : Module.finrank K U ≤ #s₂ + #s₃ :=
    (finrank_span_finset_le_card _).trans
      ((card_union_le _ _).trans (add_le_add card_image_le card_image_le))
  -- the rows of the contracted matrix
  have hrow : ∀ y, (fun z => ∑ x, h x * T x y z) =
      ∑ b ∈ s₂, f₂ b y • G₂ b + ∑ c ∈ s₃, H₃ c y • f₃ c := by
    intro y
    funext z
    simp only [hT, Finset.sum_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_add,
      Finset.sum_add_distrib, Finset.mul_sum, G₂, H₃]
    have h0 : ∑ x, ∑ a ∈ s₁, h x * (f₁ a x * g₁ a y z) = 0 := by
      rw [Finset.sum_comm]
      refine Finset.sum_eq_zero fun a ha => ?_
      have := horth a ha
      calc ∑ x, h x * (f₁ a x * g₁ a y z) = (∑ x, f₁ a x * h x) * g₁ a y z := by
            rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun x _ => by ring
        _ = 0 := by rw [this, zero_mul]
    rw [h0, zero_add]
    congr 1
    · rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun x _ => by ring
    · rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun c _ => by
        rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun x _ => by ring
  have hrowU : ∀ y, (fun z => ∑ x, h x * T x y z) ∈ U := by
    intro y
    rw [hrow y]
    refine U.add_mem (U.sum_mem fun b hb => U.smul_mem _ ?_)
      (U.sum_mem fun c hc => U.smul_mem _ ?_)
    · exact Submodule.subset_span (by simp only [coe_union, coe_image]; exact Or.inl ⟨b, hb, rfl⟩)
    · exact Submodule.subset_span (by simp only [coe_union, coe_image]; exact Or.inr ⟨c, hc, rfl⟩)
  have hdrow : ∀ y, (fun z => ∑ x, h x * T x y z) = Pi.single y (h y * T y y y) := by
    intro y
    funext z
    rw [Finset.sum_eq_single y]
    · by_cases hz : z = y
      · subst hz; simp
      · rw [Pi.single_eq_of_ne hz]
        by_contra hne
        exact hz (hoff y y z (right_ne_zero_of_mul hne)).2.symm
    · intro x _ hx
      by_contra hne
      exact hx (hoff x y z (right_ne_zero_of_mul hne)).1
    · simp
  have hsingle : Submodule.span K
      (Set.range fun i : {i // h i ≠ 0} => (Pi.single i.1 (1 : K) : ι → K)) ≤ U := by
    rw [Submodule.span_le]
    rintro _ ⟨⟨y, hy⟩, rfl⟩
    have hmem := U.smul_mem (h y * T y y y)⁻¹ (hrowU y)
    rw [hdrow y, ← Pi.single_smul', smul_eq_mul, inv_mul_cancel₀ (mul_ne_zero hy (hdiag y))]
      at hmem
    exact hmem
  have hli : LinearIndependent K fun i : {i // h i ≠ 0} => (Pi.single i.1 (1 : K) : ι → K) :=
    (Pi.linearIndependent_single_one ι K).comp _ Subtype.val_injective
  have := Submodule.finrank_mono hsingle
  rw [finrank_span_eq_card hli] at this
  omega

/-! ### The Naslund–Sawin tensor and its slice decomposition -/

/-- `ind i x = 1` if `i ∈ x` and `0` otherwise: coordinate `i` of the indicator vector of `x`. -/
def ind {n : ℕ} (i : Fin n) (x : Finset (Fin n)) : ℚ := if i ∈ x then 1 else 0

/-- The Naslund–Sawin function `T(x, y, z) = ∏ᵢ (2 - xᵢ - yᵢ - zᵢ)` on `{0,1}ⁿ`. -/
def T (n : ℕ) (x y z : Finset (Fin n)) : ℚ := ∏ i, (2 - ind i x - ind i y - ind i z)

/-- The set of coordinates on which `σ : Fin n → Fin 4` takes the value `j`. -/
def lvl {n : ℕ} (σ : Fin n → Fin 4) (j : Fin 4) : Finset (Fin n) := univ.filter (σ · = j)

/-- The coefficient of the monomial indexed by `σ` in the expansion of `T`. -/
def coef {n : ℕ} (σ : Fin n → Fin 4) : ℚ := ∏ i, if σ i = 0 then 2 else -1

/-- The indicator `[I ⊆ x]`, i.e. the multilinear monomial `∏_{i ∈ I} xᵢ`. -/
def mono {n : ℕ} (I x : Finset (Fin n)) : ℚ := if I ⊆ x then 1 else 0

theorem prod_ite_ind {n : ℕ} (σ : Fin n → Fin 4) (j : Fin 4) (x : Finset (Fin n)) :
    ∏ i, (if σ i = j then ind i x else 1) = mono (lvl σ j) x := by
  have : ∀ i, (if σ i = j then ind i x else 1) = if (σ i = j → i ∈ x) then 1 else 0 := by
    intro i; by_cases h : σ i = j <;> by_cases h' : i ∈ x <;> simp [h, h', ind]
  simp only [this, Fintype.prod_boole, mono, lvl, subset_iff, mem_filter, mem_univ, true_and]
  congr

/-- Expansion of `T` into products of three multilinear monomials. -/
theorem T_expand (n : ℕ) (x y z : Finset (Fin n)) :
    T n x y z = ∑ σ : Fin n → Fin 4,
      coef σ * mono (lvl σ 1) x * mono (lvl σ 2) y * mono (lvl σ 3) z := by
  have hfac : ∀ i : Fin n, (2 - ind i x - ind i y - ind i z) =
      ∑ j : Fin 4, (if j = 0 then 2 else -1) * (if j = 1 then ind i x else 1) *
        (if j = 2 then ind i y else 1) * (if j = 3 then ind i z else 1) := by
    intro i; simp [Fin.sum_univ_four]; ring
  rw [T, Finset.prod_congr rfl fun i _ => hfac i, Finset.prod_univ_sum, Fintype.piFinset_univ]
  refine Finset.sum_congr rfl fun σ _ => ?_
  simp only [Finset.prod_mul_distrib, prod_ite_ind, coef]

/-- The index set `{I ⊆ [n] : |I| ≤ n/3}` of low-degree multilinear monomials. -/
def small (n : ℕ) : Finset (Finset (Fin n)) := univ.filter (fun I => #I ≤ n / 3)

theorem card_small (n : ℕ) : #(small n) = ∑ k ∈ range (n / 3 + 1), n.choose k := by
  rw [card_eq_sum_card_fiberwise (f := Finset.card) (t := range (n / 3 + 1))]
  · refine sum_congr rfl fun k hk => ?_
    have hk' : k ≤ n / 3 := Nat.lt_succ_iff.mp (mem_range.mp hk)
    have : {I ∈ small n | #I = k} = powersetCard k univ := by
      ext I
      simp only [small, mem_filter, mem_univ, true_and, mem_powersetCard_univ]
      constructor
      · exact fun h => h.2
      · intro h; exact ⟨h ▸ hk', h⟩
    rw [this, card_powersetCard, card_univ, Fintype.card_fin]
  · intro I hI
    simp only [small, coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hI
    simp only [coe_range, Set.mem_Iio]
    omega

theorem card_lvl_add_le {n : ℕ} (σ : Fin n → Fin 4) :
    #(lvl σ 1) + #(lvl σ 2) + #(lvl σ 3) ≤ n := by
  have := card_eq_sum_card_fiberwise (f := σ) (s := univ) (t := univ) (fun _ _ => mem_univ _)
  simp only [card_univ, Fintype.card_fin, Fin.sum_univ_four] at this
  simp only [lvl]
  omega

/-- Regrouping a sum over `σ` according to the monomial `lvl σ j`. -/
theorem sum_small_fiber {n : ℕ} (s : Finset (Fin n → Fin 4)) (j : Fin 4)
    (hs : ∀ σ ∈ s, lvl σ j ∈ small n) (u : Finset (Fin n) → ℚ) (w : (Fin n → Fin 4) → ℚ) :
    ∑ a ∈ small n, u a * ∑ σ ∈ s with lvl σ j = a, w σ = ∑ σ ∈ s, u (lvl σ j) * w σ := by
  rw [← sum_fiberwise_of_maps_to hs]
  refine sum_congr rfl fun a _ => ?_
  rw [mul_sum]
  refine sum_congr rfl fun σ hσ => ?_
  rw [(mem_filter.mp hσ).2]

/-- The part of `T` whose first monomial has degree `≤ n/3`. -/
def G₁ (n : ℕ) (a y z : Finset (Fin n)) : ℚ :=
  ∑ σ ∈ (univ.filter fun σ => #(lvl σ 1) ≤ n / 3) with lvl σ 1 = a,
    coef σ * mono (lvl σ 2) y * mono (lvl σ 3) z

/-- The part of `T` assigned to the second monomial. -/
def G₂ (n : ℕ) (b x z : Finset (Fin n)) : ℚ :=
  ∑ σ ∈ (univ.filter fun σ => ¬ #(lvl σ 1) ≤ n / 3 ∧ #(lvl σ 2) ≤ n / 3) with lvl σ 2 = b,
    coef σ * mono (lvl σ 1) x * mono (lvl σ 3) z

/-- The part of `T` assigned to the third monomial. -/
def G₃ (n : ℕ) (c x y : Finset (Fin n)) : ℚ :=
  ∑ σ ∈ (univ.filter fun σ => ¬ #(lvl σ 1) ≤ n / 3 ∧ ¬ #(lvl σ 2) ≤ n / 3) with lvl σ 3 = c,
    coef σ * mono (lvl σ 1) x * mono (lvl σ 2) y

/-- The slice decomposition of `T`: every term of the expansion has a monomial of degree
`≤ n/3` in one of the three variables. -/
theorem T_decomp (n : ℕ) (x y z : Finset (Fin n)) :
    T n x y z = ∑ a ∈ small n, mono a x * G₁ n a y z + ∑ b ∈ small n, mono b y * G₂ n b x z +
      ∑ c ∈ small n, mono c z * G₃ n c x y := by
  rw [T_expand]
  simp only [G₁, G₂, G₃]
  rw [sum_small_fiber _ 1 (fun σ hσ => by simpa [small] using hσ),
    sum_small_fiber _ 2 (fun σ hσ => by simp [small] at hσ ⊢; exact hσ.2),
    sum_small_fiber _ 3 (fun σ hσ => by
      simp [small] at hσ ⊢; have := card_lvl_add_le σ; omega)]
  rw [← sum_filter_add_sum_filter_not univ (fun σ => #(lvl σ 1) ≤ n / 3),
    ← sum_filter_add_sum_filter_not (univ.filter fun σ => ¬ #(lvl σ 1) ≤ n / 3)
      (fun σ => #(lvl σ 2) ≤ n / 3), filter_filter, filter_filter, add_assoc]
  congr 1
  · exact sum_congr rfl fun σ _ => by ring
  · congr 1
    · exact sum_congr rfl fun σ _ => by ring
    · exact sum_congr rfl fun σ _ => by ring

/-! ### Sunflower-free families -/

theorem factor_ne_zero {n : ℕ} {i : Fin n} {x y z : Finset (Fin n)}
    (h : (2 - ind i x - ind i y - ind i z : ℚ) ≠ 0) :
    ¬ (i ∈ x ∧ i ∈ y ∧ i ∉ z) ∧ ¬ (i ∈ x ∧ i ∉ y ∧ i ∈ z) ∧ ¬ (i ∉ x ∧ i ∈ y ∧ i ∈ z) := by
  by_cases hx : i ∈ x <;> by_cases hy : i ∈ y <;> by_cases hz : i ∈ z <;>
    simp only [ind, hx, hy, hz, ↓reduceIte] at h <;> norm_num at h <;> simp [hx, hy, hz]

theorem T_self_ne_zero (n : ℕ) (x : Finset (Fin n)) : T n x x x ≠ 0 := by
  refine prod_ne_zero_iff.mpr fun i _ => ?_
  by_cases hx : i ∈ x <;> simp [ind, hx]; norm_num

/-- On one layer (sets of a fixed size `l`) of a family with no `3`-sunflower, `T(x, y, z) ≠ 0`
forces `x = y = z`. -/
theorem eq_of_T_ne_zero {n l : ℕ} (F : Set (Set (Fin n)))
    (hF : ∀ S ⊆ F, S.ncard = 3 → ¬ IsSunflower S) {x y z : Finset (Fin n)}
    (hx : (x : Set (Fin n)) ∈ F) (hy : (y : Set (Fin n)) ∈ F) (hz : (z : Set (Fin n)) ∈ F)
    (hxl : #x = l) (hyl : #y = l) (hzl : #z = l) (hT : T n x y z ≠ 0) : x = y ∧ x = z := by
  have key : ∀ i, _ := fun i => factor_ne_zero (prod_ne_zero_iff.mp hT i (mem_univ i))
  have hnot : ∀ u v : Finset (Fin n), #u = l → #v = l → u ≠ v → ∃ i ∈ u, i ∉ v := by
    intro u v hu hv huv
    by_contra hcon
    push Not at hcon
    exact huv (eq_of_subset_of_card_le hcon (by omega))
  by_cases hxy : x = y
  · subst hxy
    by_cases hxz : x = z
    · exact ⟨rfl, hxz⟩
    · obtain ⟨i, hi, hiz⟩ := hnot x z hxl hzl hxz
      exact absurd ⟨hi, hi, hiz⟩ (key i).1
  · by_cases hxz : x = z
    · subst hxz
      obtain ⟨i, hi, hiy⟩ := hnot x y hxl hyl hxy
      exact absurd ⟨hi, hiy, hi⟩ (key i).2.1
    · by_cases hyz : y = z
      · subst hyz
        obtain ⟨i, hi, hix⟩ := hnot y x hyl hxl (Ne.symm hxy)
        exact absurd ⟨hix, hi, hi⟩ (key i).2.2
      · exfalso
        refine hF {(x : Set (Fin n)), (y : Set (Fin n)), (z : Set (Fin n))} ?_ ?_ ?_
        · intro S hS
          rcases hS with rfl | rfl | rfl <;> assumption
        · rw [Set.ncard_eq_three]
          exact ⟨x, y, z, by simpa using hxy, by simpa using hxz, by simpa using hyz, rfl⟩
        · refine ⟨(x : Set (Fin n)) ∩ y ∩ z, ?_⟩
          intro A hA B hB hAB
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hA hB
          rcases hA with rfl | rfl | rfl <;> rcases hB with rfl | rfl | rfl <;>
            first
            | exact absurd rfl hAB
            | (ext i; have := key i; simp only [Set.mem_inter_iff, Finset.mem_coe]; tauto)

/-- The Naslund–Sawin bound for one layer. -/
theorem card_layer_le (n l : ℕ) (F : Set (Set (Fin n)))
    (hF : ∀ S ⊆ F, S.ncard = 3 → ¬ IsSunflower S) (A : Finset (Finset (Fin n)))
    (hA : ∀ x ∈ A, (x : Set (Fin n)) ∈ F ∧ #x = l) : #A ≤ 3 * #(small n) := by
  have hmem : ∀ x : A, (x.1 : Set (Fin n)) ∈ F ∧ #x.1 = l := fun x => hA x.1 x.2
  have := card_le_of_diagonal (K := ℚ) (ι := A) (β := Finset (Fin n))
    (fun x y z => T n x.1 y.1 z.1)
    (fun x y z h => by
      have := eq_of_T_ne_zero F hF (hmem x).1 (hmem y).1 (hmem z).1 (hmem x).2 (hmem y).2
        (hmem z).2 h
      exact ⟨Subtype.ext this.1, Subtype.ext this.2⟩)
    (fun x => T_self_ne_zero n x.1) (small n) (small n) (small n)
    (fun a x => mono a x.1) (fun b y => mono b y.1) (fun c z => mono c z.1)
    (fun a y z => G₁ n a y.1 z.1) (fun b x z => G₂ n b x.1 z.1) (fun c x y => G₃ n c x.1 y.1)
    (fun x y z => T_decomp n x.1 y.1 z.1)
  simp only [Fintype.card_coe] at this
  omega

/-- **Naslund–Sawin** (Theorem 3 of [NaSa17]): a family of subsets of `{1, …, n}` containing no
`3`-sunflower has at most `3 (n + 1) ∑_{k ≤ n/3} C(n, k)` members. -/
theorem ncard_le_of_sunflowerFree (n : ℕ) (F : Set (Set (Fin n)))
    (hF : ∀ S ⊆ F, S.ncard = 3 → ¬ IsSunflower S) :
    F.ncard ≤ 3 * (n + 1) * ∑ k ∈ range (n / 3 + 1), n.choose k := by
  classical
  set G := univ.filter fun x : Finset (Fin n) => (x : Set (Fin n)) ∈ F with hG
  have hFG : F = (fun x : Finset (Fin n) => (x : Set (Fin n))) '' (G : Set (Finset (Fin n))) := by
    ext S
    simp only [Set.mem_image, hG, coe_filter, mem_univ, true_and, Set.mem_ofPred_eq]
    constructor
    · intro hS
      exact ⟨S.toFinset, by simpa using hS, by simp⟩
    · rintro ⟨x, hx, rfl⟩
      exact hx
  have hcard : F.ncard = #G := by
    rw [hFG, Set.ncard_image_of_injective _ Finset.coe_injective, Set.ncard_coe_finset]
  rw [hcard, card_eq_sum_card_fiberwise (f := Finset.card) (t := range (n + 1))
    (fun x _ => by simpa [Nat.lt_succ_iff] using card_le_univ x)]
  calc ∑ l ∈ range (n + 1), #{x ∈ G | #x = l}
      ≤ ∑ l ∈ range (n + 1), 3 * #(small n) := sum_le_sum fun l _ => by
        refine card_layer_le n l F hF _ fun x hx => ?_
        simp only [hG, mem_filter, mem_univ, true_and] at hx
        exact hx
    _ = 3 * (n + 1) * ∑ k ∈ range (n / 3 + 1), n.choose k := by
        rw [sum_const, card_range, smul_eq_mul, card_small]; ring

/-- A family with more than `3 (n + 1) ∑_{k ≤ n/3} C(n, k)` members contains a `3`-sunflower. -/
theorem exists_sunflower_of_lt_ncard (n : ℕ) (F : Set (Set (Fin n)))
    (hF : 3 * (n + 1) * ∑ k ∈ range (n / 3 + 1), n.choose k < F.ncard) :
    ∃ S ⊆ F, S.ncard = 3 ∧ IsSunflower S := by
  by_contra hcon
  push Not at hcon
  have := ncard_le_of_sunflowerFree n F hcon
  omega

/-- `m n 3` is the least threshold: `m n 3 ≤ t` iff every family of at least `t` subsets of
`Fin n` contains a `3`-sunflower. In particular the set in the definition of `m` is nonempty,
so the `sInf ∅ = 0` convention plays no role. -/
theorem m_three_le_iff (n t : ℕ) :
    m n 3 ≤ t ↔
      ∀ F : Set (Set (Fin n)), t ≤ F.ncard → ∃ S ⊆ F, S.ncard = 3 ∧ IsSunflower S := by
  have hne : {t : ℕ | ∀ (F : Set (Set (Fin n))), t ≤ F.ncard →
      ∃ S ⊆ F, S.ncard = 3 ∧ IsSunflower S}.Nonempty :=
    ⟨3 * (n + 1) * ∑ k ∈ range (n / 3 + 1), n.choose k + 1,
      fun F hF => exists_sunflower_of_lt_ncard n F hF⟩
  constructor
  · intro h F hF
    exact Nat.sInf_mem hne F (h.trans hF)
  · intro h
    exact Nat.sInf_le h

/-- For `n = 0` the only subset is `∅`, so `m 0 3 = 2`. -/
theorem m_zero_three : m 0 3 = 2 := by
  apply le_antisymm
  · rw [m_three_le_iff]
    intro F hF
    exfalso
    have : F.ncard ≤ 1 := by
      calc F.ncard ≤ (Set.univ : Set (Set (Fin 0))).ncard := Set.ncard_le_ncard (Set.subset_univ F)
        _ = 1 := by rw [Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_set]; simp
    omega
  · by_contra h
    push Not at h
    obtain ⟨S, hS, hS3, -⟩ := (m_three_le_iff 0 1).mp (by omega) {∅} (by simp)
    have := Set.ncard_le_ncard hS
    simp only [Set.ncard_singleton] at this
    omega

/-- **Erdős Problem 857, Naslund–Sawin bound**: `m(n, 3) ≤ 3 (n + 1) ∑_{k ≤ n/3} C(n, k) + 1`. -/
theorem erdos_857.variants.naslund_sawin (n : ℕ) :
    m n 3 ≤ 3 * (n + 1) * ∑ k ∈ range (n / 3 + 1), n.choose k + 1 :=
  (m_three_le_iff n _).mpr fun F hF => exists_sunflower_of_lt_ncard n F hF

/-! ### The asymptotic form -/

/-- The entropy bound `∑_{k ≤ n/3} C(n, k) ≤ (3 / 2^(2/3))^n`. -/
theorem sum_choose_le_rpow (n : ℕ) :
    (∑ k ∈ range (n / 3 + 1), (n.choose k : ℝ)) ≤ (3 / 2 ^ (2 / 3 : ℝ)) ^ n := by
  set c : ℝ := 3 / 2 ^ (2 / 3 : ℝ) with hc
  have hcn : c ^ n = 3 ^ n / 2 ^ ((2 / 3 : ℝ) * n) := by
    rw [hc, div_pow, ← Real.rpow_natCast (2 ^ (2 / 3 : ℝ)), ← Real.rpow_mul (by norm_num)]
  have hterm : ∀ k ∈ range (n / 3 + 1),
      (n.choose k : ℝ) ≤ (1 / 3 : ℝ) ^ k * (2 / 3 : ℝ) ^ (n - k) * n.choose k * c ^ n := by
    intro k hk
    have hk' : k ≤ n / 3 := Nat.lt_succ_iff.mp (mem_range.mp hk)
    have hkn : k ≤ n := hk'.trans (Nat.div_le_self _ _)
    have h1 : (1 : ℝ) ≤ (1 / 3 : ℝ) ^ k * (2 / 3 : ℝ) ^ (n - k) * c ^ n := by
      rw [hcn]
      have e : (1 / 3 : ℝ) ^ k * (2 / 3 : ℝ) ^ (n - k) * (3 ^ n / 2 ^ ((2 / 3 : ℝ) * n)) =
          2 ^ (n - k) / 2 ^ ((2 / 3 : ℝ) * n) := by
        have h3 : (3 : ℝ) ^ n = 3 ^ k * 3 ^ (n - k) := by
          rw [← pow_add, Nat.add_sub_cancel' hkn]
        rw [h3, div_pow, one_pow, div_pow]
        field_simp
      rw [e, one_le_div (by positivity), ← Real.rpow_natCast]
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      rw [Nat.cast_sub hkn]
      have : (k : ℝ) * 3 ≤ n := by exact_mod_cast (by omega : k * 3 ≤ n)
      linarith
    have h0 : (0 : ℝ) ≤ n.choose k := Nat.cast_nonneg _
    nlinarith
  calc (∑ k ∈ range (n / 3 + 1), (n.choose k : ℝ))
      ≤ ∑ k ∈ range (n / 3 + 1), (1 / 3 : ℝ) ^ k * (2 / 3 : ℝ) ^ (n - k) * n.choose k * c ^ n :=
        sum_le_sum hterm
    _ ≤ ∑ k ∈ range (n + 1), (1 / 3 : ℝ) ^ k * (2 / 3 : ℝ) ^ (n - k) * n.choose k * c ^ n :=
        sum_le_sum_of_subset_of_nonneg (range_subset_range.mpr (by omega))
          (fun _ _ _ => by positivity)
    _ = (1 / 3 + 2 / 3 : ℝ) ^ n * c ^ n := by rw [add_pow, sum_mul]
    _ = c ^ n := by norm_num

/-- `m(n, 3) ≤ 3 (n + 1) (3 / 2^(2/3))^n + 1`. -/
theorem erdos_857.variants.naslund_sawin_rpow (n : ℕ) :
    (m n 3 : ℝ) ≤ 3 * (n + 1) * (3 / 2 ^ (2 / 3 : ℝ)) ^ n + 1 := by
  have h : (m n 3 : ℝ) ≤ 3 * (n + 1) * ∑ k ∈ range (n / 3 + 1), (n.choose k : ℝ) + 1 := by
    exact_mod_cast erdos_857.variants.naslund_sawin n
  have := sum_choose_le_rpow n
  calc (m n 3 : ℝ) ≤ 3 * (n + 1) * ∑ k ∈ range (n / 3 + 1), (n.choose k : ℝ) + 1 := h
    _ ≤ 3 * (n + 1) * (3 / 2 ^ (2 / 3 : ℝ)) ^ n + 1 := by gcongr

/-- **Erdős Problem 857, the bound on the problem page**:
`m(n, 3) ≤ (3 / 2^(2/3))^((1 + o(1)) n)` for `n ≥ 1`. -/
theorem erdos_857.variants.naslund_sawin_asymp :
    ∃ o : ℕ → ℝ, Tendsto o atTop (𝓝 0) ∧
      ∀ n ≥ 1, (m n 3 : ℝ) ≤ (3 / 2 ^ (2 / 3 : ℝ)) ^ ((1 + o n) * n) := by
  set c : ℝ := 3 / 2 ^ (2 / 3 : ℝ) with hc
  have hc1 : 1 < c := by
    rw [hc, lt_div_iff₀ (by positivity), one_mul]
    calc (2 : ℝ) ^ (2 / 3 : ℝ) ≤ 2 ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      _ < 3 := by norm_num
  have hlogc : 0 < Real.log c := Real.log_pos hc1
  refine ⟨fun n => Real.log (7 * n) / (n * Real.log c), ?_, ?_⟩
  · have h1 : Tendsto (fun x : ℝ => Real.log x / x) atTop (𝓝 0) := by
      simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
    have h2 : Tendsto (fun n : ℕ => (7 : ℝ) * n) atTop atTop :=
      tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num)
    have h3 := (h1.comp h2).mul_const (7 / Real.log c)
    rw [zero_mul] at h3
    refine h3.congr fun n => ?_
    simp only [Function.comp_apply]
    rw [div_mul_div_comm, mul_comm (Real.log (7 * n)) 7, mul_assoc,
      mul_div_mul_left _ _ (by norm_num : (7 : ℝ) ≠ 0)]
  · intro n hn
    have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hcn : 1 ≤ c ^ n := one_le_pow₀ hc1.le
    have key : c ^ ((1 + Real.log (7 * n) / (n * Real.log c)) * n) = c ^ n * (7 * n) := by
      rw [add_mul, one_mul, Real.rpow_add (by linarith), Real.rpow_natCast]
      congr 1
      rw [Real.rpow_def_of_pos (by linarith)]
      have : Real.log c * (Real.log (7 * n) / (n * Real.log c) * n) = Real.log (7 * n) := by
        field_simp
      rw [this, Real.exp_log (by linarith)]
    have hprod : (0 : ℝ) ≤ (4 * n - 3) * (c ^ n - 1) :=
      mul_nonneg (by linarith) (by linarith)
    rw [key]
    calc (m n 3 : ℝ) ≤ 3 * (n + 1) * c ^ n + 1 := erdos_857.variants.naslund_sawin_rpow n
      _ ≤ c ^ n * (7 * n) := by nlinarith

end Erdos857
