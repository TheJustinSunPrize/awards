import Mathlib

/-!
# Erdős Problem 129: Girão's counterexample `R(n;3,r) ≥ C^n`

Erdős Problem 129 ([Er97b], https://www.erdosproblems.com/129) reads:

> Let `R(n;k,r)` be the smallest `N` such that if the edges of `K_N` are `r`-coloured then there
> is a set of `n` vertices which does not contain a copy of `K_k` in at least one of the `r`
> colours. Prove that there is a constant `C = C(r) > 1` such that `R(n;3,r) < C^{√n}`.

The problem page records a remark of Antonio Girão: the problem as written is easily disproved,
since a uniformly random colouring shows `R(n;3,2) ≥ C^n` for an absolute `C > 1` (every set of
`n` vertices contains `≫ n²` edge-disjoint triangles). The page also marks the original source as
ambiguous: Erdős may have had a different problem in mind, but it is not clear which. This file
formalizes Girão's argument, for every number of colours `r ≥ 2`, and derives the negation of the
conjecture exactly as written. It says nothing about any other intended version.

## Definitions and faithfulness

* `EdgeColouring N r`: maps from the edge set of the complete graph `⊤ : SimpleGraph (Fin N)`
  (that is, `K_N`) to `Fin r`.
* `colourClass χ c`: the graph on `Fin N` formed by the edges of colour `c`.
* `R n k r`: the infimum of the set of `N` such that for every `χ : EdgeColouring N r` there are
  an `n`-set `S` and a colour `c` such that no `T ⊆ S` is a `k`-clique of `colourClass χ c`,
  i.e. `S` contains no copy of `K_k` in colour `c`. "In at least one of the `r` colours" is read
  as "there is a colour `c`"; this is the reading under which `r = k = 2` gives the classical
  Ramsey numbers, as the problem page notes.

## Non-vacuity

`sInf ∅ = 0`, so the lower bound is only meaningful once the defining set is nonempty.
`R_set_nonempty` proves this for all `n` and all `k, r ≥ 2`: merge the colours into
"colour `0`" and "not colour `0`" and apply the finite Ramsey theorem `ramsey_exists`
(copied from our `Jsp/Erdos564.lean`). A set that is monochromatic in the merged colouring has
no `K_k` (`k ≥ 2`) in colour `1`, respectively in colour `0`. Hence `R n k r` is a genuine
minimum. (For `r = 1`, `k = 3`, `n ≥ 3` the set is empty; such `r` are excluded throughout.)

## Proof of the lower bound (counting, no probability)

* **Packing** (`tri`, `card_bad_le`). Let `m = ⌊n/4⌋` and list an `n`-set `S` increasingly as
  `v₀ < v₁ < ⋯`. For `i, j < m` the triangles `{v_i, v_{m+j}, v_{2m+i+j}}` are pairwise
  edge-disjoint, giving `m²` edge-disjoint triangles inside `S`.
* **Counting** (`card_filter_le`). If `g : P × Fin 3 → E` is injective, the maps `E → Fin r`
  that give no `p ∈ P` all three edges `g (p, ·)` the colour `c` number at most
  `(r³ - 1)^|P| · r^(|E| - 3|P|)`. So for each `n`-set `S` and colour `c`, at most
  `(r³ - 1)^{m²} · r^(|E| - 3m²)` colourings have no triangle of colour `c` inside `S`.
* **Union bound** (`exists_colouring`, `lt_R`). If `C(N, n) · r · (r³ - 1)^{m²} < r^{3m²}`, some
  colouring of `K_N` has triangles of every colour inside every `n`-set, so `N < R n 3 r`.
* **Arithmetic** (`two_pow_lt_R`). With `a = r³ - 1`, `2^⌊M/a⌋ · a^M ≤ (a + 1)^M` (from
  `2 a^a ≤ (a + 1)^a`), and `N ≤ 2^t` with `t = ⌊n/(32a)⌋` satisfies the condition once
  `n ≥ 8a + 12`.
* **Conclusion**. `R(n;3,r) ≥ c^n` with `c = 2^{1/(64 (r³ - 1))}` for all large `n`, and
  `c^n` eventually exceeds `C^{√n}` for every `C > 1`.

## Main results

* `Erdos129.R_set_nonempty`: the set defining `R n k r` is nonempty for `k, r ≥ 2`.
* `Erdos129.two_pow_lt_R`: `2 ≤ r → 8 (r³ - 1) + 12 ≤ n → 2 ^ (n / (32 (r³ - 1))) < R n 3 r`.
* `Erdos129.girao_lower_bound`: for `r ≥ 2`, `∃ c > 1, ∀ᶠ n in atTop, c ^ n ≤ R n 3 r`.
* `Erdos129.erdos_129_disproof`: for each `r ≥ 2` there is no `C > 1` with
  `R n 3 r < C ^ √n` for all large `n`.
* `Erdos129.erdos_129`: the conjecture as written, `∀ r ≥ 2, ∃ C > 1, ∀ n, R n 3 r < C ^ √n`,
  is false.
* `Erdos129.erdos_gyarfas_lower_bound`: for `r ≥ 2` and every `C > 1`, eventually
  `C ^ √n < R n 3 r` (this contains the Erdős–Gyárfás lower bound `R(n;3,r) > C^{√n}`).
-/

open Filter

namespace Erdos129

/-- An `r`-colouring of the edges of the complete graph `K_N` on the vertex set `Fin N`. -/
abbrev EdgeColouring (N r : ℕ) : Type := (⊤ : SimpleGraph (Fin N)).edgeSet → Fin r

/-- The graph on `Fin N` whose edges are the edges of `K_N` that `χ` colours `c`. -/
def colourClass {N r : ℕ} (χ : EdgeColouring N r) (c : Fin r) : SimpleGraph (Fin N) :=
  SimpleGraph.fromEdgeSet {e | ∃ h : e ∈ (⊤ : SimpleGraph (Fin N)).edgeSet, χ ⟨e, h⟩ = c}

/-- `R(n;k,r)`: the smallest `N` such that for every `r`-colouring of the edges of `K_N` there
are a set `S` of `n` vertices and a colour `c` such that `S` contains no copy of `K_k` all of
whose edges have colour `c`. -/
noncomputable def R (n k r : ℕ) : ℕ :=
  sInf {N | ∀ χ : EdgeColouring N r, ∃ S : Finset (Fin N), S.card = n ∧
    ∃ c : Fin r, ∀ T ⊆ S, ¬ (colourClass χ c).IsNClique k T}

/-- The edge `{x, y}` of `K_N`, for `x ≠ y`. -/
def edge {N : ℕ} (x y : Fin N) (h : x ≠ y) : (⊤ : SimpleGraph (Fin N)).edgeSet :=
  ⟨s(x, y), (SimpleGraph.mem_edgeSet _).mpr ((SimpleGraph.top_adj x y).mpr h)⟩

theorem colourClass_adj {N r : ℕ} (χ : EdgeColouring N r) (c : Fin r) (x y : Fin N) :
    (colourClass χ c).Adj x y ↔ ∃ h : x ≠ y, χ (edge x y h) = c := by
  simp only [colourClass, SimpleGraph.fromEdgeSet_adj, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨⟨_, hc⟩, hxy⟩
    exact ⟨hxy, hc⟩
  · rintro ⟨hxy, hc⟩
    exact ⟨⟨_, hc⟩, hxy⟩

/-! ### Edge-disjoint triangles -/

/-- For `p = (i, j)`, the three edges of the triangle with vertex indices `i`, `m + j`,
`2m + i + j`, each given as the pair of its endpoint indices (smaller first). -/
def tri (m : ℕ) (p : Fin m × Fin m) : Fin 3 → ℕ × ℕ :=
  ![(p.1, m + p.2), (p.1, 2 * m + p.1 + p.2), (m + p.2, 2 * m + p.1 + p.2)]

/-- The endpoint indices of each edge are increasing and below `4m`. -/
theorem tri_lt (m : ℕ) (p : Fin m × Fin m) (t : Fin 3) :
    (tri m p t).1 < (tri m p t).2 ∧ (tri m p t).2 < 4 * m := by
  obtain ⟨⟨i, hi⟩, ⟨j, hj⟩⟩ := p
  fin_cases t <;> simp [tri] <;> omega

/-- Distinct `(triangle, edge)` labels give distinct index pairs: the triangles are pairwise
edge-disjoint. -/
theorem tri_injective (m : ℕ) (p p' : Fin m × Fin m) (t t' : Fin 3)
    (h : tri m p t = tri m p' t') : p = p' ∧ t = t' := by
  obtain ⟨⟨i, hi⟩, ⟨j, hj⟩⟩ := p
  obtain ⟨⟨i', hi'⟩, ⟨j', hj'⟩⟩ := p'
  fin_cases t <;> fin_cases t' <;> simp [tri, Prod.ext_iff] at h ⊢ <;> omega

/-! ### Counting colourings -/

/-- If `g : P × Fin 3 → E` is injective (so the `|P|` triples `g (p, ·)` are pairwise disjoint),
then the maps `χ : E → Fin r` such that no triple is entirely coloured `c` satisfy
`#{χ} · r^(3|P|) ≤ (r³ - 1)^|P| · r^|E|`. -/
theorem card_filter_le {E P : Type*} [Fintype E] [DecidableEq E] [Fintype P] [DecidableEq P]
    (r : ℕ) (c : Fin r) (g : P × Fin 3 → E) (hg : Function.Injective g) :
    (Finset.univ.filter (fun χ : E → Fin r => ∀ p, ∃ t, χ (g (p, t)) ≠ c)).card *
        r ^ (3 * Fintype.card P) ≤ (r ^ 3 - 1) ^ Fintype.card P * r ^ Fintype.card E := by
  set F := Finset.univ.filter (fun χ : E → Fin r => ∀ p, ∃ t, χ (g (p, t)) ≠ c) with hF
  set A : Finset (Fin 3 → Fin r) := Finset.univ.filter (fun u => ∃ t, u t ≠ c) with hA
  have hAcard : A.card ≤ r ^ 3 - 1 := by
    have hsub : A ⊆ Finset.univ.erase (fun _ => c) := by
      intro u hu
      simp only [hA, Finset.mem_filter, Finset.mem_univ, true_and] at hu
      obtain ⟨t, ht⟩ := hu
      exact Finset.mem_erase.mpr ⟨fun h => ht (by rw [h]), Finset.mem_univ _⟩
    refine (Finset.card_le_card hsub).trans ?_
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fun,
      Fintype.card_fin, Fintype.card_fin]
  set I : Finset E := Finset.univ.image g with hI
  have hIcard : I.card = 3 * Fintype.card P := by
    rw [hI, Finset.card_image_of_injective _ hg, Finset.card_univ, Fintype.card_prod,
      Fintype.card_fin, mul_comm]
  set B := {e : E // e ∉ I}
  have hBcard : Fintype.card B = Fintype.card E - 3 * Fintype.card P := by
    rw [Fintype.card_subtype_compl, Fintype.card_coe, hIcard]
  have hle3 : 3 * Fintype.card P ≤ Fintype.card E := by
    rw [← hIcard]; exact Finset.card_le_univ I
  let Φ : (E → Fin r) → (P → Fin 3 → Fin r) × (B → Fin r) :=
    fun χ => (fun p t => χ (g (p, t)), fun b => χ b.1)
  have hΦ : Function.Injective Φ := by
    intro χ χ' h
    simp only [Φ, Prod.mk.injEq] at h
    obtain ⟨h1, h2⟩ := h
    funext e
    by_cases he : e ∈ I
    · obtain ⟨⟨p, t⟩, -, rfl⟩ := Finset.mem_image.mp he
      exact congrFun (congrFun h1 p) t
    · exact congrFun h2 ⟨e, he⟩
  have hcard := Finset.card_le_card_of_injOn Φ (s := F)
    (t := Fintype.piFinset (fun _ : P => A) ×ˢ (Finset.univ : Finset (B → Fin r)))
    (fun χ hχ => by
      rw [Finset.mem_coe, hF, Finset.mem_filter] at hχ
      rw [Finset.mem_coe, Finset.mem_product, Fintype.mem_piFinset]
      exact ⟨fun p => Finset.mem_filter.mpr ⟨Finset.mem_univ _, hχ.2 p⟩, Finset.mem_univ _⟩)
    (hΦ.injOn)
  rw [Finset.card_product, Fintype.card_piFinset, Finset.prod_const, Finset.card_univ,
    Finset.card_univ, Fintype.card_fun, Fintype.card_fin, hBcard] at hcard
  calc _ ≤ A.card ^ Fintype.card P * r ^ (Fintype.card E - 3 * Fintype.card P) *
        r ^ (3 * Fintype.card P) := Nat.mul_le_mul_right _ hcard
    _ ≤ (r ^ 3 - 1) ^ Fintype.card P * r ^ (Fintype.card E - 3 * Fintype.card P) *
        r ^ (3 * Fintype.card P) :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hAcard _))
    _ = _ := by rw [mul_assoc, ← pow_add, Nat.sub_add_cancel hle3]

open scoped Classical in
/-- For an `n`-set `S` with `4m ≤ n` and a colour `c`, the colourings of `K_N` with no triangle of
colour `c` inside `S` number at most `(r³ - 1)^{m²} · r^(|E| - 3m²)`. -/
theorem card_bad_le {N n m r : ℕ} (hm : 4 * m ≤ n) (S : Finset (Fin N)) (hS : S.card = n)
    (c : Fin r) :
    (Finset.univ.filter (fun χ : EdgeColouring N r =>
        ∀ T ⊆ S, ¬ (colourClass χ c).IsNClique 3 T)).card * r ^ (3 * (m * m)) ≤
      (r ^ 3 - 1) ^ (m * m) * r ^ Fintype.card (⊤ : SimpleGraph (Fin N)).edgeSet := by
  set v := S.orderEmbOfFin hS
  have hb : ∀ (p : Fin m × Fin m) (t : Fin 3), (tri m p t).1 < n ∧ (tri m p t).2 < n := by
    intro p t
    have := tri_lt m p t
    omega
  let g : (Fin m × Fin m) × Fin 3 → (⊤ : SimpleGraph (Fin N)).edgeSet := fun pt =>
    edge (v ⟨(tri m pt.1 pt.2).1, (hb pt.1 pt.2).1⟩) (v ⟨(tri m pt.1 pt.2).2, (hb pt.1 pt.2).2⟩)
      (fun h => by
        have h1 := Fin.mk.inj_iff.mp (v.injective h)
        have h2 := (tri_lt m pt.1 pt.2).1
        omega)
  have hg : Function.Injective g := by
    rintro ⟨p, t⟩ ⟨p', t'⟩ h
    have h' := congrArg Subtype.val h
    simp only [g, edge, Sym2.eq_iff] at h'
    have hlt := (tri_lt m p t).1
    have hlt' := (tri_lt m p' t').1
    rcases h' with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have e1 := Fin.mk.inj_iff.mp (v.injective h1)
      have e2 := Fin.mk.inj_iff.mp (v.injective h2)
      obtain ⟨rfl, rfl⟩ := tri_injective m p p' t t' (Prod.ext e1 e2)
      rfl
    · have e1 := Fin.mk.inj_iff.mp (v.injective h1)
      have e2 := Fin.mk.inj_iff.mp (v.injective h2)
      omega
  have key := card_filter_le r c g hg
  rw [Fintype.card_prod, Fintype.card_fin] at key
  refine le_trans (Nat.mul_le_mul_right _ (Finset.card_le_card ?_)) key
  intro χ hχ
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hχ ⊢
  intro p
  by_contra hall
  push Not at hall
  have hv : ∀ (k : ℕ) (hk : k < n), v ⟨k, hk⟩ ∈ S := fun k hk => S.orderEmbOfFin_mem hS _
  apply hχ {v ⟨(tri m p 0).1, (hb p 0).1⟩, v ⟨(tri m p 0).2, (hb p 0).2⟩,
    v ⟨(tri m p 1).2, (hb p 1).2⟩}
  · intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl <;> exact hv _ _
  · rw [SimpleGraph.is3Clique_triple_iff, colourClass_adj, colourClass_adj, colourClass_adj]
    exact ⟨⟨_, hall 0⟩, ⟨_, hall 1⟩, ⟨_, hall 2⟩⟩

open scoped Classical in
/-- Union bound: if `C(N, n) · r · (r³ - 1)^{m²} < r^{3m²}` (with `4m ≤ n`), some colouring of
`K_N` has, for every colour, a triangle of that colour inside every `n`-set. -/
theorem exists_colouring {N n m r : ℕ} (hr : 1 ≤ r) (hm : 4 * m ≤ n)
    (h : N.choose n * r * (r ^ 3 - 1) ^ (m * m) < r ^ (3 * (m * m))) :
    ∃ χ : EdgeColouring N r, ∀ S : Finset (Fin N), S.card = n → ∀ c : Fin r,
      ∃ T ⊆ S, (colourClass χ c).IsNClique 3 T := by
  by_contra hcon
  push Not at hcon
  set K := Fintype.card (⊤ : SimpleGraph (Fin N)).edgeSet
  set M := m * m
  let bad : Finset (Fin N) → Fin r → Finset (EdgeColouring N r) := fun S c =>
    Finset.univ.filter (fun χ => ∀ T ⊆ S, ¬ (colourClass χ c).IsNClique 3 T)
  have hsub : (Finset.univ : Finset (EdgeColouring N r)) ⊆
      ((Finset.univ : Finset (Fin N)).powersetCard n).biUnion
        (fun S => (Finset.univ : Finset (Fin r)).biUnion (bad S)) := by
    intro χ _
    obtain ⟨S, hS, c, hc⟩ := hcon χ
    simp only [Finset.mem_biUnion, Finset.mem_powersetCard, Finset.mem_univ, true_and]
    refine ⟨S, ⟨Finset.subset_univ S, hS⟩, c, ?_⟩
    simp only [bad, Finset.mem_filter, Finset.mem_univ, true_and]
    exact hc
  have h1 := (Finset.card_le_card hsub).trans
    (Finset.card_biUnion_le.trans (Finset.sum_le_sum fun S _ => Finset.card_biUnion_le))
  rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin] at h1
  have h2 : (∑ S ∈ (Finset.univ : Finset (Fin N)).powersetCard n,
      ∑ c : Fin r, (bad S c).card) * r ^ (3 * M) ≤
      ∑ S ∈ (Finset.univ : Finset (Fin N)).powersetCard n,
        ∑ _c : Fin r, (r ^ 3 - 1) ^ M * r ^ K := by
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun S hS => ?_
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum fun c _ => card_bad_le hm S (Finset.mem_powersetCard.mp hS).2 c
  rw [Finset.sum_const, Finset.sum_const, Finset.card_powersetCard, Finset.card_univ,
    Finset.card_univ, Fintype.card_fin, Fintype.card_fin, smul_eq_mul, smul_eq_mul] at h2
  have h3 := (Nat.mul_le_mul_right (r ^ (3 * M)) h1).trans h2
  have hK : 0 < r ^ K := by positivity
  have h4 : N.choose n * r * (r ^ 3 - 1) ^ M * r ^ K < r ^ (3 * M) * r ^ K :=
    Nat.mul_lt_mul_of_pos_right h hK
  nlinarith

/-- Finite off-diagonal hypergraph Ramsey theorem (copied from our `Jsp/Erdos564.lean`): for all
`r a b` there is `N` such that for every finset `X` with at least `N` elements and every
`c : Finset α → Bool`, some `a`-subset of `X` has all its `r`-subsets coloured `true`, or some
`b`-subset has all its `r`-subsets coloured `false`. Only `r = 2` is used here. -/
theorem ramsey_exists (r : ℕ) :
    ∀ a b : ℕ, ∃ N : ℕ, ∀ {α : Type} [DecidableEq α] (X : Finset α),
      N ≤ X.card → ∀ c : Finset α → Bool,
        (∃ S ⊆ X, S.card = a ∧ ∀ e ⊆ S, e.card = r → c e = true) ∨
        (∃ S ⊆ X, S.card = b ∧ ∀ e ⊆ S, e.card = r → c e = false) := by
  induction r with
  | zero =>
    intro a b
    refine ⟨a + b, fun X hX c => ?_⟩
    cases hc : c ∅ with
    | true =>
      obtain ⟨S, hS, hcard⟩ := Finset.exists_subset_card_eq (show a ≤ X.card by omega)
      exact Or.inl ⟨S, hS, hcard, fun e _ he => by rw [Finset.card_eq_zero.mp he]; exact hc⟩
    | false =>
      obtain ⟨S, hS, hcard⟩ := Finset.exists_subset_card_eq (show b ≤ X.card by omega)
      exact Or.inr ⟨S, hS, hcard, fun e _ he => by rw [Finset.card_eq_zero.mp he]; exact hc⟩
  | succ r ih =>
    intro a
    induction a with
    | zero =>
      intro b
      refine ⟨0, fun X _ c => Or.inl ⟨∅, Finset.empty_subset _, rfl, fun e he hcard => ?_⟩⟩
      simp [Finset.subset_empty.mp he] at hcard
    | succ a iha =>
      intro b
      induction b with
      | zero =>
        refine ⟨0, fun X _ c => Or.inr ⟨∅, Finset.empty_subset _, rfl, fun e he hcard => ?_⟩⟩
        simp [Finset.subset_empty.mp he] at hcard
      | succ b ihb =>
        obtain ⟨N₁, hN₁⟩ := iha (b + 1)
        obtain ⟨N₂, hN₂⟩ := ihb
        obtain ⟨M, hM⟩ := ih N₁ N₂
        refine ⟨M + 1, fun {α} _ X hX c => ?_⟩
        obtain ⟨v, hv⟩ : X.Nonempty := Finset.card_pos.mp (by omega)
        have hX' : M ≤ (X.erase v).card := by rw [Finset.card_erase_of_mem hv]; omega
        -- adding `v` to a set `Z` whose `r`-sets `T` all give `c (insert v T) = col`
        -- and whose `(r+1)`-sets all have colour `col` keeps it monochromatic
        have key : ∀ (col : Bool) (Z : Finset α), Z ⊆ X.erase v →
            (∀ T ⊆ Z, T.card = r → c (insert v T) = col) →
            (∀ e ⊆ Z, e.card = r + 1 → c e = col) →
            insert v Z ⊆ X ∧ (insert v Z).card = Z.card + 1 ∧
              ∀ e ⊆ insert v Z, e.card = r + 1 → c e = col := by
          intro col Z hZX hT hZ
          have hvZ : v ∉ Z := fun h => by simpa using hZX h
          refine ⟨Finset.insert_subset hv (hZX.trans (Finset.erase_subset v X)),
            Finset.card_insert_of_notMem hvZ, fun e he hcard => ?_⟩
          by_cases hve : v ∈ e
          · have h := hT (e.erase v) (fun x hx => ?_)
              (by rw [Finset.card_erase_of_mem hve, hcard]; rfl)
            · rwa [Finset.insert_erase hve] at h
            · obtain ⟨hxv, hxe⟩ := Finset.mem_erase.mp hx
              rcases Finset.mem_insert.mp (he hxe) with h | h
              · exact absurd h hxv
              · exact h
          · refine hZ e (fun x hx => ?_) hcard
            rcases Finset.mem_insert.mp (he hx) with h | h
            · exact absurd (h ▸ hx) hve
            · exact h
        rcases hM (X.erase v) hX' (fun T => c (insert v T)) with
          ⟨Y, hYX, hYcard, hY⟩ | ⟨Y, hYX, hYcard, hY⟩
        · rcases hN₁ Y hYcard.ge c with ⟨Z, hZY, hZcard, hZ⟩ | ⟨Z, hZY, hZcard, hZ⟩
          · obtain ⟨h1, h2, h3⟩ :=
              key true Z (hZY.trans hYX) (fun T hT => hY T (hT.trans hZY)) hZ
            exact Or.inl ⟨insert v Z, h1, by rw [h2, hZcard], h3⟩
          · exact Or.inr ⟨Z, (hZY.trans hYX).trans (Finset.erase_subset v X), hZcard, hZ⟩
        · rcases hN₂ Y hYcard.ge c with ⟨Z, hZY, hZcard, hZ⟩ | ⟨Z, hZY, hZcard, hZ⟩
          · exact Or.inl ⟨Z, (hZY.trans hYX).trans (Finset.erase_subset v X), hZcard, hZ⟩
          · obtain ⟨h1, h2, h3⟩ :=
              key false Z (hZY.trans hYX) (fun T hT => hY T (hT.trans hZY)) hZ
            exact Or.inr ⟨insert v Z, h1, by rw [h2, hZcard], h3⟩

/-! ### Non-vacuity and the lower bound -/

/-- The set whose infimum defines `R n k r` is nonempty for `k ≥ 2` and `r ≥ 2`, so `R n k r` is a
genuine minimum (and not the junk value `sInf ∅ = 0`). -/
theorem R_set_nonempty (n k r : ℕ) (hk : 2 ≤ k) (hr : 2 ≤ r) :
    {N | ∀ χ : EdgeColouring N r, ∃ S : Finset (Fin N), S.card = n ∧
      ∃ c : Fin r, ∀ T ⊆ S, ¬ (colourClass χ c).IsNClique k T}.Nonempty := by
  classical
  obtain ⟨N, hN⟩ := ramsey_exists 2 n n
  refine ⟨N, fun χ => ?_⟩
  let c0 : Fin r := ⟨0, by omega⟩
  let c1 : Fin r := ⟨1, by omega⟩
  let col : Finset (Fin N) → Bool := fun e =>
    decide (∀ x ∈ e, ∀ y ∈ e, ∀ h : x ≠ y, χ (edge x y h) = c0)
  have two : ∀ (c : Fin r) (T : Finset (Fin N)), (colourClass χ c).IsNClique k T →
      ∃ x ∈ T, ∃ y ∈ T, ∃ h : x ≠ y, χ (edge x y h) = c := by
    intro c T hT
    obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.mp (by rw [hT.card_eq]; omega)
    obtain ⟨h, hc⟩ := (colourClass_adj χ c x y).mp (hT.isClique hx hy hxy)
    exact ⟨x, hx, y, hy, h, hc⟩
  have pair_sub : ∀ (S T : Finset (Fin N)), T ⊆ S → ∀ x ∈ T, ∀ y ∈ T,
      ({x, y} : Finset (Fin N)) ⊆ S := by
    intro S T hTS x hx y hy z hz
    rcases Finset.mem_insert.mp hz with rfl | hz
    · exact hTS hx
    · rw [Finset.mem_singleton.mp hz]; exact hTS hy
  rcases hN Finset.univ (by simp) col with ⟨S, -, hS, hcol⟩ | ⟨S, -, hS, hcol⟩
  · refine ⟨S, hS, c1, fun T hTS hT => ?_⟩
    obtain ⟨x, hx, y, hy, hxy, hc⟩ := two c1 T hT
    have h := hcol {x, y} (pair_sub S T hTS x hx y hy) (Finset.card_pair hxy)
    simp only [col, decide_eq_true_eq] at h
    have h' := h x (by simp) y (by simp) hxy
    rw [hc] at h'
    exact absurd (congrArg Fin.val h') (by simp [c0, c1])
  · refine ⟨S, hS, c0, fun T hTS hT => ?_⟩
    obtain ⟨x, hx, y, hy, hxy, hc⟩ := two c0 T hT
    have h := hcol {x, y} (pair_sub S T hTS x hx y hy) (Finset.card_pair hxy)
    simp only [col, decide_eq_false_iff_not] at h
    apply h
    intro a ha b hb hab
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact absurd rfl hab
    · exact hc
    · rw [← hc]; exact congrArg χ (Subtype.ext Sym2.eq_swap)
    · exact absurd rfl hab

/-- If `C(N, n) · r · (r³ - 1)^{m²} < r^{3m²}` with `4m ≤ n`, then `N < R(n;3,r)`. -/
theorem lt_R {N n m r : ℕ} (hr : 2 ≤ r) (hm : 4 * m ≤ n)
    (h : N.choose n * r * (r ^ 3 - 1) ^ (m * m) < r ^ (3 * (m * m))) : N < R n 3 r := by
  have hmem := Nat.sInf_mem (R_set_nonempty n 3 r (by norm_num) hr)
  by_contra hle
  push Not at hle
  obtain ⟨χ, hχ⟩ := exists_colouring (N := R n 3 r) (by omega) hm
    (lt_of_le_of_lt (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _
      (Nat.choose_le_choose n hle))) h)
  obtain ⟨S, hS, c, hc⟩ := hmem χ
  obtain ⟨T, hTS, hT⟩ := hχ S hS c
  exact hc T hTS hT

/-! ### Arithmetic -/

/-- Bernoulli-type inequality `a^j (a + j) ≤ (a + 1)^j a`. -/
theorem pow_mul_add_le (a : ℕ) : ∀ j : ℕ, a ^ j * (a + j) ≤ (a + 1) ^ j * a
  | 0 => by simp
  | j + 1 => by
    have ih := pow_mul_add_le a j
    have h0 : 0 ≤ a ^ j * j := Nat.zero_le _
    rw [pow_succ, pow_succ]
    nlinarith

theorem two_mul_pow_self_le {a : ℕ} (ha : 1 ≤ a) : 2 * a ^ a ≤ (a + 1) ^ a := by
  have h := pow_mul_add_le a a
  have h' : (2 * a ^ a) * a ≤ (a + 1) ^ a * a := by linarith
  exact Nat.le_of_mul_le_mul_right h' ha

theorem two_pow_div_mul_pow_le {a : ℕ} (ha : 1 ≤ a) (M : ℕ) :
    2 ^ (M / a) * a ^ M ≤ (a + 1) ^ M := by
  have hM := Nat.div_add_mod M a
  calc 2 ^ (M / a) * a ^ M = (2 * a ^ a) ^ (M / a) * a ^ (M % a) := by
        rw [show a ^ M = (a ^ a) ^ (M / a) * a ^ (M % a) by rw [← pow_mul, ← pow_add, hM],
          mul_pow, mul_assoc]
    _ ≤ ((a + 1) ^ a) ^ (M / a) * (a + 1) ^ (M % a) :=
        Nat.mul_le_mul (Nat.pow_le_pow_left (two_mul_pow_self_le ha) _)
          (Nat.pow_le_pow_left (Nat.le_succ a) _)
    _ = (a + 1) ^ M := by
        conv_rhs => rw [← hM]
        rw [pow_add, pow_mul]

/-- **Girão's counterexample**, explicit form: for `r ≥ 2` and `n ≥ 8 (r³ - 1) + 12`,
`2 ^ ⌊n / (32 (r³ - 1))⌋ < R(n;3,r)`. -/
theorem two_pow_lt_R {r n : ℕ} (hr : 2 ≤ r) (hn : 8 * (r ^ 3 - 1) + 12 ≤ n) :
    2 ^ (n / (32 * (r ^ 3 - 1))) < R n 3 r := by
  set a := r ^ 3 - 1
  set t := n / (32 * a)
  set m := n / 4
  have hr3 : 8 ≤ r ^ 3 := by
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ r ^ 3 := Nat.pow_le_pow_left hr 3
  have ha7 : 7 ≤ a := by omega
  have ha1 : a + 1 = r ^ 3 := by omega
  have hra : r ≤ a := by
    have h4 : 4 ≤ r * r := by nlinarith
    have h3 : r ^ 3 = r * (r * r) := by ring
    have : r * 4 ≤ r * (r * r) := Nat.mul_le_mul_left r h4
    omega
  apply lt_R hr (m := m) (by omega)
  have htK : t * (32 * a) ≤ n := Nat.div_mul_le_self n _
  have hn4 : n ≤ 4 * m + 3 := by omega
  have hm : 2 * a + 3 ≤ m := by omega
  have hkey : (t * n + r) * a ≤ m * m := by
    have h1 : t * n * (32 * a) ≤ n * n := by nlinarith
    have h2 : n * n ≤ (4 * m + 3) * (4 * m + 3) := Nat.mul_le_mul hn4 hn4
    have h3 : r * a ≤ a * a := Nat.mul_le_mul_right a hra
    nlinarith
  have hdiv : t * n + r ≤ m * m / a := (Nat.le_div_iff_mul_le (by omega)).mpr hkey
  have hpos : 0 < a ^ (m * m) := by positivity
  calc (2 ^ t).choose n * r * a ^ (m * m)
      ≤ 2 ^ (t * n) * r * a ^ (m * m) := by
        refine Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ ?_)
        exact (Nat.choose_le_pow _ _).trans (by rw [← pow_mul])
    _ < 2 ^ (t * n) * 2 ^ r * a ^ (m * m) := by
        refine Nat.mul_lt_mul_of_pos_right ?_ hpos
        exact Nat.mul_lt_mul_of_pos_left (Nat.lt_two_pow_self) (by positivity)
    _ = 2 ^ (t * n + r) * a ^ (m * m) := by rw [pow_add]
    _ ≤ 2 ^ (m * m / a) * a ^ (m * m) :=
        Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by norm_num) hdiv)
    _ ≤ (a + 1) ^ (m * m) := two_pow_div_mul_pow_le (by omega) _
    _ = r ^ (3 * (m * m)) := by rw [ha1, ← pow_mul]

/-- **Girão's counterexample**: for every `r ≥ 2` there is `c > 1` with `R(n;3,r) ≥ c^n` for all
large `n` (here `c = 2^{1/(64 (r³ - 1))}`). -/
theorem girao_lower_bound (r : ℕ) (hr : 2 ≤ r) :
    ∃ c : ℝ, 1 < c ∧ ∀ᶠ n : ℕ in atTop, c ^ n ≤ (R n 3 r : ℝ) := by
  set K := 32 * (r ^ 3 - 1)
  have hr3 : 8 ≤ r ^ 3 := by
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ r ^ 3 := Nat.pow_le_pow_left hr 3
  have hK : 0 < K := by omega
  refine ⟨(2 : ℝ) ^ ((1 : ℝ) / (2 * K)), Real.one_lt_rpow (by norm_num) (by positivity),
    eventually_atTop.mpr ⟨8 * (r ^ 3 - 1) + 12 + 2 * K, fun n hn => ?_⟩⟩
  have hlt := two_pow_lt_R hr (n := n) (by omega)
  have hdiv : n < n / K * K + K := Nat.lt_div_mul_add hK
  have hnat : n ≤ 2 * K * (n / K) := by
    have : 2 * K ≤ n := by omega
    nlinarith
  have hreal : (1 : ℝ) / (2 * K) * n ≤ ((n / K : ℕ) : ℝ) := by
    rw [one_div_mul_eq_div, div_le_iff₀ (by positivity)]
    have : ((n : ℕ) : ℝ) ≤ ((2 * K * (n / K) : ℕ) : ℝ) := by exact_mod_cast hnat
    push_cast at this
    linarith
  calc ((2 : ℝ) ^ ((1 : ℝ) / (2 * K))) ^ n = (2 : ℝ) ^ ((1 : ℝ) / (2 * K) * n) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    _ ≤ (2 : ℝ) ^ ((n / K : ℕ) : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hreal
    _ = ((2 ^ (n / K) : ℕ) : ℝ) := by rw [Real.rpow_natCast]; push_cast; rfl
    _ ≤ (R n 3 r : ℝ) := by exact_mod_cast hlt.le

/-- For `c, C > 1`, eventually `C^{√n} < c^n`. -/
theorem eventually_rpow_sqrt_lt_pow {c C : ℝ} (hc : 1 < c) (hC : 1 < C) :
    ∀ᶠ n : ℕ in atTop, C ^ Real.sqrt n < c ^ n := by
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt C hc
  refine eventually_atTop.mpr ⟨k ^ 2 + 1, fun n hn => ?_⟩
  have hkn : ((k : ℝ)) ^ 2 < n := by exact_mod_cast (show k ^ 2 < n by omega)
  have hs : (k : ℝ) < Real.sqrt n := (Real.lt_sqrt (Nat.cast_nonneg k)).mpr hkn
  have hs0 : 0 < Real.sqrt n := lt_of_le_of_lt (Nat.cast_nonneg k) hs
  have hsq : Real.sqrt n * Real.sqrt n = n := Real.mul_self_sqrt (Nat.cast_nonneg n)
  calc C ^ Real.sqrt n < (c ^ k) ^ Real.sqrt n := Real.rpow_lt_rpow (by linarith) hk hs0
    _ = c ^ ((k : ℝ) * Real.sqrt n) := by
        rw [Real.rpow_mul (by linarith), Real.rpow_natCast]
    _ < c ^ (n : ℝ) := Real.rpow_lt_rpow_of_exponent_lt hc (by nlinarith)
    _ = c ^ n := Real.rpow_natCast c n

/-- **Erdős Problem 129 is false as written**, for each fixed `r ≥ 2`: there is no `C > 1` such
that `R(n;3,r) < C^{√n}`, not even for all sufficiently large `n`. -/
theorem erdos_129_disproof (r : ℕ) (hr : 2 ≤ r) :
    ¬ ∃ C : ℝ, 1 < C ∧ ∀ᶠ n : ℕ in atTop, (R n 3 r : ℝ) < C ^ Real.sqrt n := by
  rintro ⟨C, hC, hev⟩
  obtain ⟨c, hc, hlow⟩ := girao_lower_bound r hr
  obtain ⟨n, h1, h2, h3⟩ :=
    (hev.and (hlow.and (eventually_rpow_sqrt_lt_pow hc hC))).exists
  linarith

/-- **Erdős Problem 129**, the statement as written ("there is `C = C(r) > 1` such that
`R(n;3,r) < C^{√n}`"), is false. -/
theorem erdos_129 :
    ¬ ∀ r : ℕ, 2 ≤ r → ∃ C : ℝ, 1 < C ∧ ∀ n : ℕ, (R n 3 r : ℝ) < C ^ Real.sqrt n := by
  intro h
  obtain ⟨C, hC, hall⟩ := h 2 le_rfl
  exact erdos_129_disproof 2 le_rfl ⟨C, hC, Filter.Eventually.of_forall hall⟩

/-- The Erdős–Gyárfás lower bound, in the stronger form given by Girão's argument: for `r ≥ 2`
and every `C > 1`, eventually `C^{√n} < R(n;3,r)`. -/
theorem erdos_gyarfas_lower_bound (r : ℕ) (hr : 2 ≤ r) {C : ℝ} (hC : 1 < C) :
    ∀ᶠ n : ℕ in atTop, C ^ Real.sqrt n < (R n 3 r : ℝ) := by
  obtain ⟨c, hc, hlow⟩ := girao_lower_bound r hr
  filter_upwards [hlow, eventually_rpow_sqrt_lt_pow hc hC] with n h1 h2
  linarith

end Erdos129
