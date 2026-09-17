import Mathlib

/-!
# Erdős Problem 1178: the Brown–Erdős–Sós lower bound `d_r(e) ≥ (r-2)e+3`

Erdős Problem 1178 (https://www.erdosproblems.com/1178), a conjecture of Brown, Erdős and
Sós [BES73], reads:

> For `r ≥ 3` let `d_r(e)` be the minimal `d` such that `ex_r(n, 𝓕) = o(n²)`, where `𝓕` is the
> family of `r`-uniform hypergraphs on `d` vertices with `e` edges. Prove that
> `d_r(e) = (r-2)e+3` for all `r, e ≥ 3`.

Brown, Erdős and Sós proved the lower bound `d_r(e) ≥ (r-2)e+3`. This file formalizes that lower
bound for all `r, e ≥ 3`. It does **not** prove the upper bound `d_r(e) ≤ (r-2)e+3`, which is the
open part of the conjecture (known for `e = 3` by Erdős, Frankl and Rödl [EFR86], and for
`r = e = 3` by Ruzsa and Szemerédi [RuSz78]).

## Statements proved

* `erdos_1178_lower_bound`: for `r, e ≥ 3`, `(r - 2) * e + 3 ≤ d_r r e`.
* `erdos_1178_not_isSubquadratic`: for `r, e ≥ 3` and every `d ≤ (r-2)e+2`,
  `ex_r(n, 𝓕) = o(n²)` fails.
* `ex_lower_bound` (explicit form, for `r, e ≥ 2`): if `d ≤ (r-2)e+2` and `n ≥ 2r`, then
  `n² / besConst r e ≤ ex r d e n`, where
  `besConst r e = 4 (2^r r!)² e ((D+1) C(C(D,r),e) + 1)` with `D = (r-2)e+2`.

## Definitions and faithfulness

* `Hypergraph n = Finset (Finset (Fin n))`; `IsUniform r G` says every edge has `r` vertices.
* `ContainsCopy F G` (`F` on `Fin d`, `G` on `Fin n`): there is an injective vertex map
  `Fin d ↪ Fin n` sending every edge of `F` to an edge of `G`, i.e. `G` has a (not necessarily
  induced) subhypergraph isomorphic to `F`.
* `family r d e` is the set of `r`-uniform hypergraphs on the vertex set `Fin d` with exactly `e`
  edges, and `IsFamilyFree r d e G` says `G` contains no member of it.
* `ex r d e n` is the `sSup` of the edge numbers of `𝓕`-free `r`-uniform hypergraphs on `Fin n`.
  It is the true maximum: `card_le_ex` (every such hypergraph has at most `ex r d e n` edges) and
  `exists_card_eq_ex` (for `e ≥ 1` the value is attained).
* `IsSubquadratic r d e` is `(fun n => (ex r d e n : ℝ)) =o[atTop] (fun n => (n : ℝ) ^ 2)`, and
  `d_r r e = sInf {d | IsSubquadratic r d e}` is the least such `d`. The set is nonempty:
  `ex_le_of_mul_le` shows `ex r d e n ≤ e` once `d ≥ re` and `n ≥ d`, hence `d_r_le` gives
  `d_r r e ≤ r e`. So `sInf` is the minimum and not the junk value `0`.
* `family_nonempty`: at the critical value `d = (r-2)e+2` the family `𝓕` is nonempty, so the
  lower bound does not come from an empty forbidden family.
* The definitions were cross-checked against the statement-only file
  `Statements/Erdos1178BrownErdosSosThreshold.lean` of `WoshuaJolk/jig-verifier` (Apache-2.0,
  no proof). It uses the same encoding `Finset (Finset (Fin n))`, the same notion of copy and the
  same `o(n²)` threshold. `erdos_1178_not_isSubquadratic` is the second conjunct of that
  statement, with `ex` written as an `sSup` instead of a `Finset.sup`.

## Proof

Let `D = (r-2)e+2`, let `E` be the set of all `r`-subsets of `Fin n` and `N = |E| = C(n,r)`.

1. *Bad configurations* (`badConfigs`, `card_badConfigs_le`). Every set of `e` edges whose union
   has at most `D` vertices lies in `powersetCard e (powersetCard r U)` for some `U` with
   `|U| ≤ D`, so there are at most `A n^D` of them, `A = (D+1) C(C(D,r),e)`.
2. *Averaging* (`weight`, `sum_weight_mul_card`, `sum_weight_mul_card_filter`). Give `H ⊆ E` the
   weight `p^|H| (1-p)^(N-|H|)`; the weights sum to `1`, and the weight of the sets containing a
   fixed `B ⊆ E` is `p^|B|`. Hence the weighted average of `|H| - e·#(bad configurations inside H)`
   is `pN - e p^e #bad`, and some `H` is at least this large.
3. *Deletion* (`exists_sparse_of_weight`). Removing from `H` every edge of every bad configuration
   inside `H` leaves `G` with `|G| ≥ pN - e p^e #bad` in which any `e` edges span more than `D`
   vertices.
4. *Constants* (`exists_sparse`). With `x = n ≥ 2r`, `N ≥ x^r / (2^r r!)`,
   `c = 1 / (2 · 2^r r! · e (A+1))` and `p = c / x^(r-2)`, the exponents match
   (`(2-r)e + D = 2`), `c^e ≤ c²`, and `|G| ≥ x² / besConst r e`.
5. *Conclusion*. Such a `G` contains no `r`-uniform hypergraph on `d ≤ D` vertices with `e` edges
   (`isFamilyFree_of_spread`), so `ex r d e n ≥ n² / besConst r e` for `n ≥ 2r`, which is not
   `o(n²)`.

The result is due to Brown, Erdős and Sós [BES73]. The argument above is the standard deletion
method, written as an averaging argument over binomial weights. The Lean formalization was
written with AI assistance (Claude, Anthropic).

## References

* [BES73] W. G. Brown, P. Erdős and V. T. Sós, _Some extremal problems on r-graphs_, in New
  Directions in the Theory of Graphs (Proc. Third Ann Arbor Conf., 1971), Academic Press (1973),
  53–63.
* [RuSz78] I. Z. Ruzsa and E. Szemerédi, _Triple systems with no six points carrying three
  triangles_, Combinatorics (Proc. Fifth Hungarian Colloq., Keszthely, 1976), Vol. II (1978),
  939–945.
* [EFR86] P. Erdős, P. Frankl and V. Rödl, _The asymptotic number of graphs not containing a
  fixed subgraph and a problem for hypergraphs having no exponent_, Graphs Combin. 2 (1986),
  113–121.
* [erdosproblems.com/1178](https://www.erdosproblems.com/1178)
-/

open Finset Filter Asymptotics

namespace Erdos1178

section Problem

/-- A hypergraph on the vertex set `Fin n`: a finite set of edges, each edge a set of vertices. -/
abbrev Hypergraph (n : ℕ) := Finset (Finset (Fin n))

/-- `G` is `r`-uniform: every edge has exactly `r` vertices. -/
def IsUniform (r : ℕ) {n : ℕ} (G : Hypergraph n) : Prop := ∀ edge ∈ G, #edge = r

/-- `G` contains a copy of `F`, i.e. `F` is isomorphic to a (not necessarily induced)
subhypergraph of `G`: an injective vertex map sends every edge of `F` to an edge of `G`. -/
def ContainsCopy {d n : ℕ} (F : Hypergraph d) (G : Hypergraph n) : Prop :=
  ∃ f : Fin d ↪ Fin n, ∀ edge ∈ F, edge.map f ∈ G

/-- The family `𝓕` of all `r`-uniform hypergraphs on `d` vertices with `e` edges. -/
def family (r d e : ℕ) : Set (Hypergraph d) := {F | IsUniform r F ∧ #F = e}

/-- `G` contains no member of the family `𝓕` of `r`-uniform hypergraphs on `d` vertices with
`e` edges. -/
def IsFamilyFree (r d e : ℕ) {n : ℕ} (G : Hypergraph n) : Prop :=
  ∀ F ∈ family r d e, ¬ ContainsCopy F G

/-- `ex_r(n, 𝓕)`: the largest number of edges of an `r`-uniform hypergraph on `n` vertices that
contains no member of `𝓕`. -/
noncomputable def ex (r d e n : ℕ) : ℕ :=
  sSup {m | ∃ G : Hypergraph n, IsUniform r G ∧ IsFamilyFree r d e G ∧ #G = m}

/-- `ex_r(n, 𝓕) = o(n²)`. -/
def IsSubquadratic (r d e : ℕ) : Prop :=
  (fun n => (ex r d e n : ℝ)) =o[atTop] (fun n => (n : ℝ) ^ 2)

/-- `d_r(e)`: the least `d` such that `ex_r(n, 𝓕) = o(n²)`. -/
noncomputable def d_r (r e : ℕ) : ℕ := sInf {d | IsSubquadratic r d e}

theorem ex_bddAbove (r d e n : ℕ) :
    BddAbove {m | ∃ G : Hypergraph n, IsUniform r G ∧ IsFamilyFree r d e G ∧ #G = m} := by
  refine ⟨2 ^ n, ?_⟩
  rintro m ⟨G, -, -, rfl⟩
  simpa using card_le_univ G

/-- Every `𝓕`-free `r`-uniform hypergraph on `n` vertices has at most `ex r d e n` edges. -/
theorem card_le_ex {r d e n : ℕ} {G : Hypergraph n} (hu : IsUniform r G)
    (hf : IsFamilyFree r d e G) : #G ≤ ex r d e n :=
  le_csSup (ex_bddAbove r d e n) ⟨G, hu, hf, rfl⟩

/-- For `e ≥ 1` the maximum in `ex` is attained. -/
theorem exists_card_eq_ex (r d e n : ℕ) (he : 1 ≤ e) :
    ∃ G : Hypergraph n, IsUniform r G ∧ IsFamilyFree r d e G ∧ #G = ex r d e n := by
  have hfree : IsFamilyFree r d e (∅ : Hypergraph n) := by
    rintro F ⟨-, hF⟩ ⟨f, hf⟩
    obtain ⟨a, ha⟩ : F.Nonempty := card_pos.1 (by omega)
    simpa using hf a ha
  have hmem : 0 ∈ {m | ∃ G : Hypergraph n, IsUniform r G ∧ IsFamilyFree r d e G ∧ #G = m} :=
    ⟨∅, by simp [IsUniform], hfree, rfl⟩
  exact Nat.sSup_mem ⟨0, hmem⟩ (ex_bddAbove r d e n)

/-- If every `e` edges of `G` span more than `D` vertices, then `G` contains no `r`-uniform
hypergraph on `d ≤ D` vertices with `e` edges. -/
theorem isFamilyFree_of_spread {r d e n D : ℕ} {G : Hypergraph n}
    (hG : ∀ B ⊆ G, #B = e → D < #(B.biUnion id)) (hd : d ≤ D) : IsFamilyFree r d e G := by
  rintro F ⟨-, hFe⟩ ⟨f, hf⟩
  set B := F.map (mapEmbedding f).toEmbedding with hB
  have hBG : B ⊆ G := by
    intro b hb
    simp only [hB, Finset.mem_map, RelEmbedding.coe_toEmbedding, mapEmbedding_apply] at hb
    obtain ⟨a, ha, rfl⟩ := hb
    exact hf a ha
  have hBU : B.biUnion id ⊆ univ.map f := by
    intro x hx
    simp only [hB, mem_biUnion, Finset.mem_map, RelEmbedding.coe_toEmbedding, mapEmbedding_apply,
      id] at hx
    obtain ⟨b, ⟨a, -, rfl⟩, hx⟩ := hx
    obtain ⟨y, -, rfl⟩ := Finset.mem_map.1 hx
    exact mem_map_of_mem f (mem_univ y)
  have h1 := card_le_card hBU
  rw [card_map, card_univ, Fintype.card_fin] at h1
  have h2 := hG B hBG (by rw [hB, card_map, hFe])
  omega

/-- Conversely, `e` edges of an `r`-uniform `G` spanning at most `d ≤ n` vertices give a copy of a
member of `𝓕`. -/
theorem containsCopy_of_subset {r d e n : ℕ} {G : Hypergraph n} (hG : IsUniform r G)
    {B : Hypergraph n} (hBG : B ⊆ G) (hB : #B = e) (hU : #(B.biUnion id) ≤ d) (hdn : d ≤ n) :
    ∃ F ∈ family r d e, ContainsCopy F G := by
  obtain ⟨S, hUS, hS⟩ := exists_superset_card_eq (α := Fin n) (n := d) (s := B.biUnion id) hU
    (by simp [hdn])
  let f : Fin d ↪ Fin n := (S.orderEmbOfFin hS).toEmbedding
  have hrange : univ.map f = S := by
    apply coe_injective
    rw [coe_map, coe_univ, Set.image_univ]
    exact range_orderEmbOfFin S hS
  let F : Hypergraph d := {a ∈ (univ : Finset (Finset (Fin d))) | a.map f ∈ B}
  have hFB : F.map (mapEmbedding f).toEmbedding = B := by
    ext b
    simp only [F, Finset.mem_map, mem_filter, mem_univ, true_and, RelEmbedding.coe_toEmbedding,
      mapEmbedding_apply]
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact ha
    · intro hb
      have hbS : b ⊆ univ.map f := hrange ▸ fun x hx => hUS (mem_biUnion.2 ⟨b, hb, hx⟩)
      obtain ⟨u, -, rfl⟩ := subset_map_iff.1 hbS
      exact ⟨u, hb, rfl⟩
  refine ⟨F, ⟨fun a ha => ?_, ?_⟩, f, fun a ha => ?_⟩
  · have := hG _ (hBG (mem_filter.1 ha).2)
    rwa [card_map] at this
  · rw [← hB, ← hFB, card_map]
  · exact hBG (mem_filter.1 ha).2

/-- Once `d ≥ re`, any `e` edges span at most `d` vertices, so `ex r d e n ≤ e` for `n ≥ d`. -/
theorem ex_le_of_mul_le {r d e n : ℕ} (hd : r * e ≤ d) (hn : d ≤ n) : ex r d e n ≤ e := by
  refine csSup_le' ?_
  rintro m ⟨G, hGu, hGf, rfl⟩
  by_contra hlt
  rw [not_le] at hlt
  obtain ⟨B, hBG, hB⟩ := exists_subset_card_eq hlt.le
  have hU : #(B.biUnion id) ≤ d := by
    calc #(B.biUnion id) ≤ ∑ b ∈ B, #(id b) := card_biUnion_le
      _ = ∑ b ∈ B, r := sum_congr rfl fun b hb => hGu b (hBG hb)
      _ = r * e := by rw [sum_const, hB, smul_eq_mul, mul_comm]
      _ ≤ d := hd
  obtain ⟨F, hF, hFG⟩ := containsCopy_of_subset hGu hBG hB hU hn
  exact hGf F hF hFG

theorem isSubquadratic_of_mul_le {r d e : ℕ} (hd : r * e ≤ d) : IsSubquadratic r d e := by
  have h1 : (fun n => (ex r d e n : ℝ)) =O[atTop] (fun _ => (1 : ℝ)) := by
    refine IsBigO.of_bound e (eventually_atTop.2 ⟨d, fun n hn => ?_⟩)
    simp only [Real.norm_natCast, norm_one, mul_one]
    exact_mod_cast ex_le_of_mul_le hd hn
  refine h1.trans_isLittleO ((isLittleO_one_left_iff ℝ).2 ?_)
  simp only [norm_pow, Real.norm_natCast]
  exact (tendsto_pow_atTop two_ne_zero).comp tendsto_natCast_atTop_atTop

theorem d_r_le (r e : ℕ) : d_r r e ≤ r * e :=
  Nat.sInf_le (isSubquadratic_of_mul_le le_rfl)

theorem add_one_le_choose (a k : ℕ) : a + 1 ≤ (a + k + 1).choose (k + 1) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show a + (k + 1) + 1 = (a + k + 1) + 1 by ring, Nat.choose_succ_succ]
    omega

/-- At the critical value `d = (r-2)e+2` the family `𝓕` is nonempty (for `r ≥ 3`), so the lower
bound is not about an empty family of forbidden hypergraphs. -/
theorem family_nonempty (r e : ℕ) (hr : 3 ≤ r) : (family r ((r - 2) * e + 2) e).Nonempty := by
  have hc : e ≤ ((r - 2) * e + 2).choose r := by
    rcases Nat.eq_zero_or_pos e with rfl | he
    · exact Nat.zero_le _
    obtain ⟨s, rfl⟩ : ∃ s, r = s + 3 := ⟨r - 3, by omega⟩
    obtain ⟨t, rfl⟩ : ∃ t, e = t + 1 := ⟨e - 1, by omega⟩
    have h1 := add_one_le_choose ((s + 1) * t) (s + 2)
    have h2 : (s + 3 - 2) * (t + 1) + 2 = (s + 1) * t + (s + 2) + 1 := by
      rw [show s + 3 - 2 = s + 1 by omega]; ring
    rw [h2]
    calc t + 1 ≤ (s + 1) * t + 1 := by nlinarith
      _ ≤ _ := h1
  obtain ⟨F, hF, hFe⟩ := exists_subset_card_eq
    (s := powersetCard r (univ : Finset (Fin ((r - 2) * e + 2)))) (n := e) (by simpa using hc)
  exact ⟨F, fun a ha => (mem_powersetCard.1 (hF ha)).2, hFe⟩

end Problem

section Weights

variable {α : Type*}

/-- The binomial weight `p^|H| (1-p)^(|E|-|H|)` of a subset `H ⊆ E`. -/
def weight (E : Finset α) (p : ℝ) (H : Finset α) : ℝ := p ^ #H * (1 - p) ^ (#E - #H)

theorem sum_weight (E : Finset α) (p : ℝ) : ∑ H ∈ E.powerset, weight E p H = 1 := by
  simp only [weight]
  rw [sum_pow_mul_eq_add_pow]
  simp

theorem weight_nonneg (E : Finset α) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (H : Finset α) :
    0 ≤ weight E p H :=
  mul_nonneg (pow_nonneg hp0 _) (pow_nonneg (by linarith) _)

/-- The total weight of the subsets of `E` containing a fixed `B ⊆ E` is `p^|B|`. -/
theorem sum_weight_superset [DecidableEq α] (E B : Finset α) (hB : B ⊆ E) (p : ℝ) :
    ∑ H ∈ E.powerset with B ⊆ H, weight E p H = p ^ #B := by
  rw [Finset.sum_nbij' (fun H => H \ B) (fun H => H ∪ B)
    (g := fun H => weight (E \ B) p H * p ^ #B) (t := (E \ B).powerset)]
  · rw [← Finset.sum_mul, sum_weight, one_mul]
  · intro H hH
    simp only [mem_filter, mem_powerset] at hH
    simp only [mem_powerset]
    exact sdiff_subset_sdiff hH.1 le_rfl
  · intro H hH
    simp only [mem_powerset] at hH
    simp only [mem_filter, mem_powerset]
    exact ⟨union_subset (hH.trans sdiff_subset) hB, subset_union_right⟩
  · intro H hH
    simp only [mem_filter, mem_powerset] at hH
    exact sdiff_union_of_subset hH.2
  · intro H hH
    simp only [mem_powerset] at hH
    apply union_sdiff_cancel_right
    exact disjoint_of_subset_left hH sdiff_disjoint
  · intro H hH
    simp only [mem_filter, mem_powerset] at hH
    have hBH : #B ≤ #H := card_le_card hH.2
    have hHE : #H ≤ #E := card_le_card hH.1
    simp only [weight, card_sdiff_of_subset hH.2, card_sdiff_of_subset hB]
    rw [mul_right_comm, pow_sub_mul_pow p hBH]
    congr 2
    omega

/-- Linearity of expectation for the number of members of `S` contained in a random subset. -/
theorem sum_weight_mul_card_filter [DecidableEq α] (E : Finset α) (S : Finset (Finset α))
    (hS : ∀ B ∈ S, B ⊆ E) (p : ℝ) :
    ∑ H ∈ E.powerset, weight E p H * (#{B ∈ S | B ⊆ H} : ℝ) = ∑ B ∈ S, p ^ #B := by
  simp_rw [← sum_boole, mul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun B hB => ?_
  rw [← sum_weight_superset E B (hS B hB) p, sum_filter]
  simp

theorem sum_weight_mul_card [DecidableEq α] (E : Finset α) (p : ℝ) :
    ∑ H ∈ E.powerset, weight E p H * (#H : ℝ) = p * #E := by
  have h := sum_weight_mul_card_filter E (E.map ⟨fun x => {x}, singleton_injective⟩)
    (by simp) p
  have hc : ∀ H ∈ E.powerset,
      #{B ∈ E.map ⟨fun x => {x}, singleton_injective⟩ | B ⊆ H} = #H := by
    intro H hH
    rw [mem_powerset] at hH
    rw [filter_map, card_map]
    congr 1
    ext x
    simp only [mem_filter, Function.comp_apply, Function.Embedding.coeFn_mk, singleton_subset_iff]
    exact ⟨fun h => h.2, fun h => ⟨hH h, h⟩⟩
  rw [sum_congr rfl fun H hH => by rw [hc H hH]] at h
  rw [h]
  simp [mul_comm]

end Weights

section Configurations

variable {n : ℕ}

/-- Over-approximation of the "bad" configurations: `e`-sets of `r`-sets that all lie inside
some vertex set of size at most `D`. -/
def badConfigs (n r e D : ℕ) : Finset (Finset (Finset (Fin n))) :=
  (range (D + 1)).biUnion fun k =>
    (powersetCard k (univ : Finset (Fin n))).biUnion fun U => powersetCard e (powersetCard r U)

theorem mem_badConfigs {r e D : ℕ} {B : Finset (Finset (Fin n))}
    (hB : ∀ b ∈ B, #b = r) (hcard : #B = e) (hD : #(B.biUnion id) ≤ D) :
    B ∈ badConfigs n r e D := by
  simp only [badConfigs, mem_biUnion, mem_range, mem_powersetCard, subset_univ, true_and]
  refine ⟨#(B.biUnion id), by omega, B.biUnion id, rfl, fun b hb => ?_, hcard⟩
  rw [mem_powersetCard]
  exact ⟨fun x hx => mem_biUnion.2 ⟨b, hb, hx⟩, hB b hb⟩

theorem badConfigs_spec {r e D : ℕ} {B : Finset (Finset (Fin n))}
    (hB : B ∈ badConfigs n r e D) : B ⊆ powersetCard r univ ∧ #B = e := by
  simp only [badConfigs, mem_biUnion, mem_range, mem_powersetCard, subset_univ, true_and] at hB
  obtain ⟨k, -, U, -, hBU, hc⟩ := hB
  refine ⟨fun b hb => ?_, hc⟩
  have := hBU hb
  rw [mem_powersetCard] at this ⊢
  exact ⟨subset_univ _, this.2⟩

theorem card_badConfigs_le (r e D : ℕ) (hn : 1 ≤ n) :
    #(badConfigs n r e D) ≤ (D + 1) * n ^ D * (D.choose r).choose e := by
  calc #(badConfigs n r e D)
      ≤ ∑ k ∈ range (D + 1), #((powersetCard k (univ : Finset (Fin n))).biUnion
          fun U => powersetCard e (powersetCard r U)) := card_biUnion_le
    _ ≤ ∑ k ∈ range (D + 1), n ^ D * (D.choose r).choose e := by
        refine sum_le_sum fun k hk => ?_
        rw [mem_range] at hk
        calc _ ≤ ∑ U ∈ powersetCard k (univ : Finset (Fin n)),
                #(powersetCard e (powersetCard r U)) := card_biUnion_le
          _ ≤ ∑ U ∈ powersetCard k (univ : Finset (Fin n)), (D.choose r).choose e := by
              refine sum_le_sum fun U hU => ?_
              rw [mem_powersetCard] at hU
              rw [card_powersetCard, card_powersetCard, hU.2]
              exact Nat.choose_le_choose _ (Nat.choose_le_choose _ (by omega))
          _ = n.choose k * (D.choose r).choose e := by
              rw [sum_const, card_powersetCard, card_univ, Fintype.card_fin, smul_eq_mul]
          _ ≤ n ^ D * (D.choose r).choose e := by
              gcongr
              exact (Nat.choose_le_pow n k).trans (Nat.pow_le_pow_right hn (by omega))
    _ = (D + 1) * n ^ D * (D.choose r).choose e := by
        rw [sum_const, card_range, smul_eq_mul, mul_assoc]

end Configurations

section Construction

/-- The deletion step: from a subset `H` of all `r`-sets that is at least as good as the average
of the binomial weights, remove every edge lying in a bad configuration. -/
theorem exists_sparse_of_weight (n r e D : ℕ) (he : 1 ≤ e) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    ∃ G : Finset (Finset (Fin n)), G ⊆ powersetCard r univ ∧
      (∀ B ⊆ G, #B = e → D < #(B.biUnion id)) ∧
      p * (n.choose r) - e * p ^ e * #(badConfigs n r e D) ≤ #G := by
  set E : Finset (Finset (Fin n)) := powersetCard r univ with hE
  set S := badConfigs n r e D with hS
  have hEcard : #E = n.choose r := by simp [hE]
  let f : Finset (Finset (Fin n)) → ℝ := fun H => (#H : ℝ) - e * (#{B ∈ S | B ⊆ H} : ℝ)
  have hsum : ∑ H ∈ E.powerset, weight E p H * f H = p * (n.choose r) - e * p ^ e * #S := by
    have h1 := sum_weight_mul_card E p
    have h2 := sum_weight_mul_card_filter E S (fun B hB => (badConfigs_spec hB).1) p
    have h3 : ∑ B ∈ S, p ^ #B = #S * p ^ e := by
      rw [sum_congr rfl fun B hB => by rw [(badConfigs_spec hB).2], sum_const, nsmul_eq_mul]
    simp only [f, mul_sub, sum_sub_distrib, h1, hEcard]
    rw [sum_congr rfl fun H _ => mul_left_comm (weight E p H) (e : ℝ) _, ← mul_sum, h2, h3]
    ring
  obtain ⟨H, hH, hmax⟩ := E.powerset.exists_max_image f ⟨∅, empty_mem_powerset E⟩
  have hfH : p * (n.choose r) - e * p ^ e * #S ≤ f H := by
    rw [← hsum]
    calc ∑ H' ∈ E.powerset, weight E p H' * f H'
        ≤ ∑ H' ∈ E.powerset, weight E p H' * f H :=
          sum_le_sum fun H' hH' =>
            mul_le_mul_of_nonneg_left (hmax H' hH') (weight_nonneg E hp0 hp1 H')
      _ = f H := by rw [← sum_mul, sum_weight, one_mul]
  have hHE : H ⊆ E := mem_powerset.1 hH
  set X := {B ∈ S | B ⊆ H} with hX
  refine ⟨H \ X.biUnion id, sdiff_subset.trans hHE, ?_, ?_⟩
  · intro B hBG hB
    by_contra hlt
    rw [not_lt] at hlt
    have hBS : B ∈ S := mem_badConfigs
      (fun b hb => (mem_powersetCard.1 (hHE (sdiff_subset (hBG hb)))).2) hB hlt
    have hBX : B ∈ X := mem_filter.2 ⟨hBS, hBG.trans sdiff_subset⟩
    obtain ⟨b, hb⟩ : B.Nonempty := card_pos.1 (by omega)
    have hbG := hBG hb
    rw [Finset.mem_sdiff] at hbG
    exact hbG.2 (mem_biUnion.2 ⟨B, hBX, hb⟩)
  · have h1 : #H ≤ #(H \ X.biUnion id) + #(X.biUnion id) := card_le_card_sdiff_add_card
    have h2 : #(X.biUnion id) ≤ e * #X := by
      calc #(X.biUnion id) ≤ ∑ B ∈ X, #(id B) := card_biUnion_le
        _ = ∑ B ∈ X, e := sum_congr rfl fun B hB => (badConfigs_spec (mem_filter.1 hB).1).2
        _ = e * #X := by rw [sum_const, smul_eq_mul, mul_comm]
    have h3 : (#H : ℝ) ≤ #(H \ X.biUnion id) + e * #X := by
      exact_mod_cast h1.trans (by omega)
    have h4 : f H = #H - e * #X := rfl
    linarith

/-- The explicit constant `4 (2^r r!)² e ((D+1) C(C(D,r),e) + 1)` with `D = (r-2)e+2`. -/
def besConst (r e : ℕ) : ℕ :=
  4 * (2 ^ r * r.factorial) ^ 2 * e *
    (((r - 2) * e + 3) * (((r - 2) * e + 2).choose r).choose e + 1)

theorem exists_sparse (r e : ℕ) (hr : 2 ≤ r) (he : 2 ≤ e) (n : ℕ) (hn : 2 * r ≤ n) :
    ∃ G : Finset (Finset (Fin n)), G ⊆ powersetCard r univ ∧
      (∀ B ⊆ G, #B = e → (r - 2) * e + 2 < #(B.biUnion id)) ∧
      (n : ℝ) ^ 2 / besConst r e ≤ #G := by
  set D := (r - 2) * e + 2 with hD
  set A : ℕ := (D + 1) * (D.choose r).choose e with hA
  set Dc : ℝ := 2 ^ r * r.factorial with hDc
  set x : ℝ := (n : ℝ) with hx
  set q : ℝ := x ^ (r - 2) with hq
  set c : ℝ := 1 / (2 * Dc * e * (A + 1)) with hc
  set p : ℝ := c / q with hp
  have hx1 : 1 ≤ x := by rw [hx]; exact_mod_cast (show 1 ≤ n by omega)
  have hq1 : 1 ≤ q := one_le_pow₀ hx1
  have hq0 : 0 < q := by linarith
  have hDc1 : 1 ≤ Dc := by
    rw [hDc]
    exact one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by norm_num))
      (by exact_mod_cast Nat.one_le_iff_ne_zero.2 (Nat.factorial_ne_zero r))
  have he1 : (1 : ℝ) ≤ e := by exact_mod_cast (show 1 ≤ e by omega)
  have hA0 : (0 : ℝ) ≤ A := Nat.cast_nonneg _
  have hden : 1 ≤ 2 * Dc * e * (A + 1) :=
    one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le (by linarith) he1) (by linarith)
  have hc0 : 0 < c := by rw [hc]; positivity
  have hc1 : c ≤ 1 := by rw [hc]; exact div_le_one_of_le₀ (by linarith) (by linarith)
  have hp0 : 0 ≤ p := div_nonneg hc0.le hq0.le
  have hp1 : p ≤ 1 := div_le_one_of_le₀ (hc1.trans hq1) hq0.le
  obtain ⟨G, hG1, hG2, hG3⟩ := exists_sparse_of_weight n r e D (by omega) hp0 hp1
  refine ⟨G, hG1, hG2, le_trans ?_ hG3⟩
  have hxr : x ^ r = q * x ^ 2 := by rw [hq, ← pow_add]; congr 1; omega
  have hxD : x ^ D = q ^ e * x ^ 2 := by rw [hq, ← pow_mul, ← pow_add]
  have hN : x ^ r / Dc ≤ (n.choose r : ℝ) := by
    refine le_trans ?_ (Nat.pow_le_choose (α := ℝ) r n)
    have h2 : x ≤ 2 * ((n + 1 - r : ℕ) : ℝ) := by
      rw [hx]; exact_mod_cast (show n ≤ 2 * (n + 1 - r) by omega)
    have h3 : x ^ r ≤ 2 ^ r * ((n + 1 - r : ℕ) : ℝ) ^ r := by
      rw [← mul_pow]; exact pow_le_pow_left₀ (by linarith) h2 r
    rw [hDc, div_le_div_iff₀ (by positivity) (by positivity)]
    calc x ^ r * r.factorial ≤ 2 ^ r * ((n + 1 - r : ℕ) : ℝ) ^ r * r.factorial := by gcongr
      _ = _ := by ring
  have hBad : (#(badConfigs n r e D) : ℝ) ≤ A * x ^ D := by
    have := card_badConfigs_le (n := n) r e D (by omega)
    have h' : (D + 1) * n ^ D * (D.choose r).choose e = A * n ^ D := by rw [hA]; ring
    rw [h'] at this
    rw [hx]; exact_mod_cast this
  have key1 : c * x ^ 2 / Dc ≤ p * (n.choose r) := by
    calc c * x ^ 2 / Dc = p * (x ^ r / Dc) := by
          rw [hxr, hp]; field_simp
      _ ≤ p * (n.choose r) := mul_le_mul_of_nonneg_left hN hp0
  have key2 : e * p ^ e * #(badConfigs n r e D) ≤ c * x ^ 2 / (2 * Dc) := by
    calc e * p ^ e * #(badConfigs n r e D) ≤ e * p ^ e * (A * x ^ D) := by gcongr
      _ = e * A * c ^ e * x ^ 2 := by
          rw [hxD, hp, div_pow]; field_simp
      _ ≤ e * (A + 1) * c ^ 2 * x ^ 2 := by
          have h1 : c ^ e ≤ c ^ 2 := pow_le_pow_of_le_one hc0.le hc1 he
          have h2 : (e : ℝ) * A * c ^ e ≤ e * (A + 1) * c ^ 2 :=
            mul_le_mul (mul_le_mul_of_nonneg_left (by linarith) (by linarith)) h1
              (by positivity) (by positivity)
          exact mul_le_mul_of_nonneg_right h2 (by positivity)
      _ = c * x ^ 2 / (2 * Dc) := by
          rw [hc]; field_simp
  have hconst : (besConst r e : ℝ) = 4 * Dc ^ 2 * e * (A + 1) := by
    simp only [besConst, hDc, hA, hD]
    push_cast
    ring
  have hfinal : x ^ 2 / besConst r e = c * x ^ 2 / Dc - c * x ^ 2 / (2 * Dc) := by
    rw [hconst, hc]; field_simp; ring
  rw [hfinal]
  linarith

end Construction

section Main

theorem besConst_pos (r e : ℕ) (he : 1 ≤ e) : 0 < besConst r e := by
  unfold besConst
  have := Nat.factorial_pos r
  exact Nat.mul_pos (Nat.mul_pos (by positivity) (by omega)) (by omega)

/-- Brown–Erdős–Sós, explicit form: for `d ≤ (r-2)e+2` and `n ≥ 2r`,
`ex_r(n, 𝓕) ≥ n² / besConst r e`. -/
theorem ex_lower_bound (r e : ℕ) (hr : 2 ≤ r) (he : 2 ≤ e) {d : ℕ} (hd : d ≤ (r - 2) * e + 2)
    {n : ℕ} (hn : 2 * r ≤ n) : (n : ℝ) ^ 2 / besConst r e ≤ ex r d e n := by
  obtain ⟨G, hG1, hG2, hG3⟩ := exists_sparse r e hr he n hn
  refine hG3.trans ?_
  exact_mod_cast card_le_ex (r := r) (d := d) (e := e)
    (fun a ha => (mem_powersetCard.1 (hG1 ha)).2) (isFamilyFree_of_spread hG2 hd)

theorem not_isSubquadratic (r e : ℕ) (hr : 2 ≤ r) (he : 2 ≤ e) {d : ℕ}
    (hd : d ≤ (r - 2) * e + 2) : ¬ IsSubquadratic r d e := by
  intro h
  have hC : (0 : ℝ) < besConst r e := by exact_mod_cast besConst_pos r e (by omega)
  obtain ⟨n, hn1, hn2⟩ :=
    ((h.def (c := 1 / (2 * besConst r e)) (by positivity)).and (eventually_ge_atTop (2 * r))).exists
  have hlow := ex_lower_bound r e hr he hd hn2
  simp only [Real.norm_natCast, norm_pow] at hn1
  have hn : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hy : 0 < (n : ℝ) ^ 2 / besConst r e := by positivity
  have : 1 / (2 * (besConst r e : ℝ)) * (n : ℝ) ^ 2 = (n : ℝ) ^ 2 / besConst r e / 2 := by
    field_simp
  linarith

/-- **Erdős Problem 1178, Brown–Erdős–Sós lower bound**, in the form "not `o(n²)`": for
`r, e ≥ 3` and every `d ≤ (r-2)e+2`, `ex_r(n, 𝓕) = o(n²)` fails. -/
theorem erdos_1178_not_isSubquadratic (r e : ℕ) (hr : 3 ≤ r) (he : 3 ≤ e) :
    ∀ d ≤ (r - 2) * e + 2, ¬ IsSubquadratic r d e :=
  fun _ hd => not_isSubquadratic r e (by omega) (by omega) hd

/-- **Erdős Problem 1178, Brown–Erdős–Sós lower bound**: `d_r(e) ≥ (r-2)e+3` for all
`r, e ≥ 3`. -/
theorem erdos_1178_lower_bound (r e : ℕ) (hr : 3 ≤ r) (he : 3 ≤ e) : (r - 2) * e + 3 ≤ d_r r e := by
  refine le_csInf ⟨r * e, isSubquadratic_of_mul_le le_rfl⟩ fun d hd => ?_
  by_contra hlt
  exact not_isSubquadratic r e (by omega) (by omega) (by omega) hd

end Main

end Erdos1178
