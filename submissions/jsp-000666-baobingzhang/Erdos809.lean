import Mathlib

/-!
# Erdős Problem 809 for `k ≥ 4`: `χ_S(n, ⌊n²/4⌋ + 1, C_{2k+1}) ∼ n²/8`

For a graph `H`, `χ_S(n, e, H)` is the smallest `r` such that there is a graph with `n` vertices
and `e` edges with an `r`-colouring of its edges in which every copy of `H` has pairwise distinct
edge colours. Erdős Problem 809 (Burr, Erdős, Graham and Sós) asks whether
`χ_S(n, ⌊n²/4⌋ + 1, C_{2k+1}) ∼ n²/8` for every `k ≥ 3`. Bucić, Chen and Ma [BCM26] proved this
for all `k ≥ 4`; the case `k = 3` is still open and is not treated here.

## Statement

* `AllCopiesRainbow H G col`: for every copy `f : H.Copy G` (an injective graph homomorphism, so a
  not necessarily induced subgraph of `G`), the colouring `col : G.edgeSet → α` is injective on the
  edges of the copy.
* `chiS n e H`: the infimum of all `r` for which some `G : SimpleGraph (Fin n)` with exactly `e`
  edges (`G.edgeSet.ncard = e`) has a colouring `col : G.edgeSet → Fin r` with
  `AllCopiesRainbow H G col`.
* `erdos_809 k hk`: for `k ≥ 4`, `χ_S(n, ⌊n²/4⌋ + 1, C_{2k+1}) / n² → 1/8` as `n → ∞`, where
  `C_{2k+1}` is Mathlib's `SimpleGraph.cycleGraph (2 * k + 1)` and `⌊n²/4⌋` is `n ^ 2 / 4` in `ℕ`.
* `erdos_809_isEquivalent k hk`: the same statement in the form `χ_S ∼ n²/8`
  (`Asymptotics.IsEquivalent`).
* `chiS_attained`: for `n ≥ 64` the defining set is nonempty, so `chiS` is attained by an actual
  graph and colouring (the value is not a default value of `sInf`).

## Proof

The proof follows [BCM26].

* **Upper bound** (`upper_mem`): two disjoint cliques on `a = ⌊n/2⌋ + ⌊√n⌋ + 2` and `n - a`
  vertices have at least `⌊n²/4⌋ + 1` edges; a subgraph with exactly that many edges is kept. Edges
  of each clique get distinct colours from a palette of `C(a, 2)` colours shared by both cliques.
  Every cycle lies inside one clique, so all cycles are rainbow.
* **Lower bound** (`lower_induction`): with `ε = 1/x` (`x ≥ 100`) and `C = (1000 k x³)²`, every
  colouring of `G[W]` in which all `C_{2k+1}` are rainbow uses at least
  `g(n, e) = e/2 + (n/2)√(e - n²/4) - εn² - C` colours, where `n = |W|` and `e = e(G[W]) > n²/4`.
  The proof is by induction on `W`. Deleting a vertex of minimum degree `δ` settles the step
  unless `δ > n/2 - √(e - n²/4) - 1/2` (`delta_bound_A`). If `e - δ ≤ (n-1)²/4` the inductive
  hypothesis does not apply, but then `δ ≥ n/2 - 1/4 + (e - n²/4)`, which already gives the
  degree bounds used below.
  * *Case 1*, `√(e - n²/4) ≥ εn/4`. Then `δ > n/2 - √(e - n²/4) + c` (`delta_bound_B`). Lemma 3.2
    of [BCM26] (`path4_adj`, `path4`, `path4_avoid`) joins any two vertices by a path with exactly
    four edges avoiding any `2k - 4` vertices. Lemma 3.1 (`dist3_set`) gives a set `A` of at least
    `n/2 + √(e - n²/4)` vertices at pairwise distance `≤ 3`. Any two edges meeting `A` lie on a
    common `C_{2k+1}` (`case1_connector`, `case1_pair`), and counting them gives the bound
    (`case1_count`, `case1_final`).
  * *Case 2*, `√(e - n²/4) < εn/4`. Then `δ > n/2 - εn/4 - 1/2`. Claim 1 of [BCM26] (`claim1`)
    either gives paths with two or three edges between any two vertices avoiding any `5k`
    vertices, or a dense set `Y` in which any two edges lie on a common `C_{2k+1}`
    (`dense_edges`). In the first case, instead of the book theorem of Edwards and
    Khadžiivanov–Nikiforov used in [BCM26], we use Mantel's theorem (`mantel`) to find a triangle.
    Because the minimum degree is close to `n/2`, one edge `pq` of the triangle has at least
    `δ - n/3` common neighbours (`triangle_book`), which is enough here. The three configurations
    of two good edges (`case2_shared`, `case2_disj1`, `case2_disj2`) use a common neighbour of `p`
    and `q` as a parity adjuster. Counting the good edges gives the bound (`case2_count`,
    `case2_final`).
  Both cases use the greedy path lemma (`greedy`). The inequality in the proof of Lemma 3.2 that
  [BCM26] reduce to `(|A| - 2)(δ₁ - 3) ≥ 0` is handled here using the slack in the final estimate
  (`P4Setup.A_bound`), so `δ₁ ≥ 3` is not needed.

Cycles are handled as lists of distinct vertices (`IsPathL`), and `cycRainbow_of_copies` turns a
cycle list into a `SimpleGraph.Copy` of `cycleGraph (2k + 1)`. All vertex sets are `Finset`s inside
one ambient graph; `dW G W v` and `sdeg G W` are degrees and the degree sum in `G[W]`.

## References

* [BCM26] M. Bucić, K. Chen, J. Ma, _On a maximal anti-Ramsey conjecture of Burr, Erdős, Graham,
  and Sós_, arXiv:2603.18952 (2026).
* [BEGS89] S. A. Burr, P. Erdős, R. L. Graham, V. T. Sós, _Maximal antiramsey graphs and the strong
  chromatic number_, J. Graph Theory 13 (1989), 263–282.
* [erdosproblems.com/809](https://www.erdosproblems.com/809)
-/

open Finset

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.deprecated false

namespace Erdos809

section Statement

/-- Every copy of `H` in `G` is rainbow under the edge colouring `col`: distinct edges of the
copy get distinct colours. A copy is an injective graph homomorphism `H → G` (a not necessarily
induced subgraph), and `f.mapEdgeSet` sends the edges of `H` to the corresponding edges of `G`. -/
def AllCopiesRainbow {U V α : Type*} (H : SimpleGraph U) (G : SimpleGraph V)
    (col : G.edgeSet → α) : Prop :=
  ∀ f : H.Copy G, Function.Injective (col ∘ f.mapEdgeSet)

/-- `χ_S(n, e, H)` from erdosproblems.com/809: the least `r` such that some graph with `n`
vertices and `e` edges has an `r`-colouring of its edges in which every copy of `H` is rainbow. -/
noncomputable def chiS {U : Type*} (n e : ℕ) (H : SimpleGraph U) : ℕ :=
  sInf {r : ℕ | ∃ G : SimpleGraph (Fin n), G.edgeSet.ncard = e ∧
    ∃ col : G.edgeSet → Fin r, AllCopiesRainbow H G col}

end Statement


section Basic

variable {V : Type*} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The neighbours of `v` inside the vertex set `W`. -/
def nbW (W : Finset V) (v : V) : Finset V := W.filter (G.Adj v)

/-- The degree of `v` inside `W`. -/
def dW (W : Finset V) (v : V) : ℕ := (nbW G W v).card

/-- The degree sum of `G[W]` (twice its number of edges). -/
def sdeg (W : Finset V) : ℕ := ∑ v ∈ W, dW G W v

/-- A list of distinct vertices, consecutive ones adjacent. -/
def IsPathL (l : List V) : Prop := l.Nodup ∧ l.IsChain G.Adj

/-- List form of "every copy of `C_m` is rainbow": two edges that occur consecutively in a
cycle list get equal colours only if they are equal. -/
def CycRainbow {α : Type*} (col : Sym2 V → α) (m : ℕ) : Prop :=
  ∀ l : List V, IsPathL G l → l.length = m → (∀ a ∈ l.head?, ∀ b ∈ l.getLast?, G.Adj b a) →
    ∀ x y z w, [x, y] <:+: l ++ l.take 1 → [z, w] <:+: l ++ l.take 1 →
      col s(x, y) = col s(z, w) → s(x, y) = s(z, w)

variable {G}

@[simp] lemma mem_nbW {W : Finset V} {v u : V} : u ∈ nbW G W v ↔ u ∈ W ∧ G.Adj v u := by
  simp [nbW]

lemma nbW_subset (W : Finset V) (v : V) : nbW G W v ⊆ W := filter_subset _ _

lemma dW_le (W : Finset V) (v : V) (hv : v ∈ W) : dW G W v + 1 ≤ W.card := by
  unfold dW
  have : nbW G W v ⊆ W.erase v := by
    intro u hu
    rw [mem_nbW] at hu
    exact mem_erase.2 ⟨fun h => G.irrefl (h ▸ hu.2), hu.1⟩
  have := card_le_card this
  rw [card_erase_of_mem hv] at this
  have : 1 ≤ W.card := card_pos.2 ⟨v, hv⟩
  omega

lemma sdeg_erase (W : Finset V) (v : V) (hv : v ∈ W) :
    sdeg G (W.erase v) + 2 * dW G W v = sdeg G W := by
  unfold sdeg
  have h1 : ∀ u ∈ W.erase v, dW G (W.erase v) u + (if G.Adj u v then 1 else 0) = dW G W u := by
    intro u hu
    unfold dW nbW
    rw [filter_erase]
    by_cases h : G.Adj u v
    · rw [if_pos h, card_erase_of_mem (mem_filter.2 ⟨hv, h⟩)]
      have : 0 < (W.filter (G.Adj u)).card := card_pos.2 ⟨v, mem_filter.2 ⟨hv, h⟩⟩
      omega
    · rw [if_neg h, erase_eq_of_notMem (fun hm => h (mem_filter.1 hm).2)]
      simp
  have h2 : ∑ u ∈ W.erase v, (if G.Adj u v then 1 else 0) = dW G W v := by
    rw [sum_boole]
    unfold dW nbW
    norm_cast
    congr 1
    ext u
    simp only [mem_filter, mem_erase]
    constructor
    · rintro ⟨⟨_, hu⟩, h⟩; exact ⟨hu, h.symm⟩
    · rintro ⟨hu, h⟩; exact ⟨⟨fun e => G.irrefl (e ▸ h), hu⟩, h.symm⟩
  have h3 : ∑ u ∈ W.erase v, dW G W u + dW G W v = ∑ u ∈ W, dW G W u :=
    sum_erase_add W _ hv
  have h4 : dW G W v = dW G W v := rfl
  rw [← h3, ← sum_congr rfl h1, sum_add_distrib, h2]
  ring

lemma sdeg_le (W : Finset V) : sdeg G W + W.card ≤ W.card * W.card := by
  unfold sdeg
  have : ∑ v ∈ W, (dW G W v + 1) ≤ ∑ _v ∈ W, W.card := sum_le_sum fun v hv => dW_le W v hv
  simpa [sum_add_distrib] using this

/-- Unordered pairs coming from a set of ordered pairs: at most two-to-one. -/
lemma card_le_two_mul_image (T : Finset (V × V)) :
    T.card ≤ 2 * (T.image (fun p => s(p.1, p.2))).card := by
  apply card_le_mul_card_image
  intro b _
  induction b using Sym2.ind with
  | _ a c =>
    calc (T.filter (fun p => s(p.1, p.2) = s(a, c))).card ≤ ({(a, c), (c, a)} : Finset (V × V)).card := by
          apply card_le_card
          intro p hp
          rw [mem_filter] at hp
          rcases Sym2.eq_iff.1 hp.2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · simp [Prod.ext_iff, h1, h2]
          · simp [Prod.ext_iff, h1, h2]
      _ ≤ 2 := card_le_two

lemma card_le_of_injOn_col {r : ℕ} (col : Sym2 V → Fin r) (E : Finset (Sym2 V))
    (h : ∀ e₁ ∈ E, ∀ e₂ ∈ E, col e₁ = col e₂ → e₁ = e₂) : E.card ≤ r := by
  have := card_le_card_of_injOn col (t := (univ : Finset (Fin r))) (fun _ _ => mem_coe.2 (mem_univ _))
    (fun a ha b hb hab => h a ha b hb hab)
  simpa using this

lemma IsPathL.append {l₁ l₂ : List V} (h₁ : IsPathL G l₁) (h₂ : IsPathL G l₂)
    (hd : ∀ v ∈ l₂, v ∉ l₁) (ha : ∀ a ∈ l₁.getLast?, ∀ b ∈ l₂.head?, G.Adj a b) :
    IsPathL G (l₁ ++ l₂) :=
  ⟨List.nodup_append.2 ⟨h₁.1, h₂.1, fun a ha b hb e => hd b hb (e ▸ ha)⟩,
    List.isChain_append.2 ⟨h₁.2, h₂.2, ha⟩⟩

lemma IsPathL.cons {v : V} {l : List V} (h : IsPathL G l) (hv : v ∉ l)
    (ha : ∀ b ∈ l.head?, G.Adj v b) : IsPathL G (v :: l) := by
  have := IsPathL.append (l₁ := [v]) (l₂ := l) ⟨List.nodup_singleton v, List.isChain_singleton v⟩ h
    (fun u hu e => hv (by simp at e; exact e ▸ hu)) (by simpa using ha)
  simpa using this

lemma IsPathL.sublist {l₁ l₂ : List V} (h : IsPathL G l₂) (hs : l₁ <:+: l₂) : IsPathL G l₁ :=
  ⟨h.1.sublist hs.sublist, h.2.infix hs⟩

lemma IsPathL.reverse {l : List V} (h : IsPathL G l) : IsPathL G l.reverse :=
  ⟨List.nodup_reverse.2 h.1, List.isChain_reverse.2 (h.2.imp fun _ _ h => h.symm)⟩

/-- Greedy path lemma: if all degrees in `W` are at least `D`, a path with `L` further vertices
starts at any `v ∈ W` and avoids any `T` with `|T| + L ≤ D`. -/
lemma greedy (W : Finset V) (D : ℕ) (hD : ∀ u ∈ W, D ≤ dW G W u) :
    ∀ (L : ℕ) (v : V) (T : Finset V), v ∈ W → T.card + L ≤ D →
      ∃ l : List V, l.length = L ∧ IsPathL G (v :: l) ∧ ∀ u ∈ l, u ∈ W ∧ u ∉ T := by
  intro L
  induction L with
  | zero => intro v T _ _; exact ⟨[], rfl, ⟨List.nodup_singleton v, List.isChain_singleton v⟩, by simp⟩
  | succ L ih =>
    intro v T hv hT
    have hlt : (nbW G W v ∩ T).card < (nbW G W v).card := by
      have := card_le_card (inter_subset_right : nbW G W v ∩ T ⊆ T)
      have := hD v hv
      unfold dW at this
      omega
    obtain ⟨v₁, hv₁, hv₁T⟩ := exists_mem_notMem_of_card_lt_card hlt
    have hv₁' : v₁ ∈ W ∧ G.Adj v v₁ := mem_nbW.1 hv₁
    have hv₁T' : v₁ ∉ T := fun h => hv₁T (mem_inter.2 ⟨hv₁, h⟩)
    obtain ⟨l, hl, hp, hlT⟩ := ih v₁ (insert v T) hv₁'.1 (by
      have := card_insert_le v T; omega)
    refine ⟨v₁ :: l, by simp [hl], ?_, ?_⟩
    · refine hp.cons ?_ (by simpa using hv₁'.2)
      intro hm
      rcases List.mem_cons.1 hm with h | h
      · exact G.irrefl (h ▸ hv₁'.2)
      · exact (hlT v h).2 (mem_insert_self v T)
    · intro u hu
      rcases List.mem_cons.1 hu with h | h
      · exact h ▸ ⟨hv₁'.1, hv₁T'⟩
      · exact ⟨(hlT u h).1, fun hh => (hlT u h).2 (mem_insert_of_mem hh)⟩

end Basic

section Cycle

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}

lemma getElem_closed {l : List V} {m : ℕ} (hl : l.length = m) (hm : 0 < m) (q : ℕ)
    (hq : q < m + 1) :
    (l ++ l.take 1)[q]'(by simp [hl]; omega) = l[q % m]'(by rw [hl]; exact Nat.mod_lt _ hm) := by
  rcases Nat.lt_or_ge q m with h | h
  · rw [List.getElem_append_left (by omega)]
    simp [Nat.mod_eq_of_lt h]
  · have hqm : q = m := by omega
    subst hqm
    rw [List.getElem_append_right (by omega)]
    simp [hl]

lemma fin_succ_of_sub {m : ℕ} (i j : Fin m) (h : ((j - i : Fin m) : ℕ) = 1) :
    (j : ℕ) = ((i : ℕ) + 1) % m := by
  have hi := i.isLt
  have hj := j.isLt
  rcases le_or_gt i j with hij | hij
  · rw [Fin.coe_sub_iff_le.2 hij] at h
    rw [Nat.mod_eq_of_lt (by omega)]
    omega
  · rw [Fin.coe_sub_iff_lt.2 hij] at h
    have h1 : (i : ℕ) + 1 = m := by omega
    rw [h1, Nat.mod_self]
    omega

lemma cycRainbow_of_copies {α : Type*} [DecidableRel G.Adj] (col₀ : G.edgeSet → α)
    (col : Sym2 V → α) (hext : ∀ z (hz : z ∈ G.edgeSet), col z = col₀ ⟨z, hz⟩) (m : ℕ)
    (hm : 3 ≤ m) (h : AllCopiesRainbow (SimpleGraph.cycleGraph m) G col₀) :
    CycRainbow G col m := by
  intro l hp hl hclose x y z w hxy hzw hcol
  have hm0 : 0 < m := by omega
  -- adjacency along `l ++ l.take 1`
  have hchain : (l ++ l.take 1).IsChain G.Adj := by
    refine List.isChain_append.2 ⟨hp.2, ?_, ?_⟩
    · rcases l with _ | ⟨a, l⟩
      · simp
      · simp
    · intro b hb a ha
      rcases l with _ | ⟨c, l⟩
      · simp at hb
      · simp only [List.take_succ_cons, List.take_zero, List.head?_cons, Option.mem_def,
          Option.some.injEq] at ha
        subst ha
        exact hclose c (by simp) b hb
  have hadj : ∀ p (hp : p + 1 < m + 1), G.Adj ((l ++ l.take 1)[p]'(by simp [hl]; omega))
      ((l ++ l.take 1)[p + 1]'(by simp [hl]; omega)) :=
    fun p hp' => hchain.getElem p (by simp [hl]; omega)
  let f : Fin m → V := fun i => l[(i : ℕ)]'(by rw [hl]; exact i.isLt)
  have hfclosed : ∀ q (hq : q < m + 1), f ⟨q % m, Nat.mod_lt _ hm0⟩ =
      (l ++ l.take 1)[q]'(by simp [hl]; omega) := fun q hq => (getElem_closed hl hm0 q hq).symm
  have hinj : Function.Injective f := by
    intro i j hij
    exact Fin.ext ((List.Nodup.getElem_inj_iff hp.1).1 hij)
  have hmap : ∀ i j : Fin m, (SimpleGraph.cycleGraph m).Adj i j → G.Adj (f i) (f j) := by
    have key : ∀ i j : Fin m, ((j - i : Fin m) : ℕ) = 1 → G.Adj (f i) (f j) := by
      intro i j hji
      have hj := fin_succ_of_sub i j hji
      have e1 : f j = (l ++ l.take 1)[(i : ℕ) + 1]'(by simp [hl]; omega) := by
        rw [← hfclosed _ (by omega)]
        congr 1
        exact Fin.ext hj
      have e2 : f i = (l ++ l.take 1)[(i : ℕ)]'(by simp [hl]; omega) := by
        rw [← hfclosed _ (by omega)]
        congr 1
        exact Fin.ext (Nat.mod_eq_of_lt i.isLt).symm
      rw [e1, e2]
      exact hadj _ (by omega)
    intro i j hij
    rcases SimpleGraph.cycleGraph_adj'.1 hij with h1 | h1
    · exact (key j i h1).symm
    · exact key i j h1
  let F : (SimpleGraph.cycleGraph m).Copy G := ⟨⟨f, fun {a b} hab => hmap a b hab⟩, hinj⟩
  -- edges of the cycle graph
  have hedge : ∀ p (hp : p < m), s((⟨p, hp⟩ : Fin m), (⟨(p + 1) % m, Nat.mod_lt _ hm0⟩ : Fin m)) ∈
      (SimpleGraph.cycleGraph m).edgeSet := by
    intro p hp'
    rw [SimpleGraph.mem_edgeSet, SimpleGraph.cycleGraph_adj']
    right
    rcases Nat.lt_or_ge (p + 1) m with h1 | h1
    · have hle : (⟨p, hp'⟩ : Fin m) ≤ ⟨(p + 1) % m, Nat.mod_lt _ hm0⟩ := by
        rw [Fin.le_def]; simp [Nat.mod_eq_of_lt h1]
      rw [Fin.coe_sub_iff_le.2 hle]
      simp [Nat.mod_eq_of_lt h1]
    · have h2 : p + 1 = m := by omega
      have hlt : (⟨(p + 1) % m, Nat.mod_lt _ hm0⟩ : Fin m) < ⟨p, hp'⟩ := by
        rw [Fin.lt_def]; simp [h2]; omega
      rw [Fin.coe_sub_iff_lt.2 hlt]
      simp [h2]
      omega
  have hinfix : ∀ a b, [a, b] <:+: l ++ l.take 1 → ∃ p, ∃ hp : p < m,
      s(a, b) = Sym2.map F s((⟨p, hp⟩ : Fin m), (⟨(p + 1) % m, Nat.mod_lt _ hm0⟩ : Fin m)) := by
    intro a b hab
    obtain ⟨p, hp1, hp2⟩ := List.infix_iff_getElem?.1 hab
    simp only [List.length_cons, List.length_nil, List.length_append, List.length_take, hl] at hp1
    have hlen : (l ++ l.take 1).length = m + 1 := by simp [hl]; omega
    have ha := hp2 0 (by simp)
    have hb := hp2 1 (by simp)
    simp only [zero_add, List.getElem_cons_zero, List.getElem_cons_succ] at ha hb
    rw [List.getElem?_eq_getElem (by omega)] at ha
    rw [add_comm 1 p, List.getElem?_eq_getElem (by omega)] at hb
    refine ⟨p, by omega, ?_⟩
    rw [Sym2.map_mk]
    have e1 : F ⟨p, by omega⟩ = a := by
      have := hfclosed p (by omega)
      have e : (⟨p % m, Nat.mod_lt _ hm0⟩ : Fin m) = ⟨p, by omega⟩ :=
        Fin.ext (Nat.mod_eq_of_lt (by omega : p < m))
      rw [e] at this
      exact this.trans (Option.some.inj ha)
    have e2 : F ⟨(p + 1) % m, Nat.mod_lt _ hm0⟩ = b := by
      have := hfclosed (p + 1) (by omega)
      exact this.trans (Option.some.inj hb)
    rw [e1, e2]
  obtain ⟨p, hp', hpe⟩ := hinfix x y hxy
  obtain ⟨q, hq', hqe⟩ := hinfix z w hzw
  have hmem : ∀ e (he : e ∈ (SimpleGraph.cycleGraph m).edgeSet),
      col (Sym2.map F e) = (col₀ ∘ F.mapEdgeSet) ⟨e, he⟩ := by
    intro e he
    exact hext _ _
  have key := h F (a₁ := ⟨_, hedge p hp'⟩) (a₂ := ⟨_, hedge q hq'⟩) (by
    rw [← hmem, ← hmem, ← hpe, ← hqe]; exact hcol)
  rw [hpe, hqe]
  exact congrArg (fun e : (SimpleGraph.cycleGraph m).edgeSet => Sym2.map F e.1) key

end Cycle

section Book

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

lemma sum_nbW_swap (W : Finset V) (g : V → ℕ) :
    ∑ u ∈ W, ∑ v ∈ nbW G W u, g v = ∑ v ∈ W, dW G W v * g v := by
  rw [Finset.sum_comm' (t' := W) (s' := fun v => nbW G W v)]
  · apply sum_congr rfl
    intro v _
    rw [sum_const, smul_eq_mul]
    rfl
  · intro u v
    simp only [mem_nbW]
    constructor
    · rintro ⟨hu, hv, h⟩; exact ⟨⟨hu, h.symm⟩, hv⟩
    · rintro ⟨⟨hu, h⟩, hv⟩; exact ⟨hu, hv, h.symm⟩

/-- Mantel's theorem inside `W`: more than `|W|²/4` edges force a triangle. -/
lemma mantel (W : Finset V) (h : W.card * W.card < 2 * sdeg G W) :
    ∃ a ∈ W, ∃ b ∈ W, ∃ c ∈ W, G.Adj a b ∧ G.Adj b c ∧ G.Adj a c := by
  by_contra hno
  push Not at hno
  set n := W.card
  have hpair : ∀ u ∈ W, ∀ v ∈ nbW G W u, dW G W u + dW G W v ≤ n := by
    intro u hu v hv
    rw [mem_nbW] at hv
    have hdisj : Disjoint (nbW G W u) (nbW G W v) := by
      rw [Finset.disjoint_left]
      intro c hcu hcv
      rw [mem_nbW] at hcu hcv
      exact hno u hu v hv.1 c hcu.1 hv.2 hcv.2 hcu.2
    unfold dW
    rw [← card_union_of_disjoint hdisj]
    exact card_le_card (union_subset (nbW_subset _ _) (nbW_subset _ _))
  have h1 : ∑ u ∈ W, ∑ v ∈ nbW G W u, (dW G W u + dW G W v) ≤ ∑ u ∈ W, dW G W u * n := by
    apply sum_le_sum
    intro u hu
    calc ∑ v ∈ nbW G W u, (dW G W u + dW G W v) ≤ ∑ _v ∈ nbW G W u, n := sum_le_sum (hpair u hu)
      _ = dW G W u * n := by rw [sum_const, smul_eq_mul]; rfl
  have h2 : ∑ u ∈ W, ∑ v ∈ nbW G W u, (dW G W u + dW G W v) =
      2 * ∑ u ∈ W, dW G W u * dW G W u := by
    simp only [sum_add_distrib, sum_nbW_swap W (fun v => dW G W v)]
    have : ∀ u ∈ W, ∑ _v ∈ nbW G W u, dW G W u = dW G W u * dW G W u := by
      intro u _; rw [sum_const, smul_eq_mul]; rfl
    rw [sum_congr rfl this]
    ring
  have h3 : ∑ u ∈ W, dW G W u * n = sdeg G W * n := by
    unfold sdeg; rw [sum_mul]
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq W (fun u => (dW G W u : ℕ)) (fun _ => (1 : ℕ))
  simp only [mul_one, one_pow, sum_const, smul_eq_mul] at hcs
  have hs : ∑ u ∈ W, dW G W u = sdeg G W := rfl
  rw [hs] at hcs
  have h4 : ∑ u ∈ W, dW G W u ^ 2 = ∑ u ∈ W, dW G W u * dW G W u := by
    apply sum_congr rfl; intro u _; ring
  rw [h4] at hcs
  -- 2 Σ d² ≤ n σ and σ² ≤ n Σ d²
  have h5 : 2 * ∑ u ∈ W, dW G W u * dW G W u ≤ sdeg G W * n := by
    rw [← h2, ← h3]; exact h1
  have hpos : 0 < sdeg G W := by
    rcases Nat.eq_zero_or_pos (sdeg G W) with h0 | h0
    · rw [h0] at h; simp at h
    · exact h0
  have : 2 * (sdeg G W * sdeg G W) ≤ n * (sdeg G W * n) := by
    calc 2 * (sdeg G W * sdeg G W) = 2 * sdeg G W ^ 2 := by ring
      _ ≤ 2 * ((∑ u ∈ W, dW G W u * dW G W u) * #W) := by
          exact Nat.mul_le_mul_left 2 hcs
      _ = n * (2 * ∑ u ∈ W, dW G W u * dW G W u) := by ring
      _ ≤ n * (sdeg G W * n) := Nat.mul_le_mul_left n h5
  have : sdeg G W * (2 * sdeg G W) ≤ sdeg G W * (n * n) := by nlinarith
  have := Nat.le_of_mul_le_mul_left this hpos
  omega

/-- In a triangle, some edge has many common neighbours. -/
lemma triangle_book (W : Finset V) (a b c : V) (ha : a ∈ W) (hb : b ∈ W) (hc : c ∈ W)
    (hab : G.Adj a b) (hbc : G.Adj b c) (hac : G.Adj a c) :
    ∃ p ∈ W, ∃ q ∈ W, G.Adj p q ∧
      dW G W a + dW G W b + dW G W c ≤ 3 * (nbW G W p ∩ nbW G W q).card + W.card := by
  have hcount : dW G W a + dW G W b + dW G W c ≤ (nbW G W a ∩ nbW G W b).card +
      (nbW G W b ∩ nbW G W c).card + (nbW G W a ∩ nbW G W c).card + W.card := by
    unfold dW nbW
    simp only [← filter_and, card_filter]
    rw [card_eq_sum_ones W, ← sum_add_distrib, ← sum_add_distrib, ← sum_add_distrib,
      ← sum_add_distrib, ← sum_add_distrib]
    apply sum_le_sum
    intro v _
    split_ifs <;> simp_all
  by_cases h1 : (nbW G W b ∩ nbW G W c).card ≤ (nbW G W a ∩ nbW G W b).card ∧
      (nbW G W a ∩ nbW G W c).card ≤ (nbW G W a ∩ nbW G W b).card
  · exact ⟨a, ha, b, hb, hab, by omega⟩
  · by_cases h2 : (nbW G W a ∩ nbW G W c).card ≤ (nbW G W b ∩ nbW G W c).card
    · exact ⟨b, hb, c, hc, hbc, by omega⟩
    · exact ⟨a, ha, c, hc, hac, by omega⟩

end Book

section Path4

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

lemma card_three_le {W P Q R : Finset V} (hP : P ⊆ W) (hQ : Q ⊆ W) (hR : R ⊆ W)
    (hPQ : Disjoint P Q) (hPR : Disjoint P R) (hQR : Disjoint Q R) :
    P.card + Q.card + R.card ≤ W.card := by
  rw [← card_union_of_disjoint hPQ, ← card_union_of_disjoint (disjoint_union_left.2 ⟨hPR, hQR⟩)]
  exact card_le_card (union_subset (union_subset hP hQ) hR)

lemma sum_le_card_mul_real (T : Finset V) (f : V → ℕ) (c : ℝ) (h : ∀ z ∈ T, (f z : ℝ) ≤ c) :
    (∑ z ∈ T, (f z : ℝ)) ≤ T.card * c := by
  have := Finset.sum_le_card_nsmul T (fun z => (f z : ℝ)) c h
  simpa using this

lemma disjoint_nbW_iff {W : Finset V} {u v : V} :
    Disjoint (nbW G W u) (nbW G W v) ↔ ∀ c ∈ W, G.Adj u c → G.Adj v c → False := by
  rw [Finset.disjoint_left]
  constructor
  · intro h c hc hu hv; exact h (mem_nbW.2 ⟨hc, hu⟩) (mem_nbW.2 ⟨hc, hv⟩)
  · intro h c hu hv; exact h c (mem_nbW.1 hu).1 (mem_nbW.1 hu).2 (mem_nbW.1 hv).2

lemma notMem_nbW_self (W : Finset V) (v : V) : v ∉ nbW G W v := fun h => G.irrefl (mem_nbW.1 h).2

/-- The data and hypotheses shared by the pieces of the proof of Lemma 3.2. -/
structure P4Setup (G : SimpleGraph V) [DecidableRel G.Adj] (W : Finset V) (x y : V)
    (Nx Ny U U' A X Y S : Finset V) : Prop where
  hx : x ∈ W
  hy : y ∈ W
  hxy : G.Adj x y
  hNx : Nx = nbW G W x
  hNy : Ny = nbW G W y
  hU : U = Nx.erase y
  hU' : U' = Ny.erase x
  hA : A = Nx ∩ Ny
  hX : X = U \ A
  hY : Y = U' \ A
  hS : S = W \ (Nx ∪ Ny)
  hP : ∀ u ∈ U, ∀ v ∈ U', u ≠ v → ∀ c ∈ W, c ≠ x → c ≠ y → G.Adj u c → G.Adj c v → False

namespace P4Setup

variable {W : Finset V} {x y : V} {Nx Ny U U' A X Y S : Finset V}

lemma mNx (h : P4Setup G W x y Nx Ny U U' A X Y S) (z : V) : z ∈ Nx ↔ z ∈ W ∧ G.Adj x z := by
  rw [h.hNx, mem_nbW]
lemma mNy (h : P4Setup G W x y Nx Ny U U' A X Y S) (z : V) : z ∈ Ny ↔ z ∈ W ∧ G.Adj y z := by
  rw [h.hNy, mem_nbW]
lemma mU (h : P4Setup G W x y Nx Ny U U' A X Y S) (z : V) : z ∈ U ↔ z ≠ y ∧ z ∈ Nx := by
  rw [h.hU, mem_erase]
lemma mU' (h : P4Setup G W x y Nx Ny U U' A X Y S) (z : V) : z ∈ U' ↔ z ≠ x ∧ z ∈ Ny := by
  rw [h.hU', mem_erase]
lemma mA (h : P4Setup G W x y Nx Ny U U' A X Y S) (z : V) : z ∈ A ↔ z ∈ Nx ∧ z ∈ Ny := by
  rw [h.hA, mem_inter]
lemma mX (h : P4Setup G W x y Nx Ny U U' A X Y S) (z : V) : z ∈ X ↔ z ∈ U ∧ z ∉ A := by
  rw [h.hX, mem_sdiff]
lemma mY (h : P4Setup G W x y Nx Ny U U' A X Y S) (z : V) : z ∈ Y ↔ z ∈ U' ∧ z ∉ A := by
  rw [h.hY, mem_sdiff]
lemma mS (h : P4Setup G W x y Nx Ny U U' A X Y S) (z : V) : z ∈ S ↔ z ∈ W ∧ z ∉ Nx ∧ z ∉ Ny := by
  rw [h.hS, mem_sdiff, mem_union, not_or]

lemma yNx (h : P4Setup G W x y Nx Ny U U' A X Y S) : y ∈ Nx := (h.mNx y).2 ⟨h.hy, h.hxy⟩
lemma xNy (h : P4Setup G W x y Nx Ny U U' A X Y S) : x ∈ Ny := (h.mNy x).2 ⟨h.hx, h.hxy.symm⟩
lemma xNx (h : P4Setup G W x y Nx Ny U U' A X Y S) : x ∉ Nx := fun hh => G.irrefl ((h.mNx x).1 hh).2
lemma yNy (h : P4Setup G W x y Nx Ny U U' A X Y S) : y ∉ Ny := fun hh => G.irrefl ((h.mNy y).1 hh).2
lemma NxW (h : P4Setup G W x y Nx Ny U U' A X Y S) : Nx ⊆ W := fun z hz => ((h.mNx z).1 hz).1
lemma NyW (h : P4Setup G W x y Nx Ny U U' A X Y S) : Ny ⊆ W := fun z hz => ((h.mNy z).1 hz).1
lemma UW (h : P4Setup G W x y Nx Ny U U' A X Y S) : U ⊆ W := fun z hz => h.NxW ((h.mU z).1 hz).2
lemma U'W (h : P4Setup G W x y Nx Ny U U' A X Y S) : U' ⊆ W := fun z hz => h.NyW ((h.mU' z).1 hz).2
lemma XW (h : P4Setup G W x y Nx Ny U U' A X Y S) : X ⊆ W := fun z hz => h.UW ((h.mX z).1 hz).1
lemma YW (h : P4Setup G W x y Nx Ny U U' A X Y S) : Y ⊆ W := fun z hz => h.U'W ((h.mY z).1 hz).1
lemma AU (h : P4Setup G W x y Nx Ny U U' A X Y S) : A ⊆ U := fun z hz =>
  (h.mU z).2 ⟨fun e => h.yNy (e ▸ ((h.mA z).1 hz).2), ((h.mA z).1 hz).1⟩
lemma AU' (h : P4Setup G W x y Nx Ny U U' A X Y S) : A ⊆ U' := fun z hz =>
  (h.mU' z).2 ⟨fun e => h.xNx (e ▸ ((h.mA z).1 hz).1), ((h.mA z).1 hz).2⟩
lemma dx (h : P4Setup G W x y Nx Ny U U' A X Y S) : dW G W x = Nx.card := by rw [h.hNx]; rfl
lemma dy (h : P4Setup G W x y Nx Ny U U' A X Y S) : dW G W y = Ny.card := by rw [h.hNy]; rfl

lemma cards (h : P4Setup G W x y Nx Ny U U' A X Y S) :
    U.card + 1 = Nx.card ∧ U'.card + 1 = Ny.card ∧ X.card + A.card = U.card ∧
      Y.card + A.card = U'.card ∧ S.card + Nx.card + Ny.card = W.card + A.card := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [h.hU, card_erase_of_mem h.yNx]
    have : 0 < Nx.card := card_pos.2 ⟨y, h.yNx⟩
    omega
  · rw [h.hU', card_erase_of_mem h.xNy]
    have : 0 < Ny.card := card_pos.2 ⟨x, h.xNy⟩
    omega
  · exact h.hX ▸ card_sdiff_add_card_eq_card h.AU
  · exact h.hY ▸ card_sdiff_add_card_eq_card h.AU'
  · have e1 : S.card + (Nx ∪ Ny).card = W.card :=
      h.hS ▸ card_sdiff_add_card_eq_card (union_subset h.NxW h.NyW)
    have e2 : (Nx ∪ Ny).card + A.card = Nx.card + Ny.card := h.hA ▸ card_union_add_card_inter _ _
    omega

lemma sum_eq (h : P4Setup G W x y Nx Ny U U' A X Y S) :
    sdeg G W = ∑ z ∈ S, dW G W z + ∑ z ∈ X, dW G W z + ∑ z ∈ Y, dW G W z +
      ∑ z ∈ A, dW G W z + Nx.card + Ny.card := by
  have e1 := sum_sdiff (union_subset h.NxW h.NyW) (f := dW G W)
  have e2 := sum_union_inter (s₁ := Nx) (s₂ := Ny) (f := dW G W)
  have e3 := sum_erase_add Nx (dW G W) h.yNx
  have e4 := sum_erase_add Ny (dW G W) h.xNy
  have e5 := sum_sdiff h.AU (f := dW G W)
  have e6 := sum_sdiff h.AU' (f := dW G W)
  rw [← h.hS] at e1
  rw [← h.hA] at e2
  rw [← h.hU] at e3
  rw [← h.hU'] at e4
  rw [← h.hX] at e5
  rw [← h.hY] at e6
  rw [← h.dx, ← h.dy]
  unfold sdeg
  omega

lemma S_bound (h : P4Setup G W x y Nx Ny U U' A X Y S) (hd : Ny.card ≤ Nx.card) :
    ∀ z ∈ S, dW G W z + Ny.card + 1 ≤ W.card := by
  intro z hz
  obtain ⟨hzW, hzx, hzy⟩ := (h.mS z).1 hz
  have hzx' : ¬ G.Adj z x := fun hh => hzx ((h.mNx z).2 ⟨hzW, hh.symm⟩)
  have hzy' : ¬ G.Adj z y := fun hh => hzy ((h.mNy z).2 ⟨hzW, hh.symm⟩)
  have hzxne : z ≠ x := fun e => hzy (e ▸ h.xNy)
  have hzyne : z ≠ y := fun e => hzx (e ▸ h.yNx)
  have hc := h.cards
  have hor : (nbW G W z ∩ U').card ≤ 1 ∨ (nbW G W z ∩ U).card ≤ 1 := by
    by_contra hc
    push Not at hc
    obtain ⟨u₁, hu₁, u₂, hu₂, hne⟩ := one_lt_card.1 hc.2
    obtain ⟨v, hv⟩ := card_pos.1 (by omega : 0 < (nbW G W z ∩ U').card)
    rw [mem_inter] at hu₁ hu₂ hv
    by_cases h1 : u₁ = v
    · exact h.hP u₂ hu₂.2 v hv.2 (fun e => hne (h1.trans e.symm)) z hzW hzxne hzyne
        (mem_nbW.1 hu₂.1).2.symm (mem_nbW.1 hv.1).2
    · exact h.hP u₁ hu₁.2 v hv.2 h1 z hzW hzxne hzyne (mem_nbW.1 hu₁.1).2.symm
        (mem_nbW.1 hv.1).2
  have hR : ({x, y, z} : Finset V) ⊆ W := by
    intro v hv; simp only [mem_insert, mem_singleton] at hv
    rcases hv with rfl | rfl | rfl
    · exact h.hx
    · exact h.hy
    · exact hzW
  have hRc : ({x, y, z} : Finset V).card = 3 := by
    rw [card_insert_of_notMem, card_pair (Ne.symm hzyne)]
    simp only [mem_insert, mem_singleton, not_or]
    exact ⟨G.ne_of_adj h.hxy, Ne.symm hzxne⟩
  have hNzR : Disjoint (nbW G W z) {x, y, z} := by
    rw [disjoint_right]
    intro v hv hvz
    simp only [mem_insert, mem_singleton] at hv
    rcases hv with rfl | rfl | rfl
    · exact hzx' (mem_nbW.1 hvz).2
    · exact hzy' (mem_nbW.1 hvz).2
    · exact notMem_nbW_self W _ hvz
  rcases hor with h0 | h0
  · have h1 := card_three_le (nbW_subset (G := G) W z) (sdiff_subset.trans h.U'W) hR
      (disjoint_sdiff : Disjoint (nbW G W z) (U' \ nbW G W z)) hNzR (by
        rw [disjoint_right]; intro v hv hvU
        have hvU' := (h.mU' v).1 (mem_sdiff.1 hvU).1
        simp only [mem_insert, mem_singleton] at hv
        rcases hv with rfl | rfl | rfl
        · exact hvU'.1 rfl
        · exact h.yNy hvU'.2
        · exact hzy hvU'.2)
    have h2 : (U' \ nbW G W z).card + (nbW G W z ∩ U').card = U'.card := by
      rw [inter_comm]; exact card_sdiff_add_card_inter _ _
    unfold dW
    rw [hRc] at h1
    omega
  · have h1 := card_three_le (nbW_subset (G := G) W z) (sdiff_subset.trans h.UW) hR
      (disjoint_sdiff : Disjoint (nbW G W z) (U \ nbW G W z)) hNzR (by
        rw [disjoint_right]; intro v hv hvU
        have hvU' := (h.mU v).1 (mem_sdiff.1 hvU).1
        simp only [mem_insert, mem_singleton] at hv
        rcases hv with rfl | rfl | rfl
        · exact h.xNx hvU'.2
        · exact hvU'.1 rfl
        · exact hzx hvU'.2)
    have h2 : (U \ nbW G W z).card + (nbW G W z ∩ U).card = U.card := by
      rw [inter_comm]; exact card_sdiff_add_card_inter _ _
    unfold dW
    rw [hRc] at h1
    omega

end P4Setup

namespace P4Setup

variable {W : Finset V} {x y : V} {Nx Ny U U' A X Y S : Finset V}

lemma A_bound_one (h : P4Setup G W x y Nx Ny U U' A X Y S) (hd : Ny.card ≤ Nx.card)
    (hA1 : A.card = 1) : ∑ z ∈ A, dW G W z + Ny.card ≤ W.card + 1 := by
  obtain ⟨z, hz⟩ := card_eq_one.1 hA1
  have hzA : z ∈ A := hz ▸ mem_singleton_self z
  have hzNx := ((h.mA z).1 hzA).1
  have hzNy := ((h.mA z).1 hzA).2
  have hzW := h.NxW hzNx
  have hzx : z ≠ x := fun e => h.xNx (e ▸ hzNx)
  have hzy : z ≠ y := fun e => h.yNy (e ▸ hzNy)
  have hc := h.cards
  rw [hz, sum_singleton]
  have hor : (∀ v ∈ Y, ¬ G.Adj z v) ∨ (∀ u ∈ X, ¬ G.Adj z u) := by
    by_contra hc
    simp only [not_or, not_forall, not_not] at hc
    obtain ⟨⟨v, hvY, hzv⟩, ⟨u, huX, hzu⟩⟩ := hc
    have hu := (h.mX u).1 huX
    have hv := (h.mY v).1 hvY
    have huv : u ≠ v := by
      rintro rfl
      exact hu.2 ((h.mA u).2 ⟨((h.mU u).1 hu.1).2, ((h.mU' u).1 hv.1).2⟩)
    exact h.hP u hu.1 v hv.1 huv z hzW hzx hzy hzu.symm hzv
  have hzsingle : ({z} : Finset V) ⊆ W := singleton_subset_iff.2 hzW
  rcases hor with h0 | h0
  · have h1 := card_three_le (nbW_subset (G := G) W z) h.YW hzsingle
      (by rw [disjoint_right]; intro v hv hvz; exact h0 v hv (mem_nbW.1 hvz).2)
      (by rw [disjoint_singleton_right]; exact notMem_nbW_self W z)
      (by rw [disjoint_singleton_right]; intro hzY; exact ((h.mY z).1 hzY).2 hzA)
    rw [card_singleton] at h1
    unfold dW
    omega
  · have h1 := card_three_le (nbW_subset (G := G) W z) h.XW hzsingle
      (by rw [disjoint_right]; intro v hv hvz; exact h0 v hv (mem_nbW.1 hvz).2)
      (by rw [disjoint_singleton_right]; exact notMem_nbW_self W z)
      (by rw [disjoint_singleton_right]; intro hzX; exact ((h.mX z).1 hzX).2 hzA)
    rw [card_singleton] at h1
    unfold dW
    omega

lemma A_bound_two (h : P4Setup G W x y Nx Ny U U' A X Y S) :
    ∑ z ∈ A, dW G W z ≤ W.card + 2 * A.card := by
  have e1 : ∑ z ∈ A, dW G W z = ∑ v ∈ W, (A.filter (fun z => G.Adj z v)).card := by
    unfold dW nbW
    simp only [card_filter]
    rw [sum_comm]
  rw [e1]
  have e2 : ∀ v ∈ W, (A.filter (fun z => G.Adj z v)).card ≤
      1 + (if v = x then A.card else 0) + (if v = y then A.card else 0) := by
    intro v hv
    by_cases hvx : v = x
    · rw [if_pos hvx]; have := card_filter_le A (fun z => G.Adj z v); omega
    by_cases hvy : v = y
    · rw [if_pos hvy]; have := card_filter_le A (fun z => G.Adj z v); omega
    rw [if_neg hvx, if_neg hvy]
    have : (A.filter (fun z => G.Adj z v)).card ≤ 1 := by
      rw [card_le_one]
      intro a ha b hb
      rw [mem_filter] at ha hb
      by_contra hab
      exact h.hP a (h.AU ha.1) b (h.AU' hb.1) hab v hv hvx hvy ha.2 hb.2.symm
    omega
  calc ∑ v ∈ W, (A.filter (fun z => G.Adj z v)).card
      ≤ ∑ v ∈ W, (1 + (if v = x then A.card else 0) + (if v = y then A.card else 0)) :=
        sum_le_sum e2
    _ = W.card + 2 * A.card := by
        rw [sum_add_distrib, sum_add_distrib, sum_ite_eq' W x, sum_ite_eq' W y, if_pos h.hx,
          if_pos h.hy]
        simp; ring

lemma A_bound (h : P4Setup G W x y Nx Ny U U' A X Y S) (hd : Ny.card ≤ Nx.card) (s : ℝ)
    (hs2 : 2 ≤ s) (hs_lt : s ^ 2 * 4 ≤ (W.card : ℝ) ^ 2 - 2 * W.card)
    (hdyR : (W.card : ℝ) / 2 - s + 2 ≤ Ny.card) :
    (∑ z ∈ A, (dW G W z : ℝ)) - A.card * ((W.card : ℝ) / 2 - s + 1) < 8 * s - 8 := by
  have hs_n : s < (W.card : ℝ) / 2 := by nlinarith
  rcases Nat.lt_or_ge A.card 2 with hA2 | hA2
  · rcases Nat.lt_or_ge A.card 1 with hA1 | hA1
    · have : A = ∅ := card_eq_zero.1 (by omega)
      rw [this]; simp; linarith
    · have hb := h.A_bound_one hd (by omega)
      have hb' : (∑ z ∈ A, (dW G W z : ℝ)) + Ny.card ≤ W.card + 1 := by exact_mod_cast hb
      have : (A.card : ℝ) = 1 := by exact_mod_cast (by omega : A.card = 1)
      rw [this]
      linarith
  · have hcR : (∑ z ∈ A, (dW G W z : ℝ)) ≤ W.card + 2 * A.card := by
      exact_mod_cast h.A_bound_two
    have hAn : A.card ≤ W.card := card_le_card (h.AU.trans h.UW)
    have hAnR : (A.card : ℝ) ≤ W.card := by exact_mod_cast hAn
    have hA2R : (2 : ℝ) ≤ A.card := by exact_mod_cast hA2
    have hn6 : 6 ≤ W.card := by
      have h16 : (16 : ℝ) ≤ (W.card : ℝ) ^ 2 - 2 * W.card := by nlinarith
      by_contra hlt
      have : (W.card : ℝ) ≤ 5 := by exact_mod_cast (by omega : W.card ≤ 5)
      nlinarith
    have hn6R : (6 : ℝ) ≤ W.card := by exact_mod_cast hn6
    rcases le_or_gt ((W.card : ℝ) / 2 - s) 1 with hu | hu
    · have hu' : (1 : ℝ) / 2 ≤ (W.card : ℝ) / 2 - s := by nlinarith
      have key : (A.card : ℝ) * (1 + s - (W.card : ℝ) / 2) ≤ W.card * (1 + s - (W.card : ℝ) / 2) :=
        mul_le_mul_of_nonneg_right hAnR (by linarith)
      rcases le_or_gt 8 (W.card : ℝ) with h8 | h8
      · nlinarith
      · nlinarith
    · have key : (A.card : ℝ) * ((W.card : ℝ) / 2 - s - 1) ≥ 2 * ((W.card : ℝ) / 2 - s - 1) :=
        mul_le_mul_of_nonneg_right hA2R (by linarith)
      nlinarith

lemma XY_exists (h : P4Setup G W x y Nx Ny U U' A X Y S) (hNy3 : 3 ≤ Ny.card) (z₀ : V)
    (hz₀X : z₀ ∈ X) :
    (∀ z ∈ Y, dW G W z + dW G W z₀ ≤ W.card) ∧ ∃ z ∈ W, dW G W z + dW G W z₀ ≤ W.card := by
  have hc := h.cards
  have hz₀ := (h.mX z₀).1 hz₀X
  have hz₀Nx := ((h.mU z₀).1 hz₀.1).2
  have hz₀y := ((h.mU z₀).1 hz₀.1).1
  have hz₀W := h.NxW hz₀Nx
  have hz₀x : z₀ ≠ x := fun e => h.xNx (e ▸ hz₀Nx)
  have hz₀Ny : z₀ ∉ Ny := fun hh => hz₀.2 ((h.mA z₀).2 ⟨hz₀Nx, hh⟩)
  have hz₀U' : z₀ ∉ U' := fun hh => hz₀Ny ((h.mU' z₀).1 hh).2
  have hz₀nady : ¬ G.Adj z₀ y := fun hh => hz₀Ny ((h.mNy z₀).2 ⟨hz₀W, hh.symm⟩)
  have hYb : ∀ z ∈ Y, dW G W z + dW G W z₀ ≤ W.card := by
    intro z hzY
    have hz := (h.mY z).1 hzY
    have hzNy := ((h.mU' z).1 hz.1).2
    have hzW := h.NyW hzNy
    have hzNx : z ∉ Nx := fun hh => hz.2 ((h.mA z).2 ⟨hh, hzNy⟩)
    have hdisj : Disjoint (nbW G W z) (nbW G W z₀) := by
      rw [disjoint_nbW_iff]
      intro c hc hzc hz₀c
      by_cases hcx : c = x
      · exact hzNx ((h.mNx z).2 ⟨hzW, hcx ▸ hzc.symm⟩)
      by_cases hcy : c = y
      · exact hz₀nady (hcy ▸ hz₀c)
      exact h.hP z₀ hz₀.1 z hz.1 (fun e => hz₀U' (e ▸ hz.1)) c hc hcx hcy hz₀c hzc.symm
    have := card_le_card (union_subset (nbW_subset (G := G) W z) (nbW_subset (G := G) W z₀))
    rw [card_union_of_disjoint hdisj] at this
    exact this
  have hAb' : ∀ z ∈ A, ¬ G.Adj z₀ z → dW G W z + dW G W z₀ ≤ W.card := by
    intro z hzA hnadj
    have hxz₀ : x ∈ nbW G W z₀ := mem_nbW.2 ⟨h.hx, ((h.mNx z₀).1 hz₀Nx).2.symm⟩
    have h1 := card_three_le (nbW_subset (G := G) W z)
      ((erase_subset x _).trans (nbW_subset (G := G) W z₀)) (singleton_subset_iff.2 hz₀W)
      (by
        rw [disjoint_right]
        intro c hc hcz
        have hc' := mem_erase.1 hc
        have hcW := (mem_nbW.1 hc'.2).1
        have hz₀c := (mem_nbW.1 hc'.2).2
        have hzc := (mem_nbW.1 hcz).2
        by_cases hcy : c = y
        · exact hz₀nady (hcy ▸ hz₀c)
        exact h.hP z₀ hz₀.1 z (h.AU' hzA) (fun e => hz₀.2 (e ▸ hzA)) c hcW hc'.1 hcy hz₀c
          hzc.symm)
      (by rw [disjoint_singleton_right]; intro hh; exact hnadj (mem_nbW.1 hh).2.symm)
      (by rw [disjoint_singleton_right]; intro hh; exact notMem_nbW_self W z₀ (mem_erase.1 hh).2)
    rw [card_singleton, card_erase_of_mem hxz₀] at h1
    have : 0 < (nbW G W z₀).card := card_pos.2 ⟨x, hxz₀⟩
    unfold dW
    omega
  refine ⟨hYb, ?_⟩
  rcases Y.eq_empty_or_nonempty with hYe | ⟨z, hzY⟩
  · have hYc : Y.card = 0 := by rw [hYe]; rfl
    have hA2 : 2 ≤ A.card := by omega
    have hle1 : (A.filter (fun z => G.Adj z₀ z)).card ≤ 1 := by
      rw [card_le_one]
      intro a ha b hb
      rw [mem_filter] at ha hb
      by_contra hab
      exact h.hP a (h.AU ha.1) b (h.AU' hb.1) hab z₀ hz₀W hz₀x hz₀y ha.2.symm hb.2
    have := card_filter_add_card_filter_not (s := A) (fun z => G.Adj z₀ z)
    obtain ⟨z, hz⟩ := card_pos.1 (by omega : 0 < (A.filter (fun z => ¬ G.Adj z₀ z)).card)
    rw [mem_filter] at hz
    exact ⟨z, h.NxW ((h.mA z).1 hz.1).1, hAb' z hz.1 hz.2⟩
  · exact ⟨z, h.YW hzY, hYb z hzY⟩

lemma XY_bound (h : P4Setup G W x y Nx Ny U U' A X Y S) (hd : Ny.card ≤ Nx.card) (s : ℝ)
    (hNy3 : 3 ≤ Ny.card) (hdeg : ∀ v ∈ W, (W.card : ℝ) / 2 - s + 2 ≤ dW G W v) :
    (∑ z ∈ X, (dW G W z : ℝ)) + (∑ z ∈ Y, (dW G W z : ℝ)) ≤
      ((Nx.card : ℝ) - Ny.card) * ((W.card : ℝ) / 2 + s - 2) + Y.card * W.card := by
  have hc := h.cards
  rcases X.eq_empty_or_nonempty with hXe | hXne
  · have hXc : X.card = 0 := by rw [hXe]; rfl
    have hYc : Y.card = 0 := by omega
    have hYe : Y = ∅ := card_eq_zero.1 hYc
    have hNN : Nx.card = Ny.card := by omega
    rw [hXe, hYe, hNN]; simp
  obtain ⟨z₀, hz₀X, hz₀max⟩ := exists_max_image X (dW G W) hXne
  obtain ⟨hYb, z, hzW, hz⟩ := h.XY_exists hNy3 z₀ hz₀X
  have hDel : (dW G W z₀ : ℝ) ≤ (W.card : ℝ) / 2 + s - 2 := by
    have := hdeg z hzW
    have : (dW G W z : ℝ) + dW G W z₀ ≤ W.card := by exact_mod_cast hz
    linarith
  have hsX : (∑ z ∈ X, (dW G W z : ℝ)) ≤ X.card * (dW G W z₀ : ℝ) :=
    sum_le_card_mul_real X (dW G W) _ (fun z hz => by exact_mod_cast hz₀max z hz)
  have hsY : (∑ z ∈ Y, (dW G W z : ℝ)) ≤ Y.card * ((W.card : ℝ) - dW G W z₀) :=
    sum_le_card_mul_real Y (dW G W) _ (fun z hz => by
      have := hYb z hz
      have : (dW G W z : ℝ) + dW G W z₀ ≤ W.card := by exact_mod_cast this
      linarith)
  have hXYc : (X.card : ℝ) = Y.card + ((Nx.card : ℝ) - Ny.card) := by
    have : X.card + Ny.card = Y.card + Nx.card := by omega
    have : (X.card : ℝ) + Ny.card = Y.card + Nx.card := by exact_mod_cast this
    linarith
  have hNN : (0 : ℝ) ≤ (Nx.card : ℝ) - Ny.card := by
    have : (Ny.card : ℝ) ≤ Nx.card := by exact_mod_cast hd
    linarith
  rw [hXYc] at hsX
  nlinarith

end P4Setup

lemma path4_final (n dx dy a sS sXY sA s σ : ℝ) (hs2 : 2 ≤ s)
    (hσ : n ^ 2 / 2 + 2 * s ^ 2 ≤ σ) (hsum : σ = sS + sXY + sA + dx + dy)
    (hS0 : 0 ≤ n + a - dx - dy) (hSR : sS ≤ (n + a - dx - dy) * (n - dy - 1))
    (hXY : sXY ≤ (dx - dy) * (n / 2 + s - 2) + (dy - a - 1) * n)
    (hA : sA - a * (n / 2 - s + 1) < 8 * s - 8) (hdy : n / 2 - s + 2 ≤ dy) : False := by
  nlinarith [mul_nonneg hS0 (by linarith : (0 : ℝ) ≤ dy - (n / 2 - s + 2)),
    mul_nonneg (by linarith : (0 : ℝ) ≤ dy - (n / 2 - s + 2)) (by linarith : (0 : ℝ) ≤ 2 * s - 4)]

/-- Lemma 3.2 of Bucić–Chen–Ma for an edge `xy` with `d(y) ≤ d(x)`. -/
lemma path4_adj (W : Finset V) (s : ℝ) (hs2 : 2 ≤ s)
    (hσ : (W.card : ℝ) ^ 2 / 2 + 2 * s ^ 2 ≤ sdeg G W)
    (hdeg : ∀ v ∈ W, (W.card : ℝ) / 2 - s + 2 ≤ dW G W v)
    (x y : V) (hx : x ∈ W) (hy : y ∈ W) (hxy : G.Adj x y) (hd : dW G W y ≤ dW G W x) :
    ∃ a ∈ W, ∃ b ∈ W, ∃ c ∈ W, IsPathL G [x, a, b, c, y] := by
  by_contra hno
  simp only [not_exists, not_and] at hno
  have hP : ∀ u ∈ (nbW G W x).erase y, ∀ v ∈ (nbW G W y).erase x, u ≠ v → ∀ c ∈ W, c ≠ x →
      c ≠ y → G.Adj u c → G.Adj c v → False := by
    intro u hu v hv huv c hc hcx hcy huc hcv
    rw [mem_erase] at hu hv
    have hu' := mem_nbW.1 hu.2
    have hv' := mem_nbW.1 hv.2
    apply hno u hu'.1 c hc v hv'.1
    refine ⟨?_, ?_⟩
    · have h1 : x ≠ u := G.ne_of_adj hu'.2
      have h2 : x ≠ v := fun e => hv.1 e.symm
      have h3 : x ≠ y := G.ne_of_adj hxy
      have h4 : u ≠ c := G.ne_of_adj huc
      have h5 : c ≠ v := G.ne_of_adj hcv
      have h6 : v ≠ y := G.ne_of_adj hv'.2.symm
      simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil]
      refine ⟨?_, ?_, ?_, ?_, by simp⟩ <;> simp_all [eq_comm]
    · simp only [List.isChain_cons_cons, List.isChain_singleton, and_true]
      exact ⟨hu'.2, huc, hcv, hv'.2.symm⟩
  have h : P4Setup G W x y (nbW G W x) (nbW G W y) ((nbW G W x).erase y) ((nbW G W y).erase x)
      (nbW G W x ∩ nbW G W y) ((nbW G W x).erase y \ (nbW G W x ∩ nbW G W y))
      ((nbW G W y).erase x \ (nbW G W x ∩ nbW G W y)) (W \ (nbW G W x ∪ nbW G W y)) :=
    ⟨hx, hy, hxy, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, hP⟩
  have hd' : (nbW G W y).card ≤ (nbW G W x).card := hd
  have hσle := sdeg_le (G := G) W
  have hs_lt : s ^ 2 * 4 ≤ (W.card : ℝ) ^ 2 - 2 * W.card := by
    have : ((sdeg G W : ℕ) : ℝ) + W.card ≤ W.card * W.card := by exact_mod_cast hσle
    nlinarith
  have hdyR : (W.card : ℝ) / 2 - s + 2 ≤ (nbW G W y).card := hdeg y hy
  have hs_n : s < (W.card : ℝ) / 2 := by nlinarith
  have hNy3 : 3 ≤ (nbW G W y).card := by
    have : (2 : ℝ) < (nbW G W y).card := by linarith
    exact_mod_cast this
  have hA := h.A_bound hd' s hs2 hs_lt hdyR
  have hXY := h.XY_bound hd' s hNy3 hdeg
  have hSR := sum_le_card_mul_real _ (dW G W) _ (fun z hz => by
      have := h.S_bound hd' z hz
      have : (dW G W z : ℝ) + (nbW G W y).card + 1 ≤ W.card := by exact_mod_cast this
      exact (by linarith : (dW G W z : ℝ) ≤ W.card - (nbW G W y).card - 1))
  have hc := h.cards
  have hsum := h.sum_eq
  have hsumR : (sdeg G W : ℝ) = ((∑ z ∈ W \ (nbW G W x ∪ nbW G W y), dW G W z : ℕ) : ℝ) +
      (((∑ z ∈ (nbW G W x).erase y \ (nbW G W x ∩ nbW G W y), dW G W z : ℕ) : ℝ) +
      ((∑ z ∈ (nbW G W y).erase x \ (nbW G W x ∩ nbW G W y), dW G W z : ℕ) : ℝ)) +
      ((∑ z ∈ nbW G W x ∩ nbW G W y, dW G W z : ℕ) : ℝ) + (nbW G W x).card + (nbW G W y).card := by
    rw [hsum]; push_cast; ring
  push_cast at hsumR
  have hScR : ((W \ (nbW G W x ∪ nbW G W y)).card : ℝ) = W.card + (nbW G W x ∩ nbW G W y).card -
      (nbW G W x).card - (nbW G W y).card := by
    have e : ((W \ (nbW G W x ∪ nbW G W y)).card : ℝ) + (nbW G W x).card + (nbW G W y).card =
        W.card + (nbW G W x ∩ nbW G W y).card := by exact_mod_cast hc.2.2.2.2
    linarith
  have hYcR : (((nbW G W y).erase x \ (nbW G W x ∩ nbW G W y)).card : ℝ) =
      (nbW G W y).card - (nbW G W x ∩ nbW G W y).card - 1 := by
    have e : (((nbW G W y).erase x \ (nbW G W x ∩ nbW G W y)).card : ℝ) +
        (nbW G W x ∩ nbW G W y).card + 1 = (nbW G W y).card := by
      exact_mod_cast (by omega : ((nbW G W y).erase x \ (nbW G W x ∩ nbW G W y)).card +
        (nbW G W x ∩ nbW G W y).card + 1 = (nbW G W y).card)
    linarith
  have hS0 : (0 : ℝ) ≤ ((W \ (nbW G W x ∪ nbW G W y)).card : ℝ) := by positivity
  rw [hScR] at hS0 hSR
  rw [hYcR] at hXY
  exact path4_final _ _ _ _ _ _ _ s _ hs2 hσ hsumR hS0 hSR hXY hA hdyR


end Path4

section Path4b

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

lemma path4_transfer {x a b c y : V} (hxy : x ≠ y)
    (h : IsPathL (G ⊔ SimpleGraph.edge x y) [x, a, b, c, y]) : IsPathL G [x, a, b, c, y] := by
  obtain ⟨hnd, hch⟩ := h
  refine ⟨hnd, ?_⟩
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hnd
  simp only [List.isChain_cons_cons, List.isChain_singleton, and_true, SimpleGraph.sup_adj,
    SimpleGraph.edge_adj] at hch ⊢
  obtain ⟨h1, h2, h3, h4⟩ := hch
  refine ⟨?_, ?_, ?_, ?_⟩
  · rcases h1 with h1 | ⟨⟨_, e⟩ | ⟨e, _⟩, _⟩
    · exact h1
    · exact absurd e hnd.2.1.2.2
    · exact absurd e hxy
  · rcases h2 with h2 | ⟨⟨e, _⟩ | ⟨e, _⟩, _⟩
    · exact h2
    · exact absurd e.symm hnd.1.1
    · exact absurd e hnd.2.1.2.2
  · rcases h3 with h3 | ⟨⟨e, _⟩ | ⟨e, _⟩, _⟩
    · exact h3
    · exact absurd e.symm hnd.1.2.1
    · exact absurd e hnd.2.2.1.2
  · rcases h4 with h4 | ⟨e | ⟨e, _⟩, _⟩
    · exact h4
    · exact absurd e.symm hnd.1.2.2.1
    · exact absurd e hnd.2.2.2.1

/-- Lemma 3.2 of Bucić–Chen–Ma: under the degree conditions, any two distinct vertices of `W`
are joined by a path with exactly four edges inside `W`. -/
lemma path4 (W : Finset V) (s : ℝ) (hs2 : 2 ≤ s)
    (hσ : (W.card : ℝ) ^ 2 / 2 + 2 * s ^ 2 ≤ sdeg G W)
    (hdeg : ∀ v ∈ W, (W.card : ℝ) / 2 - s + 2 ≤ dW G W v)
    (x y : V) (hx : x ∈ W) (hy : y ∈ W) (hne : x ≠ y) :
    ∃ a ∈ W, ∃ b ∈ W, ∃ c ∈ W, IsPathL G [x, a, b, c, y] := by
  classical
  let G' := G ⊔ SimpleGraph.edge x y
  have hsub : ∀ v, nbW G W v ⊆ nbW G' W v := by
    intro v u hu
    rw [mem_nbW] at hu ⊢
    exact ⟨hu.1, (SimpleGraph.sup_adj _ _ _ _).2 (Or.inl hu.2)⟩
  have hdle : ∀ v, dW G W v ≤ dW G' W v := fun v => card_le_card (hsub v)
  have hσ' : (W.card : ℝ) ^ 2 / 2 + 2 * s ^ 2 ≤ sdeg G' W := by
    have : sdeg G W ≤ sdeg G' W := sum_le_sum fun v _ => hdle v
    have : (sdeg G W : ℝ) ≤ sdeg G' W := by exact_mod_cast this
    linarith
  have hdeg' : ∀ v ∈ W, (W.card : ℝ) / 2 - s + 2 ≤ dW G' W v := by
    intro v hv
    have := hdeg v hv
    have : (dW G W v : ℝ) ≤ dW G' W v := by exact_mod_cast hdle v
    linarith
  have hadj : G'.Adj x y := (SimpleGraph.sup_adj _ _ _ _).2 (Or.inr (by
    rw [SimpleGraph.edge_adj]; exact ⟨Or.inl ⟨rfl, rfl⟩, hne⟩))
  rcases le_total (dW G' W y) (dW G' W x) with hd | hd
  · obtain ⟨a, ha, b, hb, c, hc, hp⟩ := path4_adj (G := G') W s hs2 hσ' hdeg' x y hx hy hadj hd
    exact ⟨a, ha, b, hb, c, hc, path4_transfer hne hp⟩
  · obtain ⟨a, ha, b, hb, c, hc, hp⟩ :=
      path4_adj (G := G') W s hs2 hσ' hdeg' y x hy hx hadj.symm hd
    have hG'' : G' = G ⊔ SimpleGraph.edge y x := by
      simp only [G', SimpleGraph.edge_comm]
    rw [hG''] at hp
    have hp' := (path4_transfer hne.symm hp).reverse
    simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append] at hp'
    exact ⟨c, hc, b, hb, a, ha, hp'⟩

lemma dW_sdiff_add (W T : Finset V) (v : V) : dW G W v ≤ dW G (W \ T) v + T.card := by
  unfold dW
  calc (nbW G W v).card ≤ (nbW G (W \ T) v ∪ T).card := by
        apply card_le_card
        intro u hu
        rw [mem_nbW] at hu
        by_cases huT : u ∈ T
        · exact mem_union_right _ huT
        · exact mem_union_left _ (mem_nbW.2 ⟨mem_sdiff.2 ⟨hu.1, huT⟩, hu.2⟩)
    _ ≤ _ := card_union_le _ _

lemma sdeg_sdiff (W T : Finset V) (hT : T ⊆ W) : sdeg G W ≤ sdeg G (W \ T) + 2 * T.card * W.card := by
  induction T using Finset.induction_on with
  | empty => simp
  | insert a T haT ih =>
    have hTW : T ⊆ W := (subset_insert a T).trans hT
    have haW : a ∈ W := hT (mem_insert_self a T)
    have ih := ih hTW
    have haWT : a ∈ W \ T := mem_sdiff.2 ⟨haW, haT⟩
    have e1 := sdeg_erase (G := G) (W \ T) a haWT
    have e2 : W \ insert a T = (W \ T).erase a := by
      ext u; simp [mem_sdiff, mem_insert, mem_erase]; tauto
    have e3 : dW G (W \ T) a + 1 ≤ (W \ T).card := dW_le (W \ T) a haWT
    have e4 : (W \ T).card ≤ W.card := card_le_card sdiff_subset
    rw [e2, card_insert_of_notMem haT]
    nlinarith

/-- Lemma 3.2 applied after deleting a small vertex set `T`. -/
lemma path4_avoid (W T : Finset V) (hT : T ⊆ W) (m : ℕ) (hTm : T.card ≤ m) (s : ℝ) (hs : 0 < s)
    (hσ : (W.card : ℝ) ^ 2 / 2 + 2 * s ^ 2 ≤ sdeg G W)
    (hsm : (m : ℝ) * W.card + 2 * s ≤ s ^ 2)
    (hdeg : ∀ v ∈ W, (W.card : ℝ) / 2 - s + (m + m * W.card / s + 2) ≤ dW G W v)
    (x y : V) (hx : x ∈ W \ T) (hy : y ∈ W \ T) (hne : x ≠ y) :
    ∃ a ∈ W \ T, ∃ b ∈ W \ T, ∃ c ∈ W \ T, IsPathL G [x, a, b, c, y] := by
  have hjn : T.card ≤ W.card := card_le_card hT
  have hcard : (W \ T).card + T.card = W.card := card_sdiff_add_card_eq_card hT
  have hq : (m : ℝ) * W.card / s ≤ s - 2 := by
    rw [div_le_iff₀ hs]; nlinarith
  have hq0 : 0 ≤ (m : ℝ) * W.card / s := by positivity
  have hmn : (m : ℝ) * W.card = s * ((m : ℝ) * W.card / s) := by
    field_simp
  have hjR : (T.card : ℝ) ≤ m := by exact_mod_cast hTm
  have hjnR : (T.card : ℝ) ≤ W.card := by exact_mod_cast hjn
  have hcardR : ((W \ T).card : ℝ) = W.card - T.card := by
    have : ((W \ T).card : ℝ) + T.card = W.card := by exact_mod_cast hcard
    linarith
  apply path4 (W \ T) (s - (m : ℝ) * W.card / s) (by linarith) _ _ x y hx hy hne
  · have h1 := sdeg_sdiff (G := G) W T hT
    have h1' : (sdeg G W : ℝ) ≤ sdeg G (W \ T) + 2 * T.card * W.card := by exact_mod_cast h1
    rw [hcardR]
    have hsq : (s - (m : ℝ) * W.card / s) ^ 2 ≤ s ^ 2 - m * W.card := by
      nlinarith
    have : (0 : ℝ) ≤ T.card := Nat.cast_nonneg _
    nlinarith
  · intro v hv
    have hvW : v ∈ W := (mem_sdiff.1 hv).1
    have h1 := hdeg v hvW
    have h2 : (dW G W v : ℝ) ≤ dW G (W \ T) v + T.card := by exact_mod_cast dW_sdiff_add W T v
    rw [hcardR]
    have : (0 : ℝ) ≤ T.card := Nat.cast_nonneg _
    linarith

end Path4b

section Dist3

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

variable (G) in
/-- `u` and `v` are joined by a walk with at most three edges inside `W`. -/
def Near3 (W : Finset V) (u v : V) : Prop :=
  u = v ∨ G.Adj u v ∨ (∃ c ∈ W, G.Adj u c ∧ G.Adj c v) ∨
    (∃ c ∈ W, ∃ d ∈ W, G.Adj u c ∧ G.Adj c d ∧ G.Adj d v)

lemma near3_symm {W : Finset V} {u v : V} (h : Near3 G W u v) : Near3 G W v u := by
  rcases h with h | h | ⟨c, hc, h1, h2⟩ | ⟨c, hc, d, hd, h1, h2, h3⟩
  · exact Or.inl h.symm
  · exact Or.inr (Or.inl h.symm)
  · exact Or.inr (Or.inr (Or.inl ⟨c, hc, h2.symm, h1.symm⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨d, hd, c, hc, h3.symm, h2.symm, h1.symm⟩))

/-- Degrees near two far-apart vertices. -/
lemma far_pair_bounds (W : Finset V) (x y : V) (hx : x ∈ W) (hy : y ∈ W)
    (hfar : ¬ Near3 G W x y) (hd : dW G W x ≤ dW G W y) :
    (∀ v ∈ insert x (insert y (nbW G W x ∪ nbW G W y)), dW G W v + dW G W x + 2 ≤ W.card) ∧
      insert x (insert y (nbW G W x ∪ nbW G W y)) ⊆ W ∧
      (insert x (insert y (nbW G W x ∪ nbW G W y))).card = dW G W x + dW G W y + 2 := by
  simp only [Near3, not_or, not_exists, not_and] at hfar
  obtain ⟨hne, hnadj, hno2, hno3⟩ := hfar
  have hxNy : x ∉ nbW G W y := fun h => hnadj (mem_nbW.1 h).2.symm
  have hyNx : y ∉ nbW G W x := fun h => hnadj (mem_nbW.1 h).2
  have hdisj : Disjoint (nbW G W x) (nbW G W y) := by
    rw [disjoint_nbW_iff]; intro c hc h1 h2; exact hno2 c hc h1 h2.symm
  have hpair : ({x, y} : Finset V) ⊆ W := by
    intro v hv; simp only [mem_insert, mem_singleton] at hv; rcases hv with rfl | rfl <;> assumption
  have hpc : ({x, y} : Finset V).card = 2 := card_pair hne
  have hD : insert x (insert y (nbW G W x ∪ nbW G W y)) = (nbW G W x ∪ nbW G W y) ∪ {x, y} := by
    ext v; simp only [mem_insert, mem_union, mem_singleton]; tauto
  have hDdisj : Disjoint (nbW G W x ∪ nbW G W y) {x, y} := by
    rw [disjoint_union_left]
    constructor
    · rw [disjoint_right]; intro v hv hvN
      simp only [mem_insert, mem_singleton] at hv
      rcases hv with rfl | rfl
      · exact notMem_nbW_self W _ hvN
      · exact hyNx hvN
    · rw [disjoint_right]; intro v hv hvN
      simp only [mem_insert, mem_singleton] at hv
      rcases hv with rfl | rfl
      · exact hxNy hvN
      · exact notMem_nbW_self W _ hvN
  refine ⟨?_, ?_, ?_⟩
  · intro v hv
    rw [hD, mem_union, mem_union] at hv
    have hyb : dW G W y + dW G W x + 2 ≤ W.card := by
      have := card_three_le (nbW_subset (G := G) W y) (nbW_subset (G := G) W x) hpair
        hdisj.symm (by
          rw [disjoint_right]; intro v hv hvN
          simp only [mem_insert, mem_singleton] at hv
          rcases hv with rfl | rfl
          · exact hxNy hvN
          · exact notMem_nbW_self W _ hvN) (by
          rw [disjoint_right]; intro v hv hvN
          simp only [mem_insert, mem_singleton] at hv
          rcases hv with rfl | rfl
          · exact notMem_nbW_self W _ hvN
          · exact hyNx hvN)
      rw [hpc] at this
      exact this
    rcases hv with (hv | hv) | hv
    · -- `v` is a neighbour of `x`
      have hv' := mem_nbW.1 hv
      have hvy : v ≠ y := fun e => hyNx (e ▸ hv)
      have hvNy : v ∉ nbW G W y := fun h => hno2 v hv'.1 hv'.2 (mem_nbW.1 h).2.symm
      have hyNv : y ∉ nbW G W v := fun h => hno2 v hv'.1 hv'.2 (mem_nbW.1 h).2
      have h1 := card_three_le (nbW_subset (G := G) W v) (nbW_subset (G := G) W y)
        (show ({y, v} : Finset V) ⊆ W by
          intro u hu; simp only [mem_insert, mem_singleton] at hu
          rcases hu with rfl | rfl
          · exact hy
          · exact hv'.1)
        (by rw [disjoint_nbW_iff]; intro c hc h1 h2; exact hno3 v hv'.1 c hc hv'.2 h1 h2.symm)
        (by
          rw [disjoint_right]; intro u hu huN
          simp only [mem_insert, mem_singleton] at hu
          rcases hu with rfl | rfl
          · exact hyNv huN
          · exact notMem_nbW_self W _ huN)
        (by
          rw [disjoint_right]; intro u hu huN
          simp only [mem_insert, mem_singleton] at hu
          rcases hu with rfl | rfl
          · exact notMem_nbW_self W _ huN
          · exact hvNy huN)
      rw [card_pair hvy.symm] at h1
      unfold dW at hd ⊢
      omega
    · -- `v` is a neighbour of `y`
      have hv' := mem_nbW.1 hv
      have hvx : v ≠ x := fun e => hxNy (e ▸ hv)
      have hvNx : v ∉ nbW G W x := fun h => hno2 v hv'.1 (mem_nbW.1 h).2 hv'.2.symm
      have hxNv : x ∉ nbW G W v := fun h => hno2 v hv'.1 (mem_nbW.1 h).2.symm hv'.2.symm
      have h1 := card_three_le (nbW_subset (G := G) W v) (nbW_subset (G := G) W x)
        (show ({x, v} : Finset V) ⊆ W by
          intro u hu; simp only [mem_insert, mem_singleton] at hu
          rcases hu with rfl | rfl
          · exact hx
          · exact hv'.1)
        (by rw [disjoint_nbW_iff]; intro c hc h1 h2; exact hno3 c hc v hv'.1 h2 h1.symm hv'.2.symm)
        (by
          rw [disjoint_right]; intro u hu huN
          simp only [mem_insert, mem_singleton] at hu
          rcases hu with rfl | rfl
          · exact hxNv huN
          · exact notMem_nbW_self W _ huN)
        (by
          rw [disjoint_right]; intro u hu huN
          simp only [mem_insert, mem_singleton] at hu
          rcases hu with rfl | rfl
          · exact notMem_nbW_self W _ huN
          · exact hvNx huN)
      rw [card_pair hvx.symm] at h1
      unfold dW at ⊢
      omega
    · simp only [mem_insert, mem_singleton] at hv
      rcases hv with rfl | rfl
      · omega
      · omega
  · rw [hD]; exact union_subset (union_subset (nbW_subset _ _) (nbW_subset _ _)) hpair
  · rw [hD, card_union_of_disjoint hDdisj, card_union_of_disjoint hdisj, hpc]
    rfl

/-- The weighted degree-sum bound used in the proof of Lemma 3.1. -/
lemma dist3_sum (W B S : Finset V) (hB : B ⊆ W) (X Δ M : ℝ) (hMD : M ≤ Δ)
    (hBX : ∀ v ∈ B, (dW G W v : ℝ) ≤ X) (hΔ : ∀ v ∈ W, (dW G W v : ℝ) ≤ Δ)
    (hM : ∀ v ∈ W, v ∉ S → (dW G W v : ℝ) ≤ M) :
    (sdeg G W : ℝ) ≤ B.card * X + S.card * (Δ - M) + (W.card - B.card) * M := by
  have e1 : (sdeg G W : ℝ) = (∑ v ∈ B, (dW G W v : ℝ)) + (∑ v ∈ (W \ B) ∩ S, (dW G W v : ℝ)) +
      (∑ v ∈ (W \ B) \ S, (dW G W v : ℝ)) := by
    unfold sdeg
    push_cast
    rw [add_assoc, sum_inter_add_sum_sdiff, add_comm, sum_sdiff hB]
  have h1 : (∑ v ∈ B, (dW G W v : ℝ)) ≤ B.card * X := sum_le_card_mul_real B _ X hBX
  have h2 : (∑ v ∈ (W \ B) ∩ S, (dW G W v : ℝ)) ≤ ((W \ B) ∩ S).card * Δ :=
    sum_le_card_mul_real _ _ Δ (fun v hv => hΔ v (mem_sdiff.1 (mem_inter.1 hv).1).1)
  have h3 : (∑ v ∈ (W \ B) \ S, (dW G W v : ℝ)) ≤ ((W \ B) \ S).card * M :=
    sum_le_card_mul_real _ _ M (fun v hv => hM v (mem_sdiff.1 (mem_sdiff.1 hv).1).1
      (mem_sdiff.1 hv).2)
  have h4 : ((W \ B) ∩ S).card + ((W \ B) \ S).card = (W \ B).card := card_inter_add_card_sdiff _ _
  have h5 : (W \ B).card + B.card = W.card := card_sdiff_add_card_eq_card hB
  have h6 : ((W \ B) ∩ S).card ≤ S.card := card_le_card inter_subset_right
  have h4' : (((W \ B) ∩ S).card : ℝ) + ((W \ B) \ S).card + B.card = W.card := by
    exact_mod_cast (by omega : ((W \ B) ∩ S).card + ((W \ B) \ S).card + B.card = W.card)
  have h6' : (((W \ B) ∩ S).card : ℝ) ≤ S.card := by exact_mod_cast h6
  have h7 : (((W \ B) ∩ S).card : ℝ) * (Δ - M) ≤ S.card * (Δ - M) :=
    mul_le_mul_of_nonneg_right h6' (by linarith)
  have hj : (((W \ B) \ S).card : ℝ) = W.card - B.card - ((W \ B) ∩ S).card := by linarith
  rw [hj] at h3
  have h8 : (((W \ B) ∩ S).card : ℝ) * Δ + (W.card - B.card - ((W \ B) ∩ S).card) * M =
      (((W \ B) ∩ S).card : ℝ) * (Δ - M) + (W.card - B.card) * M := by ring
  linarith

lemma dist3_claim (n σ Δ X a ρ : ℝ) (hn : 0 ≤ n) (hΔ0 : 0 ≤ Δ) (hρ : 0 ≤ ρ) (hρ2 : 2 * ρ ^ 2 ≤ σ - n ^ 2 / 2 + n)
    (hσ : n ^ 2 < 2 * σ) (hΔn : σ ≤ n * Δ) (hsum : σ ≤ a * Δ + (n - a) * X)
    (ha : a < n / 2 + ρ) (ha0 : 0 ≤ a) (hΔ : Δ + 1 < n / 2 + ρ) : n < X + Δ + 2 := by
  by_contra hc
  push Not at hc
  have hn0 : 0 < n := by
    rcases eq_or_lt_of_le hn with h | h
    · rw [← h] at hΔn hσ; nlinarith
    · exact h
  have hΔ2 : n < 2 * Δ := by nlinarith
  have h1 : σ ≤ a * (2 * Δ + 2 - n) + n * (n - Δ - 2) := by
    have : (n - a) * X ≤ (n - a) * (n - Δ - 2) := by
      apply mul_le_mul_of_nonneg_left (by linarith)
      nlinarith
    nlinarith
  have h2 : a * (2 * Δ + 2 - n) ≤ (n / 2 + ρ) * (2 * Δ + 2 - n) :=
    mul_le_mul_of_nonneg_right ha.le (by linarith)
  have h3 : ρ * (2 * ρ - 2 * (Δ + 1) + n) ≤ 0 := by nlinarith
  have h4 : 0 < 2 * ρ - 2 * (Δ + 1) + n := by linarith
  have h5 : ρ ≤ 0 := by
    by_contra h6
    push Not at h6
    nlinarith [mul_pos h6 h4]
  nlinarith

lemma dist3_final (n σ Δ X b s ρ : ℝ) (hρ2 : 2 * ρ ^ 2 ≤ σ - n ^ 2 / 2 + n)
    (hσ : n ^ 2 < 2 * σ) (hb : n / 2 - ρ < b) (hXM : 2 * X + 2 ≤ n)
    (hsS : s ≤ n - 2 * X - 2) (hclaim : n < X + Δ + 2)
    (hsum : σ ≤ b * X + s * (Δ - (n - X - 2)) + (n - b) * (n - X - 2))
    (hΔ : Δ + 1 < n / 2 + ρ) : False := by
  have k1 : 0 ≤ (b - (n / 2 - ρ)) * ((n - X - 2) - X) := mul_nonneg (by linarith) (by linarith)
  have k2 : 0 ≤ ((n - 2 * X - 2) - s) * (Δ - (n - X - 2)) := mul_nonneg (by linarith) (by linarith)
  have k3 := sq_nonneg (n / 2 - ρ - 1 - X)
  rcases eq_or_lt_of_le hXM with hL | hL
  · nlinarith
  · have k4 : 0 < (n / 2 + ρ - Δ - 1) * (n - 2 * X - 2) := mul_pos (by linarith) (by linarith)
    nlinarith

/-- Lemma 3.1 of Bucić–Chen–Ma (for more than `|W|²/4` edges): a large vertex set whose vertices
are pairwise joined by walks of length at most three. -/
lemma dist3_set (W : Finset V) (hW : (W.card : ℝ) ^ 2 < 2 * sdeg G W) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (hρ2 : 2 * ρ ^ 2 ≤ sdeg G W - (W.card : ℝ) ^ 2 / 2 + W.card) :
    ∃ A ⊆ W, (W.card : ℝ) / 2 + ρ ≤ A.card ∧ ∀ a ∈ A, ∀ b ∈ A, Near3 G W a b := by
  classical
  have hne : W.Nonempty := by
    rcases W.eq_empty_or_nonempty with h | h
    · exfalso; rw [h] at hW; simp [sdeg] at hW
    · exact h
  obtain ⟨v₀, hv₀, hmax⟩ := exists_max_image W (dW G W) hne
  have hσle := sdeg_le (G := G) W
  have hσleR : (sdeg G W : ℝ) + W.card ≤ W.card * W.card := by exact_mod_cast hσle
  by_cases h1 : (W.card : ℝ) / 2 + ρ ≤ dW G W v₀ + 1
  · refine ⟨insert v₀ (nbW G W v₀), insert_subset hv₀ (nbW_subset _ _), ?_, ?_⟩
    · rw [card_insert_of_notMem (notMem_nbW_self W v₀)]
      push_cast; exact h1
    · intro a ha b hb
      rw [mem_insert] at ha hb
      rcases ha with rfl | ha <;> rcases hb with rfl | hb
      · exact Or.inl rfl
      · exact Or.inr (Or.inl (mem_nbW.1 hb).2)
      · exact Or.inr (Or.inl (mem_nbW.1 ha).2.symm)
      · by_cases hab : a = b
        · exact Or.inl hab
        · exact Or.inr (Or.inr (Or.inl ⟨v₀, hv₀, (mem_nbW.1 ha).2.symm, (mem_nbW.1 hb).2⟩))
  push Not at h1
  by_cases h2 : ∀ a ∈ W, ∀ b ∈ W, Near3 G W a b
  · refine ⟨W, subset_refl W, ?_, h2⟩
    nlinarith
  push Not at h2
  obtain ⟨a₀, ha₀, b₀, hb₀, hab₀⟩ := h2
  -- the "bad" vertices
  have hBadne : (W.filter (fun x => ∃ y ∈ W, dW G W x ≤ dW G W y ∧ ¬ Near3 G W x y)).Nonempty := by
    rcases le_total (dW G W a₀) (dW G W b₀) with h | h
    · exact ⟨a₀, mem_filter.2 ⟨ha₀, b₀, hb₀, h, hab₀⟩⟩
    · exact ⟨b₀, mem_filter.2 ⟨hb₀, a₀, ha₀, h, fun hh => hab₀ (near3_symm hh)⟩⟩
  obtain ⟨x, hxBad, hxmax⟩ := exists_max_image _ (dW G W) hBadne
  obtain ⟨hx, y, hy, hxy, hfar⟩ := mem_filter.1 hxBad
  refine ⟨W.filter (fun v => dW G W x < dW G W v), filter_subset _ _, ?_, ?_⟩
  swap
  · intro a ha b hb
    rw [mem_filter] at ha hb
    by_contra hab
    rcases le_total (dW G W a) (dW G W b) with h | h
    · have := hxmax a (mem_filter.2 ⟨ha.1, b, hb.1, h, hab⟩)
      omega
    · have := hxmax b (mem_filter.2 ⟨hb.1, a, ha.1, h, fun hh => hab (near3_symm hh)⟩)
      omega
  by_contra hA
  push Not at hA
  set A := W.filter (fun v => dW G W x < dW G W v) with hAdef
  set B := W.filter (fun v => dW G W v ≤ dW G W x) with hBdef
  have hAB : A.card + B.card = W.card := by
    have := card_filter_add_card_filter_not (s := W) (fun v => dW G W x < dW G W v)
    simp only [not_lt] at this
    exact this
  have hABR : (A.card : ℝ) + B.card = W.card := by exact_mod_cast hAB
  have hΔall : ∀ v ∈ W, (dW G W v : ℝ) ≤ dW G W v₀ := fun v hv => by exact_mod_cast hmax v hv
  have hBX : ∀ v ∈ B, (dW G W v : ℝ) ≤ dW G W x := fun v hv => by
    exact_mod_cast (mem_filter.1 hv).2
  -- the claim `X > n - Δ - 2`
  have hsum1 := dist3_sum W B W (filter_subset _ _) (dW G W x) (dW G W v₀) (dW G W v₀) le_rfl
    hBX hΔall (fun v hv hvW => absurd hv hvW)
  have hΔn : (sdeg G W : ℝ) ≤ W.card * dW G W v₀ := by
    have := sum_le_card_mul_real W (dW G W) _ hΔall
    unfold sdeg; push_cast; exact this
  have hclaim : (W.card : ℝ) < dW G W x + dW G W v₀ + 2 :=
    dist3_claim W.card (sdeg G W) (dW G W v₀) (dW G W x) A.card ρ (Nat.cast_nonneg _)
      (Nat.cast_nonneg _) hρ hρ2 hW hΔn (by nlinarith) hA (Nat.cast_nonneg _) h1
  obtain ⟨hDb, hDW, hDc⟩ := far_pair_bounds W x y hx hy hfar hxy
  set D := insert x (insert y (nbW G W x ∪ nbW G W y)) with hDdef
  have hXM : dW G W x + dW G W x + 2 ≤ W.card := hDb x (mem_insert_self _ _)
  have hSc : (W \ D).card + D.card = W.card := card_sdiff_add_card_eq_card hDW
  have hsum2 := dist3_sum W B (W \ D) (filter_subset _ _) (dW G W x) (dW G W v₀)
    ((W.card : ℝ) - dW G W x - 2) (by linarith) hBX hΔall (fun v hv hvS => by
      have hvD : v ∈ D := by
        by_contra hh; exact hvS (mem_sdiff.2 ⟨hv, hh⟩)
      have := hDb v hvD
      have : (dW G W v : ℝ) + dW G W x + 2 ≤ W.card := by exact_mod_cast this
      linarith)
  have hScR : ((W \ D).card : ℝ) ≤ W.card - 2 * dW G W x - 2 := by
    have : (W \ D).card + 2 * dW G W x + 2 ≤ W.card := by omega
    have : ((W \ D).card : ℝ) + 2 * dW G W x + 2 ≤ W.card := by exact_mod_cast this
    linarith
  exact dist3_final W.card (sdeg G W) (dW G W v₀) (dW G W x) B.card ((W \ D).card) ρ hρ2 hW
    (by linarith) (by exact_mod_cast (by omega : 2 * dW G W x + 2 ≤ W.card)) hScR hclaim
    (by linarith) h1

end Dist3

section Lists

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}

lemma IsPathL.append_tail {Q l : List V} {y : V} (hQ : IsPathL G Q) (hy : Q.getLast? = some y)
    (hl : IsPathL G (y :: l)) (hd : ∀ u ∈ l, u ∉ Q) : IsPathL G (Q ++ l) := by
  refine ⟨List.nodup_append.2 ⟨hQ.1, (List.nodup_cons.1 hl.1).2, fun a ha b hb e => hd b hb (e ▸ ha)⟩,
    List.isChain_append.2 ⟨hQ.2, hl.2.tail, ?_⟩⟩
  intro a ha b hb
  rw [hy, Option.mem_def, Option.some.injEq] at ha
  subst ha
  rcases l with _ | ⟨c, l⟩
  · simp at hb
  · simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hb
    subst hb
    exact (List.isChain_cons_cons.1 hl.2).1

lemma exists_getLast (v : V) (l : List V) : ∃ u, (v :: l).getLast? = some u ∧ u ∈ v :: l :=
  ⟨_, List.getLast?_eq_getLast (List.cons_ne_nil v l), List.getLast_mem _⟩

lemma infix_of_eq {l : List V} {a b : V} (A B : List V) (h : l = A ++ [a, b] ++ B) :
    [a, b] <:+: l := h ▸ List.infix_append A [a, b] B

lemma cyc_apply {α : Type*} {col : Sym2 V → α} {m : ℕ} (hcyc : CycRainbow G col m) {l : List V}
    (hp : IsPathL G l) (hlen : l.length = m) (hclose : ∀ a ∈ l.head?, ∀ b ∈ l.getLast?, G.Adj b a)
    {x y z w : V} (h1 : [x, y] <:+: l ++ l.take 1) (h2 : [z, w] <:+: l ++ l.take 1)
    (hne : s(x, y) ≠ s(z, w)) : col s(x, y) ≠ col s(z, w) :=
  fun h => hne (hcyc l hp hlen hclose x y z w h1 h2 h)

lemma pathL_pair {a b : V} (h : G.Adj a b) : IsPathL G [a, b] :=
  ⟨by simp [G.ne_of_adj h], by simp [h]⟩

lemma pathL_single (a : V) : IsPathL G [a] := ⟨List.nodup_singleton a, List.isChain_singleton a⟩

end Lists

section Dense

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

lemma dense_adjacent {r k : ℕ} (col : Sym2 V → Fin r) (hk : 3 ≤ k)
    (hcyc : CycRainbow G col (2 * k + 1)) (Y : Finset V) (hmin : ∀ z ∈ Y, 5 * k ≤ dW G Y z)
    (hcommon : ∀ a ∈ Y, ∀ b ∈ Y, 10 * k ≤ (nbW G Y a ∩ nbW G Y b).card)
    (q p z : V) (hq : q ∈ Y) (hz : z ∈ Y) (hqp : G.Adj q p) (hpz : G.Adj p z)
    (hqz : q ≠ z) : col s(q, p) ≠ col s(p, z) := by
  obtain ⟨l, hl, hpath, hlT⟩ := greedy Y (5 * k) hmin (2 * k - 3) z {q, p} hz
    (by rw [card_pair (G.ne_of_adj hqp)]; omega)
  obtain ⟨u, hu, humem⟩ := exists_getLast z l
  have huY : u ∈ Y := by
    rcases List.mem_cons.1 humem with h | h
    · exact h ▸ hz
    · exact (hlT u h).1
  have hF : (insert p (z :: l).toFinset).card < (nbW G Y u ∩ nbW G Y q).card := by
    have h1 := card_insert_le p (z :: l).toFinset
    have h2 := List.toFinset_card_le (z :: l)
    have h3 := hcommon u huY q hq
    simp only [List.length_cons, hl] at h2
    omega
  obtain ⟨b, hbC, hbF⟩ := exists_mem_notMem_of_card_lt_card hF
  rw [mem_inter, mem_nbW, mem_nbW] at hbC
  simp only [mem_insert, List.mem_toFinset, not_or] at hbF
  have hlT' : ∀ v ∈ l, v ≠ q ∧ v ≠ p := fun v hv => by
    have := (hlT v hv).2; simp only [mem_insert, mem_singleton, not_or] at this; exact this
  have hP1 : IsPathL G ([q, p] ++ (z :: l)) := by
    refine (pathL_pair hqp).append hpath ?_ (by simpa using hpz)
    intro v hv
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rcases List.mem_cons.1 hv with rfl | hv
    · exact fun h => h.elim (fun e => hqz e.symm) (fun e => G.ne_of_adj hpz e.symm)
    · exact fun h => h.elim (fun e => (hlT' v hv).1 e) (fun e => (hlT' v hv).2 e)
  have hP2 : IsPathL G ([q, p] ++ (z :: l) ++ [b]) := by
    refine hP1.append (pathL_single b) ?_ ?_
    · intro v hv
      simp only [List.mem_singleton] at hv
      subst hv
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
      rintro ((h | h) | h)
      · exact G.ne_of_adj hbC.2.2 h.symm
      · exact hbF.1 h
      · exact hbF.2 (List.mem_cons.2 h)
    · intro a ha c hc
      rw [List.getLast?_append_of_ne_nil _ (List.cons_ne_nil _ _), hu] at ha
      simp only [Option.mem_def, Option.some.injEq, List.head?_cons] at ha hc
      subst ha; subst hc
      exact hbC.1.2
  refine cyc_apply hcyc hP2 ?_ ?_ ?_ ?_ ?_
  · simp [hl]; omega
  · intro a ha c hc
    rw [List.getLast?_concat, Option.mem_def, Option.some.injEq] at hc
    simp only [List.cons_append, List.head?_cons, Option.mem_def, Option.some.injEq] at ha
    subst ha; subst hc
    exact hbC.2.2.symm
  · exact infix_of_eq [] (z :: l ++ [b] ++ [q]) (by simp)
  · exact infix_of_eq [q] (l ++ [b] ++ [q]) (by simp)
  · intro h
    rcases Sym2.eq_iff.1 h with ⟨h1, _⟩ | ⟨h1, _⟩
    · exact G.ne_of_adj hqp h1
    · exact hqz h1

lemma dense_disjoint {r k : ℕ} (col : Sym2 V → Fin r) (hk : 3 ≤ k)
    (hcyc : CycRainbow G col (2 * k + 1)) (Y : Finset V) (hmin : ∀ z ∈ Y, 5 * k ≤ dW G Y z)
    (hcommon : ∀ a ∈ Y, ∀ b ∈ Y, 10 * k ≤ (nbW G Y a ∩ nbW G Y b).card)
    (q p z w : V) (hq : q ∈ Y) (hp : p ∈ Y) (hz : z ∈ Y) (hw : w ∈ Y) (hqp : G.Adj q p)
    (hzw : G.Adj z w) (hpz : p ≠ z) (hpw : p ≠ w) (hqz : q ≠ z) (hqw : q ≠ w) :
    col s(q, p) ≠ col s(z, w) := by
  -- a common neighbour `a` of `p` and `z`
  have hFa : ({q, w} : Finset V).card < (nbW G Y p ∩ nbW G Y z).card := by
    have := card_le_two (a := q) (b := w)
    have := hcommon p hp z hz
    omega
  obtain ⟨a, haC, haF⟩ := exists_mem_notMem_of_card_lt_card hFa
  rw [mem_inter, mem_nbW, mem_nbW] at haC
  simp only [mem_insert, mem_singleton, not_or] at haF
  have hT : ({q, p, a, z} : Finset V).card + (2 * k - 5) ≤ 5 * k := by
    have : ({q, p, a, z} : Finset V).card ≤ 4 := by
      refine (card_insert_le _ _).trans ?_
      refine Nat.succ_le_succ ((card_insert_le _ _).trans ?_)
      exact Nat.succ_le_succ card_le_two
    omega
  obtain ⟨l, hl, hpath, hlT⟩ := greedy Y (5 * k) hmin (2 * k - 5) w {q, p, a, z} hw hT
  obtain ⟨u, hu, humem⟩ := exists_getLast w l
  have huY : u ∈ Y := by
    rcases List.mem_cons.1 humem with h | h
    · exact h ▸ hw
    · exact (hlT u h).1
  have hF : (insert p (insert a (insert z (w :: l).toFinset))).card <
      (nbW G Y u ∩ nbW G Y q).card := by
    have h1 := card_insert_le p (insert a (insert z (w :: l).toFinset))
    have h1' := card_insert_le a (insert z (w :: l).toFinset)
    have h1'' := card_insert_le z (w :: l).toFinset
    have h2 := List.toFinset_card_le (w :: l)
    have h3 := hcommon u huY q hq
    simp only [List.length_cons, hl] at h2
    omega
  obtain ⟨b, hbC, hbF⟩ := exists_mem_notMem_of_card_lt_card hF
  rw [mem_inter, mem_nbW, mem_nbW] at hbC
  simp only [mem_insert, List.mem_toFinset, not_or] at hbF
  have hlT' : ∀ v ∈ l, v ≠ q ∧ v ≠ p ∧ v ≠ a ∧ v ≠ z := fun v hv => by
    have := (hlT v hv).2; simp only [mem_insert, mem_singleton, not_or] at this; exact this
  have hP0 : IsPathL G [q, p, a, z] := by
    refine ⟨?_, ?_⟩
    · have e1 := G.ne_of_adj hqp
      have e2 := G.ne_of_adj haC.1.2
      have e3 := G.ne_of_adj haC.2.2
      have e4 : q ≠ a := fun h => haF.1 h.symm
      simp [e1, e2, e3.symm, e4, hqz, hpz]
    · simp only [List.isChain_cons_cons, List.isChain_singleton, and_true]
      exact ⟨hqp, haC.1.2, haC.2.2.symm⟩
  have hP1 : IsPathL G ([q, p, a, z] ++ (w :: l)) := by
    refine hP0.append hpath ?_ (by simpa using hzw)
    intro v hv
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rcases List.mem_cons.1 hv with rfl | hv
    · rintro (h | h | h | h)
      · exact hqw h.symm
      · exact hpw h.symm
      · exact haF.2 h.symm
      · exact G.ne_of_adj hzw h.symm
    · have := hlT' v hv
      rintro (h | h | h | h)
      · exact this.1 h
      · exact this.2.1 h
      · exact this.2.2.1 h
      · exact this.2.2.2 h
  have hP2 : IsPathL G ([q, p, a, z] ++ (w :: l) ++ [b]) := by
    refine hP1.append (pathL_single b) ?_ ?_
    · intro v hv
      simp only [List.mem_singleton] at hv
      subst hv
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
      rintro ((h | h | h | h) | h)
      · exact G.ne_of_adj hbC.2.2 h.symm
      · exact hbF.1 h
      · exact hbF.2.1 h
      · exact hbF.2.2.1 h
      · exact hbF.2.2.2 (List.mem_cons.2 h)
    · intro a' ha' c hc
      rw [List.getLast?_append_of_ne_nil _ (List.cons_ne_nil _ _), hu] at ha'
      simp only [Option.mem_def, Option.some.injEq, List.head?_cons] at ha' hc
      subst ha'; subst hc
      exact hbC.1.2
  refine cyc_apply hcyc hP2 ?_ ?_ ?_ ?_ ?_
  · simp [hl]; omega
  · intro a' ha' c hc
    rw [List.getLast?_concat, Option.mem_def, Option.some.injEq] at hc
    simp only [List.cons_append, List.head?_cons, Option.mem_def, Option.some.injEq] at ha'
    subst ha'; subst hc
    exact hbC.2.2.symm
  · exact infix_of_eq [] ([a, z, w] ++ l ++ [b] ++ [q]) (by simp)
  · exact infix_of_eq [q, p, a] (l ++ [b] ++ [q]) (by simp)
  · intro h
    rcases Sym2.eq_iff.1 h with ⟨h1, _⟩ | ⟨h1, _⟩
    · exact hqz h1
    · exact hqw h1

/-- In a set `Y` of minimum degree `≥ |Y|/2 + 5k` (so any two vertices have `10k` common
neighbours) any two distinct edges lie on a common `C_{2k+1}`. -/
lemma dense_edges {r k : ℕ} (col : Sym2 V → Fin r) (hk : 3 ≤ k)
    (hcyc : CycRainbow G col (2 * k + 1)) (Y : Finset V) (hmin : ∀ z ∈ Y, 5 * k ≤ dW G Y z)
    (hcommon : ∀ a ∈ Y, ∀ b ∈ Y, 10 * k ≤ (nbW G Y a ∩ nbW G Y b).card)
    (u₁ v₁ u₂ v₂ : V) (hu₁ : u₁ ∈ Y) (hv₁ : v₁ ∈ Y) (hu₂ : u₂ ∈ Y) (hv₂ : v₂ ∈ Y)
    (h₁ : G.Adj u₁ v₁) (h₂ : G.Adj u₂ v₂) (hne : s(u₁, v₁) ≠ s(u₂, v₂)) :
    col s(u₁, v₁) ≠ col s(u₂, v₂) := by
  by_cases h11 : u₁ = u₂
  · subst h11
    have := dense_adjacent col hk hcyc Y hmin hcommon v₁ u₁ v₂ hv₁ hv₂ h₁.symm h₂
      (fun e => hne (by rw [e]))
    rwa [Sym2.eq_swap (a := v₁)] at this
  by_cases h12 : u₁ = v₂
  · subst h12
    have := dense_adjacent col hk hcyc Y hmin hcommon v₁ u₁ u₂ hv₁ hu₂ h₁.symm h₂.symm
      (fun e => hne (by rw [e]; exact Sym2.eq_swap))
    rwa [Sym2.eq_swap (a := v₁), Sym2.eq_swap (a := u₁) (b := u₂)] at this
  by_cases h21 : v₁ = u₂
  · subst h21
    exact dense_adjacent col hk hcyc Y hmin hcommon u₁ v₁ v₂ hu₁ hv₂ h₁ h₂
      (fun e => hne (by rw [e]; exact Sym2.eq_swap))
  by_cases h22 : v₁ = v₂
  · subst h22
    have := dense_adjacent col hk hcyc Y hmin hcommon u₁ v₁ u₂ hu₁ hu₂ h₁ h₂.symm h11
    rwa [Sym2.eq_swap (a := v₁)] at this
  exact dense_disjoint col hk hcyc Y hmin hcommon u₁ v₁ u₂ v₂ hu₁ hv₁ hu₂ hv₂ h₁ h₂
    h21 h22 h11 h12

end Dense

section Claim1

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

variable (G) in
/-- A path with two or three edges from `x` to `y` whose inner vertices lie in `W \ S`. -/
def ShortPath (W S : Finset V) (x y : V) : Prop :=
  ∃ mid : List V, (mid.length = 1 ∨ mid.length = 2) ∧ IsPathL G (x :: mid ++ [y]) ∧
    ∀ v ∈ mid, v ∈ W ∧ v ∉ S

lemma ShortPath.symm {W S : Finset V} {x y : V} (h : ShortPath G W S x y) : ShortPath G W S y x := by
  obtain ⟨mid, hlen, hp, hm⟩ := h
  refine ⟨mid.reverse, by simpa using hlen, ?_, fun v hv => hm v (List.mem_reverse.1 hv)⟩
  have := hp.reverse
  simpa using this

lemma count_rainbow {r : ℕ} (col : Sym2 V → Fin r) (T : Finset (V × V))
    (h : ∀ p ∈ T, ∀ q ∈ T, s(p.1, p.2) ≠ s(q.1, q.2) → col s(p.1, p.2) ≠ col s(q.1, q.2)) :
    T.card ≤ 2 * r := by
  refine (card_le_two_mul_image T).trans (Nat.mul_le_mul_left 2 ?_)
  apply card_le_of_injOn_col col
  intro e₁ he₁ e₂ he₂ hc
  obtain ⟨p, hp, rfl⟩ := mem_image.1 he₁
  obtain ⟨q, hq, rfl⟩ := mem_image.1 he₂
  by_contra hne
  exact h p hp q hq hne hc

lemma card_adj_pairs (Y : Finset V) :
    ((Y ×ˢ Y).filter (fun p => G.Adj p.1 p.2)).card = sdeg G Y := by
  rw [card_filter, sum_product]
  unfold sdeg dW nbW
  apply sum_congr rfl
  intro u _
  rw [card_filter]

lemma claim1_dense {r k : ℕ} (col : Sym2 V → Fin r) (hk : 3 ≤ k)
    (hcyc : CycRainbow G col (2 * k + 1)) (W S : Finset V) (hS : S.card ≤ 5 * k) (x y : V)
    (hx : x ∈ W) (hy : y ∈ W) (hyS : y ∉ S) (hxy : x ≠ y)
    (hno : ¬ ShortPath G W S x y)
    (hXY : ((nbW G W y \ S).erase x).card ≤ ((nbW G W x \ S).erase y).card)
    (δ : ℝ) (hdeg : ∀ v ∈ W, δ ≤ dW G W v)
    (hθ : (W.card : ℝ) / 4 + 5 * k ≤ 3 * δ - W.card - 10 * k - 1) (hδ : 5 * k + 1 ≤ δ) :
    (δ - 5 * k - 1) * (3 * δ - W.card - 10 * k - 1) / 2 ≤ r := by
  set X := (nbW G W x \ S).erase y with hX
  set Y := (nbW G W y \ S).erase x with hY
  have hmX : ∀ v, v ∈ X ↔ v ≠ y ∧ v ∈ W ∧ G.Adj x v ∧ v ∉ S := fun v => by
    rw [hX, mem_erase, mem_sdiff, mem_nbW]; tauto
  have hmY : ∀ v, v ∈ Y ↔ v ≠ x ∧ v ∈ W ∧ G.Adj y v ∧ v ∉ S := fun v => by
    rw [hY, mem_erase, mem_sdiff, mem_nbW]; tauto
  -- no common neighbours, no edges between `X` and `Y`
  have hXYdisj : ∀ v ∈ X, v ∉ Y := by
    intro v hvX hvY
    have h1 := (hmX v).1 hvX
    have h2 := (hmY v).1 hvY
    apply hno
    refine ⟨[v], Or.inl rfl, ?_, by simpa using ⟨h1.2.1, h1.2.2.2⟩⟩
    refine ⟨?_, ?_⟩
    · simp [G.ne_of_adj h1.2.2.1, h1.1, hxy]
    · simp [h1.2.2.1, h2.2.2.1.symm]
  have hnoedge : ∀ a ∈ X, ∀ b ∈ Y, ¬ G.Adj a b := by
    intro a ha b hb hab
    have h1 := (hmX a).1 ha
    have h2 := (hmY b).1 hb
    apply hno
    refine ⟨[a, b], Or.inr rfl, ?_, ?_⟩
    · refine ⟨?_, ?_⟩
      · simp [G.ne_of_adj h1.2.2.1, h1.1, hxy, G.ne_of_adj hab, h2.1.symm,
          (G.ne_of_adj h2.2.2.1).symm]
      · simp [h1.2.2.1, hab, h2.2.2.1.symm]
    · intro v hv
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl
      · exact ⟨h1.2.1, h1.2.2.2⟩
      · exact ⟨h2.2.1, h2.2.2.2⟩
  have hXW : X ⊆ W := fun v hv => ((hmX v).1 hv).2.1
  have hYW : Y ⊆ W := fun v hv => ((hmY v).1 hv).2.1
  have hxX : x ∉ X := fun h => G.irrefl ((hmX x).1 h).2.2.1
  have hxY : x ∉ Y := fun h => ((hmY x).1 h).1 rfl
  have hcardXY : X.card + Y.card + 1 ≤ W.card := by
    have := card_three_le hXW hYW (singleton_subset_iff.2 hx)
      (disjoint_left.2 hXYdisj) (disjoint_singleton_right.2 hxX) (disjoint_singleton_right.2 hxY)
    simpa using this
  have hYlow : dW G W y ≤ Y.card + S.card + 1 := by
    unfold dW
    calc (nbW G W y).card ≤ (Y ∪ S ∪ {x}).card := by
          apply card_le_card
          intro v hv
          rw [mem_nbW] at hv
          by_cases hvS : v ∈ S
          · simp [hvS]
          by_cases hvx : v = x
          · simp [hvx]
          · simp only [mem_union, mem_singleton]
            exact Or.inl (Or.inl ((hmY v).2 ⟨hvx, hv.1, hv.2, hvS⟩))
      _ ≤ (Y ∪ S).card + ({x} : Finset V).card := card_union_le _ _
      _ ≤ Y.card + S.card + 1 := by
          have := card_union_le Y S; simp only [card_singleton]; omega
  -- degrees inside `Y`
  have hdY : ∀ z ∈ Y, dW G W z + X.card + Y.card + 1 ≤ dW G Y z + W.card := by
    intro z hz
    have hz' := (hmY z).1 hz
    have hzx : ¬ G.Adj z x := by
      intro h
      exact hXYdisj z ((hmX z).2 ⟨G.ne_of_adj hz'.2.2.1.symm, hz'.2.1, h.symm, hz'.2.2.2⟩) hz
    have hsub : nbW G W z ⊆ nbW G Y z ∪ (W \ (X ∪ Y ∪ {x})) := by
      intro v hv
      rw [mem_nbW] at hv
      by_cases hvY : v ∈ Y
      · exact mem_union_left _ (mem_nbW.2 ⟨hvY, hv.2⟩)
      · refine mem_union_right _ (mem_sdiff.2 ⟨hv.1, ?_⟩)
        simp only [mem_union, mem_singleton, not_or]
        refine ⟨⟨fun hvX => hnoedge v hvX z hz hv.2.symm, hvY⟩, ?_⟩
        rintro rfl; exact hzx hv.2
    have h1 := (card_le_card hsub).trans (card_union_le _ _)
    have h2 : (W \ (X ∪ Y ∪ {x})).card + (X ∪ Y ∪ {x}).card = W.card :=
      card_sdiff_add_card_eq_card (union_subset (union_subset hXW hYW) (singleton_subset_iff.2 hx))
    have h3 : (X ∪ Y ∪ {x}).card = X.card + Y.card + 1 := by
      rw [card_union_of_disjoint (disjoint_union_left.2 ⟨disjoint_singleton_right.2 hxX,
        disjoint_singleton_right.2 hxY⟩), card_union_of_disjoint (disjoint_left.2 hXYdisj),
        card_singleton]
    unfold dW at h1 ⊢
    omega
  have hYR : δ - 5 * k - 1 ≤ Y.card := by
    have := hdeg y hy
    have : (dW G W y : ℝ) ≤ Y.card + S.card + 1 := by exact_mod_cast hYlow
    have : (S.card : ℝ) ≤ 5 * k := by exact_mod_cast hS
    linarith
  have hθY : ∀ z ∈ Y, 3 * δ - W.card - 10 * k - 1 ≤ dW G Y z := by
    intro z hz
    have h1 := hdeg z (hYW hz)
    have h2 : (dW G W z : ℝ) + X.card + Y.card + 1 ≤ dW G Y z + W.card := by exact_mod_cast hdY z hz
    have h3 : (Y.card : ℝ) ≤ X.card := by exact_mod_cast hXY
    linarith
  have hYhalf : (2 : ℝ) * Y.card ≤ W.card := by
    have : (X.card : ℝ) + Y.card + 1 ≤ W.card := by exact_mod_cast hcardXY
    have h3 : (Y.card : ℝ) ≤ X.card := by exact_mod_cast hXY
    linarith
  have hmin : ∀ z ∈ Y, 5 * k ≤ dW G Y z := by
    intro z hz
    have := hθY z hz
    have : (5 * k : ℝ) ≤ dW G Y z := by
      have : (0 : ℝ) ≤ W.card := Nat.cast_nonneg _
      linarith
    exact_mod_cast this
  have hcommon : ∀ a ∈ Y, ∀ b ∈ Y, 10 * k ≤ (nbW G Y a ∩ nbW G Y b).card := by
    intro a ha b hb
    have h1 := hθY a ha
    have h2 := hθY b hb
    have h3 := card_union_add_card_inter (nbW G Y a) (nbW G Y b)
    have h4 := card_le_card (union_subset (nbW_subset (G := G) Y a) (nbW_subset (G := G) Y b))
    have h5 : ((nbW G Y a ∪ nbW G Y b).card : ℝ) + (nbW G Y a ∩ nbW G Y b).card =
        dW G Y a + dW G Y b := by exact_mod_cast h3
    have h6 : ((nbW G Y a ∪ nbW G Y b).card : ℝ) ≤ Y.card := by exact_mod_cast h4
    have : (10 * k : ℝ) ≤ (nbW G Y a ∩ nbW G Y b).card := by linarith
    exact_mod_cast this
  -- count the edges inside `Y`
  have hcount := count_rainbow col ((Y ×ˢ Y).filter (fun p => G.Adj p.1 p.2)) (by
    intro p hp q hq hne
    simp only [mem_filter, mem_product] at hp hq
    exact dense_edges col hk hcyc Y hmin hcommon p.1 p.2 q.1 q.2 hp.1.1 hp.1.2 hq.1.1 hq.1.2
      hp.2 hq.2 hne)
  rw [card_adj_pairs] at hcount
  have hsdeg : (Y.card : ℝ) * (3 * δ - W.card - 10 * k - 1) ≤ sdeg G Y := by
    have := sum_le_sum (fun z hz => hθY z hz)
    rw [sum_const, nsmul_eq_mul] at this
    unfold sdeg; push_cast; exact this
  have hcountR : (sdeg G Y : ℝ) ≤ 2 * r := by exact_mod_cast hcount
  have hθ0 : 0 ≤ 3 * δ - W.card - 10 * k - 1 := by
    have : (0 : ℝ) ≤ W.card := Nat.cast_nonneg _
    linarith
  have := mul_le_mul_of_nonneg_right hYR hθ0
  linarith

/-- Claim 1 of Bucić–Chen–Ma: either short paths avoiding any small set exist, or there are
many colours. -/
lemma claim1 {r k : ℕ} (col : Sym2 V → Fin r) (hk : 3 ≤ k)
    (hcyc : CycRainbow G col (2 * k + 1)) (W : Finset V) (δ : ℝ)
    (hdeg : ∀ v ∈ W, δ ≤ dW G W v)
    (hθ : (W.card : ℝ) / 4 + 5 * k ≤ 3 * δ - W.card - 10 * k - 1) (hδ : 5 * k + 1 ≤ δ) :
    (∀ S : Finset V, S.card ≤ 5 * k → ∀ x ∈ W, ∀ y ∈ W, x ∉ S → y ∉ S → x ≠ y →
      ShortPath G W S x y) ∨ (δ - 5 * k - 1) * (3 * δ - W.card - 10 * k - 1) / 2 ≤ r := by
  by_cases h : ∀ S : Finset V, S.card ≤ 5 * k → ∀ x ∈ W, ∀ y ∈ W, x ∉ S → y ∉ S → x ≠ y →
      ShortPath G W S x y
  · exact Or.inl h
  right
  push Not at h
  obtain ⟨S, hS, x, hx, y, hy, hxS, hyS, hxy, hno⟩ := h
  rcases le_total ((nbW G W y \ S).erase x).card ((nbW G W x \ S).erase y).card with h1 | h1
  · exact claim1_dense col hk hcyc W S hS x y hx hy hyS hxy hno h1 δ hdeg hθ hδ
  · exact claim1_dense col hk hcyc W S hS y x hy hx hxS hxy.symm (fun h => hno h.symm) h1 δ hdeg
      hθ hδ

end Claim1

section Case2Cycles

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

lemma IsPathL.skip {A C : List V} {r q p : V} (h : IsPathL G (A ++ r :: q :: p :: C))
    (hrp : G.Adj r p) : IsPathL G (A ++ r :: p :: C) := by
  refine ⟨h.1.sublist ?_, ?_⟩
  · exact List.Sublist.append_left (List.Sublist.cons₂ r (List.sublist_cons_self q (p :: C))) A
  · have h2 := h.2
    rw [List.isChain_append] at h2 ⊢
    obtain ⟨h2a, h2b, h2c⟩ := h2
    refine ⟨h2a, ?_, ?_⟩
    · rw [List.isChain_cons_cons] at h2b ⊢
      exact ⟨hrp, (List.isChain_cons_cons.1 h2b.2).2⟩
    · simpa using h2c

lemma IsPathL.prefix_cons {u : V} {mid B : List V} (h : IsPathL G (u :: mid ++ B)) :
    IsPathL G (u :: mid) :=
  h.sublist (List.prefix_append (u :: mid) B).isInfix

/-- A short path `u :: mid ++ [t]`: its last inner vertex is adjacent to `t`. -/
lemma shortPath_last_adj {u t : V} {mid : List V} (h : IsPathL G (u :: mid ++ [t])) :
    ∃ w, (u :: mid).getLast? = some w ∧ G.Adj w t := by
  obtain ⟨w, hw, _⟩ := exists_getLast u mid
  refine ⟨w, hw, ?_⟩
  have := (List.isChain_append.1 (by simpa using h.2 : ((u :: mid) ++ [t]).IsChain G.Adj)).2.2
  exact this w hw t (by simp)

lemma mem_of_shortPath_notMem {W : Finset V} {u t v : V} {mid : List V} {Q : List V} {S : Finset V}
    (hS : S = (Q.toFinset.erase u).erase t) (h : IsPathL G (u :: mid ++ [t]))
    (hm : ∀ v ∈ mid, v ∈ W ∧ v ∉ S) (hv : v ∈ mid) : v ∉ Q := by
  intro hvQ
  have hvS := (hm v hv).2
  have hnd := h.1
  simp only [List.cons_append, List.nodup_cons, List.mem_append, List.mem_singleton, not_or,
    List.nodup_append] at hnd
  have hvu : v ≠ u := fun e => hnd.1.1 (e ▸ hv)
  have hvt : v ≠ t := fun e => hnd.2.2.2 v hv t (by simp) e
  exact hvS (hS ▸ mem_erase.2 ⟨hvt, mem_erase.2 ⟨hvu, List.mem_toFinset.2 hvQ⟩⟩)

lemma getLast?_append_of_cons {Q mid : List V} {u w : V} (hu : Q.getLast? = some u)
    (hw : (u :: mid).getLast? = some w) : (Q ++ mid).getLast? = some w := by
  rcases mid with _ | ⟨a, mid⟩
  · simp only [List.getLast?_singleton, Option.some.injEq] at hw
    subst hw; simpa using hu
  · rw [List.getLast?_append_of_ne_nil _ (List.cons_ne_nil _ _)]
    rw [List.getLast?_cons_cons] at hw
    exact hw

end Case2Cycles

section Case2Shared

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Case 2, two good edges `zx`, `xy` sharing the vertex `x` (Figure 3(a) of Bucić–Chen–Ma). -/
lemma case2_shared {R k : ℕ} (col : Sym2 V → Fin R) (hk : 4 ≤ k)
    (hcyc : CycRainbow G col (2 * k + 1)) (W : Finset V) (D : ℕ)
    (hD : ∀ u ∈ W, D ≤ dW G W u) (hD2 : 2 * k + 7 ≤ D)
    (hshort : ∀ S : Finset V, S.card ≤ 5 * k → ∀ x ∈ W, ∀ y ∈ W, x ∉ S → y ∉ S → x ≠ y →
      ShortPath G W S x y)
    (p q t : V) (hp : p ∈ W) (hpq : G.Adj p q) (htp : G.Adj p t) (htq : G.Adj q t)
    (x y z : V) (hx : x ∈ W) (hy : y ∈ W) (hz : z ∈ W) (hxy : G.Adj x y) (hxz : G.Adj x z)
    (hyz : y ≠ z) (hxp : x ≠ p) (hxq : x ≠ q) (hyp : y ≠ p) (hyq : y ≠ q) (hzp : z ≠ p)
    (hzq : z ≠ q) (htx : t ≠ x) (hty : t ≠ y) (htz : t ≠ z) (hqW : q ∈ W) (htW : t ∈ W) :
    col s(z, x) ≠ col s(x, y) := by
  -- a short path from `p` to `z`
  have hS1 : ({x, y, q, t} : Finset V).card ≤ 5 * k := by
    have : ({x, y, q, t} : Finset V).card ≤ 4 := by
      refine (card_insert_le _ _).trans (Nat.succ_le_succ ((card_insert_le _ _).trans
        (Nat.succ_le_succ card_le_two)))
    omega
  have hpS1 : p ∉ ({x, y, q, t} : Finset V) := by
    simp only [mem_insert, mem_singleton, not_or]
    exact ⟨hxp.symm, hyp.symm, G.ne_of_adj hpq, G.ne_of_adj htp⟩
  have hzS1 : z ∉ ({x, y, q, t} : Finset V) := by
    simp only [mem_insert, mem_singleton, not_or]
    exact ⟨(G.ne_of_adj hxz).symm, hyz.symm, hzq, htz.symm⟩
  obtain ⟨mid₁, hlen₁, hpath₁, hmid₁⟩ := hshort _ hS1 p hp z hz hpS1 hzS1 hzp.symm
  have hmid₁' : ∀ v ∈ mid₁, v ∈ W ∧ v ≠ x ∧ v ≠ y ∧ v ≠ q ∧ v ≠ t := fun v hv => by
    have := hmid₁ v hv
    simp only [mem_insert, mem_singleton, not_or] at this
    exact ⟨this.1, this.2⟩
  -- the path `t q p mid₁ z x y`
  have hxmid : x ∉ mid₁ := fun h => (hmid₁' x h).2.1 rfl
  have hymid : y ∉ mid₁ := fun h => (hmid₁' y h).2.2.1 rfl
  have hQ1 : IsPathL G ([t, q] ++ (p :: mid₁ ++ [z]) ++ [x, y]) := by
    refine ((pathL_pair htq.symm).append hpath₁ ?_ ?_).append (pathL_pair hxy) ?_ ?_
    · intro v hv
      simp only [List.cons_append, List.mem_cons, List.mem_append, List.not_mem_nil,
        or_false] at hv
      rcases hv with rfl | hv | rfl
      · simp [G.ne_of_adj htp, G.ne_of_adj hpq]
      · have := hmid₁' v hv
        simp [this.2.2.2.1, this.2.2.2.2]
      · simp [htz.symm, hzq]
    · simpa using hpq.symm
    · intro v hv
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl
      · simp [htx.symm, hxq, hxp, hxmid, G.ne_of_adj hxz]
      · simp [hty.symm, hyq, hyp, hymid, hyz]
    · simpa [List.getLast?_cons, List.getLast?_append] using hxz.symm
  have hQ1W : ∀ v ∈ [t, q] ++ (p :: mid₁ ++ [z]) ++ [x, y], v ∈ W := by
    intro v hv
    simp at hv
    rcases hv with rfl | rfl | rfl | hv | rfl | rfl | rfl
    · exact htW
    · exact hqW
    · exact hp
    · exact (hmid₁' v hv).1
    · exact hz
    · exact hx
    · exact hy
  -- extend greedily from `y`
  set Q1 := [t, q] ++ (p :: mid₁ ++ [z]) ++ [x, y] with hQ1def
  have hQ1len : Q1.length = mid₁.length + 6 := by simp [hQ1def]
  have hT2 : Q1.toFinset.card + (2 * k - 6 - mid₁.length) ≤ D := by
    have := List.toFinset_card_le Q1
    rcases hlen₁ with h | h <;> omega
  obtain ⟨l₂, hl₂, hpath₂, hl₂T⟩ := greedy W D hD _ y Q1.toFinset hy hT2
  have hQ2 : IsPathL G (Q1 ++ l₂) :=
    hQ1.append_tail (by simp [hQ1def, List.getLast?_cons, List.getLast?_append]) hpath₂ (fun v hv hvQ => (hl₂T v hv).2 (List.mem_toFinset.2 hvQ))
  have hQ2W : ∀ v ∈ Q1 ++ l₂, v ∈ W := by
    intro v hv
    rcases List.mem_append.1 hv with h | h
    · exact hQ1W v h
    · exact (hl₂T v h).1
  have hQ2len : (Q1 ++ l₂).length = 2 * k := by
    rw [List.length_append, hQ1len, hl₂]; rcases hlen₁ with h | h <;> omega
  -- close up with a short path from the last vertex `u` back to `t`
  obtain ⟨u, hu, humem⟩ : ∃ u, (Q1 ++ l₂).getLast? = some u ∧ u ∈ Q1 ++ l₂ := by
    have hne : Q1 ++ l₂ ≠ [] := by simp [hQ1def]
    exact ⟨_, List.getLast?_eq_getLast hne, List.getLast_mem hne⟩
  have hQ2eq : Q1 ++ l₂ = t :: (q :: (p :: (mid₁ ++ z :: x :: y :: l₂))) := by simp [hQ1def]
  have hut : u ≠ t := by
    intro e
    subst e
    have hnd := hQ2.1
    rw [hQ2eq] at hnd hu
    rw [List.getLast?_cons_cons] at hu
    exact (List.nodup_cons.1 hnd).1 (List.mem_of_getLast? hu)
  have hS3 : (((Q1 ++ l₂).toFinset.erase u).erase t).card ≤ 5 * k := by
    have h1 := card_erase_le (s := (Q1 ++ l₂).toFinset.erase u) (a := t)
    have h2 := card_erase_le (s := (Q1 ++ l₂).toFinset) (a := u)
    have h3 := List.toFinset_card_le (Q1 ++ l₂)
    omega
  obtain ⟨mid₃, hlen₃, hpath₃, hmid₃⟩ := hshort _ hS3 u (hQ2W u humem) t htW
    (by simp) (by simp) hut
  have hmid₃Q : ∀ v ∈ mid₃, v ∉ Q1 ++ l₂ := fun v hv =>
    mem_of_shortPath_notMem rfl hpath₃ hmid₃ hv
  have hP : IsPathL G (Q1 ++ l₂ ++ mid₃) := hQ2.append_tail hu hpath₃.prefix_cons hmid₃Q
  obtain ⟨w₃, hw₃, hw₃t⟩ := shortPath_last_adj hpath₃
  have hlast : (Q1 ++ l₂ ++ mid₃).getLast? = some w₃ := getLast?_append_of_cons hu hw₃
  have hPeq : Q1 ++ l₂ ++ mid₃ = [] ++ t :: q :: p :: (mid₁ ++ z :: x :: y :: l₂ ++ mid₃) := by
    rw [hQ2eq]; simp
  have hne : s(z, x) ≠ s(x, y) := by
    intro h
    rcases Sym2.eq_iff.1 h with ⟨h1, _⟩ | ⟨h1, _⟩
    · exact G.ne_of_adj hxz h1.symm
    · exact hyz h1.symm
  rcases hlen₃ with h3 | h3
  · -- the cycle `t q p mid₁ z x y l₂ mid₃`
    refine cyc_apply hcyc hP ?_ ?_ ?_ ?_ hne
    · rw [List.length_append, hQ2len, h3]
    · intro a ha b hb
      rw [hlast] at hb
      rw [hPeq] at ha
      simp only [List.nil_append, List.head?_cons, Option.mem_def, Option.some.injEq] at ha hb
      subst ha; subst hb
      exact hw₃t
    · exact infix_of_eq (t :: q :: p :: mid₁) (y :: l₂ ++ mid₃ ++ [t]) (by rw [hPeq]; simp)
    · exact infix_of_eq (t :: q :: p :: mid₁ ++ [z]) (l₂ ++ mid₃ ++ [t]) (by rw [hPeq]; simp)
  · -- the cycle `t p mid₁ z x y l₂ mid₃`
    rw [hPeq] at hP
    have hP' := hP.skip htp.symm
    simp only [List.nil_append] at hP'
    refine cyc_apply hcyc hP' ?_ ?_ ?_ ?_ hne
    · have := hQ2len
      rw [hQ2eq] at this
      simp only [List.length_cons, List.length_append] at this ⊢
      omega
    · intro a ha b hb
      have hl' : (t :: p :: (mid₁ ++ z :: x :: y :: l₂ ++ mid₃)).getLast? = some w₃ := by
        rw [← hlast, hPeq]; simp [List.getLast?_cons, List.getLast?_append]
      rw [hl'] at hb
      simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at ha hb
      subst ha; subst hb
      exact hw₃t
    · exact infix_of_eq (t :: p :: mid₁) (y :: l₂ ++ mid₃ ++ [t]) (by simp)
    · exact infix_of_eq (t :: p :: mid₁ ++ [z]) (l₂ ++ mid₃ ++ [t]) (by simp)

end Case2Shared

section Case2Disj1

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Case 2, two disjoint good edges `xy`, `zw` (with `x, z ∈ N(p)`) such that `y` and `w` have a
common neighbour `u` outside `{p, q, x, z}` (Figure 3(b) of Bucić–Chen–Ma). -/
lemma case2_disj1 {R k : ℕ} (col : Sym2 V → Fin R) (hk : 4 ≤ k)
    (hcyc : CycRainbow G col (2 * k + 1)) (W : Finset V) (D : ℕ)
    (hD : ∀ u ∈ W, D ≤ dW G W u) (hD2 : 2 * k + 7 ≤ D)
    (hshort : ∀ S : Finset V, S.card ≤ 5 * k → ∀ x ∈ W, ∀ y ∈ W, x ∉ S → y ∉ S → x ≠ y →
      ShortPath G W S x y)
    (p q t : V) (hpq : G.Adj p q) (htp : G.Adj p t) (htq : G.Adj q t) (htW : t ∈ W)
    (x y z w u : V) (hx : x ∈ W) (hxy : G.Adj x y) (hzw : G.Adj z w) (hpx : G.Adj p x)
    (hpz : G.Adj p z) (hyu : G.Adj y u) (hwu : G.Adj w u)
    (hxz : x ≠ z) (hxw : x ≠ w) (hyz : y ≠ z) (hyw : y ≠ w)
    (hxq : x ≠ q) (hyp : y ≠ p) (hyq : y ≠ q) (hzq : z ≠ q) (hwp : w ≠ p) (hwq : w ≠ q)
    (hup : u ≠ p) (huq : u ≠ q) (hux : u ≠ x) (huz : u ≠ z)
    (htx : t ≠ x) (hty : t ≠ y) (htz : t ≠ z) (htw : t ≠ w) (htu : t ≠ u) :
    col s(x, y) ≠ col s(z, w) := by
  have hxp : x ≠ p := (G.ne_of_adj hpx).symm
  have hzp : z ≠ p := (G.ne_of_adj hpz).symm
  have htp' : t ≠ p := (G.ne_of_adj htp).symm
  have htq' : t ≠ q := (G.ne_of_adj htq).symm
  have hpq' : p ≠ q := G.ne_of_adj hpq
  have hxy' : x ≠ y := G.ne_of_adj hxy
  have hzw' : z ≠ w := G.ne_of_adj hzw
  have huy : u ≠ y := (G.ne_of_adj hyu).symm
  have huw : u ≠ w := (G.ne_of_adj hwu).symm
  -- a greedy path from `x`
  have hT1 : ({y, u, w, z, p, q, t} : Finset V).card + (2 * k - 8) ≤ D := by
    have : ({y, u, w, z, p, q, t} : Finset V).card ≤ 7 := by
      refine (card_insert_le _ _).trans (Nat.succ_le_succ ?_)
      refine (card_insert_le _ _).trans (Nat.succ_le_succ ?_)
      refine (card_insert_le _ _).trans (Nat.succ_le_succ ?_)
      refine (card_insert_le _ _).trans (Nat.succ_le_succ ?_)
      refine (card_insert_le _ _).trans (Nat.succ_le_succ ?_)
      exact card_le_two
    omega
  obtain ⟨l₁, hl₁, hpath₁, hl₁T⟩ := greedy W D hD (2 * k - 8) x _ hx hT1
  have hl₁' : ∀ v ∈ l₁, v ∈ W ∧ v ≠ y ∧ v ≠ u ∧ v ≠ w ∧ v ≠ z ∧ v ≠ p ∧ v ≠ q ∧ v ≠ t :=
    fun v hv => by
      have := hl₁T v hv
      simp only [mem_insert, mem_singleton, not_or] at this
      exact ⟨this.1, this.2⟩
  obtain ⟨v, hv, hvmem⟩ := exists_getLast x l₁
  have hPW : ∀ a ∈ x :: l₁, a ∈ W := fun a ha => by
    rcases List.mem_cons.1 ha with rfl | ha
    · exact hx
    · exact (hl₁' a ha).1
  have hPavoid : ∀ a ∈ x :: l₁, a ≠ y ∧ a ≠ u ∧ a ≠ w ∧ a ≠ z ∧ a ≠ p ∧ a ≠ q ∧ a ≠ t :=
    fun a ha => by
      rcases List.mem_cons.1 ha with rfl | ha
      · exact ⟨hxy', hux.symm, hxw, hxz, hxp, hxq, htx.symm⟩
      · exact (hl₁' a ha).2
  -- a short path from `v` to `t`
  set S := ((x :: l₁).toFinset.erase v) ∪ {y, u, w, z, p, q} with hSdef
  have hScard : S.card ≤ 5 * k := by
    have h1 := card_union_le ((x :: l₁).toFinset.erase v) ({y, u, w, z, p, q} : Finset V)
    have h2 : ({y, u, w, z, p, q} : Finset V).card ≤ 6 := by
      refine (card_insert_le _ _).trans (Nat.succ_le_succ ?_)
      refine (card_insert_le _ _).trans (Nat.succ_le_succ ?_)
      refine (card_insert_le _ _).trans (Nat.succ_le_succ ?_)
      refine (card_insert_le _ _).trans (Nat.succ_le_succ ?_)
      exact card_le_two
    have h3 := card_erase_le (s := (x :: l₁).toFinset) (a := v)
    have h4 := List.toFinset_card_le (x :: l₁)
    simp only [List.length_cons, hl₁] at h4
    rw [hSdef]
    omega
  have hvS : v ∉ S := by
    rw [hSdef, mem_union, not_or]
    refine ⟨fun h => (mem_erase.1 h).1 rfl, ?_⟩
    have := hPavoid v hvmem
    simp only [mem_insert, mem_singleton, not_or]
    exact ⟨this.1, this.2.1, this.2.2.1, this.2.2.2.1, this.2.2.2.2.1, this.2.2.2.2.2.1⟩
  have htP : t ∉ x :: l₁ := fun h => (hPavoid t h).2.2.2.2.2.2 rfl
  have htS : t ∉ S := by
    rw [hSdef, mem_union, not_or]
    refine ⟨fun h => htP (List.mem_toFinset.1 (mem_erase.1 h).2), ?_⟩
    simp only [mem_insert, mem_singleton, not_or]
    exact ⟨hty, htu, htw, htz, htp', htq'⟩
  have hvt : v ≠ t := fun e => htP (e ▸ hvmem)
  obtain ⟨mid, hlen, hpath, hmid⟩ := hshort S hScard v (hPW v hvmem) t htW hvS htS hvt
  have hmid' : ∀ a ∈ mid, a ∉ x :: l₁ ∧ a ≠ y ∧ a ≠ u ∧ a ≠ w ∧ a ≠ z ∧ a ≠ p ∧ a ≠ q ∧ a ≠ t := by
    intro a ha
    have hnd := hpath.1
    simp only [List.cons_append, List.nodup_cons, List.mem_append, List.mem_singleton, not_or,
      List.nodup_append] at hnd
    have hav : a ≠ v := fun e => hnd.1.1 (e ▸ ha)
    have hat : a ≠ t := fun e => hnd.2.2.2 a ha t (by simp) e
    have haS := (hmid a ha).2
    rw [hSdef, mem_union, not_or] at haS
    have h2 := haS.2
    simp only [mem_insert, mem_singleton, not_or] at h2
    refine ⟨fun h => haS.1 (mem_erase.2 ⟨hav, List.mem_toFinset.2 h⟩), h2.1, h2.2.1, h2.2.2.1,
      h2.2.2.2.1, h2.2.2.2.2.1, h2.2.2.2.2.2, hat⟩
  have hP1 : IsPathL G ((x :: l₁) ++ mid) :=
    hpath₁.append_tail hv hpath.prefix_cons (fun a ha => (hmid' a ha).1)
  obtain ⟨w₃, hw₃, hw₃t⟩ := shortPath_last_adj hpath
  have hlast1 : ((x :: l₁) ++ mid).getLast? = some w₃ := getLast?_append_of_cons hv hw₃
  -- the fixed block `t q p z w u y`
  have hB : IsPathL G [t, q, p, z, w, u, y] := by
    refine ⟨?_, ?_⟩
    · simp [htq', htp', htz, htw, htu, hty, hpq'.symm, hzq.symm, hwq.symm, huq.symm, hyq.symm,
        hzp.symm, hwp.symm, hup.symm, hyp.symm, hzw', huz.symm, hyz.symm, huw.symm, hyw.symm,
        huy]
    · simp [htq.symm, hpq.symm, hpz, hzw, hwu, hyu.symm]
  have hP2 : IsPathL G ((x :: l₁) ++ mid ++ [t, q, p, z, w, u, y]) := by
    refine hP1.append hB ?_ ?_
    · intro b hb
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      intro hb'
      rw [List.mem_append] at hb'
      rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · rcases hb' with h | h
        · exact htP h
        · exact (hmid' b h).2.2.2.2.2.2.2 rfl
      · rcases hb' with h | h
        · exact (hPavoid b h).2.2.2.2.2.1 rfl
        · exact (hmid' b h).2.2.2.2.2.2.1 rfl
      · rcases hb' with h | h
        · exact (hPavoid b h).2.2.2.2.1 rfl
        · exact (hmid' b h).2.2.2.2.2.1 rfl
      · rcases hb' with h | h
        · exact (hPavoid b h).2.2.2.1 rfl
        · exact (hmid' b h).2.2.2.2.1 rfl
      · rcases hb' with h | h
        · exact (hPavoid b h).2.2.1 rfl
        · exact (hmid' b h).2.2.2.1 rfl
      · rcases hb' with h | h
        · exact (hPavoid b h).2.1 rfl
        · exact (hmid' b h).2.2.1 rfl
      · rcases hb' with h | h
        · exact (hPavoid b h).1 rfl
        · exact (hmid' b h).2.1 rfl
    · intro a ha b hb
      rw [hlast1] at ha
      simp only [Option.mem_def, Option.some.injEq, List.head?_cons] at ha hb
      subst ha; subst hb
      exact hw₃t
  have hne : s(y, x) ≠ s(z, w) := by
    intro h
    rcases Sym2.eq_iff.1 h with ⟨h1, _⟩ | ⟨h1, _⟩
    · exact hyz h1
    · exact hyw h1
  have hswap : s(y, x) = s(x, y) := Sym2.eq_swap
  rw [← hswap]
  have hlenP : ((x :: l₁) ++ mid).length = 2 * k - 7 + mid.length := by
    simp [hl₁]; omega
  rcases hlen with h1 | h1
  · refine cyc_apply hcyc hP2 ?_ ?_ ?_ ?_ hne
    · rw [List.length_append, hlenP, h1]; simp; omega
    · intro a ha b hb
      simp only [List.cons_append, List.head?_cons, Option.mem_def, Option.some.injEq] at ha
      simp [List.getLast?_cons, List.getLast?_append] at hb
      subst ha; subst hb
      exact hxy.symm
    · exact infix_of_eq (x :: l₁ ++ mid ++ [t, q, p, z, w, u]) [] (by simp)
    · exact infix_of_eq (x :: l₁ ++ mid ++ [t, q, p]) [u, y, x] (by simp)
  · have hP3 := (show IsPathL G (((x :: l₁) ++ mid) ++ t :: q :: p :: [z, w, u, y]) by
      simpa using hP2).skip htp.symm
    refine cyc_apply hcyc hP3 ?_ ?_ ?_ ?_ hne
    · rw [List.length_append, hlenP, h1]; simp; omega
    · intro a ha b hb
      simp only [List.cons_append, List.head?_cons, Option.mem_def, Option.some.injEq] at ha
      simp [List.getLast?_cons, List.getLast?_append] at hb
      subst ha; subst hb
      exact hxy.symm
    · exact infix_of_eq (x :: l₁ ++ mid ++ [t, p, z, w, u]) [] (by simp)
    · exact infix_of_eq (x :: l₁ ++ mid ++ [t, p]) [u, y, x] (by simp)

end Case2Disj1

section Case2Disj2

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Case 2, two disjoint good edges `xy`, `zw` (with `x, z ∈ N(p)`) and a common neighbour `t`
of `p, q` adjacent to `y` (Figure 3(c) of Bucić–Chen–Ma). -/
lemma case2_disj2 {R k : ℕ} (col : Sym2 V → Fin R) (hk : 4 ≤ k)
    (hcyc : CycRainbow G col (2 * k + 1)) (W : Finset V) (D : ℕ)
    (hD : ∀ u ∈ W, D ≤ dW G W u) (hD2 : 2 * k + 7 ≤ D)
    (hshort : ∀ S : Finset V, S.card ≤ 5 * k → ∀ x ∈ W, ∀ y ∈ W, x ∉ S → y ∉ S → x ≠ y →
      ShortPath G W S x y)
    (p q t : V) (hpq : G.Adj p q) (htp : G.Adj p t) (htq : G.Adj q t)
    (x y z w : V) (hx : x ∈ W) (hw : w ∈ W) (hxy : G.Adj x y) (hzw : G.Adj z w)
    (hpx : G.Adj p x) (hpz : G.Adj p z) (hty : G.Adj t y)
    (hxz : x ≠ z) (hxw : x ≠ w) (hyz : y ≠ z) (hyw : y ≠ w)
    (hxq : x ≠ q) (hyp : y ≠ p) (hyq : y ≠ q) (hzq : z ≠ q) (hwp : w ≠ p) (hwq : w ≠ q)
    (htx : t ≠ x) (htz : t ≠ z) (htw : t ≠ w) :
    col s(x, y) ≠ col s(z, w) := by
  have hxp : x ≠ p := (G.ne_of_adj hpx).symm
  have hzp : z ≠ p := (G.ne_of_adj hpz).symm
  have htp' : t ≠ p := (G.ne_of_adj htp).symm
  have htq' : t ≠ q := (G.ne_of_adj htq).symm
  have hpq' : p ≠ q := G.ne_of_adj hpq
  have hxy' : x ≠ y := G.ne_of_adj hxy
  have hzw' : z ≠ w := G.ne_of_adj hzw
  have hty' : t ≠ y := G.ne_of_adj hty
  -- a greedy path from `x`
  have hT1 : ({y, w, z, p, q, t} : Finset V).card + (2 * k - 7) ≤ D := by
    have : ({y, w, z, p, q, t} : Finset V).card ≤ 6 := by
      refine (card_insert_le _ _).trans (Nat.succ_le_succ ?_)
      refine (card_insert_le _ _).trans (Nat.succ_le_succ ?_)
      refine (card_insert_le _ _).trans (Nat.succ_le_succ ?_)
      refine (card_insert_le _ _).trans (Nat.succ_le_succ ?_)
      exact card_le_two
    omega
  obtain ⟨l₁, hl₁, hpath₁, hl₁T⟩ := greedy W D hD (2 * k - 7) x _ hx hT1
  have hl₁' : ∀ v ∈ l₁, v ∈ W ∧ v ≠ y ∧ v ≠ w ∧ v ≠ z ∧ v ≠ p ∧ v ≠ q ∧ v ≠ t :=
    fun v hv => by
      have := hl₁T v hv
      simp only [mem_insert, mem_singleton, not_or] at this
      exact ⟨this.1, this.2⟩
  obtain ⟨v, hv, hvmem⟩ := exists_getLast x l₁
  have hPW : ∀ a ∈ x :: l₁, a ∈ W := fun a ha => by
    rcases List.mem_cons.1 ha with rfl | ha
    · exact hx
    · exact (hl₁' a ha).1
  have hPavoid : ∀ a ∈ x :: l₁, a ≠ y ∧ a ≠ w ∧ a ≠ z ∧ a ≠ p ∧ a ≠ q ∧ a ≠ t :=
    fun a ha => by
      rcases List.mem_cons.1 ha with rfl | ha
      · exact ⟨hxy', hxw, hxz, hxp, hxq, htx.symm⟩
      · exact (hl₁' a ha).2
  -- a short path from `v` to `w`
  set S := ((x :: l₁).toFinset.erase v) ∪ {z, p, q, t, y} with hSdef
  have hScard : S.card ≤ 5 * k := by
    have h1 := card_union_le ((x :: l₁).toFinset.erase v) ({z, p, q, t, y} : Finset V)
    have h2 : ({z, p, q, t, y} : Finset V).card ≤ 5 := by
      refine (card_insert_le _ _).trans (Nat.succ_le_succ ?_)
      refine (card_insert_le _ _).trans (Nat.succ_le_succ ?_)
      refine (card_insert_le _ _).trans (Nat.succ_le_succ ?_)
      exact card_le_two
    have h3 := card_erase_le (s := (x :: l₁).toFinset) (a := v)
    have h4 := List.toFinset_card_le (x :: l₁)
    simp only [List.length_cons, hl₁] at h4
    rw [hSdef]
    omega
  have hvS : v ∉ S := by
    rw [hSdef, mem_union, not_or]
    refine ⟨fun h => (mem_erase.1 h).1 rfl, ?_⟩
    have := hPavoid v hvmem
    simp only [mem_insert, mem_singleton, not_or]
    exact ⟨this.2.2.1, this.2.2.2.1, this.2.2.2.2.1, this.2.2.2.2.2, this.1⟩
  have hwP : w ∉ x :: l₁ := fun h => (hPavoid w h).2.1 rfl
  have hwS : w ∉ S := by
    rw [hSdef, mem_union, not_or]
    refine ⟨fun h => hwP (List.mem_toFinset.1 (mem_erase.1 h).2), ?_⟩
    simp only [mem_insert, mem_singleton, not_or]
    exact ⟨hzw'.symm, hwp, hwq, htw.symm, hyw.symm⟩
  have hvw : v ≠ w := fun e => hwP (e ▸ hvmem)
  obtain ⟨mid, hlen, hpath, hmid⟩ := hshort S hScard v (hPW v hvmem) w hw hvS hwS hvw
  have hmid' : ∀ a ∈ mid, a ∉ x :: l₁ ∧ a ≠ z ∧ a ≠ p ∧ a ≠ q ∧ a ≠ t ∧ a ≠ y ∧ a ≠ w := by
    intro a ha
    have hnd := hpath.1
    simp only [List.cons_append, List.nodup_cons, List.mem_append, List.mem_singleton, not_or,
      List.nodup_append] at hnd
    have hav : a ≠ v := fun e => hnd.1.1 (e ▸ ha)
    have haw : a ≠ w := fun e => hnd.2.2.2 a ha w (by simp) e
    have haS := (hmid a ha).2
    rw [hSdef, mem_union, not_or] at haS
    have h2 := haS.2
    simp only [mem_insert, mem_singleton, not_or] at h2
    exact ⟨fun h => haS.1 (mem_erase.2 ⟨hav, List.mem_toFinset.2 h⟩), h2.1, h2.2.1, h2.2.2.1,
      h2.2.2.2.1, h2.2.2.2.2, haw⟩
  -- the fixed block `z p q t y`, then `x l₁ mid w`
  have hB : IsPathL G [z, p, q, t, y] := by
    refine ⟨?_, ?_⟩
    · simp [hzp, hzq, htz.symm, hyz.symm, hpq', htp'.symm, hyp.symm, htq'.symm, hyq.symm, hty']
    · simp [hpz.symm, hpq, htq, hty]
  have hP1 : IsPathL G ([z, p, q, t, y] ++ (x :: l₁)) := by
    refine hB.append hpath₁ ?_ (by simpa using hxy.symm)
    intro a ha hab
    have := hPavoid a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hab
    rcases hab with rfl | rfl | rfl | rfl | rfl
    · exact this.2.2.1 rfl
    · exact this.2.2.2.1 rfl
    · exact this.2.2.2.2.1 rfl
    · exact this.2.2.2.2.2 rfl
    · exact this.1 rfl
  have hlast1 : ([z, p, q, t, y] ++ (x :: l₁)).getLast? = some v := by
    rw [List.getLast?_append_of_ne_nil _ (List.cons_ne_nil _ _)]; exact hv
  have hP2 : IsPathL G ([z, p, q, t, y] ++ (x :: l₁) ++ mid) := by
    refine hP1.append_tail hlast1 hpath.prefix_cons ?_
    intro a ha hab
    have := hmid' a ha
    rw [List.mem_append] at hab
    rcases hab with hab | hab
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hab
      rcases hab with rfl | rfl | rfl | rfl | rfl
      · exact this.2.1 rfl
      · exact this.2.2.1 rfl
      · exact this.2.2.2.1 rfl
      · exact this.2.2.2.2.1 rfl
      · exact this.2.2.2.2.2.1 rfl
    · exact this.1 hab
  obtain ⟨w₃, hw₃, hw₃w⟩ := shortPath_last_adj hpath
  have hlast2 : ([z, p, q, t, y] ++ (x :: l₁) ++ mid).getLast? = some w₃ :=
    getLast?_append_of_cons hlast1 hw₃
  have hP3 : IsPathL G ([z, p, q, t, y] ++ (x :: l₁) ++ mid ++ [w]) := by
    refine hP2.append (pathL_single w) ?_ ?_
    · intro a ha hab
      simp only [List.mem_singleton] at ha
      subst ha
      rw [List.mem_append, List.mem_append] at hab
      rcases hab with (hab | hab) | hab
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hab
        rcases hab with h | h | h | h | h
        · exact hzw' h.symm
        · exact hwp h
        · exact hwq h
        · exact htw h.symm
        · exact hyw h.symm
      · exact hwP hab
      · exact (hmid' a hab).2.2.2.2.2.2 rfl
    · intro a ha b hb
      rw [hlast2] at ha
      simp only [Option.mem_def, Option.some.injEq, List.head?_cons] at ha hb
      subst ha; subst hb
      exact hw₃w
  have hne : s(y, x) ≠ s(w, z) := by
    intro h
    rcases Sym2.eq_iff.1 h with ⟨h1, _⟩ | ⟨h1, _⟩
    · exact hyw h1
    · exact hyz h1
  have hswap1 : s(y, x) = s(x, y) := Sym2.eq_swap
  have hswap2 : s(w, z) = s(z, w) := Sym2.eq_swap
  rw [← hswap1, ← hswap2]
  have hlenP : ([z, p, q, t, y] ++ (x :: l₁) ++ mid).length = 2 * k - 1 + mid.length := by
    simp [hl₁]; omega
  rcases hlen with h1 | h1
  · refine cyc_apply hcyc hP3 ?_ ?_ ?_ ?_ hne
    · rw [List.length_append, hlenP, h1]; simp; omega
    · intro a ha b hb
      simp only [List.cons_append, List.head?_cons, Option.mem_def, Option.some.injEq] at ha
      simp [List.getLast?_cons, List.getLast?_append] at hb
      subst ha; subst hb
      exact hzw.symm
    · exact infix_of_eq [z, p, q, t] (l₁ ++ mid ++ [w] ++ [z]) (by simp)
    · exact infix_of_eq ([z, p, q, t, y] ++ (x :: l₁) ++ mid) [] (by simp)
  · have hP4 := (show IsPathL G ([z] ++ p :: q :: t :: ([y] ++ (x :: l₁) ++ mid ++ [w])) by
      simpa using hP3).skip htp
    refine cyc_apply hcyc hP4 ?_ ?_ ?_ ?_ hne
    · have := hlenP
      simp only [List.length_append, List.length_cons, List.length_nil] at this ⊢
      omega
    · intro a ha b hb
      simp only [List.singleton_append, List.head?_cons, Option.mem_def, Option.some.injEq] at ha
      simp [List.getLast?_cons, List.getLast?_append] at hb
      subst ha; subst hb
      exact hzw.symm
    · exact infix_of_eq [z, p, t] (l₁ ++ mid ++ [w] ++ [z]) (by simp)
    · exact infix_of_eq ([z, p, t, y] ++ (x :: l₁) ++ mid) [] (by simp)

end Case2Disj2

section Case2Count

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

lemma exists_avoid5 (C : Finset V) (hC : 6 ≤ C.card) (a b c d e : V) :
    ∃ t ∈ C, t ≠ a ∧ t ≠ b ∧ t ≠ c ∧ t ≠ d ∧ t ≠ e := by
  have h : ({a, b, c, d, e} : Finset V).card < C.card := by
    have : ({a, b, c, d, e} : Finset V).card ≤ 5 := by
      refine (card_insert_le _ _).trans (Nat.succ_le_succ ?_)
      refine (card_insert_le _ _).trans (Nat.succ_le_succ ?_)
      refine (card_insert_le _ _).trans (Nat.succ_le_succ ?_)
      exact card_le_two
    omega
  obtain ⟨t, ht, htF⟩ := exists_mem_notMem_of_card_lt_card h
  simp only [mem_insert, mem_singleton, not_or] at htF
  exact ⟨t, ht, htF⟩

/-- Any two good edges (an endpoint in `N(p) \ {q}`, no endpoint in `{p, q}`) get distinct
colours. -/
lemma case2_good_pair {R k : ℕ} (col : Sym2 V → Fin R) (hk : 4 ≤ k)
    (hcyc : CycRainbow G col (2 * k + 1)) (W : Finset V) (D : ℕ)
    (hD : ∀ u ∈ W, D ≤ dW G W u) (hD2 : 2 * k + 7 ≤ D)
    (hshort : ∀ S : Finset V, S.card ≤ 5 * k → ∀ x ∈ W, ∀ y ∈ W, x ∉ S → y ∉ S → x ≠ y →
      ShortPath G W S x y)
    (p q : V) (hp : p ∈ W) (hq : q ∈ W) (hpq : G.Adj p q)
    (hC6 : 6 ≤ (nbW G W p ∩ nbW G W q).card)
    (hC : W.card + 8 < (nbW G W p ∩ nbW G W q).card + 2 * D)
    (x y z w : V) (hx : x ∈ W) (hy : y ∈ W) (hz : z ∈ W) (hw : w ∈ W)
    (hpx : G.Adj p x) (hpz : G.Adj p z) (hxy : G.Adj x y) (hzw : G.Adj z w)
    (hxq : x ≠ q) (hzq : z ≠ q) (hyp : y ≠ p) (hyq : y ≠ q) (hwp : w ≠ p) (hwq : w ≠ q)
    (hne : s(x, y) ≠ s(z, w)) : col s(x, y) ≠ col s(z, w) := by
  have hxp : x ≠ p := (G.ne_of_adj hpx).symm
  have hzp : z ≠ p := (G.ne_of_adj hpz).symm
  have hCmem : ∀ t ∈ nbW G W p ∩ nbW G W q, t ∈ W ∧ G.Adj p t ∧ G.Adj q t := by
    intro t ht
    rw [mem_inter, mem_nbW, mem_nbW] at ht
    exact ⟨ht.1.1, ht.1.2, ht.2.2⟩
  by_cases h1 : x = z
  · subst h1
    have hyw : y ≠ w := fun e => hne (by rw [e])
    obtain ⟨t, ht, htx, hty, htw, -, -⟩ := exists_avoid5 _ hC6 x y w x x
    obtain ⟨htW, htp, htq⟩ := hCmem t ht
    have := case2_shared col hk hcyc W D hD hD2 hshort p q t hp hpq htp htq x y w hx hy hw
      hxy hzw hyw hxp hxq hyp hyq hwp hwq htx hty htw hq htW
    intro hc
    apply this
    rw [Sym2.eq_swap, ← hc]
  by_cases h2 : x = w
  · subst h2
    have hyz : y ≠ z := fun e => hne (by rw [e, Sym2.eq_swap])
    obtain ⟨t, ht, htx, hty, htz, -, -⟩ := exists_avoid5 _ hC6 x y z x x
    obtain ⟨htW, htp, htq⟩ := hCmem t ht
    have := case2_shared col hk hcyc W D hD hD2 hshort p q t hp hpq htp htq x y z hx hy hz
      hxy hzw.symm hyz hxp hxq hyp hyq hzp hzq htx hty htz hq htW
    exact fun hc => this hc.symm
  by_cases h3 : y = z
  · subst h3
    have hwx : w ≠ x := fun e => h2 e.symm
    obtain ⟨t, ht, hty, htw, htx, -, -⟩ := exists_avoid5 _ hC6 y w x y y
    obtain ⟨htW, htp, htq⟩ := hCmem t ht
    exact case2_shared col hk hcyc W D hD hD2 hshort p q t hp hpq htp htq y w x hy hw hx
      hzw hxy.symm hwx hyp hyq hwp hwq hxp hxq hty htw htx hq htW
  by_cases h4 : y = w
  · subst h4
    obtain ⟨t, ht, hty, htz, htx, -, -⟩ := exists_avoid5 _ hC6 y z x y y
    obtain ⟨htW, htp, htq⟩ := hCmem t ht
    have := case2_shared col hk hcyc W D hD hD2 hshort p q t hp hpq htp htq y z x hy hz hx
      hzw.symm hxy.symm (fun e => h1 e.symm) hyp hyq hzp hzq hxp hxq hty htz htx hq htW
    intro hc
    apply this
    rw [Sym2.eq_swap (a := y) (b := z), ← hc]
  -- the two edges are disjoint
  by_cases hu : ∃ u ∈ W, u ≠ p ∧ u ≠ q ∧ u ≠ x ∧ u ≠ z ∧ G.Adj y u ∧ G.Adj w u
  · obtain ⟨u, huW, hup, huq, hux, huz, hyu, hwu⟩ := hu
    obtain ⟨t, ht, htx, hty, htz, htw, htu⟩ := exists_avoid5 _ hC6 x y z w u
    obtain ⟨htW, htp, htq⟩ := hCmem t ht
    exact case2_disj1 col hk hcyc W D hD hD2 hshort p q t hpq htp htq htW x y z w u hx hxy hzw
      hpx hpz hyu hwu h1 h2 h3 h4 hxq hyp hyq hzq hwp hwq hup huq hux huz htx hty htz htw htu
  push Not at hu
  -- a common neighbour `t` of `p, q` adjacent to `y` or `w`
  have hinter : (nbW G W y ∩ nbW G W w).card ≤ 4 := by
    have hsub : nbW G W y ∩ nbW G W w ⊆ {p, q, x, z} := by
      intro u hu'
      rw [mem_inter, mem_nbW, mem_nbW] at hu'
      simp only [mem_insert, mem_singleton]
      by_contra hc
      push Not at hc
      exact hu u hu'.1.1 hc.1 hc.2.1 hc.2.2.1 hc.2.2.2 hu'.1.2 hu'.2.2
    refine (card_le_card hsub).trans ?_
    refine (card_insert_le _ _).trans (Nat.succ_le_succ ?_)
    refine (card_insert_le _ _).trans (Nat.succ_le_succ ?_)
    exact card_le_two
  have hexists : ∃ t ∈ nbW G W p ∩ nbW G W q, t ≠ x ∧ t ≠ z ∧ t ≠ w ∧ t ≠ y ∧
      (G.Adj t y ∨ G.Adj t w) := by
    have hC'card : (nbW G W p ∩ nbW G W q).card ≤
        ((nbW G W p ∩ nbW G W q) \ {x, y, z, w}).card + 4 := by
      have := le_card_sdiff ({x, y, z, w} : Finset V) (nbW G W p ∩ nbW G W q)
      have h4 : ({x, y, z, w} : Finset V).card ≤ 4 := by
        refine (card_insert_le _ _).trans (Nat.succ_le_succ ?_)
        refine (card_insert_le _ _).trans (Nat.succ_le_succ ?_)
        exact card_le_two
      omega
    have hneg : (((nbW G W p ∩ nbW G W q) \ {x, y, z, w}).filter
        (fun t => ¬ (G.Adj t y ∨ G.Adj t w))).card + (2 * D) ≤ W.card + 4 := by
      have hsub : ((nbW G W p ∩ nbW G W q) \ {x, y, z, w}).filter
          (fun t => ¬ (G.Adj t y ∨ G.Adj t w)) ⊆ W \ (nbW G W y ∪ nbW G W w) := by
        intro t ht
        rw [mem_filter, mem_sdiff, mem_inter, mem_nbW] at ht
        rw [mem_sdiff, mem_union, mem_nbW, mem_nbW]
        push Not at ht
        exact ⟨ht.1.1.1.1, fun h => h.elim (fun h => ht.2.1 h.2.symm) (fun h => ht.2.2 h.2.symm)⟩
      have h1 := card_le_card hsub
      have h2 := card_sdiff_add_card_eq_card (union_subset (nbW_subset (G := G) W y)
        (nbW_subset (G := G) W w))
      have h3 := card_union_add_card_inter (nbW G W y) (nbW G W w)
      have h4 := hD y hy
      have h5 := hD w hw
      unfold dW at h4 h5
      omega
    have hpos := card_filter_add_card_filter_not (s := (nbW G W p ∩ nbW G W q) \ {x, y, z, w})
      (fun t => G.Adj t y ∨ G.Adj t w)
    obtain ⟨t, ht⟩ := card_pos.1 (by omega : 0 < (((nbW G W p ∩ nbW G W q) \ {x, y, z, w}).filter
      (fun t => G.Adj t y ∨ G.Adj t w)).card)
    rw [mem_filter, mem_sdiff] at ht
    simp only [mem_insert, mem_singleton, not_or] at ht
    exact ⟨t, ht.1.1, ht.1.2.1, ht.1.2.2.2.1, ht.1.2.2.2.2, ht.1.2.2.1, ht.2⟩
  obtain ⟨t, ht, htx, htz, htw, hty, hadj⟩ := hexists
  obtain ⟨htW, htp, htq⟩ := hCmem t ht
  rcases hadj with hadj | hadj
  · exact case2_disj2 col hk hcyc W D hD hD2 hshort p q t hpq htp htq x y z w hx hw hxy hzw hpx hpz
      hadj h1 h2 h3 h4 hxq hyp hyq hzq hwp hwq htx htz htw
  · have := case2_disj2 col hk hcyc W D hD hD2 hshort p q t hpq htp htq z w x y hz hy hzw hxy hpz
      hpx hadj (fun e => h1 e.symm) (fun e => h3 e.symm) (fun e => h2 e.symm)
      (fun e => h4 e.symm) hzq hwp hwq hxq hyp hyq htz htx hty
    exact fun hc => this hc.symm

end Case2Count

section Case2Count2

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- The good-edge count in Case 2. -/
lemma case2_count {R k : ℕ} (col : Sym2 V → Fin R) (hk : 4 ≤ k)
    (hcyc : CycRainbow G col (2 * k + 1)) (W : Finset V) (D : ℕ)
    (hD : ∀ u ∈ W, D ≤ dW G W u) (hD2 : 2 * k + 7 ≤ D)
    (hshort : ∀ S : Finset V, S.card ≤ 5 * k → ∀ x ∈ W, ∀ y ∈ W, x ∉ S → y ∉ S → x ≠ y →
      ShortPath G W S x y)
    (p q : V) (hp : p ∈ W) (hq : q ∈ W) (hpq : G.Adj p q)
    (hC6 : 6 ≤ (nbW G W p ∩ nbW G W q).card)
    (hC : W.card + 8 < (nbW G W p ∩ nbW G W q).card + 2 * D) :
    (D - 1) * (D - 2) ≤ 2 * R := by
  set A := (nbW G W p).erase q with hA
  set T := (W ×ˢ W).filter (fun e => e.1 ∈ A ∧ G.Adj e.1 e.2 ∧ e.2 ≠ p ∧ e.2 ≠ q) with hT
  have hcount : T.card ≤ 2 * R := by
    apply count_rainbow col T
    intro e₁ he₁ e₂ he₂ hne
    rw [hT, mem_filter, mem_product] at he₁ he₂
    obtain ⟨⟨hx, hy⟩, hxA, hxy, hyp, hyq⟩ := he₁
    obtain ⟨⟨hz, hw⟩, hzA, hzw, hwp, hwq⟩ := he₂
    rw [hA, mem_erase, mem_nbW] at hxA hzA
    exact case2_good_pair col hk hcyc W D hD hD2 hshort p q hp hq hpq hC6 hC _ _ _ _ hx hy hz hw
      hxA.2.2 hzA.2.2 hxy hzw hxA.1 hzA.1 hyp hyq hwp hwq hne
  have hsigma : (A.sigma (fun u => ((nbW G W u).erase p).erase q)).card ≤ T.card := by
    apply card_le_card_of_injOn (fun e => (e.1, e.2))
    · intro e he
      rw [mem_coe, mem_sigma] at he
      rw [mem_coe, hT, mem_filter, mem_product]
      obtain ⟨h1, h2⟩ := he
      rw [mem_erase, mem_erase, mem_nbW] at h2
      have h1' := h1
      rw [hA, mem_erase, mem_nbW] at h1'
      exact ⟨⟨h1'.2.1, h2.2.2.1⟩, h1, h2.2.2.2, h2.2.1, h2.1⟩
    · intro e₁ _ e₂ _ h
      simp only [Prod.mk.injEq] at h
      exact Sigma.ext h.1 (heq_of_eq h.2)
  rw [card_sigma] at hsigma
  have hfib : ∀ u ∈ A, D - 2 ≤ (((nbW G W u).erase p).erase q).card := by
    intro u hu
    have huW : u ∈ W := by rw [hA, mem_erase, mem_nbW] at hu; exact hu.2.1
    have h1 := hD u huW
    have h2 := pred_card_le_card_erase (s := nbW G W u) (a := p)
    have h3 := pred_card_le_card_erase (s := (nbW G W u).erase p) (a := q)
    unfold dW at h1
    omega
  have hsum : A.card * (D - 2) ≤ ∑ u ∈ A, (((nbW G W u).erase p).erase q).card := by
    have := sum_le_sum hfib
    rwa [sum_const, smul_eq_mul] at this
  have hAcard : D - 1 ≤ A.card := by
    have hqN : q ∈ nbW G W p := mem_nbW.2 ⟨hq, hpq⟩
    rw [hA, card_erase_of_mem hqN]
    have := hD p hp
    unfold dW at this
    omega
  calc (D - 1) * (D - 2) ≤ A.card * (D - 2) := Nat.mul_le_mul_right _ hAcard
    _ ≤ T.card := hsum.trans hsigma
    _ ≤ 2 * R := hcount

end Case2Count2

section Trim

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

lemma trim_front {P : List V} {h h' l : V} (hP : IsPathL G P) (hh : P.head? = some h)
    (hl : P.getLast? = some l) (hh' : h' ≠ l) (hne : h' ≠ h) :
    ∃ P', IsPathL G P' ∧ P'.getLast? = some l ∧ (∀ v ∈ P', v ∈ P) ∧ P'.length ≤ P.length ∧
      ((P'.head? = some h ∧ h' ∉ P') ∨ (P'.head? = some h' ∧ h ∉ P')) := by
  by_cases hmem : h' ∈ P
  · obtain ⟨s, t, rfl⟩ := List.mem_iff_append.1 hmem
    have hs : s ≠ [] := by
      rintro rfl
      simp at hh
      exact hne hh
    have ht : t ≠ [] := by
      rintro rfl
      rw [List.getLast?_append_of_ne_nil _ (List.cons_ne_nil _ _)] at hl
      simp at hl
      exact hh' hl
    refine ⟨h' :: t, hP.sublist (List.suffix_append s (h' :: t)).isInfix, ?_, ?_, ?_, Or.inr ⟨rfl, ?_⟩⟩
    · rw [List.getLast?_append_of_ne_nil _ (List.cons_ne_nil _ _)] at hl; exact hl
    · intro v hv; exact List.mem_append_right _ hv
    · simp
    · intro hmem'
      obtain ⟨a, s', rfl⟩ := List.exists_cons_of_ne_nil hs
      simp only [List.cons_append, List.head?_cons, Option.some.injEq] at hh
      subst hh
      have hnd := hP.1
      rw [List.cons_append, List.nodup_cons] at hnd
      exact hnd.1 (List.mem_append_right _ hmem')
  · exact ⟨P, hP, hl, fun v hv => hv, le_rfl, Or.inl ⟨hh, hmem⟩⟩

lemma trim_back {P : List V} {h l l' : V} (hP : IsPathL G P) (hh : P.head? = some h)
    (hl : P.getLast? = some l) (hl' : l' ≠ h) (hne : l' ≠ l) :
    ∃ P', IsPathL G P' ∧ P'.head? = some h ∧ (∀ v ∈ P', v ∈ P) ∧ P'.length ≤ P.length ∧
      ((P'.getLast? = some l ∧ l' ∉ P') ∨ (P'.getLast? = some l' ∧ l ∉ P')) := by
  obtain ⟨P', hP', hlast, hsub, hlen, hor⟩ := trim_front (G := G) (P := P.reverse) (h := l)
    (h' := l') (l := h) hP.reverse (by simpa using hl) (by simpa using hh) hl' hne
  refine ⟨P'.reverse, hP'.reverse, by simpa using hlast, fun v hv => ?_, by simpa using hlen, ?_⟩
  · exact List.mem_reverse.1 (hsub v (List.mem_reverse.1 hv))
  · rcases hor with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨by simpa using h1, by simpa using h2⟩
    · exact Or.inr ⟨by simpa using h1, by simpa using h2⟩

end Trim

section Case1

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

lemma near3_path {W : Finset V} {a b : V} (ha : a ∈ W) (hb : b ∈ W) (hab : a ≠ b)
    (h : Near3 G W a b) :
    ∃ P : List V, IsPathL G P ∧ P.head? = some a ∧ P.getLast? = some b ∧ P.length ≤ 4 ∧
      ∀ v ∈ P, v ∈ W := by
  have pair : G.Adj a b → ∃ P : List V, IsPathL G P ∧ P.head? = some a ∧ P.getLast? = some b ∧
      P.length ≤ 4 ∧ ∀ v ∈ P, v ∈ W := fun hadj =>
    ⟨[a, b], pathL_pair hadj, rfl, rfl, by simp, by simp [ha, hb]⟩
  rcases h with h | h | ⟨c, hc, h1, h2⟩ | ⟨c, hc, d, hd, h1, h2, h3⟩
  · exact absurd h hab
  · exact pair h
  · refine ⟨[a, c, b], ⟨?_, ?_⟩, rfl, rfl, by simp, by simp [ha, hb, hc]⟩
    · simp [G.ne_of_adj h1, G.ne_of_adj h2, hab]
    · simp [h1, h2]
  · by_cases hda : d = a
    · subst hda; exact pair h3
    by_cases hcb : c = b
    · subst hcb; exact pair h1
    refine ⟨[a, c, d, b], ⟨?_, ?_⟩, rfl, rfl, by simp, by simp [ha, hb, hc, hd]⟩
    · simp [G.ne_of_adj h1, G.ne_of_adj h2, G.ne_of_adj h3, hab, Ne.symm hda, hcb]
    · simp [h1, h2, h3]

/-- Two distinct edges touching `A` are joined by a short path through their endpoints. -/
lemma case1_connector {W A : Finset V} (hAW : A ⊆ W) (hnear : ∀ a ∈ A, ∀ b ∈ A, Near3 G W a b)
    (x₁ y₁ x₂ y₂ : V) (hx₁ : x₁ ∈ A) (hy₁ : y₁ ∈ W) (hx₂ : x₂ ∈ A) (hy₂ : y₂ ∈ W)
    (h₁ : G.Adj x₁ y₁) (h₂ : G.Adj x₂ y₂) (hne : s(x₁, y₁) ≠ s(x₂, y₂)) :
    ∃ Q : List V, IsPathL G Q ∧ (∀ v ∈ Q, v ∈ W) ∧ Q.length ≤ 6 ∧
      ∃ a' a c c', [a', a] <+: Q ∧ [c, c'] <:+ Q ∧ s(a', a) = s(x₁, y₁) ∧ s(c, c') = s(x₂, y₂) := by
  have hx₁W := hAW hx₁
  have hx₂W := hAW hx₂
  -- edges sharing a vertex
  have shared : ∀ o₁ m o₂ : V, o₁ ∈ W → m ∈ W → o₂ ∈ W → G.Adj o₁ m → G.Adj m o₂ → o₁ ≠ o₂ →
      s(o₁, m) = s(x₁, y₁) → s(m, o₂) = s(x₂, y₂) →
      ∃ Q : List V, IsPathL G Q ∧ (∀ v ∈ Q, v ∈ W) ∧ Q.length ≤ 6 ∧
        ∃ a' a c c', [a', a] <+: Q ∧ [c, c'] <:+ Q ∧ s(a', a) = s(x₁, y₁) ∧
          s(c, c') = s(x₂, y₂) := by
    intro o₁ m o₂ ho₁ hm ho₂ h1 h2 hne' e1 e2
    refine ⟨[o₁, m, o₂], ⟨?_, ?_⟩, by simp [ho₁, hm, ho₂], by simp, o₁, m, m, o₂,
      ⟨[o₂], rfl⟩, ⟨[o₁], rfl⟩, e1, e2⟩
    · simp [G.ne_of_adj h1, G.ne_of_adj h2, hne']
    · simp [h1, h2]
  by_cases e11 : x₁ = x₂
  · subst e11
    exact shared y₁ x₁ y₂ hy₁ hx₁W hy₂ h₁.symm h₂ (fun e => hne (by rw [e]))
      Sym2.eq_swap rfl
  by_cases e12 : x₁ = y₂
  · subst e12
    exact shared y₁ x₁ x₂ hy₁ hx₁W hx₂W h₁.symm h₂.symm (fun e => hne (by rw [e, Sym2.eq_swap]))
      Sym2.eq_swap Sym2.eq_swap
  by_cases e21 : y₁ = x₂
  · subst e21
    exact shared x₁ y₁ y₂ hx₁W hy₁ hy₂ h₁ h₂ (fun e => hne (by rw [e, Sym2.eq_swap])) rfl rfl
  by_cases e22 : y₁ = y₂
  · subst e22
    exact shared x₁ y₁ x₂ hx₁W hy₁ hx₂W h₁ h₂.symm e11 rfl Sym2.eq_swap
  -- disjoint edges: connect `x₁` to `x₂` and trim
  obtain ⟨P, hP, hPh, hPl, hPlen, hPW⟩ := near3_path hx₁W hx₂W e11 (hnear x₁ hx₁ x₂ hx₂)
  obtain ⟨P₁, hP₁, hP₁l, hP₁sub, hP₁len, hor₁⟩ :=
    trim_front hP hPh hPl e21 (fun e => G.ne_of_adj h₁ e.symm)
  -- `P₁` runs from `a ∈ {x₁, y₁}` to `x₂` and avoids the other endpoint `a'`
  obtain ⟨a, a', hP₁h, ha'P₁, hea⟩ : ∃ a a', P₁.head? = some a ∧ a' ∉ P₁ ∧
      s(a', a) = s(x₁, y₁) ∧ (a = x₁ ∨ a = y₁) ∧ (a' = x₁ ∨ a' = y₁) := by
    rcases hor₁ with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨x₁, y₁, h1, h2, Sym2.eq_swap, Or.inl rfl, Or.inr rfl⟩
    · exact ⟨y₁, x₁, h1, h2, rfl, Or.inr rfl, Or.inl rfl⟩
  obtain ⟨hea, hacase, ha'case⟩ := hea
  have hax₂ : y₂ ≠ a := by
    rcases hacase with rfl | rfl
    · exact fun e => e12 e.symm
    · exact fun e => e22 e.symm
  obtain ⟨P₂, hP₂, hP₂h, hP₂sub, hP₂len, hor₂⟩ :=
    trim_back hP₁ hP₁h hP₁l hax₂ (fun e => G.ne_of_adj h₂ e.symm)
  obtain ⟨c, c', hP₂l, hc'P₂, hec⟩ : ∃ c c', P₂.getLast? = some c ∧ c' ∉ P₂ ∧
      s(c, c') = s(x₂, y₂) ∧ (c = x₂ ∨ c = y₂) ∧ (c' = x₂ ∨ c' = y₂) := by
    rcases hor₂ with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨x₂, y₂, h1, h2, rfl, Or.inl rfl, Or.inr rfl⟩
    · exact ⟨y₂, x₂, h1, h2, Sym2.eq_swap, Or.inr rfl, Or.inl rfl⟩
  obtain ⟨hec, hccase, hc'case⟩ := hec
  have ha'P₂ : a' ∉ P₂ := fun h => ha'P₁ (hP₂sub a' h)
  have ha'c' : a' ≠ c' := by
    rcases ha'case with rfl | rfl <;> rcases hc'case with rfl | rfl <;> assumption
  have hadj1 : G.Adj a' a := by rw [← SimpleGraph.mem_edgeSet, hea]; exact h₁
  have hadj2 : G.Adj c c' := by rw [← SimpleGraph.mem_edgeSet, hec]; exact h₂
  have ha'W : a' ∈ W := by rcases ha'case with rfl | rfl <;> assumption
  have hc'W : c' ∈ W := by rcases hc'case with rfl | rfl <;> assumption
  obtain ⟨rest, hrest⟩ : ∃ rest, P₂ = a :: rest := by
    rcases P₂ with _ | ⟨b, rest⟩
    · simp at hP₂h
    · simp only [List.head?_cons, Option.some.injEq] at hP₂h
      exact ⟨rest, by rw [hP₂h]⟩
  obtain ⟨init, hinit⟩ : ∃ init, P₂ = init ++ [c] := by
    rcases List.eq_nil_or_concat P₂ with h | ⟨L, b, h⟩
    · simp [h] at hP₂l
    · rw [h, List.concat_eq_append, List.getLast?_concat, Option.some.injEq] at hP₂l
      exact ⟨L, by rw [h, hP₂l, List.concat_eq_append]⟩
  have hQ : IsPathL G (a' :: P₂ ++ [c']) := by
    refine (hP₂.cons ha'P₂ ?_).append (pathL_single c') ?_ ?_
    · rw [hrest]; simpa using hadj1
    · intro v hv hv'
      simp only [List.mem_singleton] at hv
      subst hv
      rcases List.mem_cons.1 hv' with h | h
      · exact ha'c' h.symm
      · exact hc'P₂ h
    · intro u hu v hv
      rw [hinit] at hu
      simp [List.getLast?_cons, List.getLast?_append] at hu hv
      subst hu; subst hv
      exact hadj2
  refine ⟨a' :: P₂ ++ [c'], hQ, ?_, ?_, a', a, c, c', ?_, ?_, hea, hec⟩
  · intro v hv
    simp only [List.cons_append, List.mem_cons, List.mem_append, List.not_mem_nil,
      or_false] at hv
    rcases hv with rfl | hv | rfl
    · exact ha'W
    · exact hPW v (hP₁sub v (hP₂sub v hv))
    · exact hc'W
  · simp only [List.cons_append, List.length_cons, List.length_append, List.length_nil]
    omega
  · rw [hrest]; exact ⟨rest ++ [c'], by simp⟩
  · rw [hinit]; exact ⟨a' :: init, by simp⟩

end Case1

section Case1b

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Closing a short path `Q` into a `C_{2k+1}`: greedy extension, then a path of length four. -/
lemma case1_pair {R k : ℕ} (col : Sym2 V → Fin R) (hk : 4 ≤ k)
    (hcyc : CycRainbow G col (2 * k + 1)) (W : Finset V) (D : ℕ)
    (hD : ∀ u ∈ W, D ≤ dW G W u) (hD2 : 2 * k - 2 ≤ D)
    (hpath4 : ∀ T : Finset V, T ⊆ W → T.card ≤ 2 * k - 4 → ∀ a ∈ W \ T, ∀ b ∈ W \ T, a ≠ b →
      ∃ c₁ ∈ W \ T, ∃ c₂ ∈ W \ T, ∃ c₃ ∈ W \ T, IsPathL G [a, c₁, c₂, c₃, b])
    (Q : List V) (hQ : IsPathL G Q) (hQW : ∀ v ∈ Q, v ∈ W) (hQlen : Q.length ≤ 6)
    (a' a c c' : V) (hpre : [a', a] <+: Q) (hsuf : [c, c'] <:+ Q) (hne : s(a', a) ≠ s(c, c')) :
    col s(a', a) ≠ col s(c, c') := by
  obtain ⟨B, hB⟩ := hpre
  obtain ⟨F, hF⟩ := hsuf
  have hQlast : Q.getLast? = some c' := by rw [← hF]; simp [List.getLast?_append]
  have hc'W : c' ∈ W := hQW c' (by rw [← hF]; simp)
  have hQlen2 : 2 ≤ Q.length := by rw [← hB]; simp
  -- greedy extension from `c'`
  have hT : Q.toFinset.card + (2 * k - 2 - Q.length) ≤ D := by
    rw [List.toFinset_card_of_nodup hQ.1]; omega
  obtain ⟨l, hl, hpl, hlT⟩ := greedy W D hD _ c' Q.toFinset hc'W hT
  have hQ2 : IsPathL G (Q ++ l) :=
    hQ.append_tail hQlast hpl (fun v hv hvQ => (hlT v hv).2 (List.mem_toFinset.2 hvQ))
  have hQ2len : (Q ++ l).length = 2 * k - 2 := by rw [List.length_append, hl]; omega
  have hQ2W : ∀ v ∈ Q ++ l, v ∈ W := fun v hv => by
    rcases List.mem_append.1 hv with h | h
    · exact hQW v h
    · exact (hlT v h).1
  obtain ⟨u, hu, humem⟩ : ∃ u, (Q ++ l).getLast? = some u ∧ u ∈ Q ++ l := by
    have hne' : Q ++ l ≠ [] := by rw [← hB]; simp
    exact ⟨_, List.getLast?_eq_getLast hne', List.getLast_mem hne'⟩
  have hQ2eq : Q ++ l = a' :: (a :: (B ++ l)) := by rw [← hB]; simp
  have hua : u ≠ a' := by
    intro e
    subst e
    have hnd := hQ2.1
    rw [hQ2eq] at hnd hu
    rw [List.getLast?_cons_cons] at hu
    exact (List.nodup_cons.1 hnd).1 (List.mem_of_getLast? hu)
  set T := ((Q ++ l).toFinset.erase u).erase a' with hTdef
  have ha'mem : a' ∈ Q ++ l := by rw [hQ2eq]; simp
  have hTW : T ⊆ W := fun v hv => hQ2W v (List.mem_toFinset.1
    (mem_erase.1 (mem_erase.1 (hTdef ▸ hv)).2).2)
  have hTcard : T.card ≤ 2 * k - 4 := by
    rw [hTdef, card_erase_of_mem, card_erase_of_mem (List.mem_toFinset.2 humem),
      List.toFinset_card_of_nodup hQ2.1, hQ2len]
    · omega
    · exact mem_erase.2 ⟨fun e => hua e.symm, List.mem_toFinset.2 ha'mem⟩
  have huT : u ∈ W \ T := mem_sdiff.2 ⟨hQ2W u humem, by simp [hTdef]⟩
  have ha'T : a' ∈ W \ T := mem_sdiff.2 ⟨hQ2W a' ha'mem, by simp [hTdef]⟩
  obtain ⟨c₁, hc₁, c₂, hc₂, c₃, hc₃, hp4⟩ := hpath4 T hTW hTcard u huT a' ha'T hua
  have hnd4 := hp4.1
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hnd4
  have hnotQ2 : ∀ v ∈ [c₁, c₂, c₃], v ∉ Q ++ l := by
    intro v hv hvQ
    have hvT : v ∉ T := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl | rfl
      · exact (mem_sdiff.1 hc₁).2
      · exact (mem_sdiff.1 hc₂).2
      · exact (mem_sdiff.1 hc₃).2
    have hvu : v ≠ u := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl | rfl
      · exact fun e => hnd4.1.1 e.symm
      · exact fun e => hnd4.1.2.1 e.symm
      · exact fun e => hnd4.1.2.2.1 e.symm
    have hva : v ≠ a' := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl | rfl
      · exact hnd4.2.1.2.2
      · exact hnd4.2.2.1.2
      · exact hnd4.2.2.2.1
    exact hvT (by rw [hTdef]; exact mem_erase.2 ⟨hva, mem_erase.2 ⟨hvu, List.mem_toFinset.2 hvQ⟩⟩)
  have hcyc_path : IsPathL G (Q ++ l ++ [c₁, c₂, c₃]) :=
    hQ2.append_tail hu (hp4.prefix_cons (mid := [c₁, c₂, c₃]) (B := [a'])) hnotQ2
  have hc₃a : G.Adj c₃ a' := by
    have := hp4.2
    simp only [List.isChain_cons_cons, List.isChain_singleton, and_true] at this
    exact this.2.2.2
  refine cyc_apply hcyc hcyc_path ?_ ?_ ?_ ?_ hne
  · rw [List.length_append, hQ2len]; simp; omega
  · intro x hx y hy
    rw [hQ2eq] at hx
    simp at hx
    simp [List.getLast?_cons, List.getLast?_append] at hy
    subst hx; subst hy
    exact hc₃a
  · exact infix_of_eq [] (B ++ l ++ [c₁, c₂, c₃] ++ [a']) (by rw [← hB]; simp)
  · have htake : (Q ++ l ++ [c₁, c₂, c₃]).take 1 = [a'] := by rw [hQ2eq]; simp
    rw [htake]
    exact infix_of_eq F (l ++ [c₁, c₂, c₃] ++ [a']) (by rw [← hF]; simp)

end Case1b

section Case1c

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

lemma orient_edge {W A : Finset V} {u v : V} (hu : u ∈ W) (hv : v ∈ W) (h : G.Adj u v)
    (hA : u ∈ A ∨ v ∈ A) : ∃ x y, x ∈ A ∧ y ∈ W ∧ G.Adj x y ∧ s(x, y) = s(u, v) := by
  rcases hA with hA | hA
  · exact ⟨u, v, hA, hv, h, rfl⟩
  · exact ⟨v, u, hA, hu, h.symm, Sym2.eq_swap⟩

/-- The good-edge count in Case 1: all edges touching `A` get distinct colours. -/
lemma case1_count {R k : ℕ} (col : Sym2 V → Fin R) (hk : 4 ≤ k)
    (hcyc : CycRainbow G col (2 * k + 1)) (W : Finset V) (D : ℕ)
    (hD : ∀ u ∈ W, D ≤ dW G W u) (hD2 : 2 * k - 2 ≤ D)
    (hpath4 : ∀ T : Finset V, T ⊆ W → T.card ≤ 2 * k - 4 → ∀ a ∈ W \ T, ∀ b ∈ W \ T, a ≠ b →
      ∃ c₁ ∈ W \ T, ∃ c₂ ∈ W \ T, ∃ c₃ ∈ W \ T, IsPathL G [a, c₁, c₂, c₃, b])
    (A : Finset V) (hAW : A ⊆ W) (hnear : ∀ a ∈ A, ∀ b ∈ A, Near3 G W a b) :
    sdeg G W ≤ 2 * R + (W.card - A.card) * (W.card - A.card) := by
  set P := (W ×ˢ W).filter (fun e => G.Adj e.1 e.2) with hP
  have hPc : P.card = sdeg G W := card_adj_pairs W
  have hsplit := card_filter_add_card_filter_not (s := P) (fun e => e.1 ∈ A ∨ e.2 ∈ A)
  have hgood : (P.filter (fun e => e.1 ∈ A ∨ e.2 ∈ A)).card ≤ 2 * R := by
    apply count_rainbow col
    intro e₁ he₁ e₂ he₂ hne
    rw [mem_filter, hP, mem_filter, mem_product] at he₁ he₂
    obtain ⟨x₁, y₁, hx₁, hy₁, h₁, e1⟩ := orient_edge he₁.1.1.1 he₁.1.1.2 he₁.1.2 he₁.2
    obtain ⟨x₂, y₂, hx₂, hy₂, h₂, e2⟩ := orient_edge he₂.1.1.1 he₂.1.1.2 he₂.1.2 he₂.2
    rw [← e1, ← e2] at hne ⊢
    obtain ⟨Q, hQ, hQW, hQlen, a', a, c, c', hpre, hsuf, ea, ec⟩ :=
      case1_connector hAW hnear x₁ y₁ x₂ y₂ hx₁ hy₁ hx₂ hy₂ h₁ h₂ hne
    rw [← ea, ← ec] at hne ⊢
    exact case1_pair col hk hcyc W D hD hD2 hpath4 Q hQ hQW hQlen a' a c c' hpre hsuf hne
  have hbad : (P.filter (fun e => ¬ (e.1 ∈ A ∨ e.2 ∈ A))).card ≤ sdeg G (W \ A) := by
    rw [← card_adj_pairs (W \ A)]
    apply card_le_card
    intro e he
    rw [mem_filter, hP, mem_filter, mem_product] at he
    rw [mem_filter, mem_product, mem_sdiff, mem_sdiff]
    push Not at he
    exact ⟨⟨⟨he.1.1.1, he.2.1⟩, ⟨he.1.1.2, he.2.2⟩⟩, he.1.2⟩
  have hle := sdeg_le (G := G) (W \ A)
  rw [card_sdiff_of_subset hAW] at hle
  have hsq : sdeg G (W \ A) ≤ (W.card - A.card) * (W.card - A.card) := by omega
  omega

end Case1c

section Analysis

/-- The lower-bound function `g(n, e) = e/2 + (n/2) √(e - n²/4) - ε n² - C` of Bucić–Chen–Ma. -/
noncomputable def gfun (ε C n e : ℝ) : ℝ := e / 2 + n / 2 * Real.sqrt (e - n ^ 2 / 4) - ε * n ^ 2 - C

lemma delta_bound_A (ε C n e δ : ℝ) (hε : 0 < ε) (hn : 1 ≤ n) (he : n ^ 2 / 4 < e)
    (hG : gfun ε C (n - 1) (e - δ) < gfun ε C n e ∨ e - δ ≤ (n - 1) ^ 2 / 4) :
    n / 2 - Real.sqrt (e - n ^ 2 / 4) - 1 / 2 < δ := by
  set s := Real.sqrt (e - n ^ 2 / 4) with hs
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hs2 : s ^ 2 = e - n ^ 2 / 4 := Real.sq_sqrt (by linarith)
  rcases hG with hG | hG
  · by_contra hδ
    push Not at hδ
    have harg : (s + 1 / 2) ^ 2 ≤ e - δ - (n - 1) ^ 2 / 4 := by nlinarith
    have hs' : s + 1 / 2 ≤ Real.sqrt (e - δ - (n - 1) ^ 2 / 4) :=
      Real.le_sqrt_of_sq_le harg
    unfold gfun at hG
    rw [← hs] at hG
    have h1 : (n - 1) * (s + 1 / 2) ≤ (n - 1) * Real.sqrt (e - δ - (n - 1) ^ 2 / 4) :=
      mul_le_mul_of_nonneg_left hs' (by linarith)
    nlinarith
  · nlinarith

lemma delta_bound_B (ε C n e δ γ c₁ : ℝ) (hε : 0 < ε) (hn : 1 ≤ n) (he : n ^ 2 / 4 < e)
    (hγ : 0 < γ) (hsγ : γ * n ≤ Real.sqrt (e - n ^ 2 / 4)) (hc0 : 0 ≤ c₁)
    (hc : c₁ + 1 ≤ γ ^ 2 * n ^ 2) (hc2 : (c₁ + 1 / 2) * (1 + 1 / γ) ≤ 2 * ε * n)
    (hG : gfun ε C (n - 1) (e - δ) < gfun ε C n e ∨ e - δ ≤ (n - 1) ^ 2 / 4) :
    n / 2 - Real.sqrt (e - n ^ 2 / 4) + c₁ < δ := by
  set s := Real.sqrt (e - n ^ 2 / 4) with hs
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hs2 : s ^ 2 = e - n ^ 2 / 4 := Real.sq_sqrt (by linarith)
  have hγn : 0 < γ * n := by positivity
  have hss : c₁ + 1 ≤ s ^ 2 := by nlinarith
  rcases hG with hG | hG
  · by_contra hδ
    push Not at hδ
    set a := s + 1 / 2 with ha
    set β := c₁ + 1 / 2 with hβ
    have ha0 : 0 < a := by linarith
    set q := β / a with hq
    have hqa : q * a = β := by rw [hq]; field_simp
    have hq0 : 0 ≤ q := by positivity
    have hβa : β ≤ a ^ 2 := by nlinarith
    have hqa' : q ≤ a := by nlinarith
    have harg : (a - q) ^ 2 ≤ e - δ - (n - 1) ^ 2 / 4 := by nlinarith
    have hs' : a - q ≤ Real.sqrt (e - δ - (n - 1) ^ 2 / 4) := Real.le_sqrt_of_sq_le harg
    have h1 : (n - 1) * (a - q) ≤ (n - 1) * Real.sqrt (e - δ - (n - 1) ^ 2 / 4) :=
      mul_le_mul_of_nonneg_left hs' (by linarith)
    -- `(n - 1) q ≤ β / γ`
    have hq2 : (n - 1) * q * γ ≤ β := by
      have : (n - 1) * γ ≤ a := by nlinarith
      nlinarith
    have hq3 : (n - 1) * q ≤ β * (1 / γ) := by
      rw [mul_one_div, le_div_iff₀ hγ]; linarith
    unfold gfun at hG
    rw [← hs] at hG
    have hG' : 4 * ε * n - 2 * ε < δ + n * s - (n - 1) * Real.sqrt (e - δ - (n - 1) ^ 2 / 4) := by
      linarith
    have hεn : ε * 1 ≤ ε * n := mul_le_mul_of_nonneg_left hn hε.le
    have hexp : (n - 1) * (a - q) = n * s - s + n / 2 - 1 / 2 - (n - 1) * q := by
      rw [ha]; ring
    linarith
  · nlinarith

lemma sqrt_le_half (n e : ℝ) (hn : 0 ≤ n) (he : e ≤ n ^ 2 / 2) :
    Real.sqrt (e - n ^ 2 / 4) ≤ n / 2 := by
  rw [Real.sqrt_le_left (by linarith)]
  nlinarith

end Analysis

section Case1Final

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

lemma sdeg_real_le (W : Finset V) : (sdeg G W : ℝ) ≤ (W.card : ℝ) ^ 2 := by
  have h := sdeg_le (G := G) W
  have : (sdeg G W : ℝ) + W.card ≤ W.card * W.card := by exact_mod_cast h
  nlinarith [(Nat.cast_nonneg W.card : (0 : ℝ) ≤ W.card)]

/-- Case 1 of the induction step (many edges): the good-edge count gives
`e/2 + (n/2)√(e - n²/4)` colours. -/
lemma case1_final {R k : ℕ} (col : Sym2 V → Fin R) (hk : 4 ≤ k)
    (hcyc : CycRainbow G col (2 * k + 1)) (W : Finset V) (s c₁ γ : ℝ)
    (hs : s = Real.sqrt ((sdeg G W : ℝ) / 2 - (W.card : ℝ) ^ 2 / 4))
    (he : (W.card : ℝ) ^ 2 / 4 < (sdeg G W : ℝ) / 2)
    (hγ : 0 < γ) (hsγ : γ * W.card ≤ s)
    (hc₁ : ((2 * k - 4 : ℕ) : ℝ) + ((2 * k - 4 : ℕ) : ℝ) / γ + 2 ≤ c₁)
    (hsm : ((2 * k - 4 : ℕ) : ℝ) * W.card + 2 * s ≤ s ^ 2)
    (hdeg : ∀ v ∈ W, (W.card : ℝ) / 2 - s + c₁ < dW G W v) :
    (sdeg G W : ℝ) / 4 + W.card / 2 * s ≤ R := by
  have hs0 : 0 ≤ s := hs ▸ Real.sqrt_nonneg _
  have hs2 : s ^ 2 = (sdeg G W : ℝ) / 2 - (W.card : ℝ) ^ 2 / 4 := by
    rw [hs]; exact Real.sq_sqrt (by linarith)
  have hσle := sdeg_real_le (G := G) W
  have hn0 : (0 : ℝ) ≤ W.card := Nat.cast_nonneg _
  have hsn : s ≤ W.card / 2 := by
    rw [hs]; exact sqrt_le_half _ _ hn0 (by linarith)
  have hnpos : (0 : ℝ) < W.card := by
    rcases eq_or_lt_of_le hn0 with h | h
    · rw [← h] at he; nlinarith
    · exact h
  have hspos : 0 < s := lt_of_lt_of_le (by positivity) hsγ
  set m : ℕ := 2 * k - 4 with hm
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg _
  have hmγ : (m : ℝ) * W.card / s ≤ m / γ := by
    rw [div_le_div_iff₀ hspos hγ]
    nlinarith
  -- paths of length four avoiding small sets
  have hpath4 : ∀ T : Finset V, T ⊆ W → T.card ≤ 2 * k - 4 → ∀ a ∈ W \ T, ∀ b ∈ W \ T, a ≠ b →
      ∃ c₁ ∈ W \ T, ∃ c₂ ∈ W \ T, ∃ c₃ ∈ W \ T, IsPathL G [a, c₁, c₂, c₃, b] := by
    intro T hT hTm a ha b hb hab
    refine path4_avoid W T hT m hTm s hspos (by linarith) hsm (fun v hv => ?_) a b ha hb hab
    have := hdeg v hv
    linarith
  -- degrees are at least `2k - 2`
  have hD : ∀ u ∈ W, 2 * k - 2 ≤ dW G W u := by
    intro u hu
    have h1 := hdeg u hu
    have h2 : (0 : ℝ) ≤ (m : ℝ) / γ := by positivity
    have h3 : ((2 * k - 2 : ℕ) : ℝ) = m + 2 := by
      rw [hm]; push_cast [show 2 ≤ 2 * k by omega, show 4 ≤ 2 * k by omega]; ring
    have : ((2 * k - 2 : ℕ) : ℝ) ≤ dW G W u := by linarith
    exact_mod_cast this
  -- a large set of pairwise close vertices
  have hW2 : (W.card : ℝ) ^ 2 < 2 * sdeg G W := by linarith
  obtain ⟨A, hAW, hAcard, hnear⟩ := dist3_set (G := G) W hW2 s hs0 (by nlinarith)
  have hcount := case1_count col hk hcyc W (2 * k - 2) hD le_rfl hpath4 A hAW hnear
  have hAle : A.card ≤ W.card := card_le_card hAW
  have hcountR : (sdeg G W : ℝ) ≤ 2 * R + ((W.card : ℝ) - A.card) * ((W.card : ℝ) - A.card) := by
    have : ((W.card - A.card : ℕ) : ℝ) = (W.card : ℝ) - A.card := by
      rw [Nat.cast_sub hAle]
    rw [← this]
    exact_mod_cast hcount
  have hd0 : (0 : ℝ) ≤ (W.card : ℝ) - A.card := by
    have : (A.card : ℝ) ≤ W.card := by exact_mod_cast hAle
    linarith
  have hd1 : (W.card : ℝ) - A.card ≤ W.card / 2 - s := by linarith
  have hsq : ((W.card : ℝ) - A.card) * ((W.card : ℝ) - A.card) ≤
      (W.card / 2 - s) * (W.card / 2 - s) := mul_le_mul hd1 hd1 hd0 (by linarith)
  nlinarith

end Case1Final

section Case2Final

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Case 2 of the induction step (few edges, minimum degree close to `n/2`). -/
lemma case2_final {R k : ℕ} (col : Sym2 V → Fin R) (hk : 4 ≤ k)
    (hcyc : CycRainbow G col (2 * k + 1)) (W : Finset V) (s γ : ℝ)
    (he : (W.card : ℝ) ^ 2 / 4 < (sdeg G W : ℝ) / 2)
    (hγ : 0 < γ) (hγ' : γ ≤ 1 / 400) (hsγ : s < γ * W.card)
    (hdeg : ∀ v ∈ W, (W.card : ℝ) / 2 - s - 1 / 2 < dW G W v)
    (hn : 80 * (k : ℝ) + 100 ≤ W.card) :
    ((W.card : ℝ) / 2 - 3 * γ * W.card - 10 * k - 3) ^ 2 / 2 ≤ R := by
  set n : ℝ := (W.card : ℝ) with hndef
  set δ₀ : ℝ := n / 2 - γ * n - 1 / 2 with hδ₀
  have hkR : (4 : ℝ) ≤ k := by exact_mod_cast hk
  have hγn : γ * n ≤ n / 400 := by nlinarith
  have hdeg0 : ∀ v ∈ W, δ₀ < dW G W v := fun v hv => by have := hdeg v hv; linarith
  have hL0 : 0 ≤ n / 2 - 3 * γ * n - 10 * k - 3 := by nlinarith
  set L := n / 2 - 3 * γ * n - 10 * k - 3 with hL
  have hθ : n / 4 + 5 * k ≤ 3 * δ₀ - n - 10 * k - 1 := by nlinarith
  have hδ5 : 5 * (k : ℝ) + 1 ≤ δ₀ := by nlinarith
  have hD : ∀ u ∈ W, δ₀ ≤ (dW G W u : ℝ) := fun u hu => (hdeg0 u hu).le
  rcases claim1 col (by omega) hcyc W δ₀ hD hθ hδ5 with hshort | hbound
  swap
  · have h1 : L ≤ δ₀ - 5 * k - 1 := by nlinarith
    have h2 : L ≤ 3 * δ₀ - n - 10 * k - 1 := by nlinarith
    have := mul_le_mul h1 h2 hL0 (by linarith)
    nlinarith
  -- the natural lower bound `D` on the degrees
  set D : ℕ := ⌈δ₀⌉₊ with hDdef
  have hDle : ∀ u ∈ W, D ≤ dW G W u := fun u hu => Nat.ceil_le.2 (hD u hu)
  have hDge : δ₀ ≤ D := Nat.le_ceil δ₀
  have hD2 : 2 * k + 7 ≤ D := by
    have : ((2 * k + 7 : ℕ) : ℝ) ≤ D := by push_cast; nlinarith
    exact_mod_cast this
  -- a triangle, and an edge of it with many common neighbours
  have hmantel : W.card * W.card < 2 * sdeg G W := by
    have : (W.card : ℝ) * W.card < 2 * sdeg G W := by nlinarith
    exact_mod_cast this
  obtain ⟨a, ha, b, hb, c, hc, hab, hbc, hac⟩ := mantel W hmantel
  obtain ⟨p, hp, q, hq, hpq, hbook⟩ := triangle_book W a b c ha hb hc hab hbc hac
  have h3D : 3 * D ≤ 3 * (nbW G W p ∩ nbW G W q).card + W.card := by
    have := hDle a ha; have := hDle b hb; have := hDle c hc; omega
  have h3DR : 3 * (D : ℝ) ≤ 3 * (nbW G W p ∩ nbW G W q).card + n := by
    rw [hndef]; exact_mod_cast h3D
  have hC6 : 6 ≤ (nbW G W p ∩ nbW G W q).card := by
    have : (6 : ℝ) ≤ (nbW G W p ∩ nbW G W q).card := by nlinarith
    exact_mod_cast this
  have hC : W.card + 8 < (nbW G W p ∩ nbW G W q).card + 2 * D := by
    have : n + 8 < (nbW G W p ∩ nbW G W q).card + 2 * (D : ℝ) := by nlinarith
    rw [hndef] at this
    exact_mod_cast this
  have hcount := case2_count col hk hcyc W D hDle hD2 hshort p q hp hq hpq hC6 hC
  have hD2' : 2 ≤ D := by omega
  have hcountR : ((D : ℝ) - 1) * ((D : ℝ) - 2) ≤ 2 * R := by
    have : (((D - 1) * (D - 2) : ℕ) : ℝ) ≤ 2 * R := by exact_mod_cast hcount
    rw [Nat.cast_mul, Nat.cast_sub (by omega), Nat.cast_sub hD2'] at this
    simpa using this
  have h1 : L ≤ (D : ℝ) - 1 := by nlinarith
  have h2 : L ≤ (D : ℝ) - 2 := by nlinarith
  have := mul_le_mul h1 h2 hL0 (by linarith)
  nlinarith

end Case2Final

section Numeric

lemma num_base (ε C n e : ℝ) (hε : 0 < ε) (hn0 : 0 ≤ n) (he : n ^ 2 / 4 < e) (he' : e ≤ n ^ 2 / 2)
    (hC : n ^ 2 / 2 ≤ C) : gfun ε C n e ≤ 0 := by
  unfold gfun
  have hs := sqrt_le_half n e hn0 he'
  have hs0 := Real.sqrt_nonneg (e - n ^ 2 / 4)
  have : n / 2 * Real.sqrt (e - n ^ 2 / 4) ≤ n / 2 * (n / 2) :=
    mul_le_mul_of_nonneg_left hs (by linarith)
  nlinarith

lemma num_case1 (k x n m : ℝ) (hk : 4 ≤ k) (hx : 100 ≤ x) (hn : 1000 * k * x ^ 3 < n)
    (hm0 : 0 ≤ m) (hm : m ≤ 2 * k) :
    m + m / (1 / (4 * x)) + 2 + 1 ≤ (1 / (4 * x)) ^ 2 * n ^ 2 ∧
    (m + m / (1 / (4 * x)) + 2 + 1 / 2) * (1 + 1 / (1 / (4 * x))) ≤ 2 * (1 / x) * n ∧
    (∀ s, 1 / (4 * x) * n ≤ s → m * n + 2 * s ≤ s ^ 2) := by
  have hx0 : 0 < x := by linarith
  have hk0 : 0 < k := by linarith
  have hkx : 400 ≤ k * x := by nlinarith
  have hx2 : 0 < x ^ 2 := by positivity
  have hkx2 : 100 * (k * x) ≤ k * x ^ 2 := by nlinarith
  have hkx3 : 100 * (k * x ^ 2) ≤ k * x ^ 3 := by nlinarith
  have hn1 : 1 ≤ n := by nlinarith
  have e1 : m / (1 / (4 * x)) = 4 * m * x := by field_simp
  have e2 : 1 / (1 / (4 * x)) = 4 * x := by field_simp
  rw [e1, e2]
  have hmx : m * x ≤ 2 * k * x := mul_le_mul_of_nonneg_right hm hx0.le
  have hc : m + 4 * m * x + 2 + 1 ≤ 10 * k * x := by nlinarith
  refine ⟨?_, ?_, ?_⟩
  · rw [show (1 / (4 * x)) ^ 2 * n ^ 2 = n ^ 2 / (4 * x) ^ 2 by ring, le_div_iff₀ (by positivity)]
    have h1 : (m + 4 * m * x + 2 + 1) * (4 * x) ^ 2 ≤ 10 * k * x * (4 * x) ^ 2 :=
      mul_le_mul_of_nonneg_right hc (by positivity)
    have h2 : n ≤ n ^ 2 := by nlinarith
    nlinarith
  · rw [show 2 * (1 / x) * n = 2 * n / x by ring, le_div_iff₀ hx0]
    have h2 : 1 + 4 * x ≤ 5 * x := by linarith
    have h3 : (m + 4 * m * x + 2 + 1 / 2) * (1 + 4 * x) ≤ 10 * k * x * (5 * x) :=
      mul_le_mul (by linarith) h2 (by positivity) (by positivity)
    have h4 : (m + 4 * m * x + 2 + 1 / 2) * (1 + 4 * x) * x ≤ 10 * k * x * (5 * x) * x :=
      mul_le_mul_of_nonneg_right h3 hx0.le
    nlinarith
  · intro s hs
    set u := n / (4 * x) with hu
    have hsn : u ≤ s := by rw [hu, div_eq_mul_one_div, mul_comm]; exact hs
    have hu4 : u * (4 * x) = n := by rw [hu]; field_simp
    have hbig : 8 * k * x + 2 ≤ u := by
      rw [hu, le_div_iff₀ (by positivity)]
      nlinarith
    have h1 : u * (u - 2) ≤ s * (s - 2) :=
      mul_le_mul hsn (by linarith) (by nlinarith) (by nlinarith)
    have h2 : u * (4 * m * x) ≤ u * (u - 2) :=
      mul_le_mul_of_nonneg_left (by nlinarith) (by nlinarith)
    have h3 : m * n = u * (4 * m * x) := by rw [← hu4]; ring
    nlinarith

lemma num_case2 (k x n e s C : ℝ) (hk : 4 ≤ k) (hx : 100 ≤ x) (hn : 1000 * k * x ^ 3 < n)
    (hC : 0 ≤ C) (hs0 : 0 ≤ s) (hs : s = Real.sqrt (e - n ^ 2 / 4)) (he : n ^ 2 / 4 < e)
    (hsγ : s < 1 / (4 * x) * n) :
    gfun (1 / x) C n e ≤ (n / 2 - 3 * (1 / (4 * x)) * n - 10 * k - 3) ^ 2 / 2 := by
  have hx0 : 0 < x := by linarith
  have hk0 : 0 < k := by linarith
  have hs2 : s ^ 2 = e - n ^ 2 / 4 := by rw [hs]; exact Real.sq_sqrt (by linarith)
  unfold gfun
  rw [← hs]
  have hkx : 400 ≤ k * x := by nlinarith
  have hx2 : 100 * x ≤ x ^ 2 := by nlinarith
  have hkx3 : 100 * (k * x) ≤ k * x ^ 2 := by nlinarith
  have hkx4 : 100 * (k * x ^ 2) ≤ k * x ^ 3 := by nlinarith
  have hn1 : 0 ≤ n := by nlinarith
  set g := 1 / (4 * x) * n with hg
  have hg4 : 4 * x * g = n := by rw [hg]; field_simp
  have hεn : 1 / x * n ^ 2 = 4 * g * n := by
    rw [← hg4]; field_simp
  have hK : 10 * k + 3 ≤ 4 * g := by
    have : (10 * k + 3) * x ≤ 4 * x * g := by rw [hg4]; nlinarith
    nlinarith
  have hsq : s * s ≤ g * g := mul_le_mul hsγ.le hsγ.le hs0 (by linarith)
  have hns : n * s ≤ n * g := mul_le_mul_of_nonneg_left hsγ.le hn1
  have hnK : n * (10 * k + 3) ≤ n * (4 * g) := mul_le_mul_of_nonneg_left hK hn1
  rw [show 3 * (1 / (4 * x)) * n = 3 * g by rw [hg]; ring, hεn]
  nlinarith [sq_nonneg (n / 2 - 3 * g - 10 * k - 3), sq_nonneg g]

end Numeric

section Induction

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- The lower bound of Bucić–Chen–Ma, `f(n, e, C_{2k+1}) ≥ g(n, e)`, by induction on the vertex
set: every colouring of `G[W]` with all `C_{2k+1}` rainbow uses at least `g(|W|, e(G[W]))` colours,
where `ε = 1/x` and `C = (1000 k x³)²`. -/
theorem lower_induction {R k : ℕ} (col : Sym2 V → Fin R) (hk : 4 ≤ k)
    (hcyc : CycRainbow G col (2 * k + 1)) (x : ℝ) (hx : 100 ≤ x) (W : Finset V) :
    (W.card : ℝ) ^ 2 / 4 < (sdeg G W : ℝ) / 2 →
      gfun (1 / x) ((1000 * k * x ^ 3) ^ 2) W.card ((sdeg G W : ℝ) / 2) ≤ R := by
  induction W using Finset.strongInduction with
  | H W ih =>
  intro he
  have hkR : (4 : ℝ) ≤ k := by exact_mod_cast hk
  have hx0 : 0 < x := by linarith
  have hσle := sdeg_real_le (G := G) W
  have hR0 : (0 : ℝ) ≤ R := Nat.cast_nonneg _
  have hN0 : 0 < 1000 * (k : ℝ) * x ^ 3 := by positivity
  by_cases hsmall : (W.card : ℝ) ≤ 1000 * k * x ^ 3
  · have hn0 : (0 : ℝ) ≤ W.card := Nat.cast_nonneg _
    have := num_base (1 / x) ((1000 * k * x ^ 3) ^ 2) W.card ((sdeg G W : ℝ) / 2) (by positivity)
      hn0 he (by linarith) (by nlinarith)
    linarith
  push Not at hsmall
  have hn1 : (1 : ℝ) ≤ W.card := by
    have hx3 : (1 : ℝ) ≤ x ^ 3 := one_le_pow₀ (by linarith)
    have : (1 : ℝ) ≤ 1000 * k * x ^ 3 := by nlinarith
    linarith
  have hWne : W.Nonempty := by
    rcases W.eq_empty_or_nonempty with h | h
    · exfalso; rw [h] at hn1; norm_num at hn1
    · exact h
  obtain ⟨v₀, hv₀, hmin⟩ := exists_min_image W (dW G W) hWne
  have hmin' : ∀ v ∈ W, (dW G W v₀ : ℝ) ≤ dW G W v := fun v hv => by exact_mod_cast hmin v hv
  by_cases hdone : gfun (1 / x) ((1000 * k * x ^ 3) ^ 2) W.card ((sdeg G W : ℝ) / 2) ≤ R
  · exact hdone
  -- the inductive hypothesis for `W - v₀`
  have hcardE : ((W.erase v₀).card : ℝ) = W.card - 1 := by
    rw [card_erase_of_mem hv₀, Nat.cast_sub (card_pos.2 hWne)]; simp
  have hsdegE : (sdeg G (W.erase v₀) : ℝ) / 2 = (sdeg G W : ℝ) / 2 - dW G W v₀ := by
    have := sdeg_erase (G := G) W v₀ hv₀
    have : (sdeg G (W.erase v₀) : ℝ) + 2 * dW G W v₀ = sdeg G W := by exact_mod_cast this
    linarith
  have hG : gfun (1 / x) ((1000 * k * x ^ 3) ^ 2) ((W.card : ℝ) - 1)
        ((sdeg G W : ℝ) / 2 - dW G W v₀) <
      gfun (1 / x) ((1000 * k * x ^ 3) ^ 2) W.card ((sdeg G W : ℝ) / 2) ∨
      (sdeg G W : ℝ) / 2 - dW G W v₀ ≤ ((W.card : ℝ) - 1) ^ 2 / 4 := by
    by_cases h1 : ((W.card : ℝ) - 1) ^ 2 / 4 < (sdeg G W : ℝ) / 2 - dW G W v₀
    · left
      have hih := ih (W.erase v₀) (erase_ssubset hv₀) (by rw [hcardE, hsdegE]; exact h1)
      rw [hcardE, hsdegE] at hih
      by_contra hc
      push Not at hc
      exact hdone (hc.trans hih)
    · right; push Not at h1; exact h1
  set s := Real.sqrt ((sdeg G W : ℝ) / 2 - (W.card : ℝ) ^ 2 / 4) with hs
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hA := delta_bound_A (1 / x) ((1000 * k * x ^ 3) ^ 2) W.card ((sdeg G W : ℝ) / 2)
    (dW G W v₀) (by positivity) hn1 he hG
  rw [← hs] at hA
  by_cases hcase : 1 / (4 * x) * (W.card : ℝ) ≤ s
  · -- Case 1
    set m : ℝ := ((2 * k - 4 : ℕ) : ℝ) with hm
    have hm0 : 0 ≤ m := Nat.cast_nonneg _
    have hm2 : m ≤ 2 * k := by
      rw [hm]; exact_mod_cast (by omega : 2 * k - 4 ≤ 2 * k)
    obtain ⟨na, nb, nc⟩ := num_case1 k x W.card m hkR hx hsmall hm0 hm2
    have hc0 : 0 ≤ m + m / (1 / (4 * x)) + 2 := by positivity
    have hB := delta_bound_B (1 / x) ((1000 * k * x ^ 3) ^ 2) W.card ((sdeg G W : ℝ) / 2)
      (dW G W v₀) (1 / (4 * x)) (m + m / (1 / (4 * x)) + 2) (by positivity) hn1 he (by positivity)
      hcase hc0 na nb hG
    rw [← hs] at hB
    have hfin := case1_final col hk hcyc W s (m + m / (1 / (4 * x)) + 2) (1 / (4 * x)) hs he
      (by positivity) hcase le_rfl (nc s hcase) (fun v hv => lt_of_lt_of_le hB (hmin' v hv))
    unfold gfun
    rw [← hs]
    have : (0 : ℝ) ≤ 1 / x * (W.card : ℝ) ^ 2 := by positivity
    nlinarith
  · -- Case 2
    push Not at hcase
    have hγ' : 1 / (4 * x) ≤ 1 / 400 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
    have hn80 : 80 * (k : ℝ) + 100 ≤ W.card := by
      have : (400 : ℝ) ≤ k * x := by nlinarith
      have : 100 * (k * x) ≤ k * x ^ 2 := by nlinarith
      have : 100 * (k * x ^ 2) ≤ k * x ^ 3 := by nlinarith
      nlinarith
    have hfin := case2_final col hk hcyc W s (1 / (4 * x)) he (by positivity) hγ' hcase
      (fun v hv => lt_of_lt_of_le hA (hmin' v hv)) hn80
    have hnum := num_case2 k x W.card ((sdeg G W : ℝ) / 2) s ((1000 * k * x ^ 3) ^ 2) hkR hx
      hsmall (by positivity) hs0 hs he hcase
    linarith

end Induction

section Upper

/-- Two disjoint cliques, on the vertices `< a` and on the vertices `≥ a`. -/
def twoCliques (n a : ℕ) : SimpleGraph (Fin n) where
  Adj u v := u ≠ v ∧ ((u : ℕ) < a ↔ (v : ℕ) < a)
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

lemma twoCliques_adj {n a : ℕ} {u v : Fin n} :
    (twoCliques n a).Adj u v ↔ u ≠ v ∧ ((u : ℕ) < a ↔ (v : ℕ) < a) := Iff.rfl

instance (n a : ℕ) : DecidableRel (twoCliques n a).Adj := fun _ _ =>
  decidable_of_iff _ twoCliques_adj.symm

lemma sdeg_univ_eq {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    sdeg G univ = 2 * G.edgeSet.ncard := by
  have h1 : sdeg G univ = ∑ v, G.degree v := by
    unfold sdeg dW nbW
    apply sum_congr rfl
    intro v _
    rw [← SimpleGraph.card_neighborFinset_eq_degree, SimpleGraph.neighborFinset_eq_filter]
  rw [h1, SimpleGraph.sum_degrees_eq_twice_card_edges, ← Set.ncard_coe_finset,
    SimpleGraph.coe_edgeFinset]

lemma card_filter_val_lt (n a : ℕ) (h : a ≤ n) :
    (univ.filter (fun i : Fin n => (i : ℕ) < a)).card = a := by
  have : univ.filter (fun i : Fin n => (i : ℕ) < a) = (univ : Finset (Fin a)).map (Fin.castLEEmb h) := by
    ext i
    simp only [mem_filter, mem_univ, true_and, mem_map, Fin.castLEEmb_apply]
    constructor
    · intro hi; exact ⟨⟨i, hi⟩, rfl⟩
    · rintro ⟨j, rfl⟩; simp
  rw [this, card_map, card_univ, Fintype.card_fin]

lemma twoCliques_ncard (n a : ℕ) (h : a ≤ n) :
    2 * (twoCliques n a).edgeSet.ncard = a * (a - 1) + (n - a) * (n - a - 1) := by
  rw [← sdeg_univ_eq]
  have hA := card_filter_val_lt n a h
  have hB : (univ.filter (fun i : Fin n => ¬ (i : ℕ) < a)).card = n - a := by
    have := card_filter_add_card_filter_not (s := (univ : Finset (Fin n))) (fun i => (i : ℕ) < a)
    rw [hA, card_univ, Fintype.card_fin] at this
    omega
  unfold sdeg
  rw [← sum_filter_add_sum_filter_not univ (fun i : Fin n => (i : ℕ) < a)]
  have e1 : ∀ v ∈ univ.filter (fun i : Fin n => (i : ℕ) < a), dW (twoCliques n a) univ v = a - 1 := by
    intro v hv
    rw [mem_filter] at hv
    unfold dW nbW
    have : univ.filter ((twoCliques n a).Adj v) = (univ.filter (fun i : Fin n => (i : ℕ) < a)).erase v := by
      ext u
      simp only [mem_filter, mem_univ, true_and, mem_erase, twoCliques_adj]
      constructor
      · rintro ⟨h1, h2⟩; exact ⟨h1.symm, h2.1 hv.2⟩
      · rintro ⟨h1, h2⟩; exact ⟨h1.symm, ⟨fun _ => h2, fun _ => hv.2⟩⟩
    rw [this, card_erase_of_mem (mem_filter.2 ⟨mem_univ v, hv.2⟩ :
      v ∈ univ.filter (fun i : Fin n => (i : ℕ) < a)), hA]
  have e2 : ∀ v ∈ univ.filter (fun i : Fin n => ¬ (i : ℕ) < a),
      dW (twoCliques n a) univ v = n - a - 1 := by
    intro v hv
    rw [mem_filter] at hv
    unfold dW nbW
    have : univ.filter ((twoCliques n a).Adj v) =
        (univ.filter (fun i : Fin n => ¬ (i : ℕ) < a)).erase v := by
      ext u
      simp only [mem_filter, mem_univ, true_and, mem_erase, twoCliques_adj]
      constructor
      · rintro ⟨h1, h2⟩; exact ⟨h1.symm, fun hu => hv.2 (h2.2 hu)⟩
      · rintro ⟨h1, h2⟩; exact ⟨h1.symm, ⟨fun h' => absurd h' hv.2, fun h' => absurd h' h2⟩⟩
    rw [this, card_erase_of_mem (mem_filter.2 ⟨mem_univ v, hv.2⟩ :
      v ∈ univ.filter (fun i : Fin n => ¬ (i : ℕ) < a)), hB]
  rw [sum_congr rfl e1, sum_congr rfl e2, sum_const, sum_const, hA, hB, smul_eq_mul, smul_eq_mul]

/-- The index of a vertex inside its clique. -/
def localIdx (n a : ℕ) (h : n ≤ 2 * a) (u : Fin n) : Fin a :=
  ⟨if (u : ℕ) < a then u else u - a, by split_ifs <;> omega⟩

lemma localIdx_inj (n a : ℕ) (h : n ≤ 2 * a) {u v : Fin n} (hb : (u : ℕ) < a ↔ (v : ℕ) < a)
    (he : localIdx n a h u = localIdx n a h v) : u = v := by
  simp only [localIdx, Fin.mk.injEq] at he
  apply Fin.ext
  by_cases hu : (u : ℕ) < a
  · have hv := hb.1 hu; rw [if_pos hu, if_pos hv] at he; exact he
  · have hv : ¬ (v : ℕ) < a := fun h' => hu (hb.2 h')
    rw [if_neg hu, if_neg hv] at he; omega

lemma copy_same_block {n a m : ℕ} (hm : 1 ≤ m) {G : SimpleGraph (Fin n)}
    (hGK : ∀ u v, G.Adj u v → (twoCliques n a).Adj u v)
    (f : (SimpleGraph.cycleGraph m).Copy G) :
    ∀ j (hj : j < m), ((f ⟨j, hj⟩ : ℕ) < a ↔ (f ⟨0, hm⟩ : ℕ) < a) := by
  intro j
  induction j with
  | zero => intro hj; exact Iff.rfl
  | succ j ih =>
    intro hj
    have hadj : (SimpleGraph.cycleGraph m).Adj ⟨j, by omega⟩ ⟨j + 1, hj⟩ := by
      rw [SimpleGraph.cycleGraph_adj']
      right
      rw [Fin.coe_sub_iff_le.2 (by rw [Fin.le_def]; simp)]
      simp
    have := twoCliques_adj.1 (hGK _ _ (f.toHom.map_adj hadj))
    exact this.2.symm.trans (ih (by omega))

/-- The two-clique construction: `C(a, 2)` colours suffice for a graph with `e` edges. -/
lemma upper_mem (n a e m : ℕ) (hm : 3 ≤ m) (han : a ≤ n) (h2a : n ≤ 2 * a) (ha2 : 2 ≤ a)
    (he : 2 * e ≤ a * (a - 1) + (n - a) * (n - a - 1)) :
    ∃ G : SimpleGraph (Fin n), G.edgeSet.ncard = e ∧
      ∃ col : G.edgeSet → Fin (a.choose 2), AllCopiesRainbow (SimpleGraph.cycleGraph m) G col := by
  classical
  have hK := twoCliques_ncard n a han
  obtain ⟨S, hSK, hScard⟩ := Set.exists_subset_card_eq (s := (twoCliques n a).edgeSet) (n := e)
    (by omega)
  have hGedge : (SimpleGraph.fromEdgeSet S).edgeSet = S := by
    rw [SimpleGraph.edgeSet_fromEdgeSet]
    ext z
    simp only [Set.mem_diff, and_iff_left_iff_imp]
    intro hz hd
    exact (twoCliques n a).not_isDiag_of_mem_edgeSet (hSK hz) hd
  have hGK : ∀ u v, (SimpleGraph.fromEdgeSet S).Adj u v → (twoCliques n a).Adj u v := by
    intro u v h
    rw [SimpleGraph.fromEdgeSet_adj] at h
    exact (SimpleGraph.mem_edgeSet _).1 (hSK h.1)
  have hcard : Fintype.card {z : Sym2 (Fin a) // ¬ z.IsDiag} = a.choose 2 := by
    rw [Sym2.card_subtype_not_diag, Fintype.card_fin]
  have hpos : 0 < a.choose 2 := Nat.choose_pos ha2
  let col' : Sym2 (Fin n) → Fin (a.choose 2) := fun z =>
    if h : ¬ (z.map (localIdx n a h2a)).IsDiag then Fintype.equivFinOfCardEq hcard ⟨_, h⟩
    else ⟨0, hpos⟩
  refine ⟨SimpleGraph.fromEdgeSet S, by rw [hGedge]; exact hScard, fun z => col' z.1, ?_⟩
  intro f
  have hblock := copy_same_block (by omega : 1 ≤ m) hGK f
  have hblk : ∀ i j : Fin m, ((f i : ℕ) < a ↔ (f j : ℕ) < a) := fun i j =>
    (hblock i i.2).trans (hblock j j.2).symm
  -- the colour of the image of an edge of the cycle
  have hcol : ∀ i j : Fin m, (SimpleGraph.cycleGraph m).Adj i j →
      ∃ h : ¬ (s(localIdx n a h2a (f i), localIdx n a h2a (f j))).IsDiag,
        col' s(f i, f j) = Fintype.equivFinOfCardEq hcard ⟨_, h⟩ := by
    intro i j hij
    have hadj := f.toHom.map_adj hij
    have hne : localIdx n a h2a (f i) ≠ localIdx n a h2a (f j) := fun h =>
      (SimpleGraph.fromEdgeSet S).ne_of_adj hadj (localIdx_inj n a h2a (hblk i j) h)
    have hnd : ¬ (s(localIdx n a h2a (f i), localIdx n a h2a (f j))).IsDiag := by
      rw [Sym2.mk_isDiag_iff]; exact hne
    refine ⟨hnd, ?_⟩
    have hnd' : ¬ (Sym2.map (localIdx n a h2a) s(f i, f j)).IsDiag := by
      rw [Sym2.map_mk]; exact hnd
    simp only [col']
    rw [dif_pos hnd']
    rfl
  rintro ⟨e₁, he₁⟩ ⟨e₂, he₂⟩ hc
  induction e₁ using Sym2.ind with
  | _ i₁ j₁ =>
  induction e₂ using Sym2.ind with
  | _ i₂ j₂ =>
  change col' (Sym2.map f s(i₁, j₁)) = col' (Sym2.map f s(i₂, j₂)) at hc
  rw [Sym2.map_mk, Sym2.map_mk] at hc
  obtain ⟨h1, e1⟩ := hcol i₁ j₁ he₁
  obtain ⟨h2, e2⟩ := hcol i₂ j₂ he₂
  rw [e1, e2] at hc
  have hc' := congrArg Subtype.val ((Fintype.equivFinOfCardEq hcard).injective hc)
  simp only at hc'
  apply Subtype.ext
  simp only
  have inj : ∀ i j : Fin m, localIdx n a h2a (f i) = localIdx n a h2a (f j) → i = j :=
    fun i j h => f.injective (localIdx_inj n a h2a (hblk i j) h)
  rcases Sym2.eq_iff.1 hc' with ⟨h3, h4⟩ | ⟨h3, h4⟩
  · rw [inj _ _ h3, inj _ _ h4]
  · rw [inj _ _ h3, inj _ _ h4, Sym2.eq_swap]

end Upper

section Statement

/-- Every admissible number of colours satisfies the Bucić–Chen–Ma lower bound. -/
lemma member_lower {n k r : ℕ} (hk : 4 ≤ k) (G : SimpleGraph (Fin n))
    (hG : G.edgeSet.ncard = n ^ 2 / 4 + 1) (col : G.edgeSet → Fin r)
    (hcol : AllCopiesRainbow (SimpleGraph.cycleGraph (2 * k + 1)) G col) (x : ℝ) (hx : 100 ≤ x) :
    (n : ℝ) ^ 2 / 8 - 1 / x * n ^ 2 - (1000 * k * x ^ 3) ^ 2 ≤ r := by
  classical
  have hne : G.edgeSet.Nonempty := Set.nonempty_of_ncard_ne_zero (by rw [hG]; omega)
  obtain ⟨e, he⟩ := hne
  have hr : 0 < r := Fin.pos (col ⟨e, he⟩)
  let col' : Sym2 (Fin n) → Fin r := fun z => if h : z ∈ G.edgeSet then col ⟨z, h⟩ else ⟨0, hr⟩
  have hext : ∀ z (hz : z ∈ G.edgeSet), col' z = col ⟨z, hz⟩ := fun z hz => by
    simp only [col', dif_pos hz]
  have hcyc := cycRainbow_of_copies col col' hext (2 * k + 1) (by omega) hcol
  have hsdeg : (sdeg G (univ : Finset (Fin n)) : ℝ) / 2 = ((n ^ 2 / 4 + 1 : ℕ) : ℝ) := by
    rw [sdeg_univ_eq, hG]; push_cast; ring
  have hcard : ((univ : Finset (Fin n)).card : ℝ) = n := by simp
  have hfl : (n : ℝ) ^ 2 / 4 < ((n ^ 2 / 4 + 1 : ℕ) : ℝ) := by
    have h4 : n ^ 2 < 4 * (n ^ 2 / 4 + 1) := by omega
    have : ((n : ℝ)) ^ 2 < 4 * ((n ^ 2 / 4 + 1 : ℕ) : ℝ) := by exact_mod_cast h4
    linarith
  have hmain := lower_induction col' hk hcyc x hx univ (by rw [hsdeg, hcard]; exact hfl)
  rw [hsdeg, hcard] at hmain
  unfold gfun at hmain
  have hsq := Real.sqrt_nonneg (((n ^ 2 / 4 + 1 : ℕ) : ℝ) - (n : ℝ) ^ 2 / 4)
  have : (0 : ℝ) ≤ (n : ℝ) / 2 * Real.sqrt (((n ^ 2 / 4 + 1 : ℕ) : ℝ) - (n : ℝ) ^ 2 / 4) := by
    positivity
  linarith

end Statement

section Main

open Filter Topology

lemma upper_params (n : ℕ) (hn : 64 ≤ n) :
    n / 2 + Nat.sqrt n + 2 ≤ n ∧ n ≤ 2 * (n / 2 + Nat.sqrt n + 2) ∧ 2 ≤ n / 2 + Nat.sqrt n + 2 ∧
    2 * (n ^ 2 / 4 + 1) ≤ (n / 2 + Nat.sqrt n + 2) * (n / 2 + Nat.sqrt n + 2 - 1) +
      (n - (n / 2 + Nat.sqrt n + 2)) * (n - (n / 2 + Nat.sqrt n + 2) - 1) := by
  set s := Nat.sqrt n with hs
  have h1 : s * s ≤ n := Nat.sqrt_le n
  have h2 : n < (s + 1) * (s + 1) := Nat.lt_succ_sqrt n
  have h3 : s + 2 ≤ n / 8 + 2 := by
    rcases Nat.lt_or_ge s 8 with h | h
    · omega
    · have : 8 * s ≤ s * s := Nat.mul_le_mul_right s h
      omega
  refine ⟨by omega, by omega, by omega, ?_⟩
  set a := n / 2 + s + 2 with ha
  obtain ⟨b, hb⟩ : ∃ b, b = n - a := ⟨_, rfl⟩
  rw [← hb]
  have hab : a + b = n := by omega
  have ha1 : 1 ≤ a := by omega
  have hb1 : 1 ≤ b := by omega
  have hd : 2 * s + 3 ≤ 2 * a - n := by omega
  have h4 : 4 * (n ^ 2 / 4) ≤ n ^ 2 := Nat.mul_div_le (n ^ 2) 4
  -- work in `ℤ`
  have hZ : (2 * (n ^ 2 / 4 + 1) : ℤ) ≤ (a : ℤ) * ((a : ℤ) - 1) + (b : ℤ) * ((b : ℤ) - 1) := by
    have hd' : (2 * (s : ℤ) + 3) ≤ 2 * (a : ℤ) - n := by
      have : 2 * s + 3 + n ≤ 2 * a := by omega
      have : (2 * s + 3 + n : ℤ) ≤ 2 * a := by exact_mod_cast this
      linarith
    have h2' : (n : ℤ) < ((s : ℤ) + 1) * ((s : ℤ) + 1) := by exact_mod_cast h2
    have h4' : (4 * ((n ^ 2 / 4 : ℕ) : ℤ)) ≤ (n : ℤ) ^ 2 := by exact_mod_cast h4
    have hab' : (a : ℤ) + b = n := by exact_mod_cast hab
    have hs0 : (0 : ℤ) ≤ s := Nat.cast_nonneg _
    have hsq : (2 * (s : ℤ) + 3) * (2 * (s : ℤ) + 3) ≤ (2 * (a : ℤ) - n) * (2 * (a : ℤ) - n) :=
      mul_le_mul hd' hd' (by linarith) (by linarith)
    nlinarith
  have hZ' : ((2 * (n ^ 2 / 4 + 1) : ℕ) : ℤ) ≤ ((a * (a - 1) + b * (b - 1) : ℕ) : ℤ) := by
    push_cast [Nat.cast_sub ha1, Nat.cast_sub hb1]
    exact hZ
  exact_mod_cast hZ'

/-- **Erdős Problem 809 for `k ≥ 4`** (Bucić–Chen–Ma 2026): for every `k ≥ 4`,
`χ_S(n, ⌊n²/4⌋ + 1, C_{2k+1}) / n² → 1/8`, i.e. `χ_S(n, ⌊n²/4⌋ + 1, C_{2k+1}) ∼ n²/8`. -/
theorem erdos_809 (k : ℕ) (hk : 4 ≤ k) :
    Tendsto (fun n : ℕ => (chiS n (n ^ 2 / 4 + 1) (SimpleGraph.cycleGraph (2 * k + 1)) : ℝ) /
      (n : ℝ) ^ 2) atTop (𝓝 (1 / 8)) := by
  have hmem : ∀ n : ℕ, 64 ≤ n → (n / 2 + Nat.sqrt n + 2).choose 2 ∈
      {r : ℕ | ∃ G : SimpleGraph (Fin n), G.edgeSet.ncard = n ^ 2 / 4 + 1 ∧
        ∃ col : G.edgeSet → Fin r, AllCopiesRainbow (SimpleGraph.cycleGraph (2 * k + 1)) G col} := by
    intro n hn
    obtain ⟨p1, p2, p3, p4⟩ := upper_params n hn
    exact upper_mem n _ _ (2 * k + 1) (by omega) p1 p2 p3 p4
  have hupper : ∀ n : ℕ, 64 ≤ n →
      (chiS n (n ^ 2 / 4 + 1) (SimpleGraph.cycleGraph (2 * k + 1)) : ℝ) ≤
        ((n : ℝ) / 2 + Nat.sqrt n + 2) ^ 2 / 2 := by
    intro n hn
    have h1 := Nat.sInf_le (hmem n hn)
    have h2 : 2 * (n / 2 + Nat.sqrt n + 2).choose 2 ≤
        (n / 2 + Nat.sqrt n + 2) * (n / 2 + Nat.sqrt n + 2) := by
      rw [Nat.choose_two_right]
      have := Nat.div_mul_le_self ((n / 2 + Nat.sqrt n + 2) * (n / 2 + Nat.sqrt n + 2 - 1)) 2
      have := Nat.mul_le_mul_left (n / 2 + Nat.sqrt n + 2) (Nat.sub_le (n / 2 + Nat.sqrt n + 2) 1)
      nlinarith
    have h3 : (2 * ((chiS n (n ^ 2 / 4 + 1) (SimpleGraph.cycleGraph (2 * k + 1)) : ℕ) : ℝ)) ≤
        ((n / 2 + Nat.sqrt n + 2 : ℕ) : ℝ) * ((n / 2 + Nat.sqrt n + 2 : ℕ) : ℝ) := by
      exact_mod_cast (Nat.mul_le_mul_left 2 h1).trans h2
    have h4 : ((n / 2 : ℕ) : ℝ) ≤ (n : ℝ) / 2 := by
      rw [le_div_iff₀ (by norm_num)]; exact_mod_cast Nat.div_mul_le_self n 2
    push_cast at h3
    have h5 : (0 : ℝ) ≤ ((n / 2 : ℕ) : ℝ) + Nat.sqrt n + 2 := by positivity
    nlinarith
  have hlower : ∀ n : ℕ, 64 ≤ n → ∀ x : ℝ, 100 ≤ x →
      (n : ℝ) ^ 2 / 8 - 1 / x * n ^ 2 - (1000 * k * x ^ 3) ^ 2 ≤
        (chiS n (n ^ 2 / 4 + 1) (SimpleGraph.cycleGraph (2 * k + 1)) : ℝ) := by
    intro n hn x hx
    obtain ⟨G, hG, col, hcol⟩ := Nat.sInf_mem ⟨_, hmem n hn⟩
    exact member_lower hk G hG col hcol x hx
  rw [tendsto_order]
  constructor
  · intro b hb
    set η := 1 / 8 - b with hη
    have hη0 : 0 < η := by linarith
    set x : ℝ := max 100 (4 / η) with hx
    have hx100 : 100 ≤ x := le_max_left _ _
    have hx0 : 0 < x := by linarith
    have hxη : 1 / x ≤ η / 4 := by
      rw [div_le_iff₀ hx0]
      have : 4 / η ≤ x := le_max_right _ _
      rw [div_le_iff₀ hη0] at this
      linarith
    set C := (1000 * (k : ℝ) * x ^ 3) ^ 2 with hC
    rw [eventually_atTop]
    refine ⟨max 64 (⌈4 * C / η⌉₊ + 1), fun n hn => ?_⟩
    have hn64 : 64 ≤ n := le_of_max_le_left hn
    have hnC : 4 * C / η + 1 ≤ (n : ℝ) := by
      have := le_of_max_le_right hn
      have h' : ((⌈4 * C / η⌉₊ + 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast this
      push_cast at h'
      linarith [Nat.le_ceil (4 * C / η)]
    have hnpos : (0 : ℝ) < n := by linarith [show (0 : ℝ) ≤ 4 * C / η by positivity]
    have hn1 : (1 : ℝ) ≤ n := by linarith [show (0 : ℝ) ≤ 4 * C / η by positivity]
    have hCn : C ≤ η / 4 * (n : ℝ) ^ 2 := by
      have h1 : 4 * C / η ≤ n := by linarith
      rw [div_le_iff₀ hη0] at h1
      nlinarith
    have hl := hlower n hn64 x hx100
    rw [lt_div_iff₀ (by positivity)]
    have h1 : 1 / x * (n : ℝ) ^ 2 ≤ η / 4 * (n : ℝ) ^ 2 :=
      mul_le_mul_of_nonneg_right hxη (by positivity)
    have hηn : η * (n : ℝ) ^ 2 = (n : ℝ) ^ 2 / 8 - b * (n : ℝ) ^ 2 := by rw [hη]; ring
    have hpos : 0 < η * (n : ℝ) ^ 2 := mul_pos hη0 (by positivity)
    linarith
  · intro b hb
    set η := b - 1 / 8 with hη
    have hη0 : 0 < η := by linarith
    set θ : ℝ := min (η / 2) 1 with hθ
    have hθ0 : 0 < θ := lt_min (by linarith) one_pos
    have hθη : θ ≤ η / 2 := min_le_left _ _
    have hθ1 : θ ≤ 1 := min_le_right _ _
    rw [eventually_atTop]
    refine ⟨max 64 (⌈4 / θ ^ 2⌉₊ + ⌈4 / θ⌉₊), fun n hn => ?_⟩
    have hn64 : 64 ≤ n := le_of_max_le_left hn
    have hnR : 4 / θ ^ 2 + 4 / θ ≤ (n : ℝ) := by
      have := le_of_max_le_right hn
      have h' : ((⌈4 / θ ^ 2⌉₊ + ⌈4 / θ⌉₊ : ℕ) : ℝ) ≤ n := by exact_mod_cast this
      push_cast at h'
      linarith [Nat.le_ceil (4 / θ ^ 2), Nat.le_ceil (4 / θ)]
    have hnpos : (0 : ℝ) < n := by
      have : (64 : ℝ) ≤ n := by exact_mod_cast hn64
      linarith
    have h4θ : 4 ≤ θ * n := by
      have : 4 / θ ≤ n := by linarith [show (0 : ℝ) ≤ 4 / θ ^ 2 by positivity]
      rwa [div_le_iff₀ hθ0, mul_comm] at this
    have h4θ2 : 4 ≤ θ ^ 2 * n := by
      have : 4 / θ ^ 2 ≤ n := by linarith [show (0 : ℝ) ≤ 4 / θ by positivity]
      rwa [div_le_iff₀ (by positivity), mul_comm] at this
    -- `√n + 2 ≤ θ n`
    have hsq : (Nat.sqrt n : ℝ) * Nat.sqrt n ≤ n := by exact_mod_cast Nat.sqrt_le n
    have hs : (Nat.sqrt n : ℝ) ≤ θ * n / 2 := by
      by_contra hc
      push Not at hc
      have h0 : (0 : ℝ) ≤ θ * n / 2 := by positivity
      have : θ * n / 2 * (θ * n / 2) < (Nat.sqrt n : ℝ) * Nat.sqrt n := mul_lt_mul'' hc hc h0 h0
      nlinarith
    have hu := hupper n hn64
    rw [div_lt_iff₀ (by positivity)]
    have ha : (n : ℝ) / 2 + Nat.sqrt n + 2 ≤ (n : ℝ) * (1 / 2 + θ) := by nlinarith
    have ha0 : (0 : ℝ) ≤ (n : ℝ) / 2 + Nat.sqrt n + 2 := by positivity
    have hsq2 : ((n : ℝ) / 2 + Nat.sqrt n + 2) ^ 2 ≤ ((n : ℝ) * (1 / 2 + θ)) ^ 2 :=
      pow_le_pow_left₀ ha0 ha 2
    have hθsq : θ ^ 2 ≤ θ := by nlinarith
    have hn2 : (0 : ℝ) < (n : ℝ) ^ 2 := by positivity
    nlinarith

end Main

section Corollary

open Filter Topology Asymptotics

/-- The set in the definition of `χ_S(n, ⌊n²/4⌋ + 1, C_{2k+1})` is nonempty for `n ≥ 64`, so the
infimum is attained: there is a graph on `n` vertices with `⌊n²/4⌋ + 1` edges and a colouring of
its edges with `χ_S` colours in which every copy of `C_{2k+1}` is rainbow. -/
theorem chiS_attained (k n : ℕ) (hk : 1 ≤ k) (hn : 64 ≤ n) :
    ∃ G : SimpleGraph (Fin n), G.edgeSet.ncard = n ^ 2 / 4 + 1 ∧
      ∃ col : G.edgeSet → Fin (chiS n (n ^ 2 / 4 + 1) (SimpleGraph.cycleGraph (2 * k + 1))),
        AllCopiesRainbow (SimpleGraph.cycleGraph (2 * k + 1)) G col := by
  obtain ⟨p1, p2, p3, p4⟩ := upper_params n hn
  have hmem : (n / 2 + Nat.sqrt n + 2).choose 2 ∈
      {r : ℕ | ∃ G : SimpleGraph (Fin n), G.edgeSet.ncard = n ^ 2 / 4 + 1 ∧
        ∃ col : G.edgeSet → Fin r, AllCopiesRainbow (SimpleGraph.cycleGraph (2 * k + 1)) G col} :=
    upper_mem n _ _ (2 * k + 1) (by omega) p1 p2 p3 p4
  exact Nat.sInf_mem ⟨_, hmem⟩

/-- **Erdős Problem 809 for `k ≥ 4`**, in the form `χ_S(n, ⌊n²/4⌋ + 1, C_{2k+1}) ∼ n²/8`. -/
theorem erdos_809_isEquivalent (k : ℕ) (hk : 4 ≤ k) :
    (fun n : ℕ => (chiS n (n ^ 2 / 4 + 1) (SimpleGraph.cycleGraph (2 * k + 1)) : ℝ)) ~[atTop]
      (fun n : ℕ => (n : ℝ) ^ 2 / 8) := by
  apply isEquivalent_of_tendsto_one
  have h := (erdos_809 k hk).const_mul 8
  rw [show (8 : ℝ) * (1 / 8) = 1 by norm_num] at h
  refine h.congr' ?_
  rw [EventuallyEq, eventually_atTop]
  refine ⟨1, fun n hn => ?_⟩
  have : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  simp only [Pi.div_apply]
  field_simp

end Corollary
end Erdos809
