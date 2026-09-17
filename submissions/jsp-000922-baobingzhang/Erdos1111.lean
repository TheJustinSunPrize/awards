import Mathlib

/-!
# Erdős Problem 1111: the case `c = 2` (Wagon's bound and the El Zahar–Erdős recurrence)

Erdős Problem 1111 ([ElEr85], https://www.erdosproblems.com/1111) reads:

> If `G` is a finite graph and `A, B` are disjoint sets of vertices then we call `A, B`
> anticomplete if there are no edges between `A` and `B`. If `t, c ≥ 1` then there exists `d ≥ 1`
> such that if `χ(G) ≥ d` and `ω(G) < t` then there are anticomplete sets `A, B` with
> `χ(A) ≥ χ(B) ≥ c`.

The problem is open for general `c`. For `c = 2` the page records, from El Zahar and Erdős
[ElEr85]: a result of Wagon [Wa80b] gives `d(t,2) ≤ C(t,2) + 1` and `d(t+1,2) ≤ d(t,2) + t`;
moreover `d(2,2) = 2`, `d(3,2) = 4` and `d(4,2) = 5`. It also records `d(3,3) ≤ 8`, a bound on
`d(t,3)`, and a weaker variant for all `c` due to Nguyen, Scott and Seymour [NSS24].

This file proves:

* the statement of the problem for `c ≤ 2` and every `t ≥ 1`, with `d = C(t,2) + 1`;
* Wagon's bound `d(t,2) ≤ C(t,2) + 1`, and Wagon's theorem behind it: a graph with no induced
  `2K₂` and clique number `ω` is `C(ω+1,2)`-colourable;
* the recurrence `d(t+1,2) ≤ d(t,2) + t` for `t ≥ 1`;
* the exact values `d(2,2) = 2` and `d(3,2) = 4`, and the lower bound `d(4,2) ≥ 5`.

It does **not** prove the upper bound `d(4,2) ≤ 5`. That bound says that every `K₄`-free graph
with no induced `2K₂` is 4-colourable, which is the theorem of Gaspers and Huang [GaHu19]. It also
proves nothing for `c ≥ 3`.

## Definitions and faithfulness

`IsAnticomplete`, `IsChromaticBound`, `d` and the theorem names `erdos_1111.variants.*` are copied
from the statement-only formal-conjectures pull request #5892 (Po-Han Shih, September 2026). That
pull request was closed without being merged.

* `IsAnticomplete G A B`: `A` and `B` are disjoint and no vertex of `A` is adjacent to a vertex of
  `B`.
* `IsChromaticBound t c d`: every graph `G` on a finite type with `d ≤ χ(G)` and `ω(G) < t` has
  anticomplete sets `A, B` with `c ≤ χ(G[A])` and `c ≤ χ(G[B])`. Here `χ` is Mathlib's
  `chromaticNumber` (valued in `ℕ∞`), `ω(G) < t` is `G.CliqueFree t`, and `G[A]` is
  `G.induce A`.
* `d t c = sInf {n | IsChromaticBound t c n}` is the least admissible `d`, and `0` if none exists.
  Every upper bound `d t 2 ≤ k` below is proved by showing that `k` is admissible. Every lower
  bound `k ≤ d t 2` is proved by showing that the set is nonempty and that no `n < k` is
  admissible. So none of these statements comes from the convention `sInf ∅ = 0`.
* `TwoK2Free G`: any two edges `ab`, `cd` are joined by an edge. If the four vertices are not
  distinct, the condition holds automatically, so this says exactly that `G` has no induced
  `2K₂`. By `exists_anticomplete_iff`, `G` has anticomplete `A, B` with `χ(G[A]), χ(G[B]) ≥ 2`
  iff `¬ TwoK2Free G`, because `χ(G[A]) ≥ 2` just means that `A` contains an edge.
* In `erdos_1111.variants.wagon` the hypothesis `1 ≤ t` is not used, since no graph is
  `K₀`-free. It is kept to match #5892. In `erdos_1111.variants.wagon_recurrence` it is needed.
  #5892 states the recurrence for all `t`, but it fails at `t = 0` because `d 0 2 = 0` and
  `d 1 2 = 1` (`not_wagon_recurrence_zero`). The problem only concerns `t ≥ 1`.

## Proofs

* **Wagon's theorem** (`wagon`, `colorable_of_maximum_clique`). Let `K` be a maximum clique. For a
  vertex `u`, let `M(u)` be the set of vertices of `K` not adjacent to `u` (`missed`). `M(u)` is
  nonempty: for `u ∈ K` it contains `u`, and otherwise `K ∪ {u}` would be a larger clique.
  Colour `u` by an unordered pair `{x, y}` with `x, y ∈ M(u)`, choosing `x = y` only when
  `M(u) = {x}`. The colours lie in `K.sym2`, which has `C(|K|+1, 2)` elements. Suppose two
  adjacent vertices `u, u'` get the same colour (`Good.false`).
  - If the colour is `{x, x}`, then `u` and `u'` are adjacent to all of `K \ {x}`, so
    `(K \ {x}) ∪ {u, u'}` is a clique larger than `K`.
  - If the colour is `{x, y}` with `x ≠ y`, then `uu'` and `xy` are edges with no edge between
    them, which is an induced `2K₂`.
* **Wagon's bound** (`erdos_1111.variants.wagon`). If `ω(G) < t` then
  `C(ω+1, 2) ≤ C(t, 2)`. So a graph with `χ(G) ≥ C(t,2) + 1` and `ω(G) < t` has an induced
  `2K₂`, and its two edges are the required sets `A, B`.
* **Recurrence** (`chromaticBound_succ`). Let `D` be admissible for `(t, 2)`, and let `G` have
  `ω(G) ≤ t` and no induced `2K₂`. If `ω(G) < t` then `χ(G) < D`. Otherwise pick a vertex `v`
  of a `t`-clique `K`, which is then a maximum clique. The neighbourhood of `v` induces a
  `K_t`-free graph with no induced `2K₂`, so its chromatic number `m` satisfies `m < D`. Every
  non-neighbour `u` of `v` has `v ∈ M(u)`. Colour it by some `y ∈ M(u)`, choosing `y ≠ v` when
  possible (`exists_good_of_not_adj`). Then `u` has colour `{v, y}` in the sense above, so this
  is a proper colouring of the non-neighbours with `|K| = t` colours. Together, `χ(G) ≤ m + t`,
  which is less than `D + t`. This is the neighbourhood argument that yields the recurrence. We
  did not check it against the text of [ElEr85].
* **Lower bounds** (`erdos_1111.variants.d_two_two`, `erdos_1111.variants.d_three_two`,
  `five_le_d_four_two`). The graph with one vertex has `χ = 1` and no edge. The 5-cycle `C5` is
  triangle-free, has no induced `2K₂`, and is not 2-colourable. The complement `C7c` of the
  7-cycle has these properties:
  - it is `K₄`-free, because the 7-cycle has no independent set of size 4;
  - it has no induced `2K₂`, because the 7-cycle has no induced 4-cycle;
  - it is not 3-colourable, because by pigeonhole some colour class would contain 3 vertices,
    and any 3 vertices of the 7-cycle span an edge of `C7c`.

  The finite checks on `Fin 5` and `Fin 7` are done by `decide`.

## Main results

* `Erdos1111.erdos_1111_of_le_two`: for `1 ≤ t` and `1 ≤ c ≤ 2`,
  `∃ d ≥ 1, IsChromaticBound t c d`.
* `Erdos1111.erdos_1111.variants.wagon`: `IsChromaticBound t 2 (t.choose 2 + 1)`.
* `Erdos1111.erdos_1111.variants.wagon_recurrence`: `1 ≤ t → d (t + 1) 2 ≤ d t 2 + t`.
* `Erdos1111.erdos_1111.variants.d_two_two`: `d 2 2 = 2`.
* `Erdos1111.erdos_1111.variants.d_three_two`: `d 3 2 = 4`; `isChromaticBound_three_two` is the
  explicit form `IsChromaticBound 3 2 4`.
* `Erdos1111.five_le_d_four_two`: `5 ≤ d 4 2`.
* `Erdos1111.wagon`: `TwoK2Free G → G.Colorable ((G.cliqueNum + 1).choose 2)` for finite `G`.
* `Erdos1111.d_zero_two`, `Erdos1111.d_one_two`, `Erdos1111.not_wagon_recurrence_zero`.

## References

* [ElEr85] El-Zahar, M. and Erdős, P., _On the existence of two nonneighboring subgraphs in a
  graph_, Combinatorica 5 (1985), 295–300.
* [Wa80b] Wagon, S., _A bound on the chromatic number of graphs without certain induced
  subgraphs_, J. Combin. Theory Ser. B 29 (1980), 345–346.
* [NSS24] Nguyen, T., Scott, A. and Seymour, P., _On a problem of El-Zahar and Erdős_,
  J. Combin. Theory Ser. B (2024), 211–222.
* [GaHu19] Gaspers, S. and Huang, S., _`(2P₂, K₄)`-free graphs are 4-colorable_, SIAM J. Discrete
  Math. 33 (2019); arXiv:1807.05547.
* formal-conjectures pull request #5892 (statement only, closed):
  https://github.com/google-deepmind/formal-conjectures/pull/5892
-/

namespace Erdos1111

open SimpleGraph

/-! ## The problem (definitions copied from formal-conjectures PR #5892) -/

/--
If $G$ is a finite graph and $A,B$ are disjoint sets of vertices then we call $A,B$ anticomplete
if there are no edges between $A$ and $B$.
-/
def IsAnticomplete {V : Type*} (G : SimpleGraph V) (A B : Set V) : Prop :=
  Disjoint A B ∧ ∀ a ∈ A, ∀ b ∈ B, ¬ G.Adj a b

/--
`IsChromaticBound t c d` means that $d$ is admissible for $d(t,c)$: every finite graph $G$
with $\chi(G)\ge d$ and $\omega(G)<t$ has anticomplete vertex sets $A,B$ with
$\chi(A),\chi(B)\ge c$. Here $\chi(A)$ is the chromatic number of the induced subgraph $G[A]$,
and `G.CliqueFree t` is $\omega(G)<t$.
-/
def IsChromaticBound (t c d : ℕ) : Prop :=
  ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
    (d : ℕ∞) ≤ G.chromaticNumber → G.CliqueFree t →
      ∃ A B : Set V, IsAnticomplete G A B ∧
        (c : ℕ∞) ≤ (G.induce A).chromaticNumber ∧
        (c : ℕ∞) ≤ (G.induce B).chromaticNumber

/--
$d(t,c)$ is the least $d$ such that every finite graph $G$ with $\chi(G)\ge d$ and $\omega(G)<t$
has anticomplete sets $A,B$ with $\chi(A),\chi(B)\ge c$. This is $0$ if no such $d$ exists.
-/
noncomputable def d (t c : ℕ) : ℕ :=
  sInf {n | IsChromaticBound t c n}

/-! ## Induced `2K₂` and the case `c = 2` -/

/-- `G` has no induced `2K₂`: any two edges `ab` and `cd` are joined by an edge. (If the four
vertices are not distinct, this holds automatically.) -/
def TwoK2Free {V : Type*} (G : SimpleGraph V) : Prop :=
  ∀ a b c d : V, G.Adj a b → G.Adj c d → G.Adj a c ∨ G.Adj a d ∨ G.Adj b c ∨ G.Adj b d

section Basic

variable {V : Type*} {G : SimpleGraph V}

theorem exists_adj_of_two_le {A : Set V} (h : ((2 : ℕ) : ℕ∞) ≤ (G.induce A).chromaticNumber) :
    ∃ a ∈ A, ∃ b ∈ A, G.Adj a b := by
  obtain ⟨x, y, hxy⟩ :=
    ne_bot_iff_exists_adj.mp (two_le_chromaticNumber_iff_ne_bot.mp (by simpa using h))
  exact ⟨x, x.2, y, y.2, hxy⟩

theorem two_le_of_adj {A : Set V} {a b : V} (ha : a ∈ A) (hb : b ∈ A) (h : G.Adj a b) :
    ((2 : ℕ) : ℕ∞) ≤ (G.induce A).chromaticNumber := by
  simpa using two_le_chromaticNumber_of_adj (G := G.induce A) (u := ⟨a, ha⟩) (v := ⟨b, hb⟩) h

/-- The conclusion of the problem for `c = 2` holds exactly when `G` has an induced `2K₂`. -/
theorem exists_anticomplete_iff :
    (∃ A B : Set V, IsAnticomplete G A B ∧ ((2 : ℕ) : ℕ∞) ≤ (G.induce A).chromaticNumber ∧
        ((2 : ℕ) : ℕ∞) ≤ (G.induce B).chromaticNumber) ↔ ¬ TwoK2Free G := by
  constructor
  · rintro ⟨A, B, ⟨-, hAB⟩, hA, hB⟩ h
    obtain ⟨a, ha, b, hb, hab⟩ := exists_adj_of_two_le hA
    obtain ⟨c, hc, d, hd, hcd⟩ := exists_adj_of_two_le hB
    rcases h a b c d hab hcd with h | h | h | h
    · exact hAB a ha c hc h
    · exact hAB a ha d hd h
    · exact hAB b hb c hc h
    · exact hAB b hb d hd h
  · intro h
    simp only [TwoK2Free, not_forall, not_or] at h
    obtain ⟨a, b, c, d, hab, hcd, hac, had, hbc, hbd⟩ := h
    have h1 : a ≠ c := fun h => had (h ▸ hcd)
    have h2 : a ≠ d := fun h => hac (h ▸ hcd.symm)
    have h3 : b ≠ c := fun h => hbd (h ▸ hcd)
    have h4 : b ≠ d := fun h => hbc (h ▸ hcd.symm)
    refine ⟨{a, b}, {c, d}, ⟨?_, ?_⟩, two_le_of_adj (by simp) (by simp) hab,
      two_le_of_adj (by simp) (by simp) hcd⟩
    · rw [Set.disjoint_left]
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      rintro x (rfl | rfl) (h | h)
      exacts [h1 h, h2 h, h3 h, h4 h]
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      rintro x (rfl | rfl) y (rfl | rfl)
      exacts [hac, had, hbc, hbd]

end Basic

/-! ## Wagon's theorem -/

section Wagon

variable {V : Type*} {G : SimpleGraph V} {K : Finset V}

open Classical in
/-- The vertices of `K` that are not adjacent to `u`. -/
noncomputable def missed (G : SimpleGraph V) (K : Finset V) (u : V) : Finset V :=
  K.filter (fun w => ¬ G.Adj u w)

theorem mem_missed {u w : V} : w ∈ missed G K u ↔ w ∈ K ∧ ¬ G.Adj u w := by
  simp [missed]

theorem missed_nonempty (hK : G.IsClique (K : Set V))
    (hmax : ∀ L : Finset V, G.IsClique (L : Set V) → L.card ≤ K.card) (u : V) :
    (missed G K u).Nonempty := by
  classical
  by_contra h
  have hadj : ∀ w ∈ K, G.Adj u w := by
    intro w hw
    by_contra hn
    exact h ⟨w, mem_missed.mpr ⟨hw, hn⟩⟩
  have hu : u ∉ K := fun hu => (hadj u hu).ne rfl
  have := hmax (insert u K) (by
    rw [Finset.coe_insert]
    exact hK.insert fun b hb _ => hadj b hb)
  rw [Finset.card_insert_of_notMem hu] at this
  omega

/-- Two adjacent vertices cannot both miss exactly the same single vertex `x` of a maximum
clique `K`: otherwise `(K \ {x}) ∪ {u, u'}` would be a larger clique. -/
theorem false_of_missed_singleton (hK : G.IsClique (K : Set V))
    (hmax : ∀ L : Finset V, G.IsClique (L : Set V) → L.card ≤ K.card) {u u' x : V}
    (huu' : G.Adj u u') (hx : x ∈ missed G K u)
    (hu : ∀ z ∈ missed G K u, z = x) (hu' : ∀ z ∈ missed G K u', z = x) : False := by
  classical
  have hxK : x ∈ K := (mem_missed.mp hx).1
  have hadj : ∀ w ∈ K.erase x, G.Adj u w := by
    intro w hw
    obtain ⟨hne, hwK⟩ := Finset.mem_erase.mp hw
    by_contra hn
    exact hne (hu w (mem_missed.mpr ⟨hwK, hn⟩))
  have hadj' : ∀ w ∈ K.erase x, G.Adj u' w := by
    intro w hw
    obtain ⟨hne, hwK⟩ := Finset.mem_erase.mp hw
    by_contra hn
    exact hne (hu' w (mem_missed.mpr ⟨hwK, hn⟩))
  have hu1 : u ∉ K.erase x := fun h => (hadj u h).ne rfl
  have hu1' : u' ∉ K.erase x := fun h => (hadj' u' h).ne rfl
  have hu2 : u ∉ insert u' (K.erase x) := by
    rw [Finset.mem_insert]
    rintro (h | h)
    · exact huu'.ne h
    · exact hu1 h
  have hcl : G.IsClique ((insert u (insert u' (K.erase x)) : Finset V) : Set V) := by
    rw [Finset.coe_insert, Finset.coe_insert]
    refine IsClique.insert (IsClique.insert
      (hK.subset (Finset.coe_subset.mpr (Finset.erase_subset x K))) ?_) ?_
    · intro b hb _
      exact hadj' b hb
    · intro b hb _
      rcases hb with rfl | hb
      · exact huu'
      · exact hadj b hb
  have := hmax _ hcl
  rw [Finset.card_insert_of_notMem hu2, Finset.card_insert_of_notMem hu1',
    Finset.card_erase_of_mem hxK] at this
  have : 0 < K.card := Finset.card_pos.mpr ⟨x, hxK⟩
  omega

/-- Two adjacent vertices cannot both miss two distinct vertices `x ≠ y` of the clique `K`:
the edges `uu'` and `xy` would form an induced `2K₂`. -/
theorem false_of_missed_pair (hK : G.IsClique (K : Set V)) (h2 : TwoK2Free G) {u u' x y : V}
    (huu' : G.Adj u u') (hxy : x ≠ y) (hx : x ∈ missed G K u) (hy : y ∈ missed G K u)
    (hx' : x ∈ missed G K u') (hy' : y ∈ missed G K u') : False := by
  rw [mem_missed] at hx hy hx' hy'
  have hxy' : G.Adj x y := hK hx.1 hy.1 hxy
  rcases h2 u u' x y huu' hxy' with h | h | h | h
  exacts [hx.2 h, hy.2 h, hx'.2 h, hy'.2 h]

/-- `Good G K u p`: the pair `p = {x, y}` is an admissible colour for `u`, i.e. `x, y` are
missed by `u`, and `x = y` only if `x` is the only vertex of `K` missed by `u`. -/
def Good (G : SimpleGraph V) (K : Finset V) (u : V) (p : Sym2 V) : Prop :=
  ∃ x y, p = s(x, y) ∧ x ∈ missed G K u ∧ y ∈ missed G K u ∧
    (x = y → ∀ z ∈ missed G K u, z = x)

/-- Adjacent vertices never share an admissible colour. -/
theorem Good.false (hK : G.IsClique (K : Set V))
    (hmax : ∀ L : Finset V, G.IsClique (L : Set V) → L.card ≤ K.card) (h2 : TwoK2Free G)
    {u u' : V} {p : Sym2 V} (hu : Good G K u p) (hu' : Good G K u' p) (huu' : G.Adj u u') :
    False := by
  obtain ⟨x, y, rfl, hx, hy, hxy⟩ := hu
  obtain ⟨x', y', he, hx', hy', hxy'⟩ := hu'
  by_cases h : x = y
  · subst h
    have hx'y' : x' = y' := by
      rcases Sym2.eq_iff.mp he with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> rw [← e1, ← e2]
    subst hx'y'
    have : x = x' := by
      rcases Sym2.eq_iff.mp he with ⟨e1, -⟩ | ⟨e1, -⟩ <;> exact e1
    subst this
    exact false_of_missed_singleton hK hmax huu' hx (hxy rfl) (hxy' rfl)
  · rcases Sym2.eq_iff.mp he with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> subst e1 e2
    · exact false_of_missed_pair hK h2 huu' h hx hy hx' hy'
    · exact false_of_missed_pair hK h2 huu' h hx hy hy' hx'

theorem exists_good (hK : G.IsClique (K : Set V))
    (hmax : ∀ L : Finset V, G.IsClique (L : Set V) → L.card ≤ K.card) (u : V) :
    ∃ x ∈ K, ∃ y ∈ K, Good G K u s(x, y) := by
  obtain ⟨x, hx⟩ := missed_nonempty hK hmax u
  by_cases h : ∀ z ∈ missed G K u, z = x
  · exact ⟨x, (mem_missed.mp hx).1, x, (mem_missed.mp hx).1, x, x, rfl, hx, hx, fun _ => h⟩
  · push Not at h
    obtain ⟨z, hz, hzx⟩ := h
    exact ⟨x, (mem_missed.mp hx).1, z, (mem_missed.mp hz).1, x, z, rfl, hx, hz,
      fun h => absurd h.symm hzx⟩

/-- A non-neighbour `u` of `v ∈ K` has an admissible colour of the form `{v, y}`. -/
theorem exists_good_of_not_adj {v u : V} (hv : v ∈ K) (hvu : ¬ G.Adj v u) :
    ∃ y ∈ K, Good G K u s(v, y) := by
  have hvm : v ∈ missed G K u := mem_missed.mpr ⟨hv, fun h => hvu h.symm⟩
  by_cases h : ∀ z ∈ missed G K u, z = v
  · exact ⟨v, hv, v, v, rfl, hvm, hvm, fun _ => h⟩
  · push Not at h
    obtain ⟨z, hz, hzv⟩ := h
    exact ⟨z, (mem_missed.mp hz).1, v, z, rfl, hvm, hz, fun h => absurd h.symm hzv⟩

/-- Wagon's colouring: a graph with no induced `2K₂` and a maximum clique `K` is
`C(|K|+1, 2)`-colourable. -/
theorem colorable_of_maximum_clique (hK : G.IsClique (K : Set V))
    (hmax : ∀ L : Finset V, G.IsClique (L : Set V) → L.card ≤ K.card) (h2 : TwoK2Free G) :
    G.Colorable ((K.card + 1).choose 2) := by
  classical
  choose x hx y hy hg using exists_good hK hmax
  let C : G.Coloring K.sym2 := Coloring.mk
    (fun u => ⟨s(x u, y u), Finset.mk_mem_sym2_iff.mpr ⟨hx u, hy u⟩⟩)
    (fun {u u'} huu' he => by
      have he' : s(x u, y u) = s(x u', y u') := congrArg Subtype.val he
      exact (hg u).false hK hmax h2 (he' ▸ hg u') huu')
  have := C.colorable
  rwa [Fintype.card_coe, Finset.card_sym2] at this

/-- **Wagon's theorem** [Wa80b]: a finite graph with no induced `2K₂` and clique number `ω` is
`C(ω+1, 2)`-colourable. -/
theorem wagon {V : Type*} [Finite V] (G : SimpleGraph V) (h2 : TwoK2Free G) :
    G.Colorable ((G.cliqueNum + 1).choose 2) := by
  obtain ⟨K, hK⟩ := G.maximumClique_exists
  rw [← maximumClique_card_eq_cliqueNum K hK]
  exact colorable_of_maximum_clique hK.isClique hK.maximum h2

theorem colorable_of_cliqueFree {V : Type*} [Finite V] (G : SimpleGraph V) {t : ℕ}
    (ht : G.CliqueFree t) (h2 : TwoK2Free G) : G.Colorable (t.choose 2) := by
  refine (wagon G h2).mono (Nat.choose_le_choose 2 ?_)
  obtain ⟨s, hs⟩ := G.exists_isNClique_cliqueNum
  by_contra hlt
  exact ht.mono (by omega) s hs

end Wagon

/-! ## Wagon's bound and the recurrence -/

/--
El Zahar and Erdős [ElEr85] note that a result of Wagon [Wa80b] implies
$d(t,2)\leq \binom{t}{2}+1$.
-/
theorem erdos_1111.variants.wagon (t : ℕ) (_ht : 1 ≤ t) :
    IsChromaticBound t 2 (t.choose 2 + 1) := by
  intro V _ G hχ hG
  rw [exists_anticomplete_iff]
  intro h2
  have h := hχ.trans (colorable_of_cliqueFree G hG h2).chromaticNumber_le
  norm_cast at h
  omega

/-- The explicit instance `d(3,2) ≤ 4`: every finite triangle-free graph with `χ(G) ≥ 4` has two
anticomplete sets, each inducing a subgraph of chromatic number at least `2`. -/
theorem isChromaticBound_three_two : IsChromaticBound 3 2 4 :=
  erdos_1111.variants.wagon 3 (by norm_num)

/-- If `D` is admissible for `(t, 2)`, then `D + t` is admissible for `(t + 1, 2)`. -/
theorem chromaticBound_succ {t D : ℕ} (ht : 1 ≤ t) (hD : IsChromaticBound t 2 D) :
    IsChromaticBound (t + 1) 2 (D + t) := by
  intro V _ G hχ hG
  classical
  rw [exists_anticomplete_iff]
  intro h2
  by_cases hGt : G.CliqueFree t
  · exact exists_anticomplete_iff.mp
      (hD V G (le_trans (by norm_cast; omega) hχ) hGt) h2
  simp only [CliqueFree, not_forall, not_not] at hGt
  obtain ⟨K, hK⟩ := hGt
  obtain ⟨v, hv⟩ : K.Nonempty := Finset.card_pos.mp (by rw [hK.card_eq]; omega)
  have hmax : ∀ L : Finset V, G.IsClique (L : Set V) → L.card ≤ K.card := by
    intro L hL
    rw [hK.card_eq]
    by_contra hlt
    obtain ⟨L', hL'L, hL'card⟩ := Finset.exists_subset_card_eq (by omega : t + 1 ≤ L.card)
    exact hG L' ⟨hL.subset (by exact_mod_cast hL'L), hL'card⟩
  let H := G.induce (G.neighborSet v)
  have hH : H.CliqueFree t := by
    intro s hs
    rw [isNClique_induce_iff] at hs
    refine hG _ (hs.insert (a := v) ?_)
    intro b hb
    obtain ⟨b', -, rfl⟩ := Finset.mem_map.mp hb
    exact b'.2
  have hH2 : ¬ (D : ℕ∞) ≤ H.chromaticNumber := by
    intro hle
    exact exists_anticomplete_iff.mp (hD _ H hle hH) (fun a b c d hab hcd => h2 a b c d hab hcd)
  push Not at hH2
  obtain ⟨m, hm⟩ : ∃ m : ℕ, H.chromaticNumber = m :=
    ENat.ne_top_iff_exists.mp (ne_top_of_lt hH2) |>.imp fun _ h => h.symm
  have hmD : m < D := by rw [hm] at hH2; exact_mod_cast hH2
  obtain ⟨cH⟩ := chromaticNumber_le_iff_colorable.mp hm.le
  choose! y hyK hy using fun u (hu : ¬ G.Adj v u) => exists_good_of_not_adj hv hu
  let C : G.Coloring (Fin m ⊕ K) := Coloring.mk
    (fun u => if h : G.Adj v u then Sum.inl (cH ⟨u, h⟩) else Sum.inr ⟨y u, hyK u h⟩)
    (fun {u u'} huu' he => by
      by_cases hu : G.Adj v u <;> by_cases hu' : G.Adj v u' <;> simp only [hu, hu',
        dite_true, dite_false, Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq,
        Subtype.mk.injEq] at he
      · exact cH.valid (show H.Adj ⟨u, hu⟩ ⟨u', hu'⟩ from huu') he
      · exact (hy u hu).false hK.isClique hmax h2 (he ▸ hy u' hu') huu')
  have hC := C.colorable
  simp only [Fintype.card_sum, Fintype.card_fin, Fintype.card_coe, hK.card_eq] at hC
  have h := hχ.trans hC.chromaticNumber_le
  norm_cast at h
  omega

/--
In fact $d(t+1,2)\leq d(t,2)+t$ (for $t \geq 1$; see `not_wagon_recurrence_zero` for $t = 0$).
-/
theorem erdos_1111.variants.wagon_recurrence (t : ℕ) (ht : 1 ≤ t) :
    d (t + 1) 2 ≤ d t 2 + t := by
  have hD : IsChromaticBound t 2 (d t 2) :=
    Nat.sInf_mem (s := {n | IsChromaticBound t 2 n}) ⟨_, erdos_1111.variants.wagon t ht⟩
  exact Nat.sInf_le (chromaticBound_succ ht hD)

/-! ## The problem for `c ≤ 2` -/

/-- The statement of Erdős Problem 1111 holds for `c ≤ 2`, with `d = C(t,2) + 1`. -/
theorem erdos_1111_of_le_two (t c : ℕ) (ht : 1 ≤ t) (_hc : 1 ≤ c) (hc2 : c ≤ 2) :
    ∃ d ≥ 1, IsChromaticBound t c d := by
  refine ⟨t.choose 2 + 1, by omega, fun V _ G hχ hG => ?_⟩
  obtain ⟨A, B, hAB, hA, hB⟩ := erdos_1111.variants.wagon t ht V G hχ hG
  exact ⟨A, B, hAB, le_trans (by exact_mod_cast hc2) hA, le_trans (by exact_mod_cast hc2) hB⟩

/-! ## Small values -/

theorem bot_twoK2Free {V : Type*} : TwoK2Free (⊥ : SimpleGraph V) :=
  fun _ _ _ _ h => h.elim

/-- The 5-cycle. -/
def C5 : SimpleGraph (Fin 5) where
  Adj i j := (i.val + 1) % 5 = j.val ∨ (j.val + 1) % 5 = i.val
  symm := ⟨fun _ _ h => Or.symm h⟩
  loopless := ⟨fun i h => by rcases h with h | h <;> omega⟩

instance : DecidableRel C5.Adj := fun i j =>
  inferInstanceAs (Decidable ((i.val + 1) % 5 = j.val ∨ (j.val + 1) % 5 = i.val))

theorem C5_twoK2Free : TwoK2Free C5 := by
  unfold TwoK2Free
  decide

theorem C5_cliqueFree : C5.CliqueFree 3 := by
  intro s hs
  obtain ⟨x, y, z, hxy, hxz, hyz, rfl⟩ := Finset.card_eq_three.mp hs.card_eq
  have key : ∀ x y z : Fin 5, C5.Adj x y → C5.Adj x z → C5.Adj y z → False := by decide
  exact key x y z (hs.1 (by simp) (by simp) hxy) (hs.1 (by simp) (by simp) hxz)
    (hs.1 (by simp) (by simp) hyz)

theorem C5_not_colorable : ¬ C5.Colorable 2 := by
  rintro ⟨c⟩
  have h01 := Fin.val_ne_of_ne (c.valid (show C5.Adj 0 1 by decide))
  have h12 := Fin.val_ne_of_ne (c.valid (show C5.Adj 1 2 by decide))
  have h23 := Fin.val_ne_of_ne (c.valid (show C5.Adj 2 3 by decide))
  have h34 := Fin.val_ne_of_ne (c.valid (show C5.Adj 3 4 by decide))
  have h40 := Fin.val_ne_of_ne (c.valid (show C5.Adj 4 0 by decide))
  have := (c 0).isLt; have := (c 1).isLt; have := (c 2).isLt; have := (c 3).isLt
  have := (c 4).isLt
  omega

theorem C5_chromaticNumber : ((3 : ℕ) : ℕ∞) ≤ C5.chromaticNumber := by
  rw [le_chromaticNumber_iff_colorable]
  intro m hm
  by_contra h
  exact C5_not_colorable (hm.mono (by omega))

/-- We have $d(2,2)=2$. The source writes $t(2,2)=2$. -/
theorem erdos_1111.variants.d_two_two : d 2 2 = 2 := by
  have hW := erdos_1111.variants.wagon 2 (by norm_num)
  apply le_antisymm
  · exact (Nat.sInf_le (s := {n | IsChromaticBound 2 2 n}) hW).trans (by decide)
  · refine le_csInf ⟨_, hW⟩ fun n hn => ?_
    by_contra hlt
    have hχ : (⊥ : SimpleGraph (Fin 1)).chromaticNumber = 1 := chromaticNumber_bot
    exact exists_anticomplete_iff.mp (hn (Fin 1) ⊥
      (by rw [hχ]; exact_mod_cast (by omega : n ≤ 1)) (cliqueFree_bot le_rfl)) bot_twoK2Free

/-- We have $d(3,2)=4$. The source writes $t(3,2)=4$. -/
theorem erdos_1111.variants.d_three_two : d 3 2 = 4 := by
  have hW := erdos_1111.variants.wagon 3 (by norm_num)
  apply le_antisymm
  · exact (Nat.sInf_le (s := {n | IsChromaticBound 3 2 n}) hW).trans (by decide)
  · refine le_csInf ⟨_, hW⟩ fun n hn => ?_
    by_contra hlt
    exact exists_anticomplete_iff.mp (hn (Fin 5) C5
      (le_trans (by exact_mod_cast (by omega : n ≤ 3)) C5_chromaticNumber) C5_cliqueFree)
      C5_twoK2Free

/-- The complement of the 7-cycle. -/
def C7c : SimpleGraph (Fin 7) where
  Adj i j := i ≠ j ∧ (i.val + 1) % 7 ≠ j.val ∧ (j.val + 1) % 7 ≠ i.val
  symm := ⟨fun _ _ h => ⟨Ne.symm h.1, h.2.2, h.2.1⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

instance : DecidableRel C7c.Adj := fun i j =>
  inferInstanceAs (Decidable (i ≠ j ∧ (i.val + 1) % 7 ≠ j.val ∧ (j.val + 1) % 7 ≠ i.val))

theorem C7c_twoK2Free : TwoK2Free C7c := by
  unfold TwoK2Free
  decide

theorem C7c_cliqueFree : C7c.CliqueFree 4 := by
  intro s hs
  obtain ⟨a, t, hat, rfl, ht⟩ := Finset.card_eq_succ.mp hs.card_eq
  obtain ⟨x, y, z, hxy, hxz, hyz, rfl⟩ := Finset.card_eq_three.mp ht
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hat
  have key : ∀ a x y z : Fin 7, C7c.Adj a x → C7c.Adj a y → C7c.Adj a z → C7c.Adj x y →
      C7c.Adj x z → C7c.Adj y z → False := by decide
  exact key a x y z (hs.1 (by simp) (by simp) hat.1) (hs.1 (by simp) (by simp) hat.2.1)
    (hs.1 (by simp) (by simp) hat.2.2) (hs.1 (by simp) (by simp) hxy)
    (hs.1 (by simp) (by simp) hxz) (hs.1 (by simp) (by simp) hyz)

theorem C7c_not_colorable : ¬ C7c.Colorable 3 := by
  rintro ⟨c⟩
  classical
  obtain ⟨k, -, hk⟩ := Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to
    (s := Finset.univ) (t := Finset.univ) (f := fun v => c v) (n := 2)
    (fun _ _ => Finset.mem_univ _) (by simp)
  obtain ⟨x, hx, y, hy, z, hz, hxy, hxz, hyz⟩ := Finset.two_lt_card.mp hk
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx hy hz
  have key : ∀ x y z : Fin 7, x ≠ y → x ≠ z → y ≠ z →
      C7c.Adj x y ∨ C7c.Adj x z ∨ C7c.Adj y z := by decide
  rcases key x y z hxy hxz hyz with h | h | h
  · exact c.valid h (hx.trans hy.symm)
  · exact c.valid h (hx.trans hz.symm)
  · exact c.valid h (hy.trans hz.symm)

theorem C7c_chromaticNumber : ((4 : ℕ) : ℕ∞) ≤ C7c.chromaticNumber := by
  rw [le_chromaticNumber_iff_colorable]
  intro m hm
  by_contra h
  exact C7c_not_colorable (hm.mono (by omega))

/-- The lower bound half of $d(4,2)=5$. -/
theorem five_le_d_four_two : 5 ≤ d 4 2 := by
  refine le_csInf ⟨_, erdos_1111.variants.wagon 4 (by norm_num)⟩ fun n hn => ?_
  by_contra hlt
  exact exists_anticomplete_iff.mp (hn (Fin 7) C7c
    (le_trans (by exact_mod_cast (by omega : n ≤ 4)) C7c_chromaticNumber) C7c_cliqueFree)
    C7c_twoK2Free

/-! ## The case `t = 0` -/

theorem d_zero_two : d 0 2 = 0 :=
  Nat.le_zero.mp (Nat.sInf_le (s := {n | IsChromaticBound 0 2 n})
    fun _ _ _ _ h => absurd h not_cliqueFree_zero)

theorem d_one_two : d 1 2 = 1 := by
  have hW := erdos_1111.variants.wagon 1 le_rfl
  apply le_antisymm
  · exact (Nat.sInf_le (s := {n | IsChromaticBound 1 2 n}) hW).trans (by decide)
  · refine le_csInf ⟨_, hW⟩ fun n hn => ?_
    by_contra hlt
    exact exists_anticomplete_iff.mp (hn (Fin 0) ⊥ (by simp [show n = 0 by omega])
      (cliqueFree_one.mpr inferInstance)) bot_twoK2Free

/-- The recurrence `d(t+1,2) ≤ d(t,2) + t` fails at `t = 0`, which is outside the problem's
range `t ≥ 1`. -/
theorem not_wagon_recurrence_zero : ¬ d (0 + 1) 2 ≤ d 0 2 + 0 := by
  simp [d_zero_two, d_one_two]

end Erdos1111
