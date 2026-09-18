import Mathlib

/-!
# Erdős Problem 917: Dirac's dense `6`-critical graphs

A graph `G` is `k`-critical if its chromatic number is `k` and deleting any edge lowers the
chromatic number. For `k ≥ 4` let `f_k(n)` be the maximum number of edges of a `k`-critical graph
on `n` vertices. Erdős Problem 917 ([erdosproblems.com/917](https://www.erdosproblems.com/917))
asks whether `f_k(n) ≫_k n²`, whether `f_6(n) ∼ n² / 4`, and whether
`f_k(n) ∼ ½ (1 - 1 / ⌊k / 3⌋) n²` for `k ≥ 6`. This file does not settle these questions. It
formalizes the classical lower-bound construction quoted on the problem page:

* **Dirac (1952).** For every `n ≥ 1` there is a `6`-critical graph on `4n + 2` vertices with
  `4n² + 8n + 3` edges, so `f_6(4n + 2) ≥ 4n² + 8n + 3`
  (`Erdos917.dirac_construction`, `Erdos917.exists_isEdgeCritical_six`, `Erdos917.f_six_ge`).
* **The `3 ∣ k` generalization.** For `r, n ≥ 1` the join of `r` copies of `C_{2n+1}` is
  `3r`-critical, with `r (2n + 1)` vertices and `r (2n + 1) + C(r, 2) (2n + 1)²` edges
  (`Erdos917.exists_isEdgeCritical_three_mul`, `Erdos917.f_three_mul_ge`). This is the
  construction behind the question `f_k(n) ∼ ½ (1 - 1 / (k / 3)) n²` for `3 ∣ k`.

`SimpleGraph.IsCriticalEdges` and `SimpleGraph.IsCriticalEdge` are copied verbatim from Google
DeepMind's formal-conjectures project
(`FormalConjecturesForMathlib/Combinatorics/SimpleGraph/Coloring/Vertex.lean`, Apache-2.0).
formal-conjectures has no file for Problem 917, so `SimpleGraph.IsEdgeCritical` (`k`-criticality)
and `Erdos917.f` (`f_k(n)`, a supremum over graphs on `Fin n`) are defined here.

## Construction and proof

Let `N = 2n + 1` and let `joinCycles r n` have vertex set `Fin r × ZMod N`. Vertices in different
copies are always adjacent, and inside a copy `k` is adjacent to `k ± 1`.

* `χ ≤ 3r`: colour `(j, k)` by `(j, c(k))`, where `c` is a proper `3`-colouring of `C_N`.
* `χ > 3r - 1`: in a proper colouring the copies use pairwise disjoint colour sets, and each odd
  cycle needs at least `3` colours (if only two colours are used then `c(k + 2) = c(k)`, and
  `2(n + 1) = 1` in `ZMod N` gives `c(k + 1) = c(k)`).
* Deleting the cycle edge `(j, k)(j, k + 1)`: colour copy `j` by `3`-colouring it with `(j, k + 1)`
  the only vertex of colour `(j, 2)`, then recolour that vertex with `(j, 0)`. Only the deleted
  edge becomes monochromatic, and colour `(j, 2)` is unused, leaving `3r - 1` colours.
* Deleting the cross edge `(a, u)(b, v)`: `3`-colour copy `a` with `(a, u)` the only vertex of
  colour `(a, 2)` and copy `b` with `(b, v)` the only vertex of colour `(b, 2)`, then recolour
  `(b, v)` with `(a, 2)`. Only the deleted edge becomes monochromatic, and colour `(b, 2)` is
  unused.
* Every vertex has degree `2 + (r - 1) N`, so by the handshake lemma there are
  `r N + C(r, 2) N²` edges.

Everything transfers to `Fin (r N)` along an equivalence. For `r = 2` this is Dirac's graph.

## References

* [Di52] Dirac, G. A., _A property of 4-chromatic graphs and some remarks on critical graphs_.
  J. London Math. Soc. (1952), 85-92.
* [Er69b] Erdős, P., _Problems and results in chromatic graph theory_. Proof Techniques in Graph
  Theory (1969), 27-35.
* [erdosproblems.com/917](https://www.erdosproblems.com/917)
-/

namespace SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

variable (G) in
/-- A set of edges is critical if deleting them reduces the chromatic number. -/
def IsCriticalEdges (edges : Set (Sym2 V)) : Prop :=
  (G.deleteEdges edges).chromaticNumber < G.chromaticNumber

variable (G) in
/-- An edge is critical if deleting it reduces the chromatic number. -/
def IsCriticalEdge (e : Sym2 V) : Prop := G.IsCriticalEdges ({e} : Set (Sym2 V))

variable (G) in
/-- `G` is `k`-critical: its chromatic number is `k` and deleting any edge of `G` lowers the
chromatic number. -/
def IsEdgeCritical (k : ℕ) : Prop :=
  G.chromaticNumber = k ∧ ∀ e ∈ G.edgeSet, G.IsCriticalEdge e

end SimpleGraph

namespace Erdos917

open Finset SimpleGraph

variable {V : Type*}

/-- `f_k(n)`: the maximum number of edges of a `k`-critical graph on `n` vertices. The set is
bounded above by `Nat.card (Sym2 (Fin n))` (see `Erdos917.ncard_le_f`). -/
noncomputable def f (k n : ℕ) : ℕ :=
  sSup {m | ∃ G : SimpleGraph (Fin n), G.IsEdgeCritical k ∧ G.edgeSet.ncard = m}

section General

variable {W : Type*}

/-- Deleting one edge lowers the chromatic number by at most one. -/
lemma colorable_succ_of_deleteEdges {G : SimpleGraph V} {x y : V} {m : ℕ}
    (h : (G.deleteEdges {s(x, y)}).Colorable m) : G.Colorable (m + 1) := by
  classical
  obtain ⟨c⟩ := h
  refine ⟨Coloring.mk (fun v => if v = x then Fin.last m else (c v).castSucc) ?_⟩
  intro u v huv
  by_cases hu : u = x <;> by_cases hv : v = x
  · subst hu; subst hv; exact (huv.ne rfl).elim
  · simp [hu, hv, Fin.ext_iff, Fin.val_last, (c v).isLt.ne']
  · simp [hu, hv, Fin.ext_iff, Fin.val_last, (c u).isLt.ne]
  · have : (G.deleteEdges {s(x, y)}).Adj u v := by
      simp [huv, hu, hv]
    simpa [hu, hv] using c.valid this

/-- `k`-criticality is invariant under graph isomorphism. -/
theorem isEdgeCritical_of_iso {G : SimpleGraph V} {H : SimpleGraph W} (φ : G ≃g H) {k : ℕ}
    (hG : G.IsEdgeCritical k) : H.IsEdgeCritical k := by
  refine ⟨(chromaticNumber_congr φ).symm.trans hG.1, fun e he => ?_⟩
  induction e using Sym2.ind with
  | h x y =>
    have hxy : G.Adj (φ.symm x) (φ.symm y) := φ.symm.map_adj_iff.mpr he
    have hlt := hG.2 s(φ.symm x, φ.symm y) hxy
    unfold SimpleGraph.IsCriticalEdge SimpleGraph.IsCriticalEdges at hlt ⊢
    rw [← chromaticNumber_congr φ]
    refine lt_of_le_of_lt (chromaticNumber_mono_of_hom ⟨φ.symm, fun {a b} hab => ?_⟩) hlt
    simp only [deleteEdges_adj, Set.mem_singleton_iff] at hab ⊢
    refine ⟨φ.symm.map_adj_iff.mpr hab.1, fun heq => hab.2 ?_⟩
    have := congrArg (Sym2.map φ) heq
    simpa using this

/-- Isomorphic graphs have the same number of edges. -/
theorem ncard_edgeSet_congr {G : SimpleGraph V} {H : SimpleGraph W} (φ : G ≃g H) :
    H.edgeSet.ncard = G.edgeSet.ncard := by
  rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq]
  exact Nat.card_congr φ.mapEdgeSet.symm

/-- Transfer a `k`-critical graph on a finite type with `m` elements to `Fin m`. -/
theorem exists_fin_of_card [Fintype V] {G : SimpleGraph V} {m k : ℕ} (hV : Fintype.card V = m)
    (hG : G.IsEdgeCritical k) :
    ∃ H : SimpleGraph (Fin m), H.IsEdgeCritical k ∧ H.edgeSet.ncard = G.edgeSet.ncard := by
  let φ := Iso.map (Fintype.equivFinOfCardEq hV) G
  exact ⟨_, isEdgeCritical_of_iso φ hG, ncard_edgeSet_congr φ⟩

/-- In a `(k + 1)`-critical graph, deleting any edge leaves chromatic number exactly `k`. -/
theorem chromaticNumber_deleteEdges_eq {G : SimpleGraph V} {k : ℕ}
    (hG : G.IsEdgeCritical (k + 1)) {e : Sym2 V} (he : e ∈ G.edgeSet) :
    (G.deleteEdges {e}).chromaticNumber = k := by
  induction e using Sym2.ind with
  | h x y =>
  have hlt := hG.2 _ he
  unfold SimpleGraph.IsCriticalEdge SimpleGraph.IsCriticalEdges at hlt
  rw [hG.1, Nat.cast_add, Nat.cast_one] at hlt
  refine le_antisymm (Order.le_of_lt_add_one hlt) ?_
  rw [le_chromaticNumber_iff_colorable]
  intro m hm
  have := (colorable_succ_of_deleteEdges hm).chromaticNumber_le
  rw [hG.1] at this
  have : k + 1 ≤ m + 1 := by exact_mod_cast this
  exact_mod_cast (by omega : k ≤ m)

end General

section Cycle

variable {n : ℕ}

/-- `1 ≠ 0` in `ZMod (2n + 1)` for `n ≥ 1`. -/
lemma one_ne_zero_zmod (hn : 1 ≤ n) : (1 : ZMod (2 * n + 1)) ≠ 0 := by
  intro h
  have h' : ((1 : ℕ) : ZMod (2 * n + 1)) = 0 := by simpa using h
  rw [ZMod.natCast_eq_zero_iff] at h'
  have := Nat.le_of_dvd one_pos h'
  omega

/-- `2 ≠ 0` in `ZMod (2n + 1)` for `n ≥ 1`. -/
lemma two_ne_zero_zmod (hn : 1 ≤ n) : (2 : ZMod (2 * n + 1)) ≠ 0 := by
  intro h
  have h' : ((2 : ℕ) : ZMod (2 * n + 1)) = 0 := by simpa using h
  rw [ZMod.natCast_eq_zero_iff] at h'
  have := Nat.le_of_dvd two_pos h'
  omega

/-- Adding `1` increments `ZMod.val` unless it wraps around to `0`. -/
lemma val_add_one_of_ne (hn : 1 ≤ n) (x : ZMod (2 * n + 1)) (h : x + 1 ≠ 0) :
    (x + 1).val = x.val + 1 := by
  have h1 : (1 : ZMod (2 * n + 1)).val = 1 := ZMod.val_one'' (by omega)
  have hx : x.val < 2 * n + 1 := ZMod.val_lt x
  rcases Nat.lt_or_ge (x.val + 1) (2 * n + 1) with hlt | hge
  · rw [ZMod.val_add_of_lt (by omega), h1]
  · exfalso
    apply h
    have hxv : x.val = 2 * n := by omega
    rw [← ZMod.natCast_zmod_val x, hxv]
    have := ZMod.natCast_self (2 * n + 1)
    push_cast at this ⊢
    exact this

/-- Parity colour (in `{0, 1} ⊆ Fin 3`) of position `k` counted from `a`. -/
def par (a k : ZMod (2 * n + 1)) : Fin 3 := ⟨(k - a).val % 2, by omega⟩

/-- Parity colours are never `2`. -/
lemma par_ne_two (a k : ZMod (2 * n + 1)) : par a k ≠ 2 := by
  simp only [par, ne_eq, Fin.ext_iff, Fin.val_two]
  omega

/-- The successor of the base point has parity colour `1`. -/
lemma par_self_add_one (hn : 1 ≤ n) (a : ZMod (2 * n + 1)) : par a (a + 1) = 1 := by
  simp only [par, add_sub_cancel_left, Fin.ext_iff, Fin.val_one,
    ZMod.val_one'' (show 2 * n + 1 ≠ 1 by omega)]

/-- The base point has parity colour `0`. -/
lemma par_self (a : ZMod (2 * n + 1)) : par a a = 0 := by
  simp [par]

/-- Parity colours alternate along the path `a, a + 1, …, a - 1`. -/
lemma par_add_one_ne (hn : 1 ≤ n) {a k : ZMod (2 * n + 1)} (h : k + 1 ≠ a) :
    par a (k + 1) ≠ par a k := by
  have h' : (k - a) + 1 ≠ 0 := fun h0 => h (by linear_combination h0)
  have hv := val_add_one_of_ne hn (k - a) h'
  simp only [par, ne_eq, Fin.ext_iff]
  rw [show k + 1 - a = k - a + 1 by ring, hv]
  omega

/-- The proper `3`-colouring of the odd cycle in which `a` is the only vertex of colour `2`. -/
def cyc3 (a k : ZMod (2 * n + 1)) : Fin 3 := if k = a then 2 else par a k

/-- Only `a` gets colour `2` under `cyc3 a`. -/
lemma cyc3_eq_two {a k : ZMod (2 * n + 1)} : cyc3 a k = 2 ↔ k = a := by
  unfold cyc3
  split_ifs with h
  · simp [h]
  · simp [h, par_ne_two]

/-- `cyc3 a` is a proper colouring of the cycle `C_{2n+1}`. -/
lemma cyc3_add_one_ne (hn : 1 ≤ n) (a k : ZMod (2 * n + 1)) : cyc3 a (k + 1) ≠ cyc3 a k := by
  have h1 := one_ne_zero_zmod hn
  by_cases hk : k = a
  · subst hk
    have : k + 1 ≠ k := fun h => h1 (by linear_combination h)
    simp only [cyc3, this, ↓reduceIte]
    exact par_ne_two _ _
  · by_cases hk1 : k + 1 = a
    · simp only [cyc3, hk, hk1, ↓reduceIte]
      exact (par_ne_two _ _).symm
    · simp only [cyc3, hk, hk1, ↓reduceIte]
      exact par_add_one_ne hn hk1

/-- An odd cycle is not `2`-colourable: any proper colouring uses at least `3` colours. -/
lemma three_le_card_image {α : Type*} [DecidableEq α] (g : ZMod (2 * n + 1) → α)
    (hg : ∀ k, g (k + 1) ≠ g k) : 3 ≤ (univ.image g).card := by
  by_contra hlt
  have h2 : ∀ k, g (k + 2) = g k := by
    intro k
    by_contra hne
    have : 2 < (univ.image g).card := by
      refine Finset.two_lt_card_iff.mpr ⟨g k, g (k + 1), g (k + 2), by simp, by simp, by simp,
        (hg k).symm, fun h => hne h.symm, fun h => hg (k + 1) ?_⟩
      rw [show k + 1 + 1 = k + 2 by ring]
      exact h.symm
    omega
  have hm : ∀ m : ℕ, g (2 * (m : ZMod (2 * n + 1))) = g 0 := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [show 2 * ((m + 1 : ℕ) : ZMod (2 * n + 1)) = 2 * (m : ZMod (2 * n + 1)) + 2 by
        push_cast; ring, h2, ih]
  have key : 2 * ((n + 1 : ℕ) : ZMod (2 * n + 1)) = 0 + 1 := by
    have := ZMod.natCast_self (2 * n + 1)
    push_cast at this ⊢
    linear_combination this
  have := hm (n + 1)
  rw [key] at this
  exact hg 0 this

end Cycle

section Join

variable {r n : ℕ}

/-- The join of `r` disjoint copies of the odd cycle `C_{2n+1}`: the vertex `(j, k)` is the
`k`-th vertex of the `j`-th cycle. Two vertices are adjacent iff they are distinct and either lie
in different copies, or are consecutive (`k' = k ± 1`) in the same copy. -/
def joinCycles (r n : ℕ) : SimpleGraph (Fin r × ZMod (2 * n + 1)) where
  Adj p q := p ≠ q ∧ (p.1 ≠ q.1 ∨ q.2 = p.2 + 1 ∨ p.2 = q.2 + 1)
  symm := ⟨fun p q h => ⟨h.1.symm, by
    rcases h.2 with h | h | h
    · exact Or.inl (Ne.symm h)
    · exact Or.inr (Or.inr h)
    · exact Or.inr (Or.inl h)⟩⟩
  loopless := ⟨fun p h => h.1 rfl⟩

/-- Adjacency in `joinCycles r n`, unfolded. -/
lemma joinCycles_adj {p q : Fin r × ZMod (2 * n + 1)} :
    (joinCycles r n).Adj p q ↔ p ≠ q ∧ (p.1 ≠ q.1 ∨ q.2 = p.2 + 1 ∨ p.2 = q.2 + 1) := Iff.rfl

instance : DecidableRel (joinCycles r n).Adj := fun _ _ =>
  inferInstanceAs (Decidable (_ ∧ _))

/-- The base colouring `(j, k) ↦ (j, cyc3 (w j) k)` with `3 r` colours. -/
def baseCol (w : Fin r → ZMod (2 * n + 1)) (p : Fin r × ZMod (2 * n + 1)) : Fin r × Fin 3 :=
  (p.1, cyc3 (w p.1) p.2)

/-- `baseCol w` uses colour `(j, 2)` exactly on `(j, w j)`. -/
lemma baseCol_eq_two {w : Fin r → ZMod (2 * n + 1)} {p : Fin r × ZMod (2 * n + 1)} {j : Fin r} :
    baseCol w p = (j, 2) ↔ p = (j, w j) := by
  obtain ⟨i, k⟩ := p
  simp only [baseCol, Prod.mk.injEq]
  constructor
  · rintro ⟨rfl, h⟩
    exact ⟨rfl, cyc3_eq_two.mp h⟩
  · rintro ⟨rfl, h⟩
    exact ⟨rfl, cyc3_eq_two.mpr h⟩

/-- `baseCol w` is proper on every cycle edge. -/
lemma baseCol_add_one_ne (hn : 1 ≤ n) (w : Fin r → ZMod (2 * n + 1)) (j : Fin r)
    (k : ZMod (2 * n + 1)) : baseCol w (j, k + 1) ≠ baseCol w (j, k) := by
  simp only [baseCol, ne_eq, Prod.mk.injEq, true_and]
  exact cyc3_add_one_ne hn _ _

/-- A criterion for a colouring of `joinCycles r n` minus the edge `e` to be proper. -/
lemma deleteEdges_valid_of (e : Sym2 (Fin r × ZMod (2 * n + 1))) {C : Type*}
    (c : Fin r × ZMod (2 * n + 1) → C)
    (h1 : ∀ j k, c (j, k + 1) = c (j, k) → s((j, k + 1), (j, k)) = e)
    (h2 : ∀ i j k l, i ≠ j → c (i, k) = c (j, l) → s((i, k), (j, l)) = e) :
    ∀ p q, ((joinCycles r n).deleteEdges {e}).Adj p q → c p ≠ c q := by
  rintro ⟨i, k⟩ ⟨j, l⟩ hadj heq
  simp only [deleteEdges_adj, Set.mem_singleton_iff, joinCycles_adj] at hadj
  obtain ⟨⟨-, h⟩, hnd⟩ := hadj
  by_cases hij : i = j
  · subst hij
    simp only [ne_eq, not_true_eq_false, false_or] at h
    rcases h with rfl | rfl
    · exact hnd (Sym2.eq_swap.trans (h1 i k heq.symm))
    · exact hnd (h1 i l heq)
  · exact hnd (h2 i j k l hij heq)

/-- A proper colouring into `Fin r × Fin 3` that misses one colour shows
`(3r - 1)`-colourability. -/
lemma colorable_of_avoid {G : SimpleGraph (Fin r × ZMod (2 * n + 1))}
    (c : Fin r × ZMod (2 * n + 1) → Fin r × Fin 3) (hc : ∀ p q, G.Adj p q → c p ≠ c q)
    (c₀ : Fin r × Fin 3) (havoid : ∀ p, c p ≠ c₀) : G.Colorable (3 * r - 1) := by
  let C : G.Coloring {z : Fin r × Fin 3 // z ≠ c₀} :=
    Coloring.mk (fun p => ⟨c p, havoid p⟩) (fun {p q} h heq => hc p q h (congrArg Subtype.val heq))
  have := C.colorable
  simpa [Fintype.card_subtype_compl, mul_comm] using this

/-- `joinCycles r n` is `3r`-colourable. -/
lemma colorable_joinCycles (hn : 1 ≤ n) : (joinCycles r n).Colorable (3 * r) := by
  let C : (joinCycles r n).Coloring (Fin r × Fin 3) :=
    Coloring.mk (baseCol 0) (fun {p q} h heq => by
      obtain ⟨i, k⟩ := p
      obtain ⟨j, l⟩ := q
      obtain ⟨-, h⟩ := h
      simp only [baseCol, Prod.mk.injEq] at heq
      obtain ⟨rfl, h3⟩ := heq
      rcases h with h | rfl | rfl
      · exact h rfl
      · exact cyc3_add_one_ne hn _ k h3.symm
      · exact cyc3_add_one_ne hn _ l h3)
  simpa [mul_comm] using C.colorable

/-- `joinCycles r n` is not `(3r - 1)`-colourable. -/
lemma not_colorable_joinCycles (hr : 1 ≤ r) (hn : 1 ≤ n) :
    ¬ (joinCycles r n).Colorable (3 * r - 1) := by
  rintro ⟨c⟩
  let S : Fin r → Finset (Fin (3 * r - 1)) := fun j => univ.image fun k => c (j, k)
  have hS : ∀ j, 3 ≤ (S j).card := fun j =>
    three_le_card_image _ fun k h => c.valid (show (joinCycles r n).Adj (j, k + 1) (j, k) from
      ⟨fun h' => by
        have := congrArg Prod.snd h'
        exact one_ne_zero_zmod hn (by simpa using this), Or.inr (Or.inr rfl)⟩) h
  have hdisj : ((univ : Finset (Fin r)) : Set (Fin r)).PairwiseDisjoint S := by
    intro i _ j _ hij
    rw [Function.onFun, Finset.disjoint_left]
    intro x hx hx'
    simp only [S, mem_image, mem_univ, true_and] at hx hx'
    obtain ⟨k, rfl⟩ := hx
    obtain ⟨l, hl⟩ := hx'
    exact c.valid (show (joinCycles r n).Adj (j, l) (i, k) from
      ⟨fun h' => hij (congrArg Prod.fst h').symm, Or.inl (Ne.symm hij)⟩) hl
  have hcard := Finset.card_biUnion hdisj
  have hle : (univ.biUnion S).card ≤ 3 * r - 1 := by
    simpa using card_le_univ (univ.biUnion S)
  have hsum : ∑ _j : Fin r, 3 ≤ ∑ j, (S j).card := Finset.sum_le_sum fun j _ => hS j
  simp only [sum_const, card_univ, Fintype.card_fin, smul_eq_mul] at hsum
  omega

/-- Deleting a cycle edge `(j₀, k₀ + 1) (j₀, k₀)` leaves a `(3r - 1)`-colourable graph: recolour
the unique vertex of colour `(j₀, 2)`, namely `(j₀, k₀ + 1)`, with `(j₀, 0)`. -/
lemma colorable_deleteEdges_cycle (hn : 1 ≤ n) (j₀ : Fin r) (k₀ : ZMod (2 * n + 1)) :
    ((joinCycles r n).deleteEdges {s((j₀, k₀ + 1), (j₀, k₀))}).Colorable (3 * r - 1) := by
  classical
  let w : Fin r → ZMod (2 * n + 1) := fun _ => k₀ + 1
  let c : Fin r × ZMod (2 * n + 1) → Fin r × Fin 3 := fun p =>
    if p = (j₀, k₀ + 1) then (j₀, 0) else baseCol w p
  have hfst : ∀ p, (c p).1 = p.1 := by
    intro p
    by_cases hp : p = (j₀, k₀ + 1)
    · simp [c, hp]
    · simp [c, hp, baseCol]
  refine colorable_of_avoid c (deleteEdges_valid_of _ c (fun j k h => ?_) (fun i j k l hij h => ?_))
    (j₀, 2) (fun p hp => ?_)
  · by_cases h1 : (j, k + 1) = (j₀, k₀ + 1)
    · simp only [Prod.mk.injEq, add_left_inj] at h1
      obtain ⟨rfl, rfl⟩ := h1
      rfl
    · by_cases h0 : (j, k) = (j₀, k₀ + 1)
      · exfalso
        simp only [Prod.mk.injEq] at h0
        obtain ⟨rfl, rfl⟩ := h0
        simp only [c, h1, ↓reduceIte, baseCol, w] at h
        have hne : k₀ + 1 + 1 ≠ k₀ + 1 := fun h' => one_ne_zero_zmod hn (by linear_combination h')
        simp only [cyc3, hne, ↓reduceIte, par_self_add_one hn] at h
        simp [Prod.ext_iff] at h
      · simp only [c, h1, h0, ↓reduceIte] at h
        exact absurd h (baseCol_add_one_ne hn _ _ _)
  · exact absurd (by simpa [hfst] using congrArg Prod.fst h) hij
  · by_cases hp' : p = (j₀, k₀ + 1)
    · simp [c, hp', Prod.ext_iff] at hp
    · simp only [c, hp', ↓reduceIte, baseCol_eq_two] at hp
      exact hp' hp

/-- Deleting a cross edge `(a, u) (b, v)` (`a ≠ b`) leaves a `(3r - 1)`-colourable graph: colour
part `a` with `(a, cyc3 u ·)`, part `b` with `(b, cyc3 v ·)`, and recolour `(b, v)` with `(a, 2)`,
which is used in part `a` only by `(a, u)`. -/
lemma colorable_deleteEdges_cross (hn : 1 ≤ n) {a b : Fin r} (hab : a ≠ b)
    (u v : ZMod (2 * n + 1)) :
    ((joinCycles r n).deleteEdges {s((a, u), (b, v))}).Colorable (3 * r - 1) := by
  classical
  let w : Fin r → ZMod (2 * n + 1) := fun j => if j = a then u else v
  have hwa : w a = u := by simp [w]
  have hwb : w b = v := by simp [w, hab.symm]
  let c : Fin r × ZMod (2 * n + 1) → Fin r × Fin 3 := fun p =>
    if p = (b, v) then (a, 2) else baseCol w p
  have hc : ∀ p, p ≠ (b, v) → c p = baseCol w p := fun p hp => by simp [c, hp]
  have hcbv : c (b, v) = (a, 2) := by simp [c]
  refine colorable_of_avoid c (deleteEdges_valid_of _ c (fun j k h => ?_) (fun i j k l hij h => ?_))
    (b, 2) (fun p hp => ?_)
  · exfalso
    have hne : k + 1 ≠ k := fun h' => one_ne_zero_zmod hn (by linear_combination h')
    by_cases h1 : (j, k + 1) = (b, v)
    · rw [h1, hcbv, hc (j, k) (fun h' => hne (by simp_all [Prod.ext_iff]))] at h
      simp only [baseCol, Prod.mk.injEq] at h
      exact hab (h.1.trans (by simp_all [Prod.ext_iff]))
    · by_cases h0 : (j, k) = (b, v)
      · rw [h0, hcbv, hc _ h1] at h
        simp only [baseCol, Prod.mk.injEq] at h
        exact hab (h.1.symm.trans (by simp_all [Prod.ext_iff]))
      · rw [hc _ h0, hc _ h1] at h
        exact baseCol_add_one_ne hn _ _ _ h
  · by_cases h1 : (i, k) = (b, v)
    · rw [h1, hcbv] at h
      have hjl : (j, l) ≠ (b, v) := fun h' => hij (by simp_all [Prod.ext_iff])
      rw [hc _ hjl, eq_comm, baseCol_eq_two, hwa] at h
      rw [h1, h, Sym2.eq_swap]
    · by_cases h0 : (j, l) = (b, v)
      · rw [h0, hcbv, hc _ h1, baseCol_eq_two, hwa] at h
        rw [h0, h]
      · rw [hc _ h0, hc _ h1] at h
        exact absurd (congrArg Prod.fst h) hij
  · by_cases hp' : p = (b, v)
    · rw [hp', hcbv] at hp
      simp [Prod.ext_iff, hab] at hp
    · rw [hc _ hp', baseCol_eq_two, hwb] at hp
      exact hp' hp

/-- The join of `r ≥ 1` copies of `C_{2n+1}` (`n ≥ 1`) is `3r`-critical. -/
theorem isEdgeCritical_joinCycles (hr : 1 ≤ r) (hn : 1 ≤ n) :
    (joinCycles r n).IsEdgeCritical (3 * r) := by
  have hχ : (joinCycles r n).chromaticNumber = (3 * r : ℕ) := by
    have h := (chromaticNumber_eq_iff_colorable_not_colorable (G := joinCycles r n)
      (n := 3 * r - 1)).mpr ⟨by
        rw [show 3 * r - 1 + 1 = 3 * r by omega]; exact colorable_joinCycles hn,
        not_colorable_joinCycles hr hn⟩
    rw [h]
    norm_cast
    omega
  refine ⟨hχ, fun e he => ?_⟩
  induction e using Sym2.ind with
  | h p q =>
  obtain ⟨i, k⟩ := p
  obtain ⟨j, l⟩ := q
  obtain ⟨-, h⟩ := he
  have key : ((joinCycles r n).deleteEdges {s((i, k), (j, l))}).Colorable (3 * r - 1) := by
    by_cases hij : i = j
    · subst hij
      simp only [ne_eq, not_true_eq_false, false_or] at h
      rcases h with rfl | rfl
      · rw [Sym2.eq_swap]
        exact colorable_deleteEdges_cycle hn i k
      · exact colorable_deleteEdges_cycle hn i l
    · exact colorable_deleteEdges_cross hn hij k l
  unfold SimpleGraph.IsCriticalEdge SimpleGraph.IsCriticalEdges
  rw [hχ]
  refine key.chromaticNumber_le.trans_lt ?_
  norm_cast
  omega

/-- Every vertex of `joinCycles r n` has degree `2 + (r - 1)(2n + 1)`. -/
lemma degree_joinCycles (hn : 1 ≤ n) (p : Fin r × ZMod (2 * n + 1)) :
    (joinCycles r n).degree p = 2 + (r - 1) * (2 * n + 1) := by
  rw [← card_neighborFinset_eq_degree, neighborFinset_eq_filter, Finset.card_filter,
    Fintype.sum_prod_type, Fintype.sum_eq_add_sum_compl p.1]
  have hsame : ∑ l : ZMod (2 * n + 1), (if (joinCycles r n).Adj p (p.1, l) then 1 else 0) = 2 := by
    rw [Finset.sum_boole, Nat.cast_id]
    have h1 := one_ne_zero_zmod hn
    have h2 := two_ne_zero_zmod hn
    have hfil : ({l | (joinCycles r n).Adj p (p.1, l)} : Finset _) = {p.2 + 1, p.2 - 1} := by
      ext l
      simp only [joinCycles_adj, mem_filter, mem_univ, true_and, mem_insert, mem_singleton,
        ne_eq, not_true_eq_false, false_or, Prod.ext_iff]
      constructor
      · rintro ⟨-, h | h⟩
        · exact Or.inl h
        · exact Or.inr (by linear_combination -h)
      · rintro (h | h)
        · refine ⟨fun h' => h1 ?_, Or.inl h⟩
          linear_combination -h - h'
        · refine ⟨fun h' => h1 ?_, Or.inr (by linear_combination -h)⟩
          linear_combination h + h'
    rw [hfil, card_pair]
    intro h
    exact h2 (by linear_combination h)
  have hother : ∀ j ∈ ({p.1}ᶜ : Finset (Fin r)),
      ∑ l : ZMod (2 * n + 1), (if (joinCycles r n).Adj p (j, l) then 1 else 0) = 2 * n + 1 := by
    intro j hj
    simp only [mem_compl, mem_singleton] at hj
    have : ∀ l : ZMod (2 * n + 1), (joinCycles r n).Adj p (j, l) := fun l =>
      ⟨fun h => hj (congrArg Prod.fst h).symm, Or.inl (Ne.symm hj)⟩
    simp [this, ZMod.card]
  rw [hsame, Finset.sum_congr rfl hother, sum_const, card_compl, card_singleton, Fintype.card_fin,
    smul_eq_mul]

/-- `joinCycles r n` has `r (2n + 1) + C(r, 2) (2n + 1)²` edges. -/
theorem ncard_edgeSet_joinCycles (hn : 1 ≤ n) :
    (joinCycles r n).edgeSet.ncard = r * (2 * n + 1) + r.choose 2 * (2 * n + 1) ^ 2 := by
  rw [← coe_edgeFinset, Set.ncard_coe_finset]
  have h := sum_degrees_eq_twice_card_edges (G := joinCycles r n)
  simp only [degree_joinCycles hn, sum_const, card_univ, Fintype.card_prod, Fintype.card_fin,
    ZMod.card, smul_eq_mul] at h
  have hc : 2 * r.choose 2 = r * (r - 1) := by
    rw [Nat.choose_two_right, Nat.mul_div_cancel' (Nat.even_mul_pred_self r).two_dvd]
  have key : r * (2 * n + 1) * (2 + (r - 1) * (2 * n + 1)) =
      2 * (r * (2 * n + 1) + r.choose 2 * (2 * n + 1) ^ 2) := by
    rw [mul_add 2, ← mul_assoc 2 (r.choose 2), hc]
    ring
  exact Nat.eq_of_mul_eq_mul_left two_pos (h.symm.trans key)

end Join

section Main

/-- Any `k`-critical graph on `Fin m` has at most `f k m` edges. In particular the set in the
definition of `f` is bounded above. -/
lemma ncard_le_f {k m : ℕ} {G : SimpleGraph (Fin m)} (hG : G.IsEdgeCritical k) :
    G.edgeSet.ncard ≤ f k m := by
  refine le_csSup ⟨Nat.card (Sym2 (Fin m)), ?_⟩ ⟨G, hG, rfl⟩
  rintro _ ⟨H, -, rfl⟩
  exact (Set.ncard_le_ncard (Set.subset_univ _)).trans_eq (Set.ncard_univ _)

/-- **The `3 ∣ k` construction.** For `r, n ≥ 1` there is a `3r`-critical graph on `r (2n + 1)`
vertices with `r (2n + 1) + C(r, 2) (2n + 1)²` edges (the join of `r` copies of `C_{2n+1}`). -/
theorem exists_isEdgeCritical_three_mul (r n : ℕ) (hr : 1 ≤ r) (hn : 1 ≤ n) :
    ∃ G : SimpleGraph (Fin (r * (2 * n + 1))), G.IsEdgeCritical (3 * r) ∧
      G.edgeSet.ncard = r * (2 * n + 1) + r.choose 2 * (2 * n + 1) ^ 2 := by
  obtain ⟨H, hH, hcard⟩ := exists_fin_of_card (m := r * (2 * n + 1))
    (by simp [ZMod.card]) (isEdgeCritical_joinCycles hr hn)
  exact ⟨H, hH, hcard.trans (ncard_edgeSet_joinCycles hn)⟩

/-- `f_{3r}(r (2n + 1)) ≥ r (2n + 1) + C(r, 2) (2n + 1)²` for `r, n ≥ 1`. -/
theorem f_three_mul_ge (r n : ℕ) (hr : 1 ≤ r) (hn : 1 ≤ n) :
    r * (2 * n + 1) + r.choose 2 * (2 * n + 1) ^ 2 ≤ f (3 * r) (r * (2 * n + 1)) := by
  obtain ⟨G, hG, hcard⟩ := exists_isEdgeCritical_three_mul r n hr hn
  exact hcard ▸ ncard_le_f hG

/-- **Dirac (1952).** For every `n ≥ 1` there is a `6`-critical graph on `4n + 2` vertices with
`4n² + 8n + 3` edges. -/
theorem exists_isEdgeCritical_six (n : ℕ) (hn : 1 ≤ n) :
    ∃ G : SimpleGraph (Fin (4 * n + 2)), G.IsEdgeCritical 6 ∧
      G.edgeSet.ncard = 4 * n ^ 2 + 8 * n + 3 := by
  obtain ⟨H, hH, hcard⟩ := exists_fin_of_card (m := 4 * n + 2)
    (by simp [ZMod.card]; ring) (isEdgeCritical_joinCycles (r := 2) (by norm_num) hn)
  refine ⟨H, hH, ?_⟩
  rw [hcard, ncard_edgeSet_joinCycles hn]
  simp
  ring

/-- **Dirac (1952), explicit form.** For every `n ≥ 1` there is a graph on `4n + 2` vertices with
chromatic number `6` and exactly `4n² + 8n + 3` edges, such that deleting any single edge leaves
chromatic number exactly `5`. -/
theorem dirac_construction (n : ℕ) (hn : 1 ≤ n) :
    ∃ G : SimpleGraph (Fin (4 * n + 2)), G.chromaticNumber = 6 ∧
      (∀ e ∈ G.edgeSet, (G.deleteEdges {e}).chromaticNumber = 5) ∧
      G.edgeSet.ncard = 4 * n ^ 2 + 8 * n + 3 := by
  obtain ⟨G, hG, hcard⟩ := exists_isEdgeCritical_six n hn
  exact ⟨G, hG.1, fun e he => chromaticNumber_deleteEdges_eq (k := 5) hG he, hcard⟩

/-- **Dirac (1952).** `f_6(4n + 2) ≥ 4n² + 8n + 3` for every `n ≥ 1`. -/
theorem f_six_ge (n : ℕ) (hn : 1 ≤ n) : 4 * n ^ 2 + 8 * n + 3 ≤ f 6 (4 * n + 2) := by
  obtain ⟨G, hG, hcard⟩ := exists_isEdgeCritical_six n hn
  exact hcard ▸ ncard_le_f hG

end Main

end Erdos917
