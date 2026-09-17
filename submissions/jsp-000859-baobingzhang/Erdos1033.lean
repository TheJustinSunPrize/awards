import Mathlib

/-!
# Erdős Problem 1033: the conjectured bound `h(n) ≥ (2(√3 - 1) - o(1)) n` fails

Erdős Problem 1033 ([Er82e, p.71], [Er93, p.344], https://www.erdosproblems.com/1033), a
conjecture of Bollobás and Erdős, reads:

> Let `h(n)` be such that every graph on `n` vertices with `> n^2/4` many edges contains a
> triangle whose vertices have degrees summing to at least `h(n)`. Estimate `h(n)`. In particular,
> is it true that `h(n) ≥ (2(√3 - 1) - o(1)) n`?

The page records `21/16 n ≤ h(n) ≤ 2(√3 - 1) n + O(1)` (Fan [Fa88]; Erdős–Laskar [ErLa85]).
This file proves that the answer to the "in particular" question is **no**. It does not settle
the question "estimate `h(n)`".

## Credit

The counterexample is a blow-up of the butterfly graph (two triangles `abc` and `ade` sharing
the vertex `a`). It was posted on the erdosproblems.com forum thread for Problem 1033 by user
rickyc on 27 June 2026 as a construction produced by GPT-5.5 Pro, giving the constant
`≈ 1.46393`. Johan Land confirmed it on 26 July 2026. Wouter CvB optimized the densities of the
same blow-up to `1.463877…` on 27 July 2026. The exact integer parameters below (part sizes and
circulant densities `7/16` and `7/23`, with ratio `14727/10060 ≈ 1.463917`) are a rational
approximation of Wouter CvB's optimized densities. They were found by a small computer search for
this formalization, so that every degree is an exact integer. The definition of `h` follows the
statement-only proposal in formal-conjectures PR #5885, which was not merged.

## Definitions and faithfulness

* `h n` is the supremum of the real numbers `x` such that every `G : SimpleGraph (Fin n)` with
  `n^2/4 < |E(G)|` has a 3-clique `T` with `x ≤ ∑_{v ∈ T} deg_G v`. Edges are counted by
  `G.edgeSet.ncard`, and degrees are degrees in `G`.
* `h` is the extremal function of the problem, and not an artifact of `sSup` conventions.
  `h_spec` shows that `h n` itself has the defining property for every `n`: every graph with
  more than `n^2/4` edges has a triangle with degree sum `≥ h n`. This uses Mantel's theorem
  (Mathlib's Turán bound). `le_h` shows that for `n ≥ 3` every `x` with the property satisfies
  `x ≤ h n`. So for `n ≥ 3`, `h n` is the largest admissible value.
* "`h(n) ≥ (2(√3 - 1) - o(1)) n`" is formalized as the existence of `o : ℕ → ℝ` with
  `o =o[atTop] 1` and `(2(√3 - 1) - o n) n ≤ h n` for all sufficiently large `n`.
  `erdos_1033` proves its negation. `erdos_1033_eps` negates the equivalent form
  `∀ ε > 0, ∀ᶠ n, (2(√3 - 1) - ε) n ≤ h n`. Both negated statements only require all
  sufficiently large `n`, so they imply the negations of the versions for all `n`.
* `erdos_1033_of_bound` gives the same negation for every function `f` with the defining
  property. It therefore covers the reading "any valid `h`" as well as "the optimal `h`".
  `h_spec` shows that such `f` exist (for example `h`), so this hypothesis can be satisfied.

## Construction (`butterfly s`, on `10060 s` vertices)

Independent sets `a, b, c, d, e` of sizes `4288 s, 2476 s, 720 s, 1288 s, 1288 s`.
`a = Fin 16 × Fin (268 s)`, `c = Fin 16 × Fin (45 s)` and `d = e = Fin 23 × Fin (56 s)` are split
into blocks.

* `ab`, `bc`, `ad`, `ae` are complete bipartite.
* `(i, _) ∈ a` is joined to `(j, _) ∈ c` iff `(j - i) mod 16 < 7`, and `(i, _) ∈ d` is joined to
  `(j, _) ∈ e` iff `(j - i) mod 23 < 7`. So every vertex has exactly `7/16`, respectively `7/23`,
  of the other side as neighbours.
* There are no other edges.

Degrees (`degree_butterfly`): `a: 5367 s`, `b: 5008 s`, `c: 4352 s`, `d, e: 4680 s`. They are
computed by explicit counting over the sum type (`sum_circ16`, `sum_circ23`). The only
triangles are of type `abc` or `ade` (`triangle_sum`). Both have degree sum `14727 s`. The
handshake lemma gives `|E| = 25301312 s² > 25300900 s² = (10060 s)²/4`. Finally
`14727/10060 < 2(√3 - 1)`, since `34847² = 1214313409 < 1214443200 = 3 · 20120²` (`ratio_lt`).

## Main results

* `Erdos1033.erdos_1033`: `¬ ∃ o, o =o[atTop] 1 ∧ ∀ᶠ n in atTop, (2(√3 - 1) - o n) n ≤ h n`.
* `Erdos1033.erdos_1033_eps`: `¬ ∀ ε > 0, ∀ᶠ n in atTop, (2(√3 - 1) - ε) n ≤ h n`.
* `Erdos1033.erdos_1033_of_bound`: the same negation for any `f` with the defining property.
* `Erdos1033.exists_graph`: for `s ≥ 1` there is a graph on `Fin (10060 s)` with more than
  `(10060 s)²/4` edges that contains a triangle, and in which every triangle has degree sum
  exactly `14727 s`.
* `Erdos1033.h_le`: `h (10060 s) ≤ 14727 s` for `s ≥ 1`.
* `Erdos1033.h_spec`, `Erdos1033.le_h`: `h n` is the optimal value in the problem's sense.

## References

* [Er82e] Erdős, P., _Some of my favourite problems which recently have been solved_ (1982).
* [Er93] Erdős, P., _Some of my favorite solved and unsolved problems in graph theory_ (1993).
* [ErLa85] Erdős, P. and Laskar, R., _A note on the size of a chordal subgraph_ (1985).
* [Fa88] Fan, G., _Degree sum for a triangle in a graph_, J. Graph Theory 12 (1988).
* erdosproblems.com forum, thread 1033 (rickyc 2026-06-27; Johan Land 2026-07-26;
  Wouter CvB 2026-07-27).
-/

open Finset Filter

namespace Erdos1033

/-! ## The problem -/

open scoped Classical in
/-- `h n`: the largest real `x` such that every graph on `n` vertices with more than `n^2/4`
edges contains a triangle whose vertex degrees sum to at least `x`. If no graph on `n` vertices
has more than `n^2/4` edges (`n ≤ 2`), this is `sSup univ = 0`. -/
noncomputable def h (n : ℕ) : ℝ :=
  sSup {x : ℝ | ∀ G : SimpleGraph (Fin n),
    (n : ℝ) ^ 2 / 4 < (G.edgeSet.ncard : ℝ) →
      ∃ T : Finset (Fin n), G.IsNClique 3 T ∧ x ≤ (∑ v ∈ T, G.degree v : ℝ)}

/-! ## The construction -/

/-- The vertex set of `butterfly s`: the parts `a ⊕ b ⊕ c ⊕ d ⊕ e`. -/
abbrev Vert (s : ℕ) : Type :=
  (Fin 16 × Fin (268 * s)) ⊕ Fin (2476 * s) ⊕ (Fin 16 × Fin (45 * s)) ⊕
    (Fin 23 × Fin (56 * s)) ⊕ (Fin 23 × Fin (56 * s))

/-- Adjacency of `butterfly s`: complete between `ab`, `bc`, `ad`, `ae`; circulant between `ac`
(block offset `< 7` modulo `16`) and `de` (block offset `< 7` modulo `23`); nothing else. -/
def adjB {s : ℕ} : Vert s → Vert s → Bool
  | .inl _, .inr (.inl _) => true
  | .inr (.inl _), .inl _ => true
  | .inr (.inl _), .inr (.inr (.inl _)) => true
  | .inr (.inr (.inl _)), .inr (.inl _) => true
  | .inl (i, _), .inr (.inr (.inl (j, _))) => decide ((j - i).val < 7)
  | .inr (.inr (.inl (j, _))), .inl (i, _) => decide ((j - i).val < 7)
  | .inl _, .inr (.inr (.inr (.inl _))) => true
  | .inr (.inr (.inr (.inl _))), .inl _ => true
  | .inl _, .inr (.inr (.inr (.inr _))) => true
  | .inr (.inr (.inr (.inr _))), .inl _ => true
  | .inr (.inr (.inr (.inl (i, _)))), .inr (.inr (.inr (.inr (j, _)))) => decide ((j - i).val < 7)
  | .inr (.inr (.inr (.inr (j, _)))), .inr (.inr (.inr (.inl (i, _)))) => decide ((j - i).val < 7)
  | _, _ => false

theorem adjB_symm {s : ℕ} (v w : Vert s) : adjB v w = adjB w v := by
  rcases v with ⟨i, t⟩ | b | ⟨i, t⟩ | ⟨i, t⟩ | ⟨i, t⟩ <;>
    rcases w with ⟨j, u⟩ | b' | ⟨j, u⟩ | ⟨j, u⟩ | ⟨j, u⟩ <;> rfl

theorem adjB_irrefl {s : ℕ} (v : Vert s) : adjB v v = false := by
  rcases v with ⟨i, t⟩ | b | ⟨i, t⟩ | ⟨i, t⟩ | ⟨i, t⟩ <;> rfl

/-- The blown-up butterfly graph on `10060 s` vertices. -/
def butterfly (s : ℕ) : SimpleGraph (Vert s) where
  Adj v w := adjB v w = true
  symm := ⟨fun v w h => by rw [adjB_symm]; exact h⟩
  loopless := ⟨fun v h => by rw [adjB_irrefl] at h; exact Bool.false_ne_true h⟩

instance (s : ℕ) : DecidableRel (butterfly s).Adj := fun v w =>
  inferInstanceAs (Decidable (adjB v w = true))

theorem card_Vert (s : ℕ) : Fintype.card (Vert s) = 10060 * s := by
  simp [Fintype.card_sum, Fintype.card_prod]; ring

/-! ### Circulant counts -/

theorem circ16 (i : Fin 16) : #(univ.filter fun j : Fin 16 => (j - i).val < 7) = 7 := by
  revert i; decide

theorem circ16' (j : Fin 16) : #(univ.filter fun i : Fin 16 => (j - i).val < 7) = 7 := by
  revert j; decide

theorem circ23 (i : Fin 23) : #(univ.filter fun j : Fin 23 => (j - i).val < 7) = 7 := by
  revert i; decide

theorem circ23' (j : Fin 23) : #(univ.filter fun i : Fin 23 => (j - i).val < 7) = 7 := by
  revert j; decide

theorem sum_circ16 (i : Fin 16) (m : ℕ) :
    (∑ j : Fin 16, ∑ _t : Fin m, if (j - i).val < 7 then 1 else 0 : ℕ) = 7 * m := by
  rw [Finset.sum_comm]
  simp only [Finset.sum_boole, circ16, Nat.cast_id, sum_const, card_univ, Fintype.card_fin,
    smul_eq_mul, mul_comm]

theorem sum_circ16' (j : Fin 16) (m : ℕ) :
    (∑ i : Fin 16, ∑ _t : Fin m, if (j - i).val < 7 then 1 else 0 : ℕ) = 7 * m := by
  rw [Finset.sum_comm]
  simp only [Finset.sum_boole, circ16', Nat.cast_id, sum_const, card_univ, Fintype.card_fin,
    smul_eq_mul, mul_comm]

theorem sum_circ23 (i : Fin 23) (m : ℕ) :
    (∑ j : Fin 23, ∑ _t : Fin m, if (j - i).val < 7 then 1 else 0 : ℕ) = 7 * m := by
  rw [Finset.sum_comm]
  simp only [Finset.sum_boole, circ23, Nat.cast_id, sum_const, card_univ, Fintype.card_fin,
    smul_eq_mul, mul_comm]

theorem sum_circ23' (j : Fin 23) (m : ℕ) :
    (∑ i : Fin 23, ∑ _t : Fin m, if (j - i).val < 7 then 1 else 0 : ℕ) = 7 * m := by
  rw [Finset.sum_comm]
  simp only [Finset.sum_boole, circ23', Nat.cast_id, sum_const, card_univ, Fintype.card_fin,
    smul_eq_mul, mul_comm]

/-! ### Degrees, triangles and edges -/

/-- The degree of a vertex of `butterfly s`, which depends only on its part. -/
def partDegree {s : ℕ} : Vert s → ℕ
  | .inl _ => 5367 * s
  | .inr (.inl _) => 5008 * s
  | .inr (.inr (.inl _)) => 4352 * s
  | .inr (.inr (.inr (.inl _))) => 4680 * s
  | .inr (.inr (.inr (.inr _))) => 4680 * s

theorem degree_butterfly (s : ℕ) (v : Vert s) : (butterfly s).degree v = partDegree v := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree, SimpleGraph.neighborFinset_eq_filter,
    Finset.card_filter]
  rcases v with ⟨i, t⟩ | b | ⟨i, t⟩ | ⟨i, t⟩ | ⟨i, t⟩
  all_goals
    simp only [Fintype.sum_sum_type, Fintype.sum_prod_type, butterfly, adjB, partDegree,
      decide_eq_true_eq, sum_circ16, sum_circ16', sum_circ23, sum_circ23', Bool.false_eq_true,
      ite_true, ite_false, Finset.sum_const_zero, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, Fintype.card_prod, smul_eq_mul, mul_one, add_zero, zero_add]
  all_goals ring

/-- Every triangle of `butterfly s` has type `abc` or `ade`, so its degree sum is `14727 s`. -/
theorem triangle_sum {s : ℕ} (x y z : Vert s) (hxy : (butterfly s).Adj x y)
    (hxz : (butterfly s).Adj x z) (hyz : (butterfly s).Adj y z) :
    partDegree x + partDegree y + partDegree z = 14727 * s := by
  rcases x with ⟨i, t⟩ | b | ⟨i, t⟩ | ⟨i, t⟩ | ⟨i, t⟩ <;>
    rcases y with ⟨j, u⟩ | b' | ⟨j, u⟩ | ⟨j, u⟩ | ⟨j, u⟩ <;>
    rcases z with ⟨k, w⟩ | b'' | ⟨k, w⟩ | ⟨k, w⟩ | ⟨k, w⟩ <;>
    simp only [butterfly, adjB, Bool.false_eq_true] at hxy hxz hyz <;>
    simp only [partDegree] <;> ring

theorem sum_partDegree (s : ℕ) : ∑ v : Vert s, partDegree v = 50602624 * s ^ 2 := by
  simp only [Fintype.sum_sum_type, partDegree, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, Fintype.card_prod, smul_eq_mul]
  ring

theorem card_edgeFinset_butterfly (s : ℕ) : #(butterfly s).edgeFinset = 25301312 * s ^ 2 := by
  have h := (butterfly s).sum_degrees_eq_twice_card_edges
  simp only [degree_butterfly, sum_partDegree] at h
  omega

/-! ### The counterexample on `Fin (10060 s)` -/

open scoped Classical in
/-- For `s ≥ 1` there is a graph on `10060 s` vertices with more than `(10060 s)^2/4` edges that
contains a triangle, and in which every triangle has degree sum exactly `14727 s`. -/
theorem exists_graph (s : ℕ) (hs : 0 < s) :
    ∃ H : SimpleGraph (Fin (10060 * s)),
      ((10060 * s : ℕ) : ℝ) ^ 2 / 4 < (H.edgeSet.ncard : ℝ) ∧
      (∃ T : Finset (Fin (10060 * s)), H.IsNClique 3 T) ∧
      ∀ T : Finset (Fin (10060 * s)), H.IsNClique 3 T → ∑ v ∈ T, H.degree v = 14727 * s := by
  set H := (butterfly s).overFin (card_Vert s)
  let e : butterfly s ≃g H := (butterfly s).overFinIso (card_Vert s)
  have hdeg : ∀ u, H.degree u = partDegree (e.symm u) := by
    intro u
    obtain ⟨w, rfl⟩ := e.surjective u
    rw [e.symm_apply_apply, ← degree_butterfly s w]
    exact e.degree_eq w
  refine ⟨H, ?_, ?_, ?_⟩
  · have h1 : H.edgeSet.ncard = 25301312 * s ^ 2 := by
      rw [Set.ncard_eq_toFinset_card' H.edgeSet, ← card_edgeFinset_butterfly s]
      exact (e.card_edgeFinset_eq).symm
    rw [h1]
    have hs' : (0 : ℝ) < s := by exact_mod_cast hs
    push_cast
    nlinarith
  · have h268 : 0 < 268 * s := by omega
    have h45 : 0 < 45 * s := by omega
    have h2476 : 0 < 2476 * s := by omega
    let a : Vert s := .inl (0, ⟨0, h268⟩)
    let b : Vert s := .inr (.inl ⟨0, h2476⟩)
    let c : Vert s := .inr (.inr (.inl (0, ⟨0, h45⟩)))
    refine ⟨{e a, e b, e c}, SimpleGraph.is3Clique_triple_iff.2 ⟨?_, ?_, ?_⟩⟩ <;>
      rw [e.map_adj_iff] <;> rfl
  · intro T hT
    obtain ⟨x, y, z, hxy, hxz, hyz, rfl⟩ := SimpleGraph.is3Clique_iff.1 hT
    have hxy' : x ≠ y := H.ne_of_adj hxy
    have hxz' : x ≠ z := H.ne_of_adj hxz
    have hyz' : y ≠ z := H.ne_of_adj hyz
    rw [Finset.sum_insert (by simp [hxy', hxz']), Finset.sum_pair hyz', hdeg, hdeg, hdeg,
      ← add_assoc]
    exact triangle_sum _ _ _ (e.symm.map_adj_iff.2 hxy) (e.symm.map_adj_iff.2 hxz)
      (e.symm.map_adj_iff.2 hyz)

open scoped Classical in
/-- Any `x` with the defining property of `h (10060 s)` is at most `14727 s`. -/
theorem le_of_forall_graph (s : ℕ) (hs : 0 < s) (x : ℝ)
    (hx : ∀ G : SimpleGraph (Fin (10060 * s)),
      ((10060 * s : ℕ) : ℝ) ^ 2 / 4 < (G.edgeSet.ncard : ℝ) →
        ∃ T : Finset (Fin (10060 * s)), G.IsNClique 3 T ∧ x ≤ (∑ v ∈ T, G.degree v : ℝ)) :
    x ≤ 14727 * s := by
  obtain ⟨H, hE, -, hT⟩ := exists_graph s hs
  obtain ⟨T, hTc, hxT⟩ := hx H hE
  have := hT T hTc
  rw [← Nat.cast_sum, this] at hxT
  exact_mod_cast hxT

theorem h_le (s : ℕ) (hs : 0 < s) : h (10060 * s) ≤ 14727 * s :=
  Real.sSup_le (fun x hx => le_of_forall_graph s hs x hx) (by positivity)

theorem ratio_lt : (14727 : ℝ) / 10060 < 2 * (Real.sqrt 3 - 1) := by
  have h : (34847 : ℝ) / 20120 < Real.sqrt 3 := by
    rw [Real.lt_sqrt (by norm_num)]
    norm_num
  linarith

/-! ### `h` is the extremal function of the problem -/

open scoped Classical in
/-- Mantel: a graph on `n` vertices with more than `n^2/4` edges contains a triangle. -/
theorem exists_triangle_of_dense (n : ℕ) (G : SimpleGraph (Fin n))
    (hG : (n : ℝ) ^ 2 / 4 < (G.edgeSet.ncard : ℝ)) : ∃ T : Finset (Fin n), G.IsNClique 3 T := by
  by_contra hne
  have cf : G.CliqueFree (2 + 1) := fun T hT => hne ⟨T, hT⟩
  have h1 := cf.card_edgeFinset_le
  rw [Fintype.card_fin, SimpleGraph.turanNumber_two] at h1
  have h2 : G.edgeSet.ncard = #G.edgeFinset := Set.ncard_eq_toFinset_card' G.edgeSet
  have h3 : ((n ^ 2 / 4 : ℕ) : ℝ) ≤ (n : ℝ) ^ 2 / 4 := by
    have := Nat.cast_div_le (α := ℝ) (m := n ^ 2) (n := 4)
    push_cast at this
    exact this
  have h4 : (G.edgeSet.ncard : ℝ) ≤ ((n ^ 2 / 4 : ℕ) : ℝ) := by
    rw [h2]; exact_mod_cast h1
  linarith

open scoped Classical in
/-- `h n` has the defining property: every graph on `n` vertices with more than `n^2/4` edges
contains a triangle whose degree sum is at least `h n`. -/
theorem h_spec (n : ℕ) (G : SimpleGraph (Fin n))
    (hG : (n : ℝ) ^ 2 / 4 < (G.edgeSet.ncard : ℝ)) :
    ∃ T : Finset (Fin n), G.IsNClique 3 T ∧ h n ≤ (∑ v ∈ T, G.degree v : ℝ) := by
  obtain ⟨T₀, hT₀⟩ := exists_triangle_of_dense n G hG
  have hne : (univ.filter fun T : Finset (Fin n) => G.IsNClique 3 T).Nonempty :=
    ⟨T₀, by simp [hT₀]⟩
  obtain ⟨T, hT, hmax⟩ := Finset.exists_max_image _
    (fun T : Finset (Fin n) => (∑ v ∈ T, G.degree v : ℝ)) hne
  refine ⟨T, by simpa using hT, Real.sSup_le (fun x hx => ?_) (by positivity)⟩
  obtain ⟨T', hT', hxT'⟩ := hx G hG
  exact hxT'.trans (hmax T' (by simpa using hT'))

open scoped Classical in
/-- For `n ≥ 3`, every `x` with the defining property satisfies `x ≤ h n`. -/
theorem le_h (n : ℕ) (hn : 3 ≤ n) (x : ℝ)
    (hx : ∀ G : SimpleGraph (Fin n), (n : ℝ) ^ 2 / 4 < (G.edgeSet.ncard : ℝ) →
      ∃ T : Finset (Fin n), G.IsNClique 3 T ∧ x ≤ (∑ v ∈ T, G.degree v : ℝ)) :
    x ≤ h n := by
  have hbdd : BddAbove {x : ℝ | ∀ G : SimpleGraph (Fin n),
      (n : ℝ) ^ 2 / 4 < (G.edgeSet.ncard : ℝ) →
        ∃ T : Finset (Fin n), G.IsNClique 3 T ∧ x ≤ (∑ v ∈ T, G.degree v : ℝ)} := by
    refine ⟨3 * n, fun y hy => ?_⟩
    have hdense : (n : ℝ) ^ 2 / 4 < ((⊤ : SimpleGraph (Fin n)).edgeSet.ncard : ℝ) := by
      rw [Set.ncard_eq_toFinset_card' _, ← SimpleGraph.edgeFinset,
        SimpleGraph.card_edgeFinset_top_eq_card_choose_two, Fintype.card_fin,
        Nat.cast_choose_two]
      have : (3 : ℝ) ≤ n := by exact_mod_cast hn
      nlinarith
    obtain ⟨T, hT, hyT⟩ := hy ⊤ hdense
    refine hyT.trans ?_
    have hcard : #T = 3 := hT.card_eq
    calc _ ≤ ∑ _v ∈ T, (n : ℝ) := Finset.sum_le_sum fun v _ => ?_
      _ = 3 * n := by simp [hcard]
    rw [← SimpleGraph.ncard_neighborSet]
    have := Set.ncard_le_ncard (Set.subset_univ ((⊤ : SimpleGraph (Fin n)).neighborSet v))
    rw [Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin] at this
    exact_mod_cast this
  exact le_csSup hbdd hx

/-! ## The negative answer -/

theorem not_eventually_eps (f : ℕ → ℝ) (hf : ∀ s, 0 < s → f (10060 * s) ≤ 14727 * s) :
    ¬ ∀ ε > (0 : ℝ), ∀ᶠ n : ℕ in atTop, (2 * (Real.sqrt 3 - 1) - ε) * n ≤ f n := by
  intro H
  set δ := 2 * (Real.sqrt 3 - 1) - 14727 / 10060 with hδdef
  have hδ : 0 < δ := by linarith [ratio_lt]
  obtain ⟨N, hN⟩ := eventually_atTop.1 (H (δ / 2) (by positivity))
  have h1 := hN (10060 * (N + 1)) (by omega)
  have h2 := hf (N + 1) (by omega)
  push_cast at h1 h2
  have hpos : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  have h3 : (2 * (Real.sqrt 3 - 1) - δ / 2) * (10060 * ((N : ℝ) + 1)) =
      14727 * ((N : ℝ) + 1) + 5030 * δ * ((N : ℝ) + 1) := by
    rw [hδdef]; ring
  nlinarith

theorem not_eventually_littleO (f : ℕ → ℝ) (hf : ∀ s, 0 < s → f (10060 * s) ≤ 14727 * s) :
    ¬ ∃ o : ℕ → ℝ, o =o[atTop] (1 : ℕ → ℝ) ∧
      ∀ᶠ n : ℕ in atTop, (2 * (Real.sqrt 3 - 1) - o n) * n ≤ f n := by
  rintro ⟨o, ho, hev⟩
  have ht : Tendsto o atTop (nhds 0) := (Asymptotics.isLittleO_one_iff ℝ).1 ho
  apply not_eventually_eps f hf
  intro ε hε
  filter_upwards [hev, ht.eventually (gt_mem_nhds hε)] with n h1 h2
  exact le_trans (mul_le_mul_of_nonneg_right (by linarith) (Nat.cast_nonneg n)) h1

/-- **Erdős Problem 1033, negative answer.** It is not true that
`h(n) ≥ (2(√3 - 1) - o(1)) n`. -/
theorem erdos_1033 :
    ¬ ∃ o : ℕ → ℝ, o =o[atTop] (1 : ℕ → ℝ) ∧
      ∀ᶠ n : ℕ in atTop, (2 * (Real.sqrt 3 - 1) - o n) * n ≤ h n :=
  not_eventually_littleO h h_le

/-- The same negative answer in `ε` form. -/
theorem erdos_1033_eps :
    ¬ ∀ ε > (0 : ℝ), ∀ᶠ n : ℕ in atTop, (2 * (Real.sqrt 3 - 1) - ε) * n ≤ h n :=
  not_eventually_eps h h_le

open scoped Classical in
/-- The negative answer for every function `f` with the defining property of `h`. -/
theorem erdos_1033_of_bound (f : ℕ → ℝ)
    (hf : ∀ n, ∀ G : SimpleGraph (Fin n), (n : ℝ) ^ 2 / 4 < (G.edgeSet.ncard : ℝ) →
      ∃ T : Finset (Fin n), G.IsNClique 3 T ∧ f n ≤ (∑ v ∈ T, G.degree v : ℝ)) :
    ¬ ∃ o : ℕ → ℝ, o =o[atTop] (1 : ℕ → ℝ) ∧
      ∀ᶠ n : ℕ in atTop, (2 * (Real.sqrt 3 - 1) - o n) * n ≤ f n :=
  not_eventually_littleO f fun s hs => le_of_forall_graph s hs (f _) (hf _)

end Erdos1033
