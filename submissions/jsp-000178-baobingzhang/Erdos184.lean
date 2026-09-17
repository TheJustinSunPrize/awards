import Mathlib

/-!
# Erdős Problem 184: the `K_{3,n-3}` lower bound

Erdős Problem 184 ([erdosproblems.com/184](https://www.erdosproblems.com/184)) asks whether every
graph on `n` vertices can be decomposed into `O(n)` edge-disjoint cycles and edges. The problem
page notes: "The graph $K_{3,n-3}$ shows that at least $(1+c)n$ many cycles and edges are required,
for some constant $c>0$." This file proves that statement, with `c = 1/4`.

`SimpleGraph.IsDecomposition`
(`FormalConjecturesForMathlib/Combinatorics/SimpleGraph/Decomposition.lean`) and
`Erdos184.IsCycleOrEdge` (`FormalConjectures/ErdosProblems/184.lean`) are copied verbatim from
Google DeepMind's formal-conjectures project (Apache-2.0). The main theorem
`Erdos184.erdos_184.variants.lower_bound` has exactly the name and statement used there.

## Proof

Let `G = K_{3,n-3}` on `Fin n`, with small part `B = {0, 1, 2}` and big part `A = {3, …, n-1}`,
and let `D` decompose `G` into pieces that are either connected `2`-regular graphs ("cycles") or
graphs with exactly one edge. For a piece `H` and a vertex `v` write `d_H(v)` for the degree of `v`
in `H`. Let `S` be the pieces with at most one edge and `T` the others (which are cycles).

* Every `v ∈ A` has `G`-degree `3`, and each of its edges lies in exactly one piece, so
  `∑_{H ∈ D} d_H(v) = 3`.
* In a cycle every degree is `0` or `2`, so `∑_{H ∈ T} d_H(v)` is even and
  `∑_{H ∈ S} d_H(v) ≥ 1`.
* Every edge of `G` has exactly one endpoint in `A`, so `∑_{v ∈ A} d_H(v) ≤ 1` for `H ∈ S`, and
  `∑_{v ∈ A} d_H(v) = ∑_{w ∈ B} d_H(w) ≤ 6` for `H ∈ T`.

Summing over `v ∈ A` gives `|A| ≤ |S|` and `3 |A| ≤ |S| + 6 |T|`, hence
`6 |D| ≥ 5 |S| + 3 |A| ≥ 8 |A|`, i.e. `3 |D| ≥ 4 (n - 3)`. This is at least `(5/4) n` once
`n ≥ 48`. Connectivity of the cycles is not needed.

## Main results

* `Erdos184.four_mul_le`: every such decomposition of `K_{3,n-3}` has `4 n ≤ 3 |D| + 12`.
* `Erdos184.erdos_184.variants.lower_bound`: at least `(1 + c) n` pieces are needed, for `c = 1/4`
  and all large `n`.

## References

* [erdosproblems.com/184](https://www.erdosproblems.com/184)
-/

open Filter SimpleGraph

namespace SimpleGraph

/--
`D` is a decomposition of `G` into edge-disjoint subgraphs: the edge sets of the members of `D`
are pairwise disjoint and their union is the edge set of `G`.
-/
def IsDecomposition {V : Type*} (G : SimpleGraph V) (D : Finset G.Subgraph) : Prop :=
  Set.PairwiseDisjoint (D : Set G.Subgraph) (fun H ↦ H.edgeSet) ∧
  (⋃ H ∈ D, H.edgeSet) = G.edgeSet

end SimpleGraph

namespace Erdos184

/--
A graph $H$ is a cycle or an edge if it is connected and 2-regular, or if it has exactly one edge.
-/
def IsCycleOrEdge {U : Type*} [Fintype U] (H : SimpleGraph U) : Prop :=
  open scoped Classical in
  (H.Connected ∧ H.IsRegularOfDegree 2) ∨ H.edgeFinset.card = 1

section Counting

open Finset
open scoped Classical

/-- A cycle has all degrees equal to `2` on its vertices; a single edge has a subsingleton edge
set. -/
lemma IsCycleOrEdge.cases {V : Type*} [Fintype V] {G : SimpleGraph V} (H : G.Subgraph)
    [Fintype H.verts] (h : IsCycleOrEdge H.coe) :
    (∀ v ∈ H.verts, #{w | H.Adj v w} = 2) ∨ H.edgeSet.Subsingleton := by
  rcases h with ⟨-, hreg⟩ | h1
  · left
    intro v hv
    have := hreg ⟨v, hv⟩
    rw [← card_neighborSet_eq_degree] at this
    rw [← this, ← Fintype.card_subtype]
    convert (Fintype.card_congr (H.coeNeighborSetEquiv ⟨v, hv⟩)).symm
    exact Iff.rfl
  · right
    intro e₁ he₁ e₂ he₂
    induction e₁ using Sym2.ind with | h a b =>
    induction e₂ using Sym2.ind with | h c d =>
    rw [Subgraph.mem_edgeSet] at he₁ he₂
    have h₁ : s((⟨a, H.edge_vert he₁⟩ : H.verts), ⟨b, H.edge_vert he₁.symm⟩) ∈
        H.coe.edgeFinset := by
      simpa using he₁
    have h₂ : s((⟨c, H.edge_vert he₂⟩ : H.verts), ⟨d, H.edge_vert he₂.symm⟩) ∈
        H.coe.edgeFinset := by
      simpa using he₂
    have := Finset.card_le_one.mp h1.le _ h₁ _ h₂
    simpa using congrArg (Sym2.map Subtype.val) this

variable {n : ℕ} {G : SimpleGraph (Fin n)}

/-- In a decomposition, each edge of `G` lies in exactly one piece. -/
lemma card_filter_adj (D : Finset G.Subgraph) (hdec : IsDecomposition G D) (v w : Fin n) :
    #{H ∈ D | H.Adj v w} = if G.Adj v w then 1 else 0 := by
  split_ifs with h
  · rw [Finset.card_eq_one]
    have : s(v, w) ∈ ⋃ H ∈ D, H.edgeSet := hdec.2 ▸ h
    obtain ⟨H₀, hH₀, hvw⟩ : ∃ H ∈ D, H.Adj v w := by simpa using this
    refine ⟨H₀, ?_⟩
    ext H
    simp only [mem_filter, mem_singleton]
    constructor
    · rintro ⟨hH, hHvw⟩
      by_contra hne
      exact Set.disjoint_left.mp (hdec.1 hH hH₀ hne) (Subgraph.mem_edgeSet.mpr hHvw)
        (Subgraph.mem_edgeSet.mpr hvw)
    · rintro rfl
      exact ⟨hH₀, hvw⟩
  · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro H _ hH
    exact h (H.adj_sub hH)

/-- The counting bound: a decomposition of `K_{3,n-3}` (given through its adjacency at the big
vertices) into cycles and edges has at least `4 (n - 3) / 3` pieces. -/
lemma four_mul_le (hn : 3 ≤ n) (hG : ∀ v w : Fin n, 3 ≤ (v : ℕ) → (G.Adj v w ↔ (w : ℕ) < 3))
    (D : Finset G.Subgraph) (hD : ∀ H ∈ D, IsCycleOrEdge H.coe) (hdec : IsDecomposition G D) :
    4 * n ≤ 3 * #D + 12 := by
  set A : Finset (Fin n) := {v | 3 ≤ (v : ℕ)} with hA
  set B : Finset (Fin n) := {w | (w : ℕ) < 3} with hB
  set S := {H ∈ D | H.edgeSet.Subsingleton} with hS
  set T := {H ∈ D | ¬ H.edgeSet.Subsingleton} with hT
  have hBcard : #B = 3 := by rw [hB, Fin.card_filter_val_lt]; omega
  have hABcard : #A + #B = n := by
    have := card_filter_add_card_filter_not (s := (univ : Finset (Fin n)))
      (fun v : Fin n ↦ 3 ≤ (v : ℕ))
    simp only [not_le, card_univ, Fintype.card_fin] at this
    exact this
  have hDcard : #S + #T = #D := card_filter_add_card_filter_not _
  -- every big vertex has degree `3`
  have hdeg3 : ∀ v ∈ A, ∑ H ∈ D, #{w | H.Adj v w} = 3 := by
    intro v hv
    have hv' : 3 ≤ (v : ℕ) := by simpa [hA] using hv
    simp_rw [card_filter]
    rw [sum_comm]
    simp_rw [← card_filter, card_filter_adj D hdec, hG v _ hv', ← card_filter]
    exact hBcard
  -- degrees in cycle pieces
  have hcyc : ∀ H ∈ T, ∀ u, #{w | H.Adj u w} = if u ∈ H.verts then 2 else 0 := by
    intro H hH u
    have hH' := mem_filter.mp hH
    have h2 := ((IsCycleOrEdge.cases H (hD H hH'.1)).resolve_right hH'.2)
    split_ifs with hu
    · exact h2 u hu
    · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro w _ hw
      exact hu (H.edge_vert hw)
  -- a cycle piece has at most `6` edges
  have hT6 : ∀ H ∈ T, ∑ v ∈ A, #{w | H.Adj v w} ≤ 6 := by
    intro H hH
    calc ∑ v ∈ A, #{w | H.Adj v w} ≤ ∑ v, #{w ∈ B | H.Adj v w} := by
          refine (sum_le_sum fun v hv ↦ ?_).trans (sum_le_sum_of_subset (subset_univ A))
          apply card_le_card
          intro w hw
          have hv' : 3 ≤ (v : ℕ) := by simpa [hA] using hv
          have hw' : H.Adj v w := by simpa using hw
          simpa [hB, hw'] using (hG v w hv').mp (H.adj_sub hw')
      _ = ∑ w ∈ B, #{v | H.Adj w v} := by
          simp_rw [card_filter]
          rw [sum_comm]
          simp_rw [H.adj_comm]
      _ ≤ ∑ w ∈ B, 2 := by
          refine sum_le_sum fun w _ ↦ ?_
          rw [hcyc H hH w]
          split_ifs <;> omega
      _ = 6 := by simp [hBcard]
  -- a single-edge piece contributes at most `1`
  have hS1 : ∀ H ∈ S, ∑ v ∈ A, #{w | H.Adj v w} ≤ 1 := by
    intro H hH
    have hsub := (mem_filter.mp hH).2
    have : ∑ v ∈ A, #{w | H.Adj v w} = #{p ∈ A ×ˢ (univ : Finset (Fin n)) | H.Adj p.1 p.2} := by
      rw [card_filter, sum_product]
      simp_rw [card_filter]
    rw [this, card_le_one]
    rintro ⟨v, w⟩ hp ⟨v', w'⟩ hq
    simp only [mem_filter, mem_product, mem_univ, and_true] at hp hq
    have hv : 3 ≤ (v : ℕ) := by simpa [hA] using hp.1
    have hv' : 3 ≤ (v' : ℕ) := by simpa [hA] using hq.1
    have he : s(v, w) = s(v', w') :=
      hsub (Subgraph.mem_edgeSet.mpr hp.2) (Subgraph.mem_edgeSet.mpr hq.2)
    rcases Sym2.eq_iff.mp he with ⟨rfl, rfl⟩ | ⟨h₁, -⟩
    · rfl
    · have := (hG v' w' hv').mp (H.adj_sub hq.2)
      rw [← h₁] at this
      omega
  -- parity: every big vertex lies in a single-edge piece
  have hpar : ∀ v ∈ A, 1 ≤ ∑ H ∈ S, #{w | H.Adj v w} := by
    intro v hv
    have h3 := hdeg3 v hv
    rw [← sum_filter_add_sum_filter_not D (fun H ↦ H.edgeSet.Subsingleton)] at h3
    have heven : Even (∑ H ∈ T, #{w | H.Adj v w}) := by
      refine Finset.even_sum _ fun H hH ↦ ?_
      rw [hcyc H hH v]
      split_ifs <;> decide
    obtain ⟨r, hr⟩ := heven
    rw [← hS, ← hT] at h3
    omega
  have h1 : #A ≤ #S := by
    calc #A = ∑ v ∈ A, 1 := card_eq_sum_ones A
      _ ≤ ∑ v ∈ A, ∑ H ∈ S, #{w | H.Adj v w} := sum_le_sum hpar
      _ = ∑ H ∈ S, ∑ v ∈ A, #{w | H.Adj v w} := sum_comm
      _ ≤ ∑ H ∈ S, 1 := sum_le_sum hS1
      _ = #S := (card_eq_sum_ones S).symm
  have h2 : 3 * #A ≤ #S + 6 * #T := by
    calc 3 * #A = ∑ v ∈ A, 3 := by simp [mul_comm]
      _ = ∑ v ∈ A, ∑ H ∈ D, #{w | H.Adj v w} := (sum_congr rfl hdeg3).symm
      _ = ∑ H ∈ D, ∑ v ∈ A, #{w | H.Adj v w} := sum_comm
      _ = ∑ H ∈ S, ∑ v ∈ A, #{w | H.Adj v w} + ∑ H ∈ T, ∑ v ∈ A, #{w | H.Adj v w} :=
          (sum_filter_add_sum_filter_not D (fun H ↦ H.edgeSet.Subsingleton) _).symm
      _ ≤ ∑ H ∈ S, 1 + ∑ H ∈ T, 6 := add_le_add (sum_le_sum hS1) (sum_le_sum hT6)
      _ = #S + 6 * #T := by simp [mul_comm]
  omega

end Counting

open scoped Classical in
/--
The graph $K_{3,n-3}$ shows that at least $(1+c)n$ many cycles and edges are required, for some
constant $c>0$.
-/
theorem erdos_184.variants.lower_bound :
    ∃ c > 0, ∀ᶠ n in atTop,
      let G : SimpleGraph (Fin n) := fromRel (fun (i j : Fin n) => (i : ℕ) < 3 ∧ 3 ≤ (j : ℕ));
      ∀ (D : Finset G.Subgraph),
        (∀ H ∈ D, IsCycleOrEdge H.coe) →
        IsDecomposition G D →
        (1 + c) * (n : ℝ) ≤ (D.card : ℝ) := by
  refine ⟨1 / 4, by norm_num, ?_⟩
  filter_upwards [eventually_ge_atTop 48] with n hn
  intro G D hD hdec
  have hG : ∀ v w : Fin n, 3 ≤ (v : ℕ) → (G.Adj v w ↔ (w : ℕ) < 3) := by
    intro v w hv
    simp only [G, fromRel_adj, ne_eq, Fin.ext_iff]
    omega
  have h := four_mul_le (by omega) hG D hD hdec
  have h' : (4 : ℝ) * n ≤ 3 * D.card + 12 := by exact_mod_cast h
  have hn' : (48 : ℝ) ≤ n := by exact_mod_cast hn
  linarith

end Erdos184
