import JSP000853.UpperBound
import Mathlib.Combinatorics.SimpleGraph.Acyclic

/-!
# The incidence graph of a grid subset

A set of grid points is viewed as the edge set of a bipartite graph: rows are
the left vertices and columns are the right vertices.  This representation is
the counting device for the grid upper bound.
-/

namespace JSP000853

open SimpleGraph

set_option linter.style.haveILetI false

/-- The bipartite incidence graph whose edges are the points of `S`. -/
def gridGraph {n : ℕ} (S : Finset (Grid n)) : SimpleGraph (Sum (Fin n) (Fin n)) where
  Adj
    | .inl i, .inr j => (i, j) ∈ S
    | .inr j, .inl i => (i, j) ∈ S
    | _, _ => False
  symm := ⟨by
    intro u v
    cases u <;> cases v <;> simp_all⟩
  loopless := ⟨by
    intro u
    cases u <;> simp⟩

noncomputable instance {n : ℕ} (S : Finset (Grid n)) :
    Fintype (gridGraph S).edgeSet :=
  Fintype.ofFinite _

@[simp]
theorem gridGraph_adj_inl_inr {n : ℕ} {S : Finset (Grid n)} {i j : Fin n} :
    (gridGraph S).Adj (.inl i) (.inr j) ↔ (i, j) ∈ S :=
  Iff.rfl

@[simp]
theorem gridGraph_adj_inr_inl {n : ℕ} {S : Finset (Grid n)} {i j : Fin n} :
    (gridGraph S).Adj (.inr j) (.inl i) ↔ (i, j) ∈ S :=
  Iff.rfl

@[simp]
theorem gridGraph_not_adj_inl_inl {n : ℕ} {S : Finset (Grid n)} {i j : Fin n} :
    ¬(gridGraph S).Adj (.inl i) (.inl j) := by
  simp [gridGraph]

@[simp]
theorem gridGraph_not_adj_inr_inr {n : ℕ} {S : Finset (Grid n)} {i j : Fin n} :
    ¬(gridGraph S).Adj (.inr i) (.inr j) := by
  simp [gridGraph]

theorem gridGraph_adj_has_left_endpoint {n : ℕ} {S : Finset (Grid n)}
    {u v : Sum (Fin n) (Fin n)} (h : (gridGraph S).Adj u v) :
    ∃ i : Fin n, u = Sum.inl i ∨ v = Sum.inl i := by
  cases u <;> cases v <;> simp_all

/-- A grid point as the corresponding unordered incidence edge. -/
def gridEdge {n : ℕ} (p : Grid n) : Sym2 (Sum (Fin n) (Fin n)) :=
  s(.inl p.1, .inr p.2)

theorem gridEdge_injective {n : ℕ} : Function.Injective (@gridEdge n) := by
  rintro ⟨i, j⟩ ⟨k, l⟩ h
  simp only [gridEdge, Sym2.eq_iff] at h
  rcases h with h | h
  · simp_all
  · simp_all

theorem mem_gridGraph_edgeSet_iff {n : ℕ} {S : Finset (Grid n)} {e} :
    e ∈ (gridGraph S).edgeSet ↔ ∃ p ∈ S, gridEdge p = e := by
  induction e using Sym2.inductionOn with
  | _ u v =>
    cases u <;> cases v <;> simp [SimpleGraph.mem_edgeSet, gridEdge]

theorem gridGraph_edgeFinset_eq_image {n : ℕ} (S : Finset (Grid n)) :
    (gridGraph S).edgeFinset = S.image gridEdge := by
  classical
  ext e
  rw [SimpleGraph.mem_edgeFinset]
  simp only [Finset.mem_image]
  exact mem_gridGraph_edgeSet_iff

theorem card_gridGraph_edgeFinset {n : ℕ} (S : Finset (Grid n)) :
    (gridGraph S).edgeFinset.card = S.card := by
  classical
  rw [gridGraph_edgeFinset_eq_image, Finset.card_image_of_injective S gridEdge_injective]

/-- A finite forest has at most one fewer edge than vertices. -/
theorem forest_card_edgeFinset_add_one_le
    {V : Type*} [Fintype V] [Nonempty V] {G : SimpleGraph V}
    [Fintype G.edgeSet] (hG : G.IsAcyclic) :
    G.edgeFinset.card + 1 ≤ Fintype.card V := by
  classical
  obtain ⟨T, hGT, _hTtop, hT⟩ :=
    (SimpleGraph.connected_top (V := V)).exists_isTree_le_of_le_of_isAcyclic le_top hG
  haveI : Fintype T.edgeSet := Fintype.ofFinite _
  calc
    G.edgeFinset.card + 1 ≤ T.edgeFinset.card + 1 := by
      exact Nat.add_le_add_right
        (Finset.card_le_card (SimpleGraph.edgeFinset_mono hGT)) 1
    _ = Fintype.card V := hT.card_edgeFinset

/-- A free grid set has an acyclic incidence graph.  At the least row vertex
of a hypothetical cycle, two incident columns and the next row on the cycle
would give three points `f(x,y) = z` inside the set. -/
theorem gridGraph_isAcyclic_of_isFree {n : ℕ}
    (hcard : 2 < Fintype.card (Grid n)) {S : Finset (Grid n)}
    (hfree : (gridMapping hcard).IsFree S) : (gridGraph S).IsAcyclic := by
  intro v p hcycle
  classical
  have hleft : ∃ i : Fin n, Sum.inl i ∈ p.support := by
    have hv_support : v ∈ p.support :=
      p.mem_verts_toSubgraph.mp p.start_mem_verts_toSubgraph
    have hsnd_support : p.snd ∈ p.support :=
      List.mem_of_mem_tail (Walk.snd_mem_tail_support hcycle.not_nil)
    have hadj := p.adj_snd hcycle.not_nil
    obtain ⟨i, hi | hi⟩ := gridGraph_adj_has_left_endpoint hadj
    · exact ⟨i, hi ▸ hv_support⟩
    · exact ⟨i, hi ▸ hsnd_support⟩
  let rows : Finset (Fin n) := Finset.univ.filter fun i => Sum.inl i ∈ p.support
  have hrows : rows.Nonempty := by
    obtain ⟨i, hi⟩ := hleft
    exact ⟨i, by simp [rows, hi]⟩
  let a : Fin n := rows.min' hrows
  have ha_rows : a ∈ rows := Finset.min'_mem rows hrows
  have ha_support : Sum.inl a ∈ p.support := by
    simpa only [rows, Finset.mem_filter, Finset.mem_univ, true_and] using ha_rows
  have ha_min : ∀ c : Fin n, Sum.inl c ∈ p.support → a ≤ c := by
    intro c hc
    exact Finset.min'_le rows c (by simp [rows, hc])
  have hdeg_a := hcycle.ncard_neighborSet_toSubgraph_eq_two ha_support
  obtain ⟨x, y, hxy, hneighbors⟩ := Set.ncard_eq_two.mp hdeg_a
  have hxadj : p.toSubgraph.Adj (Sum.inl a) x := by
    change x ∈ p.toSubgraph.neighborSet (Sum.inl a)
    rw [hneighbors]
    simp
  have hyadj : p.toSubgraph.Adj (Sum.inl a) y := by
    change y ∈ p.toSubgraph.neighborSet (Sum.inl a)
    rw [hneighbors]
    simp
  obtain ⟨b, d, hbd, hab_sub, had_sub⟩ :
      ∃ b d : Fin n, b ≠ d ∧
        p.toSubgraph.Adj (Sum.inl a) (Sum.inr b) ∧
        p.toSubgraph.Adj (Sum.inl a) (Sum.inr d) := by
    cases x with
    | inl i =>
        have hbad := p.toSubgraph.adj_sub hxadj
        simp at hbad
    | inr b =>
        cases y with
        | inl i =>
            have hbad := p.toSubgraph.adj_sub hyadj
            simp at hbad
        | inr d =>
            refine ⟨b, d, ?_, hxadj, hyadj⟩
            intro h
            apply hxy
            simp [h]
  have hab : (a, b) ∈ S := by
    simpa using p.toSubgraph.adj_sub hab_sub
  have had : (a, d) ∈ S := by
    simpa using p.toSubgraph.adj_sub had_sub
  have hb_support : Sum.inr b ∈ p.support := by
    apply p.mem_verts_toSubgraph.mp
    exact p.toSubgraph.edge_vert (p.toSubgraph.adj_symm hab_sub)
  have hdeg_b := hcycle.ncard_neighborSet_toSubgraph_eq_two hb_support
  obtain ⟨x, y, hxy, hneighbors⟩ := Set.ncard_eq_two.mp hdeg_b
  have ha_neighbor : Sum.inl a ∈ p.toSubgraph.neighborSet (Sum.inr b) :=
    p.toSubgraph.adj_symm hab_sub
  have hother : ∃ z, p.toSubgraph.Adj (Sum.inr b) z ∧ z ≠ Sum.inl a := by
    rw [hneighbors] at ha_neighbor
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha_neighbor
    rcases ha_neighbor with hax | hay
    · refine ⟨y, ?_, ?_⟩
      · change y ∈ p.toSubgraph.neighborSet (Sum.inr b)
        rw [hneighbors]
        simp
      · intro hya
        exact hxy (hax.symm.trans hya.symm)
    · refine ⟨x, ?_, ?_⟩
      · change x ∈ p.toSubgraph.neighborSet (Sum.inr b)
        rw [hneighbors]
        simp
      · intro hxa
        exact hxy (hxa.trans hay)
  obtain ⟨z, hbz_sub, hza⟩ := hother
  obtain ⟨c, hca, hbc_sub⟩ :
      ∃ c : Fin n, c ≠ a ∧ p.toSubgraph.Adj (Sum.inr b) (Sum.inl c) := by
    cases z with
    | inl c =>
        refine ⟨c, ?_, hbz_sub⟩
        intro h
        exact hza (by simp [h])
    | inr j =>
        have hbad := p.toSubgraph.adj_sub hbz_sub
        simp at hbad
  have hbc : (c, b) ∈ S := by
    simpa using p.toSubgraph.adj_sub hbc_sub
  have hc_support : Sum.inl c ∈ p.support := by
    apply p.mem_verts_toSubgraph.mp
    exact p.toSubgraph.edge_vert (p.toSubgraph.adj_symm hbc_sub)
  have hac : a < c := lt_of_le_of_ne (ha_min c hc_support) hca.symm
  have hpq : (a, d) ≠ (c, b) := by
    intro h
    exact hac.ne (congrArg Prod.fst h)
  have hmap : gridMapping hcard (a, d) (c, b) = (a, b) := by
    simp [gridMapping, gridCore, hac.ne, hbd.symm, hac]
  have hnot := hfree had hbc hpq
  rw [hmap] at hnot
  exact hnot hab

/-- Every free set in the `n × n` grid construction has at most `2n - 1`
points.  The slightly weaker displayed form is more convenient downstream. -/
theorem free_card_add_one_le_two_mul {n : ℕ}
    (hcard : 2 < Fintype.card (Grid n)) {S : Finset (Grid n)}
    (hfree : (gridMapping hcard).IsFree S) : S.card + 1 ≤ 2 * n := by
  have hn : 0 < n := Nat.pos_of_ne_zero fun hn ↦ by
    subst n
    simp at hcard
  letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hforest := forest_card_edgeFinset_add_one_le
    (gridGraph_isAcyclic_of_isFree hcard hfree)
  rw [card_gridGraph_edgeFinset] at hforest
  simpa [Fintype.card_sum, Fintype.card_fin, two_mul] using hforest

theorem free_card_sq_le_four_mul_sq {n : ℕ}
    (hcard : 2 < Fintype.card (Grid n)) {S : Finset (Grid n)}
    (hfree : (gridMapping hcard).IsFree S) : S.card ^ 2 ≤ 4 * n ^ 2 := by
  have h := free_card_add_one_le_two_mul hcard hfree
  have hs : S.card ≤ 2 * n := le_trans (Nat.le_add_right S.card 1) h
  calc
    S.card ^ 2 ≤ (2 * n) ^ 2 := Nat.pow_le_pow_left hs 2
    _ = 4 * n ^ 2 := by simp only [pow_two]; ac_rfl

end JSP000853
