import JSP690.Encoding
import JSP690.Certificates
import JSP690.NonColorable
import JSP690.Subgraph

/-! A positive answer to JSP-000690 (Erdős problem 834), in its explicitly
chromatic interpretation. The mathematical construction is due to Ruiliang Li,
arXiv:2512.24850v1, Theorem 1.2 / Section 4. This file formalizes the known
construction and does not claim a new mathematical discovery. -/

namespace JSP690

theorem witness_chromatic_number : HasChromaticNumber witness 3 := by
  exact ⟨witness_three_colorable, not_colorable_of_lt_three⟩

theorem witness_all_proper_subgraphs_colorable
    (F : Hypergraph 9) (V : Vertex 9 → Prop)
    (hF : StrictSubgraphOn F witness V) : ColorableOn F V 2 := by
  exact strictSubgraphOn_colorable_of_deletions
    witness_edge_deletion_colorable witness_vertex_deletion_colorable hF

theorem witness_chromatic_critical : ChromaticCritical witness 3 := by
  exact ⟨witness_chromatic_number, witness_all_proper_subgraphs_colorable⟩

theorem witness_vertex_deletion_colorableOn (v : Vertex 9) :
    ColorableOn (deleteVertex witness v) (fun u => u ≠ v) 2 := by
  exact colorableOn_deleteVertex (witness_vertex_deletion_colorable v)

/-- The explicit strengthened existence statement: 9 vertices, 22 distinct
three-element edges, chromatic number exactly 3, all proper subhypergraphs
2-colourable on their own vertex domains, and minimum degree exactly 7. -/
theorem jsp_000690_nine_vertices :
    ∃ H : Hypergraph 9,
      Simple H ∧ H.length = 22 ∧ Uniform H 3 ∧ ChromaticCritical H 3 ∧
      (∀ v : Vertex 9, 7 ≤ degree H v) ∧ (∃ v : Vertex 9, degree H v = 7) := by
  exact ⟨witness, witness_simple, witness_edge_count, witness_three_uniform,
    witness_chromatic_critical, witness_min_degree,
    ⟨1, witness_attains_degree_seven⟩⟩

/-- JSP-000690: a finite simple 3-uniform, critically 3-chromatic hypergraph
with minimum degree at least 7 exists. No hypothesis is assumed. -/
theorem jsp_000690 :
    ∃ (n : Nat) (H : Hypergraph n),
      0 < n ∧ Simple H ∧ Uniform H 3 ∧ ChromaticCritical H 3 ∧
      ∀ v : Vertex n, 7 ≤ degree H v := by
  exact ⟨9, witness, by decide, witness_simple, witness_three_uniform,
    witness_chromatic_critical, witness_min_degree⟩

end JSP690
