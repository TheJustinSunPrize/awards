import TrianglePacking.Construction
import TrianglePacking.TriangleWeight
import TrianglePacking.WeightedPacking

/-!
# The unused edge forced by each odd core degree

A triangle packing uses an even number of edges at every vertex. When the
core size is even, each core vertex has odd degree, so it has an unused edge.
Choosing one oriented unused edge from each core vertex saves weight at least
twice the core size in the packing inequality.
-/

namespace TrianglePacking

open Finset

/-- Neighbors joined to `v` by an edge of some member of the packing. -/
def coveredNeighbors {V : Type*} [DecidableEq V]
    (P : Finset (Finset V)) (v : V) : Finset V :=
  (P.filter fun T => v ∈ T).biUnion fun T => T.erase v

lemma mem_coveredNeighbors_iff {V : Type*} [DecidableEq V]
    (P : Finset (Finset V)) (v w : V) :
    w ∈ coveredNeighbors P v ↔ (v, w) ∈ P.biUnion arcs := by
  simp only [coveredNeighbors, mem_biUnion, mem_filter, mem_erase, arcs, mem_offDiag]
  aesop

lemma coveredNeighbors_subset {V : Type*} [Fintype V] [DecidableEq V]
    (P : Finset (Finset V)) (v : V) :
    coveredNeighbors P v ⊆ (univ : Finset V).erase v := by
  intro w hw
  rw [mem_coveredNeighbors_iff] at hw
  obtain ⟨T, _, he⟩ := mem_biUnion.mp hw
  have he' := mem_offDiag.mp he
  exact mem_erase.mpr ⟨he'.2.2.symm, mem_univ w⟩

/-- Every incident triangle contributes exactly two different neighbors. -/
theorem IsPacking.card_coveredNeighbors {V : Type*} [DecidableEq V]
    {G : SimpleGraph V} {P : Finset (Finset V)} (hP : IsPacking G P) (v : V) :
    (coveredNeighbors P v).card = 2 * (P.filter fun T => v ∈ T).card := by
  have hd : (↑(P.filter fun T => v ∈ T) : Set (Finset V)).PairwiseDisjoint
      (fun T => T.erase v) := by
    intro T hT U hU hTU
    change Disjoint (T.erase v) (U.erase v)
    rw [Finset.disjoint_left]
    intro w hwT hwU
    have hT' := mem_filter.mp hT
    have hU' := mem_filter.mp hU
    have hd' := hP.2 hT'.1 hU'.1 hTU
    have haT : (v, w) ∈ arcs T :=
      mem_offDiag.mpr ⟨hT'.2, (mem_erase.mp hwT).2, (mem_erase.mp hwT).1.symm⟩
    have haU : (v, w) ∈ arcs U :=
      mem_offDiag.mpr ⟨hU'.2, (mem_erase.mp hwU).2, (mem_erase.mp hwU).1.symm⟩
    exact Finset.disjoint_left.mp hd' haT haU
  unfold coveredNeighbors
  rw [card_biUnion hd]
  have hc : ∀ T ∈ P.filter (fun T => v ∈ T), (T.erase v).card = 2 := by
    intro T hT
    have hT' := mem_filter.mp hT
    rw [card_erase_of_mem hT'.2, (hP.1 T hT'.1).card_eq]
  rw [sum_congr rfl hc]
  simp [Nat.mul_comm]

/-- An even core has an unused outgoing edge at each of its vertices. -/
theorem IsPacking.exists_unused_core_arc {r s : ℕ}
    {P : Finset (Finset (Vertex r s))} (hP : IsPacking (graph r s) P)
    (hs : Even s) (c : Fin s) :
    ∃ w : Vertex r s, w ≠ Sum.inr c ∧ (Sum.inr c, w) ∉ P.biUnion arcs := by
  let v : Vertex r s := Sum.inr c
  have hc := hP.card_coveredNeighbors v
  have hsubset := coveredNeighbors_subset P v
  have hle := card_le_card hsubset
  have hcard : ((univ : Finset (Vertex r s)).erase v).card = 2 * r + s - 1 := by
    rw [card_erase_of_mem (mem_univ v), card_univ, vertex_card]
  have hlt : (coveredNeighbors P v).card < ((univ : Finset (Vertex r s)).erase v).card := by
    rw [hc, hcard] at hle ⊢
    obtain ⟨k, hk⟩ := hs
    have hspos := c.isLt
    omega
  obtain ⟨w, hw, hw'⟩ := exists_mem_notMem_of_card_lt_card hlt
  refine ⟨w, (mem_erase.mp hw).1, ?_⟩
  simpa only [mem_coveredNeighbors_iff] using hw'

/-- An even core forces unused oriented weight at least `2*s`. -/
theorem IsPacking.weighted_bound_even_core {r s : ℕ}
    {P : Finset (Finset (Vertex r s))} (hP : IsPacking (graph r s) P)
    (hs : Even s) :
    12 * P.card + 2 * s ≤ 12 * r * s + 2 * s * (s - 1) := by
  classical
  choose w hw hnot using hP.exists_unused_core_arc hs
  let f : Fin s → Vertex r s × Vertex r s := fun c => (Sum.inr c, w c)
  let M : Finset (Vertex r s × Vertex r s) := univ.image f
  let U : Finset (Vertex r s × Vertex r s) := P.biUnion arcs
  have hf : Function.Injective f := by
    intro c d h
    exact Sum.inr.inj (congrArg Prod.fst h)
  have hMcard : M.card = s := by
    change (univ.image f).card = s
    rw [card_image_of_injective univ hf, card_univ, Fintype.card_fin]
  have hMU : Disjoint U M := by
    rw [Finset.disjoint_left]
    intro e heU heM
    obtain ⟨c, _, rfl⟩ := mem_image.mp heM
    exact hnot c heU
  have hsub : U ∪ M ⊆ (univ : Finset (Vertex r s)).offDiag := by
    intro e he
    rcases mem_union.mp he with he | he
    · obtain ⟨T, _, heT⟩ := mem_biUnion.mp he
      exact offDiag_mono (subset_univ T) heT
    · obtain ⟨c, _, rfl⟩ := mem_image.mp he
      exact mem_offDiag.mpr ⟨mem_univ _, mem_univ _, (hw c).symm⟩
  have hMweight : 2 * s ≤ ∑ e ∈ M, weight e := by
    calc
      2 * s = ∑ _e ∈ M, 2 := by simp [hMcard, Nat.mul_comm]
      _ ≤ ∑ e ∈ M, weight e := by
        apply sum_le_sum
        intro e he
        obtain ⟨c, _, rfl⟩ := mem_image.mp he
        change 2 ≤ if part (w c) = 2 then 2 else 3
        by_cases hc : part (w c) = 2 <;> simp [hc]
  have hUweight : 12 * P.card ≤ ∑ e ∈ U, weight e := by
    calc
      12 * P.card = ∑ _T ∈ P, 12 := by simp [Nat.mul_comm]
      _ ≤ ∑ T ∈ P, ∑ e ∈ arcs T, weight e :=
        sum_le_sum fun T hT => triangle_weight (hP.1 T hT)
      _ = ∑ e ∈ U, weight e := (sum_biUnion hP.2).symm
  have htotal : (∑ e ∈ U, weight e) + ∑ e ∈ M, weight e ≤
      12 * r * s + 2 * s * (s - 1) := by
    rw [← sum_union hMU, ← total_weight r s]
    exact sum_le_sum_of_subset hsub
  omega

/-- Strengthened packing bound for every positive even core size. -/
theorem IsPacking.bound_even_core {r s : ℕ}
    {P : Finset (Finset (Vertex r s))} (hP : IsPacking (graph r s) P)
    (hs : Even s) (hspos : 0 < s) :
    6 * P.card ≤ 6 * r * s + s * (s - 2) := by
  have h := hP.weighted_bound_even_core hs
  obtain ⟨k, hk⟩ := hs
  have hs2 : 2 ≤ s := by omega
  have hsub : s - 1 = s - 2 + 1 := by omega
  rw [hsub] at h
  nlinarith

end TrianglePacking
