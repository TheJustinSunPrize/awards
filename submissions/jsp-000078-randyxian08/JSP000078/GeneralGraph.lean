/-
SPDX-License-Identifier: Apache-2.0

JSP-000078 / Erdos 58: arbitrary-graph scope formalization.
See VERIFICATION.md for actual verification evidence and the overlapping PR #130.

Mathematical finite theorem: Andras Gyarfas, 1992.
Existing finite Lean development: plby/lean-proofs; its main file credits
Codex and GPT-5.6 Sol. All original notices remain in downloaded dependencies.

This file does not re-prove or claim authorship of that finite theorem.
It discharges the infinite-graph extension using graph-coloring compactness.
-/
import JSP000078.Compactness
import ErdosProblems.Erdos58
import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.Circumference

open scoped SimpleGraph

namespace JSP000078

universe u

/-- The imported finite proof and the Formal Conjectures specification use
extensionally identical sets of odd cycle lengths. -/
theorem oddCycleLengths_alignment {V : Type u} (G : SimpleGraph V) :
    G.oddCycleLengths = Erdos58.oddCycleLengths G := by
  ext n
  change
    ((∃ (v : V) (p : G.Walk v v), p.IsCycle ∧ p.length = n) ∧ Odd n) ↔
      (Odd n ∧ ∃ (v : V) (p : G.Walk v v), p.IsCycle ∧ p.length = n)
  exact and_comm

/-- Passing to an induced graph cannot increase the extended cardinality
of the set of odd cycle lengths, even when the ambient graph is infinite. -/
theorem induced_oddCycleLengths_bound
    {V : Type u} (G : SimpleGraph V) (k : ℕ)
    (hk : (Erdos58.oddCycleLengths G).encard ≤ (k : ℕ∞)) (s : Set V) :
    (Erdos58.oddCycleLengths (G.induce s)).encard ≤ (k : ℕ∞) :=
  (Set.encard_mono (Erdos58.oddCycleLengths_induce_subset G s)).trans hk

/-- The finite bound extends to arbitrary vertex types by compactness. -/
theorem colorable_two_mul_add_two
    {V : Type u} (G : SimpleGraph V) (k : ℕ)
    (hk : (Erdos58.oddCycleLengths G).encard ≤ (k : ℕ∞)) :
    G.Colorable (2 * k + 2) := by
  classical
  apply colorable_of_finite_induced G (2 * k + 2)
  intro s
  have hfinite := Erdos58.erdos_58 (G.induce (s : Set V)) k
    (induced_oddCycleLengths_bound G k hk (s : Set V))
  exact SimpleGraph.chromaticNumber_le_iff_colorable.mp hfinite.1

/-- If the sharp complete graph is absent, one fewer color suffices.
Both the upper bound and the equality case of the finite theorem are used.
In particular, this is not merely an upper-bound extension. -/
theorem colorable_two_mul_add_one_of_no_clique
    {V : Type u} (G : SimpleGraph V) (k : ℕ)
    (hk : (Erdos58.oddCycleLengths G).encard ≤ (k : ℕ∞))
    (hno : ¬ SimpleGraph.completeGraph (Fin (2 * k + 2)) ⊑ G) :
    G.Colorable (2 * k + 1) := by
  classical
  apply colorable_of_finite_induced G (2 * k + 1)
  intro s
  have hfinite := Erdos58.erdos_58 (G.induce (s : Set V)) k
    (induced_oddCycleLengths_bound G k hk (s : Set V))
  apply colorable_pred_of_bound_and_ne
  · simpa only [Nat.add_assoc, Nat.reduceAdd] using hfinite.1
  · intro heq
    have heq' : (G.induce (s : Set V)).chromaticNumber =
        ((2 * k + 2 : ℕ) : ℕ∞) := by
      simpa only [Nat.add_assoc, Nat.reduceAdd] using heq
    have hcopy := hfinite.2.mp heq'
    exact hno (hcopy.trans
      (SimpleGraph.Embedding.induce (G := G) (s : Set V)).toCopy.isContained)

/-- The complete sharp theorem for arbitrary graphs, expressed with encard.
No finite-case theorem is left as a hypothesis: the concrete imported finite
proof is applied in the preceding lemmas. -/
theorem erdos_58_of_encard_bound
    {V : Type u} (G : SimpleGraph V) (k : ℕ)
    (hk : (Erdos58.oddCycleLengths G).encard ≤ (k : ℕ∞)) :
    G.chromaticNumber ≤ ((2 * k + 2 : ℕ) : ℕ∞) ∧
      (G.chromaticNumber = ((2 * k + 2 : ℕ) : ℕ∞) ↔
        SimpleGraph.completeGraph (Fin (2 * k + 2)) ⊑ G) := by
  have hupper : G.chromaticNumber ≤ ((2 * k + 2 : ℕ) : ℕ∞) :=
    (colorable_two_mul_add_two G k hk).chromaticNumber_le
  refine ⟨hupper, ?_⟩
  constructor
  · intro hχ
    by_contra hno
    have hle := (colorable_two_mul_add_one_of_no_clique G k hk hno).chromaticNumber_le
    rw [hχ] at hle
    have hnat : 2 * k + 2 ≤ 2 * k + 1 := by exact_mod_cast hle
    omega
  · intro hcopy
    exact le_antisymm hupper
      (Erdos58.completeGraph_card_le_chromaticNumber_of_isContained hcopy)

/-- Arbitrary-graph version in the exact odd-cycle-length predicate used by
the Formal Conjectures specification. Includes k=0 and the empty graph. -/
theorem erdos_58
    {V : Type u} (G : SimpleGraph V) (k : ℕ)
    (hfinite : G.oddCycleLengths.Finite)
    (hk : G.oddCycleLengths.ncard ≤ k) :
    G.chromaticNumber ≤ (2 * k + 2 : ℕ∞) ∧
      (G.chromaticNumber = (2 * k + 2 : ℕ∞) ↔
        (SimpleGraph.completeGraph (Fin (2 * k + 2))).IsContained G) := by
  have hencard : (Erdos58.oddCycleLengths G).encard ≤ (k : ℕ∞) := by
    rw [← oddCycleLengths_alignment G, ← hfinite.cast_ncard_eq]
    exact_mod_cast hk
  simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] using
    erdos_58_of_encard_bound G k hencard

/-- A closed theorem declaration mirroring the quantifiers of the upstream
Formal Conjectures problem, under a fresh namespace to avoid replacing the
existing finite theorem with the same name. -/
theorem erdos_58_exact_statement :
    ∀ {V : Type u} (G : SimpleGraph V) (k : ℕ),
      G.oddCycleLengths.Finite →
      G.oddCycleLengths.ncard ≤ k →
        G.chromaticNumber ≤ (2 * k + 2 : ℕ∞) ∧
        (G.chromaticNumber = (2 * k + 2 : ℕ∞) ↔
          (SimpleGraph.completeGraph (Fin (2 * k + 2))).IsContained G) := by
  intro V G k hfinite hk
  exact erdos_58 G k hfinite hk

end JSP000078
