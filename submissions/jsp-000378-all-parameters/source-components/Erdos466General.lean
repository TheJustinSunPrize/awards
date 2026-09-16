/- Full parameter classification for Erdős 466 / JSP-000378.
See Erdos466Construction.lean, README and ATTRIBUTION for prior work and scope.
Released under the Apache 2.0 license. -/
import Erdos466Construction
import Erdos466Endpoint

open Metric Set Filter
open scoped Topology
namespace Erdos466General
noncomputable section

lemma realizable_card_le_three {δ X : ℝ} (hδ : 1 / 2 ≤ δ) {n : ℕ}
    (h : Realizable X δ n) : n ≤ 3 := by
  by_contra hn
  have hn4 : 4 ≤ n := by omega
  rcases h with ⟨c, P, hPinj, hPmem, hPsep⟩
  let e : Fin 4 → Fin n := fun i ↦ ⟨i.val, lt_of_lt_of_le i.isLt hn4⟩
  apply no_four_at_or_above_half hδ (P ∘ e)
  intro i j hij
  apply hPsep
  intro he
  apply hij
  exact Fin.ext (congrArg (fun x : Fin n ↦ x.val) he)

theorem N_le_three_at_or_above_half {δ : ℝ} (hδ : 1 / 2 ≤ δ) (X : ℝ) :
    N X δ ≤ 3 := by
  exact realizable_card_le_three hδ (N_realizable X (by linarith))

/-- Full parameter classification for the original non-strict E466 definition. -/
theorem erdos_466_parameter_classification {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun X : ℝ ↦ N X δ) atTop atTop ↔ δ < 1 / 2 := by
  constructor
  · intro ht
    by_contra hn
    have hd : 1 / 2 ≤ δ := le_of_not_gt hn
    obtain ⟨X, hX⟩ := ((tendsto_atTop.1 ht) 4).exists
    have := N_le_three_at_or_above_half hd X
    omega
  · exact N_tendsto_infinity hδ

/-- The original existence question follows from the stronger classification. -/
theorem erdos_466 : ∃ δ : ℝ, 0 < δ ∧
    Tendsto (fun X : ℝ ↦ N X δ) atTop atTop := by
  exact ⟨1 / 10, by norm_num, N_tendsto_infinity (by norm_num) (by norm_num)⟩

#print axioms erdos_466_parameter_classification
#print axioms erdos_466

end
end Erdos466General
