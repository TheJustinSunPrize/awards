/-
Copyright 2026 The Formal Conjectures Authors.
Copyright 2026 James-16.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.

The definition Erdos120For and the finite-set target follow Formal Conjectures
at 40e7c98697de6f66b8cbdbf641749ab39ed9c152. Proofs in this file were developed
with substantial OpenAI Codex assistance. The mathematical result is known
and is commonly attributed to Steinhaus (1920).
-/

import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic.Push

open Set MeasureTheory Filter
open scoped Topology Pointwise

namespace Erdos120FinitePatterns

/-- A compact set of positive measure contains a homothetic copy of every finite pattern. -/
theorem compact_finite_pattern (A : Finset ℝ) {K : Set ℝ}
    (hK : IsCompact K) (hpos : 0 < volume K) :
    ∃ t > (0 : ℝ), ∃ b : ℝ, ∀ x ∈ A, t * x + b ∈ K := by
  classical
  have hlim : ∀ x : ℝ, Tendsto (fun t : ℝ ↦ volume (((t * x) +ᵥ K) \ K))
      (𝓝 0) (𝓝 0) := by
    intro x
    have hc : Tendsto (fun t : ℝ ↦ t * x) (𝓝 0) (𝓝 0) := by
      have hc0 : Continuous (fun t : ℝ ↦ t * x) := continuous_id.mul_const x
      simpa only [zero_mul] using hc0.tendsto 0
    exact (tendsto_measure_vadd_sdiff_isCompact_isClosed (μ := volume) hK hK.isClosed).comp hc
  have hsum : Tendsto (fun t : ℝ ↦ ∑ x ∈ A, volume (((t * x) +ᵥ K) \ K))
      (𝓝 0) (𝓝 0) := by
    simpa using tendsto_finsetSum A (fun x _ ↦ hlim x)
  have hevent : ∀ᶠ t : ℝ in 𝓝 0, (∑ x ∈ A, volume (((t * x) +ᵥ K) \ K)) < volume K :=
    hsum.eventually (gt_mem_nhds hpos)
  have hwithin : ∀ᶠ t : ℝ in 𝓝[>] 0,
      (∑ x ∈ A, volume (((t * x) +ᵥ K) \ K)) < volume K :=
    hevent.filter_mono inf_le_left
  obtain ⟨t, ht, htpos⟩ := (hwithin.and self_mem_nhdsWithin).exists
  refine ⟨t, htpos, ?_⟩
  by_contra h
  push Not at h
  let B : ℝ → Set ℝ := fun x ↦ (fun b : ℝ ↦ t * x + b) ⁻¹' (((t * x) +ᵥ K) \ K)
  have hcover : K ⊆ ⋃ x ∈ A, B x := by
    intro b hb
    obtain ⟨x, hx, hbad⟩ := h b
    apply mem_iUnion.mpr
    refine ⟨x, mem_iUnion.mpr ⟨hx, ?_⟩⟩
    exact ⟨⟨b, hb, rfl⟩, hbad⟩
  have hle : volume K ≤ ∑ x ∈ A, volume (((t * x) +ᵥ K) \ K) := by
    calc
      volume K ≤ volume (⋃ x ∈ A, B x) := measure_mono hcover
      _ ≤ ∑ x ∈ A, volume (B x) := measure_biUnion_finset_le _ _
      _ = ∑ x ∈ A, volume (((t * x) +ᵥ K) \ K) := by
        simp only [B, measure_preimage_add]
  exact (not_lt_of_ge hle) ht

/-- The finite-set variant of Erdős 120, attributed to Steinhaus (1920). -/
theorem finite_pattern {A E : Set ℝ} (hA : A.Finite) (hE : MeasurableSet E)
    (hpos : 0 < volume E) :
    ∃ t > (0 : ℝ), ∃ b : ℝ, (fun x ↦ t * x + b) '' A ⊆ E := by
  obtain ⟨K, hKE, hK, hKpos⟩ := hE.exists_lt_isCompact hpos
  obtain ⟨t, ht, b, hb⟩ := compact_finite_pattern hA.toFinset hK hKpos
  refine ⟨t, ht, b, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  exact hKE (hb x (hA.mem_toFinset.mpr hx))

def Erdos120For (A : Set ℝ) : Prop := ∃ E : Set ℝ,
  MeasurableSet E ∧ 0 < volume E ∧
    ∀ a b : ℝ, a ≠ 0 → ¬ (fun x ↦ a * x + b) '' A ⊆ E

theorem finite_set {A : Set ℝ} (h : A.Finite) : ¬ Erdos120For A := by
  rintro ⟨E, hE, hpos, havoid⟩
  obtain ⟨a, ha, b, hab⟩ := finite_pattern h hE hpos
  exact havoid a b ha.ne' hab

end Erdos120FinitePatterns
