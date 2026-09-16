/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.

This worker package is an attributed adaptation of the public proof of the
square-set variant of Erdős Problem 318.
-/

import Statement

open Set Real

namespace JSP000264

set_option autoImplicit false

/--
A source-faithful proof of the square-set counterexample for Erdős Problem 318.
The signing is `+1` at `1` and `-1` elsewhere.  If `1` is absent, the
finite sum is negative.  If `1` is present, the square reciprocals other than
`1` have total sum strictly less than `1`, so the finite sum is positive.
-/
theorem solution : target := by
  change ¬ P₁ ({n : ℕ | IsSquare n})
  simp only [P₁, not_forall, not_exists, not_and]
  refine ⟨fun n => if n = 1 then 1 else - 1, fun h => ?_, fun h => ?_,
    fun x ⟨y, hy⟩ => ?_, fun S h hs => ?_⟩
  · have : (- 1 : ℝ) = 1 := by
      simpa using congr_fun h ⟨4, ⟨⟨2, by grind⟩, by grind⟩⟩
    grind
  · have : 1 = (- 1 : ℝ) := by
      simpa using congr_fun h ⟨1, ⟨IsSquare.one, by grind⟩⟩
    grind
  · by_cases x = 1 <;> grind
  by_cases h1 : 1 ∈ S
  · rw [Finset.sum_eq_add_sum_sdiff_singleton 1 _ (by simp [h1]),
      Finset.sum_congr rfl (g := fun n : ℕ => (- 1 : ℝ) / n)]
    · simp only [↓reduceIte, Nat.cast_one, div_self one_ne_zero, ← ne_eq,
        div_eq_mul_one_div (- 1 : ℝ), ← Finset.mul_sum,
        neg_one_mul (∑ x ∈ S \ {1}, 1 / (x : ℝ)), ← sub_eq_add_neg]
      apply ne_of_gt
      calc
      _ < 1 - (π ^ 2 / 6 - 1) := by
        have : π ^ 2 < 3.15 ^ 2 := by gcongr; exact Real.pi_lt_d2
        linarith
      _ = 1 - (∑' n : ℕ, 1 / (n : ℝ) ^ 2 - 1) := by
        congr
        exact hasSum_zeta_two.tsum_eq.symm
      _ ≤ 1 - ∑ n ∈ S \ {1}, 1 / (n : ℝ) := by
        gcongr
        have : 1 = 1 / ((1 : ℕ) : ℝ) := by norm_cast; grind
        nth_rewrite 3 [this]
        rw [le_sub_iff_add_le, ← Finset.sum_eq_sum_sdiff_singleton_add h1]
        let S' := S.preimage (· ^ 2)
          (Function.Injective.injOn (Nat.pow_left_injective (by decide)))
        have hS' : S'.map ⟨(· ^ 2), Nat.pow_left_injective (by decide)⟩ = S := by
          apply Finset.coe_injective
          have h : (S : Set ℕ) ⊆ Set.range (· ^ 2) :=
            hs.trans (by simp [isSquare_iff_exists_sq, Set.subset_def])
          simpa [S', Set.image_preimage_eq_iff] using h
        rw [← hS', Finset.sum_map, Function.Embedding.coeFn_mk]
        simpa [Nat.cast_pow] using
          Summable.sum_le_tsum S' (fun _ _ => by positivity) (by simp)
    · intro _ _
      grind
  · suffices ∑ n ∈ S, (fun n ↦ if n = 1 then 1 else - 1) n / (n : ℝ) < 0 from by
      linarith
    refine Finset.sum_neg (fun p hp => ?_) h
    have : p ≠ 1 := by grind
    simp_all [neg_div, zero_lt_iff, (not_iff_not.2 mem_singleton_iff).1 (hs hp).2]

#print axioms solution

end JSP000264
