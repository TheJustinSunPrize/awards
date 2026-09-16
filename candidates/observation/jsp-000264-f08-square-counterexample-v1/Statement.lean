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

This worker package is an attributed adaptation of the public
FormalConjectures formulation of Erdős Problem 318.
-/

import Mathlib

open Set Real

namespace JSP000264

set_option autoImplicit false

/--
Property `P₁` from Sattler's formulation of Erdős Problem 318.
The function is defined on all naturals, but is compared on `A \ {0}`;
selected witnesses are finite nonempty subsets of that same set.
-/
def P₁ (A : Set ℕ) : Prop := ∀ (f : ℕ → ℝ),
  f ∘ (Subtype.val : (A \ {0} : Set ℕ) → ℕ) ≠ (fun _ => 1) →
  f ∘ (Subtype.val : (A \ {0} : Set ℕ) → ℕ) ≠ (fun _ => - 1) →
  Set.range f ⊆ {1, -1} →
  ∃ S : Finset ℕ, S.Nonempty ∧ ↑S ⊆ A \ {0} ∧ ∑ n ∈ S, f n / n = 0

/-- The square-set counterexample explicitly recorded for Problem 318. -/
def target : Prop := ¬ P₁ ({n : ℕ | IsSquare n})

end JSP000264
