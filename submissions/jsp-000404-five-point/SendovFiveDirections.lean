import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

/-!
A sharp necessary condition for five ordered planar-direction labels.
Generated finite case split; every leaf is checked by Lean's kernel.
This does not yet prove a theorem about actual planar point sets. In particular,
it assumes explicit direction-triple constraints and does not assert that
an arbitrary point configuration has been mapped to them.
-/
namespace SendovFiveDirections

def Triangle (t a b c : ℝ) : Prop :=
  (a ≤ b ∧ b ≤ c ∧ 1 ≤ c-a ∧ b-a ≤ t-1 ∧ c-b ≤ t-1) ∨
  (c ≤ b ∧ b ≤ a ∧ 1 ≤ a-c ∧ a-b ≤ t-1 ∧ b-c ≤ t-1)

set_option maxRecDepth 4096
set_option maxHeartbeats 20000000

theorem five_halves_le
    (t x01 x02 x03 x04 x12 x13 x14 x23 x24 x34 : ℝ)
    (r01 : 0 ≤ x01 ∧ x01 < t)
    (r02 : 0 ≤ x02 ∧ x02 < t)
    (r03 : 0 ≤ x03 ∧ x03 < t)
    (r04 : 0 ≤ x04 ∧ x04 < t)
    (r12 : 0 ≤ x12 ∧ x12 < t)
    (r13 : 0 ≤ x13 ∧ x13 < t)
    (r14 : 0 ≤ x14 ∧ x14 < t)
    (r23 : 0 ≤ x23 ∧ x23 < t)
    (r24 : 0 ≤ x24 ∧ x24 < t)
    (r34 : 0 ≤ x34 ∧ x34 < t)
    (h012 : Triangle t x01 x02 x12)
    (h013 : Triangle t x01 x03 x13)
    (h014 : Triangle t x01 x04 x14)
    (h023 : Triangle t x02 x03 x23)
    (h024 : Triangle t x02 x04 x24)
    (h034 : Triangle t x03 x04 x34)
    (h123 : Triangle t x12 x13 x23)
    (h124 : Triangle t x12 x14 x24)
    (h134 : Triangle t x13 x14 x34)
    (h234 : Triangle t x23 x24 x34)
    : 5 / 2 ≤ t := by
  by_contra hn
  have ht : t < 5 / 2 := lt_of_not_ge hn
  unfold Triangle at h012 h013 h014 h023 h024 h034 h123 h124 h134 h234
  rcases h012 with ⟨h012a, h012b, h012c, h012d, h012e⟩ | ⟨h012a, h012b, h012c, h012d, h012e⟩
  · rcases h013 with ⟨h013a, h013b, h013c, h013d, h013e⟩ | ⟨h013a, h013b, h013c, h013d, h013e⟩
    · rcases h014 with ⟨h014a, h014b, h014c, h014d, h014e⟩ | ⟨h014a, h014b, h014c, h014d, h014e⟩
      · rcases h023 with ⟨h023a, h023b, h023c, h023d, h023e⟩ | ⟨h023a, h023b, h023c, h023d, h023e⟩
        · rcases h024 with ⟨h024a, h024b, h024c, h024d, h024e⟩ | ⟨h024a, h024b, h024c, h024d, h024e⟩
          · rcases h034 with ⟨h034a, h034b, h034c, h034d, h034e⟩ | ⟨h034a, h034b, h034c, h034d, h034e⟩
            · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
              · rcases h124 with ⟨h124a, h124b, h124c, h124d, h124e⟩ | ⟨h124a, h124b, h124c, h124d, h124e⟩
                · rcases h134 with ⟨h134a, h134b, h134c, h134d, h134e⟩ | ⟨h134a, h134b, h134c, h134d, h134e⟩
                  · rcases h234 with ⟨h234a, h234b, h234c, h234d, h234e⟩ | ⟨h234a, h234b, h234c, h234d, h234e⟩
                    · linarith only [ht, r01.1, r34.2, h012c, h123c, h234c]
                    · linarith only [ht, h023e, h034c, h234c]
                  · linarith only [ht, r01.1, r13.2, h012c, h023e, h034c, h123c, h134c]
                · linarith only [ht, r02.1, r23.2, h024c, h123c, h124c]
              · linarith only [ht, h012e, h023c, h123c]
            · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
              · rcases h124 with ⟨h124a, h124b, h124c, h124d, h124e⟩ | ⟨h124a, h124b, h124c, h124d, h124e⟩
                · rcases h134 with ⟨h134a, h134b, h134c, h134d, h134e⟩ | ⟨h134a, h134b, h134c, h134d, h134e⟩
                  · linarith only [h013b, h034c, h134a, h134b]
                  · rcases h234 with ⟨h234a, h234b, h234c, h234d, h234e⟩ | ⟨h234a, h234b, h234c, h234d, h234e⟩
                    · linarith only [ht, r02.1, r23.2, h012c, h013d, h024c, h034c, h123c, h234b]
                    · linarith only [ht, h012c, h013d, h034c, h124c, h234e]
                · linarith only [ht, h012e, h024c, h124c]
              · linarith only [ht, h012e, h023c, h123c]
          · rcases h034 with ⟨h034a, h034b, h034c, h034d, h034e⟩ | ⟨h034a, h034b, h034c, h034d, h034e⟩
            · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
              · rcases h124 with ⟨h124a, h124b, h124c, h124d, h124e⟩ | ⟨h124a, h124b, h124c, h124d, h124e⟩
                · linarith only [ht, r01.1, r23.2, h012b, h014c, h024c, h123c, h124b]
                · rcases h134 with ⟨h134a, h134b, h134c, h134d, h134e⟩ | ⟨h134a, h134b, h134c, h134d, h134e⟩
                  · rcases h234 with ⟨h234a, h234b, h234c, h234d, h234e⟩ | ⟨h234a, h234b, h234c, h234d, h234e⟩
                    · linarith only [h012b, h024c, h123c, h234a]
                    · linarith only [ht, r03.1, r23.2, h012b, h024c, h034c, h123c, h234a]
                  · linarith only [ht, r23.2, r24.1, h023a, h024c, h034c, h123c, h124b, h134a]
              · linarith only [ht, r12.2, r24.1, h023c, h024c, h123c]
            · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
              · rcases h124 with ⟨h124a, h124b, h124c, h124d, h124e⟩ | ⟨h124a, h124b, h124c, h124d, h124e⟩
                · linarith only [ht, r01.1, r23.2, h012b, h014c, h024c, h124b, h123c]
                · rcases h134 with ⟨h134a, h134b, h134c, h134d, h134e⟩ | ⟨h134a, h134b, h134c, h134d, h134e⟩
                  · linarith only [h013b, h034c, h134a, h134b]
                  · rcases h234 with ⟨h234a, h234b, h234c, h234d, h234e⟩ | ⟨h234a, h234b, h234c, h234d, h234e⟩
                    · linarith only [ht, r01.1, r02.2, h012c, h024c, h123c, h234a]
                    · linarith only [ht, h012b, h024c, h123c, h234d]
              · linarith only [ht, r12.2, r24.1, h023c, h024c, h123c]
        · rcases h024 with ⟨h024a, h024b, h024c, h024d, h024e⟩ | ⟨h024a, h024b, h024c, h024d, h024e⟩
          · rcases h034 with ⟨h034a, h034b, h034c, h034d, h034e⟩ | ⟨h034a, h034b, h034c, h034d, h034e⟩
            · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
              · linarith only [ht, r01.1, r24.2, h013c, h023c, h024c, h123b]
              · rcases h124 with ⟨h124a, h124b, h124c, h124d, h124e⟩ | ⟨h124a, h124b, h124c, h124d, h124e⟩
                · rcases h134 with ⟨h134a, h134b, h134c, h134d, h134e⟩ | ⟨h134a, h134b, h134c, h134d, h134e⟩
                  · rcases h234 with ⟨h234a, h234b, h234c, h234d, h234e⟩ | ⟨h234a, h234b, h234c, h234d, h234e⟩
                    · linarith only [ht, h023c, h024c, h234d]
                    · linarith only [h023c, h024c, h234b]
                  · linarith only [ht, r03.1, r24.2, h034c, h123b, h124c, h134c]
                · linarith only [ht, h012e, h024c, h124c]
            · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
              · linarith only [h013b, h023c, h024a, h034b, h123b]
              · rcases h124 with ⟨h124a, h124b, h124c, h124d, h124e⟩ | ⟨h124a, h124b, h124c, h124d, h124e⟩
                · rcases h134 with ⟨h134a, h134b, h134c, h134d, h134e⟩ | ⟨h134a, h134b, h134c, h134d, h134e⟩
                  · linarith only [ht, h012c, h013d, h034c, h124a, h134b]
                  · rcases h234 with ⟨h234a, h234b, h234c, h234d, h234e⟩ | ⟨h234a, h234b, h234c, h234d, h234e⟩
                    · linarith only [h023b, h024b, h024a, h034c, h234b]
                    · linarith only [h023c, h024c, h234b]
                · linarith only [ht, r12.2, r23.1, h023c, h024c, h124c]
          · rcases h034 with ⟨h034a, h034b, h034c, h034d, h034e⟩ | ⟨h034a, h034b, h034c, h034d, h034e⟩
            · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
              · linarith only [h012b, h023c, h123a, h123b]
              · rcases h124 with ⟨h124a, h124b, h124c, h124d, h124e⟩ | ⟨h124a, h124b, h124c, h124d, h124e⟩
                · linarith only [ht, h012d, h014c, h024c, h124b]
                · rcases h134 with ⟨h134a, h134b, h134c, h134d, h134e⟩ | ⟨h134a, h134b, h134c, h134d, h134e⟩
                  · rcases h234 with ⟨h234a, h234b, h234c, h234d, h234e⟩ | ⟨h234a, h234b, h234c, h234d, h234e⟩
                    · linarith only [ht, h012d, h013c, h024c, h234e, h134c]
                    · linarith only [ht, h012d, h013c, h024c, h134c, h234a]
                  · linarith only [ht, h013e, h034c, h134c]
            · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
              · linarith only [ht, h012d, h013c, h023c, h123b]
              · rcases h124 with ⟨h124a, h124b, h124c, h124d, h124e⟩ | ⟨h124a, h124b, h124c, h124d, h124e⟩
                · linarith only [h012b, h024c, h124a, h124b]
                · rcases h134 with ⟨h134a, h134b, h134c, h134d, h134e⟩ | ⟨h134a, h134b, h134c, h134d, h134e⟩
                  · linarith only [ht, h013d, h014c, h034c, h134b]
                  · rcases h234 with ⟨h234a, h234b, h234c, h234d, h234e⟩ | ⟨h234a, h234b, h234c, h234d, h234e⟩
                    · linarith only [ht, h023e, h034c, h234c]
                    · linarith only [ht, h012d, h014c, h023c, h134e, h234c]
      · rcases h023 with ⟨h023a, h023b, h023c, h023d, h023e⟩ | ⟨h023a, h023b, h023c, h023d, h023e⟩
        · rcases h024 with ⟨h024a, h024b, h024c, h024d, h024e⟩ | ⟨h024a, h024b, h024c, h024d, h024e⟩
          · rcases h034 with ⟨h034a, h034b, h034c, h034d, h034e⟩ | ⟨h034a, h034b, h034c, h034d, h034e⟩
            · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
              · linarith only [ht, r14.1, r23.2, h012c, h014c, h123c]
              · linarith only [ht, h012a, r12.2, r14.1, h014c, h023c, h123c]
            · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
              · linarith only [ht, r14.1, r23.2, h012c, h014c, h123c]
              · linarith only [ht, h012a, r12.2, r14.1, h014c, h023c, h123c]
          · rcases h034 with ⟨h034a, h034b, h034c, h034d, h034e⟩ | ⟨h034a, h034b, h034c, h034d, h034e⟩
            · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
              · linarith only [ht, r14.1, r23.2, h012c, h014c, h123c]
              · linarith only [ht, h012a, r12.2, r14.1, h014c, h023c, h123c]
            · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
              · linarith only [ht, r14.1, r23.2, h012c, h014c, h123c]
              · linarith only [ht, h012a, r12.2, r14.1, h014c, h023c, h123c]
        · rcases h024 with ⟨h024a, h024b, h024c, h024d, h024e⟩ | ⟨h024a, h024b, h024c, h024d, h024e⟩
          · rcases h034 with ⟨h034a, h034b, h034c, h034d, h034e⟩ | ⟨h034a, h034b, h034c, h034d, h034e⟩
            · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
              · linarith only [h012b, h123a, h023c, h123b]
              · linarith only [ht, h013c, h014b, h024a, h023c, h123e]
            · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
              · linarith only [h013c, h014b, h024a, h123b, h023c]
              · linarith only [ht, h013c, h014b, h024a, h123e, h023c]
          · rcases h034 with ⟨h034a, h034b, h034c, h034d, h034e⟩ | ⟨h034a, h034b, h034c, h034d, h034e⟩
            · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
              · linarith only [ht, r02.2, r14.1, h013c, h014c, h123b, h023c]
              · rcases h124 with ⟨h124a, h124b, h124c, h124d, h124e⟩ | ⟨h124a, h124b, h124c, h124d, h124e⟩
                · linarith only [h012a, h012b, h014c, h124a]
                · linarith only [ht, h012c, h014c, h124d]
            · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
              · linarith only [ht, r02.2, r14.1, h013c, h014c, h023c, h123b]
              · rcases h124 with ⟨h124a, h124b, h124c, h124d, h124e⟩ | ⟨h124a, h124b, h124c, h124d, h124e⟩
                · linarith only [h012a, h012b, h014c, h124a]
                · linarith only [ht, h012c, h014c, h124d]
    · rcases h014 with ⟨h014a, h014b, h014c, h014d, h014e⟩ | ⟨h014a, h014b, h014c, h014d, h014e⟩
      · rcases h023 with ⟨h023a, h023b, h023c, h023d, h023e⟩ | ⟨h023a, h023b, h023c, h023d, h023e⟩
        · rcases h024 with ⟨h024a, h024b, h024c, h024d, h024e⟩ | ⟨h024a, h024b, h024c, h024d, h024e⟩
          · rcases h034 with ⟨h034a, h034b, h034c, h034d, h034e⟩ | ⟨h034a, h034b, h034c, h034d, h034e⟩
            · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
              · linarith only [h012c, h013c, h123a]
              · linarith only [ht, r02.1, r12.2, h012c, h013c, h023c, h123a]
            · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
              · linarith only [h012a, h012b, h013c, h123a]
              · linarith only [h012a, h013c, h023c, h123a]
          · rcases h034 with ⟨h034a, h034b, h034c, h034d, h034e⟩ | ⟨h034a, h034b, h034c, h034d, h034e⟩
            · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
              · linarith only [h012c, h013c, h123a]
              · linarith only [h012a, h013c, h023c, h123a]
            · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
              · linarith only [h012c, h013c, h123a]
              · linarith only [h012a, h013c, h023c, h123a]
        · rcases h024 with ⟨h024a, h024b, h024c, h024d, h024e⟩ | ⟨h024a, h024b, h024c, h024d, h024e⟩
          · rcases h034 with ⟨h034a, h034b, h034c, h034d, h034e⟩ | ⟨h034a, h034b, h034c, h034d, h034e⟩
            · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
              · linarith only [h012c, h013c, h123a]
              · linarith only [ht, h012c, h013c, h123d]
            · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
              · linarith only [h012c, h013c, h123a]
              · linarith only [ht, h012c, h013c, h123d]
          · rcases h034 with ⟨h034a, h034b, h034c, h034d, h034e⟩ | ⟨h034a, h034b, h034c, h034d, h034e⟩
            · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
              · linarith only [h012c, h013c, h123a]
              · linarith only [ht, h012c, h013c, h123d]
            · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
              · linarith only [h012c, h013c, h123a]
              · linarith only [ht, h012c, h013c, h123d]
      · rcases h023 with ⟨h023a, h023b, h023c, h023d, h023e⟩ | ⟨h023a, h023b, h023c, h023d, h023e⟩
        · rcases h024 with ⟨h024a, h024b, h024c, h024d, h024e⟩ | ⟨h024a, h024b, h024c, h024d, h024e⟩
          · rcases h034 with ⟨h034a, h034b, h034c, h034d, h034e⟩ | ⟨h034a, h034b, h034c, h034d, h034e⟩
            · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
              · linarith only [h012c, h013c, h123a]
              · linarith only [h012a, h013c, h023c, h123a]
            · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
              · linarith only [h012c, h013c, h123a]
              · linarith only [h012a, h013c, h023c, h123a]
          · rcases h034 with ⟨h034a, h034b, h034c, h034d, h034e⟩ | ⟨h034a, h034b, h034c, h034d, h034e⟩
            · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
              · linarith only [h012c, h013c, h123a]
              · linarith only [h012a, h013c, h023c, h123a]
            · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
              · linarith only [h012c, h013c, h123a]
              · linarith only [h012a, h013c, h123a, h023c]
        · rcases h024 with ⟨h024a, h024b, h024c, h024d, h024e⟩ | ⟨h024a, h024b, h024c, h024d, h024e⟩
          · rcases h034 with ⟨h034a, h034b, h034c, h034d, h034e⟩ | ⟨h034a, h034b, h034c, h034d, h034e⟩
            · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
              · linarith only [h012c, h013c, h123a]
              · linarith only [ht, h012c, h013c, h123d]
            · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
              · linarith only [h012c, h013c, h123a]
              · linarith only [ht, h012c, h013c, h123d]
          · rcases h034 with ⟨h034a, h034b, h034c, h034d, h034e⟩ | ⟨h034a, h034b, h034c, h034d, h034e⟩
            · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
              · linarith only [h012c, h013c, h123a]
              · linarith only [ht, h012c, h013c, h123d]
            · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
              · linarith only [h012c, h013c, h123a]
              · linarith only [ht, h012c, h013c, h123d]
  · rcases h013 with ⟨h013a, h013b, h013c, h013d, h013e⟩ | ⟨h013a, h013b, h013c, h013d, h013e⟩
    · rcases h014 with ⟨h014a, h014b, h014c, h014d, h014e⟩ | ⟨h014a, h014b, h014c, h014d, h014e⟩
      · rcases h023 with ⟨h023a, h023b, h023c, h023d, h023e⟩ | ⟨h023a, h023b, h023c, h023d, h023e⟩
        · rcases h024 with ⟨h024a, h024b, h024c, h024d, h024e⟩ | ⟨h024a, h024b, h024c, h024d, h024e⟩
          · rcases h034 with ⟨h034a, h034b, h034c, h034d, h034e⟩ | ⟨h034a, h034b, h034c, h034d, h034e⟩
            · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
              · linarith only [ht, h012c, h013c, h123d]
              · linarith only [h012c, h013c, h123b]
            · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
              · linarith only [ht, h012c, h013c, h123d]
              · linarith only [h012c, h013c, h123b]
          · rcases h034 with ⟨h034a, h034b, h034c, h034d, h034e⟩ | ⟨h034a, h034b, h034c, h034d, h034e⟩
            · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
              · linarith only [ht, h012c, h013c, h123d]
              · linarith only [h012c, h013c, h123b]
            · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
              · linarith only [ht, h012c, h013c, h123d]
              · linarith only [h012c, h013c, h123b]
        · rcases h024 with ⟨h024a, h024b, h024c, h024d, h024e⟩ | ⟨h024a, h024b, h024c, h024d, h024e⟩
          · rcases h034 with ⟨h034a, h034b, h034c, h034d, h034e⟩ | ⟨h034a, h034b, h034c, h034d, h034e⟩
            · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
              · linarith only [ht, r02.2, r12.1, h012c, h013c, h023c, h123b]
              · linarith only [h012c, h013c, h123b]
            · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
              · linarith only [h012b, h013c, h123b, h023c]
              · linarith only [h012c, h013c, h123b]
          · rcases h034 with ⟨h034a, h034b, h034c, h034d, h034e⟩ | ⟨h034a, h034b, h034c, h034d, h034e⟩
            · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
              · linarith only [h012b, h013c, h123b, h023c]
              · linarith only [h012c, h013c, h123b]
            · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
              · linarith only [h012b, h013c, h123b, h023c]
              · linarith only [h012c, h013c, h123b]
      · rcases h023 with ⟨h023a, h023b, h023c, h023d, h023e⟩ | ⟨h023a, h023b, h023c, h023d, h023e⟩
        · rcases h024 with ⟨h024a, h024b, h024c, h024d, h024e⟩ | ⟨h024a, h024b, h024c, h024d, h024e⟩
          · rcases h034 with ⟨h034a, h034b, h034c, h034d, h034e⟩ | ⟨h034a, h034b, h034c, h034d, h034e⟩
            · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
              · linarith only [ht, h012c, h013c, h123d]
              · linarith only [h012c, h013c, h123b]
            · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
              · linarith only [ht, h012c, h013c, h123d]
              · linarith only [h012c, h013c, h123b]
          · rcases h034 with ⟨h034a, h034b, h034c, h034d, h034e⟩ | ⟨h034a, h034b, h034c, h034d, h034e⟩
            · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
              · linarith only [ht, h012c, h013c, h123d]
              · linarith only [h012c, h013c, h123b]
            · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
              · linarith only [ht, h012c, h013c, h123d]
              · linarith only [h012c, h013c, h123b]
        · rcases h024 with ⟨h024a, h024b, h024c, h024d, h024e⟩ | ⟨h024a, h024b, h024c, h024d, h024e⟩
          · rcases h034 with ⟨h034a, h034b, h034c, h034d, h034e⟩ | ⟨h034a, h034b, h034c, h034d, h034e⟩
            · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
              · linarith only [h012b, h013c, h023c, h123b]
              · linarith only [h012c, h013c, h123b]
            · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
              · linarith only [h012b, h013c, h023c, h123b]
              · linarith only [h012c, h013c, h123b]
          · rcases h034 with ⟨h034a, h034b, h034c, h034d, h034e⟩ | ⟨h034a, h034b, h034c, h034d, h034e⟩
            · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
              · linarith only [h012b, h013c, h023c, h123b]
              · linarith only [h012c, h013c, h123b]
            · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
              · linarith only [h012b, h013c, h023c, h123b]
              · linarith only [h012c, h013c, h123b]
    · rcases h014 with ⟨h014a, h014b, h014c, h014d, h014e⟩ | ⟨h014a, h014b, h014c, h014d, h014e⟩
      · rcases h023 with ⟨h023a, h023b, h023c, h023d, h023e⟩ | ⟨h023a, h023b, h023c, h023d, h023e⟩
        · rcases h024 with ⟨h024a, h024b, h024c, h024d, h024e⟩ | ⟨h024a, h024b, h024c, h024d, h024e⟩
          · rcases h034 with ⟨h034a, h034b, h034c, h034d, h034e⟩ | ⟨h034a, h034b, h034c, h034d, h034e⟩
            · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
              · rcases h124 with ⟨h124a, h124b, h124c, h124d, h124e⟩ | ⟨h124a, h124b, h124c, h124d, h124e⟩
                · linarith only [ht, h012c, h014c, h124d]
                · linarith only [h012c, h014c, h124b]
              · linarith only [ht, r02.1, r14.2, h013c, h014c, h023c, h123a]
            · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
              · rcases h124 with ⟨h124a, h124b, h124c, h124d, h124e⟩ | ⟨h124a, h124b, h124c, h124d, h124e⟩
                · linarith only [ht, h012c, h014c, h124d]
                · linarith only [h012c, h014c, h124b]
              · linarith only [ht, r02.1, r14.2, h013c, h014c, h023c, h123a]
          · rcases h034 with ⟨h034a, h034b, h034c, h034d, h034e⟩ | ⟨h034a, h034b, h034c, h034d, h034e⟩
            · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
              · linarith only [ht, h014a, h013c, h024b, h023c, h123e]
              · linarith only [h014a, h013c, h024b, h023c, h123a]
            · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
              · linarith only [ht, h014a, h013c, h024b, h023c, h123e]
              · linarith only [h014a, h013c, h024b, h023c, h123a]
        · rcases h024 with ⟨h024a, h024b, h024c, h024d, h024e⟩ | ⟨h024a, h024b, h024c, h024d, h024e⟩
          · rcases h034 with ⟨h034a, h034b, h034c, h034d, h034e⟩ | ⟨h034a, h034b, h034c, h034d, h034e⟩
            · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
              · linarith only [ht, r12.1, r24.2, h023c, h024c, h123c]
              · linarith only [ht, r14.2, r23.1, h012c, h014c, h123c]
            · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
              · linarith only [ht, r12.1, r24.2, h123c, h023c, h024c]
              · linarith only [ht, r14.2, r23.1, h012c, h014c, h123c]
          · rcases h034 with ⟨h034a, h034b, h034c, h034d, h034e⟩ | ⟨h034a, h034b, h034c, h034d, h034e⟩
            · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
              · linarith only [ht, r12.1, r14.2, h012b, h014c, h023c, h123c]
              · linarith only [ht, r14.2, r23.1, h012c, h123c, h014c]
            · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
              · linarith only [ht, r12.1, r14.2, h012b, h014c, h023c, h123c]
              · linarith only [ht, r14.2, r23.1, h012c, h014c, h123c]
      · rcases h023 with ⟨h023a, h023b, h023c, h023d, h023e⟩ | ⟨h023a, h023b, h023c, h023d, h023e⟩
        · rcases h024 with ⟨h024a, h024b, h024c, h024d, h024e⟩ | ⟨h024a, h024b, h024c, h024d, h024e⟩
          · rcases h034 with ⟨h034a, h034b, h034c, h034d, h034e⟩ | ⟨h034a, h034b, h034c, h034d, h034e⟩
            · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
              · rcases h124 with ⟨h124a, h124b, h124c, h124d, h124e⟩ | ⟨h124a, h124b, h124c, h124d, h124e⟩
                · rcases h134 with ⟨h134a, h134b, h134c, h134d, h134e⟩ | ⟨h134a, h134b, h134c, h134d, h134e⟩
                  · rcases h234 with ⟨h234a, h234b, h234c, h234d, h234e⟩ | ⟨h234a, h234b, h234c, h234d, h234e⟩
                    · linarith only [ht, h012d, h014c, h023c, h134e, h234c]
                    · linarith only [ht, h023e, h034c, h234c]
                  · linarith only [ht, h013d, h014c, h034c, h134a]
                · linarith only [ht, h012d, h014c, h024c, h124a]
              · linarith only [ht, h012d, h013c, h023c, h123a]
            · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
              · rcases h124 with ⟨h124a, h124b, h124c, h124d, h124e⟩ | ⟨h124a, h124b, h124c, h124d, h124e⟩
                · rcases h134 with ⟨h134a, h134b, h134c, h134d, h134e⟩ | ⟨h134a, h134b, h134c, h134d, h134e⟩
                  · linarith only [ht, h013e, h034c, h134c]
                  · rcases h234 with ⟨h234a, h234b, h234c, h234d, h234e⟩ | ⟨h234a, h234b, h234c, h234d, h234e⟩
                    · linarith only [ht, h012d, h013a, h013b, h024c, h234b, h134c]
                    · linarith only [ht, h012d, h013c, h024c, h234e, h134c]
                · linarith only [ht, h012d, h014c, h024c, h124a]
              · linarith only [ht, h012d, h013c, h023c, h123a]
          · rcases h034 with ⟨h034a, h034b, h034c, h034d, h034e⟩ | ⟨h034a, h034b, h034c, h034d, h034e⟩
            · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
              · rcases h124 with ⟨h124a, h124b, h124c, h124d, h124e⟩ | ⟨h124a, h124b, h124c, h124d, h124e⟩
                · linarith only [ht, r12.1, r23.2, h024c, h023c, h124c]
                · rcases h134 with ⟨h134a, h134b, h134c, h134d, h134e⟩ | ⟨h134a, h134b, h134c, h134d, h134e⟩
                  · rcases h234 with ⟨h234a, h234b, h234c, h234d, h234e⟩ | ⟨h234a, h234b, h234c, h234d, h234e⟩
                    · linarith only [h012a, h023c, h234a, h124c]
                    · linarith only [h012a, h023a, h034c, h124c, h234a]
                  · linarith only [ht, r01.2, r24.1, h012a, h014c, h023a, h034c, h134a, h124c]
              · linarith only [ht, r24.1, r34.2, h013a, h024c, h023c, h123a, h034c]
            · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
              · rcases h124 with ⟨h124a, h124b, h124c, h124d, h124e⟩ | ⟨h124a, h124b, h124c, h124d, h124e⟩
                · linarith only [ht, r12.1, r23.2, h024c, h023c, h124c]
                · rcases h134 with ⟨h134a, h134b, h134c, h134d, h134e⟩ | ⟨h134a, h134b, h134c, h134d, h134e⟩
                  · linarith only [ht, h013e, h134c, h034c]
                  · rcases h234 with ⟨h234a, h234b, h234c, h234d, h234e⟩ | ⟨h234a, h234b, h234c, h234d, h234e⟩
                    · linarith only [h012a, h023c, h124c, h234a]
                    · linarith only [ht, h012a, h023c, h124c, h234d]
              · linarith only [ht, r01.2, r24.1, h013c, h024c, h023c, h123a]
        · rcases h024 with ⟨h024a, h024b, h024c, h024d, h024e⟩ | ⟨h024a, h024b, h024c, h024d, h024e⟩
          · rcases h034 with ⟨h034a, h034b, h034c, h034d, h034e⟩ | ⟨h034a, h034b, h034c, h034d, h034e⟩
            · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
              · linarith only [ht, r12.1, r24.2, h023c, h024c, h123c]
              · rcases h124 with ⟨h124a, h124b, h124c, h124d, h124e⟩ | ⟨h124a, h124b, h124c, h124d, h124e⟩
                · rcases h134 with ⟨h134a, h134b, h134c, h134d, h134e⟩ | ⟨h134a, h134b, h134c, h134d, h134e⟩
                  · rcases h234 with ⟨h234a, h234b, h234c, h234d, h234e⟩ | ⟨h234a, h234b, h234c, h234d, h234e⟩
                    · linarith only [ht, h012a, h024c, h123c, h234d]
                    · linarith only [h012a, h024c, h234b, h123c]
                  · linarith only [ht, h013d, h014c, h034c, h134a]
                · linarith only [ht, r01.2, r23.1, h012a, h014c, h024c, h124a, h123c]
            · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
              · linarith only [ht, r12.1, r24.2, h023c, h123c, h024c]
              · rcases h124 with ⟨h124a, h124b, h124c, h124d, h124e⟩ | ⟨h124a, h124b, h124c, h124d, h124e⟩
                · rcases h134 with ⟨h134a, h134b, h134c, h134d, h134e⟩ | ⟨h134a, h134b, h134c, h134d, h134e⟩
                  · linarith only [ht, r23.1, r24.2, h023b, h024c, h123c, h034c, h124a, h134b]
                  · rcases h234 with ⟨h234a, h234b, h234c, h234d, h234e⟩ | ⟨h234a, h234b, h234c, h234d, h234e⟩
                    · linarith only [ht, r13.2, r23.1, h012a, h024c, h123c, h134c, h234b]
                    · linarith only [h012a, h024c, h123c, h234b]
                · linarith only [ht, r01.2, r23.1, h012a, h014c, h124a, h024c, h123c]
          · rcases h034 with ⟨h034a, h034b, h034c, h034d, h034e⟩ | ⟨h034a, h034b, h034c, h034d, h034e⟩
            · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
              · linarith only [ht, h012e, h023c, h123c]
              · rcases h124 with ⟨h124a, h124b, h124c, h124d, h124e⟩ | ⟨h124a, h124b, h124c, h124d, h124e⟩
                · linarith only [ht, r02.2, r23.1, h024c, h123c, h124c]
                · rcases h134 with ⟨h134a, h134b, h134c, h134d, h134e⟩ | ⟨h134a, h134b, h134c, h134d, h134e⟩
                  · rcases h234 with ⟨h234a, h234b, h234c, h234d, h234e⟩ | ⟨h234a, h234b, h234c, h234d, h234e⟩
                    · linarith only [ht, h012c, h013d, h124c, h034c, h234e]
                    · linarith only [ht, h012c, h013d, h124c, h034c, h234a]
                  · linarith only [ht, h012c, h013d, h034c, h124b, h134a]
            · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
              · linarith only [ht, h012e, h023c, h123c]
              · rcases h124 with ⟨h124a, h124b, h124c, h124d, h124e⟩ | ⟨h124a, h124b, h124c, h124d, h124e⟩
                · linarith only [ht, r02.2, r23.1, h024c, h124c, h123c]
                · rcases h134 with ⟨h134a, h134b, h134c, h134d, h134e⟩ | ⟨h134a, h134b, h134c, h134d, h134e⟩
                  · linarith only [ht, h013e, h034c, h134c]
                  · rcases h234 with ⟨h234a, h234b, h234c, h234d, h234e⟩ | ⟨h234a, h234b, h234c, h234d, h234e⟩
                    · linarith only [ht, h013a, h023e, h234c, h134c]
                    · linarith only [ht, r01.2, r34.1, h012c, h123c, h234c]

#print axioms five_halves_le
end SendovFiveDirections
