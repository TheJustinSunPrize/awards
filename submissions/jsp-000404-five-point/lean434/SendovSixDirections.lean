import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

/-!
A sharp necessary condition for six ordered planar-direction labels.
Generated finite case split; every leaf is checked by Lean's kernel.
This does not yet prove a theorem about actual planar point sets. In particular,
it assumes explicit direction-triple constraints and does not assert that
an arbitrary point configuration has been mapped to them.
-/
namespace SendovSixDirections

def Triangle (t a b c : ℝ) : Prop :=
  (a ≤ b ∧ b ≤ c ∧ 1 ≤ c-a ∧ b-a ≤ t-1 ∧ c-b ≤ t-1) ∨
  (c ≤ b ∧ b ≤ a ∧ 1 ≤ a-c ∧ a-b ≤ t-1 ∧ b-c ≤ t-1)

set_option maxRecDepth 4096
set_option maxHeartbeats 20000000

theorem three_le
    (t x01 x02 x03 x04 x05 x12 x13 x14 x15 x23 x24 x25 x34 x35 x45 : ℝ)
    (r01 : 0 ≤ x01 ∧ x01 < t)
    (r02 : 0 ≤ x02 ∧ x02 < t)
    (r03 : 0 ≤ x03 ∧ x03 < t)
    (r04 : 0 ≤ x04 ∧ x04 < t)
    (r05 : 0 ≤ x05 ∧ x05 < t)
    (r12 : 0 ≤ x12 ∧ x12 < t)
    (r13 : 0 ≤ x13 ∧ x13 < t)
    (r14 : 0 ≤ x14 ∧ x14 < t)
    (r15 : 0 ≤ x15 ∧ x15 < t)
    (r23 : 0 ≤ x23 ∧ x23 < t)
    (r24 : 0 ≤ x24 ∧ x24 < t)
    (r25 : 0 ≤ x25 ∧ x25 < t)
    (r34 : 0 ≤ x34 ∧ x34 < t)
    (r35 : 0 ≤ x35 ∧ x35 < t)
    (r45 : 0 ≤ x45 ∧ x45 < t)
    (h012 : Triangle t x01 x02 x12)
    (h013 : Triangle t x01 x03 x13)
    (h014 : Triangle t x01 x04 x14)
    (h015 : Triangle t x01 x05 x15)
    (h023 : Triangle t x02 x03 x23)
    (h024 : Triangle t x02 x04 x24)
    (h025 : Triangle t x02 x05 x25)
    (h034 : Triangle t x03 x04 x34)
    (h035 : Triangle t x03 x05 x35)
    (h045 : Triangle t x04 x05 x45)
    (h123 : Triangle t x12 x13 x23)
    (h124 : Triangle t x12 x14 x24)
    (h125 : Triangle t x12 x15 x25)
    (h134 : Triangle t x13 x14 x34)
    (h135 : Triangle t x13 x15 x35)
    (h145 : Triangle t x14 x15 x45)
    (h234 : Triangle t x23 x24 x34)
    (h235 : Triangle t x23 x25 x35)
    (h245 : Triangle t x24 x25 x45)
    (h345 : Triangle t x34 x35 x45)
    : 3 ≤ t := by
  by_contra hn
  have ht : t < 3 := lt_of_not_ge hn
  unfold Triangle at h012 h013 h014 h015 h023 h024 h025 h034 h035 h045 h123 h124 h125 h134 h135 h145 h234 h235 h245 h345
  rcases h012 with ⟨h012a, h012b, h012c, h012d, h012e⟩ | ⟨h012a, h012b, h012c, h012d, h012e⟩
  · rcases h013 with ⟨h013a, h013b, h013c, h013d, h013e⟩ | ⟨h013a, h013b, h013c, h013d, h013e⟩
    · rcases h014 with ⟨h014a, h014b, h014c, h014d, h014e⟩ | ⟨h014a, h014b, h014c, h014d, h014e⟩
      · rcases h015 with ⟨h015a, h015b, h015c, h015d, h015e⟩ | ⟨h015a, h015b, h015c, h015d, h015e⟩
        · rcases h023 with ⟨h023a, h023b, h023c, h023d, h023e⟩ | ⟨h023a, h023b, h023c, h023d, h023e⟩
          · rcases h024 with ⟨h024a, h024b, h024c, h024d, h024e⟩ | ⟨h024a, h024b, h024c, h024d, h024e⟩
            · rcases h025 with ⟨h025a, h025b, h025c, h025d, h025e⟩ | ⟨h025a, h025b, h025c, h025d, h025e⟩
              · rcases h034 with ⟨h034a, h034b, h034c, h034d, h034e⟩ | ⟨h034a, h034b, h034c, h034d, h034e⟩
                · rcases h035 with ⟨h035a, h035b, h035c, h035d, h035e⟩ | ⟨h035a, h035b, h035c, h035d, h035e⟩
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · rcases h124 with ⟨h124a, h124b, h124c, h124d, h124e⟩ | ⟨h124a, h124b, h124c, h124d, h124e⟩
                        · rcases h125 with ⟨h125a, h125b, h125c, h125d, h125e⟩ | ⟨h125a, h125b, h125c, h125d, h125e⟩
                          · rcases h134 with ⟨h134a, h134b, h134c, h134d, h134e⟩ | ⟨h134a, h134b, h134c, h134d, h134e⟩
                            · rcases h135 with ⟨h135a, h135b, h135c, h135d, h135e⟩ | ⟨h135a, h135b, h135c, h135d, h135e⟩
                              · rcases h145 with ⟨h145a, h145b, h145c, h145d, h145e⟩ | ⟨h145a, h145b, h145c, h145d, h145e⟩
                                · rcases h234 with ⟨h234a, h234b, h234c, h234d, h234e⟩ | ⟨h234a, h234b, h234c, h234d, h234e⟩
                                  · linarith only [ht, r01.1, h012c, r34.2, h123c, h234c]
                                  · linarith only [ht, h023e, h034c, h234c]
                                · linarith only [ht, h014e, h045c, h145c]
                              · linarith only [ht, r01.1, h012c, r34.2, h023e, h035c, h123c, h134c, h135c]
                            · linarith only [ht, h013e, h034c, h134c]
                          · linarith only [ht, r02.1, r23.2, h025c, h123c, h125c]
                        · linarith only [ht, h023e, h024b, h034a, h123c, h124c]
                      · linarith only [ht, h012e, h023c, h123c]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · rcases h124 with ⟨h124a, h124b, h124c, h124d, h124e⟩ | ⟨h124a, h124b, h124c, h124d, h124e⟩
                        · rcases h125 with ⟨h125a, h125b, h125c, h125d, h125e⟩ | ⟨h125a, h125b, h125c, h125d, h125e⟩
                          · rcases h134 with ⟨h134a, h134b, h134c, h134d, h134e⟩ | ⟨h134a, h134b, h134c, h134d, h134e⟩
                            · rcases h135 with ⟨h135a, h135b, h135c, h135d, h135e⟩ | ⟨h135a, h135b, h135c, h135d, h135e⟩
                              · rcases h145 with ⟨h145a, h145b, h145c, h145d, h145e⟩ | ⟨h145a, h145b, h145c, h145d, h145e⟩
                                · linarith only [ht, h014d, h015c, h045c, h145b]
                                · rcases h234 with ⟨h234a, h234b, h234c, h234d, h234e⟩ | ⟨h234a, h234b, h234c, h234d, h234e⟩
                                  · linarith only [ht, r01.1, h012c, r34.2, h123c, h234c]
                                  · linarith only [ht, h023e, h034c, h234c]
                              · linarith only [ht, r01.1, h012c, r34.2, h023e, h035c, h123c, h134c, h135c]
                            · linarith only [ht, h023e, h034c, h123b, h134c]
                          · linarith only [ht, r02.1, r23.2, h025c, h123c, h125c]
                        · linarith only [ht, r23.2, r45.1, h024b, h045c, h123c, h124c]
                      · linarith only [ht, h012e, h023c, h123c]
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · rcases h124 with ⟨h124a, h124b, h124c, h124d, h124e⟩ | ⟨h124a, h124b, h124c, h124d, h124e⟩
                        · rcases h125 with ⟨h125a, h125b, h125c, h125d, h125e⟩ | ⟨h125a, h125b, h125c, h125d, h125e⟩
                          · rcases h134 with ⟨h134a, h134b, h134c, h134d, h134e⟩ | ⟨h134a, h134b, h134c, h134d, h134e⟩
                            · rcases h135 with ⟨h135a, h135b, h135c, h135d, h135e⟩ | ⟨h135a, h135b, h135c, h135d, h135e⟩
                              · linarith only [h015b, h034a, h045a, h035c, h135b]
                              · rcases h145 with ⟨h145a, h145b, h145c, h145d, h145e⟩ | ⟨h145a, h145b, h145c, h145d, h145e⟩
                                · rcases h234 with ⟨h234a, h234b, h234c, h234d, h234e⟩ | ⟨h234a, h234b, h234c, h234d, h234e⟩
                                  · linarith only [ht, r01.1, h012c, r34.2, h123c, h234c]
                                  · linarith only [ht, r23.2, r35.1, h034c, h035c, h234c]
                                · linarith only [ht, r34.2, r35.1, h034a, h035c, h045c, h134c, h145a, h135b]
                            · linarith only [ht, r13.2, r35.1, h034c, h035c, h134c]
                          · linarith only [ht, r02.1, r23.2, h025c, h123c, h125c]
                        · linarith only [ht, r23.2, r35.1, h024b, h034a, h035c, h123c, h124c]
                      · linarith only [ht, h012e, h023c, h123c]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · rcases h124 with ⟨h124a, h124b, h124c, h124d, h124e⟩ | ⟨h124a, h124b, h124c, h124d, h124e⟩
                        · rcases h125 with ⟨h125a, h125b, h125c, h125d, h125e⟩ | ⟨h125a, h125b, h125c, h125d, h125e⟩
                          · rcases h134 with ⟨h134a, h134b, h134c, h134d, h134e⟩ | ⟨h134a, h134b, h134c, h134d, h134e⟩
                            · rcases h135 with ⟨h135a, h135b, h135c, h135d, h135e⟩ | ⟨h135a, h135b, h135c, h135d, h135e⟩
                              · linarith only [ht, r01.1, r34.2, h013b, h015c, h035c, h134c, h135b]
                              · rcases h145 with ⟨h145a, h145b, h145c, h145d, h145e⟩ | ⟨h145a, h145b, h145c, h145d, h145e⟩
                                · linarith only [h014b, h045c, h145a, h145b]
                                · rcases h234 with ⟨h234a, h234b, h234c, h234d, h234e⟩ | ⟨h234a, h234b, h234c, h234d, h234e⟩
                                  · linarith only [ht, r01.1, h012c, r34.2, h123c, h234c]
                                  · linarith only [ht, r23.2, r35.1, h013b, h035c, h134c, h234c]
                            · linarith only [ht, r13.2, r35.1, h034c, h035c, h134c]
                          · linarith only [ht, r02.1, r24.2, h025c, h125c, h124c]
                        · linarith only [ht, r23.2, r45.1, h024b, h045c, h123c, h124c]
                      · linarith only [ht, h012e, h023c, h123c]
                · rcases h035 with ⟨h035a, h035b, h035c, h035d, h035e⟩ | ⟨h035a, h035b, h035c, h035d, h035e⟩
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · rcases h124 with ⟨h124a, h124b, h124c, h124d, h124e⟩ | ⟨h124a, h124b, h124c, h124d, h124e⟩
                        · rcases h125 with ⟨h125a, h125b, h125c, h125d, h125e⟩ | ⟨h125a, h125b, h125c, h125d, h125e⟩
                          · rcases h134 with ⟨h134a, h134b, h134c, h134d, h134e⟩ | ⟨h134a, h134b, h134c, h134d, h134e⟩
                            · linarith only [ht, r01.1, r35.2, h014c, h034c, h035c, h134b]
                            · rcases h135 with ⟨h135a, h135b, h135c, h135d, h135e⟩ | ⟨h135a, h135b, h135c, h135d, h135e⟩
                              · rcases h145 with ⟨h145a, h145b, h145c, h145d, h145e⟩ | ⟨h145a, h145b, h145c, h145d, h145e⟩
                                · rcases h234 with ⟨h234a, h234b, h234c, h234d, h234e⟩ | ⟨h234a, h234b, h234c, h234d, h234e⟩
                                  · linarith only [ht, r12.1, r35.2, h034c, h035c, h124c, h234b]
                                  · rcases h235 with ⟨h235a, h235b, h235c, h235d, h235e⟩ | ⟨h235a, h235b, h235c, h235d, h235e⟩
                                    · linarith only [ht, r01.1, h012c, r35.2, h123c, h235c]
                                    · linarith only [ht, r23.2, r34.1, h034c, h035c, h235c]
                                · linarith only [ht, r01.1, h012c, r35.2, h024e, h045c, h135c, h124c, h134b, h145c]
                              · linarith only [ht, r13.2, r34.1, h034c, h035c, h135c]
                          · linarith only [ht, r24.2, r34.1, h025b, h035a, h034c, h124c, h125c]
                        · linarith only [ht, r02.1, r23.2, h024c, h123c, h124c]
                      · linarith only [ht, h012e, h023c, h123c]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · rcases h124 with ⟨h124a, h124b, h124c, h124d, h124e⟩ | ⟨h124a, h124b, h124c, h124d, h124e⟩
                        · rcases h125 with ⟨h125a, h125b, h125c, h125d, h125e⟩ | ⟨h125a, h125b, h125c, h125d, h125e⟩
                          · rcases h134 with ⟨h134a, h134b, h134c, h134d, h134e⟩ | ⟨h134a, h134b, h134c, h134d, h134e⟩
                            · linarith only [ht, r35.2, r45.1, h014b, h034c, h035c, h045c, h134b]
                            · rcases h135 with ⟨h135a, h135b, h135c, h135d, h135e⟩ | ⟨h135a, h135b, h135c, h135d, h135e⟩
                              · rcases h145 with ⟨h145a, h145b, h145c, h145d, h145e⟩ | ⟨h145a, h145b, h145c, h145d, h145e⟩
                                · linarith only [ht, h013c, h014d, h045c, h135a, h145b]
                                · rcases h234 with ⟨h234a, h234b, h234c, h234d, h234e⟩ | ⟨h234a, h234b, h234c, h234d, h234e⟩
                                  · linarith only [ht, r01.1, r03.2, h012c, h034c, h124c, h234b]
                                  · rcases h235 with ⟨h235a, h235b, h235c, h235d, h235e⟩ | ⟨h235a, h235b, h235c, h235d, h235e⟩
                                    · linarith only [ht, r01.1, h012c, r35.2, h123c, h235c]
                                    · linarith only [ht, r23.2, r34.1, h013b, h034c, h135c, h235c]
                              · linarith only [ht, r13.2, r34.1, h034c, h035c, h135c]
                          · linarith only [ht, r02.1, r24.2, h025c, h124c, h125c]
                        · linarith only [ht, r23.2, r45.1, h024b, h045c, h123c, h124c]
                      · linarith only [ht, h012e, h023c, h123c]
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · rcases h124 with ⟨h124a, h124b, h124c, h124d, h124e⟩ | ⟨h124a, h124b, h124c, h124d, h124e⟩
                        · rcases h125 with ⟨h125a, h125b, h125c, h125d, h125e⟩ | ⟨h125a, h125b, h125c, h125d, h125e⟩
                          · rcases h134 with ⟨h134a, h134b, h134c, h134d, h134e⟩ | ⟨h134a, h134b, h134c, h134d, h134e⟩
                            · linarith only [h013b, h034c, h134b, h134a]
                            · rcases h135 with ⟨h135a, h135b, h135c, h135d, h135e⟩ | ⟨h135a, h135b, h135c, h135d, h135e⟩
                              · linarith only [ht, h013d, h015c, h035c, h135b]
                              · rcases h145 with ⟨h145a, h145b, h145c, h145d, h145e⟩ | ⟨h145a, h145b, h145c, h145d, h145e⟩
                                · rcases h234 with ⟨h234a, h234b, h234c, h234d, h234e⟩ | ⟨h234a, h234b, h234c, h234d, h234e⟩
                                  · linarith only [ht, h012c, h013d, h034c, h124c, h234b]
                                  · rcases h235 with ⟨h235a, h235b, h235c, h235d, h235e⟩ | ⟨h235a, h235b, h235c, h235d, h235e⟩
                                    · linarith only [ht, h012a, h013d, h025c, h035c, h235b]
                                    · rcases h245 with ⟨h245a, h245b, h245c, h245d, h245e⟩ | ⟨h245a, h245b, h245c, h245d, h245e⟩
                                      · linarith only [ht, r01.1, h012c, r45.2, h124c, h245c]
                                      · linarith only [ht, h024e, h045c, h245c]
                                · linarith only [ht, h014e, h045c, h145c]
                          · linarith only [ht, r02.1, r23.2, h025c, h123c, h125c]
                        · linarith only [ht, r01.1, h012a, r23.2, h024c, h123c, h124c]
                      · linarith only [ht, h012e, h023c, h123c]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · rcases h124 with ⟨h124a, h124b, h124c, h124d, h124e⟩ | ⟨h124a, h124b, h124c, h124d, h124e⟩
                        · rcases h125 with ⟨h125a, h125b, h125c, h125d, h125e⟩ | ⟨h125a, h125b, h125c, h125d, h125e⟩
                          · rcases h134 with ⟨h134a, h134b, h134c, h134d, h134e⟩ | ⟨h134a, h134b, h134c, h134d, h134e⟩
                            · linarith only [ht, h013d, h014c, h034c, h134b]
                            · rcases h135 with ⟨h135a, h135b, h135c, h135d, h135e⟩ | ⟨h135a, h135b, h135c, h135d, h135e⟩
                              · linarith only [h013b, h035c, h135b, h135a]
                              · rcases h145 with ⟨h145a, h145b, h145c, h145d, h145e⟩ | ⟨h145a, h145b, h145c, h145d, h145e⟩
                                · linarith only [ht, h014d, h015c, h045c, h145b]
                                · rcases h234 with ⟨h234a, h234b, h234c, h234d, h234e⟩ | ⟨h234a, h234b, h234c, h234d, h234e⟩
                                  · linarith only [ht, h012a, h013d, h024c, h034c, h234b]
                                  · rcases h235 with ⟨h235a, h235b, h235c, h235d, h235e⟩ | ⟨h235a, h235b, h235c, h235d, h235e⟩
                                    · linarith only [h023b, h035c, h235b, h235a]
                                    · rcases h245 with ⟨h245a, h245b, h245c, h245d, h245e⟩ | ⟨h245a, h245b, h245c, h245d, h245e⟩
                                      · linarith only [ht, h012c, h014d, h045b, h045a, h125c, h245b]
                                      · rcases h345 with ⟨h345a, h345b, h345c, h345d, h345e⟩ | ⟨h345a, h345b, h345c, h345d, h345e⟩
                                        · linarith only [ht, h034e, h045c, h345c]
                                        · linarith only [ht, h012c, h013d, h034c, h125c, h245e, h345c]
                          · linarith only [ht, r01.1, h012a, r23.2, h025c, h123c, h125c]
                        · linarith only [ht, r01.1, h012a, r23.2, h024c, h123c, h124c]
                      · linarith only [ht, h012e, h023c, h123c]
              · rcases h034 with ⟨h034a, h034b, h034c, h034d, h034e⟩ | ⟨h034a, h034b, h034c, h034d, h034e⟩
                · rcases h035 with ⟨h035a, h035b, h035c, h035d, h035e⟩ | ⟨h035a, h035b, h035c, h035d, h035e⟩
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · rcases h124 with ⟨h124a, h124b, h124c, h124d, h124e⟩ | ⟨h124a, h124b, h124c, h124d, h124e⟩
                        · rcases h125 with ⟨h125a, h125b, h125c, h125d, h125e⟩ | ⟨h125a, h125b, h125c, h125d, h125e⟩
                          · linarith only [ht, r01.1, h012b, r23.2, h015c, h025c, h123c, h125b]
                          · rcases h134 with ⟨h134a, h134b, h134c, h134d, h134e⟩ | ⟨h134a, h134b, h134c, h134d, h134e⟩
                            · rcases h135 with ⟨h135a, h135b, h135c, h135d, h135e⟩ | ⟨h135a, h135b, h135c, h135d, h135e⟩
                              · rcases h145 with ⟨h145a, h145b, h145c, h145d, h145e⟩ | ⟨h145a, h145b, h145c, h145d, h145e⟩
                                · rcases h234 with ⟨h234a, h234b, h234c, h234d, h234e⟩ | ⟨h234a, h234b, h234c, h234d, h234e⟩
                                  · linarith only [ht, r25.1, r34.2, h023c, h025c, h234c]
                                  · linarith only [ht, r23.2, r25.1, h023a, h025c, h034c, h234c]
                                · linarith only [ht, r23.2, r25.1, h024a, h025c, h045c, h123c, h125b, h145a]
                              · linarith only [ht, r23.2, r25.1, h023a, h025c, h035c, h123c, h125b, h135a]
                            · linarith only [ht, r13.2, r25.1, h023a, h025c, h034c, h134c]
                        · linarith only [ht, r23.2, r25.1, h024c, h025c, h124b, h123c, h124a]
                      · linarith only [ht, r12.2, r25.1, h023c, h025c, h123c]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · rcases h124 with ⟨h124a, h124b, h124c, h124d, h124e⟩ | ⟨h124a, h124b, h124c, h124d, h124e⟩
                        · rcases h125 with ⟨h125a, h125b, h125c, h125d, h125e⟩ | ⟨h125a, h125b, h125c, h125d, h125e⟩
                          · linarith only [ht, r01.1, r34.2, h015c, h023a, h025c, h034c, h125b]
                          · rcases h134 with ⟨h134a, h134b, h134c, h134d, h134e⟩ | ⟨h134a, h134b, h134c, h134d, h134e⟩
                            · rcases h135 with ⟨h135a, h135b, h135c, h135d, h135e⟩ | ⟨h135a, h135b, h135c, h135d, h135e⟩
                              · rcases h145 with ⟨h145a, h145b, h145c, h145d, h145e⟩ | ⟨h145a, h145b, h145c, h145d, h145e⟩
                                · linarith only [h014b, h045c, h145a, h145b]
                                · rcases h234 with ⟨h234a, h234b, h234c, h234d, h234e⟩ | ⟨h234a, h234b, h234c, h234d, h234e⟩
                                  · linarith only [ht, r01.1, h012c, r34.2, h123c, h234c]
                                  · linarith only [ht, h023e, h034c, h234c]
                              · linarith only [ht, r24.2, r25.1, h023a, h025c, h035c, h125b, h124c, h135a]
                            · linarith only [ht, r13.2, r25.1, h023a, h025c, h034c, h134c]
                        · linarith only [ht, r23.2, r25.1, h024c, h025c, h123c, h124b, h124a]
                      · linarith only [ht, r12.2, r25.1, h023c, h025c, h123c]
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · rcases h124 with ⟨h124a, h124b, h124c, h124d, h124e⟩ | ⟨h124a, h124b, h124c, h124d, h124e⟩
                        · rcases h125 with ⟨h125a, h125b, h125c, h125d, h125e⟩ | ⟨h125a, h125b, h125c, h125d, h125e⟩
                          · linarith only [ht, r01.1, r34.2, h015c, h023a, h025c, h034c, h125b]
                          · rcases h134 with ⟨h134a, h134b, h134c, h134d, h134e⟩ | ⟨h134a, h134b, h134c, h134d, h134e⟩
                            · rcases h135 with ⟨h135a, h135b, h135c, h135d, h135e⟩ | ⟨h135a, h135b, h135c, h135d, h135e⟩
                              · linarith only [h015b, h034a, h035c, h045a, h135b]
                              · rcases h145 with ⟨h145a, h145b, h145c, h145d, h145e⟩ | ⟨h145a, h145b, h145c, h145d, h145e⟩
                                · rcases h234 with ⟨h234a, h234b, h234c, h234d, h234e⟩ | ⟨h234a, h234b, h234c, h234d, h234e⟩
                                  · linarith only [ht, r25.1, r34.2, h023c, h025c, h234c]
                                  · linarith only [ht, r23.2, r35.1, h034c, h035c, h234c]
                                · linarith only [ht, r24.2, r25.1, h024a, h025c, h045c, h124c, h125b, h145a]
                            · linarith only [ht, r13.2, r35.1, h034c, h035c, h134c]
                        · linarith only [ht, r23.2, r25.1, h024c, h025c, h123c, h124a, h124b]
                      · linarith only [ht, r12.2, r25.1, h023c, h025c, h123c]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · rcases h124 with ⟨h124a, h124b, h124c, h124d, h124e⟩ | ⟨h124a, h124b, h124c, h124d, h124e⟩
                        · rcases h125 with ⟨h125a, h125b, h125c, h125d, h125e⟩ | ⟨h125a, h125b, h125c, h125d, h125e⟩
                          · linarith only [ht, r01.1, h012b, r23.2, h015c, h025c, h125b, h123c]
                          · rcases h134 with ⟨h134a, h134b, h134c, h134d, h134e⟩ | ⟨h134a, h134b, h134c, h134d, h134e⟩
                            · rcases h135 with ⟨h135a, h135b, h135c, h135d, h135e⟩ | ⟨h135a, h135b, h135c, h135d, h135e⟩
                              · linarith only [ht, r01.1, r34.2, h015c, h034c, h035c, h135b]
                              · rcases h145 with ⟨h145a, h145b, h145c, h145d, h145e⟩ | ⟨h145a, h145b, h145c, h145d, h145e⟩
                                · linarith only [h014b, h045c, h145a, h145b]
                                · rcases h234 with ⟨h234a, h234b, h234c, h234d, h234e⟩ | ⟨h234a, h234b, h234c, h234d, h234e⟩
                                  · linarith only [ht, r25.1, r34.2, h023c, h025c, h234c]
                                  · linarith only [ht, r23.2, r35.1, h034c, h035c, h234c]
                            · linarith only [ht, r13.2, r35.1, h034c, h035c, h134c]
                        · linarith only [ht, r23.2, r25.1, h024c, h025c, h123c, h124b, h124a]
                      · linarith only [ht, r12.2, r25.1, h023c, h025c, h123c]
                · rcases h035 with ⟨h035a, h035b, h035c, h035d, h035e⟩ | ⟨h035a, h035b, h035c, h035d, h035e⟩
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · rcases h124 with ⟨h124a, h124b, h124c, h124d, h124e⟩ | ⟨h124a, h124b, h124c, h124d, h124e⟩
                        · rcases h125 with ⟨h125a, h125b, h125c, h125d, h125e⟩ | ⟨h125a, h125b, h125c, h125d, h125e⟩
                          · linarith only [h012b, h025c, h125b, h125a]
                          · rcases h134 with ⟨h134a, h134b, h134c, h134d, h134e⟩ | ⟨h134a, h134b, h134c, h134d, h134e⟩
                            · linarith only [h013b, h034c, h134b, h134a]
                            · rcases h135 with ⟨h135a, h135b, h135c, h135d, h135e⟩ | ⟨h135a, h135b, h135c, h135d, h135e⟩
                              · rcases h145 with ⟨h145a, h145b, h145c, h145d, h145e⟩ | ⟨h145a, h145b, h145c, h145d, h145e⟩
                                · rcases h234 with ⟨h234a, h234b, h234c, h234d, h234e⟩ | ⟨h234a, h234b, h234c, h234d, h234e⟩
                                  · linarith only [h024c, h025b, h035a, h034c, h234b]
                                  · linarith only [ht, h024c, h025b, h035a, h034c, h234e]
                                · linarith only [ht, r23.2, r25.1, h024a, h025c, h045c, h125b, h123c, h145a]
                              · linarith only [ht, r23.2, r34.1, h034c, h035c, h125b, h123c, h135a]
                        · linarith only [ht, r23.2, r25.1, h024c, h025c, h124a, h123c, h124b]
                      · linarith only [ht, r12.2, r25.1, h023c, h025c, h123c]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · rcases h124 with ⟨h124a, h124b, h124c, h124d, h124e⟩ | ⟨h124a, h124b, h124c, h124d, h124e⟩
                        · rcases h125 with ⟨h125a, h125b, h125c, h125d, h125e⟩ | ⟨h125a, h125b, h125c, h125d, h125e⟩
                          · linarith only [ht, r23.2, r34.1, h015b, h023c, h025c, h035a, h034c, h125b]
                          · rcases h134 with ⟨h134a, h134b, h134c, h134d, h134e⟩ | ⟨h134a, h134b, h134c, h134d, h134e⟩
                            · linarith only [ht, r25.1, r35.2, h014b, h024a, h025c, h034c, h035c, h134b]
                            · rcases h135 with ⟨h135a, h135b, h135c, h135d, h135e⟩ | ⟨h135a, h135b, h135c, h135d, h135e⟩
                              · rcases h145 with ⟨h145a, h145b, h145c, h145d, h145e⟩ | ⟨h145a, h145b, h145c, h145d, h145e⟩
                                · linarith only [ht, h013c, h014d, h045c, h145b, h135a]
                                · rcases h234 with ⟨h234a, h234b, h234c, h234d, h234e⟩ | ⟨h234a, h234b, h234c, h234d, h234e⟩
                                  · linarith only [h024c, h025b, h035a, h034b, h034a, h234b]
                                  · linarith only [ht, h024c, h025b, h035a, h034c, h234e]
                              · linarith only [ht, r23.2, r34.1, h034c, h035c, h123c, h125b, h135a]
                        · linarith only [ht, r23.2, r25.1, h024c, h025c, h124b, h123c, h124a]
                      · linarith only [ht, r12.2, r25.1, h023c, h025c, h123c]
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · rcases h124 with ⟨h124a, h124b, h124c, h124d, h124e⟩ | ⟨h124a, h124b, h124c, h124d, h124e⟩
                        · rcases h125 with ⟨h125a, h125b, h125c, h125d, h125e⟩ | ⟨h125a, h125b, h125c, h125d, h125e⟩
                          · linarith only [ht, r01.1, r23.2, h015c, h023c, h025c, h125b]
                          · rcases h134 with ⟨h134a, h134b, h134c, h134d, h134e⟩ | ⟨h134a, h134b, h134c, h134d, h134e⟩
                            · linarith only [ht, h013d, h014c, h034c, h134b]
                            · rcases h135 with ⟨h135a, h135b, h135c, h135d, h135e⟩ | ⟨h135a, h135b, h135c, h135d, h135e⟩
                              · linarith only [h013b, h035c, h135a, h135b]
                              · rcases h145 with ⟨h145a, h145b, h145c, h145d, h145e⟩ | ⟨h145a, h145b, h145c, h145d, h145e⟩
                                · rcases h234 with ⟨h234a, h234b, h234c, h234d, h234e⟩ | ⟨h234a, h234b, h234c, h234d, h234e⟩
                                  · linarith only [ht, r03.2, h012b, r25.1, h025c, h034c, h124c, h234b]
                                  · rcases h235 with ⟨h235a, h235b, h235c, h235d, h235e⟩ | ⟨h235a, h235b, h235c, h235d, h235e⟩
                                    · linarith only [ht, h012b, r24.2, r34.1, h023b, h025c, h034c, h124c, h235a]
                                    · linarith only [ht, h012b, h025c, h123c, h235d]
                                · linarith only [ht, r23.2, r25.1, h024a, h025c, h045c, h123c, h125b, h145a]
                        · linarith only [ht, r23.2, r25.1, h024c, h025c, h124b, h123c, h124a]
                      · linarith only [ht, r12.2, r25.1, h023c, h025c, h123c]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · rcases h124 with ⟨h124a, h124b, h124c, h124d, h124e⟩ | ⟨h124a, h124b, h124c, h124d, h124e⟩
                        · rcases h125 with ⟨h125a, h125b, h125c, h125d, h125e⟩ | ⟨h125a, h125b, h125c, h125d, h125e⟩
                          · linarith only [ht, r01.1, r23.2, h015c, h023c, h025c, h125b]
                          · rcases h134 with ⟨h134a, h134b, h134c, h134d, h134e⟩ | ⟨h134a, h134b, h134c, h134d, h134e⟩
                            · linarith only [ht, h013d, h014c, h034c, h134b]
                            · rcases h135 with ⟨h135a, h135b, h135c, h135d, h135e⟩ | ⟨h135a, h135b, h135c, h135d, h135e⟩
                              · linarith only [h013b, h035c, h135a, h135b]
                              · rcases h145 with ⟨h145a, h145b, h145c, h145d, h145e⟩ | ⟨h145a, h145b, h145c, h145d, h145e⟩
                                · linarith only [ht, h014d, h015c, h045c, h145b]
                                · rcases h234 with ⟨h234a, h234b, h234c, h234d, h234e⟩ | ⟨h234a, h234b, h234c, h234d, h234e⟩
                                  · linarith only [ht, r03.2, r25.1, h024c, h025c, h034c, h234b]
                                  · rcases h235 with ⟨h235a, h235b, h235c, h235d, h235e⟩ | ⟨h235a, h235b, h235c, h235d, h235e⟩
                                    · linarith only [ht, r01.1, r02.2, h012c, h025c, h123c, h235a]
                                    · linarith only [ht, h012b, h025c, h123c, h235d]
                        · linarith only [ht, r23.2, r25.1, h024c, h025c, h124b, h123c, h124a]
                      · linarith only [ht, r12.2, r25.1, h023c, h025c, h123c]
            · rcases h025 with ⟨h025a, h025b, h025c, h025d, h025e⟩ | ⟨h025a, h025b, h025c, h025d, h025e⟩
              · rcases h034 with ⟨h034a, h034b, h034c, h034d, h034e⟩ | ⟨h034a, h034b, h034c, h034d, h034e⟩
                · rcases h035 with ⟨h035a, h035b, h035c, h035d, h035e⟩ | ⟨h035a, h035b, h035c, h035d, h035e⟩
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · rcases h124 with ⟨h124a, h124b, h124c, h124d, h124e⟩ | ⟨h124a, h124b, h124c, h124d, h124e⟩
                        · linarith only [ht, r01.1, r25.2, h014c, h024c, h025c, h124b]
                        · rcases h125 with ⟨h125a, h125b, h125c, h125d, h125e⟩ | ⟨h125a, h125b, h125c, h125d, h125e⟩
                          · rcases h134 with ⟨h134a, h134b, h134c, h134d, h134e⟩ | ⟨h134a, h134b, h134c, h134d, h134e⟩
                            · rcases h135 with ⟨h135a, h135b, h135c, h135d, h135e⟩ | ⟨h135a, h135b, h135c, h135d, h135e⟩
                              · rcases h145 with ⟨h145a, h145b, h145c, h145d, h145e⟩ | ⟨h145a, h145b, h145c, h145d, h145e⟩
                                · rcases h234 with ⟨h234a, h234b, h234c, h234d, h234e⟩ | ⟨h234a, h234b, h234c, h234d, h234e⟩
                                  · linarith only [ht, r12.1, r25.2, h024c, h025c, h123c, h234a]
                                  · linarith only [ht, r03.1, r25.2, h024c, h025c, h034c, h234a]
                                · linarith only [ht, r23.2, r24.1, h023a, h024c, h034a, h045c, h145b, h123c, h145a, h124b]
                              · linarith only [ht, r24.1, r34.2, h023a, h024c, h035c, h134c, h135a, h135b]
                            · linarith only [ht, r23.2, r24.1, h023a, h024c, h034c, h123c, h134a, h124b]
                          · linarith only [ht, r23.2, r24.1, h024c, h025c, h123c, h125a, h125b]
                      · linarith only [ht, r12.2, r24.1, h023c, h024c, h123c]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · rcases h124 with ⟨h124a, h124b, h124c, h124d, h124e⟩ | ⟨h124a, h124b, h124c, h124d, h124e⟩
                        · linarith only [h014b, h023a, h024c, h034a, h124b]
                        · rcases h125 with ⟨h125a, h125b, h125c, h125d, h125e⟩ | ⟨h125a, h125b, h125c, h125d, h125e⟩
                          · rcases h134 with ⟨h134a, h134b, h134c, h134d, h134e⟩ | ⟨h134a, h134b, h134c, h134d, h134e⟩
                            · rcases h135 with ⟨h135a, h135b, h135c, h135d, h135e⟩ | ⟨h135a, h135b, h135c, h135d, h135e⟩
                              · rcases h145 with ⟨h145a, h145b, h145c, h145d, h145e⟩ | ⟨h145a, h145b, h145c, h145d, h145e⟩
                                · linarith only [ht, h014d, h015c, h045c, h145b]
                                · rcases h234 with ⟨h234a, h234b, h234c, h234d, h234e⟩ | ⟨h234a, h234b, h234c, h234d, h234e⟩
                                  · linarith only [ht, r01.1, r02.2, h012c, h024c, h123c, h234a]
                                  · linarith only [h013b, h023a, h024c, h134c, h234a]
                              · linarith only [ht, r24.1, r34.2, h023a, h024c, h035c, h135b, h134c, h135a]
                            · linarith only [ht, r23.2, r24.1, h023a, h024c, h034c, h123c, h124b, h134a]
                          · linarith only [ht, r23.2, r24.1, h024c, h025c, h123c, h125a, h125b]
                      · linarith only [ht, r12.2, r24.1, h023c, h024c, h123c]
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · rcases h124 with ⟨h124a, h124b, h124c, h124d, h124e⟩ | ⟨h124a, h124b, h124c, h124d, h124e⟩
                        · linarith only [ht, r01.1, r25.2, h014c, h024c, h025c, h124b]
                        · rcases h125 with ⟨h125a, h125b, h125c, h125d, h125e⟩ | ⟨h125a, h125b, h125c, h125d, h125e⟩
                          · rcases h134 with ⟨h134a, h134b, h134c, h134d, h134e⟩ | ⟨h134a, h134b, h134c, h134d, h134e⟩
                            · rcases h135 with ⟨h135a, h135b, h135c, h135d, h135e⟩ | ⟨h135a, h135b, h135c, h135d, h135e⟩
                              · linarith only [ht, r24.1, r34.2, h015b, h025a, h024c, h034c, h035c, h135b]
                              · rcases h145 with ⟨h145a, h145b, h145c, h145d, h145e⟩ | ⟨h145a, h145b, h145c, h145d, h145e⟩
                                · rcases h234 with ⟨h234a, h234b, h234c, h234d, h234e⟩ | ⟨h234a, h234b, h234c, h234d, h234e⟩
                                  · linarith only [h012b, h024a, h024b, h123c, h234a]
                                  · linarith only [ht, r03.1, h012b, r23.2, h024c, h034c, h123c, h234a]
                                · linarith only [ht, r23.2, r35.1, h034a, h035c, h045c, h124b, h123c, h134a, h135b, h145a]
                            · linarith only [ht, r23.2, r35.1, h034c, h035c, h124b, h123c, h134a]
                          · linarith only [ht, r23.2, r24.1, h024c, h025c, h123c, h125a, h125b]
                      · linarith only [ht, r12.2, r24.1, h023c, h024c, h123c]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · rcases h124 with ⟨h124a, h124b, h124c, h124d, h124e⟩ | ⟨h124a, h124b, h124c, h124d, h124e⟩
                        · linarith only [ht, r23.2, r35.1, h014b, h023c, h024c, h034a, h035c, h124b]
                        · rcases h125 with ⟨h125a, h125b, h125c, h125d, h125e⟩ | ⟨h125a, h125b, h125c, h125d, h125e⟩
                          · rcases h134 with ⟨h134a, h134b, h134c, h134d, h134e⟩ | ⟨h134a, h134b, h134c, h134d, h134e⟩
                            · rcases h135 with ⟨h135a, h135b, h135c, h135d, h135e⟩ | ⟨h135a, h135b, h135c, h135d, h135e⟩
                              · linarith only [ht, r24.1, r34.2, h015b, h025a, h024c, h034c, h035c, h135b]
                              · rcases h145 with ⟨h145a, h145b, h145c, h145d, h145e⟩ | ⟨h145a, h145b, h145c, h145d, h145e⟩
                                · linarith only [h015b, h025a, h024b, h045c, h145b]
                                · rcases h234 with ⟨h234a, h234b, h234c, h234d, h234e⟩ | ⟨h234a, h234b, h234c, h234d, h234e⟩
                                  · linarith only [h023c, h024a, h024b, h234a]
                                  · linarith only [ht, r03.1, h012b, r25.2, h024c, h034c, h125c, h234a]
                            · linarith only [ht, r24.1, r25.2, h023a, h024c, h034c, h125c, h124b, h134a]
                          · linarith only [ht, r23.2, r24.1, h024c, h025c, h123c, h125a, h125b]
                      · linarith only [ht, r12.2, r24.1, h023c, h024c, h123c]
                · rcases h035 with ⟨h035a, h035b, h035c, h035d, h035e⟩ | ⟨h035a, h035b, h035c, h035d, h035e⟩
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · rcases h124 with ⟨h124a, h124b, h124c, h124d, h124e⟩ | ⟨h124a, h124b, h124c, h124d, h124e⟩
                        · linarith only [ht, r01.1, r23.2, h014c, h023c, h024c, h124b]
                        · rcases h125 with ⟨h125a, h125b, h125c, h125d, h125e⟩ | ⟨h125a, h125b, h125c, h125d, h125e⟩
                          · rcases h134 with ⟨h134a, h134b, h134c, h134d, h134e⟩ | ⟨h134a, h134b, h134c, h134d, h134e⟩
                            · linarith only [h013b, h034c, h134b, h134a]
                            · rcases h135 with ⟨h135a, h135b, h135c, h135d, h135e⟩ | ⟨h135a, h135b, h135c, h135d, h135e⟩
                              · rcases h145 with ⟨h145a, h145b, h145c, h145d, h145e⟩ | ⟨h145a, h145b, h145c, h145d, h145e⟩
                                · rcases h234 with ⟨h234a, h234b, h234c, h234d, h234e⟩ | ⟨h234a, h234b, h234c, h234d, h234e⟩
                                  · linarith only [h023c, h024c, h234a]
                                  · linarith only [ht, h023c, h024c, h234d]
                                · linarith only [ht, r04.1, r23.2, h045c, h124b, h123c, h145c]
                              · linarith only [ht, h013e, h035c, h135c]
                          · linarith only [ht, r23.2, r24.1, h024c, h025c, h125b, h123c, h125a]
                      · linarith only [ht, r12.2, r24.1, h023c, h024c, h123c]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · rcases h124 with ⟨h124a, h124b, h124c, h124d, h124e⟩ | ⟨h124a, h124b, h124c, h124d, h124e⟩
                        · linarith only [h014b, h025a, h024c, h045b, h124b]
                        · rcases h125 with ⟨h125a, h125b, h125c, h125d, h125e⟩ | ⟨h125a, h125b, h125c, h125d, h125e⟩
                          · rcases h134 with ⟨h134a, h134b, h134c, h134d, h134e⟩ | ⟨h134a, h134b, h134c, h134d, h134e⟩
                            · linarith only [h013b, h034c, h134b, h134a]
                            · rcases h135 with ⟨h135a, h135b, h135c, h135d, h135e⟩ | ⟨h135a, h135b, h135c, h135d, h135e⟩
                              · rcases h145 with ⟨h145a, h145b, h145c, h145d, h145e⟩ | ⟨h145a, h145b, h145c, h145d, h145e⟩
                                · linarith only [ht, h014d, h015c, h045c, h145b]
                                · rcases h234 with ⟨h234a, h234b, h234c, h234d, h234e⟩ | ⟨h234a, h234b, h234c, h234d, h234e⟩
                                  · linarith only [h012b, h024c, h123c, h234a]
                                  · linarith only [ht, h012b, h024c, h123c, h234d]
                              · linarith only [ht, r13.2, r34.1, h034c, h035c, h135c]
                          · linarith only [ht, r23.2, r24.1, h024c, h025c, h125a, h125b, h123c]
                      · linarith only [ht, r12.2, r24.1, h023c, h024c, h123c]
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · rcases h124 with ⟨h124a, h124b, h124c, h124d, h124e⟩ | ⟨h124a, h124b, h124c, h124d, h124e⟩
                        · linarith only [h012b, h024c, h124a, h124b]
                        · rcases h125 with ⟨h125a, h125b, h125c, h125d, h125e⟩ | ⟨h125a, h125b, h125c, h125d, h125e⟩
                          · rcases h134 with ⟨h134a, h134b, h134c, h134d, h134e⟩ | ⟨h134a, h134b, h134c, h134d, h134e⟩
                            · linarith only [h013b, h034c, h134a, h134b]
                            · rcases h135 with ⟨h135a, h135b, h135c, h135d, h135e⟩ | ⟨h135a, h135b, h135c, h135d, h135e⟩
                              · linarith only [ht, h013d, h015c, h035c, h135b]
                              · rcases h145 with ⟨h145a, h145b, h145c, h145d, h145e⟩ | ⟨h145a, h145b, h145c, h145d, h145e⟩
                                · rcases h234 with ⟨h234a, h234b, h234c, h234d, h234e⟩ | ⟨h234a, h234b, h234c, h234d, h234e⟩
                                  · linarith only [h012b, h024c, h123c, h234a]
                                  · linarith only [ht, h012b, h024c, h123c, h234d]
                                · linarith only [ht, r04.1, r23.2, h045c, h123c, h145c, h124b]
                          · linarith only [ht, r23.2, r24.1, h024c, h025c, h125b, h123c, h125a]
                      · linarith only [ht, r12.2, r24.1, h023c, h024c, h123c]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · rcases h124 with ⟨h124a, h124b, h124c, h124d, h124e⟩ | ⟨h124a, h124b, h124c, h124d, h124e⟩
                        · linarith only [h014b, h025a, h024c, h124b, h045b]
                        · rcases h125 with ⟨h125a, h125b, h125c, h125d, h125e⟩ | ⟨h125a, h125b, h125c, h125d, h125e⟩
                          · rcases h134 with ⟨h134a, h134b, h134c, h134d, h134e⟩ | ⟨h134a, h134b, h134c, h134d, h134e⟩
                            · linarith only [h013b, h034c, h134b, h134a]
                            · rcases h135 with ⟨h135a, h135b, h135c, h135d, h135e⟩ | ⟨h135a, h135b, h135c, h135d, h135e⟩
                              · linarith only [ht, h013d, h015c, h035c, h135b]
                              · rcases h145 with ⟨h145a, h145b, h145c, h145d, h145e⟩ | ⟨h145a, h145b, h145c, h145d, h145e⟩
                                · linarith only [ht, h014d, h015c, h045c, h145b]
                                · rcases h234 with ⟨h234a, h234b, h234c, h234d, h234e⟩ | ⟨h234a, h234b, h234c, h234d, h234e⟩
                                  · linarith only [ht, r01.1, r02.2, h012c, h024c, h234a, h123c]
                                  · linarith only [ht, h012b, h024c, h234d, h123c]
                          · linarith only [ht, r23.2, r24.1, h024c, h025c, h125b, h125a, h123c]
                      · linarith only [ht, r12.2, r24.1, h023c, h024c, h123c]
              · rcases h034 with ⟨h034a, h034b, h034c, h034d, h034e⟩ | ⟨h034a, h034b, h034c, h034d, h034e⟩
                · rcases h035 with ⟨h035a, h035b, h035c, h035d, h035e⟩ | ⟨h035a, h035b, h035c, h035d, h035e⟩
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · rcases h124 with ⟨h124a, h124b, h124c, h124d, h124e⟩ | ⟨h124a, h124b, h124c, h124d, h124e⟩
                        · linarith only [ht, r01.1, h012b, r23.2, h014c, h024c, h123c, h124b]
                        · rcases h125 with ⟨h125a, h125b, h125c, h125d, h125e⟩ | ⟨h125a, h125b, h125c, h125d, h125e⟩
                          · linarith only [ht, r01.1, r34.2, h015c, h023a, h025c, h034c, h125b]
                          · rcases h134 with ⟨h134a, h134b, h134c, h134d, h134e⟩ | ⟨h134a, h134b, h134c, h134d, h134e⟩
                            · rcases h135 with ⟨h135a, h135b, h135c, h135d, h135e⟩ | ⟨h135a, h135b, h135c, h135d, h135e⟩
                              · rcases h145 with ⟨h145a, h145b, h145c, h145d, h145e⟩ | ⟨h145a, h145b, h145c, h145d, h145e⟩
                                · rcases h234 with ⟨h234a, h234b, h234c, h234d, h234e⟩ | ⟨h234a, h234b, h234c, h234d, h234e⟩
                                  · linarith only [ht, r12.1, r34.2, h023a, h024c, h034c, h123c, h234a]
                                  · linarith only [h023a, h024c, h034c, h234a]
                                · linarith only [ht, r23.2, r24.1, h023a, h024c, h034a, h045c, h125b, h123c, h145a]
                              · linarith only [ht, r23.2, r24.1, h023a, h024c, h035c, h125b, h123c, h135a]
                            · linarith only [ht, r23.2, r24.1, h023a, h024c, h034c, h124b, h134a, h123c]
                      · linarith only [ht, r12.2, r24.1, h023c, h024c, h123c]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · rcases h124 with ⟨h124a, h124b, h124c, h124d, h124e⟩ | ⟨h124a, h124b, h124c, h124d, h124e⟩
                        · linarith only [h014b, h023a, h024c, h034a, h124b]
                        · rcases h125 with ⟨h125a, h125b, h125c, h125d, h125e⟩ | ⟨h125a, h125b, h125c, h125d, h125e⟩
                          · linarith only [h015b, h023a, h025c, h035a, h125b]
                          · rcases h134 with ⟨h134a, h134b, h134c, h134d, h134e⟩ | ⟨h134a, h134b, h134c, h134d, h134e⟩
                            · rcases h135 with ⟨h135a, h135b, h135c, h135d, h135e⟩ | ⟨h135a, h135b, h135c, h135d, h135e⟩
                              · rcases h145 with ⟨h145a, h145b, h145c, h145d, h145e⟩ | ⟨h145a, h145b, h145c, h145d, h145e⟩
                                · linarith only [ht, h014d, h015c, h045c, h145b]
                                · rcases h234 with ⟨h234a, h234b, h234c, h234d, h234e⟩ | ⟨h234a, h234b, h234c, h234d, h234e⟩
                                  · linarith only [h023a, h023b, h024c, h234a]
                                  · linarith only [h023a, h024c, h034c, h234a]
                              · linarith only [ht, r23.2, r24.1, h023a, h024c, h035c, h125b, h135a, h123c]
                            · linarith only [ht, r23.2, r24.1, h023a, h024c, h034c, h124b, h123c, h134a]
                      · linarith only [ht, r12.2, r24.1, h023c, h024c, h123c]
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · rcases h124 with ⟨h124a, h124b, h124c, h124d, h124e⟩ | ⟨h124a, h124b, h124c, h124d, h124e⟩
                        · linarith only [ht, r01.1, r23.2, h014c, h023c, h024c, h124b]
                        · rcases h125 with ⟨h125a, h125b, h125c, h125d, h125e⟩ | ⟨h125a, h125b, h125c, h125d, h125e⟩
                          · linarith only [h015b, h023a, h034a, h025c, h045a, h125b]
                          · rcases h134 with ⟨h134a, h134b, h134c, h134d, h134e⟩ | ⟨h134a, h134b, h134c, h134d, h134e⟩
                            · rcases h135 with ⟨h135a, h135b, h135c, h135d, h135e⟩ | ⟨h135a, h135b, h135c, h135d, h135e⟩
                              · linarith only [h015b, h034a, h045a, h035c, h135b]
                              · rcases h145 with ⟨h145a, h145b, h145c, h145d, h145e⟩ | ⟨h145a, h145b, h145c, h145d, h145e⟩
                                · rcases h234 with ⟨h234a, h234b, h234c, h234d, h234e⟩ | ⟨h234a, h234b, h234c, h234d, h234e⟩
                                  · linarith only [h023c, h024c, h234a]
                                  · linarith only [h023a, h024c, h034c, h234a]
                                · linarith only [ht, r23.2, r24.1, h023a, h024c, h034a, h045c, h125b, h123c, h145a]
                            · linarith only [ht, r23.2, r24.1, h023a, h024c, h034c, h134a, h124b, h123c]
                      · linarith only [ht, r12.2, r24.1, h023c, h024c, h123c]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · rcases h124 with ⟨h124a, h124b, h124c, h124d, h124e⟩ | ⟨h124a, h124b, h124c, h124d, h124e⟩
                        · linarith only [h014b, h023a, h024c, h034a, h124b]
                        · rcases h125 with ⟨h125a, h125b, h125c, h125d, h125e⟩ | ⟨h125a, h125b, h125c, h125d, h125e⟩
                          · linarith only [ht, r01.1, r23.2, h015c, h023c, h025c, h125b]
                          · rcases h134 with ⟨h134a, h134b, h134c, h134d, h134e⟩ | ⟨h134a, h134b, h134c, h134d, h134e⟩
                            · rcases h135 with ⟨h135a, h135b, h135c, h135d, h135e⟩ | ⟨h135a, h135b, h135c, h135d, h135e⟩
                              · linarith only [h013b, h135b, h035c, h135a]
                              · rcases h145 with ⟨h145a, h145b, h145c, h145d, h145e⟩ | ⟨h145a, h145b, h145c, h145d, h145e⟩
                                · linarith only [ht, h014d, h015c, h045c, h145b]
                                · rcases h234 with ⟨h234a, h234b, h234c, h234d, h234e⟩ | ⟨h234a, h234b, h234c, h234d, h234e⟩
                                  · linarith only [h023c, h024c, h234a]
                                  · linarith only [h023a, h024c, h034c, h234a]
                            · linarith only [ht, r23.2, r24.1, h023a, h024c, h034c, h124b, h134a, h123c]
                      · linarith only [ht, r12.2, r24.1, h023c, h024c, h123c]
                · rcases h035 with ⟨h035a, h035b, h035c, h035d, h035e⟩ | ⟨h035a, h035b, h035c, h035d, h035e⟩
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · rcases h124 with ⟨h124a, h124b, h124c, h124d, h124e⟩ | ⟨h124a, h124b, h124c, h124d, h124e⟩
                        · linarith only [ht, r01.1, r35.2, h014c, h023a, h024c, h124b, h035c]
                        · rcases h125 with ⟨h125a, h125b, h125c, h125d, h125e⟩ | ⟨h125a, h125b, h125c, h125d, h125e⟩
                          · linarith only [h015b, h023a, h025c, h125b, h035a]
                          · rcases h134 with ⟨h134a, h134b, h134c, h134d, h134e⟩ | ⟨h134a, h134b, h134c, h134d, h134e⟩
                            · linarith only [h013b, h034c, h134a, h134b]
                            · rcases h135 with ⟨h135a, h135b, h135c, h135d, h135e⟩ | ⟨h135a, h135b, h135c, h135d, h135e⟩
                              · rcases h145 with ⟨h145a, h145b, h145c, h145d, h145e⟩ | ⟨h145a, h145b, h145c, h145d, h145e⟩
                                · rcases h234 with ⟨h234a, h234b, h234c, h234d, h234e⟩ | ⟨h234a, h234b, h234c, h234d, h234e⟩
                                  · linarith only [ht, r12.1, r35.2, h023a, h024c, h035c, h123c, h234a]
                                  · linarith only [ht, h012b, h024c, h234d, h123c]
                                · linarith only [ht, h014e, h045c, h145c]
                              · linarith only [ht, r23.2, r24.1, h023a, h024c, h035c, h125b, h123c, h135a]
                      · linarith only [ht, r12.2, r24.1, h023c, h024c, h123c]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · rcases h124 with ⟨h124a, h124b, h124c, h124d, h124e⟩ | ⟨h124a, h124b, h124c, h124d, h124e⟩
                        · linarith only [h014b, h023a, h024c, h045b, h124b, h035a]
                        · rcases h125 with ⟨h125a, h125b, h125c, h125d, h125e⟩ | ⟨h125a, h125b, h125c, h125d, h125e⟩
                          · linarith only [h015b, h023a, h025c, h125b, h035a]
                          · rcases h134 with ⟨h134a, h134b, h134c, h134d, h134e⟩ | ⟨h134a, h134b, h134c, h134d, h134e⟩
                            · linarith only [h014b, h034c, h045b, h035a, h134b]
                            · rcases h135 with ⟨h135a, h135b, h135c, h135d, h135e⟩ | ⟨h135a, h135b, h135c, h135d, h135e⟩
                              · rcases h145 with ⟨h145a, h145b, h145c, h145d, h145e⟩ | ⟨h145a, h145b, h145c, h145d, h145e⟩
                                · linarith only [ht, h014d, h015c, h045c, h145b]
                                · rcases h234 with ⟨h234a, h234b, h234c, h234d, h234e⟩ | ⟨h234a, h234b, h234c, h234d, h234e⟩
                                  · linarith only [h012b, h024c, h123c, h234a]
                                  · linarith only [ht, h012b, h024c, h123c, h234d]
                              · linarith only [ht, r23.2, r24.1, h023a, h024c, h035c, h125b, h123c, h135a]
                      · linarith only [ht, r12.2, r45.1, h023c, h024b, h045c, h123c]
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · rcases h124 with ⟨h124a, h124b, h124c, h124d, h124e⟩ | ⟨h124a, h124b, h124c, h124d, h124e⟩
                        · linarith only [ht, r01.1, r23.2, h014c, h023c, h024c, h124b]
                        · rcases h125 with ⟨h125a, h125b, h125c, h125d, h125e⟩ | ⟨h125a, h125b, h125c, h125d, h125e⟩
                          · linarith only [ht, r01.1, r23.2, h015c, h023c, h025c, h125b]
                          · rcases h134 with ⟨h134a, h134b, h134c, h134d, h134e⟩ | ⟨h134a, h134b, h134c, h134d, h134e⟩
                            · linarith only [h013b, h034c, h134b, h134a]
                            · rcases h135 with ⟨h135a, h135b, h135c, h135d, h135e⟩ | ⟨h135a, h135b, h135c, h135d, h135e⟩
                              · linarith only [ht, h013d, h015c, h035c, h135b]
                              · rcases h145 with ⟨h145a, h145b, h145c, h145d, h145e⟩ | ⟨h145a, h145b, h145c, h145d, h145e⟩
                                · rcases h234 with ⟨h234a, h234b, h234c, h234d, h234e⟩ | ⟨h234a, h234b, h234c, h234d, h234e⟩
                                  · linarith only [h012b, h024c, h123c, h234a]
                                  · linarith only [ht, h012b, h024c, h234d, h123c]
                                · linarith only [ht, h014e, h045c, h145c]
                      · linarith only [ht, r12.2, r24.1, h023c, h024c, h123c]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · rcases h124 with ⟨h124a, h124b, h124c, h124d, h124e⟩ | ⟨h124a, h124b, h124c, h124d, h124e⟩
                        · linarith only [ht, h012b, r23.2, r45.1, h014b, h024c, h045c, h124b, h123c]
                        · rcases h125 with ⟨h125a, h125b, h125c, h125d, h125e⟩ | ⟨h125a, h125b, h125c, h125d, h125e⟩
                          · linarith only [h012b, h025c, h125a, h125b]
                          · rcases h134 with ⟨h134a, h134b, h134c, h134d, h134e⟩ | ⟨h134a, h134b, h134c, h134d, h134e⟩
                            · linarith only [h013b, h034c, h134a, h134b]
                            · rcases h135 with ⟨h135a, h135b, h135c, h135d, h135e⟩ | ⟨h135a, h135b, h135c, h135d, h135e⟩
                              · linarith only [ht, h013d, h015c, h035c, h135b]
                              · rcases h145 with ⟨h145a, h145b, h145c, h145d, h145e⟩ | ⟨h145a, h145b, h145c, h145d, h145e⟩
                                · linarith only [h014b, h045c, h145a, h145b]
                                · rcases h234 with ⟨h234a, h234b, h234c, h234d, h234e⟩ | ⟨h234a, h234b, h234c, h234d, h234e⟩
                                  · linarith only [h012b, h024c, h123c, h234a]
                                  · linarith only [ht, h012b, h024c, h123c, h234d]
                      · linarith only [ht, r12.2, r24.1, h023c, h024c, h123c]
          · rcases h024 with ⟨h024a, h024b, h024c, h024d, h024e⟩ | ⟨h024a, h024b, h024c, h024d, h024e⟩
            · rcases h025 with ⟨h025a, h025b, h025c, h025d, h025e⟩ | ⟨h025a, h025b, h025c, h025d, h025e⟩
              · rcases h034 with ⟨h034a, h034b, h034c, h034d, h034e⟩ | ⟨h034a, h034b, h034c, h034d, h034e⟩
                · rcases h035 with ⟨h035a, h035b, h035c, h035d, h035e⟩ | ⟨h035a, h035b, h035c, h035d, h035e⟩
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012b, h023c, h123b, h123a]
                      · rcases h124 with ⟨h124a, h124b, h124c, h124d, h124e⟩ | ⟨h124a, h124b, h124c, h124d, h124e⟩
                        · rcases h125 with ⟨h125a, h125b, h125c, h125d, h125e⟩ | ⟨h125a, h125b, h125c, h125d, h125e⟩
                          · rcases h134 with ⟨h134a, h134b, h134c, h134d, h134e⟩ | ⟨h134a, h134b, h134c, h134d, h134e⟩
                            · rcases h135 with ⟨h135a, h135b, h135c, h135d, h135e⟩ | ⟨h135a, h135b, h135c, h135d, h135e⟩
                              · rcases h145 with ⟨h145a, h145b, h145c, h145d, h145e⟩ | ⟨h145a, h145b, h145c, h145d, h145e⟩
                                · rcases h234 with ⟨h234a, h234b, h234c, h234d, h234e⟩ | ⟨h234a, h234b, h234c, h234d, h234e⟩
                                  · linarith only [ht, h023c, h024c, h234d]
                                  · linarith only [h023c, h024c, h234b]
                                · linarith only [ht, r14.2, r23.1, h023c, h024a, h045c, h145c]
                              · linarith only [ht, h013e, h035c, h135c]
                            · linarith only [ht, r23.1, r24.2, h023c, h024a, h034b, h123b, h124c, h134c]
                          · linarith only [ht, r23.1, r24.2, h023c, h025c, h125b, h124c, h125a]
                        · linarith only [ht, r12.2, r23.1, h023c, h024c, h124c]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012b, h023c, h123a, h123b]
                      · rcases h124 with ⟨h124a, h124b, h124c, h124d, h124e⟩ | ⟨h124a, h124b, h124c, h124d, h124e⟩
                        · rcases h125 with ⟨h125a, h125b, h125c, h125d, h125e⟩ | ⟨h125a, h125b, h125c, h125d, h125e⟩
                          · rcases h134 with ⟨h134a, h134b, h134c, h134d, h134e⟩ | ⟨h134a, h134b, h134c, h134d, h134e⟩
                            · rcases h135 with ⟨h135a, h135b, h135c, h135d, h135e⟩ | ⟨h135a, h135b, h135c, h135d, h135e⟩
                              · rcases h145 with ⟨h145a, h145b, h145c, h145d, h145e⟩ | ⟨h145a, h145b, h145c, h145d, h145e⟩
                                · linarith only [h014b, h045c, h145b, h145a]
                                · rcases h234 with ⟨h234a, h234b, h234c, h234d, h234e⟩ | ⟨h234a, h234b, h234c, h234d, h234e⟩
                                  · linarith only [ht, h023c, h024c, h234d]
                                  · linarith only [h023c, h024c, h234b]
                              · linarith only [ht, r23.1, r34.2, h023c, h025a, h035b, h134c, h135c]
                            · linarith only [ht, h013e, h034c, h134c]
                          · linarith only [ht, r23.1, r24.2, h023c, h025c, h125b, h124c, h125a]
                        · linarith only [ht, r12.2, r23.1, h023c, h024c, h124c]
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h013b, h023c, h025a, h035b, h123b]
                      · rcases h124 with ⟨h124a, h124b, h124c, h124d, h124e⟩ | ⟨h124a, h124b, h124c, h124d, h124e⟩
                        · rcases h125 with ⟨h125a, h125b, h125c, h125d, h125e⟩ | ⟨h125a, h125b, h125c, h125d, h125e⟩
                          · rcases h134 with ⟨h134a, h134b, h134c, h134d, h134e⟩ | ⟨h134a, h134b, h134c, h134d, h134e⟩
                            · rcases h135 with ⟨h135a, h135b, h135c, h135d, h135e⟩ | ⟨h135a, h135b, h135c, h135d, h135e⟩
                              · linarith only [ht, r23.1, r34.2, h015b, h023c, h025a, h034c, h035c, h135b]
                              · rcases h145 with ⟨h145a, h145b, h145c, h145d, h145e⟩ | ⟨h145a, h145b, h145c, h145d, h145e⟩
                                · rcases h234 with ⟨h234a, h234b, h234c, h234d, h234e⟩ | ⟨h234a, h234b, h234c, h234d, h234e⟩
                                  · linarith only [ht, h012b, h023c, h124c, h234d]
                                  · linarith only [h012b, h023c, h124c, h234b]
                                · linarith only [ht, r23.1, r24.2, h023c, h024a, h124c, h045c, h123b, h135b, h145a]
                            · linarith only [ht, r24.2, r35.1, h034c, h035c, h124c, h123b, h134b, h134a]
                          · linarith only [ht, r23.1, r24.2, h023c, h025c, h124c, h125a, h125b]
                        · linarith only [ht, r12.2, r23.1, h023c, h024c, h124c]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012b, h123b, h023c, h123a]
                      · rcases h124 with ⟨h124a, h124b, h124c, h124d, h124e⟩ | ⟨h124a, h124b, h124c, h124d, h124e⟩
                        · rcases h125 with ⟨h125a, h125b, h125c, h125d, h125e⟩ | ⟨h125a, h125b, h125c, h125d, h125e⟩
                          · rcases h134 with ⟨h134a, h134b, h134c, h134d, h134e⟩ | ⟨h134a, h134b, h134c, h134d, h134e⟩
                            · rcases h135 with ⟨h135a, h135b, h135c, h135d, h135e⟩ | ⟨h135a, h135b, h135c, h135d, h135e⟩
                              · linarith only [ht, r23.1, r34.2, h015b, h023c, h025a, h034c, h035c, h135b]
                              · rcases h145 with ⟨h145a, h145b, h145c, h145d, h145e⟩ | ⟨h145a, h145b, h145c, h145d, h145e⟩
                                · linarith only [h014b, h145a, h045c, h145b]
                                · rcases h234 with ⟨h234a, h234b, h234c, h234d, h234e⟩ | ⟨h234a, h234b, h234c, h234d, h234e⟩
                                  · linarith only [ht, h012b, h023c, h124c, h234d]
                                  · linarith only [h012b, h023c, h124c, h234b]
                            · linarith only [ht, r23.1, r24.2, h023c, h025a, h034c, h035b, h124c, h134a, h134b, h123b]
                          · linarith only [ht, r23.1, r24.2, h023c, h025c, h125a, h124c, h125b]
                        · linarith only [ht, r12.2, r23.1, h023c, h024c, h124c]
                · rcases h035 with ⟨h035a, h035b, h035c, h035d, h035e⟩ | ⟨h035a, h035b, h035c, h035d, h035e⟩
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012b, h023c, h123a, h123b]
                      · rcases h124 with ⟨h124a, h124b, h124c, h124d, h124e⟩ | ⟨h124a, h124b, h124c, h124d, h124e⟩
                        · rcases h125 with ⟨h125a, h125b, h125c, h125d, h125e⟩ | ⟨h125a, h125b, h125c, h125d, h125e⟩
                          · rcases h134 with ⟨h134a, h134b, h134c, h134d, h134e⟩ | ⟨h134a, h134b, h134c, h134d, h134e⟩
                            · linarith only [ht, r01.1, r24.2, h014c, h023b, h024c, h034c, h134b]
                            · rcases h135 with ⟨h135a, h135b, h135c, h135d, h135e⟩ | ⟨h135a, h135b, h135c, h135d, h135e⟩
                              · rcases h145 with ⟨h145a, h145b, h145c, h145d, h145e⟩ | ⟨h145a, h145b, h145c, h145d, h145e⟩
                                · rcases h234 with ⟨h234a, h234b, h234c, h234d, h234e⟩ | ⟨h234a, h234b, h234c, h234d, h234e⟩
                                  · linarith only [h023b, h024c, h034c, h234b]
                                  · linarith only [h023c, h024c, h234b]
                                · linarith only [ht, h023c, h024a, h045c, h145b, h145a, h123e, h134b]
                              · linarith only [ht, r24.2, r34.1, h034c, h035c, h124c, h135a, h123b, h135b]
                          · linarith only [ht, r23.1, r24.2, h023c, h025c, h125b, h125a, h124c]
                        · linarith only [ht, r12.2, r23.1, h023c, h024c, h124c]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012b, h023c, h123b, h123a]
                      · rcases h124 with ⟨h124a, h124b, h124c, h124d, h124e⟩ | ⟨h124a, h124b, h124c, h124d, h124e⟩
                        · rcases h125 with ⟨h125a, h125b, h125c, h125d, h125e⟩ | ⟨h125a, h125b, h125c, h125d, h125e⟩
                          · rcases h134 with ⟨h134a, h134b, h134c, h134d, h134e⟩ | ⟨h134a, h134b, h134c, h134d, h134e⟩
                            · linarith only [ht, r23.1, r35.2, h014b, h023c, h024a, h034c, h035c, h134b]
                            · rcases h135 with ⟨h135a, h135b, h135c, h135d, h135e⟩ | ⟨h135a, h135b, h135c, h135d, h135e⟩
                              · rcases h145 with ⟨h145a, h145b, h145c, h145d, h145e⟩ | ⟨h145a, h145b, h145c, h145d, h145e⟩
                                · linarith only [ht, h014d, h015c, h045c, h145b]
                                · rcases h234 with ⟨h234a, h234b, h234c, h234d, h234e⟩ | ⟨h234a, h234b, h234c, h234d, h234e⟩
                                  · linarith only [ht, r01.1, r02.2, h012c, h023b, h034c, h124c, h234b]
                                  · linarith only [h012b, h023b, h023a, h124c, h234b]
                              · linarith only [ht, r24.2, r34.1, h034c, h035c, h124c, h123b, h135b, h135a]
                          · linarith only [ht, r23.1, r24.2, h023c, h025c, h125a, h124c, h125b]
                        · linarith only [ht, r12.2, r23.1, h023c, h024c, h124c]
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012b, h023c, h123a, h123b]
                      · rcases h124 with ⟨h124a, h124b, h124c, h124d, h124e⟩ | ⟨h124a, h124b, h124c, h124d, h124e⟩
                        · rcases h125 with ⟨h125a, h125b, h125c, h125d, h125e⟩ | ⟨h125a, h125b, h125c, h125d, h125e⟩
                          · rcases h134 with ⟨h134a, h134b, h134c, h134d, h134e⟩ | ⟨h134a, h134b, h134c, h134d, h134e⟩
                            · linarith only [ht, h013d, h014c, h034c, h134b]
                            · rcases h135 with ⟨h135a, h135b, h135c, h135d, h135e⟩ | ⟨h135a, h135b, h135c, h135d, h135e⟩
                              · linarith only [h015b, h023b, h025a, h035c, h135b]
                              · rcases h145 with ⟨h145a, h145b, h145c, h145d, h145e⟩ | ⟨h145a, h145b, h145c, h145d, h145e⟩
                                · rcases h234 with ⟨h234a, h234b, h234c, h234d, h234e⟩ | ⟨h234a, h234b, h234c, h234d, h234e⟩
                                  · linarith only [h023b, h024c, h034c, h234b]
                                  · linarith only [h023c, h024c, h234b]
                                · linarith only [ht, h023c, h024a, h045c, h135b, h145a, h123e]
                          · linarith only [ht, r23.1, r24.2, h023c, h025c, h125b, h125a, h124c]
                        · linarith only [ht, r12.2, r23.1, h023c, h024c, h124c]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012b, h023c, h123b, h123a]
                      · rcases h124 with ⟨h124a, h124b, h124c, h124d, h124e⟩ | ⟨h124a, h124b, h124c, h124d, h124e⟩
                        · rcases h125 with ⟨h125a, h125b, h125c, h125d, h125e⟩ | ⟨h125a, h125b, h125c, h125d, h125e⟩
                          · rcases h134 with ⟨h134a, h134b, h134c, h134d, h134e⟩ | ⟨h134a, h134b, h134c, h134d, h134e⟩
                            · linarith only [h014b, h023b, h024a, h034c, h134b]
                            · rcases h135 with ⟨h135a, h135b, h135c, h135d, h135e⟩ | ⟨h135a, h135b, h135c, h135d, h135e⟩
                              · linarith only [h015b, h023b, h025a, h135b, h035c]
                              · rcases h145 with ⟨h145a, h145b, h145c, h145d, h145e⟩ | ⟨h145a, h145b, h145c, h145d, h145e⟩
                                · linarith only [ht, h014d, h015c, h045c, h145b]
                                · rcases h234 with ⟨h234a, h234b, h234c, h234d, h234e⟩ | ⟨h234a, h234b, h234c, h234d, h234e⟩
                                  · linarith only [h023b, h024c, h034c, h234b]
                                  · linarith only [h023c, h024c, h234b]
                          · linarith only [ht, r23.1, r24.2, h023c, h025c, h125a, h125b, h124c]
                        · linarith only [ht, r12.2, r23.1, h023c, h024c, h124c]
              · rcases h034 with ⟨h034a, h034b, h034c, h034d, h034e⟩ | ⟨h034a, h034b, h034c, h034d, h034e⟩
                · rcases h035 with ⟨h035a, h035b, h035c, h035d, h035e⟩ | ⟨h035a, h035b, h035c, h035d, h035e⟩
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012b, h023c, h123b, h123a]
                      · rcases h124 with ⟨h124a, h124b, h124c, h124d, h124e⟩ | ⟨h124a, h124b, h124c, h124d, h124e⟩
                        · rcases h125 with ⟨h125a, h125b, h125c, h125d, h125e⟩ | ⟨h125a, h125b, h125c, h125d, h125e⟩
                          · linarith only [ht, r01.1, r24.2, h015c, h024c, h025c, h125b]
                          · rcases h134 with ⟨h134a, h134b, h134c, h134d, h134e⟩ | ⟨h134a, h134b, h134c, h134d, h134e⟩
                            · rcases h135 with ⟨h135a, h135b, h135c, h135d, h135e⟩ | ⟨h135a, h135b, h135c, h135d, h135e⟩
                              · rcases h145 with ⟨h145a, h145b, h145c, h145d, h145e⟩ | ⟨h145a, h145b, h145c, h145d, h145e⟩
                                · rcases h234 with ⟨h234a, h234b, h234c, h234d, h234e⟩ | ⟨h234a, h234b, h234c, h234d, h234e⟩
                                  · linarith only [ht, h023c, h024c, h234d]
                                  · linarith only [h023c, h024c, h234b]
                                · linarith only [ht, r23.1, r24.2, h023c, h024a, h045c, h125b, h145a, h124c]
                              · linarith only [ht, r03.1, r34.2, h135c, h035c, h134c]
                            · linarith only [ht, h013e, h034c, h134c]
                        · linarith only [ht, r12.2, r23.1, h023c, h024c, h124c]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012b, h023c, h123a, h123b]
                      · rcases h124 with ⟨h124a, h124b, h124c, h124d, h124e⟩ | ⟨h124a, h124b, h124c, h124d, h124e⟩
                        · rcases h125 with ⟨h125a, h125b, h125c, h125d, h125e⟩ | ⟨h125a, h125b, h125c, h125d, h125e⟩
                          · linarith only [ht, r01.1, r24.2, h015c, h024c, h025c, h125b]
                          · rcases h134 with ⟨h134a, h134b, h134c, h134d, h134e⟩ | ⟨h134a, h134b, h134c, h134d, h134e⟩
                            · rcases h135 with ⟨h135a, h135b, h135c, h135d, h135e⟩ | ⟨h135a, h135b, h135c, h135d, h135e⟩
                              · rcases h145 with ⟨h145a, h145b, h145c, h145d, h145e⟩ | ⟨h145a, h145b, h145c, h145d, h145e⟩
                                · linarith only [h014b, h145b, h045c, h145a]
                                · rcases h234 with ⟨h234a, h234b, h234c, h234d, h234e⟩ | ⟨h234a, h234b, h234c, h234d, h234e⟩
                                  · linarith only [ht, h023c, h024c, h234d]
                                  · linarith only [h023c, h024c, h234b]
                              · linarith only [ht, r03.1, r34.2, h035c, h135c, h134c]
                            · linarith only [ht, h013e, h034c, h134c]
                        · linarith only [ht, r12.2, r23.1, h023c, h024c, h124c]
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, r24.2, r35.1, h013b, h023c, h024c, h035c, h123b]
                      · rcases h124 with ⟨h124a, h124b, h124c, h124d, h124e⟩ | ⟨h124a, h124b, h124c, h124d, h124e⟩
                        · rcases h125 with ⟨h125a, h125b, h125c, h125d, h125e⟩ | ⟨h125a, h125b, h125c, h125d, h125e⟩
                          · linarith only [h015b, h024a, h025c, h045a, h125b]
                          · rcases h134 with ⟨h134a, h134b, h134c, h134d, h134e⟩ | ⟨h134a, h134b, h134c, h134d, h134e⟩
                            · rcases h135 with ⟨h135a, h135b, h135c, h135d, h135e⟩ | ⟨h135a, h135b, h135c, h135d, h135e⟩
                              · linarith only [ht, h013d, h015c, h035c, h135b]
                              · rcases h145 with ⟨h145a, h145b, h145c, h145d, h145e⟩ | ⟨h145a, h145b, h145c, h145d, h145e⟩
                                · rcases h234 with ⟨h234a, h234b, h234c, h234d, h234e⟩ | ⟨h234a, h234b, h234c, h234d, h234e⟩
                                  · linarith only [ht, h012b, h023c, h124c, h234d]
                                  · linarith only [h012b, h023c, h234b, h124c]
                                · linarith only [ht, r23.1, r24.2, h023c, h024a, h145a, h124c, h045c, h125b]
                            · linarith only [ht, r24.2, r35.1, h034c, h035c, h124c, h134b, h123b, h134a]
                        · linarith only [ht, r12.2, r23.1, h023c, h024c, h124c]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012b, h023c, h123a, h123b]
                      · rcases h124 with ⟨h124a, h124b, h124c, h124d, h124e⟩ | ⟨h124a, h124b, h124c, h124d, h124e⟩
                        · rcases h125 with ⟨h125a, h125b, h125c, h125d, h125e⟩ | ⟨h125a, h125b, h125c, h125d, h125e⟩
                          · linarith only [ht, r01.1, r24.2, h015c, h024c, h025c, h125b]
                          · rcases h134 with ⟨h134a, h134b, h134c, h134d, h134e⟩ | ⟨h134a, h134b, h134c, h134d, h134e⟩
                            · rcases h135 with ⟨h135a, h135b, h135c, h135d, h135e⟩ | ⟨h135a, h135b, h135c, h135d, h135e⟩
                              · linarith only [ht, h013d, h015c, h035c, h135b]
                              · rcases h145 with ⟨h145a, h145b, h145c, h145d, h145e⟩ | ⟨h145a, h145b, h145c, h145d, h145e⟩
                                · linarith only [h014b, h045c, h145a, h145b]
                                · rcases h234 with ⟨h234a, h234b, h234c, h234d, h234e⟩ | ⟨h234a, h234b, h234c, h234d, h234e⟩
                                  · linarith only [ht, h023c, h024c, h234d]
                                  · linarith only [h023c, h024c, h234b]
                            · linarith only [ht, r24.2, r35.1, h034c, h035c, h134b, h123b, h134a, h124c]
                        · linarith only [ht, r12.2, r23.1, h023c, h024c, h124c]
                · rcases h035 with ⟨h035a, h035b, h035c, h035d, h035e⟩ | ⟨h035a, h035b, h035c, h035d, h035e⟩
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012b, h023c, h123a, h123b]
                      · rcases h124 with ⟨h124a, h124b, h124c, h124d, h124e⟩ | ⟨h124a, h124b, h124c, h124d, h124e⟩
                        · rcases h125 with ⟨h125a, h125b, h125c, h125d, h125e⟩ | ⟨h125a, h125b, h125c, h125d, h125e⟩
                          · linarith only [ht, r01.1, r24.2, h015c, h024c, h025c, h125b]
                          · rcases h134 with ⟨h134a, h134b, h134c, h134d, h134e⟩ | ⟨h134a, h134b, h134c, h134d, h134e⟩
                            · linarith only [ht, r01.1, r24.2, h014c, h023b, h024c, h034c, h134b]
                            · rcases h135 with ⟨h135a, h135b, h135c, h135d, h135e⟩ | ⟨h135a, h135b, h135c, h135d, h135e⟩
                              · rcases h145 with ⟨h145a, h145b, h145c, h145d, h145e⟩ | ⟨h145a, h145b, h145c, h145d, h145e⟩
                                · rcases h234 with ⟨h234a, h234b, h234c, h234d, h234e⟩ | ⟨h234a, h234b, h234c, h234d, h234e⟩
                                  · linarith only [h023b, h024c, h034c, h234b]
                                  · linarith only [h023c, h024c, h234b]
                                · linarith only [ht, r23.1, r24.2, h023c, h024a, h045c, h125b, h145a, h124c]
                              · linarith only [ht, r24.2, r34.1, h034c, h035c, h135a, h125b, h124c]
                        · linarith only [ht, r12.2, r23.1, h023c, h024c, h124c]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012b, h023c, h123a, h123b]
                      · rcases h124 with ⟨h124a, h124b, h124c, h124d, h124e⟩ | ⟨h124a, h124b, h124c, h124d, h124e⟩
                        · rcases h125 with ⟨h125a, h125b, h125c, h125d, h125e⟩ | ⟨h125a, h125b, h125c, h125d, h125e⟩
                          · linarith only [ht, r24.2, r34.1, h015b, h024c, h025c, h035a, h034c, h125b]
                          · rcases h134 with ⟨h134a, h134b, h134c, h134d, h134e⟩ | ⟨h134a, h134b, h134c, h134d, h134e⟩
                            · linarith only [ht, r25.1, r35.2, h014b, h024a, h025c, h034c, h035c, h134b]
                            · rcases h135 with ⟨h135a, h135b, h135c, h135d, h135e⟩ | ⟨h135a, h135b, h135c, h135d, h135e⟩
                              · rcases h145 with ⟨h145a, h145b, h145c, h145d, h145e⟩ | ⟨h145a, h145b, h145c, h145d, h145e⟩
                                · linarith only [ht, h013c, h014d, h135a, h045c, h145b]
                                · rcases h234 with ⟨h234a, h234b, h234c, h234d, h234e⟩ | ⟨h234a, h234b, h234c, h234d, h234e⟩
                                  · linarith only [ht, r01.1, r02.2, h012c, h023b, h034c, h234b, h124c]
                                  · linarith only [h012b, h023b, h023a, h124c, h234b]
                              · linarith only [ht, r24.2, r34.1, h034c, h035c, h125b, h124c, h135a]
                        · linarith only [ht, r12.2, r23.1, h023c, h024c, h124c]
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, r01.1, r24.2, h013c, h023c, h024c, h123b]
                      · rcases h124 with ⟨h124a, h124b, h124c, h124d, h124e⟩ | ⟨h124a, h124b, h124c, h124d, h124e⟩
                        · rcases h125 with ⟨h125a, h125b, h125c, h125d, h125e⟩ | ⟨h125a, h125b, h125c, h125d, h125e⟩
                          · linarith only [ht, r01.1, r45.2, h015c, h024a, h025c, h045c, h125b]
                          · rcases h134 with ⟨h134a, h134b, h134c, h134d, h134e⟩ | ⟨h134a, h134b, h134c, h134d, h134e⟩
                            · linarith only [ht, h013d, h014c, h034c, h134b]
                            · rcases h135 with ⟨h135a, h135b, h135c, h135d, h135e⟩ | ⟨h135a, h135b, h135c, h135d, h135e⟩
                              · linarith only [h015b, h023b, h024a, h135b, h045a, h035c]
                              · rcases h145 with ⟨h145a, h145b, h145c, h145d, h145e⟩ | ⟨h145a, h145b, h145c, h145d, h145e⟩
                                · rcases h234 with ⟨h234a, h234b, h234c, h234d, h234e⟩ | ⟨h234a, h234b, h234c, h234d, h234e⟩
                                  · linarith only [h023b, h024b, h024a, h034c, h234b]
                                  · linarith only [h023c, h024c, h234b]
                                · linarith only [ht, r23.1, r24.2, h023c, h024a, h045c, h125b, h145a, h124c]
                        · linarith only [ht, r12.2, r23.1, h023c, h024c, h124c]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, r24.2, r34.1, h013b, h023c, h024c, h034c, h123b]
                      · rcases h124 with ⟨h124a, h124b, h124c, h124d, h124e⟩ | ⟨h124a, h124b, h124c, h124d, h124e⟩
                        · rcases h125 with ⟨h125a, h125b, h125c, h125d, h125e⟩ | ⟨h125a, h125b, h125c, h125d, h125e⟩
                          · linarith only [ht, r01.1, r24.2, h015c, h024c, h025c, h125b]
                          · rcases h134 with ⟨h134a, h134b, h134c, h134d, h134e⟩ | ⟨h134a, h134b, h134c, h134d, h134e⟩
                            · linarith only [ht, h013d, h014c, h034c, h134b]
                            · rcases h135 with ⟨h135a, h135b, h135c, h135d, h135e⟩ | ⟨h135a, h135b, h135c, h135d, h135e⟩
                              · linarith only [h013b, h135a, h135b, h035c]
                              · rcases h145 with ⟨h145a, h145b, h145c, h145d, h145e⟩ | ⟨h145a, h145b, h145c, h145d, h145e⟩
                                · linarith only [ht, h014d, h015c, h145b, h045c]
                                · rcases h234 with ⟨h234a, h234b, h234c, h234d, h234e⟩ | ⟨h234a, h234b, h234c, h234d, h234e⟩
                                  · linarith only [h023b, h024c, h034c, h234b]
                                  · linarith only [h023c, h024c, h234b]
                        · linarith only [ht, r12.2, r23.1, h023c, h024c, h124c]
            · rcases h025 with ⟨h025a, h025b, h025c, h025d, h025e⟩ | ⟨h025a, h025b, h025c, h025d, h025e⟩
              · rcases h034 with ⟨h034a, h034b, h034c, h034d, h034e⟩ | ⟨h034a, h034b, h034c, h034d, h034e⟩
                · rcases h035 with ⟨h035a, h035b, h035c, h035d, h035e⟩ | ⟨h035a, h035b, h035c, h035d, h035e⟩
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, r01.1, r25.2, h013c, h023c, h025c, h123b]
                      · rcases h124 with ⟨h124a, h124b, h124c, h124d, h124e⟩ | ⟨h124a, h124b, h124c, h124d, h124e⟩
                        · linarith only [ht, r01.1, r25.2, h014c, h024c, h025c, h124b]
                        · rcases h125 with ⟨h125a, h125b, h125c, h125d, h125e⟩ | ⟨h125a, h125b, h125c, h125d, h125e⟩
                          · rcases h134 with ⟨h134a, h134b, h134c, h134d, h134e⟩ | ⟨h134a, h134b, h134c, h134d, h134e⟩
                            · rcases h135 with ⟨h135a, h135b, h135c, h135d, h135e⟩ | ⟨h135a, h135b, h135c, h135d, h135e⟩
                              · rcases h145 with ⟨h145a, h145b, h145c, h145d, h145e⟩ | ⟨h145a, h145b, h145c, h145d, h145e⟩
                                · rcases h234 with ⟨h234a, h234b, h234c, h234d, h234e⟩ | ⟨h234a, h234b, h234c, h234d, h234e⟩
                                  · rcases h235 with ⟨h235a, h235b, h235c, h235d, h235e⟩ | ⟨h235a, h235b, h235c, h235d, h235e⟩
                                    · linarith only [ht, h023c, h025c, h235d]
                                    · linarith only [h023c, h025c, h235b]
                                  · linarith only [ht, r01.1, r25.2, h013c, h024c, h025c, h134c, h234a]
                                · linarith only [ht, h014e, h045c, h145c]
                              · linarith only [ht, r03.1, r34.2, h035c, h134c, h135c]
                            · linarith only [ht, h013e, h034c, h134c]
                          · linarith only [ht, r12.2, r24.1, h024c, h025c, h125c]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012b, h023c, h123a, h123b]
                      · rcases h124 with ⟨h124a, h124b, h124c, h124d, h124e⟩ | ⟨h124a, h124b, h124c, h124d, h124e⟩
                        · linarith only [ht, r25.2, r45.1, h014b, h024c, h025c, h045c, h124b]
                        · rcases h125 with ⟨h125a, h125b, h125c, h125d, h125e⟩ | ⟨h125a, h125b, h125c, h125d, h125e⟩
                          · rcases h134 with ⟨h134a, h134b, h134c, h134d, h134e⟩ | ⟨h134a, h134b, h134c, h134d, h134e⟩
                            · rcases h135 with ⟨h135a, h135b, h135c, h135d, h135e⟩ | ⟨h135a, h135b, h135c, h135d, h135e⟩
                              · rcases h145 with ⟨h145a, h145b, h145c, h145d, h145e⟩ | ⟨h145a, h145b, h145c, h145d, h145e⟩
                                · linarith only [ht, h014d, h015c, h045c, h145b]
                                · rcases h234 with ⟨h234a, h234b, h234c, h234d, h234e⟩ | ⟨h234a, h234b, h234c, h234d, h234e⟩
                                  · rcases h235 with ⟨h235a, h235b, h235c, h235d, h235e⟩ | ⟨h235a, h235b, h235c, h235d, h235e⟩
                                    · linarith only [ht, h023c, h025c, h235d]
                                    · linarith only [h023c, h025c, h235b]
                                  · linarith only [ht, r01.1, r25.2, h013c, h024c, h025c, h134c, h234a]
                              · linarith only [ht, r03.1, r34.2, h035c, h135c, h134c]
                            · linarith only [ht, h013e, h034c, h134c]
                          · linarith only [ht, r12.2, r23.1, h023c, h025c, h125c]
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012b, h023c, h123a, h123b]
                      · rcases h124 with ⟨h124a, h124b, h124c, h124d, h124e⟩ | ⟨h124a, h124b, h124c, h124d, h124e⟩
                        · linarith only [ht, r01.1, r25.2, h014c, h024c, h025c, h124b]
                        · rcases h125 with ⟨h125a, h125b, h125c, h125d, h125e⟩ | ⟨h125a, h125b, h125c, h125d, h125e⟩
                          · rcases h134 with ⟨h134a, h134b, h134c, h134d, h134e⟩ | ⟨h134a, h134b, h134c, h134d, h134e⟩
                            · rcases h135 with ⟨h135a, h135b, h135c, h135d, h135e⟩ | ⟨h135a, h135b, h135c, h135d, h135e⟩
                              · linarith only [ht, r23.1, r34.2, h015b, h023c, h025a, h034c, h035c, h135b]
                              · rcases h145 with ⟨h145a, h145b, h145c, h145d, h145e⟩ | ⟨h145a, h145b, h145c, h145d, h145e⟩
                                · rcases h234 with ⟨h234a, h234b, h234c, h234d, h234e⟩ | ⟨h234a, h234b, h234c, h234d, h234e⟩
                                  · linarith only [ht, h024c, h025a, h035b, h034c, h234e]
                                  · linarith only [h024c, h025a, h035b, h034c, h234a]
                                · linarith only [ht, h023c, h025a, h035b, h045c, h123e, h034a, h135b, h145a]
                            · linarith only [ht, r23.1, r25.2, h023c, h025a, h035b, h034c, h134a, h125c, h124b]
                          · linarith only [ht, r12.2, r23.1, h023c, h025c, h125c]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012b, h023c, h123b, h123a]
                      · rcases h124 with ⟨h124a, h124b, h124c, h124d, h124e⟩ | ⟨h124a, h124b, h124c, h124d, h124e⟩
                        · linarith only [h014b, h024c, h025a, h035b, h034a, h124b]
                        · rcases h125 with ⟨h125a, h125b, h125c, h125d, h125e⟩ | ⟨h125a, h125b, h125c, h125d, h125e⟩
                          · rcases h134 with ⟨h134a, h134b, h134c, h134d, h134e⟩ | ⟨h134a, h134b, h134c, h134d, h134e⟩
                            · rcases h135 with ⟨h135a, h135b, h135c, h135d, h135e⟩ | ⟨h135a, h135b, h135c, h135d, h135e⟩
                              · linarith only [ht, r23.1, r34.2, h015b, h023c, h025a, h034c, h035c, h135b]
                              · rcases h145 with ⟨h145a, h145b, h145c, h145d, h145e⟩ | ⟨h145a, h145b, h145c, h145d, h145e⟩
                                · linarith only [ht, h014d, h015c, h045c, h145b]
                                · rcases h234 with ⟨h234a, h234b, h234c, h234d, h234e⟩ | ⟨h234a, h234b, h234c, h234d, h234e⟩
                                  · linarith only [ht, h024c, h025a, h035b, h034c, h234e]
                                  · linarith only [h024c, h025a, h035b, h034c, h234a]
                            · linarith only [ht, h024c, h025a, h035b, h034c, h124e, h134a]
                          · linarith only [ht, r12.2, r24.1, h024c, h025c, h125c]
                · rcases h035 with ⟨h035a, h035b, h035c, h035d, h035e⟩ | ⟨h035a, h035b, h035c, h035d, h035e⟩
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, r01.1, r25.2, h013c, h023c, h025c, h123b]
                      · rcases h124 with ⟨h124a, h124b, h124c, h124d, h124e⟩ | ⟨h124a, h124b, h124c, h124d, h124e⟩
                        · linarith only [ht, r01.1, r25.2, h014c, h024c, h025c, h124b]
                        · rcases h125 with ⟨h125a, h125b, h125c, h125d, h125e⟩ | ⟨h125a, h125b, h125c, h125d, h125e⟩
                          · rcases h134 with ⟨h134a, h134b, h134c, h134d, h134e⟩ | ⟨h134a, h134b, h134c, h134d, h134e⟩
                            · linarith only [ht, r01.1, r35.2, h014c, h034c, h035c, h134b]
                            · rcases h135 with ⟨h135a, h135b, h135c, h135d, h135e⟩ | ⟨h135a, h135b, h135c, h135d, h135e⟩
                              · rcases h145 with ⟨h145a, h145b, h145c, h145d, h145e⟩ | ⟨h145a, h145b, h145c, h145d, h145e⟩
                                · rcases h234 with ⟨h234a, h234b, h234c, h234d, h234e⟩ | ⟨h234a, h234b, h234c, h234d, h234e⟩
                                  · linarith only [ht, r23.1, r35.2, h034c, h035c, h234c]
                                  · linarith only [ht, r25.2, r34.1, h023c, h025c, h234c]
                                · linarith only [ht, h014e, h045c, h145c]
                              · linarith only [ht, r25.2, r34.1, h034c, h035c, h135b, h123b, h135a, h125c]
                          · linarith only [ht, r12.2, r23.1, h023c, h025c, h125c]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012b, h023c, h123b, h123a]
                      · rcases h124 with ⟨h124a, h124b, h124c, h124d, h124e⟩ | ⟨h124a, h124b, h124c, h124d, h124e⟩
                        · linarith only [h014b, h024c, h025a, h045b, h124b]
                        · rcases h125 with ⟨h125a, h125b, h125c, h125d, h125e⟩ | ⟨h125a, h125b, h125c, h125d, h125e⟩
                          · rcases h134 with ⟨h134a, h134b, h134c, h134d, h134e⟩ | ⟨h134a, h134b, h134c, h134d, h134e⟩
                            · linarith only [ht, r23.1, r35.2, h014b, h023c, h025a, h034c, h035c, h045b, h134b]
                            · rcases h135 with ⟨h135a, h135b, h135c, h135d, h135e⟩ | ⟨h135a, h135b, h135c, h135d, h135e⟩
                              · rcases h145 with ⟨h145a, h145b, h145c, h145d, h145e⟩ | ⟨h145a, h145b, h145c, h145d, h145e⟩
                                · linarith only [ht, h014d, h015c, h045c, h145b]
                                · rcases h234 with ⟨h234a, h234b, h234c, h234d, h234e⟩ | ⟨h234a, h234b, h234c, h234d, h234e⟩
                                  · linarith only [ht, r23.1, r25.2, h023b, h034c, h025c, h234c]
                                  · linarith only [ht, r25.2, r34.1, h023c, h025c, h234c]
                              · linarith only [ht, h023c, h034b, h025a, h035c, h045b, h123e, h135a, h135b]
                          · linarith only [ht, r12.2, r23.1, h023c, h025c, h125c]
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012b, h023c, h123a, h123b]
                      · rcases h124 with ⟨h124a, h124b, h124c, h124d, h124e⟩ | ⟨h124a, h124b, h124c, h124d, h124e⟩
                        · linarith only [ht, r01.1, r25.2, h014c, h024c, h025c, h124b]
                        · rcases h125 with ⟨h125a, h125b, h125c, h125d, h125e⟩ | ⟨h125a, h125b, h125c, h125d, h125e⟩
                          · rcases h134 with ⟨h134a, h134b, h134c, h134d, h134e⟩ | ⟨h134a, h134b, h134c, h134d, h134e⟩
                            · linarith only [ht, h013d, h014c, h034c, h134b]
                            · rcases h135 with ⟨h135a, h135b, h135c, h135d, h135e⟩ | ⟨h135a, h135b, h135c, h135d, h135e⟩
                              · linarith only [h015b, h023b, h025a, h135b, h035c]
                              · rcases h145 with ⟨h145a, h145b, h145c, h145d, h145e⟩ | ⟨h145a, h145b, h145c, h145d, h145e⟩
                                · rcases h234 with ⟨h234a, h234b, h234c, h234d, h234e⟩ | ⟨h234a, h234b, h234c, h234d, h234e⟩
                                  · linarith only [ht, r23.1, r25.2, h023b, h034c, h025c, h234c]
                                  · linarith only [ht, r25.2, r34.1, h023c, h025c, h234c]
                                · linarith only [ht, h014e, h045c, h145c]
                          · linarith only [ht, r12.2, r23.1, h023c, h025c, h125c]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012b, h023c, h123a, h123b]
                      · rcases h124 with ⟨h124a, h124b, h124c, h124d, h124e⟩ | ⟨h124a, h124b, h124c, h124d, h124e⟩
                        · linarith only [h014b, h024c, h025a, h045b, h124b]
                        · rcases h125 with ⟨h125a, h125b, h125c, h125d, h125e⟩ | ⟨h125a, h125b, h125c, h125d, h125e⟩
                          · rcases h134 with ⟨h134a, h134b, h134c, h134d, h134e⟩ | ⟨h134a, h134b, h134c, h134d, h134e⟩
                            · linarith only [h014b, h023b, h025a, h034c, h045b, h134b]
                            · rcases h135 with ⟨h135a, h135b, h135c, h135d, h135e⟩ | ⟨h135a, h135b, h135c, h135d, h135e⟩
                              · linarith only [h015b, h023b, h025a, h035c, h135b]
                              · rcases h145 with ⟨h145a, h145b, h145c, h145d, h145e⟩ | ⟨h145a, h145b, h145c, h145d, h145e⟩
                                · linarith only [ht, h014d, h015c, h045c, h145b]
                                · rcases h234 with ⟨h234a, h234b, h234c, h234d, h234e⟩ | ⟨h234a, h234b, h234c, h234d, h234e⟩
                                  · linarith only [ht, r23.1, r25.2, h023b, h034c, h025c, h234c]
                                  · linarith only [ht, r25.2, r34.1, h023c, h025c, h234c]
                          · linarith only [ht, r12.2, r23.1, h023c, h025c, h125c]
              · rcases h034 with ⟨h034a, h034b, h034c, h034d, h034e⟩ | ⟨h034a, h034b, h034c, h034d, h034e⟩
                · rcases h035 with ⟨h035a, h035b, h035c, h035d, h035e⟩ | ⟨h035a, h035b, h035c, h035d, h035e⟩
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012b, h023c, h123b, h123a]
                      · rcases h124 with ⟨h124a, h124b, h124c, h124d, h124e⟩ | ⟨h124a, h124b, h124c, h124d, h124e⟩
                        · linarith only [ht, h012d, h014c, h024c, h124b]
                        · rcases h125 with ⟨h125a, h125b, h125c, h125d, h125e⟩ | ⟨h125a, h125b, h125c, h125d, h125e⟩
                          · linarith only [ht, h012d, h015c, h025c, h125b]
                          · rcases h134 with ⟨h134a, h134b, h134c, h134d, h134e⟩ | ⟨h134a, h134b, h134c, h134d, h134e⟩
                            · rcases h135 with ⟨h135a, h135b, h135c, h135d, h135e⟩ | ⟨h135a, h135b, h135c, h135d, h135e⟩
                              · rcases h145 with ⟨h145a, h145b, h145c, h145d, h145e⟩ | ⟨h145a, h145b, h145c, h145d, h145e⟩
                                · rcases h234 with ⟨h234a, h234b, h234c, h234d, h234e⟩ | ⟨h234a, h234b, h234c, h234d, h234e⟩
                                  · rcases h235 with ⟨h235a, h235b, h235c, h235d, h235e⟩ | ⟨h235a, h235b, h235c, h235d, h235e⟩
                                    · rcases h245 with ⟨h245a, h245b, h245c, h245d, h245e⟩ | ⟨h245a, h245b, h245c, h245d, h245e⟩
                                      · rcases h345 with ⟨h345a, h345b, h345c, h345d, h345e⟩ | ⟨h345a, h345b, h345c, h345d, h345e⟩
                                        · linarith only [ht, r01.1, r45.2, h013c, h134c, h345c]
                                        · linarith only [ht, h034e, h045c, h345c]
                                      · linarith only [ht, h014c, h015d, h025a, h145c, h245a]
                                    · linarith only [ht, h012d, h013c, h135c, h025c, h235a]
                                  · linarith only [ht, h012d, h013a, h024c, h034c, h234a]
                                · linarith only [ht, h014e, h045c, h145c]
                              · linarith only [ht, r03.1, r34.2, h134c, h035c, h135c]
                            · linarith only [ht, h013e, h034c, h134c]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, h012d, h013c, h023c, h123b]
                      · rcases h124 with ⟨h124a, h124b, h124c, h124d, h124e⟩ | ⟨h124a, h124b, h124c, h124d, h124e⟩
                        · linarith only [ht, h012d, h014c, h024c, h124b]
                        · rcases h125 with ⟨h125a, h125b, h125c, h125d, h125e⟩ | ⟨h125a, h125b, h125c, h125d, h125e⟩
                          · linarith only [h012b, h125a, h025c, h125b]
                          · rcases h134 with ⟨h134a, h134b, h134c, h134d, h134e⟩ | ⟨h134a, h134b, h134c, h134d, h134e⟩
                            · rcases h135 with ⟨h135a, h135b, h135c, h135d, h135e⟩ | ⟨h135a, h135b, h135c, h135d, h135e⟩
                              · rcases h145 with ⟨h145a, h145b, h145c, h145d, h145e⟩ | ⟨h145a, h145b, h145c, h145d, h145e⟩
                                · linarith only [ht, h014d, h015c, h145b, h045c]
                                · rcases h234 with ⟨h234a, h234b, h234c, h234d, h234e⟩ | ⟨h234a, h234b, h234c, h234d, h234e⟩
                                  · rcases h235 with ⟨h235a, h235b, h235c, h235d, h235e⟩ | ⟨h235a, h235b, h235c, h235d, h235e⟩
                                    · rcases h245 with ⟨h245a, h245b, h245c, h245d, h245e⟩ | ⟨h245a, h245b, h245c, h245d, h245e⟩
                                      · linarith only [ht, h024e, h045c, h245c]
                                      · rcases h345 with ⟨h345a, h345b, h345c, h345d, h345e⟩ | ⟨h345a, h345b, h345c, h345d, h345e⟩
                                        · linarith only [ht, r01.1, r24.2, h013c, h135c, h245c, h345b]
                                        · linarith only [ht, h012d, h013c, h024c, h135c, h245c, h345e]
                                    · linarith only [ht, h012d, h013c, h025c, h235a, h135c]
                                  · linarith only [ht, h012d, h013c, h024c, h134c, h234a]
                              · linarith only [ht, r03.1, r34.2, h134c, h035c, h135c]
                            · linarith only [ht, h013e, h034c, h134c]
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, h012d, h013c, h023c, h123b]
                      · rcases h124 with ⟨h124a, h124b, h124c, h124d, h124e⟩ | ⟨h124a, h124b, h124c, h124d, h124e⟩
                        · linarith only [ht, h012d, h014c, h024c, h124b]
                        · rcases h125 with ⟨h125a, h125b, h125c, h125d, h125e⟩ | ⟨h125a, h125b, h125c, h125d, h125e⟩
                          · linarith only [h012b, h125b, h125a, h025c]
                          · rcases h134 with ⟨h134a, h134b, h134c, h134d, h134e⟩ | ⟨h134a, h134b, h134c, h134d, h134e⟩
                            · rcases h135 with ⟨h135a, h135b, h135c, h135d, h135e⟩ | ⟨h135a, h135b, h135c, h135d, h135e⟩
                              · linarith only [ht, r01.1, r34.2, h013b, h015c, h134c, h035c, h135b]
                              · rcases h145 with ⟨h145a, h145b, h145c, h145d, h145e⟩ | ⟨h145a, h145b, h145c, h145d, h145e⟩
                                · rcases h234 with ⟨h234a, h234b, h234c, h234d, h234e⟩ | ⟨h234a, h234b, h234c, h234d, h234e⟩
                                  · rcases h235 with ⟨h235a, h235b, h235c, h235d, h235e⟩ | ⟨h235a, h235b, h235c, h235d, h235e⟩
                                    · linarith only [ht, r23.1, r34.2, h013b, h134c, h035c, h235c]
                                    · rcases h245 with ⟨h245a, h245b, h245c, h245d, h245e⟩ | ⟨h245a, h245b, h245c, h245d, h245e⟩
                                      · rcases h345 with ⟨h345a, h345b, h345c, h345d, h345e⟩ | ⟨h345a, h345b, h345c, h345d, h345e⟩
                                        · linarith only [ht, r02.2, r03.1, h013b, h023c, h134c, h235c, h345a]
                                        · linarith only [ht, h012d, h014a, h023c, h045a, h045b, h235c, h345a]
                                      · linarith only [ht, h012d, h014c, h023c, h145c, h235b, h245a]
                                  · linarith only [ht, r01.1, r45.2, h013c, h014b, h024a, h134c, h145c, h234a]
                                · linarith only [ht, h034e, h045c, h134c, h145a, h135b]
                            · linarith only [ht, r13.2, r35.1, h034c, h134c, h035c]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, h012d, h013c, h023c, h123b]
                      · rcases h124 with ⟨h124a, h124b, h124c, h124d, h124e⟩ | ⟨h124a, h124b, h124c, h124d, h124e⟩
                        · linarith only [ht, h012d, h014c, h024c, h124b]
                        · rcases h125 with ⟨h125a, h125b, h125c, h125d, h125e⟩ | ⟨h125a, h125b, h125c, h125d, h125e⟩
                          · linarith only [ht, h012d, h015c, h025c, h125b]
                          · rcases h134 with ⟨h134a, h134b, h134c, h134d, h134e⟩ | ⟨h134a, h134b, h134c, h134d, h134e⟩
                            · rcases h135 with ⟨h135a, h135b, h135c, h135d, h135e⟩ | ⟨h135a, h135b, h135c, h135d, h135e⟩
                              · linarith only [ht, r01.1, r34.2, h013b, h015c, h135b, h035c, h134c]
                              · rcases h145 with ⟨h145a, h145b, h145c, h145d, h145e⟩ | ⟨h145a, h145b, h145c, h145d, h145e⟩
                                · linarith only [ht, h014d, h015c, h045c, h145b]
                                · rcases h234 with ⟨h234a, h234b, h234c, h234d, h234e⟩ | ⟨h234a, h234b, h234c, h234d, h234e⟩
                                  · rcases h235 with ⟨h235a, h235b, h235c, h235d, h235e⟩ | ⟨h235a, h235b, h235c, h235d, h235e⟩
                                    · linarith only [ht, r23.1, r34.2, h013b, h035c, h134c, h235c]
                                    · rcases h245 with ⟨h245a, h245b, h245c, h245d, h245e⟩ | ⟨h245a, h245b, h245c, h245d, h245e⟩
                                      · linarith only [ht, h024e, h045c, h245c]
                                      · rcases h345 with ⟨h345a, h345b, h345c, h345d, h345e⟩ | ⟨h345a, h345b, h345c, h345d, h345e⟩
                                        · linarith only [ht, r02.2, r03.1, h013b, h023c, h134c, h235c, h345a]
                                        · linarith only [ht, h012d, h013c, h023c, h134c, h235c, h345d]
                                  · linarith only [ht, h013c, h014d, h024a, h134c, h234a]
                            · linarith only [ht, h013e, h034c, h134c]
                · rcases h035 with ⟨h035a, h035b, h035c, h035d, h035e⟩ | ⟨h035a, h035b, h035c, h035d, h035e⟩
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, h012d, h013c, h023c, h123b]
                      · rcases h124 with ⟨h124a, h124b, h124c, h124d, h124e⟩ | ⟨h124a, h124b, h124c, h124d, h124e⟩
                        · linarith only [h012b, h024c, h124a, h124b]
                        · rcases h125 with ⟨h125a, h125b, h125c, h125d, h125e⟩ | ⟨h125a, h125b, h125c, h125d, h125e⟩
                          · linarith only [h012b, h125b, h125a, h025c]
                          · rcases h134 with ⟨h134a, h134b, h134c, h134d, h134e⟩ | ⟨h134a, h134b, h134c, h134d, h134e⟩
                            · linarith only [ht, r01.1, r35.2, h014c, h034c, h035c, h134b]
                            · rcases h135 with ⟨h135a, h135b, h135c, h135d, h135e⟩ | ⟨h135a, h135b, h135c, h135d, h135e⟩
                              · rcases h145 with ⟨h145a, h145b, h145c, h145d, h145e⟩ | ⟨h145a, h145b, h145c, h145d, h145e⟩
                                · rcases h234 with ⟨h234a, h234b, h234c, h234d, h234e⟩ | ⟨h234a, h234b, h234c, h234d, h234e⟩
                                  · linarith only [ht, h023e, h034c, h234c]
                                  · rcases h235 with ⟨h235a, h235b, h235c, h235d, h235e⟩ | ⟨h235a, h235b, h235c, h235d, h235e⟩
                                    · rcases h245 with ⟨h245a, h245b, h245c, h245d, h245e⟩ | ⟨h245a, h245b, h245c, h245d, h245e⟩
                                      · rcases h345 with ⟨h345a, h345b, h345c, h345d, h345e⟩ | ⟨h345a, h345b, h345c, h345d, h345e⟩
                                        · linarith only [ht, h023a, h035c, h234c, h345d]
                                        · linarith only [ht, h012d, h013c, h023c, h234c, h135c, h345b]
                                      · linarith only [ht, h012d, h014a, h045c, h025c, h245a]
                                    · linarith only [ht, h012d, h013c, h025c, h135c, h235a]
                                · linarith only [ht, r34.1, r35.2, h034c, h145c, h045b, h134b, h035a, h135c]
                              · linarith only [ht, r13.2, r34.1, h034c, h035c, h135c]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, h012d, h013c, h023c, h123b]
                      · rcases h124 with ⟨h124a, h124b, h124c, h124d, h124e⟩ | ⟨h124a, h124b, h124c, h124d, h124e⟩
                        · linarith only [ht, h012d, h014c, h024c, h124b]
                        · rcases h125 with ⟨h125a, h125b, h125c, h125d, h125e⟩ | ⟨h125a, h125b, h125c, h125d, h125e⟩
                          · linarith only [ht, h012d, h015c, h025c, h125b]
                          · rcases h134 with ⟨h134a, h134b, h134c, h134d, h134e⟩ | ⟨h134a, h134b, h134c, h134d, h134e⟩
                            · linarith only [ht, r01.1, r35.2, h014c, h034c, h035c, h134b]
                            · rcases h135 with ⟨h135a, h135b, h135c, h135d, h135e⟩ | ⟨h135a, h135b, h135c, h135d, h135e⟩
                              · rcases h145 with ⟨h145a, h145b, h145c, h145d, h145e⟩ | ⟨h145a, h145b, h145c, h145d, h145e⟩
                                · linarith only [ht, h014d, h015c, h045c, h145b]
                                · rcases h234 with ⟨h234a, h234b, h234c, h234d, h234e⟩ | ⟨h234a, h234b, h234c, h234d, h234e⟩
                                  · linarith only [ht, r23.1, r35.2, h034c, h035c, h234c]
                                  · rcases h235 with ⟨h235a, h235b, h235c, h235d, h235e⟩ | ⟨h235a, h235b, h235c, h235d, h235e⟩
                                    · rcases h245 with ⟨h245a, h245b, h245c, h245d, h245e⟩ | ⟨h245a, h245b, h245c, h245d, h245e⟩
                                      · linarith only [ht, r34.1, r35.2, h045c, h035c, h034b, h234c, h245b, h235a]
                                      · rcases h345 with ⟨h345a, h345b, h345c, h345d, h345e⟩ | ⟨h345a, h345b, h345c, h345d, h345e⟩
                                        · linarith only [ht, r02.2, r03.1, h024c, h035c, h245c, h345b]
                                        · linarith only [ht, r03.2, r45.1, h012d, h013c, h023a, h024c, h234c, h135c, h245c, h345b]
                                    · linarith only [ht, h012d, h013a, h013b, h025c, h135c, h235a]
                              · linarith only [ht, r13.2, r34.1, h034c, h035c, h135c]
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, h012d, h013c, h023c, h123b]
                      · rcases h124 with ⟨h124a, h124b, h124c, h124d, h124e⟩ | ⟨h124a, h124b, h124c, h124d, h124e⟩
                        · linarith only [h012b, h024c, h124a, h124b]
                        · rcases h125 with ⟨h125a, h125b, h125c, h125d, h125e⟩ | ⟨h125a, h125b, h125c, h125d, h125e⟩
                          · linarith only [h012b, h125a, h025c, h125b]
                          · rcases h134 with ⟨h134a, h134b, h134c, h134d, h134e⟩ | ⟨h134a, h134b, h134c, h134d, h134e⟩
                            · linarith only [ht, h013d, h014c, h034c, h134b]
                            · rcases h135 with ⟨h135a, h135b, h135c, h135d, h135e⟩ | ⟨h135a, h135b, h135c, h135d, h135e⟩
                              · linarith only [ht, h013d, h015c, h035c, h135b]
                              · rcases h145 with ⟨h145a, h145b, h145c, h145d, h145e⟩ | ⟨h145a, h145b, h145c, h145d, h145e⟩
                                · rcases h234 with ⟨h234a, h234b, h234c, h234d, h234e⟩ | ⟨h234a, h234b, h234c, h234d, h234e⟩
                                  · linarith only [ht, h023e, h034c, h234c]
                                  · rcases h235 with ⟨h235a, h235b, h235c, h235d, h235e⟩ | ⟨h235a, h235b, h235c, h235d, h235e⟩
                                    · linarith only [ht, r34.1, r45.2, h013d, h014c, h035c, h234c, h145c, h235c]
                                    · rcases h245 with ⟨h245a, h245b, h245c, h245d, h245e⟩ | ⟨h245a, h245b, h245c, h245d, h245e⟩
                                      · rcases h345 with ⟨h345a, h345b, h345c, h345d, h345e⟩ | ⟨h345a, h345b, h345c, h345d, h345e⟩
                                        · linarith only [ht, h012d, h014c, h023c, h145c, h235c, h345e]
                                        · linarith only [ht, h012d, h014c, h023c, h145c, h235c, h345a]
                                      · linarith only [ht, h012d, h014c, h023c, h145c, h235b, h245a]
                                · linarith only [ht, h014e, h045c, h145c]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, h012d, h013c, h023c, h123b]
                      · rcases h124 with ⟨h124a, h124b, h124c, h124d, h124e⟩ | ⟨h124a, h124b, h124c, h124d, h124e⟩
                        · linarith only [ht, h012d, h014c, h024c, h124b]
                        · rcases h125 with ⟨h125a, h125b, h125c, h125d, h125e⟩ | ⟨h125a, h125b, h125c, h125d, h125e⟩
                          · linarith only [h012b, h025c, h125a, h125b]
                          · rcases h134 with ⟨h134a, h134b, h134c, h134d, h134e⟩ | ⟨h134a, h134b, h134c, h134d, h134e⟩
                            · linarith only [ht, h013d, h014c, h034c, h134b]
                            · rcases h135 with ⟨h135a, h135b, h135c, h135d, h135e⟩ | ⟨h135a, h135b, h135c, h135d, h135e⟩
                              · linarith only [ht, h013d, h015c, h035c, h135b]
                              · rcases h145 with ⟨h145a, h145b, h145c, h145d, h145e⟩ | ⟨h145a, h145b, h145c, h145d, h145e⟩
                                · linarith only [ht, h014d, h015c, h045c, h145b]
                                · rcases h234 with ⟨h234a, h234b, h234c, h234d, h234e⟩ | ⟨h234a, h234b, h234c, h234d, h234e⟩
                                  · linarith only [ht, h023e, h034c, h234c]
                                  · rcases h235 with ⟨h235a, h235b, h235c, h235d, h235e⟩ | ⟨h235a, h235b, h235c, h235d, h235e⟩
                                    · linarith only [ht, r03.2, r34.1, h035c, h235c, h234c]
                                    · rcases h245 with ⟨h245a, h245b, h245c, h245d, h245e⟩ | ⟨h245a, h245b, h245c, h245d, h245e⟩
                                      · linarith only [ht, h024e, h045c, h245c]
                                      · rcases h345 with ⟨h345a, h345b, h345c, h345d, h345e⟩ | ⟨h345a, h345b, h345c, h345d, h345e⟩
                                        · linarith only [ht, h024a, h034e, h345c, h245c]
                                        · linarith only [ht, r02.2, r45.1, h023c, h234c, h345c]
        · rcases h023 with ⟨h023a, h023b, h023c, h023d, h023e⟩ | ⟨h023a, h023b, h023c, h023d, h023e⟩
          · rcases h024 with ⟨h024a, h024b, h024c, h024d, h024e⟩ | ⟨h024a, h024b, h024c, h024d, h024e⟩
            · rcases h025 with ⟨h025a, h025b, h025c, h025d, h025e⟩ | ⟨h025a, h025b, h025c, h025d, h025e⟩
              · rcases h034 with ⟨h034a, h034b, h034c, h034d, h034e⟩ | ⟨h034a, h034b, h034c, h034d, h034e⟩
                · rcases h035 with ⟨h035a, h035b, h035c, h035d, h035e⟩ | ⟨h035a, h035b, h035c, h035d, h035e⟩
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, r15.1, r23.2, h012c, h015c, h123c]
                      · linarith only [ht, r12.2, h012a, r15.1, h015c, h023c, h123c]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, r15.1, r23.2, h012c, h015c, h123c]
                      · linarith only [ht, r12.2, h012a, r15.1, h015c, h023c, h123c]
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, r15.1, r23.2, h012c, h015c, h123c]
                      · linarith only [ht, r12.2, h012a, r15.1, h015c, h023c, h123c]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, r15.1, r23.2, h012c, h015c, h123c]
                      · linarith only [ht, r12.2, h012a, r15.1, h015c, h023c, h123c]
                · rcases h035 with ⟨h035a, h035b, h035c, h035d, h035e⟩ | ⟨h035a, h035b, h035c, h035d, h035e⟩
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, r15.1, r23.2, h012c, h015c, h123c]
                      · linarith only [ht, r12.2, h012a, r15.1, h015c, h023c, h123c]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, r15.1, r23.2, h012c, h015c, h123c]
                      · linarith only [ht, r12.2, h012a, r15.1, h015c, h023c, h123c]
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, r15.1, r23.2, h012c, h015c, h123c]
                      · linarith only [ht, r12.2, h012a, r15.1, h015c, h023c, h123c]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, r15.1, r23.2, h012c, h015c, h123c]
                      · linarith only [ht, r12.2, h012a, r15.1, h015c, h023c, h123c]
              · rcases h034 with ⟨h034a, h034b, h034c, h034d, h034e⟩ | ⟨h034a, h034b, h034c, h034d, h034e⟩
                · rcases h035 with ⟨h035a, h035b, h035c, h035d, h035e⟩ | ⟨h035a, h035b, h035c, h035d, h035e⟩
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, r15.1, r23.2, h012c, h015c, h123c]
                      · linarith only [ht, r12.2, h012a, r15.1, h015c, h023c, h123c]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, r15.1, r23.2, h012c, h015c, h123c]
                      · linarith only [ht, r12.2, h012a, r15.1, h015c, h023c, h123c]
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, r15.1, r23.2, h012c, h015c, h123c]
                      · linarith only [ht, r12.2, h012a, r15.1, h015c, h023c, h123c]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, r15.1, r23.2, h012c, h015c, h123c]
                      · linarith only [ht, r12.2, h012a, r15.1, h015c, h023c, h123c]
                · rcases h035 with ⟨h035a, h035b, h035c, h035d, h035e⟩ | ⟨h035a, h035b, h035c, h035d, h035e⟩
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, r15.1, r23.2, h012c, h015c, h123c]
                      · linarith only [ht, r12.2, h012a, r15.1, h015c, h023c, h123c]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, r15.1, r23.2, h012c, h015c, h123c]
                      · linarith only [ht, r12.2, h012a, r15.1, h015c, h023c, h123c]
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, r15.1, r23.2, h012c, h015c, h123c]
                      · linarith only [ht, r12.2, h012a, r15.1, h015c, h023c, h123c]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, r15.1, r23.2, h012c, h015c, h123c]
                      · linarith only [ht, r12.2, h012a, r15.1, h015c, h023c, h123c]
            · rcases h025 with ⟨h025a, h025b, h025c, h025d, h025e⟩ | ⟨h025a, h025b, h025c, h025d, h025e⟩
              · rcases h034 with ⟨h034a, h034b, h034c, h034d, h034e⟩ | ⟨h034a, h034b, h034c, h034d, h034e⟩
                · rcases h035 with ⟨h035a, h035b, h035c, h035d, h035e⟩ | ⟨h035a, h035b, h035c, h035d, h035e⟩
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, r15.1, r23.2, h012c, h015c, h123c]
                      · linarith only [ht, r12.2, h012a, r15.1, h015c, h023c, h123c]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, r15.1, r23.2, h012c, h015c, h123c]
                      · linarith only [ht, r12.2, h012a, r15.1, h015c, h023c, h123c]
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, r15.1, r23.2, h012c, h015c, h123c]
                      · linarith only [ht, r12.2, h012a, r15.1, h015c, h023c, h123c]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, r15.1, r23.2, h012c, h015c, h123c]
                      · linarith only [ht, r12.2, h012a, r15.1, h015c, h023c, h123c]
                · rcases h035 with ⟨h035a, h035b, h035c, h035d, h035e⟩ | ⟨h035a, h035b, h035c, h035d, h035e⟩
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, r15.1, r23.2, h012c, h015c, h123c]
                      · linarith only [ht, r12.2, h012a, r15.1, h015c, h023c, h123c]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, r15.1, r23.2, h012c, h015c, h123c]
                      · linarith only [ht, r12.2, h012a, r15.1, h015c, h023c, h123c]
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, r15.1, r23.2, h012c, h015c, h123c]
                      · linarith only [ht, r12.2, h012a, r15.1, h015c, h023c, h123c]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, r15.1, r23.2, h012c, h015c, h123c]
                      · linarith only [ht, r12.2, h012a, r15.1, h015c, h023c, h123c]
              · rcases h034 with ⟨h034a, h034b, h034c, h034d, h034e⟩ | ⟨h034a, h034b, h034c, h034d, h034e⟩
                · rcases h035 with ⟨h035a, h035b, h035c, h035d, h035e⟩ | ⟨h035a, h035b, h035c, h035d, h035e⟩
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, r15.1, r23.2, h012c, h015c, h123c]
                      · linarith only [ht, r12.2, h012a, r15.1, h015c, h023c, h123c]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, r15.1, r23.2, h012c, h015c, h123c]
                      · linarith only [ht, r12.2, h012a, r15.1, h015c, h023c, h123c]
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, r15.1, r23.2, h012c, h015c, h123c]
                      · linarith only [ht, r12.2, h012a, r15.1, h015c, h023c, h123c]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, r15.1, r23.2, h012c, h015c, h123c]
                      · linarith only [ht, r12.2, h012a, r15.1, h015c, h023c, h123c]
                · rcases h035 with ⟨h035a, h035b, h035c, h035d, h035e⟩ | ⟨h035a, h035b, h035c, h035d, h035e⟩
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, r15.1, r23.2, h012c, h015c, h123c]
                      · linarith only [ht, r12.2, h012a, r15.1, h015c, h023c, h123c]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, r15.1, r23.2, h012c, h015c, h123c]
                      · linarith only [ht, r12.2, h012a, r15.1, h015c, h023c, h123c]
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, r15.1, r23.2, h012c, h015c, h123c]
                      · linarith only [ht, r12.2, h012a, r15.1, h015c, h023c, h123c]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, r15.1, r23.2, h012c, h015c, h123c]
                      · linarith only [ht, r12.2, h012a, r15.1, h015c, h023c, h123c]
          · rcases h024 with ⟨h024a, h024b, h024c, h024d, h024e⟩ | ⟨h024a, h024b, h024c, h024d, h024e⟩
            · rcases h025 with ⟨h025a, h025b, h025c, h025d, h025e⟩ | ⟨h025a, h025b, h025c, h025d, h025e⟩
              · rcases h034 with ⟨h034a, h034b, h034c, h034d, h034e⟩ | ⟨h034a, h034b, h034c, h034d, h034e⟩
                · rcases h035 with ⟨h035a, h035b, h035c, h035d, h035e⟩ | ⟨h035a, h035b, h035c, h035d, h035e⟩
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, r02.2, r15.1, h013c, h015c, h023c, h123b]
                      · linarith only [ht, h013c, h015b, h023c, h025a, h123e]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h013c, h015b, h023c, h025a, h123b]
                      · linarith only [ht, h013c, h015b, h023c, h025a, h123e]
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h013c, h015b, h023c, h025a, h123b]
                      · linarith only [ht, h013c, h015b, h023c, h025a, h123e]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h013c, h015b, h023c, h025a, h123b]
                      · linarith only [ht, h013c, h015b, h023c, h025a, h123e]
                · rcases h035 with ⟨h035a, h035b, h035c, h035d, h035e⟩ | ⟨h035a, h035b, h035c, h035d, h035e⟩
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h013c, h015b, h023c, h025a, h123b]
                      · linarith only [ht, h013c, h015b, h023c, h025a, h123e]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h013c, h015b, h023c, h025a, h123b]
                      · linarith only [ht, h013c, h015b, h023c, h025a, h123e]
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h013c, h015b, h023c, h025a, h123b]
                      · linarith only [ht, h013c, h015b, h023c, h025a, h123e]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h013c, h015b, h023c, h025a, h123b]
                      · linarith only [ht, h013c, h015b, h023c, h025a, h123e]
              · rcases h034 with ⟨h034a, h034b, h034c, h034d, h034e⟩ | ⟨h034a, h034b, h034c, h034d, h034e⟩
                · rcases h035 with ⟨h035a, h035b, h035c, h035d, h035e⟩ | ⟨h035a, h035b, h035c, h035d, h035e⟩
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, r01.1, r24.2, h013c, h023c, h024c, h123b]
                      · linarith only [ht, h013c, h015b, h023c, h024a, h123e, h045a]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, r02.2, r15.1, h013c, h015c, h023c, h123b]
                      · rcases h124 with ⟨h124a, h124b, h124c, h124d, h124e⟩ | ⟨h124a, h124b, h124c, h124d, h124e⟩
                        · linarith only [ht, r15.1, r24.2, h012c, h015c, h124c]
                        · linarith only [ht, r12.2, r23.1, h023c, h024c, h124c]
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, r02.2, r15.1, h013c, h015c, h023c, h123b]
                      · linarith only [ht, h013c, h015b, h023c, h024a, h045a, h123e]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, r02.2, r15.1, h013c, h015c, h023c, h123b]
                      · rcases h124 with ⟨h124a, h124b, h124c, h124d, h124e⟩ | ⟨h124a, h124b, h124c, h124d, h124e⟩
                        · linarith only [ht, r15.1, r24.2, h012c, h015c, h124c]
                        · linarith only [ht, r12.2, r23.1, h023c, h024c, h124c]
                · rcases h035 with ⟨h035a, h035b, h035c, h035d, h035e⟩ | ⟨h035a, h035b, h035c, h035d, h035e⟩
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, r02.2, r15.1, h013c, h015c, h023c, h123b]
                      · linarith only [ht, h013c, h015b, h023c, h024a, h034b, h035a, h123e]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h013c, h015b, h023c, h024a, h034b, h123b, h035a]
                      · linarith only [ht, h013c, h015b, h023c, h024a, h034b, h035a, h123e]
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, r01.1, r24.2, h013c, h023c, h024c, h123b]
                      · linarith only [ht, h013c, h015b, h023c, h024a, h123e, h045a]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, r01.1, r24.2, h013c, h023c, h024c, h123b]
                      · rcases h124 with ⟨h124a, h124b, h124c, h124d, h124e⟩ | ⟨h124a, h124b, h124c, h124d, h124e⟩
                        · linarith only [ht, r15.1, r24.2, h012c, h015c, h124c]
                        · linarith only [ht, r12.2, r23.1, h023c, h024c, h124c]
            · rcases h025 with ⟨h025a, h025b, h025c, h025d, h025e⟩ | ⟨h025a, h025b, h025c, h025d, h025e⟩
              · rcases h034 with ⟨h034a, h034b, h034c, h034d, h034e⟩ | ⟨h034a, h034b, h034c, h034d, h034e⟩
                · rcases h035 with ⟨h035a, h035b, h035c, h035d, h035e⟩ | ⟨h035a, h035b, h035c, h035d, h035e⟩
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, r02.2, r15.1, h013c, h015c, h023c, h123b]
                      · linarith only [ht, h013c, h015b, h023c, h025a, h123e]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h013c, h015b, h023c, h025a, h123b]
                      · linarith only [ht, h013c, h015b, h023c, h025a, h123e]
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h013c, h015b, h023c, h025a, h123b]
                      · linarith only [ht, h013c, h015b, h023c, h025a, h123e]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h013c, h015b, h023c, h025a, h123b]
                      · linarith only [ht, h013c, h015b, h023c, h025a, h123e]
                · rcases h035 with ⟨h035a, h035b, h035c, h035d, h035e⟩ | ⟨h035a, h035b, h035c, h035d, h035e⟩
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h013c, h015b, h023c, h025a, h123b]
                      · linarith only [ht, h013c, h015b, h023c, h025a, h123e]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h013c, h015b, h023c, h025a, h123b]
                      · linarith only [ht, h013c, h015b, h023c, h025a, h123e]
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h013c, h015b, h023c, h025a, h123b]
                      · linarith only [ht, h013c, h015b, h023c, h025a, h123e]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h013c, h015b, h023c, h025a, h123b]
                      · linarith only [ht, h013c, h015b, h023c, h025a, h123e]
              · rcases h034 with ⟨h034a, h034b, h034c, h034d, h034e⟩ | ⟨h034a, h034b, h034c, h034d, h034e⟩
                · rcases h035 with ⟨h035a, h035b, h035c, h035d, h035e⟩ | ⟨h035a, h035b, h035c, h035d, h035e⟩
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, r02.2, r15.1, h013c, h015c, h023c, h123b]
                      · rcases h124 with ⟨h124a, h124b, h124c, h124d, h124e⟩ | ⟨h124a, h124b, h124c, h124d, h124e⟩
                        · linarith only [ht, r15.1, h012c, r45.2, h015c, h024a, h124a, h124b, h045c]
                        · rcases h125 with ⟨h125a, h125b, h125c, h125d, h125e⟩ | ⟨h125a, h125b, h125c, h125d, h125e⟩
                          · linarith only [h012c, h015c, h125a]
                          · linarith only [ht, h012c, h015c, h125d]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, r02.2, r15.1, h013c, h015c, h023c, h123b]
                      · rcases h124 with ⟨h124a, h124b, h124c, h124d, h124e⟩ | ⟨h124a, h124b, h124c, h124d, h124e⟩
                        · linarith only [h012b, h124b, h124a, h024c]
                        · rcases h125 with ⟨h125a, h125b, h125c, h125d, h125e⟩ | ⟨h125a, h125b, h125c, h125d, h125e⟩
                          · linarith only [ht, h012b, r13.2, r24.1, h013c, h015c, h125a, h024c]
                          · linarith only [ht, h012c, h015c, h125d]
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, r02.2, r15.1, h013c, h015c, h023c, h123b]
                      · rcases h124 with ⟨h124a, h124b, h124c, h124d, h124e⟩ | ⟨h124a, h124b, h124c, h124d, h124e⟩
                        · linarith only [ht, r15.1, h012c, r45.2, h015c, h024a, h045c, h124a, h124b]
                        · rcases h125 with ⟨h125a, h125b, h125c, h125d, h125e⟩ | ⟨h125a, h125b, h125c, h125d, h125e⟩
                          · linarith only [h012c, h015c, h125a]
                          · linarith only [ht, h012c, h015c, h125d]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, r02.2, r15.1, h013c, h015c, h023c, h123b]
                      · rcases h124 with ⟨h124a, h124b, h124c, h124d, h124e⟩ | ⟨h124a, h124b, h124c, h124d, h124e⟩
                        · linarith only [h012b, h124a, h124b, h024c]
                        · rcases h125 with ⟨h125a, h125b, h125c, h125d, h125e⟩ | ⟨h125a, h125b, h125c, h125d, h125e⟩
                          · linarith only [ht, h012b, r13.2, r24.1, h013c, h015c, h125a, h024c]
                          · linarith only [ht, h012c, h015c, h125d]
                · rcases h035 with ⟨h035a, h035b, h035c, h035d, h035e⟩ | ⟨h035a, h035b, h035c, h035d, h035e⟩
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, r02.2, r15.1, h013c, h015c, h023c, h123b]
                      · rcases h124 with ⟨h124a, h124b, h124c, h124d, h124e⟩ | ⟨h124a, h124b, h124c, h124d, h124e⟩
                        · linarith only [h014c, h015b, h024a, h035a, h034b, h124b]
                        · rcases h125 with ⟨h125a, h125b, h125c, h125d, h125e⟩ | ⟨h125a, h125b, h125c, h125d, h125e⟩
                          · linarith only [h012b, h012a, h015c, h125a]
                          · linarith only [ht, h012c, h015c, h125d]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, r02.2, r15.1, h013c, h015c, h023c, h123b]
                      · rcases h124 with ⟨h124a, h124b, h124c, h124d, h124e⟩ | ⟨h124a, h124b, h124c, h124d, h124e⟩
                        · linarith only [h012c, h015b, h024a, h035a, h124a, h034b, h124b]
                        · rcases h125 with ⟨h125a, h125b, h125c, h125d, h125e⟩ | ⟨h125a, h125b, h125c, h125d, h125e⟩
                          · linarith only [h012c, h015c, h125a]
                          · linarith only [ht, h012c, h015c, h125d]
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, r02.2, r15.1, h013c, h015c, h023c, h123b]
                      · rcases h124 with ⟨h124a, h124b, h124c, h124d, h124e⟩ | ⟨h124a, h124b, h124c, h124d, h124e⟩
                        · linarith only [ht, r15.1, h012c, r45.2, h015c, h024a, h045c, h124b, h124a]
                        · rcases h125 with ⟨h125a, h125b, h125c, h125d, h125e⟩ | ⟨h125a, h125b, h125c, h125d, h125e⟩
                          · linarith only [h012c, h015c, h125a]
                          · linarith only [ht, h012c, h015c, h125d]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, r02.2, r15.1, h013c, h015c, h023c, h123b]
                      · rcases h124 with ⟨h124a, h124b, h124c, h124d, h124e⟩ | ⟨h124a, h124b, h124c, h124d, h124e⟩
                        · linarith only [h012b, h124b, h124a, h024c]
                        · rcases h125 with ⟨h125a, h125b, h125c, h125d, h125e⟩ | ⟨h125a, h125b, h125c, h125d, h125e⟩
                          · linarith only [h012c, h015c, h125a]
                          · linarith only [ht, h012c, h015c, h125d]
      · rcases h015 with ⟨h015a, h015b, h015c, h015d, h015e⟩ | ⟨h015a, h015b, h015c, h015d, h015e⟩
        · rcases h023 with ⟨h023a, h023b, h023c, h023d, h023e⟩ | ⟨h023a, h023b, h023c, h023d, h023e⟩
          · rcases h024 with ⟨h024a, h024b, h024c, h024d, h024e⟩ | ⟨h024a, h024b, h024c, h024d, h024e⟩
            · rcases h025 with ⟨h025a, h025b, h025c, h025d, h025e⟩ | ⟨h025a, h025b, h025c, h025d, h025e⟩
              · rcases h034 with ⟨h034a, h034b, h034c, h034d, h034e⟩ | ⟨h034a, h034b, h034c, h034d, h034e⟩
                · rcases h035 with ⟨h035a, h035b, h035c, h035d, h035e⟩ | ⟨h035a, h035b, h035c, h035d, h035e⟩
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, r14.1, r23.2, h012c, h014c, h123c]
                      · linarith only [ht, r12.2, r14.1, h012a, h014c, h023c, h123c]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, r14.1, r23.2, h012c, h014c, h123c]
                      · linarith only [ht, r12.2, r14.1, h012a, h014c, h023c, h123c]
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, r14.1, r23.2, h012c, h014c, h123c]
                      · linarith only [ht, r12.2, r14.1, h012a, h014c, h023c, h123c]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, r14.1, r23.2, h012c, h014c, h123c]
                      · linarith only [ht, r12.2, r14.1, h012a, h014c, h023c, h123c]
                · rcases h035 with ⟨h035a, h035b, h035c, h035d, h035e⟩ | ⟨h035a, h035b, h035c, h035d, h035e⟩
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, r14.1, r23.2, h012c, h014c, h123c]
                      · linarith only [ht, r12.2, r14.1, h012a, h014c, h023c, h123c]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, r14.1, r23.2, h012c, h014c, h123c]
                      · linarith only [ht, r12.2, r14.1, h012a, h014c, h023c, h123c]
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, r14.1, r23.2, h012c, h014c, h123c]
                      · linarith only [ht, r12.2, r14.1, h012a, h014c, h023c, h123c]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, r14.1, r23.2, h012c, h014c, h123c]
                      · linarith only [ht, r12.2, r14.1, h012a, h014c, h023c, h123c]
              · rcases h034 with ⟨h034a, h034b, h034c, h034d, h034e⟩ | ⟨h034a, h034b, h034c, h034d, h034e⟩
                · rcases h035 with ⟨h035a, h035b, h035c, h035d, h035e⟩ | ⟨h035a, h035b, h035c, h035d, h035e⟩
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, r14.1, r23.2, h012c, h014c, h123c]
                      · linarith only [ht, r12.2, r14.1, h012a, h014c, h023c, h123c]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, r14.1, r23.2, h012c, h014c, h123c]
                      · linarith only [ht, r12.2, r14.1, h012a, h014c, h023c, h123c]
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, r14.1, r23.2, h012c, h014c, h123c]
                      · linarith only [ht, r12.2, r14.1, h012a, h014c, h023c, h123c]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, r14.1, r23.2, h012c, h014c, h123c]
                      · linarith only [ht, r12.2, r14.1, h012a, h014c, h023c, h123c]
                · rcases h035 with ⟨h035a, h035b, h035c, h035d, h035e⟩ | ⟨h035a, h035b, h035c, h035d, h035e⟩
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, r14.1, r23.2, h012c, h014c, h123c]
                      · linarith only [ht, r12.2, r14.1, h012a, h014c, h023c, h123c]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, r14.1, r23.2, h012c, h014c, h123c]
                      · linarith only [ht, r12.2, r14.1, h012a, h014c, h023c, h123c]
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, r14.1, r23.2, h012c, h014c, h123c]
                      · linarith only [ht, r12.2, r14.1, h012a, h014c, h023c, h123c]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, r14.1, r23.2, h012c, h014c, h123c]
                      · linarith only [ht, r12.2, r14.1, h012a, h014c, h023c, h123c]
            · rcases h025 with ⟨h025a, h025b, h025c, h025d, h025e⟩ | ⟨h025a, h025b, h025c, h025d, h025e⟩
              · rcases h034 with ⟨h034a, h034b, h034c, h034d, h034e⟩ | ⟨h034a, h034b, h034c, h034d, h034e⟩
                · rcases h035 with ⟨h035a, h035b, h035c, h035d, h035e⟩ | ⟨h035a, h035b, h035c, h035d, h035e⟩
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, r14.1, r23.2, h012c, h014c, h123c]
                      · linarith only [ht, r12.2, r14.1, h012a, h014c, h023c, h123c]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, r14.1, r23.2, h012c, h014c, h123c]
                      · linarith only [ht, r12.2, r14.1, h012a, h014c, h023c, h123c]
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, r14.1, r23.2, h012c, h014c, h123c]
                      · linarith only [ht, r12.2, r14.1, h012a, h014c, h023c, h123c]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, r14.1, r23.2, h012c, h014c, h123c]
                      · linarith only [ht, r12.2, r14.1, h012a, h014c, h023c, h123c]
                · rcases h035 with ⟨h035a, h035b, h035c, h035d, h035e⟩ | ⟨h035a, h035b, h035c, h035d, h035e⟩
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, r14.1, r23.2, h012c, h014c, h123c]
                      · linarith only [ht, r12.2, r14.1, h012a, h014c, h023c, h123c]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, r14.1, r23.2, h012c, h014c, h123c]
                      · linarith only [ht, r12.2, r14.1, h012a, h014c, h023c, h123c]
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, r14.1, r23.2, h012c, h014c, h123c]
                      · linarith only [ht, r12.2, r14.1, h012a, h014c, h023c, h123c]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, r14.1, r23.2, h012c, h014c, h123c]
                      · linarith only [ht, r12.2, r14.1, h012a, h014c, h023c, h123c]
              · rcases h034 with ⟨h034a, h034b, h034c, h034d, h034e⟩ | ⟨h034a, h034b, h034c, h034d, h034e⟩
                · rcases h035 with ⟨h035a, h035b, h035c, h035d, h035e⟩ | ⟨h035a, h035b, h035c, h035d, h035e⟩
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, r14.1, r23.2, h012c, h014c, h123c]
                      · linarith only [ht, r12.2, r14.1, h012a, h014c, h023c, h123c]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, r14.1, r23.2, h012c, h014c, h123c]
                      · linarith only [ht, r12.2, r14.1, h012a, h014c, h023c, h123c]
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, r14.1, r23.2, h012c, h014c, h123c]
                      · linarith only [ht, r12.2, r14.1, h012a, h014c, h023c, h123c]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, r14.1, r23.2, h012c, h014c, h123c]
                      · linarith only [ht, r12.2, r14.1, h012a, h014c, h023c, h123c]
                · rcases h035 with ⟨h035a, h035b, h035c, h035d, h035e⟩ | ⟨h035a, h035b, h035c, h035d, h035e⟩
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, r14.1, r23.2, h012c, h014c, h123c]
                      · linarith only [ht, r12.2, r14.1, h012a, h014c, h023c, h123c]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, r14.1, r23.2, h012c, h014c, h123c]
                      · linarith only [ht, r12.2, r14.1, h012a, h014c, h023c, h123c]
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, r14.1, r23.2, h012c, h014c, h123c]
                      · linarith only [ht, r12.2, r14.1, h012a, h014c, h023c, h123c]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, r14.1, r23.2, h012c, h014c, h123c]
                      · linarith only [ht, r12.2, r14.1, h012a, h014c, h023c, h123c]
          · rcases h024 with ⟨h024a, h024b, h024c, h024d, h024e⟩ | ⟨h024a, h024b, h024c, h024d, h024e⟩
            · rcases h025 with ⟨h025a, h025b, h025c, h025d, h025e⟩ | ⟨h025a, h025b, h025c, h025d, h025e⟩
              · rcases h034 with ⟨h034a, h034b, h034c, h034d, h034e⟩ | ⟨h034a, h034b, h034c, h034d, h034e⟩
                · rcases h035 with ⟨h035a, h035b, h035c, h035d, h035e⟩ | ⟨h035a, h035b, h035c, h035d, h035e⟩
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, r02.2, r14.1, h013c, h014c, h023c, h123b]
                      · linarith only [ht, h013c, h014b, h023c, h123e, h024a]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h013c, h014b, h023c, h024a, h123b]
                      · linarith only [ht, h013c, h014b, h123e, h023c, h024a]
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h013c, h014b, h123b, h023c, h024a]
                      · linarith only [ht, h013c, h014b, h023c, h024a, h123e]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h013c, h014b, h023c, h123b, h024a]
                      · linarith only [ht, h013c, h014b, h023c, h123e, h024a]
                · rcases h035 with ⟨h035a, h035b, h035c, h035d, h035e⟩ | ⟨h035a, h035b, h035c, h035d, h035e⟩
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h013c, h014b, h023c, h024a, h123b]
                      · linarith only [ht, h013c, h014b, h023c, h123e, h024a]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h013c, h014b, h023c, h123b, h024a]
                      · linarith only [ht, h013c, h014b, h123e, h023c, h024a]
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h013c, h014b, h023c, h123b, h024a]
                      · linarith only [ht, h013c, h014b, h023c, h024a, h123e]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h013c, h014b, h023c, h123b, h024a]
                      · linarith only [ht, h013c, h014b, h023c, h123e, h024a]
              · rcases h034 with ⟨h034a, h034b, h034c, h034d, h034e⟩ | ⟨h034a, h034b, h034c, h034d, h034e⟩
                · rcases h035 with ⟨h035a, h035b, h035c, h035d, h035e⟩ | ⟨h035a, h035b, h035c, h035d, h035e⟩
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h013c, h014b, h023c, h123b, h024a]
                      · linarith only [ht, h013c, h014b, h023c, h123e, h024a]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h013c, h014b, h123b, h023c, h024a]
                      · linarith only [ht, h013c, h014b, h123e, h023c, h024a]
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h013c, h014b, h023c, h123b, h024a]
                      · linarith only [ht, h013c, h014b, h023c, h024a, h123e]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h013c, h014b, h023c, h024a, h123b]
                      · linarith only [ht, h013c, h014b, h023c, h123e, h024a]
                · rcases h035 with ⟨h035a, h035b, h035c, h035d, h035e⟩ | ⟨h035a, h035b, h035c, h035d, h035e⟩
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h013c, h014b, h023c, h123b, h024a]
                      · linarith only [ht, h013c, h014b, h023c, h123e, h024a]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h013c, h014b, h023c, h024a, h123b]
                      · linarith only [ht, h013c, h014b, h123e, h023c, h024a]
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h013c, h014b, h023c, h024a, h123b]
                      · linarith only [ht, h013c, h014b, h023c, h024a, h123e]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h013c, h014b, h023c, h123b, h024a]
                      · linarith only [ht, h013c, h014b, h023c, h123e, h024a]
            · rcases h025 with ⟨h025a, h025b, h025c, h025d, h025e⟩ | ⟨h025a, h025b, h025c, h025d, h025e⟩
              · rcases h034 with ⟨h034a, h034b, h034c, h034d, h034e⟩ | ⟨h034a, h034b, h034c, h034d, h034e⟩
                · rcases h035 with ⟨h035a, h035b, h035c, h035d, h035e⟩ | ⟨h035a, h035b, h035c, h035d, h035e⟩
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, r02.2, r14.1, h013c, h014c, h023c, h123b]
                      · rcases h124 with ⟨h124a, h124b, h124c, h124d, h124e⟩ | ⟨h124a, h124b, h124c, h124d, h124e⟩
                        · linarith only [ht, h012b, r13.2, r23.1, h013c, h014c, h124a, h023c]
                        · linarith only [ht, h012c, h014c, h124d]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h013c, h014b, h023c, h123b, h025a, h045b]
                      · linarith only [ht, h013c, h014b, h023c, h025a, h045b, h123e]
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, r02.2, r14.1, h013c, h014c, h023c, h123b]
                      · linarith only [ht, h013c, h014b, h034a, h023c, h025a, h035b, h123e]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h013c, h014b, h034a, h023c, h123b, h025a, h035b]
                      · linarith only [ht, h013c, h014b, h034a, h023c, h025a, h035b, h123e]
                · rcases h035 with ⟨h035a, h035b, h035c, h035d, h035e⟩ | ⟨h035a, h035b, h035c, h035d, h035e⟩
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, r01.1, r25.2, h013c, h025c, h023c, h123b]
                      · rcases h124 with ⟨h124a, h124b, h124c, h124d, h124e⟩ | ⟨h124a, h124b, h124c, h124d, h124e⟩
                        · linarith only [h012c, h014c, h124a]
                        · linarith only [ht, h012c, h014c, h124d]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h013c, h014b, h045b, h123b, h023c, h025a]
                      · linarith only [ht, h013c, h014b, h045b, h023c, h025a, h123e]
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, r01.1, r25.2, h013c, h025c, h023c, h123b]
                      · rcases h124 with ⟨h124a, h124b, h124c, h124d, h124e⟩ | ⟨h124a, h124b, h124c, h124d, h124e⟩
                        · linarith only [h012c, h014c, h124a]
                        · linarith only [ht, h012c, h014c, h124d]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h013c, h014b, h023c, h045b, h025a, h123b]
                      · linarith only [ht, h013c, h014b, h123e, h023c, h045b, h025a]
              · rcases h034 with ⟨h034a, h034b, h034c, h034d, h034e⟩ | ⟨h034a, h034b, h034c, h034d, h034e⟩
                · rcases h035 with ⟨h035a, h035b, h035c, h035d, h035e⟩ | ⟨h035a, h035b, h035c, h035d, h035e⟩
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, h012d, h013c, h023c, h123b]
                      · rcases h124 with ⟨h124a, h124b, h124c, h124d, h124e⟩ | ⟨h124a, h124b, h124c, h124d, h124e⟩
                        · linarith only [h012b, h012a, h014c, h124a]
                        · linarith only [ht, h012c, h014c, h124d]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, r02.2, r14.1, h013c, h014c, h023c, h123b]
                      · rcases h124 with ⟨h124a, h124b, h124c, h124d, h124e⟩ | ⟨h124a, h124b, h124c, h124d, h124e⟩
                        · linarith only [h012b, h012a, h014c, h124a]
                        · linarith only [ht, h012c, h014c, h124d]
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, r02.2, r14.1, h013c, h014c, h123b, h023c]
                      · rcases h124 with ⟨h124a, h124b, h124c, h124d, h124e⟩ | ⟨h124a, h124b, h124c, h124d, h124e⟩
                        · linarith only [h012b, h012a, h014c, h124a]
                        · linarith only [ht, h012c, h014c, h124d]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, r02.2, r14.1, h013c, h014c, h023c, h123b]
                      · rcases h124 with ⟨h124a, h124b, h124c, h124d, h124e⟩ | ⟨h124a, h124b, h124c, h124d, h124e⟩
                        · linarith only [h012b, h012a, h014c, h124a]
                        · linarith only [ht, h012c, h014c, h124d]
                · rcases h035 with ⟨h035a, h035b, h035c, h035d, h035e⟩ | ⟨h035a, h035b, h035c, h035d, h035e⟩
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, r02.2, r14.1, h013c, h014c, h023c, h123b]
                      · rcases h124 with ⟨h124a, h124b, h124c, h124d, h124e⟩ | ⟨h124a, h124b, h124c, h124d, h124e⟩
                        · linarith only [h012b, h012a, h014c, h124a]
                        · linarith only [ht, h012c, h014c, h124d]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, r02.2, r14.1, h013c, h014c, h023c, h123b]
                      · rcases h124 with ⟨h124a, h124b, h124c, h124d, h124e⟩ | ⟨h124a, h124b, h124c, h124d, h124e⟩
                        · linarith only [h012b, h012a, h014c, h124a]
                        · linarith only [ht, h012c, h014c, h124d]
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, r02.2, r14.1, h013c, h014c, h023c, h123b]
                      · rcases h124 with ⟨h124a, h124b, h124c, h124d, h124e⟩ | ⟨h124a, h124b, h124c, h124d, h124e⟩
                        · linarith only [h012b, h012a, h014c, h124a]
                        · linarith only [ht, h012c, h014c, h124d]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, r02.2, r14.1, h013c, h014c, h023c, h123b]
                      · rcases h124 with ⟨h124a, h124b, h124c, h124d, h124e⟩ | ⟨h124a, h124b, h124c, h124d, h124e⟩
                        · linarith only [h012b, h012a, h014c, h124a]
                        · linarith only [ht, h012c, h014c, h124d]
        · rcases h023 with ⟨h023a, h023b, h023c, h023d, h023e⟩ | ⟨h023a, h023b, h023c, h023d, h023e⟩
          · rcases h024 with ⟨h024a, h024b, h024c, h024d, h024e⟩ | ⟨h024a, h024b, h024c, h024d, h024e⟩
            · rcases h025 with ⟨h025a, h025b, h025c, h025d, h025e⟩ | ⟨h025a, h025b, h025c, h025d, h025e⟩
              · rcases h034 with ⟨h034a, h034b, h034c, h034d, h034e⟩ | ⟨h034a, h034b, h034c, h034d, h034e⟩
                · rcases h035 with ⟨h035a, h035b, h035c, h035d, h035e⟩ | ⟨h035a, h035b, h035c, h035d, h035e⟩
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, r14.1, r23.2, h012c, h014c, h123c]
                      · linarith only [ht, r12.2, r14.1, h012a, h014c, h023c, h123c]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, r14.1, r23.2, h012c, h014c, h123c]
                      · linarith only [ht, r12.2, r14.1, h012a, h014c, h023c, h123c]
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, r14.1, r23.2, h012c, h014c, h123c]
                      · linarith only [ht, r12.2, r14.1, h012a, h014c, h023c, h123c]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, r14.1, r23.2, h012c, h014c, h123c]
                      · linarith only [ht, r12.2, r14.1, h012a, h014c, h023c, h123c]
                · rcases h035 with ⟨h035a, h035b, h035c, h035d, h035e⟩ | ⟨h035a, h035b, h035c, h035d, h035e⟩
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, r14.1, r23.2, h012c, h014c, h123c]
                      · linarith only [ht, r12.2, r14.1, h012a, h014c, h023c, h123c]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, r14.1, r23.2, h012c, h014c, h123c]
                      · linarith only [ht, r12.2, r14.1, h012a, h014c, h023c, h123c]
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, r14.1, r23.2, h012c, h014c, h123c]
                      · linarith only [ht, r12.2, r14.1, h012a, h014c, h023c, h123c]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, r14.1, r23.2, h012c, h014c, h123c]
                      · linarith only [ht, r12.2, r14.1, h012a, h014c, h023c, h123c]
              · rcases h034 with ⟨h034a, h034b, h034c, h034d, h034e⟩ | ⟨h034a, h034b, h034c, h034d, h034e⟩
                · rcases h035 with ⟨h035a, h035b, h035c, h035d, h035e⟩ | ⟨h035a, h035b, h035c, h035d, h035e⟩
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, r14.1, r23.2, h012c, h014c, h123c]
                      · linarith only [ht, r12.2, r14.1, h012a, h014c, h023c, h123c]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, r14.1, r23.2, h012c, h014c, h123c]
                      · linarith only [ht, r12.2, r14.1, h012a, h014c, h023c, h123c]
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, r14.1, r23.2, h012c, h014c, h123c]
                      · linarith only [ht, r12.2, r14.1, h012a, h014c, h023c, h123c]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, r14.1, r23.2, h012c, h014c, h123c]
                      · linarith only [ht, r12.2, r14.1, h012a, h014c, h023c, h123c]
                · rcases h035 with ⟨h035a, h035b, h035c, h035d, h035e⟩ | ⟨h035a, h035b, h035c, h035d, h035e⟩
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, r14.1, r23.2, h012c, h014c, h123c]
                      · linarith only [ht, r12.2, r14.1, h012a, h014c, h023c, h123c]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, r14.1, r23.2, h012c, h014c, h123c]
                      · linarith only [ht, r12.2, r14.1, h012a, h014c, h023c, h123c]
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, r14.1, r23.2, h012c, h014c, h123c]
                      · linarith only [ht, r12.2, r14.1, h012a, h014c, h023c, h123c]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, r14.1, r23.2, h012c, h014c, h123c]
                      · linarith only [ht, r12.2, r14.1, h012a, h014c, h023c, h123c]
            · rcases h025 with ⟨h025a, h025b, h025c, h025d, h025e⟩ | ⟨h025a, h025b, h025c, h025d, h025e⟩
              · rcases h034 with ⟨h034a, h034b, h034c, h034d, h034e⟩ | ⟨h034a, h034b, h034c, h034d, h034e⟩
                · rcases h035 with ⟨h035a, h035b, h035c, h035d, h035e⟩ | ⟨h035a, h035b, h035c, h035d, h035e⟩
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, r14.1, r23.2, h012c, h014c, h123c]
                      · linarith only [ht, r12.2, r14.1, h012a, h014c, h023c, h123c]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, r14.1, r23.2, h012c, h014c, h123c]
                      · linarith only [ht, r12.2, r14.1, h012a, h014c, h023c, h123c]
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, r14.1, r23.2, h012c, h014c, h123c]
                      · linarith only [ht, r12.2, r14.1, h012a, h014c, h023c, h123c]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, r14.1, r23.2, h012c, h014c, h123c]
                      · linarith only [ht, r12.2, r14.1, h012a, h014c, h023c, h123c]
                · rcases h035 with ⟨h035a, h035b, h035c, h035d, h035e⟩ | ⟨h035a, h035b, h035c, h035d, h035e⟩
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, r14.1, r23.2, h012c, h014c, h123c]
                      · linarith only [ht, r12.2, r14.1, h012a, h014c, h023c, h123c]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, r14.1, r23.2, h012c, h014c, h123c]
                      · linarith only [ht, r12.2, r14.1, h012a, h014c, h023c, h123c]
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, r14.1, r23.2, h012c, h014c, h123c]
                      · linarith only [ht, r12.2, r14.1, h012a, h014c, h023c, h123c]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, r14.1, r23.2, h012c, h014c, h123c]
                      · linarith only [ht, r12.2, r14.1, h012a, h014c, h023c, h123c]
              · rcases h034 with ⟨h034a, h034b, h034c, h034d, h034e⟩ | ⟨h034a, h034b, h034c, h034d, h034e⟩
                · rcases h035 with ⟨h035a, h035b, h035c, h035d, h035e⟩ | ⟨h035a, h035b, h035c, h035d, h035e⟩
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, r14.1, r23.2, h012c, h014c, h123c]
                      · linarith only [ht, r12.2, r14.1, h012a, h014c, h023c, h123c]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, r14.1, r23.2, h012c, h014c, h123c]
                      · linarith only [ht, r12.2, r14.1, h012a, h014c, h023c, h123c]
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, r14.1, r23.2, h012c, h014c, h123c]
                      · linarith only [ht, r12.2, r14.1, h012a, h014c, h023c, h123c]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, r14.1, r23.2, h012c, h014c, h123c]
                      · linarith only [ht, r12.2, r14.1, h012a, h014c, h023c, h123c]
                · rcases h035 with ⟨h035a, h035b, h035c, h035d, h035e⟩ | ⟨h035a, h035b, h035c, h035d, h035e⟩
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, r14.1, r23.2, h012c, h014c, h123c]
                      · linarith only [ht, r12.2, r14.1, h012a, h014c, h023c, h123c]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, r14.1, r23.2, h012c, h014c, h123c]
                      · linarith only [ht, r12.2, r14.1, h012a, h014c, h023c, h123c]
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, r14.1, r23.2, h012c, h014c, h123c]
                      · linarith only [ht, r12.2, r14.1, h012a, h014c, h023c, h123c]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, r14.1, r23.2, h012c, h014c, h123c]
                      · linarith only [ht, r12.2, r14.1, h012a, h014c, h023c, h123c]
          · rcases h024 with ⟨h024a, h024b, h024c, h024d, h024e⟩ | ⟨h024a, h024b, h024c, h024d, h024e⟩
            · rcases h025 with ⟨h025a, h025b, h025c, h025d, h025e⟩ | ⟨h025a, h025b, h025c, h025d, h025e⟩
              · rcases h034 with ⟨h034a, h034b, h034c, h034d, h034e⟩ | ⟨h034a, h034b, h034c, h034d, h034e⟩
                · rcases h035 with ⟨h035a, h035b, h035c, h035d, h035e⟩ | ⟨h035a, h035b, h035c, h035d, h035e⟩
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, r02.2, r14.1, h013c, h014c, h023c, h123b]
                      · linarith only [ht, h013c, h014b, h023c, h024a, h123e]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h013c, h014b, h023c, h024a, h123b]
                      · linarith only [ht, h013c, h014b, h023c, h024a, h123e]
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h013c, h014b, h023c, h024a, h123b]
                      · linarith only [ht, h013c, h014b, h023c, h024a, h123e]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h013c, h014b, h023c, h024a, h123b]
                      · linarith only [ht, h013c, h014b, h023c, h024a, h123e]
                · rcases h035 with ⟨h035a, h035b, h035c, h035d, h035e⟩ | ⟨h035a, h035b, h035c, h035d, h035e⟩
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h013c, h014b, h023c, h024a, h123b]
                      · linarith only [ht, h013c, h014b, h023c, h024a, h123e]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h013c, h014b, h023c, h024a, h123b]
                      · linarith only [ht, h013c, h014b, h023c, h024a, h123e]
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h013c, h014b, h023c, h024a, h123b]
                      · linarith only [ht, h013c, h014b, h023c, h024a, h123e]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h013c, h014b, h023c, h024a, h123b]
                      · linarith only [ht, h013c, h014b, h023c, h024a, h123e]
              · rcases h034 with ⟨h034a, h034b, h034c, h034d, h034e⟩ | ⟨h034a, h034b, h034c, h034d, h034e⟩
                · rcases h035 with ⟨h035a, h035b, h035c, h035d, h035e⟩ | ⟨h035a, h035b, h035c, h035d, h035e⟩
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h013c, h014b, h023c, h024a, h123b]
                      · linarith only [ht, h013c, h014b, h023c, h024a, h123e]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h013c, h014b, h023c, h024a, h123b]
                      · linarith only [ht, h013c, h014b, h023c, h024a, h123e]
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h013c, h014b, h023c, h024a, h123b]
                      · linarith only [ht, h013c, h014b, h023c, h024a, h123e]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h013c, h014b, h023c, h024a, h123b]
                      · linarith only [ht, h013c, h014b, h023c, h024a, h123e]
                · rcases h035 with ⟨h035a, h035b, h035c, h035d, h035e⟩ | ⟨h035a, h035b, h035c, h035d, h035e⟩
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h013c, h014b, h023c, h024a, h123b]
                      · linarith only [ht, h013c, h014b, h023c, h024a, h123e]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h013c, h014b, h023c, h024a, h123b]
                      · linarith only [ht, h013c, h014b, h023c, h024a, h123e]
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h013c, h014b, h023c, h024a, h123b]
                      · linarith only [ht, h013c, h014b, h023c, h024a, h123e]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h013c, h014b, h023c, h024a, h123b]
                      · linarith only [ht, h013c, h014b, h023c, h024a, h123e]
            · rcases h025 with ⟨h025a, h025b, h025c, h025d, h025e⟩ | ⟨h025a, h025b, h025c, h025d, h025e⟩
              · rcases h034 with ⟨h034a, h034b, h034c, h034d, h034e⟩ | ⟨h034a, h034b, h034c, h034d, h034e⟩
                · rcases h035 with ⟨h035a, h035b, h035c, h035d, h035e⟩ | ⟨h035a, h035b, h035c, h035d, h035e⟩
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, r02.2, r14.1, h013c, h014c, h023c, h123b]
                      · linarith only [ht, h013c, h015b, h023c, h123e, h025a]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h013c, h015b, h023c, h123b, h025a]
                      · linarith only [ht, h013c, h015b, h023c, h123e, h025a]
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h013c, h015b, h023c, h123b, h025a]
                      · linarith only [ht, h013c, h015b, h023c, h123e, h025a]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h013c, h015b, h023c, h123b, h025a]
                      · linarith only [ht, h013c, h015b, h023c, h123e, h025a]
                · rcases h035 with ⟨h035a, h035b, h035c, h035d, h035e⟩ | ⟨h035a, h035b, h035c, h035d, h035e⟩
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h013c, h015b, h023c, h025a, h123b]
                      · linarith only [ht, h013c, h015b, h023c, h123e, h025a]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h013c, h015b, h023c, h123b, h025a]
                      · linarith only [ht, h013c, h015b, h023c, h123e, h025a]
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h013c, h015b, h023c, h123b, h025a]
                      · linarith only [ht, h013c, h015b, h023c, h123e, h025a]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h013c, h015b, h023c, h123b, h025a]
                      · linarith only [ht, h013c, h015b, h023c, h123e, h025a]
              · rcases h034 with ⟨h034a, h034b, h034c, h034d, h034e⟩ | ⟨h034a, h034b, h034c, h034d, h034e⟩
                · rcases h035 with ⟨h035a, h035b, h035c, h035d, h035e⟩ | ⟨h035a, h035b, h035c, h035d, h035e⟩
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, r02.2, r14.1, h013c, h014c, h023c, h123b]
                      · rcases h124 with ⟨h124a, h124b, h124c, h124d, h124e⟩ | ⟨h124a, h124b, h124c, h124d, h124e⟩
                        · linarith only [h012b, h012a, h014c, h124a]
                        · linarith only [ht, h012c, h014c, h124d]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, r02.2, r14.1, h013c, h014c, h023c, h123b]
                      · rcases h124 with ⟨h124a, h124b, h124c, h124d, h124e⟩ | ⟨h124a, h124b, h124c, h124d, h124e⟩
                        · linarith only [h012b, h012a, h014c, h124a]
                        · linarith only [ht, h012c, h014c, h124d]
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, r02.2, r14.1, h013c, h014c, h023c, h123b]
                      · rcases h124 with ⟨h124a, h124b, h124c, h124d, h124e⟩ | ⟨h124a, h124b, h124c, h124d, h124e⟩
                        · linarith only [h012b, h012a, h014c, h124a]
                        · linarith only [ht, h012c, h014c, h124d]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, r02.2, r14.1, h013c, h014c, h023c, h123b]
                      · rcases h124 with ⟨h124a, h124b, h124c, h124d, h124e⟩ | ⟨h124a, h124b, h124c, h124d, h124e⟩
                        · linarith only [h012b, h012a, h014c, h124a]
                        · linarith only [ht, h012c, h014c, h124d]
                · rcases h035 with ⟨h035a, h035b, h035c, h035d, h035e⟩ | ⟨h035a, h035b, h035c, h035d, h035e⟩
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, r02.2, r14.1, h013c, h014c, h023c, h123b]
                      · rcases h124 with ⟨h124a, h124b, h124c, h124d, h124e⟩ | ⟨h124a, h124b, h124c, h124d, h124e⟩
                        · linarith only [h012b, h012a, h014c, h124a]
                        · linarith only [ht, h012c, h014c, h124d]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, r02.2, r14.1, h013c, h014c, h023c, h123b]
                      · rcases h124 with ⟨h124a, h124b, h124c, h124d, h124e⟩ | ⟨h124a, h124b, h124c, h124d, h124e⟩
                        · linarith only [h012b, h012a, h014c, h124a]
                        · linarith only [ht, h012c, h014c, h124d]
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, r02.2, r14.1, h013c, h014c, h023c, h123b]
                      · rcases h124 with ⟨h124a, h124b, h124c, h124d, h124e⟩ | ⟨h124a, h124b, h124c, h124d, h124e⟩
                        · linarith only [h012b, h012a, h014c, h124a]
                        · linarith only [ht, h012c, h014c, h124d]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, r02.2, r14.1, h013c, h014c, h023c, h123b]
                      · rcases h124 with ⟨h124a, h124b, h124c, h124d, h124e⟩ | ⟨h124a, h124b, h124c, h124d, h124e⟩
                        · linarith only [h012b, h012a, h014c, h124a]
                        · linarith only [ht, h012c, h014c, h124d]
    · rcases h014 with ⟨h014a, h014b, h014c, h014d, h014e⟩ | ⟨h014a, h014b, h014c, h014d, h014e⟩
      · rcases h015 with ⟨h015a, h015b, h015c, h015d, h015e⟩ | ⟨h015a, h015b, h015c, h015d, h015e⟩
        · rcases h023 with ⟨h023a, h023b, h023c, h023d, h023e⟩ | ⟨h023a, h023b, h023c, h023d, h023e⟩
          · rcases h024 with ⟨h024a, h024b, h024c, h024d, h024e⟩ | ⟨h024a, h024b, h024c, h024d, h024e⟩
            · rcases h025 with ⟨h025a, h025b, h025c, h025d, h025e⟩ | ⟨h025a, h025b, h025c, h025d, h025e⟩
              · rcases h034 with ⟨h034a, h034b, h034c, h034d, h034e⟩ | ⟨h034a, h034b, h034c, h034d, h034e⟩
                · rcases h035 with ⟨h035a, h035b, h035c, h035d, h035e⟩ | ⟨h035a, h035b, h035c, h035d, h035e⟩
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012c, h013c, h123a]
                      · linarith only [ht, r02.1, r12.2, h012c, h013c, h023c, h123a]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012b, h012a, h013c, h123a]
                      · linarith only [h012a, h013c, h023c, h123a]
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012c, h013c, h123a]
                      · linarith only [h012a, h013c, h023c, h123a]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012c, h013c, h123a]
                      · linarith only [h012a, h013c, h023c, h123a]
                · rcases h035 with ⟨h035a, h035b, h035c, h035d, h035e⟩ | ⟨h035a, h035b, h035c, h035d, h035e⟩
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012c, h013c, h123a]
                      · linarith only [h012a, h013c, h123a, h023c]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012c, h013c, h123a]
                      · linarith only [h012a, h013c, h023c, h123a]
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012c, h013c, h123a]
                      · linarith only [h012a, h013c, h023c, h123a]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012c, h013c, h123a]
                      · linarith only [h012a, h013c, h023c, h123a]
              · rcases h034 with ⟨h034a, h034b, h034c, h034d, h034e⟩ | ⟨h034a, h034b, h034c, h034d, h034e⟩
                · rcases h035 with ⟨h035a, h035b, h035c, h035d, h035e⟩ | ⟨h035a, h035b, h035c, h035d, h035e⟩
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012c, h013c, h123a]
                      · linarith only [h012a, h013c, h023c, h123a]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012c, h013c, h123a]
                      · linarith only [h012a, h013c, h023c, h123a]
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012c, h013c, h123a]
                      · linarith only [h012a, h013c, h023c, h123a]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012c, h013c, h123a]
                      · linarith only [h012a, h013c, h023c, h123a]
                · rcases h035 with ⟨h035a, h035b, h035c, h035d, h035e⟩ | ⟨h035a, h035b, h035c, h035d, h035e⟩
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012c, h013c, h123a]
                      · linarith only [h012a, h013c, h023c, h123a]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012c, h013c, h123a]
                      · linarith only [h012a, h013c, h023c, h123a]
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012c, h013c, h123a]
                      · linarith only [h012a, h013c, h023c, h123a]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012c, h013c, h123a]
                      · linarith only [h012a, h013c, h023c, h123a]
            · rcases h025 with ⟨h025a, h025b, h025c, h025d, h025e⟩ | ⟨h025a, h025b, h025c, h025d, h025e⟩
              · rcases h034 with ⟨h034a, h034b, h034c, h034d, h034e⟩ | ⟨h034a, h034b, h034c, h034d, h034e⟩
                · rcases h035 with ⟨h035a, h035b, h035c, h035d, h035e⟩ | ⟨h035a, h035b, h035c, h035d, h035e⟩
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012c, h013c, h123a]
                      · linarith only [h012a, h013c, h023c, h123a]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012c, h013c, h123a]
                      · linarith only [h012a, h013c, h023c, h123a]
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012c, h013c, h123a]
                      · linarith only [h012a, h013c, h023c, h123a]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012c, h013c, h123a]
                      · linarith only [h012a, h013c, h023c, h123a]
                · rcases h035 with ⟨h035a, h035b, h035c, h035d, h035e⟩ | ⟨h035a, h035b, h035c, h035d, h035e⟩
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012c, h013c, h123a]
                      · linarith only [h012a, h013c, h023c, h123a]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012c, h013c, h123a]
                      · linarith only [h012a, h013c, h023c, h123a]
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012c, h013c, h123a]
                      · linarith only [h012a, h013c, h023c, h123a]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012c, h013c, h123a]
                      · linarith only [h012a, h013c, h023c, h123a]
              · rcases h034 with ⟨h034a, h034b, h034c, h034d, h034e⟩ | ⟨h034a, h034b, h034c, h034d, h034e⟩
                · rcases h035 with ⟨h035a, h035b, h035c, h035d, h035e⟩ | ⟨h035a, h035b, h035c, h035d, h035e⟩
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012c, h013c, h123a]
                      · linarith only [h012a, h013c, h023c, h123a]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012c, h013c, h123a]
                      · linarith only [h012a, h013c, h023c, h123a]
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012c, h013c, h123a]
                      · linarith only [h012a, h013c, h023c, h123a]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012c, h013c, h123a]
                      · linarith only [h012a, h013c, h023c, h123a]
                · rcases h035 with ⟨h035a, h035b, h035c, h035d, h035e⟩ | ⟨h035a, h035b, h035c, h035d, h035e⟩
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012c, h013c, h123a]
                      · linarith only [h012a, h013c, h023c, h123a]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012c, h013c, h123a]
                      · linarith only [h012a, h013c, h023c, h123a]
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012c, h013c, h123a]
                      · linarith only [h012a, h013c, h023c, h123a]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012c, h013c, h123a]
                      · linarith only [h012a, h013c, h023c, h123a]
          · rcases h024 with ⟨h024a, h024b, h024c, h024d, h024e⟩ | ⟨h024a, h024b, h024c, h024d, h024e⟩
            · rcases h025 with ⟨h025a, h025b, h025c, h025d, h025e⟩ | ⟨h025a, h025b, h025c, h025d, h025e⟩
              · rcases h034 with ⟨h034a, h034b, h034c, h034d, h034e⟩ | ⟨h034a, h034b, h034c, h034d, h034e⟩
                · rcases h035 with ⟨h035a, h035b, h035c, h035d, h035e⟩ | ⟨h035a, h035b, h035c, h035d, h035e⟩
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012c, h013c, h123a]
                      · linarith only [ht, h012c, h013c, h123d]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012c, h013c, h123a]
                      · linarith only [ht, h012c, h013c, h123d]
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012c, h013c, h123a]
                      · linarith only [ht, h012c, h013c, h123d]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012c, h013c, h123a]
                      · linarith only [ht, h012c, h013c, h123d]
                · rcases h035 with ⟨h035a, h035b, h035c, h035d, h035e⟩ | ⟨h035a, h035b, h035c, h035d, h035e⟩
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012c, h013c, h123a]
                      · linarith only [ht, h012c, h013c, h123d]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012c, h013c, h123a]
                      · linarith only [ht, h012c, h013c, h123d]
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012c, h013c, h123a]
                      · linarith only [ht, h012c, h013c, h123d]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012c, h013c, h123a]
                      · linarith only [ht, h012c, h013c, h123d]
              · rcases h034 with ⟨h034a, h034b, h034c, h034d, h034e⟩ | ⟨h034a, h034b, h034c, h034d, h034e⟩
                · rcases h035 with ⟨h035a, h035b, h035c, h035d, h035e⟩ | ⟨h035a, h035b, h035c, h035d, h035e⟩
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012c, h013c, h123a]
                      · linarith only [ht, h012c, h013c, h123d]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012c, h013c, h123a]
                      · linarith only [ht, h012c, h013c, h123d]
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012c, h013c, h123a]
                      · linarith only [ht, h012c, h013c, h123d]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012c, h013c, h123a]
                      · linarith only [ht, h012c, h013c, h123d]
                · rcases h035 with ⟨h035a, h035b, h035c, h035d, h035e⟩ | ⟨h035a, h035b, h035c, h035d, h035e⟩
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012c, h013c, h123a]
                      · linarith only [ht, h012c, h013c, h123d]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012c, h013c, h123a]
                      · linarith only [ht, h012c, h013c, h123d]
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012c, h013c, h123a]
                      · linarith only [ht, h012c, h013c, h123d]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012c, h013c, h123a]
                      · linarith only [ht, h012c, h013c, h123d]
            · rcases h025 with ⟨h025a, h025b, h025c, h025d, h025e⟩ | ⟨h025a, h025b, h025c, h025d, h025e⟩
              · rcases h034 with ⟨h034a, h034b, h034c, h034d, h034e⟩ | ⟨h034a, h034b, h034c, h034d, h034e⟩
                · rcases h035 with ⟨h035a, h035b, h035c, h035d, h035e⟩ | ⟨h035a, h035b, h035c, h035d, h035e⟩
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012c, h013c, h123a]
                      · linarith only [ht, h012c, h013c, h123d]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012c, h013c, h123a]
                      · linarith only [ht, h012c, h013c, h123d]
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012c, h013c, h123a]
                      · linarith only [ht, h012c, h013c, h123d]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012c, h013c, h123a]
                      · linarith only [ht, h012c, h013c, h123d]
                · rcases h035 with ⟨h035a, h035b, h035c, h035d, h035e⟩ | ⟨h035a, h035b, h035c, h035d, h035e⟩
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012c, h013c, h123a]
                      · linarith only [ht, h012c, h013c, h123d]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012c, h013c, h123a]
                      · linarith only [ht, h012c, h013c, h123d]
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012c, h013c, h123a]
                      · linarith only [ht, h012c, h013c, h123d]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012c, h013c, h123a]
                      · linarith only [ht, h012c, h013c, h123d]
              · rcases h034 with ⟨h034a, h034b, h034c, h034d, h034e⟩ | ⟨h034a, h034b, h034c, h034d, h034e⟩
                · rcases h035 with ⟨h035a, h035b, h035c, h035d, h035e⟩ | ⟨h035a, h035b, h035c, h035d, h035e⟩
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012c, h013c, h123a]
                      · linarith only [ht, h012c, h013c, h123d]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012c, h013c, h123a]
                      · linarith only [ht, h012c, h013c, h123d]
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012c, h013c, h123a]
                      · linarith only [ht, h012c, h013c, h123d]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012c, h013c, h123a]
                      · linarith only [ht, h012c, h013c, h123d]
                · rcases h035 with ⟨h035a, h035b, h035c, h035d, h035e⟩ | ⟨h035a, h035b, h035c, h035d, h035e⟩
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012c, h013c, h123a]
                      · linarith only [ht, h012c, h013c, h123d]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012c, h013c, h123a]
                      · linarith only [ht, h012c, h013c, h123d]
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012c, h013c, h123a]
                      · linarith only [ht, h012c, h013c, h123d]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012c, h013c, h123a]
                      · linarith only [ht, h012c, h013c, h123d]
        · rcases h023 with ⟨h023a, h023b, h023c, h023d, h023e⟩ | ⟨h023a, h023b, h023c, h023d, h023e⟩
          · rcases h024 with ⟨h024a, h024b, h024c, h024d, h024e⟩ | ⟨h024a, h024b, h024c, h024d, h024e⟩
            · rcases h025 with ⟨h025a, h025b, h025c, h025d, h025e⟩ | ⟨h025a, h025b, h025c, h025d, h025e⟩
              · rcases h034 with ⟨h034a, h034b, h034c, h034d, h034e⟩ | ⟨h034a, h034b, h034c, h034d, h034e⟩
                · rcases h035 with ⟨h035a, h035b, h035c, h035d, h035e⟩ | ⟨h035a, h035b, h035c, h035d, h035e⟩
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012c, h013c, h123a]
                      · linarith only [h012a, h013c, h123a, h023c]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012c, h013c, h123a]
                      · linarith only [h012a, h013c, h023c, h123a]
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012c, h013c, h123a]
                      · linarith only [h012a, h013c, h123a, h023c]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012c, h013c, h123a]
                      · linarith only [h012a, h013c, h123a, h023c]
                · rcases h035 with ⟨h035a, h035b, h035c, h035d, h035e⟩ | ⟨h035a, h035b, h035c, h035d, h035e⟩
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012c, h013c, h123a]
                      · linarith only [h012a, h013c, h123a, h023c]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012c, h013c, h123a]
                      · linarith only [h012a, h013c, h123a, h023c]
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012c, h013c, h123a]
                      · linarith only [h012a, h013c, h123a, h023c]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012c, h013c, h123a]
                      · linarith only [h012a, h013c, h023c, h123a]
              · rcases h034 with ⟨h034a, h034b, h034c, h034d, h034e⟩ | ⟨h034a, h034b, h034c, h034d, h034e⟩
                · rcases h035 with ⟨h035a, h035b, h035c, h035d, h035e⟩ | ⟨h035a, h035b, h035c, h035d, h035e⟩
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012c, h013c, h123a]
                      · linarith only [h012a, h013c, h023c, h123a]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012c, h013c, h123a]
                      · linarith only [h012a, h013c, h123a, h023c]
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012c, h013c, h123a]
                      · linarith only [h012a, h013c, h123a, h023c]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012c, h013c, h123a]
                      · linarith only [h012a, h013c, h123a, h023c]
                · rcases h035 with ⟨h035a, h035b, h035c, h035d, h035e⟩ | ⟨h035a, h035b, h035c, h035d, h035e⟩
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012c, h013c, h123a]
                      · linarith only [h012a, h013c, h123a, h023c]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012c, h013c, h123a]
                      · linarith only [h012a, h013c, h023c, h123a]
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012c, h013c, h123a]
                      · linarith only [h012a, h013c, h123a, h023c]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012c, h013c, h123a]
                      · linarith only [h012a, h013c, h123a, h023c]
            · rcases h025 with ⟨h025a, h025b, h025c, h025d, h025e⟩ | ⟨h025a, h025b, h025c, h025d, h025e⟩
              · rcases h034 with ⟨h034a, h034b, h034c, h034d, h034e⟩ | ⟨h034a, h034b, h034c, h034d, h034e⟩
                · rcases h035 with ⟨h035a, h035b, h035c, h035d, h035e⟩ | ⟨h035a, h035b, h035c, h035d, h035e⟩
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012c, h013c, h123a]
                      · linarith only [h012a, h013c, h123a, h023c]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012c, h013c, h123a]
                      · linarith only [h012a, h013c, h123a, h023c]
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012c, h013c, h123a]
                      · linarith only [h012a, h013c, h023c, h123a]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012c, h013c, h123a]
                      · linarith only [h012a, h013c, h023c, h123a]
                · rcases h035 with ⟨h035a, h035b, h035c, h035d, h035e⟩ | ⟨h035a, h035b, h035c, h035d, h035e⟩
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012c, h013c, h123a]
                      · linarith only [h012a, h013c, h023c, h123a]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012c, h013c, h123a]
                      · linarith only [h012a, h013c, h123a, h023c]
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012c, h013c, h123a]
                      · linarith only [h012a, h013c, h123a, h023c]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012c, h013c, h123a]
                      · linarith only [h012a, h013c, h123a, h023c]
              · rcases h034 with ⟨h034a, h034b, h034c, h034d, h034e⟩ | ⟨h034a, h034b, h034c, h034d, h034e⟩
                · rcases h035 with ⟨h035a, h035b, h035c, h035d, h035e⟩ | ⟨h035a, h035b, h035c, h035d, h035e⟩
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012c, h013c, h123a]
                      · linarith only [h012a, h013c, h123a, h023c]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012c, h013c, h123a]
                      · linarith only [h012a, h013c, h123a, h023c]
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012c, h013c, h123a]
                      · linarith only [h012a, h013c, h123a, h023c]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012c, h013c, h123a]
                      · linarith only [h012a, h013c, h123a, h023c]
                · rcases h035 with ⟨h035a, h035b, h035c, h035d, h035e⟩ | ⟨h035a, h035b, h035c, h035d, h035e⟩
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012c, h013c, h123a]
                      · linarith only [h012a, h013c, h123a, h023c]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012c, h013c, h123a]
                      · linarith only [h012a, h013c, h023c, h123a]
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012c, h013c, h123a]
                      · linarith only [h012a, h013c, h123a, h023c]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012c, h013c, h123a]
                      · linarith only [h012a, h013c, h023c, h123a]
          · rcases h024 with ⟨h024a, h024b, h024c, h024d, h024e⟩ | ⟨h024a, h024b, h024c, h024d, h024e⟩
            · rcases h025 with ⟨h025a, h025b, h025c, h025d, h025e⟩ | ⟨h025a, h025b, h025c, h025d, h025e⟩
              · rcases h034 with ⟨h034a, h034b, h034c, h034d, h034e⟩ | ⟨h034a, h034b, h034c, h034d, h034e⟩
                · rcases h035 with ⟨h035a, h035b, h035c, h035d, h035e⟩ | ⟨h035a, h035b, h035c, h035d, h035e⟩
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012c, h013c, h123a]
                      · linarith only [ht, h012c, h013c, h123d]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012c, h013c, h123a]
                      · linarith only [ht, h012c, h013c, h123d]
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012c, h013c, h123a]
                      · linarith only [ht, h012c, h013c, h123d]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012c, h013c, h123a]
                      · linarith only [ht, h012c, h013c, h123d]
                · rcases h035 with ⟨h035a, h035b, h035c, h035d, h035e⟩ | ⟨h035a, h035b, h035c, h035d, h035e⟩
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012c, h013c, h123a]
                      · linarith only [ht, h012c, h013c, h123d]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012c, h013c, h123a]
                      · linarith only [ht, h012c, h013c, h123d]
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012c, h013c, h123a]
                      · linarith only [ht, h012c, h013c, h123d]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012c, h013c, h123a]
                      · linarith only [ht, h012c, h013c, h123d]
              · rcases h034 with ⟨h034a, h034b, h034c, h034d, h034e⟩ | ⟨h034a, h034b, h034c, h034d, h034e⟩
                · rcases h035 with ⟨h035a, h035b, h035c, h035d, h035e⟩ | ⟨h035a, h035b, h035c, h035d, h035e⟩
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012c, h013c, h123a]
                      · linarith only [ht, h012c, h013c, h123d]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012c, h013c, h123a]
                      · linarith only [ht, h012c, h013c, h123d]
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012c, h013c, h123a]
                      · linarith only [ht, h012c, h013c, h123d]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012c, h013c, h123a]
                      · linarith only [ht, h012c, h013c, h123d]
                · rcases h035 with ⟨h035a, h035b, h035c, h035d, h035e⟩ | ⟨h035a, h035b, h035c, h035d, h035e⟩
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012c, h013c, h123a]
                      · linarith only [ht, h012c, h013c, h123d]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012c, h013c, h123a]
                      · linarith only [ht, h012c, h013c, h123d]
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012c, h013c, h123a]
                      · linarith only [ht, h012c, h013c, h123d]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012c, h013c, h123a]
                      · linarith only [ht, h012c, h013c, h123d]
            · rcases h025 with ⟨h025a, h025b, h025c, h025d, h025e⟩ | ⟨h025a, h025b, h025c, h025d, h025e⟩
              · rcases h034 with ⟨h034a, h034b, h034c, h034d, h034e⟩ | ⟨h034a, h034b, h034c, h034d, h034e⟩
                · rcases h035 with ⟨h035a, h035b, h035c, h035d, h035e⟩ | ⟨h035a, h035b, h035c, h035d, h035e⟩
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012c, h013c, h123a]
                      · linarith only [ht, h012c, h013c, h123d]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012c, h013c, h123a]
                      · linarith only [ht, h012c, h013c, h123d]
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012c, h013c, h123a]
                      · linarith only [ht, h012c, h013c, h123d]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012c, h013c, h123a]
                      · linarith only [ht, h012c, h013c, h123d]
                · rcases h035 with ⟨h035a, h035b, h035c, h035d, h035e⟩ | ⟨h035a, h035b, h035c, h035d, h035e⟩
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012c, h013c, h123a]
                      · linarith only [ht, h012c, h013c, h123d]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012c, h013c, h123a]
                      · linarith only [ht, h012c, h013c, h123d]
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012c, h013c, h123a]
                      · linarith only [ht, h012c, h013c, h123d]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012c, h013c, h123a]
                      · linarith only [ht, h012c, h013c, h123d]
              · rcases h034 with ⟨h034a, h034b, h034c, h034d, h034e⟩ | ⟨h034a, h034b, h034c, h034d, h034e⟩
                · rcases h035 with ⟨h035a, h035b, h035c, h035d, h035e⟩ | ⟨h035a, h035b, h035c, h035d, h035e⟩
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012c, h013c, h123a]
                      · linarith only [ht, h012c, h013c, h123d]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012c, h013c, h123a]
                      · linarith only [ht, h012c, h013c, h123d]
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012c, h013c, h123a]
                      · linarith only [ht, h012c, h013c, h123d]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012c, h013c, h123a]
                      · linarith only [ht, h012c, h013c, h123d]
                · rcases h035 with ⟨h035a, h035b, h035c, h035d, h035e⟩ | ⟨h035a, h035b, h035c, h035d, h035e⟩
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012c, h013c, h123a]
                      · linarith only [ht, h012c, h013c, h123d]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012c, h013c, h123a]
                      · linarith only [ht, h012c, h013c, h123d]
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012c, h013c, h123a]
                      · linarith only [ht, h012c, h013c, h123d]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012c, h013c, h123a]
                      · linarith only [ht, h012c, h013c, h123d]
      · rcases h015 with ⟨h015a, h015b, h015c, h015d, h015e⟩ | ⟨h015a, h015b, h015c, h015d, h015e⟩
        · rcases h023 with ⟨h023a, h023b, h023c, h023d, h023e⟩ | ⟨h023a, h023b, h023c, h023d, h023e⟩
          · rcases h024 with ⟨h024a, h024b, h024c, h024d, h024e⟩ | ⟨h024a, h024b, h024c, h024d, h024e⟩
            · rcases h025 with ⟨h025a, h025b, h025c, h025d, h025e⟩ | ⟨h025a, h025b, h025c, h025d, h025e⟩
              · rcases h034 with ⟨h034a, h034b, h034c, h034d, h034e⟩ | ⟨h034a, h034b, h034c, h034d, h034e⟩
                · rcases h035 with ⟨h035a, h035b, h035c, h035d, h035e⟩ | ⟨h035a, h035b, h035c, h035d, h035e⟩
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012c, h013c, h123a]
                      · linarith only [h012a, h013c, h023c, h123a]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012c, h013c, h123a]
                      · linarith only [h012a, h013c, h023c, h123a]
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012c, h013c, h123a]
                      · linarith only [h012a, h013c, h023c, h123a]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012c, h013c, h123a]
                      · linarith only [h012a, h013c, h023c, h123a]
                · rcases h035 with ⟨h035a, h035b, h035c, h035d, h035e⟩ | ⟨h035a, h035b, h035c, h035d, h035e⟩
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012c, h013c, h123a]
                      · linarith only [h012a, h013c, h023c, h123a]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012c, h013c, h123a]
                      · linarith only [h012a, h013c, h023c, h123a]
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012c, h013c, h123a]
                      · linarith only [h012a, h013c, h023c, h123a]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012c, h013c, h123a]
                      · linarith only [h012a, h013c, h023c, h123a]
              · rcases h034 with ⟨h034a, h034b, h034c, h034d, h034e⟩ | ⟨h034a, h034b, h034c, h034d, h034e⟩
                · rcases h035 with ⟨h035a, h035b, h035c, h035d, h035e⟩ | ⟨h035a, h035b, h035c, h035d, h035e⟩
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012c, h013c, h123a]
                      · linarith only [h012a, h013c, h023c, h123a]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012c, h013c, h123a]
                      · linarith only [h012a, h013c, h023c, h123a]
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012c, h013c, h123a]
                      · linarith only [h012a, h013c, h023c, h123a]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012c, h013c, h123a]
                      · linarith only [h012a, h013c, h023c, h123a]
                · rcases h035 with ⟨h035a, h035b, h035c, h035d, h035e⟩ | ⟨h035a, h035b, h035c, h035d, h035e⟩
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012c, h013c, h123a]
                      · linarith only [h012a, h013c, h023c, h123a]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012c, h013c, h123a]
                      · linarith only [h012a, h013c, h023c, h123a]
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012c, h013c, h123a]
                      · linarith only [h012a, h013c, h023c, h123a]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012c, h013c, h123a]
                      · linarith only [h012a, h013c, h023c, h123a]
            · rcases h025 with ⟨h025a, h025b, h025c, h025d, h025e⟩ | ⟨h025a, h025b, h025c, h025d, h025e⟩
              · rcases h034 with ⟨h034a, h034b, h034c, h034d, h034e⟩ | ⟨h034a, h034b, h034c, h034d, h034e⟩
                · rcases h035 with ⟨h035a, h035b, h035c, h035d, h035e⟩ | ⟨h035a, h035b, h035c, h035d, h035e⟩
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012c, h013c, h123a]
                      · linarith only [h012a, h013c, h023c, h123a]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012c, h013c, h123a]
                      · linarith only [h012a, h013c, h023c, h123a]
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012c, h013c, h123a]
                      · linarith only [h012a, h013c, h023c, h123a]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012c, h013c, h123a]
                      · linarith only [h012a, h013c, h023c, h123a]
                · rcases h035 with ⟨h035a, h035b, h035c, h035d, h035e⟩ | ⟨h035a, h035b, h035c, h035d, h035e⟩
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012c, h013c, h123a]
                      · linarith only [h012a, h013c, h023c, h123a]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012c, h013c, h123a]
                      · linarith only [h012a, h013c, h023c, h123a]
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012c, h013c, h123a]
                      · linarith only [h012a, h013c, h023c, h123a]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012c, h013c, h123a]
                      · linarith only [h012a, h013c, h023c, h123a]
              · rcases h034 with ⟨h034a, h034b, h034c, h034d, h034e⟩ | ⟨h034a, h034b, h034c, h034d, h034e⟩
                · rcases h035 with ⟨h035a, h035b, h035c, h035d, h035e⟩ | ⟨h035a, h035b, h035c, h035d, h035e⟩
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012c, h013c, h123a]
                      · linarith only [h012a, h013c, h023c, h123a]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012c, h013c, h123a]
                      · linarith only [h012a, h013c, h023c, h123a]
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012c, h013c, h123a]
                      · linarith only [h012a, h013c, h023c, h123a]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012c, h013c, h123a]
                      · linarith only [h012a, h013c, h023c, h123a]
                · rcases h035 with ⟨h035a, h035b, h035c, h035d, h035e⟩ | ⟨h035a, h035b, h035c, h035d, h035e⟩
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012c, h013c, h123a]
                      · linarith only [h012a, h013c, h023c, h123a]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012c, h013c, h123a]
                      · linarith only [h012a, h013c, h023c, h123a]
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012c, h013c, h123a]
                      · linarith only [h012a, h013c, h023c, h123a]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012c, h013c, h123a]
                      · linarith only [h012a, h013c, h023c, h123a]
          · rcases h024 with ⟨h024a, h024b, h024c, h024d, h024e⟩ | ⟨h024a, h024b, h024c, h024d, h024e⟩
            · rcases h025 with ⟨h025a, h025b, h025c, h025d, h025e⟩ | ⟨h025a, h025b, h025c, h025d, h025e⟩
              · rcases h034 with ⟨h034a, h034b, h034c, h034d, h034e⟩ | ⟨h034a, h034b, h034c, h034d, h034e⟩
                · rcases h035 with ⟨h035a, h035b, h035c, h035d, h035e⟩ | ⟨h035a, h035b, h035c, h035d, h035e⟩
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012c, h013c, h123a]
                      · linarith only [ht, h012c, h013c, h123d]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012c, h013c, h123a]
                      · linarith only [ht, h012c, h013c, h123d]
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012c, h013c, h123a]
                      · linarith only [ht, h012c, h013c, h123d]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012c, h013c, h123a]
                      · linarith only [ht, h012c, h013c, h123d]
                · rcases h035 with ⟨h035a, h035b, h035c, h035d, h035e⟩ | ⟨h035a, h035b, h035c, h035d, h035e⟩
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012c, h013c, h123a]
                      · linarith only [ht, h012c, h013c, h123d]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012c, h013c, h123a]
                      · linarith only [ht, h012c, h013c, h123d]
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012c, h013c, h123a]
                      · linarith only [ht, h012c, h013c, h123d]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012c, h013c, h123a]
                      · linarith only [ht, h012c, h013c, h123d]
              · rcases h034 with ⟨h034a, h034b, h034c, h034d, h034e⟩ | ⟨h034a, h034b, h034c, h034d, h034e⟩
                · rcases h035 with ⟨h035a, h035b, h035c, h035d, h035e⟩ | ⟨h035a, h035b, h035c, h035d, h035e⟩
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012c, h013c, h123a]
                      · linarith only [ht, h012c, h013c, h123d]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012c, h013c, h123a]
                      · linarith only [ht, h012c, h013c, h123d]
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012c, h013c, h123a]
                      · linarith only [ht, h012c, h013c, h123d]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012c, h013c, h123a]
                      · linarith only [ht, h012c, h013c, h123d]
                · rcases h035 with ⟨h035a, h035b, h035c, h035d, h035e⟩ | ⟨h035a, h035b, h035c, h035d, h035e⟩
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012c, h013c, h123a]
                      · linarith only [ht, h012c, h013c, h123d]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012c, h013c, h123a]
                      · linarith only [ht, h012c, h013c, h123d]
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012c, h013c, h123a]
                      · linarith only [ht, h012c, h013c, h123d]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012c, h013c, h123a]
                      · linarith only [ht, h012c, h013c, h123d]
            · rcases h025 with ⟨h025a, h025b, h025c, h025d, h025e⟩ | ⟨h025a, h025b, h025c, h025d, h025e⟩
              · rcases h034 with ⟨h034a, h034b, h034c, h034d, h034e⟩ | ⟨h034a, h034b, h034c, h034d, h034e⟩
                · rcases h035 with ⟨h035a, h035b, h035c, h035d, h035e⟩ | ⟨h035a, h035b, h035c, h035d, h035e⟩
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012c, h013c, h123a]
                      · linarith only [ht, h012c, h013c, h123d]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012c, h013c, h123a]
                      · linarith only [ht, h012c, h013c, h123d]
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012c, h013c, h123a]
                      · linarith only [ht, h012c, h013c, h123d]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012c, h013c, h123a]
                      · linarith only [ht, h012c, h013c, h123d]
                · rcases h035 with ⟨h035a, h035b, h035c, h035d, h035e⟩ | ⟨h035a, h035b, h035c, h035d, h035e⟩
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012c, h013c, h123a]
                      · linarith only [ht, h012c, h013c, h123d]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012c, h013c, h123a]
                      · linarith only [ht, h012c, h013c, h123d]
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012c, h013c, h123a]
                      · linarith only [ht, h012c, h013c, h123d]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012c, h013c, h123a]
                      · linarith only [ht, h012c, h013c, h123d]
              · rcases h034 with ⟨h034a, h034b, h034c, h034d, h034e⟩ | ⟨h034a, h034b, h034c, h034d, h034e⟩
                · rcases h035 with ⟨h035a, h035b, h035c, h035d, h035e⟩ | ⟨h035a, h035b, h035c, h035d, h035e⟩
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012c, h013c, h123a]
                      · linarith only [ht, h012c, h013c, h123d]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012c, h013c, h123a]
                      · linarith only [ht, h012c, h013c, h123d]
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012c, h013c, h123a]
                      · linarith only [ht, h012c, h013c, h123d]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012c, h013c, h123a]
                      · linarith only [ht, h012c, h013c, h123d]
                · rcases h035 with ⟨h035a, h035b, h035c, h035d, h035e⟩ | ⟨h035a, h035b, h035c, h035d, h035e⟩
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012c, h013c, h123a]
                      · linarith only [ht, h012c, h013c, h123d]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012c, h013c, h123a]
                      · linarith only [ht, h012c, h013c, h123d]
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012c, h013c, h123a]
                      · linarith only [ht, h012c, h013c, h123d]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012c, h013c, h123a]
                      · linarith only [ht, h012c, h013c, h123d]
        · rcases h023 with ⟨h023a, h023b, h023c, h023d, h023e⟩ | ⟨h023a, h023b, h023c, h023d, h023e⟩
          · rcases h024 with ⟨h024a, h024b, h024c, h024d, h024e⟩ | ⟨h024a, h024b, h024c, h024d, h024e⟩
            · rcases h025 with ⟨h025a, h025b, h025c, h025d, h025e⟩ | ⟨h025a, h025b, h025c, h025d, h025e⟩
              · rcases h034 with ⟨h034a, h034b, h034c, h034d, h034e⟩ | ⟨h034a, h034b, h034c, h034d, h034e⟩
                · rcases h035 with ⟨h035a, h035b, h035c, h035d, h035e⟩ | ⟨h035a, h035b, h035c, h035d, h035e⟩
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012c, h013c, h123a]
                      · linarith only [h012a, h013c, h023c, h123a]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012c, h013c, h123a]
                      · linarith only [h012a, h013c, h023c, h123a]
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012c, h013c, h123a]
                      · linarith only [h012a, h013c, h023c, h123a]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012c, h013c, h123a]
                      · linarith only [h012a, h013c, h023c, h123a]
                · rcases h035 with ⟨h035a, h035b, h035c, h035d, h035e⟩ | ⟨h035a, h035b, h035c, h035d, h035e⟩
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012c, h013c, h123a]
                      · linarith only [h012a, h013c, h023c, h123a]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012c, h013c, h123a]
                      · linarith only [h012a, h013c, h023c, h123a]
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012c, h013c, h123a]
                      · linarith only [h012a, h013c, h023c, h123a]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012c, h013c, h123a]
                      · linarith only [h012a, h013c, h023c, h123a]
              · rcases h034 with ⟨h034a, h034b, h034c, h034d, h034e⟩ | ⟨h034a, h034b, h034c, h034d, h034e⟩
                · rcases h035 with ⟨h035a, h035b, h035c, h035d, h035e⟩ | ⟨h035a, h035b, h035c, h035d, h035e⟩
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012c, h013c, h123a]
                      · linarith only [h012a, h013c, h023c, h123a]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012c, h013c, h123a]
                      · linarith only [h012a, h013c, h023c, h123a]
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012c, h013c, h123a]
                      · linarith only [h012a, h013c, h023c, h123a]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012c, h013c, h123a]
                      · linarith only [h012a, h013c, h023c, h123a]
                · rcases h035 with ⟨h035a, h035b, h035c, h035d, h035e⟩ | ⟨h035a, h035b, h035c, h035d, h035e⟩
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012c, h013c, h123a]
                      · linarith only [h012a, h013c, h023c, h123a]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012c, h013c, h123a]
                      · linarith only [h012a, h013c, h023c, h123a]
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012c, h013c, h123a]
                      · linarith only [h012a, h013c, h023c, h123a]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012c, h013c, h123a]
                      · linarith only [h012a, h013c, h023c, h123a]
            · rcases h025 with ⟨h025a, h025b, h025c, h025d, h025e⟩ | ⟨h025a, h025b, h025c, h025d, h025e⟩
              · rcases h034 with ⟨h034a, h034b, h034c, h034d, h034e⟩ | ⟨h034a, h034b, h034c, h034d, h034e⟩
                · rcases h035 with ⟨h035a, h035b, h035c, h035d, h035e⟩ | ⟨h035a, h035b, h035c, h035d, h035e⟩
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012c, h013c, h123a]
                      · linarith only [h012a, h013c, h023c, h123a]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012c, h013c, h123a]
                      · linarith only [h012a, h013c, h023c, h123a]
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012c, h013c, h123a]
                      · linarith only [h012a, h013c, h023c, h123a]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012c, h013c, h123a]
                      · linarith only [h012a, h013c, h023c, h123a]
                · rcases h035 with ⟨h035a, h035b, h035c, h035d, h035e⟩ | ⟨h035a, h035b, h035c, h035d, h035e⟩
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012c, h013c, h123a]
                      · linarith only [h012a, h013c, h023c, h123a]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012c, h013c, h123a]
                      · linarith only [h012a, h013c, h023c, h123a]
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012c, h013c, h123a]
                      · linarith only [h012a, h013c, h023c, h123a]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012c, h013c, h123a]
                      · linarith only [h012a, h013c, h023c, h123a]
              · rcases h034 with ⟨h034a, h034b, h034c, h034d, h034e⟩ | ⟨h034a, h034b, h034c, h034d, h034e⟩
                · rcases h035 with ⟨h035a, h035b, h035c, h035d, h035e⟩ | ⟨h035a, h035b, h035c, h035d, h035e⟩
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012c, h013c, h123a]
                      · linarith only [h012a, h013c, h023c, h123a]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012c, h013c, h123a]
                      · linarith only [h012a, h013c, h023c, h123a]
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012c, h013c, h123a]
                      · linarith only [h012a, h013c, h023c, h123a]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012c, h013c, h123a]
                      · linarith only [h012a, h013c, h023c, h123a]
                · rcases h035 with ⟨h035a, h035b, h035c, h035d, h035e⟩ | ⟨h035a, h035b, h035c, h035d, h035e⟩
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012c, h013c, h123a]
                      · linarith only [h012a, h013c, h023c, h123a]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012c, h013c, h123a]
                      · linarith only [h012a, h013c, h023c, h123a]
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012c, h013c, h123a]
                      · linarith only [h012a, h013c, h023c, h123a]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012c, h013c, h123a]
                      · linarith only [h012a, h013c, h023c, h123a]
          · rcases h024 with ⟨h024a, h024b, h024c, h024d, h024e⟩ | ⟨h024a, h024b, h024c, h024d, h024e⟩
            · rcases h025 with ⟨h025a, h025b, h025c, h025d, h025e⟩ | ⟨h025a, h025b, h025c, h025d, h025e⟩
              · rcases h034 with ⟨h034a, h034b, h034c, h034d, h034e⟩ | ⟨h034a, h034b, h034c, h034d, h034e⟩
                · rcases h035 with ⟨h035a, h035b, h035c, h035d, h035e⟩ | ⟨h035a, h035b, h035c, h035d, h035e⟩
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012c, h013c, h123a]
                      · linarith only [ht, h012c, h013c, h123d]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012c, h013c, h123a]
                      · linarith only [ht, h012c, h013c, h123d]
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012c, h013c, h123a]
                      · linarith only [ht, h012c, h013c, h123d]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012c, h013c, h123a]
                      · linarith only [ht, h012c, h013c, h123d]
                · rcases h035 with ⟨h035a, h035b, h035c, h035d, h035e⟩ | ⟨h035a, h035b, h035c, h035d, h035e⟩
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012c, h013c, h123a]
                      · linarith only [ht, h012c, h013c, h123d]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012c, h013c, h123a]
                      · linarith only [ht, h012c, h013c, h123d]
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012c, h013c, h123a]
                      · linarith only [ht, h012c, h013c, h123d]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012c, h013c, h123a]
                      · linarith only [ht, h012c, h013c, h123d]
              · rcases h034 with ⟨h034a, h034b, h034c, h034d, h034e⟩ | ⟨h034a, h034b, h034c, h034d, h034e⟩
                · rcases h035 with ⟨h035a, h035b, h035c, h035d, h035e⟩ | ⟨h035a, h035b, h035c, h035d, h035e⟩
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012c, h013c, h123a]
                      · linarith only [ht, h012c, h013c, h123d]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012c, h013c, h123a]
                      · linarith only [ht, h012c, h013c, h123d]
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012c, h013c, h123a]
                      · linarith only [ht, h012c, h013c, h123d]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012c, h013c, h123a]
                      · linarith only [ht, h012c, h013c, h123d]
                · rcases h035 with ⟨h035a, h035b, h035c, h035d, h035e⟩ | ⟨h035a, h035b, h035c, h035d, h035e⟩
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012c, h013c, h123a]
                      · linarith only [ht, h012c, h013c, h123d]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012c, h013c, h123a]
                      · linarith only [ht, h012c, h013c, h123d]
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012c, h013c, h123a]
                      · linarith only [ht, h012c, h013c, h123d]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012c, h013c, h123a]
                      · linarith only [ht, h012c, h013c, h123d]
            · rcases h025 with ⟨h025a, h025b, h025c, h025d, h025e⟩ | ⟨h025a, h025b, h025c, h025d, h025e⟩
              · rcases h034 with ⟨h034a, h034b, h034c, h034d, h034e⟩ | ⟨h034a, h034b, h034c, h034d, h034e⟩
                · rcases h035 with ⟨h035a, h035b, h035c, h035d, h035e⟩ | ⟨h035a, h035b, h035c, h035d, h035e⟩
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012c, h013c, h123a]
                      · linarith only [ht, h012c, h013c, h123d]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012c, h013c, h123a]
                      · linarith only [ht, h012c, h013c, h123d]
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012c, h013c, h123a]
                      · linarith only [ht, h012c, h013c, h123d]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012c, h013c, h123a]
                      · linarith only [ht, h012c, h013c, h123d]
                · rcases h035 with ⟨h035a, h035b, h035c, h035d, h035e⟩ | ⟨h035a, h035b, h035c, h035d, h035e⟩
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012c, h013c, h123a]
                      · linarith only [ht, h012c, h013c, h123d]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012c, h013c, h123a]
                      · linarith only [ht, h012c, h013c, h123d]
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012c, h013c, h123a]
                      · linarith only [ht, h012c, h013c, h123d]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012c, h013c, h123a]
                      · linarith only [ht, h012c, h013c, h123d]
              · rcases h034 with ⟨h034a, h034b, h034c, h034d, h034e⟩ | ⟨h034a, h034b, h034c, h034d, h034e⟩
                · rcases h035 with ⟨h035a, h035b, h035c, h035d, h035e⟩ | ⟨h035a, h035b, h035c, h035d, h035e⟩
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012c, h013c, h123a]
                      · linarith only [ht, h012c, h013c, h123d]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012c, h013c, h123a]
                      · linarith only [ht, h012c, h013c, h123d]
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012c, h013c, h123a]
                      · linarith only [ht, h012c, h013c, h123d]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012c, h013c, h123a]
                      · linarith only [ht, h012c, h013c, h123d]
                · rcases h035 with ⟨h035a, h035b, h035c, h035d, h035e⟩ | ⟨h035a, h035b, h035c, h035d, h035e⟩
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012c, h013c, h123a]
                      · linarith only [ht, h012c, h013c, h123d]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012c, h013c, h123a]
                      · linarith only [ht, h012c, h013c, h123d]
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012c, h013c, h123a]
                      · linarith only [ht, h012c, h013c, h123d]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012c, h013c, h123a]
                      · linarith only [ht, h012c, h013c, h123d]
  · rcases h013 with ⟨h013a, h013b, h013c, h013d, h013e⟩ | ⟨h013a, h013b, h013c, h013d, h013e⟩
    · rcases h014 with ⟨h014a, h014b, h014c, h014d, h014e⟩ | ⟨h014a, h014b, h014c, h014d, h014e⟩
      · rcases h015 with ⟨h015a, h015b, h015c, h015d, h015e⟩ | ⟨h015a, h015b, h015c, h015d, h015e⟩
        · rcases h023 with ⟨h023a, h023b, h023c, h023d, h023e⟩ | ⟨h023a, h023b, h023c, h023d, h023e⟩
          · rcases h024 with ⟨h024a, h024b, h024c, h024d, h024e⟩ | ⟨h024a, h024b, h024c, h024d, h024e⟩
            · rcases h025 with ⟨h025a, h025b, h025c, h025d, h025e⟩ | ⟨h025a, h025b, h025c, h025d, h025e⟩
              · rcases h034 with ⟨h034a, h034b, h034c, h034d, h034e⟩ | ⟨h034a, h034b, h034c, h034d, h034e⟩
                · rcases h035 with ⟨h035a, h035b, h035c, h035d, h035e⟩ | ⟨h035a, h035b, h035c, h035d, h035e⟩
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, h012c, h013c, h123d]
                      · linarith only [h012c, h013c, h123b]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, h012c, h013c, h123d]
                      · linarith only [h012c, h013c, h123b]
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, h012c, h013c, h123d]
                      · linarith only [h012c, h013c, h123b]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, h012c, h013c, h123d]
                      · linarith only [h012c, h013c, h123b]
                · rcases h035 with ⟨h035a, h035b, h035c, h035d, h035e⟩ | ⟨h035a, h035b, h035c, h035d, h035e⟩
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, h012c, h013c, h123d]
                      · linarith only [h012c, h013c, h123b]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, h012c, h013c, h123d]
                      · linarith only [h012c, h013c, h123b]
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, h012c, h013c, h123d]
                      · linarith only [h012c, h013c, h123b]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, h012c, h013c, h123d]
                      · linarith only [h012c, h013c, h123b]
              · rcases h034 with ⟨h034a, h034b, h034c, h034d, h034e⟩ | ⟨h034a, h034b, h034c, h034d, h034e⟩
                · rcases h035 with ⟨h035a, h035b, h035c, h035d, h035e⟩ | ⟨h035a, h035b, h035c, h035d, h035e⟩
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, h012c, h013c, h123d]
                      · linarith only [h012c, h013c, h123b]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, h012c, h013c, h123d]
                      · linarith only [h012c, h013c, h123b]
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, h012c, h013c, h123d]
                      · linarith only [h012c, h013c, h123b]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, h012c, h013c, h123d]
                      · linarith only [h012c, h013c, h123b]
                · rcases h035 with ⟨h035a, h035b, h035c, h035d, h035e⟩ | ⟨h035a, h035b, h035c, h035d, h035e⟩
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, h012c, h013c, h123d]
                      · linarith only [h012c, h013c, h123b]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, h012c, h013c, h123d]
                      · linarith only [h012c, h013c, h123b]
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, h012c, h013c, h123d]
                      · linarith only [h012c, h013c, h123b]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, h012c, h013c, h123d]
                      · linarith only [h012c, h013c, h123b]
            · rcases h025 with ⟨h025a, h025b, h025c, h025d, h025e⟩ | ⟨h025a, h025b, h025c, h025d, h025e⟩
              · rcases h034 with ⟨h034a, h034b, h034c, h034d, h034e⟩ | ⟨h034a, h034b, h034c, h034d, h034e⟩
                · rcases h035 with ⟨h035a, h035b, h035c, h035d, h035e⟩ | ⟨h035a, h035b, h035c, h035d, h035e⟩
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, h012c, h013c, h123d]
                      · linarith only [h012c, h013c, h123b]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, h012c, h013c, h123d]
                      · linarith only [h012c, h013c, h123b]
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, h012c, h013c, h123d]
                      · linarith only [h012c, h013c, h123b]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, h012c, h013c, h123d]
                      · linarith only [h012c, h013c, h123b]
                · rcases h035 with ⟨h035a, h035b, h035c, h035d, h035e⟩ | ⟨h035a, h035b, h035c, h035d, h035e⟩
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, h012c, h013c, h123d]
                      · linarith only [h012c, h013c, h123b]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, h012c, h013c, h123d]
                      · linarith only [h012c, h013c, h123b]
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, h012c, h013c, h123d]
                      · linarith only [h012c, h013c, h123b]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, h012c, h013c, h123d]
                      · linarith only [h012c, h013c, h123b]
              · rcases h034 with ⟨h034a, h034b, h034c, h034d, h034e⟩ | ⟨h034a, h034b, h034c, h034d, h034e⟩
                · rcases h035 with ⟨h035a, h035b, h035c, h035d, h035e⟩ | ⟨h035a, h035b, h035c, h035d, h035e⟩
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, h012c, h013c, h123d]
                      · linarith only [h012c, h013c, h123b]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, h012c, h013c, h123d]
                      · linarith only [h012c, h013c, h123b]
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, h012c, h013c, h123d]
                      · linarith only [h012c, h013c, h123b]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, h012c, h013c, h123d]
                      · linarith only [h012c, h013c, h123b]
                · rcases h035 with ⟨h035a, h035b, h035c, h035d, h035e⟩ | ⟨h035a, h035b, h035c, h035d, h035e⟩
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, h012c, h013c, h123d]
                      · linarith only [h012c, h013c, h123b]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, h012c, h013c, h123d]
                      · linarith only [h012c, h013c, h123b]
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, h012c, h013c, h123d]
                      · linarith only [h012c, h013c, h123b]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, h012c, h013c, h123d]
                      · linarith only [h012c, h013c, h123b]
          · rcases h024 with ⟨h024a, h024b, h024c, h024d, h024e⟩ | ⟨h024a, h024b, h024c, h024d, h024e⟩
            · rcases h025 with ⟨h025a, h025b, h025c, h025d, h025e⟩ | ⟨h025a, h025b, h025c, h025d, h025e⟩
              · rcases h034 with ⟨h034a, h034b, h034c, h034d, h034e⟩ | ⟨h034a, h034b, h034c, h034d, h034e⟩
                · rcases h035 with ⟨h035a, h035b, h035c, h035d, h035e⟩ | ⟨h035a, h035b, h035c, h035d, h035e⟩
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, r02.2, r12.1, h012c, h013c, h123b, h023c]
                      · linarith only [h012c, h013c, h123b]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012b, h013c, h123b, h023c]
                      · linarith only [h012c, h013c, h123b]
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012b, h013c, h123b, h023c]
                      · linarith only [h012c, h013c, h123b]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012b, h013c, h123b, h023c]
                      · linarith only [h012c, h013c, h123b]
                · rcases h035 with ⟨h035a, h035b, h035c, h035d, h035e⟩ | ⟨h035a, h035b, h035c, h035d, h035e⟩
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012b, h013c, h123b, h023c]
                      · linarith only [h012c, h013c, h123b]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012b, h013c, h123b, h023c]
                      · linarith only [h012c, h013c, h123b]
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012b, h013c, h023c, h123b]
                      · linarith only [h012c, h013c, h123b]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012b, h013c, h123b, h023c]
                      · linarith only [h012c, h013c, h123b]
              · rcases h034 with ⟨h034a, h034b, h034c, h034d, h034e⟩ | ⟨h034a, h034b, h034c, h034d, h034e⟩
                · rcases h035 with ⟨h035a, h035b, h035c, h035d, h035e⟩ | ⟨h035a, h035b, h035c, h035d, h035e⟩
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012b, h013c, h023c, h123b]
                      · linarith only [h012c, h013c, h123b]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012b, h013c, h123b, h023c]
                      · linarith only [h012c, h013c, h123b]
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012b, h013c, h123b, h023c]
                      · linarith only [h012c, h013c, h123b]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012b, h013c, h123b, h023c]
                      · linarith only [h012c, h013c, h123b]
                · rcases h035 with ⟨h035a, h035b, h035c, h035d, h035e⟩ | ⟨h035a, h035b, h035c, h035d, h035e⟩
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012b, h013c, h123b, h023c]
                      · linarith only [h012c, h013c, h123b]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012b, h013c, h123b, h023c]
                      · linarith only [h012c, h013c, h123b]
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012b, h013c, h023c, h123b]
                      · linarith only [h012c, h013c, h123b]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012b, h013c, h023c, h123b]
                      · linarith only [h012c, h013c, h123b]
            · rcases h025 with ⟨h025a, h025b, h025c, h025d, h025e⟩ | ⟨h025a, h025b, h025c, h025d, h025e⟩
              · rcases h034 with ⟨h034a, h034b, h034c, h034d, h034e⟩ | ⟨h034a, h034b, h034c, h034d, h034e⟩
                · rcases h035 with ⟨h035a, h035b, h035c, h035d, h035e⟩ | ⟨h035a, h035b, h035c, h035d, h035e⟩
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012b, h013c, h123b, h023c]
                      · linarith only [h012c, h013c, h123b]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012b, h013c, h023c, h123b]
                      · linarith only [h012c, h013c, h123b]
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012b, h013c, h123b, h023c]
                      · linarith only [h012c, h013c, h123b]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012b, h013c, h123b, h023c]
                      · linarith only [h012c, h013c, h123b]
                · rcases h035 with ⟨h035a, h035b, h035c, h035d, h035e⟩ | ⟨h035a, h035b, h035c, h035d, h035e⟩
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012b, h013c, h123b, h023c]
                      · linarith only [h012c, h013c, h123b]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012b, h013c, h023c, h123b]
                      · linarith only [h012c, h013c, h123b]
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012b, h013c, h123b, h023c]
                      · linarith only [h012c, h013c, h123b]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012b, h013c, h123b, h023c]
                      · linarith only [h012c, h013c, h123b]
              · rcases h034 with ⟨h034a, h034b, h034c, h034d, h034e⟩ | ⟨h034a, h034b, h034c, h034d, h034e⟩
                · rcases h035 with ⟨h035a, h035b, h035c, h035d, h035e⟩ | ⟨h035a, h035b, h035c, h035d, h035e⟩
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012b, h013c, h123b, h023c]
                      · linarith only [h012c, h013c, h123b]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012b, h013c, h023c, h123b]
                      · linarith only [h012c, h013c, h123b]
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012b, h013c, h123b, h023c]
                      · linarith only [h012c, h013c, h123b]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012b, h013c, h123b, h023c]
                      · linarith only [h123b, h012c, h013c]
                · rcases h035 with ⟨h035a, h035b, h035c, h035d, h035e⟩ | ⟨h035a, h035b, h035c, h035d, h035e⟩
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012b, h013c, h123b, h023c]
                      · linarith only [h012c, h013c, h123b]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012b, h013c, h023c, h123b]
                      · linarith only [h012c, h013c, h123b]
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012b, h013c, h023c, h123b]
                      · linarith only [h012c, h013c, h123b]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012b, h013c, h123b, h023c]
                      · linarith only [h012c, h013c, h123b]
        · rcases h023 with ⟨h023a, h023b, h023c, h023d, h023e⟩ | ⟨h023a, h023b, h023c, h023d, h023e⟩
          · rcases h024 with ⟨h024a, h024b, h024c, h024d, h024e⟩ | ⟨h024a, h024b, h024c, h024d, h024e⟩
            · rcases h025 with ⟨h025a, h025b, h025c, h025d, h025e⟩ | ⟨h025a, h025b, h025c, h025d, h025e⟩
              · rcases h034 with ⟨h034a, h034b, h034c, h034d, h034e⟩ | ⟨h034a, h034b, h034c, h034d, h034e⟩
                · rcases h035 with ⟨h035a, h035b, h035c, h035d, h035e⟩ | ⟨h035a, h035b, h035c, h035d, h035e⟩
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, h012c, h013c, h123d]
                      · linarith only [h012c, h013c, h123b]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, h012c, h013c, h123d]
                      · linarith only [h012c, h013c, h123b]
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, h012c, h013c, h123d]
                      · linarith only [h012c, h013c, h123b]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, h012c, h013c, h123d]
                      · linarith only [h012c, h013c, h123b]
                · rcases h035 with ⟨h035a, h035b, h035c, h035d, h035e⟩ | ⟨h035a, h035b, h035c, h035d, h035e⟩
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, h012c, h013c, h123d]
                      · linarith only [h012c, h013c, h123b]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, h012c, h013c, h123d]
                      · linarith only [h012c, h013c, h123b]
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, h012c, h013c, h123d]
                      · linarith only [h012c, h013c, h123b]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, h012c, h013c, h123d]
                      · linarith only [h012c, h013c, h123b]
              · rcases h034 with ⟨h034a, h034b, h034c, h034d, h034e⟩ | ⟨h034a, h034b, h034c, h034d, h034e⟩
                · rcases h035 with ⟨h035a, h035b, h035c, h035d, h035e⟩ | ⟨h035a, h035b, h035c, h035d, h035e⟩
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, h012c, h013c, h123d]
                      · linarith only [h012c, h013c, h123b]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, h012c, h013c, h123d]
                      · linarith only [h012c, h013c, h123b]
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, h012c, h013c, h123d]
                      · linarith only [h012c, h013c, h123b]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, h012c, h013c, h123d]
                      · linarith only [h012c, h013c, h123b]
                · rcases h035 with ⟨h035a, h035b, h035c, h035d, h035e⟩ | ⟨h035a, h035b, h035c, h035d, h035e⟩
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, h012c, h013c, h123d]
                      · linarith only [h012c, h013c, h123b]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, h012c, h013c, h123d]
                      · linarith only [h012c, h013c, h123b]
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, h012c, h013c, h123d]
                      · linarith only [h012c, h013c, h123b]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, h012c, h013c, h123d]
                      · linarith only [h012c, h013c, h123b]
            · rcases h025 with ⟨h025a, h025b, h025c, h025d, h025e⟩ | ⟨h025a, h025b, h025c, h025d, h025e⟩
              · rcases h034 with ⟨h034a, h034b, h034c, h034d, h034e⟩ | ⟨h034a, h034b, h034c, h034d, h034e⟩
                · rcases h035 with ⟨h035a, h035b, h035c, h035d, h035e⟩ | ⟨h035a, h035b, h035c, h035d, h035e⟩
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, h012c, h013c, h123d]
                      · linarith only [h012c, h013c, h123b]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, h012c, h013c, h123d]
                      · linarith only [h012c, h013c, h123b]
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, h012c, h013c, h123d]
                      · linarith only [h012c, h013c, h123b]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, h012c, h013c, h123d]
                      · linarith only [h012c, h013c, h123b]
                · rcases h035 with ⟨h035a, h035b, h035c, h035d, h035e⟩ | ⟨h035a, h035b, h035c, h035d, h035e⟩
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, h012c, h013c, h123d]
                      · linarith only [h012c, h013c, h123b]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, h012c, h013c, h123d]
                      · linarith only [h012c, h013c, h123b]
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, h012c, h013c, h123d]
                      · linarith only [h012c, h013c, h123b]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, h012c, h013c, h123d]
                      · linarith only [h012c, h013c, h123b]
              · rcases h034 with ⟨h034a, h034b, h034c, h034d, h034e⟩ | ⟨h034a, h034b, h034c, h034d, h034e⟩
                · rcases h035 with ⟨h035a, h035b, h035c, h035d, h035e⟩ | ⟨h035a, h035b, h035c, h035d, h035e⟩
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, h012c, h013c, h123d]
                      · linarith only [h012c, h013c, h123b]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, h012c, h013c, h123d]
                      · linarith only [h012c, h013c, h123b]
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, h012c, h013c, h123d]
                      · linarith only [h012c, h013c, h123b]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, h012c, h013c, h123d]
                      · linarith only [h012c, h013c, h123b]
                · rcases h035 with ⟨h035a, h035b, h035c, h035d, h035e⟩ | ⟨h035a, h035b, h035c, h035d, h035e⟩
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, h012c, h013c, h123d]
                      · linarith only [h012c, h013c, h123b]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, h012c, h013c, h123d]
                      · linarith only [h012c, h013c, h123b]
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, h012c, h013c, h123d]
                      · linarith only [h012c, h013c, h123b]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, h012c, h013c, h123d]
                      · linarith only [h012c, h013c, h123b]
          · rcases h024 with ⟨h024a, h024b, h024c, h024d, h024e⟩ | ⟨h024a, h024b, h024c, h024d, h024e⟩
            · rcases h025 with ⟨h025a, h025b, h025c, h025d, h025e⟩ | ⟨h025a, h025b, h025c, h025d, h025e⟩
              · rcases h034 with ⟨h034a, h034b, h034c, h034d, h034e⟩ | ⟨h034a, h034b, h034c, h034d, h034e⟩
                · rcases h035 with ⟨h035a, h035b, h035c, h035d, h035e⟩ | ⟨h035a, h035b, h035c, h035d, h035e⟩
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012b, h013c, h023c, h123b]
                      · linarith only [h012c, h013c, h123b]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012b, h013c, h023c, h123b]
                      · linarith only [h012c, h013c, h123b]
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012b, h013c, h023c, h123b]
                      · linarith only [h012c, h013c, h123b]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012b, h013c, h023c, h123b]
                      · linarith only [h012c, h013c, h123b]
                · rcases h035 with ⟨h035a, h035b, h035c, h035d, h035e⟩ | ⟨h035a, h035b, h035c, h035d, h035e⟩
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012b, h013c, h023c, h123b]
                      · linarith only [h012c, h013c, h123b]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012b, h013c, h023c, h123b]
                      · linarith only [h012c, h013c, h123b]
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012b, h013c, h023c, h123b]
                      · linarith only [h012c, h013c, h123b]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012b, h013c, h023c, h123b]
                      · linarith only [h012c, h013c, h123b]
              · rcases h034 with ⟨h034a, h034b, h034c, h034d, h034e⟩ | ⟨h034a, h034b, h034c, h034d, h034e⟩
                · rcases h035 with ⟨h035a, h035b, h035c, h035d, h035e⟩ | ⟨h035a, h035b, h035c, h035d, h035e⟩
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012b, h013c, h023c, h123b]
                      · linarith only [h012c, h013c, h123b]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012b, h013c, h123b, h023c]
                      · linarith only [h012c, h013c, h123b]
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012b, h013c, h023c, h123b]
                      · linarith only [h012c, h013c, h123b]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012b, h013c, h023c, h123b]
                      · linarith only [h012c, h013c, h123b]
                · rcases h035 with ⟨h035a, h035b, h035c, h035d, h035e⟩ | ⟨h035a, h035b, h035c, h035d, h035e⟩
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012b, h013c, h023c, h123b]
                      · linarith only [h012c, h013c, h123b]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012b, h013c, h023c, h123b]
                      · linarith only [h012c, h013c, h123b]
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012b, h013c, h023c, h123b]
                      · linarith only [h012c, h013c, h123b]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012b, h013c, h023c, h123b]
                      · linarith only [h012c, h013c, h123b]
            · rcases h025 with ⟨h025a, h025b, h025c, h025d, h025e⟩ | ⟨h025a, h025b, h025c, h025d, h025e⟩
              · rcases h034 with ⟨h034a, h034b, h034c, h034d, h034e⟩ | ⟨h034a, h034b, h034c, h034d, h034e⟩
                · rcases h035 with ⟨h035a, h035b, h035c, h035d, h035e⟩ | ⟨h035a, h035b, h035c, h035d, h035e⟩
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012b, h013c, h023c, h123b]
                      · linarith only [h012c, h013c, h123b]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012b, h013c, h023c, h123b]
                      · linarith only [h012c, h013c, h123b]
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012b, h013c, h023c, h123b]
                      · linarith only [h012c, h013c, h123b]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012b, h013c, h023c, h123b]
                      · linarith only [h012c, h013c, h123b]
                · rcases h035 with ⟨h035a, h035b, h035c, h035d, h035e⟩ | ⟨h035a, h035b, h035c, h035d, h035e⟩
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012b, h013c, h023c, h123b]
                      · linarith only [h012c, h013c, h123b]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012b, h013c, h023c, h123b]
                      · linarith only [h012c, h013c, h123b]
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012b, h013c, h023c, h123b]
                      · linarith only [h012c, h013c, h123b]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012b, h013c, h023c, h123b]
                      · linarith only [h012c, h013c, h123b]
              · rcases h034 with ⟨h034a, h034b, h034c, h034d, h034e⟩ | ⟨h034a, h034b, h034c, h034d, h034e⟩
                · rcases h035 with ⟨h035a, h035b, h035c, h035d, h035e⟩ | ⟨h035a, h035b, h035c, h035d, h035e⟩
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012b, h013c, h023c, h123b]
                      · linarith only [h012c, h013c, h123b]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012b, h013c, h023c, h123b]
                      · linarith only [h012c, h013c, h123b]
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012b, h013c, h023c, h123b]
                      · linarith only [h012c, h013c, h123b]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012b, h013c, h023c, h123b]
                      · linarith only [h012c, h013c, h123b]
                · rcases h035 with ⟨h035a, h035b, h035c, h035d, h035e⟩ | ⟨h035a, h035b, h035c, h035d, h035e⟩
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012b, h013c, h023c, h123b]
                      · linarith only [h012c, h013c, h123b]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012b, h013c, h023c, h123b]
                      · linarith only [h012c, h013c, h123b]
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012b, h013c, h023c, h123b]
                      · linarith only [h012c, h013c, h123b]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012b, h013c, h023c, h123b]
                      · linarith only [h012c, h013c, h123b]
      · rcases h015 with ⟨h015a, h015b, h015c, h015d, h015e⟩ | ⟨h015a, h015b, h015c, h015d, h015e⟩
        · rcases h023 with ⟨h023a, h023b, h023c, h023d, h023e⟩ | ⟨h023a, h023b, h023c, h023d, h023e⟩
          · rcases h024 with ⟨h024a, h024b, h024c, h024d, h024e⟩ | ⟨h024a, h024b, h024c, h024d, h024e⟩
            · rcases h025 with ⟨h025a, h025b, h025c, h025d, h025e⟩ | ⟨h025a, h025b, h025c, h025d, h025e⟩
              · rcases h034 with ⟨h034a, h034b, h034c, h034d, h034e⟩ | ⟨h034a, h034b, h034c, h034d, h034e⟩
                · rcases h035 with ⟨h035a, h035b, h035c, h035d, h035e⟩ | ⟨h035a, h035b, h035c, h035d, h035e⟩
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, h012c, h013c, h123d]
                      · linarith only [h012c, h013c, h123b]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, h012c, h013c, h123d]
                      · linarith only [h012c, h013c, h123b]
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, h012c, h013c, h123d]
                      · linarith only [h012c, h013c, h123b]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, h012c, h013c, h123d]
                      · linarith only [h012c, h013c, h123b]
                · rcases h035 with ⟨h035a, h035b, h035c, h035d, h035e⟩ | ⟨h035a, h035b, h035c, h035d, h035e⟩
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, h012c, h013c, h123d]
                      · linarith only [h012c, h013c, h123b]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, h012c, h013c, h123d]
                      · linarith only [h012c, h013c, h123b]
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, h012c, h013c, h123d]
                      · linarith only [h012c, h013c, h123b]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, h012c, h013c, h123d]
                      · linarith only [h012c, h013c, h123b]
              · rcases h034 with ⟨h034a, h034b, h034c, h034d, h034e⟩ | ⟨h034a, h034b, h034c, h034d, h034e⟩
                · rcases h035 with ⟨h035a, h035b, h035c, h035d, h035e⟩ | ⟨h035a, h035b, h035c, h035d, h035e⟩
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, h012c, h013c, h123d]
                      · linarith only [h012c, h013c, h123b]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, h012c, h013c, h123d]
                      · linarith only [h012c, h013c, h123b]
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, h012c, h013c, h123d]
                      · linarith only [h012c, h013c, h123b]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, h012c, h013c, h123d]
                      · linarith only [h012c, h013c, h123b]
                · rcases h035 with ⟨h035a, h035b, h035c, h035d, h035e⟩ | ⟨h035a, h035b, h035c, h035d, h035e⟩
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, h012c, h013c, h123d]
                      · linarith only [h012c, h013c, h123b]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, h012c, h013c, h123d]
                      · linarith only [h012c, h013c, h123b]
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, h012c, h013c, h123d]
                      · linarith only [h012c, h013c, h123b]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, h012c, h013c, h123d]
                      · linarith only [h012c, h013c, h123b]
            · rcases h025 with ⟨h025a, h025b, h025c, h025d, h025e⟩ | ⟨h025a, h025b, h025c, h025d, h025e⟩
              · rcases h034 with ⟨h034a, h034b, h034c, h034d, h034e⟩ | ⟨h034a, h034b, h034c, h034d, h034e⟩
                · rcases h035 with ⟨h035a, h035b, h035c, h035d, h035e⟩ | ⟨h035a, h035b, h035c, h035d, h035e⟩
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, h012c, h013c, h123d]
                      · linarith only [h012c, h013c, h123b]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, h012c, h013c, h123d]
                      · linarith only [h012c, h013c, h123b]
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, h012c, h013c, h123d]
                      · linarith only [h012c, h013c, h123b]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, h012c, h013c, h123d]
                      · linarith only [h012c, h013c, h123b]
                · rcases h035 with ⟨h035a, h035b, h035c, h035d, h035e⟩ | ⟨h035a, h035b, h035c, h035d, h035e⟩
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, h012c, h013c, h123d]
                      · linarith only [h012c, h013c, h123b]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, h012c, h013c, h123d]
                      · linarith only [h012c, h013c, h123b]
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, h012c, h013c, h123d]
                      · linarith only [h012c, h013c, h123b]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, h012c, h013c, h123d]
                      · linarith only [h012c, h013c, h123b]
              · rcases h034 with ⟨h034a, h034b, h034c, h034d, h034e⟩ | ⟨h034a, h034b, h034c, h034d, h034e⟩
                · rcases h035 with ⟨h035a, h035b, h035c, h035d, h035e⟩ | ⟨h035a, h035b, h035c, h035d, h035e⟩
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, h012c, h013c, h123d]
                      · linarith only [h012c, h013c, h123b]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, h012c, h013c, h123d]
                      · linarith only [h012c, h013c, h123b]
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, h012c, h013c, h123d]
                      · linarith only [h012c, h013c, h123b]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, h012c, h013c, h123d]
                      · linarith only [h012c, h013c, h123b]
                · rcases h035 with ⟨h035a, h035b, h035c, h035d, h035e⟩ | ⟨h035a, h035b, h035c, h035d, h035e⟩
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, h012c, h013c, h123d]
                      · linarith only [h012c, h013c, h123b]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, h012c, h013c, h123d]
                      · linarith only [h012c, h013c, h123b]
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, h012c, h013c, h123d]
                      · linarith only [h012c, h013c, h123b]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, h012c, h013c, h123d]
                      · linarith only [h012c, h013c, h123b]
          · rcases h024 with ⟨h024a, h024b, h024c, h024d, h024e⟩ | ⟨h024a, h024b, h024c, h024d, h024e⟩
            · rcases h025 with ⟨h025a, h025b, h025c, h025d, h025e⟩ | ⟨h025a, h025b, h025c, h025d, h025e⟩
              · rcases h034 with ⟨h034a, h034b, h034c, h034d, h034e⟩ | ⟨h034a, h034b, h034c, h034d, h034e⟩
                · rcases h035 with ⟨h035a, h035b, h035c, h035d, h035e⟩ | ⟨h035a, h035b, h035c, h035d, h035e⟩
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012b, h013c, h023c, h123b]
                      · linarith only [h012c, h013c, h123b]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012b, h013c, h023c, h123b]
                      · linarith only [h012c, h013c, h123b]
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012b, h013c, h023c, h123b]
                      · linarith only [h012c, h013c, h123b]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012b, h013c, h023c, h123b]
                      · linarith only [h012c, h013c, h123b]
                · rcases h035 with ⟨h035a, h035b, h035c, h035d, h035e⟩ | ⟨h035a, h035b, h035c, h035d, h035e⟩
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012b, h013c, h023c, h123b]
                      · linarith only [h012c, h013c, h123b]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012b, h013c, h023c, h123b]
                      · linarith only [h012c, h013c, h123b]
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012b, h013c, h023c, h123b]
                      · linarith only [h012c, h013c, h123b]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012b, h013c, h023c, h123b]
                      · linarith only [h012c, h013c, h123b]
              · rcases h034 with ⟨h034a, h034b, h034c, h034d, h034e⟩ | ⟨h034a, h034b, h034c, h034d, h034e⟩
                · rcases h035 with ⟨h035a, h035b, h035c, h035d, h035e⟩ | ⟨h035a, h035b, h035c, h035d, h035e⟩
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012b, h013c, h023c, h123b]
                      · linarith only [h012c, h013c, h123b]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012b, h013c, h023c, h123b]
                      · linarith only [h012c, h013c, h123b]
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012b, h013c, h023c, h123b]
                      · linarith only [h012c, h013c, h123b]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012b, h013c, h023c, h123b]
                      · linarith only [h012c, h013c, h123b]
                · rcases h035 with ⟨h035a, h035b, h035c, h035d, h035e⟩ | ⟨h035a, h035b, h035c, h035d, h035e⟩
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012b, h013c, h023c, h123b]
                      · linarith only [h012c, h013c, h123b]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012b, h013c, h023c, h123b]
                      · linarith only [h012c, h013c, h123b]
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012b, h013c, h023c, h123b]
                      · linarith only [h012c, h013c, h123b]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012b, h013c, h023c, h123b]
                      · linarith only [h012c, h013c, h123b]
            · rcases h025 with ⟨h025a, h025b, h025c, h025d, h025e⟩ | ⟨h025a, h025b, h025c, h025d, h025e⟩
              · rcases h034 with ⟨h034a, h034b, h034c, h034d, h034e⟩ | ⟨h034a, h034b, h034c, h034d, h034e⟩
                · rcases h035 with ⟨h035a, h035b, h035c, h035d, h035e⟩ | ⟨h035a, h035b, h035c, h035d, h035e⟩
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012b, h013c, h023c, h123b]
                      · linarith only [h012c, h013c, h123b]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012b, h013c, h023c, h123b]
                      · linarith only [h012c, h013c, h123b]
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012b, h013c, h023c, h123b]
                      · linarith only [h012c, h013c, h123b]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012b, h013c, h023c, h123b]
                      · linarith only [h012c, h013c, h123b]
                · rcases h035 with ⟨h035a, h035b, h035c, h035d, h035e⟩ | ⟨h035a, h035b, h035c, h035d, h035e⟩
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012b, h013c, h023c, h123b]
                      · linarith only [h012c, h013c, h123b]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012b, h013c, h023c, h123b]
                      · linarith only [h012c, h013c, h123b]
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012b, h013c, h023c, h123b]
                      · linarith only [h012c, h013c, h123b]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012b, h013c, h023c, h123b]
                      · linarith only [h012c, h013c, h123b]
              · rcases h034 with ⟨h034a, h034b, h034c, h034d, h034e⟩ | ⟨h034a, h034b, h034c, h034d, h034e⟩
                · rcases h035 with ⟨h035a, h035b, h035c, h035d, h035e⟩ | ⟨h035a, h035b, h035c, h035d, h035e⟩
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012b, h013c, h023c, h123b]
                      · linarith only [h012c, h013c, h123b]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012b, h013c, h023c, h123b]
                      · linarith only [h012c, h013c, h123b]
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012b, h013c, h023c, h123b]
                      · linarith only [h012c, h013c, h123b]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012b, h013c, h023c, h123b]
                      · linarith only [h012c, h013c, h123b]
                · rcases h035 with ⟨h035a, h035b, h035c, h035d, h035e⟩ | ⟨h035a, h035b, h035c, h035d, h035e⟩
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012b, h013c, h023c, h123b]
                      · linarith only [h012c, h013c, h123b]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012b, h013c, h023c, h123b]
                      · linarith only [h012c, h013c, h123b]
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012b, h013c, h023c, h123b]
                      · linarith only [h123b, h012c, h013c]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012b, h013c, h023c, h123b]
                      · linarith only [h012c, h013c, h123b]
        · rcases h023 with ⟨h023a, h023b, h023c, h023d, h023e⟩ | ⟨h023a, h023b, h023c, h023d, h023e⟩
          · rcases h024 with ⟨h024a, h024b, h024c, h024d, h024e⟩ | ⟨h024a, h024b, h024c, h024d, h024e⟩
            · rcases h025 with ⟨h025a, h025b, h025c, h025d, h025e⟩ | ⟨h025a, h025b, h025c, h025d, h025e⟩
              · rcases h034 with ⟨h034a, h034b, h034c, h034d, h034e⟩ | ⟨h034a, h034b, h034c, h034d, h034e⟩
                · rcases h035 with ⟨h035a, h035b, h035c, h035d, h035e⟩ | ⟨h035a, h035b, h035c, h035d, h035e⟩
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, h012c, h013c, h123d]
                      · linarith only [h012c, h013c, h123b]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, h012c, h013c, h123d]
                      · linarith only [h012c, h013c, h123b]
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, h012c, h013c, h123d]
                      · linarith only [h012c, h013c, h123b]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, h012c, h013c, h123d]
                      · linarith only [h012c, h013c, h123b]
                · rcases h035 with ⟨h035a, h035b, h035c, h035d, h035e⟩ | ⟨h035a, h035b, h035c, h035d, h035e⟩
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, h012c, h013c, h123d]
                      · linarith only [h012c, h013c, h123b]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, h012c, h013c, h123d]
                      · linarith only [h012c, h013c, h123b]
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, h012c, h013c, h123d]
                      · linarith only [h012c, h013c, h123b]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, h012c, h013c, h123d]
                      · linarith only [h012c, h013c, h123b]
              · rcases h034 with ⟨h034a, h034b, h034c, h034d, h034e⟩ | ⟨h034a, h034b, h034c, h034d, h034e⟩
                · rcases h035 with ⟨h035a, h035b, h035c, h035d, h035e⟩ | ⟨h035a, h035b, h035c, h035d, h035e⟩
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, h012c, h013c, h123d]
                      · linarith only [h012c, h013c, h123b]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, h012c, h013c, h123d]
                      · linarith only [h012c, h013c, h123b]
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, h012c, h013c, h123d]
                      · linarith only [h012c, h013c, h123b]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, h012c, h013c, h123d]
                      · linarith only [h012c, h013c, h123b]
                · rcases h035 with ⟨h035a, h035b, h035c, h035d, h035e⟩ | ⟨h035a, h035b, h035c, h035d, h035e⟩
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, h012c, h013c, h123d]
                      · linarith only [h012c, h013c, h123b]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, h012c, h013c, h123d]
                      · linarith only [h012c, h013c, h123b]
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, h012c, h013c, h123d]
                      · linarith only [h012c, h013c, h123b]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, h012c, h013c, h123d]
                      · linarith only [h012c, h013c, h123b]
            · rcases h025 with ⟨h025a, h025b, h025c, h025d, h025e⟩ | ⟨h025a, h025b, h025c, h025d, h025e⟩
              · rcases h034 with ⟨h034a, h034b, h034c, h034d, h034e⟩ | ⟨h034a, h034b, h034c, h034d, h034e⟩
                · rcases h035 with ⟨h035a, h035b, h035c, h035d, h035e⟩ | ⟨h035a, h035b, h035c, h035d, h035e⟩
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, h012c, h013c, h123d]
                      · linarith only [h012c, h013c, h123b]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, h012c, h013c, h123d]
                      · linarith only [h012c, h013c, h123b]
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, h012c, h013c, h123d]
                      · linarith only [h012c, h013c, h123b]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, h012c, h013c, h123d]
                      · linarith only [h012c, h013c, h123b]
                · rcases h035 with ⟨h035a, h035b, h035c, h035d, h035e⟩ | ⟨h035a, h035b, h035c, h035d, h035e⟩
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, h012c, h013c, h123d]
                      · linarith only [h012c, h013c, h123b]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, h012c, h013c, h123d]
                      · linarith only [h012c, h013c, h123b]
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, h012c, h013c, h123d]
                      · linarith only [h012c, h013c, h123b]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, h012c, h013c, h123d]
                      · linarith only [h012c, h013c, h123b]
              · rcases h034 with ⟨h034a, h034b, h034c, h034d, h034e⟩ | ⟨h034a, h034b, h034c, h034d, h034e⟩
                · rcases h035 with ⟨h035a, h035b, h035c, h035d, h035e⟩ | ⟨h035a, h035b, h035c, h035d, h035e⟩
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, h012c, h013c, h123d]
                      · linarith only [h012c, h013c, h123b]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, h012c, h013c, h123d]
                      · linarith only [h012c, h013c, h123b]
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, h012c, h013c, h123d]
                      · linarith only [h012c, h013c, h123b]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, h012c, h013c, h123d]
                      · linarith only [h012c, h013c, h123b]
                · rcases h035 with ⟨h035a, h035b, h035c, h035d, h035e⟩ | ⟨h035a, h035b, h035c, h035d, h035e⟩
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, h012c, h013c, h123d]
                      · linarith only [h012c, h013c, h123b]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, h012c, h013c, h123d]
                      · linarith only [h012c, h013c, h123b]
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, h012c, h013c, h123d]
                      · linarith only [h012c, h013c, h123b]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, h012c, h013c, h123d]
                      · linarith only [h012c, h013c, h123b]
          · rcases h024 with ⟨h024a, h024b, h024c, h024d, h024e⟩ | ⟨h024a, h024b, h024c, h024d, h024e⟩
            · rcases h025 with ⟨h025a, h025b, h025c, h025d, h025e⟩ | ⟨h025a, h025b, h025c, h025d, h025e⟩
              · rcases h034 with ⟨h034a, h034b, h034c, h034d, h034e⟩ | ⟨h034a, h034b, h034c, h034d, h034e⟩
                · rcases h035 with ⟨h035a, h035b, h035c, h035d, h035e⟩ | ⟨h035a, h035b, h035c, h035d, h035e⟩
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012b, h013c, h023c, h123b]
                      · linarith only [h012c, h013c, h123b]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012b, h013c, h023c, h123b]
                      · linarith only [h012c, h013c, h123b]
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012b, h013c, h023c, h123b]
                      · linarith only [h012c, h013c, h123b]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012b, h013c, h023c, h123b]
                      · linarith only [h012c, h013c, h123b]
                · rcases h035 with ⟨h035a, h035b, h035c, h035d, h035e⟩ | ⟨h035a, h035b, h035c, h035d, h035e⟩
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012b, h013c, h023c, h123b]
                      · linarith only [h012c, h013c, h123b]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012b, h013c, h023c, h123b]
                      · linarith only [h012c, h013c, h123b]
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012b, h013c, h023c, h123b]
                      · linarith only [h012c, h013c, h123b]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012b, h013c, h023c, h123b]
                      · linarith only [h012c, h013c, h123b]
              · rcases h034 with ⟨h034a, h034b, h034c, h034d, h034e⟩ | ⟨h034a, h034b, h034c, h034d, h034e⟩
                · rcases h035 with ⟨h035a, h035b, h035c, h035d, h035e⟩ | ⟨h035a, h035b, h035c, h035d, h035e⟩
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012b, h013c, h023c, h123b]
                      · linarith only [h012c, h013c, h123b]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012b, h013c, h023c, h123b]
                      · linarith only [h012c, h013c, h123b]
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012b, h013c, h023c, h123b]
                      · linarith only [h012c, h013c, h123b]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012b, h013c, h023c, h123b]
                      · linarith only [h012c, h013c, h123b]
                · rcases h035 with ⟨h035a, h035b, h035c, h035d, h035e⟩ | ⟨h035a, h035b, h035c, h035d, h035e⟩
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012b, h013c, h023c, h123b]
                      · linarith only [h012c, h013c, h123b]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012b, h013c, h023c, h123b]
                      · linarith only [h012c, h013c, h123b]
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012b, h013c, h023c, h123b]
                      · linarith only [h012c, h013c, h123b]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012b, h013c, h023c, h123b]
                      · linarith only [h012c, h013c, h123b]
            · rcases h025 with ⟨h025a, h025b, h025c, h025d, h025e⟩ | ⟨h025a, h025b, h025c, h025d, h025e⟩
              · rcases h034 with ⟨h034a, h034b, h034c, h034d, h034e⟩ | ⟨h034a, h034b, h034c, h034d, h034e⟩
                · rcases h035 with ⟨h035a, h035b, h035c, h035d, h035e⟩ | ⟨h035a, h035b, h035c, h035d, h035e⟩
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012b, h013c, h023c, h123b]
                      · linarith only [h012c, h013c, h123b]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012b, h013c, h023c, h123b]
                      · linarith only [h012c, h013c, h123b]
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012b, h013c, h023c, h123b]
                      · linarith only [h012c, h013c, h123b]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012b, h013c, h023c, h123b]
                      · linarith only [h012c, h013c, h123b]
                · rcases h035 with ⟨h035a, h035b, h035c, h035d, h035e⟩ | ⟨h035a, h035b, h035c, h035d, h035e⟩
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012b, h013c, h023c, h123b]
                      · linarith only [h012c, h013c, h123b]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012b, h013c, h023c, h123b]
                      · linarith only [h012c, h013c, h123b]
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012b, h013c, h023c, h123b]
                      · linarith only [h012c, h013c, h123b]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012b, h013c, h023c, h123b]
                      · linarith only [h012c, h013c, h123b]
              · rcases h034 with ⟨h034a, h034b, h034c, h034d, h034e⟩ | ⟨h034a, h034b, h034c, h034d, h034e⟩
                · rcases h035 with ⟨h035a, h035b, h035c, h035d, h035e⟩ | ⟨h035a, h035b, h035c, h035d, h035e⟩
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012b, h013c, h023c, h123b]
                      · linarith only [h012c, h013c, h123b]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012b, h013c, h023c, h123b]
                      · linarith only [h012c, h013c, h123b]
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012b, h013c, h023c, h123b]
                      · linarith only [h012c, h013c, h123b]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012b, h013c, h023c, h123b]
                      · linarith only [h012c, h013c, h123b]
                · rcases h035 with ⟨h035a, h035b, h035c, h035d, h035e⟩ | ⟨h035a, h035b, h035c, h035d, h035e⟩
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012b, h013c, h023c, h123b]
                      · linarith only [h012c, h013c, h123b]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012b, h013c, h023c, h123b]
                      · linarith only [h012c, h013c, h123b]
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012b, h013c, h023c, h123b]
                      · linarith only [h012c, h013c, h123b]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [h012b, h013c, h023c, h123b]
                      · linarith only [h012c, h013c, h123b]
    · rcases h014 with ⟨h014a, h014b, h014c, h014d, h014e⟩ | ⟨h014a, h014b, h014c, h014d, h014e⟩
      · rcases h015 with ⟨h015a, h015b, h015c, h015d, h015e⟩ | ⟨h015a, h015b, h015c, h015d, h015e⟩
        · rcases h023 with ⟨h023a, h023b, h023c, h023d, h023e⟩ | ⟨h023a, h023b, h023c, h023d, h023e⟩
          · rcases h024 with ⟨h024a, h024b, h024c, h024d, h024e⟩ | ⟨h024a, h024b, h024c, h024d, h024e⟩
            · rcases h025 with ⟨h025a, h025b, h025c, h025d, h025e⟩ | ⟨h025a, h025b, h025c, h025d, h025e⟩
              · rcases h034 with ⟨h034a, h034b, h034c, h034d, h034e⟩ | ⟨h034a, h034b, h034c, h034d, h034e⟩
                · rcases h035 with ⟨h035a, h035b, h035c, h035d, h035e⟩ | ⟨h035a, h035b, h035c, h035d, h035e⟩
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · rcases h124 with ⟨h124a, h124b, h124c, h124d, h124e⟩ | ⟨h124a, h124b, h124c, h124d, h124e⟩
                        · linarith only [ht, h012c, h014c, h124d]
                        · linarith only [h012c, h014c, h124b]
                      · linarith only [ht, r02.1, r14.2, h014c, h013c, h023c, h123a]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · rcases h124 with ⟨h124a, h124b, h124c, h124d, h124e⟩ | ⟨h124a, h124b, h124c, h124d, h124e⟩
                        · linarith only [ht, h012c, h014c, h124d]
                        · linarith only [h012c, h014c, h124b]
                      · linarith only [ht, r02.1, r14.2, h014c, h013c, h023c, h123a]
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · rcases h124 with ⟨h124a, h124b, h124c, h124d, h124e⟩ | ⟨h124a, h124b, h124c, h124d, h124e⟩
                        · linarith only [ht, h012c, h014c, h124d]
                        · linarith only [h012c, h014c, h124b]
                      · linarith only [ht, r02.1, r14.2, h014c, h013c, h023c, h123a]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · rcases h124 with ⟨h124a, h124b, h124c, h124d, h124e⟩ | ⟨h124a, h124b, h124c, h124d, h124e⟩
                        · linarith only [ht, h012c, h014c, h124d]
                        · linarith only [h012c, h014c, h124b]
                      · linarith only [ht, r02.1, r14.2, h014c, h013c, h023c, h123a]
                · rcases h035 with ⟨h035a, h035b, h035c, h035d, h035e⟩ | ⟨h035a, h035b, h035c, h035d, h035e⟩
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · rcases h124 with ⟨h124a, h124b, h124c, h124d, h124e⟩ | ⟨h124a, h124b, h124c, h124d, h124e⟩
                        · linarith only [ht, h012c, h014c, h124d]
                        · linarith only [h012c, h014c, h124b]
                      · linarith only [ht, r02.1, r14.2, h014c, h013c, h023c, h123a]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · rcases h124 with ⟨h124a, h124b, h124c, h124d, h124e⟩ | ⟨h124a, h124b, h124c, h124d, h124e⟩
                        · linarith only [ht, h012c, h014c, h124d]
                        · linarith only [h012c, h014c, h124b]
                      · linarith only [ht, r02.1, r14.2, h014c, h013c, h023c, h123a]
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · rcases h124 with ⟨h124a, h124b, h124c, h124d, h124e⟩ | ⟨h124a, h124b, h124c, h124d, h124e⟩
                        · linarith only [ht, h012c, h014c, h124d]
                        · linarith only [h012c, h014c, h124b]
                      · linarith only [ht, r02.1, r14.2, h014c, h013c, h023c, h123a]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · rcases h124 with ⟨h124a, h124b, h124c, h124d, h124e⟩ | ⟨h124a, h124b, h124c, h124d, h124e⟩
                        · linarith only [ht, h012c, h014c, h124d]
                        · linarith only [h012c, h014c, h124b]
                      · linarith only [ht, r02.1, r14.2, h014c, h013c, h023c, h123a]
              · rcases h034 with ⟨h034a, h034b, h034c, h034d, h034e⟩ | ⟨h034a, h034b, h034c, h034d, h034e⟩
                · rcases h035 with ⟨h035a, h035b, h035c, h035d, h035e⟩ | ⟨h035a, h035b, h035c, h035d, h035e⟩
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, h013c, h015a, h023c, h025b, h123e]
                      · linarith only [h013c, h015a, h023c, h025b, h123a]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, h013c, h015a, h023c, h025b, h123e]
                      · linarith only [h013c, h015a, h023c, h025b, h123a]
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, h013c, h015a, h023c, h025b, h123e]
                      · linarith only [h013c, h015a, h023c, h025b, h123a]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, h013c, h015a, h023c, h025b, h123e]
                      · linarith only [h013c, h015a, h023c, h025b, h123a]
                · rcases h035 with ⟨h035a, h035b, h035c, h035d, h035e⟩ | ⟨h035a, h035b, h035c, h035d, h035e⟩
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, h013c, h015a, h023c, h025b, h123e]
                      · linarith only [h013c, h015a, h023c, h025b, h123a]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, h013c, h015a, h023c, h025b, h123e]
                      · linarith only [h013c, h015a, h023c, h025b, h123a]
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, h013c, h015a, h023c, h025b, h123e]
                      · linarith only [h013c, h015a, h023c, h025b, h123a]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, h013c, h015a, h023c, h025b, h123e]
                      · linarith only [h013c, h015a, h023c, h025b, h123a]
            · rcases h025 with ⟨h025a, h025b, h025c, h025d, h025e⟩ | ⟨h025a, h025b, h025c, h025d, h025e⟩
              · rcases h034 with ⟨h034a, h034b, h034c, h034d, h034e⟩ | ⟨h034a, h034b, h034c, h034d, h034e⟩
                · rcases h035 with ⟨h035a, h035b, h035c, h035d, h035e⟩ | ⟨h035a, h035b, h035c, h035d, h035e⟩
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, h014a, h013c, h023c, h024b, h123e]
                      · linarith only [h014a, h013c, h023c, h123a, h024b]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, h014a, h013c, h023c, h123e, h024b]
                      · linarith only [h014a, h013c, h023c, h024b, h123a]
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, h014a, h013c, h023c, h123e, h024b]
                      · linarith only [h014a, h013c, h023c, h123a, h024b]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, h014a, h013c, h023c, h024b, h123e]
                      · linarith only [h014a, h013c, h023c, h024b, h123a]
                · rcases h035 with ⟨h035a, h035b, h035c, h035d, h035e⟩ | ⟨h035a, h035b, h035c, h035d, h035e⟩
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, h014a, h013c, h023c, h123e, h024b]
                      · linarith only [h014a, h013c, h023c, h123a, h024b]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, h014a, h013c, h023c, h123e, h024b]
                      · linarith only [h014a, h013c, h023c, h123a, h024b]
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, h014a, h013c, h023c, h024b, h123e]
                      · linarith only [h014a, h013c, h023c, h123a, h024b]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, h014a, h013c, h023c, h123e, h024b]
                      · linarith only [h014a, h013c, h023c, h123a, h024b]
              · rcases h034 with ⟨h034a, h034b, h034c, h034d, h034e⟩ | ⟨h034a, h034b, h034c, h034d, h034e⟩
                · rcases h035 with ⟨h035a, h035b, h035c, h035d, h035e⟩ | ⟨h035a, h035b, h035c, h035d, h035e⟩
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, h014a, h013c, h023c, h123e, h024b]
                      · linarith only [h014a, h013c, h023c, h123a, h024b]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, h014a, h013c, h023c, h123e, h024b]
                      · linarith only [h014a, h013c, h023c, h123a, h024b]
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, h014a, h013c, h023c, h123e, h024b]
                      · linarith only [h014a, h013c, h023c, h024b, h123a]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, h014a, h013c, h023c, h123e, h024b]
                      · linarith only [h014a, h013c, h023c, h123a, h024b]
                · rcases h035 with ⟨h035a, h035b, h035c, h035d, h035e⟩ | ⟨h035a, h035b, h035c, h035d, h035e⟩
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, h014a, h013c, h023c, h123e, h024b]
                      · linarith only [h014a, h013c, h023c, h123a, h024b]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, h014a, h013c, h023c, h123e, h024b]
                      · linarith only [h014a, h013c, h023c, h123a, h024b]
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, h014a, h013c, h023c, h123e, h024b]
                      · linarith only [h014a, h013c, h023c, h123a, h024b]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, h014a, h013c, h023c, h123e, h024b]
                      · linarith only [h014a, h013c, h023c, h123a, h024b]
          · rcases h024 with ⟨h024a, h024b, h024c, h024d, h024e⟩ | ⟨h024a, h024b, h024c, h024d, h024e⟩
            · rcases h025 with ⟨h025a, h025b, h025c, h025d, h025e⟩ | ⟨h025a, h025b, h025c, h025d, h025e⟩
              · rcases h034 with ⟨h034a, h034b, h034c, h034d, h034e⟩ | ⟨h034a, h034b, h034c, h034d, h034e⟩
                · rcases h035 with ⟨h035a, h035b, h035c, h035d, h035e⟩ | ⟨h035a, h035b, h035c, h035d, h035e⟩
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, r12.1, r24.2, h024c, h023c, h123c]
                      · linarith only [ht, r14.2, r23.1, h012c, h014c, h123c]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, r12.1, r24.2, h123c, h024c, h023c]
                      · linarith only [ht, r14.2, r23.1, h012c, h014c, h123c]
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, r12.1, r24.2, h024c, h123c, h023c]
                      · linarith only [ht, r14.2, r23.1, h012c, h014c, h123c]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, r12.1, r24.2, h024c, h023c, h123c]
                      · linarith only [ht, r14.2, r23.1, h012c, h014c, h123c]
                · rcases h035 with ⟨h035a, h035b, h035c, h035d, h035e⟩ | ⟨h035a, h035b, h035c, h035d, h035e⟩
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, r12.1, r24.2, h024c, h023c, h123c]
                      · linarith only [ht, r14.2, r23.1, h012c, h014c, h123c]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, r12.1, r24.2, h024c, h023c, h123c]
                      · linarith only [ht, r14.2, r23.1, h012c, h014c, h123c]
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, r12.1, r24.2, h024c, h023c, h123c]
                      · linarith only [ht, r14.2, r23.1, h012c, h014c, h123c]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, r12.1, r24.2, h024c, h123c, h023c]
                      · linarith only [ht, r14.2, r23.1, h012c, h014c, h123c]
              · rcases h034 with ⟨h034a, h034b, h034c, h034d, h034e⟩ | ⟨h034a, h034b, h034c, h034d, h034e⟩
                · rcases h035 with ⟨h035a, h035b, h035c, h035d, h035e⟩ | ⟨h035a, h035b, h035c, h035d, h035e⟩
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, r12.1, r24.2, h123c, h024c, h023c]
                      · linarith only [ht, r14.2, r23.1, h012c, h014c, h123c]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, r12.1, r24.2, h024c, h123c, h023c]
                      · linarith only [ht, r14.2, r23.1, h012c, h014c, h123c]
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, r12.1, r24.2, h024c, h023c, h123c]
                      · linarith only [ht, r14.2, r23.1, h012c, h014c, h123c]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, r12.1, r24.2, h123c, h024c, h023c]
                      · linarith only [ht, r14.2, r23.1, h012c, h014c, h123c]
                · rcases h035 with ⟨h035a, h035b, h035c, h035d, h035e⟩ | ⟨h035a, h035b, h035c, h035d, h035e⟩
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, r12.1, r24.2, h024c, h023c, h123c]
                      · linarith only [ht, r14.2, r23.1, h012c, h014c, h123c]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, r12.1, r24.2, h024c, h023c, h123c]
                      · linarith only [ht, r14.2, r23.1, h012c, h014c, h123c]
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, r12.1, r24.2, h024c, h023c, h123c]
                      · linarith only [ht, r14.2, r23.1, h012c, h014c, h123c]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, r12.1, r24.2, h024c, h123c, h023c]
                      · linarith only [ht, r14.2, r23.1, h012c, h014c, h123c]
            · rcases h025 with ⟨h025a, h025b, h025c, h025d, h025e⟩ | ⟨h025a, h025b, h025c, h025d, h025e⟩
              · rcases h034 with ⟨h034a, h034b, h034c, h034d, h034e⟩ | ⟨h034a, h034b, h034c, h034d, h034e⟩
                · rcases h035 with ⟨h035a, h035b, h035c, h035d, h035e⟩ | ⟨h035a, h035b, h035c, h035d, h035e⟩
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, r12.1, r25.2, h123c, h023c, h025c]
                      · linarith only [ht, r14.2, r23.1, h012c, h014c, h123c]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, r12.1, r25.2, h123c, h023c, h025c]
                      · linarith only [ht, r14.2, r23.1, h012c, h014c, h123c]
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, r12.1, r25.2, h023c, h123c, h025c]
                      · linarith only [ht, r14.2, r23.1, h012c, h014c, h123c]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, r12.1, r25.2, h023c, h123c, h025c]
                      · linarith only [ht, r14.2, r23.1, h012c, h014c, h123c]
                · rcases h035 with ⟨h035a, h035b, h035c, h035d, h035e⟩ | ⟨h035a, h035b, h035c, h035d, h035e⟩
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, r12.1, r25.2, h023c, h025c, h123c]
                      · linarith only [ht, r14.2, r23.1, h012c, h014c, h123c]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, r12.1, r25.2, h023c, h123c, h025c]
                      · linarith only [ht, r14.2, r23.1, h012c, h014c, h123c]
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, r12.1, r25.2, h023c, h123c, h025c]
                      · linarith only [ht, r14.2, r23.1, h012c, h014c, h123c]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, r12.1, r25.2, h023c, h123c, h025c]
                      · linarith only [ht, r14.2, r23.1, h012c, h014c, h123c]
              · rcases h034 with ⟨h034a, h034b, h034c, h034d, h034e⟩ | ⟨h034a, h034b, h034c, h034d, h034e⟩
                · rcases h035 with ⟨h035a, h035b, h035c, h035d, h035e⟩ | ⟨h035a, h035b, h035c, h035d, h035e⟩
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, r12.1, r14.2, h012b, h014c, h023c, h123c]
                      · linarith only [ht, r14.2, r23.1, h012c, h014c, h123c]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, r12.1, r14.2, h012b, h014c, h123c, h023c]
                      · linarith only [ht, r14.2, r23.1, h012c, h014c, h123c]
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, r12.1, r14.2, h012b, h014c, h023c, h123c]
                      · linarith only [ht, r14.2, r23.1, h012c, h014c, h123c]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, r12.1, r14.2, h012b, h014c, h023c, h123c]
                      · linarith only [ht, r14.2, r23.1, h012c, h014c, h123c]
                · rcases h035 with ⟨h035a, h035b, h035c, h035d, h035e⟩ | ⟨h035a, h035b, h035c, h035d, h035e⟩
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, r12.1, r14.2, h012b, h014c, h023c, h123c]
                      · linarith only [ht, r14.2, r23.1, h012c, h014c, h123c]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, r12.1, r14.2, h012b, h014c, h023c, h123c]
                      · linarith only [ht, r14.2, r23.1, h012c, h014c, h123c]
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, r12.1, r14.2, h012b, h014c, h023c, h123c]
                      · linarith only [ht, r14.2, r23.1, h012c, h014c, h123c]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, r12.1, r14.2, h012b, h014c, h023c, h123c]
                      · linarith only [ht, r14.2, r23.1, h012c, h014c, h123c]
        · rcases h023 with ⟨h023a, h023b, h023c, h023d, h023e⟩ | ⟨h023a, h023b, h023c, h023d, h023e⟩
          · rcases h024 with ⟨h024a, h024b, h024c, h024d, h024e⟩ | ⟨h024a, h024b, h024c, h024d, h024e⟩
            · rcases h025 with ⟨h025a, h025b, h025c, h025d, h025e⟩ | ⟨h025a, h025b, h025c, h025d, h025e⟩
              · rcases h034 with ⟨h034a, h034b, h034c, h034d, h034e⟩ | ⟨h034a, h034b, h034c, h034d, h034e⟩
                · rcases h035 with ⟨h035a, h035b, h035c, h035d, h035e⟩ | ⟨h035a, h035b, h035c, h035d, h035e⟩
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · rcases h124 with ⟨h124a, h124b, h124c, h124d, h124e⟩ | ⟨h124a, h124b, h124c, h124d, h124e⟩
                        · linarith only [ht, h012c, h014c, h124d]
                        · linarith only [h012c, h014c, h124b]
                      · linarith only [ht, r02.1, r14.2, h014c, h013c, h023c, h123a]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · rcases h124 with ⟨h124a, h124b, h124c, h124d, h124e⟩ | ⟨h124a, h124b, h124c, h124d, h124e⟩
                        · linarith only [ht, h012c, h014c, h124d]
                        · linarith only [h012c, h014c, h124b]
                      · linarith only [ht, r02.1, r14.2, h014c, h013c, h023c, h123a]
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · rcases h124 with ⟨h124a, h124b, h124c, h124d, h124e⟩ | ⟨h124a, h124b, h124c, h124d, h124e⟩
                        · linarith only [ht, h012c, h014c, h124d]
                        · linarith only [h012c, h014c, h124b]
                      · linarith only [ht, r02.1, r14.2, h014c, h013c, h023c, h123a]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · rcases h124 with ⟨h124a, h124b, h124c, h124d, h124e⟩ | ⟨h124a, h124b, h124c, h124d, h124e⟩
                        · linarith only [ht, h012c, h014c, h124d]
                        · linarith only [h012c, h014c, h124b]
                      · linarith only [ht, r02.1, r14.2, h014c, h013c, h023c, h123a]
                · rcases h035 with ⟨h035a, h035b, h035c, h035d, h035e⟩ | ⟨h035a, h035b, h035c, h035d, h035e⟩
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · rcases h124 with ⟨h124a, h124b, h124c, h124d, h124e⟩ | ⟨h124a, h124b, h124c, h124d, h124e⟩
                        · linarith only [ht, h012c, h014c, h124d]
                        · linarith only [h012c, h014c, h124b]
                      · linarith only [ht, r02.1, r14.2, h014c, h013c, h023c, h123a]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · rcases h124 with ⟨h124a, h124b, h124c, h124d, h124e⟩ | ⟨h124a, h124b, h124c, h124d, h124e⟩
                        · linarith only [ht, h012c, h014c, h124d]
                        · linarith only [h012c, h014c, h124b]
                      · linarith only [ht, r02.1, r14.2, h014c, h013c, h023c, h123a]
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · rcases h124 with ⟨h124a, h124b, h124c, h124d, h124e⟩ | ⟨h124a, h124b, h124c, h124d, h124e⟩
                        · linarith only [ht, h012c, h014c, h124d]
                        · linarith only [h012c, h014c, h124b]
                      · linarith only [ht, r02.1, r14.2, h014c, h013c, h023c, h123a]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · rcases h124 with ⟨h124a, h124b, h124c, h124d, h124e⟩ | ⟨h124a, h124b, h124c, h124d, h124e⟩
                        · linarith only [ht, h012c, h014c, h124d]
                        · linarith only [h012c, h014c, h124b]
                      · linarith only [ht, r02.1, r14.2, h014c, h013c, h023c, h123a]
              · rcases h034 with ⟨h034a, h034b, h034c, h034d, h034e⟩ | ⟨h034a, h034b, h034c, h034d, h034e⟩
                · rcases h035 with ⟨h035a, h035b, h035c, h035d, h035e⟩ | ⟨h035a, h035b, h035c, h035d, h035e⟩
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, h014a, h013c, h023c, h045a, h025b, h123e]
                      · linarith only [h014a, h013c, h023c, h045a, h025b, h123a]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · rcases h124 with ⟨h124a, h124b, h124c, h124d, h124e⟩ | ⟨h124a, h124b, h124c, h124d, h124e⟩
                        · linarith only [ht, h012c, h014c, h124d]
                        · linarith only [h012c, h014c, h124b]
                      · linarith only [ht, r01.2, r25.1, h013c, h023c, h123a, h025c]
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, h014a, h013c, h023c, h025b, h045a, h123e]
                      · linarith only [h014a, h013c, h023c, h025b, h045a, h123a]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · rcases h124 with ⟨h124a, h124b, h124c, h124d, h124e⟩ | ⟨h124a, h124b, h124c, h124d, h124e⟩
                        · linarith only [ht, h012c, h014c, h124d]
                        · linarith only [h012c, h014c, h124b]
                      · linarith only [ht, r02.1, r14.2, h014c, h013c, h023c, h123a]
                · rcases h035 with ⟨h035a, h035b, h035c, h035d, h035e⟩ | ⟨h035a, h035b, h035c, h035d, h035e⟩
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, h014a, h013c, h023c, h123e, h025b, h034b, h035a]
                      · linarith only [h014a, h013c, h023c, h025b, h034b, h123a, h035a]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, h014a, h013c, h023c, h123e, h025b, h034b, h035a]
                      · linarith only [h014a, h013c, h023c, h025b, h034b, h035a, h123a]
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, h014a, h013c, h023c, h045a, h025b, h123e]
                      · linarith only [h014a, h013c, h023c, h045a, h025b, h123a]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · rcases h124 with ⟨h124a, h124b, h124c, h124d, h124e⟩ | ⟨h124a, h124b, h124c, h124d, h124e⟩
                        · linarith only [ht, h012c, h014c, h124d]
                        · linarith only [h012c, h014c, h124b]
                      · linarith only [ht, r02.1, r14.2, h014c, h013c, h023c, h123a]
            · rcases h025 with ⟨h025a, h025b, h025c, h025d, h025e⟩ | ⟨h025a, h025b, h025c, h025d, h025e⟩
              · rcases h034 with ⟨h034a, h034b, h034c, h034d, h034e⟩ | ⟨h034a, h034b, h034c, h034d, h034e⟩
                · rcases h035 with ⟨h035a, h035b, h035c, h035d, h035e⟩ | ⟨h035a, h035b, h035c, h035d, h035e⟩
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, h014a, h013c, h024b, h023c, h123e]
                      · linarith only [h014a, h013c, h024b, h023c, h123a]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, h014a, h013c, h024b, h023c, h123e]
                      · linarith only [h014a, h013c, h024b, h023c, h123a]
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, h014a, h013c, h024b, h023c, h123e]
                      · linarith only [h014a, h013c, h024b, h023c, h123a]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, h014a, h013c, h024b, h023c, h123e]
                      · linarith only [h014a, h013c, h024b, h023c, h123a]
                · rcases h035 with ⟨h035a, h035b, h035c, h035d, h035e⟩ | ⟨h035a, h035b, h035c, h035d, h035e⟩
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, h014a, h013c, h024b, h023c, h123e]
                      · linarith only [h014a, h013c, h024b, h023c, h123a]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, h014a, h013c, h024b, h023c, h123e]
                      · linarith only [h014a, h013c, h024b, h023c, h123a]
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, h014a, h013c, h024b, h023c, h123e]
                      · linarith only [h014a, h013c, h024b, h023c, h123a]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, h014a, h013c, h024b, h023c, h123e]
                      · linarith only [h014a, h013c, h024b, h023c, h123a]
              · rcases h034 with ⟨h034a, h034b, h034c, h034d, h034e⟩ | ⟨h034a, h034b, h034c, h034d, h034e⟩
                · rcases h035 with ⟨h035a, h035b, h035c, h035d, h035e⟩ | ⟨h035a, h035b, h035c, h035d, h035e⟩
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, h014a, h013c, h024b, h023c, h123e]
                      · linarith only [h014a, h013c, h024b, h023c, h123a]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, h014a, h013c, h024b, h023c, h123e]
                      · linarith only [h014a, h013c, h024b, h023c, h123a]
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, h014a, h013c, h024b, h023c, h123e]
                      · linarith only [h014a, h013c, h024b, h023c, h123a]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, h014a, h013c, h024b, h023c, h123e]
                      · linarith only [h014a, h013c, h024b, h023c, h123a]
                · rcases h035 with ⟨h035a, h035b, h035c, h035d, h035e⟩ | ⟨h035a, h035b, h035c, h035d, h035e⟩
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, h014a, h013c, h024b, h023c, h123e]
                      · linarith only [h014a, h013c, h024b, h023c, h123a]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, h014a, h013c, h024b, h023c, h123e]
                      · linarith only [h014a, h013c, h024b, h023c, h123a]
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, h014a, h013c, h024b, h023c, h123e]
                      · linarith only [h014a, h013c, h024b, h023c, h123a]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, h014a, h013c, h024b, h023c, h123e]
                      · linarith only [h014a, h013c, h024b, h023c, h123a]
          · rcases h024 with ⟨h024a, h024b, h024c, h024d, h024e⟩ | ⟨h024a, h024b, h024c, h024d, h024e⟩
            · rcases h025 with ⟨h025a, h025b, h025c, h025d, h025e⟩ | ⟨h025a, h025b, h025c, h025d, h025e⟩
              · rcases h034 with ⟨h034a, h034b, h034c, h034d, h034e⟩ | ⟨h034a, h034b, h034c, h034d, h034e⟩
                · rcases h035 with ⟨h035a, h035b, h035c, h035d, h035e⟩ | ⟨h035a, h035b, h035c, h035d, h035e⟩
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, r12.1, r24.2, h123c, h023c, h024c]
                      · linarith only [ht, r14.2, r23.1, h012c, h014c, h123c]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, r12.1, r14.2, h012b, h014c, h023c, h123c]
                      · linarith only [ht, r14.2, r23.1, h012c, h014c, h123c]
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, r12.1, r14.2, h012b, h014c, h123c, h023c]
                      · linarith only [ht, r14.2, r23.1, h012c, h014c, h123c]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, r12.1, r14.2, h012b, h014c, h023c, h123c]
                      · linarith only [ht, r14.2, r23.1, h012c, h014c, h123c]
                · rcases h035 with ⟨h035a, h035b, h035c, h035d, h035e⟩ | ⟨h035a, h035b, h035c, h035d, h035e⟩
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, r12.1, r14.2, h012b, h014c, h023c, h123c]
                      · linarith only [ht, r14.2, r23.1, h012c, h014c, h123c]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, r12.1, r14.2, h012b, h014c, h123c, h023c]
                      · linarith only [ht, r14.2, r23.1, h012c, h014c, h123c]
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, r12.1, r14.2, h012b, h014c, h123c, h023c]
                      · linarith only [ht, r14.2, r23.1, h012c, h014c, h123c]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, r12.1, r14.2, h012b, h014c, h023c, h123c]
                      · linarith only [ht, r14.2, r23.1, h012c, h014c, h123c]
              · rcases h034 with ⟨h034a, h034b, h034c, h034d, h034e⟩ | ⟨h034a, h034b, h034c, h034d, h034e⟩
                · rcases h035 with ⟨h035a, h035b, h035c, h035d, h035e⟩ | ⟨h035a, h035b, h035c, h035d, h035e⟩
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, r12.1, r14.2, h012b, h014c, h023c, h123c]
                      · linarith only [ht, r14.2, r23.1, h012c, h014c, h123c]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, r12.1, r14.2, h012b, h014c, h023c, h123c]
                      · linarith only [ht, r14.2, r23.1, h012c, h014c, h123c]
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, r12.1, r14.2, h012b, h014c, h123c, h023c]
                      · linarith only [ht, r14.2, r23.1, h012c, h014c, h123c]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, r12.1, r14.2, h012b, h014c, h023c, h123c]
                      · linarith only [ht, r14.2, r23.1, h012c, h014c, h123c]
                · rcases h035 with ⟨h035a, h035b, h035c, h035d, h035e⟩ | ⟨h035a, h035b, h035c, h035d, h035e⟩
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, r12.1, r14.2, h012b, h014c, h023c, h123c]
                      · linarith only [ht, r14.2, r23.1, h012c, h014c, h123c]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, r12.1, r14.2, h012b, h014c, h123c, h023c]
                      · linarith only [ht, r14.2, r23.1, h012c, h014c, h123c]
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, r12.1, r14.2, h012b, h014c, h023c, h123c]
                      · linarith only [ht, r14.2, r23.1, h012c, h014c, h123c]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, r12.1, r14.2, h012b, h014c, h023c, h123c]
                      · linarith only [ht, r14.2, r23.1, h012c, h014c, h123c]
            · rcases h025 with ⟨h025a, h025b, h025c, h025d, h025e⟩ | ⟨h025a, h025b, h025c, h025d, h025e⟩
              · rcases h034 with ⟨h034a, h034b, h034c, h034d, h034e⟩ | ⟨h034a, h034b, h034c, h034d, h034e⟩
                · rcases h035 with ⟨h035a, h035b, h035c, h035d, h035e⟩ | ⟨h035a, h035b, h035c, h035d, h035e⟩
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, r12.1, r14.2, h012b, h014c, h023c, h123c]
                      · linarith only [ht, r14.2, r23.1, h012c, h014c, h123c]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, r12.1, r14.2, h012b, h014c, h023c, h123c]
                      · linarith only [ht, r14.2, r23.1, h012c, h014c, h123c]
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, r12.1, r14.2, h012b, h014c, h023c, h123c]
                      · linarith only [ht, r14.2, r23.1, h012c, h014c, h123c]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, r12.1, r14.2, h012b, h014c, h123c, h023c]
                      · linarith only [ht, r14.2, r23.1, h012c, h014c, h123c]
                · rcases h035 with ⟨h035a, h035b, h035c, h035d, h035e⟩ | ⟨h035a, h035b, h035c, h035d, h035e⟩
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, r12.1, r14.2, h012b, h014c, h023c, h123c]
                      · linarith only [ht, r14.2, r23.1, h012c, h014c, h123c]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, r12.1, r14.2, h012b, h014c, h123c, h023c]
                      · linarith only [ht, r14.2, r23.1, h012c, h014c, h123c]
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, r12.1, r14.2, h012b, h014c, h023c, h123c]
                      · linarith only [ht, r14.2, r23.1, h012c, h014c, h123c]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, r12.1, r14.2, h012b, h014c, h023c, h123c]
                      · linarith only [ht, r14.2, r23.1, h012c, h014c, h123c]
              · rcases h034 with ⟨h034a, h034b, h034c, h034d, h034e⟩ | ⟨h034a, h034b, h034c, h034d, h034e⟩
                · rcases h035 with ⟨h035a, h035b, h035c, h035d, h035e⟩ | ⟨h035a, h035b, h035c, h035d, h035e⟩
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, r12.1, r14.2, h012b, h014c, h023c, h123c]
                      · linarith only [ht, r14.2, r23.1, h012c, h014c, h123c]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, r12.1, r14.2, h012b, h014c, h123c, h023c]
                      · linarith only [ht, r14.2, r23.1, h012c, h014c, h123c]
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, r12.1, r14.2, h012b, h014c, h023c, h123c]
                      · linarith only [ht, r14.2, r23.1, h012c, h014c, h123c]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, r12.1, r14.2, h012b, h014c, h023c, h123c]
                      · linarith only [ht, r14.2, r23.1, h012c, h014c, h123c]
                · rcases h035 with ⟨h035a, h035b, h035c, h035d, h035e⟩ | ⟨h035a, h035b, h035c, h035d, h035e⟩
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, r12.1, r14.2, h012b, h014c, h123c, h023c]
                      · linarith only [ht, r14.2, r23.1, h012c, h014c, h123c]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, r12.1, r14.2, h012b, h014c, h123c, h023c]
                      · linarith only [ht, r14.2, r23.1, h012c, h014c, h123c]
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, r12.1, r14.2, h012b, h014c, h023c, h123c]
                      · linarith only [ht, r14.2, r23.1, h012c, h014c, h123c]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, r12.1, r14.2, h012b, h014c, h023c, h123c]
                      · linarith only [ht, r14.2, r23.1, h012c, h014c, h123c]
      · rcases h015 with ⟨h015a, h015b, h015c, h015d, h015e⟩ | ⟨h015a, h015b, h015c, h015d, h015e⟩
        · rcases h023 with ⟨h023a, h023b, h023c, h023d, h023e⟩ | ⟨h023a, h023b, h023c, h023d, h023e⟩
          · rcases h024 with ⟨h024a, h024b, h024c, h024d, h024e⟩ | ⟨h024a, h024b, h024c, h024d, h024e⟩
            · rcases h025 with ⟨h025a, h025b, h025c, h025d, h025e⟩ | ⟨h025a, h025b, h025c, h025d, h025e⟩
              · rcases h034 with ⟨h034a, h034b, h034c, h034d, h034e⟩ | ⟨h034a, h034b, h034c, h034d, h034e⟩
                · rcases h035 with ⟨h035a, h035b, h035c, h035d, h035e⟩ | ⟨h035a, h035b, h035c, h035d, h035e⟩
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · rcases h124 with ⟨h124a, h124b, h124c, h124d, h124e⟩ | ⟨h124a, h124b, h124c, h124d, h124e⟩
                        · rcases h125 with ⟨h125a, h125b, h125c, h125d, h125e⟩ | ⟨h125a, h125b, h125c, h125d, h125e⟩
                          · linarith only [ht, h012c, h015c, h125d]
                          · linarith only [h012c, h015c, h125b]
                        · linarith only [ht, r02.1, r15.2, h014c, h015c, h024c, h124a]
                      · linarith only [ht, r02.1, r15.2, h013c, h015c, h023c, h123a]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · rcases h124 with ⟨h124a, h124b, h124c, h124d, h124e⟩ | ⟨h124a, h124b, h124c, h124d, h124e⟩
                        · rcases h125 with ⟨h125a, h125b, h125c, h125d, h125e⟩ | ⟨h125a, h125b, h125c, h125d, h125e⟩
                          · linarith only [ht, h012c, h015c, h125d]
                          · linarith only [ht, r14.1, r23.2, h012a, h014c, h015c, h023c, h125b]
                        · linarith only [ht, r02.1, r15.2, h014c, h015c, h024c, h124a]
                      · linarith only [ht, r02.1, r15.2, h013c, h015c, h023c, h123a]
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · rcases h124 with ⟨h124a, h124b, h124c, h124d, h124e⟩ | ⟨h124a, h124b, h124c, h124d, h124e⟩
                        · rcases h125 with ⟨h125a, h125b, h125c, h125d, h125e⟩ | ⟨h125a, h125b, h125c, h125d, h125e⟩
                          · linarith only [ht, h012c, h015c, h125d]
                          · linarith only [h012c, h015c, h125b]
                        · linarith only [ht, r02.1, r15.2, h014c, h015c, h024c, h124a]
                      · linarith only [ht, r15.2, h123a, r35.1, h013c, h015c, h023b, h035c]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · rcases h124 with ⟨h124a, h124b, h124c, h124d, h124e⟩ | ⟨h124a, h124b, h124c, h124d, h124e⟩
                        · rcases h125 with ⟨h125a, h125b, h125c, h125d, h125e⟩ | ⟨h125a, h125b, h125c, h125d, h125e⟩
                          · linarith only [ht, h012c, h015c, h125d]
                          · linarith only [h012c, h015c, h125b]
                        · linarith only [ht, r02.1, r15.2, h014c, h015c, h124a, h024c]
                      · linarith only [ht, r02.1, r34.2, h013c, h023c, h035b, h034c, h015a, h123a]
                · rcases h035 with ⟨h035a, h035b, h035c, h035d, h035e⟩ | ⟨h035a, h035b, h035c, h035d, h035e⟩
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · rcases h124 with ⟨h124a, h124b, h124c, h124d, h124e⟩ | ⟨h124a, h124b, h124c, h124d, h124e⟩
                        · rcases h125 with ⟨h125a, h125b, h125c, h125d, h125e⟩ | ⟨h125a, h125b, h125c, h125d, h125e⟩
                          · linarith only [ht, h012c, h015c, h125d]
                          · linarith only [h012c, h015c, h125b]
                        · linarith only [ht, r02.1, r15.2, h014c, h015c, h024c, h124a]
                      · linarith only [ht, r15.2, r34.1, h013c, h015c, h023b, h123a, h034c]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · rcases h124 with ⟨h124a, h124b, h124c, h124d, h124e⟩ | ⟨h124a, h124b, h124c, h124d, h124e⟩
                        · rcases h125 with ⟨h125a, h125b, h125c, h125d, h125e⟩ | ⟨h125a, h125b, h125c, h125d, h125e⟩
                          · linarith only [ht, h012c, h015c, h125d]
                          · linarith only [h012c, h015c, h125b]
                        · linarith only [ht, r02.1, r15.2, h014c, h015c, h024c, h124a]
                      · linarith only [h013c, h023b, h034b, h123a, h015a, h045b]
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · rcases h124 with ⟨h124a, h124b, h124c, h124d, h124e⟩ | ⟨h124a, h124b, h124c, h124d, h124e⟩
                        · rcases h125 with ⟨h125a, h125b, h125c, h125d, h125e⟩ | ⟨h125a, h125b, h125c, h125d, h125e⟩
                          · linarith only [ht, h012c, h015c, h125d]
                          · linarith only [h012c, h015c, h125b]
                        · linarith only [ht, r02.1, r15.2, h014c, h015c, h124a, h024c]
                      · linarith only [ht, r15.2, r34.1, h013c, h015c, h023b, h034c, h123a]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · rcases h124 with ⟨h124a, h124b, h124c, h124d, h124e⟩ | ⟨h124a, h124b, h124c, h124d, h124e⟩
                        · rcases h125 with ⟨h125a, h125b, h125c, h125d, h125e⟩ | ⟨h125a, h125b, h125c, h125d, h125e⟩
                          · linarith only [ht, h012c, h015c, h125d]
                          · linarith only [h012c, h015c, h125b]
                        · linarith only [ht, r02.1, r15.2, h014c, h015c, h024c, h124a]
                      · linarith only [h013c, h023b, h035b, h123a, h015a]
              · rcases h034 with ⟨h034a, h034b, h034c, h034d, h034e⟩ | ⟨h034a, h034b, h034c, h034d, h034e⟩
                · rcases h035 with ⟨h035a, h035b, h035c, h035d, h035e⟩ | ⟨h035a, h035b, h035c, h035d, h035e⟩
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, h013c, h025b, h023c, h123e, h015a]
                      · linarith only [h013c, h025b, h023c, h123a, h015a]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, h013c, h025b, h023c, h123e, h015a]
                      · linarith only [h013c, h025b, h123a, h023c, h015a]
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, h013c, h025b, h023c, h015a, h123e]
                      · linarith only [h013c, h025b, h023c, h123a, h015a]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, h013c, h025b, h023c, h123e, h015a]
                      · linarith only [h013c, h025b, h023c, h015a, h123a]
                · rcases h035 with ⟨h035a, h035b, h035c, h035d, h035e⟩ | ⟨h035a, h035b, h035c, h035d, h035e⟩
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, h013c, h025b, h023c, h123e, h015a]
                      · linarith only [h013c, h025b, h023c, h123a, h015a]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, h013c, h025b, h023c, h015a, h123e]
                      · linarith only [h013c, h025b, h023c, h123a, h015a]
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, h013c, h025b, h023c, h123e, h015a]
                      · linarith only [h013c, h025b, h023c, h123a, h015a]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, h013c, h025b, h023c, h123e, h015a]
                      · linarith only [h013c, h025b, h023c, h015a, h123a]
            · rcases h025 with ⟨h025a, h025b, h025c, h025d, h025e⟩ | ⟨h025a, h025b, h025c, h025d, h025e⟩
              · rcases h034 with ⟨h034a, h034b, h034c, h034d, h034e⟩ | ⟨h034a, h034b, h034c, h034d, h034e⟩
                · rcases h035 with ⟨h035a, h035b, h035c, h035d, h035e⟩ | ⟨h035a, h035b, h035c, h035d, h035e⟩
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · rcases h124 with ⟨h124a, h124b, h124c, h124d, h124e⟩ | ⟨h124a, h124b, h124c, h124d, h124e⟩
                        · linarith only [ht, r12.1, r15.2, h013c, h015c, h024c, h023c, h123e, h124c]
                        · linarith only [ht, r15.2, r24.1, h012c, h015c, h124c]
                      · linarith only [ht, r02.1, r15.2, h013c, h015c, h023c, h123a]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, h013c, h023c, h123e, h015a, h045b, h024b]
                      · linarith only [h013c, h023c, h123a, h015a, h045b, h024b]
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, h013c, h023c, h035b, h034a, h015a, h024b, h123e]
                      · linarith only [h013c, h023c, h035b, h034a, h015a, h024b, h123a]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, h013c, h023c, h035b, h034a, h015a, h024b, h123e]
                      · linarith only [h013c, h023c, h035b, h123a, h034a, h015a, h024b]
                · rcases h035 with ⟨h035a, h035b, h035c, h035d, h035e⟩ | ⟨h035a, h035b, h035c, h035d, h035e⟩
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · rcases h124 with ⟨h124a, h124b, h124c, h124d, h124e⟩ | ⟨h124a, h124b, h124c, h124d, h124e⟩
                        · linarith only [ht, r12.1, r15.2, h013c, h015c, h024c, h023c, h123e, h124c]
                        · linarith only [ht, r15.2, r24.1, h012c, h015c, h124c]
                      · linarith only [ht, r02.1, r15.2, h013c, h015c, h023c, h123a]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, h013c, h023c, h045b, h123e, h015a, h024b]
                      · linarith only [h013c, h023c, h045b, h123a, h015a, h024b]
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · rcases h124 with ⟨h124a, h124b, h124c, h124d, h124e⟩ | ⟨h124a, h124b, h124c, h124d, h124e⟩
                        · linarith only [ht, r12.1, r15.2, h013c, h015c, h024c, h023c, h124c, h123e]
                        · linarith only [ht, r15.2, r24.1, h012c, h015c, h124c]
                      · linarith only [ht, r02.1, r15.2, h013c, h015c, h023c, h123a]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, h013c, h023c, h015a, h123e, h024b, h045b]
                      · linarith only [h013c, h023c, h123a, h015a, h024b, h045b]
              · rcases h034 with ⟨h034a, h034b, h034c, h034d, h034e⟩ | ⟨h034a, h034b, h034c, h034d, h034e⟩
                · rcases h035 with ⟨h035a, h035b, h035c, h035d, h035e⟩ | ⟨h035a, h035b, h035c, h035d, h035e⟩
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, h013c, h023c, h025b, h123e, h015a]
                      · linarith only [h013c, h123a, h023c, h025b, h015a]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, h013c, h023c, h025b, h015a, h123e]
                      · linarith only [h013c, h023c, h025b, h123a, h015a]
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, h013c, h023c, h025b, h123e, h015a]
                      · linarith only [h013c, h023c, h123a, h025b, h015a]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, h013c, h023c, h025b, h123e, h015a]
                      · linarith only [h013c, h023c, h123a, h025b, h015a]
                · rcases h035 with ⟨h035a, h035b, h035c, h035d, h035e⟩ | ⟨h035a, h035b, h035c, h035d, h035e⟩
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, h013c, h023c, h025b, h123e, h015a]
                      · linarith only [h013c, h023c, h025b, h015a, h123a]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, h013c, h023c, h123e, h025b, h015a]
                      · linarith only [h013c, h023c, h025b, h015a, h123a]
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, h013c, h023c, h025b, h123e, h015a]
                      · linarith only [h013c, h023c, h025b, h123a, h015a]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, h013c, h023c, h025b, h123e, h015a]
                      · linarith only [h013c, h023c, h025b, h123a, h015a]
          · rcases h024 with ⟨h024a, h024b, h024c, h024d, h024e⟩ | ⟨h024a, h024b, h024c, h024d, h024e⟩
            · rcases h025 with ⟨h025a, h025b, h025c, h025d, h025e⟩ | ⟨h025a, h025b, h025c, h025d, h025e⟩
              · rcases h034 with ⟨h034a, h034b, h034c, h034d, h034e⟩ | ⟨h034a, h034b, h034c, h034d, h034e⟩
                · rcases h035 with ⟨h035a, h035b, h035c, h035d, h035e⟩ | ⟨h035a, h035b, h035c, h035d, h035e⟩
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, r12.1, r24.2, h024c, h023c, h123c]
                      · linarith only [ht, r15.2, r23.1, h012c, h015c, h123c]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, r12.1, r24.2, h024c, h023c, h123c]
                      · linarith only [ht, r15.2, r23.1, h012c, h015c, h123c]
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, r12.1, r24.2, h123c, h024c, h023c]
                      · linarith only [ht, r15.2, r23.1, h012c, h015c, h123c]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, r12.1, r24.2, h123c, h024c, h023c]
                      · linarith only [ht, r15.2, r23.1, h012c, h015c, h123c]
                · rcases h035 with ⟨h035a, h035b, h035c, h035d, h035e⟩ | ⟨h035a, h035b, h035c, h035d, h035e⟩
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, r12.1, r24.2, h024c, h023c, h123c]
                      · linarith only [ht, r15.2, r23.1, h012c, h015c, h123c]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, r12.1, r24.2, h123c, h024c, h023c]
                      · linarith only [ht, r15.2, r23.1, h012c, h015c, h123c]
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, r12.1, r24.2, h024c, h023c, h123c]
                      · linarith only [ht, r15.2, r23.1, h012c, h015c, h123c]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, r12.1, r24.2, h024c, h123c, h023c]
                      · linarith only [ht, r15.2, r23.1, h012c, h015c, h123c]
              · rcases h034 with ⟨h034a, h034b, h034c, h034d, h034e⟩ | ⟨h034a, h034b, h034c, h034d, h034e⟩
                · rcases h035 with ⟨h035a, h035b, h035c, h035d, h035e⟩ | ⟨h035a, h035b, h035c, h035d, h035e⟩
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, r12.1, r24.2, h123c, h024c, h023c]
                      · linarith only [ht, r15.2, r23.1, h012c, h015c, h123c]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, r12.1, r24.2, h024c, h123c, h023c]
                      · linarith only [ht, r15.2, r23.1, h012c, h015c, h123c]
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, r12.1, r24.2, h024c, h123c, h023c]
                      · linarith only [ht, r15.2, r23.1, h012c, h015c, h123c]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, r12.1, r24.2, h024c, h123c, h023c]
                      · linarith only [ht, r15.2, r23.1, h012c, h015c, h123c]
                · rcases h035 with ⟨h035a, h035b, h035c, h035d, h035e⟩ | ⟨h035a, h035b, h035c, h035d, h035e⟩
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, r12.1, r24.2, h024c, h023c, h123c]
                      · linarith only [ht, r15.2, r23.1, h012c, h015c, h123c]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, r12.1, r24.2, h024c, h123c, h023c]
                      · linarith only [ht, r15.2, r23.1, h012c, h015c, h123c]
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, r12.1, r24.2, h024c, h123c, h023c]
                      · linarith only [ht, r15.2, r23.1, h012c, h015c, h123c]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, r12.1, r24.2, h024c, h123c, h023c]
                      · linarith only [ht, r15.2, r23.1, h012c, h015c, h123c]
            · rcases h025 with ⟨h025a, h025b, h025c, h025d, h025e⟩ | ⟨h025a, h025b, h025c, h025d, h025e⟩
              · rcases h034 with ⟨h034a, h034b, h034c, h034d, h034e⟩ | ⟨h034a, h034b, h034c, h034d, h034e⟩
                · rcases h035 with ⟨h035a, h035b, h035c, h035d, h035e⟩ | ⟨h035a, h035b, h035c, h035d, h035e⟩
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, r12.1, r25.2, h025c, h023c, h123c]
                      · linarith only [ht, r15.2, r23.1, h012c, h015c, h123c]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, r12.1, r25.2, h025c, h023c, h123c]
                      · linarith only [ht, r15.2, r23.1, h012c, h015c, h123c]
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, r12.1, r25.2, h025c, h123c, h023c]
                      · linarith only [ht, r15.2, r23.1, h012c, h015c, h123c]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, r12.1, r25.2, h123c, h025c, h023c]
                      · linarith only [ht, r15.2, r23.1, h012c, h015c, h123c]
                · rcases h035 with ⟨h035a, h035b, h035c, h035d, h035e⟩ | ⟨h035a, h035b, h035c, h035d, h035e⟩
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, r12.1, r25.2, h123c, h025c, h023c]
                      · linarith only [ht, r15.2, r23.1, h012c, h015c, h123c]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, r12.1, r25.2, h025c, h123c, h023c]
                      · linarith only [ht, r15.2, r23.1, h012c, h015c, h123c]
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, r12.1, r25.2, h025c, h023c, h123c]
                      · linarith only [ht, r15.2, r23.1, h012c, h015c, h123c]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, r12.1, r25.2, h025c, h023c, h123c]
                      · linarith only [ht, r15.2, r23.1, h012c, h015c, h123c]
              · rcases h034 with ⟨h034a, h034b, h034c, h034d, h034e⟩ | ⟨h034a, h034b, h034c, h034d, h034e⟩
                · rcases h035 with ⟨h035a, h035b, h035c, h035d, h035e⟩ | ⟨h035a, h035b, h035c, h035d, h035e⟩
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, r12.1, r15.2, h012b, h015c, h023c, h123c]
                      · linarith only [ht, r15.2, r23.1, h012c, h015c, h123c]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, r12.1, r15.2, h012b, h015c, h023c, h123c]
                      · linarith only [ht, r15.2, r23.1, h012c, h015c, h123c]
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, r12.1, r15.2, h012b, h015c, h123c, h023c]
                      · linarith only [ht, r15.2, r23.1, h012c, h015c, h123c]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, r12.1, r15.2, h012b, h015c, h023c, h123c]
                      · linarith only [ht, r15.2, r23.1, h012c, h015c, h123c]
                · rcases h035 with ⟨h035a, h035b, h035c, h035d, h035e⟩ | ⟨h035a, h035b, h035c, h035d, h035e⟩
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, r12.1, r15.2, h012b, h015c, h023c, h123c]
                      · linarith only [ht, r15.2, r23.1, h012c, h015c, h123c]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, r12.1, r15.2, h012b, h015c, h123c, h023c]
                      · linarith only [ht, r15.2, r23.1, h012c, h015c, h123c]
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, r12.1, r15.2, h012b, h015c, h123c, h023c]
                      · linarith only [ht, r15.2, r23.1, h012c, h015c, h123c]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, r12.1, r15.2, h012b, h015c, h023c, h123c]
                      · linarith only [ht, r15.2, r23.1, h012c, h015c, h123c]
        · rcases h023 with ⟨h023a, h023b, h023c, h023d, h023e⟩ | ⟨h023a, h023b, h023c, h023d, h023e⟩
          · rcases h024 with ⟨h024a, h024b, h024c, h024d, h024e⟩ | ⟨h024a, h024b, h024c, h024d, h024e⟩
            · rcases h025 with ⟨h025a, h025b, h025c, h025d, h025e⟩ | ⟨h025a, h025b, h025c, h025d, h025e⟩
              · rcases h034 with ⟨h034a, h034b, h034c, h034d, h034e⟩ | ⟨h034a, h034b, h034c, h034d, h034e⟩
                · rcases h035 with ⟨h035a, h035b, h035c, h035d, h035e⟩ | ⟨h035a, h035b, h035c, h035d, h035e⟩
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · rcases h124 with ⟨h124a, h124b, h124c, h124d, h124e⟩ | ⟨h124a, h124b, h124c, h124d, h124e⟩
                        · rcases h125 with ⟨h125a, h125b, h125c, h125d, h125e⟩ | ⟨h125a, h125b, h125c, h125d, h125e⟩
                          · rcases h134 with ⟨h134a, h134b, h134c, h134d, h134e⟩ | ⟨h134a, h134b, h134c, h134d, h134e⟩
                            · rcases h135 with ⟨h135a, h135b, h135c, h135d, h135e⟩ | ⟨h135a, h135b, h135c, h135d, h135e⟩
                              · rcases h145 with ⟨h145a, h145b, h145c, h145d, h145e⟩ | ⟨h145a, h145b, h145c, h145d, h145e⟩
                                · rcases h234 with ⟨h234a, h234b, h234c, h234d, h234e⟩ | ⟨h234a, h234b, h234c, h234d, h234e⟩
                                  · rcases h235 with ⟨h235a, h235b, h235c, h235d, h235e⟩ | ⟨h235a, h235b, h235c, h235d, h235e⟩
                                    · rcases h245 with ⟨h245a, h245b, h245c, h245d, h245e⟩ | ⟨h245a, h245b, h245c, h245d, h245e⟩
                                      · rcases h345 with ⟨h345a, h345b, h345c, h345d, h345e⟩ | ⟨h345a, h345b, h345c, h345d, h345e⟩
                                        · linarith only [ht, r02.1, r45.2, h023c, h234c, h345c]
                                        · linarith only [ht, h045c, h034e, h345c]
                                      · linarith only [ht, h045c, h024e, h245c]
                                    · linarith only [ht, r03.1, r34.2, h035c, h235c, h234c]
                                  · linarith only [ht, h013a, h234c, h034c, h123e]
                                · linarith only [ht, h015c, h014d, h045c, h145a]
                              · linarith only [ht, h013d, h015c, h035c, h135a]
                            · linarith only [ht, h013d, h014c, h134a, h034c]
                          · linarith only [ht, h012d, h015c, h025c, h125a]
                        · linarith only [ht, h012d, h014c, h024c, h124a]
                      · linarith only [ht, h012d, h013c, h023c, h123a]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · rcases h124 with ⟨h124a, h124b, h124c, h124d, h124e⟩ | ⟨h124a, h124b, h124c, h124d, h124e⟩
                        · rcases h125 with ⟨h125a, h125b, h125c, h125d, h125e⟩ | ⟨h125a, h125b, h125c, h125d, h125e⟩
                          · rcases h134 with ⟨h134a, h134b, h134c, h134d, h134e⟩ | ⟨h134a, h134b, h134c, h134d, h134e⟩
                            · rcases h135 with ⟨h135a, h135b, h135c, h135d, h135e⟩ | ⟨h135a, h135b, h135c, h135d, h135e⟩
                              · rcases h145 with ⟨h145a, h145b, h145c, h145d, h145e⟩ | ⟨h145a, h145b, h145c, h145d, h145e⟩
                                · linarith only [ht, h014e, h045c, h145c]
                                · rcases h234 with ⟨h234a, h234b, h234c, h234d, h234e⟩ | ⟨h234a, h234b, h234c, h234d, h234e⟩
                                  · rcases h235 with ⟨h235a, h235b, h235c, h235d, h235e⟩ | ⟨h235a, h235b, h235c, h235d, h235e⟩
                                    · rcases h245 with ⟨h245a, h245b, h245c, h245d, h245e⟩ | ⟨h245a, h245b, h245c, h245d, h245e⟩
                                      · linarith only [h014a, h024b, h245b, h245a, h145c]
                                      · rcases h345 with ⟨h345a, h345b, h345c, h345d, h345e⟩ | ⟨h345a, h345b, h345c, h345d, h345e⟩
                                        · linarith only [ht, r03.1, h012d, r34.2, h014c, h023c, h035c, h145c, h234c, h345b]
                                        · linarith only [ht, h012d, h014c, h023c, h345e, h235c, h145c]
                                    · linarith only [ht, r03.1, r34.2, h035c, h235c, h234c]
                                  · linarith only [ht, h023e, h034c, h234c]
                              · linarith only [ht, h013d, h015c, h135a, h035c]
                            · linarith only [ht, h013d, h014c, h034c, h134a]
                          · linarith only [ht, h012d, h015c, h125a, h025c]
                        · linarith only [ht, h012d, h014c, h024c, h124a]
                      · linarith only [ht, h012d, h013c, h023c, h123a]
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · rcases h124 with ⟨h124a, h124b, h124c, h124d, h124e⟩ | ⟨h124a, h124b, h124c, h124d, h124e⟩
                        · rcases h125 with ⟨h125a, h125b, h125c, h125d, h125e⟩ | ⟨h125a, h125b, h125c, h125d, h125e⟩
                          · rcases h134 with ⟨h134a, h134b, h134c, h134d, h134e⟩ | ⟨h134a, h134b, h134c, h134d, h134e⟩
                            · rcases h135 with ⟨h135a, h135b, h135c, h135d, h135e⟩ | ⟨h135a, h135b, h135c, h135d, h135e⟩
                              · linarith only [ht, r13.1, r34.2, h035c, h135c, h034c]
                              · rcases h145 with ⟨h145a, h145b, h145c, h145d, h145e⟩ | ⟨h145a, h145b, h145c, h145d, h145e⟩
                                · rcases h234 with ⟨h234a, h234b, h234c, h234d, h234e⟩ | ⟨h234a, h234b, h234c, h234d, h234e⟩
                                  · rcases h235 with ⟨h235a, h235b, h235c, h235d, h235e⟩ | ⟨h235a, h235b, h235c, h235d, h235e⟩
                                    · linarith only [ht, r02.1, r34.2, h013a, h034c, h135c, h025c, h235b]
                                    · rcases h245 with ⟨h245a, h245b, h245c, h245d, h245e⟩ | ⟨h245a, h245b, h245c, h245d, h245e⟩
                                      · rcases h345 with ⟨h345a, h345b, h345c, h345d, h345e⟩ | ⟨h345a, h345b, h345c, h345d, h345e⟩
                                        · linarith only [ht, r01.2, r03.1, h013c, h034c, h135c, h345a]
                                        · linarith only [ht, r02.1, r03.2, h013a, h024c, h245c, h135c, h345a]
                                      · linarith only [ht, r34.2, r35.1, h013a, h045c, h234c, h034a, h135c, h245a, h235b]
                                  · linarith only [ht, r23.2, r35.1, h013a, h034c, h234c, h135c]
                                · linarith only [h013a, h045c, h034a, h135b, h145a]
                            · linarith only [ht, r01.2, r35.1, h014c, h035c, h134a, h034c]
                          · linarith only [ht, h012d, h015c, h125a, h025c]
                        · linarith only [ht, h012d, h014c, h024c, h124a]
                      · linarith only [ht, h012d, h013c, h023c, h123a]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · rcases h124 with ⟨h124a, h124b, h124c, h124d, h124e⟩ | ⟨h124a, h124b, h124c, h124d, h124e⟩
                        · rcases h125 with ⟨h125a, h125b, h125c, h125d, h125e⟩ | ⟨h125a, h125b, h125c, h125d, h125e⟩
                          · rcases h134 with ⟨h134a, h134b, h134c, h134d, h134e⟩ | ⟨h134a, h134b, h134c, h134d, h134e⟩
                            · rcases h135 with ⟨h135a, h135b, h135c, h135d, h135e⟩ | ⟨h135a, h135b, h135c, h135d, h135e⟩
                              · linarith only [ht, r13.1, r34.2, h035c, h034c, h135c]
                              · rcases h145 with ⟨h145a, h145b, h145c, h145d, h145e⟩ | ⟨h145a, h145b, h145c, h145d, h145e⟩
                                · linarith only [ht, r04.2, r35.1, h134a, h145c, h045c, h135c]
                                · rcases h234 with ⟨h234a, h234b, h234c, h234d, h234e⟩ | ⟨h234a, h234b, h234c, h234d, h234e⟩
                                  · rcases h235 with ⟨h235a, h235b, h235c, h235d, h235e⟩ | ⟨h235a, h235b, h235c, h235d, h235e⟩
                                    · linarith only [ht, h012d, h013c, h235b, h025c, h135c]
                                    · rcases h245 with ⟨h245a, h245b, h245c, h245d, h245e⟩ | ⟨h245a, h245b, h245c, h245d, h245e⟩
                                      · linarith only [h014a, h024b, h145c, h245b, h245a]
                                      · rcases h345 with ⟨h345a, h345b, h345c, h345d, h345e⟩ | ⟨h345a, h345b, h345c, h345d, h345e⟩
                                        · linarith only [ht, r01.2, r45.1, h013c, h034b, h014a, h145c, h135c, h345a]
                                        · linarith only [ht, h012d, h013c, h023c, h135c, h345d, h234c]
                                  · linarith only [ht, r23.2, r35.1, h013a, h034c, h234c, h135c]
                            · linarith only [ht, r01.2, r35.1, h014c, h035c, h134a, h034c]
                          · linarith only [ht, h012d, h015c, h125a, h025c]
                        · linarith only [ht, h012d, h014c, h024c, h124a]
                      · linarith only [ht, h012d, h013c, h023c, h123a]
                · rcases h035 with ⟨h035a, h035b, h035c, h035d, h035e⟩ | ⟨h035a, h035b, h035c, h035d, h035e⟩
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · rcases h124 with ⟨h124a, h124b, h124c, h124d, h124e⟩ | ⟨h124a, h124b, h124c, h124d, h124e⟩
                        · rcases h125 with ⟨h125a, h125b, h125c, h125d, h125e⟩ | ⟨h125a, h125b, h125c, h125d, h125e⟩
                          · rcases h134 with ⟨h134a, h134b, h134c, h134d, h134e⟩ | ⟨h134a, h134b, h134c, h134d, h134e⟩
                            · linarith only [ht, r13.1, r35.2, h035c, h034c, h134c]
                            · rcases h135 with ⟨h135a, h135b, h135c, h135d, h135e⟩ | ⟨h135a, h135b, h135c, h135d, h135e⟩
                              · rcases h145 with ⟨h145a, h145b, h145c, h145d, h145e⟩ | ⟨h145a, h145b, h145c, h145d, h145e⟩
                                · rcases h234 with ⟨h234a, h234b, h234c, h234d, h234e⟩ | ⟨h234a, h234b, h234c, h234d, h234e⟩
                                  · linarith only [ht, r02.1, r35.2, h013a, h024c, h035c, h134c, h234b]
                                  · rcases h235 with ⟨h235a, h235b, h235c, h235d, h235e⟩ | ⟨h235a, h235b, h235c, h235d, h235e⟩
                                    · rcases h245 with ⟨h245a, h245b, h245c, h245d, h245e⟩ | ⟨h245a, h245b, h245c, h245d, h245e⟩
                                      · rcases h345 with ⟨h345a, h345b, h345c, h345d, h345e⟩ | ⟨h345a, h345b, h345c, h345d, h345e⟩
                                        · linarith only [ht, h013a, h035c, h134c, h345d]
                                        · linarith only [ht, h012d, h013c, h023c, h134c, h235c, h345b]
                                      · linarith only [ht, h045c, h024e, h245c]
                                    · linarith only [ht, r23.2, r34.1, h013a, h035c, h134c, h235c]
                                · linarith only [ht, h015c, h014d, h045c, h145a]
                              · linarith only [ht, r01.2, r34.1, h013a, h015c, h035c, h134c, h135a]
                          · linarith only [ht, h012d, h015c, h125a, h025c]
                        · linarith only [ht, h012d, h014c, h024c, h124a]
                      · linarith only [ht, h012d, h013c, h023c, h123a]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · rcases h124 with ⟨h124a, h124b, h124c, h124d, h124e⟩ | ⟨h124a, h124b, h124c, h124d, h124e⟩
                        · rcases h125 with ⟨h125a, h125b, h125c, h125d, h125e⟩ | ⟨h125a, h125b, h125c, h125d, h125e⟩
                          · rcases h134 with ⟨h134a, h134b, h134c, h134d, h134e⟩ | ⟨h134a, h134b, h134c, h134d, h134e⟩
                            · linarith only [ht, r13.1, r35.2, h035c, h034c, h134c]
                            · rcases h135 with ⟨h135a, h135b, h135c, h135d, h135e⟩ | ⟨h135a, h135b, h135c, h135d, h135e⟩
                              · rcases h145 with ⟨h145a, h145b, h145c, h145d, h145e⟩ | ⟨h145a, h145b, h145c, h145d, h145e⟩
                                · linarith only [ht, r34.1, r35.2, h035c, h135a, h034b, h045c, h134c, h145b]
                                · rcases h234 with ⟨h234a, h234b, h234c, h234d, h234e⟩ | ⟨h234a, h234b, h234c, h234d, h234e⟩
                                  · linarith only [h135a, h014a, h024b, h134c, h234b, h145b]
                                  · rcases h235 with ⟨h235a, h235b, h235c, h235d, h235e⟩ | ⟨h235a, h235b, h235c, h235d, h235e⟩
                                    · rcases h245 with ⟨h245a, h245b, h245c, h245d, h245e⟩ | ⟨h245a, h245b, h245c, h245d, h245e⟩
                                      · linarith only [ht, r01.2, r34.1, h013a, h014c, h025b, h145c, h134c, h035a, h245b]
                                      · rcases h345 with ⟨h345a, h345b, h345c, h345d, h345e⟩ | ⟨h345a, h345b, h345c, h345d, h345e⟩
                                        · linarith only [ht, h012d, h014c, h023c, h145c, h235c, h345b]
                                        · linarith only [ht, h012d, h013b, h023c, h034a, h034b, h235c, h345b]
                                    · linarith only [ht, r23.2, r45.1, h013a, h035c, h145c, h134b, h235c]
                              · linarith only [ht, r01.2, r34.1, h013a, h015c, h035c, h134c, h135a]
                          · linarith only [ht, h012d, h015c, h125a, h025c]
                        · linarith only [ht, h012d, h014c, h024c, h124a]
                      · linarith only [ht, h012d, h013c, h023c, h123a]
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · rcases h124 with ⟨h124a, h124b, h124c, h124d, h124e⟩ | ⟨h124a, h124b, h124c, h124d, h124e⟩
                        · rcases h125 with ⟨h125a, h125b, h125c, h125d, h125e⟩ | ⟨h125a, h125b, h125c, h125d, h125e⟩
                          · rcases h134 with ⟨h134a, h134b, h134c, h134d, h134e⟩ | ⟨h134a, h134b, h134c, h134d, h134e⟩
                            · linarith only [ht, h013e, h034c, h134c]
                            · rcases h135 with ⟨h135a, h135b, h135c, h135d, h135e⟩ | ⟨h135a, h135b, h135c, h135d, h135e⟩
                              · linarith only [ht, r03.2, r34.1, h035c, h134c, h135c]
                              · rcases h145 with ⟨h145a, h145b, h145c, h145d, h145e⟩ | ⟨h145a, h145b, h145c, h145d, h145e⟩
                                · rcases h234 with ⟨h234a, h234b, h234c, h234d, h234e⟩ | ⟨h234a, h234b, h234c, h234d, h234e⟩
                                  · linarith only [h023b, h034c, h234a, h234b]
                                  · rcases h235 with ⟨h235a, h235b, h235c, h235d, h235e⟩ | ⟨h235a, h235b, h235c, h235d, h235e⟩
                                    · linarith only [ht, h013c, h014d, h045a, h025b, h235b, h135c]
                                    · rcases h245 with ⟨h245a, h245b, h245c, h245d, h245e⟩ | ⟨h245a, h245b, h245c, h245d, h245e⟩
                                      · rcases h345 with ⟨h345a, h345b, h345c, h345d, h345e⟩ | ⟨h345a, h345b, h345c, h345d, h345e⟩
                                        · linarith only [ht, h012d, h013c, h024c, h245c, h135c, h345e]
                                        · linarith only [ht, h012d, h013c, h024c, h245c, h135c, h345a]
                                      · linarith only [ht, h024e, h045c, h245c]
                                · linarith only [ht, h015c, h014d, h045c, h145a]
                          · linarith only [ht, h012d, h015c, h025c, h125a]
                        · linarith only [ht, h012d, h014c, h024c, h124a]
                      · linarith only [ht, h012d, h013c, h023c, h123a]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · rcases h124 with ⟨h124a, h124b, h124c, h124d, h124e⟩ | ⟨h124a, h124b, h124c, h124d, h124e⟩
                        · rcases h125 with ⟨h125a, h125b, h125c, h125d, h125e⟩ | ⟨h125a, h125b, h125c, h125d, h125e⟩
                          · rcases h134 with ⟨h134a, h134b, h134c, h134d, h134e⟩ | ⟨h134a, h134b, h134c, h134d, h134e⟩
                            · linarith only [ht, h013e, h034c, h134c]
                            · rcases h135 with ⟨h135a, h135b, h135c, h135d, h135e⟩ | ⟨h135a, h135b, h135c, h135d, h135e⟩
                              · linarith only [ht, r03.2, r34.1, h035c, h135c, h134c]
                              · rcases h145 with ⟨h145a, h145b, h145c, h145d, h145e⟩ | ⟨h145a, h145b, h145c, h145d, h145e⟩
                                · linarith only [ht, h014e, h045c, h145c]
                                · rcases h234 with ⟨h234a, h234b, h234c, h234d, h234e⟩ | ⟨h234a, h234b, h234c, h234d, h234e⟩
                                  · linarith only [h013a, h023b, h234a, h134c, h234b]
                                  · rcases h235 with ⟨h235a, h235b, h235c, h235d, h235e⟩ | ⟨h235a, h235b, h235c, h235d, h235e⟩
                                    · linarith only [h013a, h023b, h135c, h235b, h235a]
                                    · rcases h245 with ⟨h245a, h245b, h245c, h245d, h245e⟩ | ⟨h245a, h245b, h245c, h245d, h245e⟩
                                      · linarith only [ht, h012d, h013b, h045c, h034b, h025c, h245b]
                                      · rcases h345 with ⟨h345a, h345b, h345c, h345d, h345e⟩ | ⟨h345a, h345b, h345c, h345d, h345e⟩
                                        · linarith only [ht, r01.2, r34.1, h014c, h145c, h345c]
                                        · linarith only [ht, r01.2, r45.1, h013c, h134c, h345c]
                          · linarith only [ht, h012d, h015c, h125a, h025c]
                        · linarith only [ht, h012d, h014c, h024c, h124a]
                      · linarith only [ht, h012d, h013c, h023c, h123a]
              · rcases h034 with ⟨h034a, h034b, h034c, h034d, h034e⟩ | ⟨h034a, h034b, h034c, h034d, h034e⟩
                · rcases h035 with ⟨h035a, h035b, h035c, h035d, h035e⟩ | ⟨h035a, h035b, h035c, h035d, h035e⟩
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · rcases h124 with ⟨h124a, h124b, h124c, h124d, h124e⟩ | ⟨h124a, h124b, h124c, h124d, h124e⟩
                        · rcases h125 with ⟨h125a, h125b, h125c, h125d, h125e⟩ | ⟨h125a, h125b, h125c, h125d, h125e⟩
                          · linarith only [ht, r12.1, r23.2, h023c, h025c, h125c]
                          · rcases h134 with ⟨h134a, h134b, h134c, h134d, h134e⟩ | ⟨h134a, h134b, h134c, h134d, h134e⟩
                            · rcases h135 with ⟨h135a, h135b, h135c, h135d, h135e⟩ | ⟨h135a, h135b, h135c, h135d, h135e⟩
                              · rcases h145 with ⟨h145a, h145b, h145c, h145d, h145e⟩ | ⟨h145a, h145b, h145c, h145d, h145e⟩
                                · rcases h234 with ⟨h234a, h234b, h234c, h234d, h234e⟩ | ⟨h234a, h234b, h234c, h234d, h234e⟩
                                  · linarith only [ht, r25.1, r34.2, h012a, h023c, h234c, h125c]
                                  · linarith only [ht, r23.2, r25.1, h012a, h023a, h125c, h034c, h234c]
                                · linarith only [ht, h012c, h014d, h045c, h125b, h145a]
                              · linarith only [h012a, h023a, h135a, h125b, h035c]
                            · linarith only [ht, r25.1, r45.2, h012a, h023a, h014a, h045c, h125c, h034c, h134a]
                        · linarith only [ht, r01.2, r25.1, h014c, h024c, h025c, h124a]
                      · linarith only [ht, r25.1, r34.2, h013a, h023c, h025c, h034c, h123a]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · rcases h124 with ⟨h124a, h124b, h124c, h124d, h124e⟩ | ⟨h124a, h124b, h124c, h124d, h124e⟩
                        · rcases h125 with ⟨h125a, h125b, h125c, h125d, h125e⟩ | ⟨h125a, h125b, h125c, h125d, h125e⟩
                          · linarith only [ht, r12.1, r23.2, h023c, h025c, h125c]
                          · rcases h134 with ⟨h134a, h134b, h134c, h134d, h134e⟩ | ⟨h134a, h134b, h134c, h134d, h134e⟩
                            · rcases h135 with ⟨h135a, h135b, h135c, h135d, h135e⟩ | ⟨h135a, h135b, h135c, h135d, h135e⟩
                              · rcases h145 with ⟨h145a, h145b, h145c, h145d, h145e⟩ | ⟨h145a, h145b, h145c, h145d, h145e⟩
                                · linarith only [ht, h014e, h045c, h145c]
                                · rcases h234 with ⟨h234a, h234b, h234c, h234d, h234e⟩ | ⟨h234a, h234b, h234c, h234d, h234e⟩
                                  · linarith only [ht, r25.1, r34.2, h012a, h023c, h125c, h234c]
                                  · linarith only [ht, r23.2, r25.1, h012a, h023a, h125c, h034c, h234c]
                              · linarith only [ht, r01.2, r25.1, h012a, h015c, h023a, h125c, h035c, h135a]
                            · linarith only [ht, r01.2, r25.1, h012a, h014c, h023a, h125c, h134a, h034c]
                        · linarith only [ht, r01.2, r25.1, h014c, h024c, h025c, h124a]
                      · linarith only [ht, r25.1, r34.2, h013a, h023c, h025c, h123a, h034c]
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · rcases h124 with ⟨h124a, h124b, h124c, h124d, h124e⟩ | ⟨h124a, h124b, h124c, h124d, h124e⟩
                        · rcases h125 with ⟨h125a, h125b, h125c, h125d, h125e⟩ | ⟨h125a, h125b, h125c, h125d, h125e⟩
                          · linarith only [ht, r12.1, r23.2, h023c, h025c, h125c]
                          · rcases h134 with ⟨h134a, h134b, h134c, h134d, h134e⟩ | ⟨h134a, h134b, h134c, h134d, h134e⟩
                            · rcases h135 with ⟨h135a, h135b, h135c, h135d, h135e⟩ | ⟨h135a, h135b, h135c, h135d, h135e⟩
                              · linarith only [ht, r23.2, r25.1, h023c, h123a, h034a, h045a, h135b, h035c, h025b, h125c, h135a]
                              · rcases h145 with ⟨h145a, h145b, h145c, h145d, h145e⟩ | ⟨h145a, h145b, h145c, h145d, h145e⟩
                                · rcases h234 with ⟨h234a, h234b, h234c, h234d, h234e⟩ | ⟨h234a, h234b, h234c, h234d, h234e⟩
                                  · linarith only [ht, r25.1, r34.2, h012a, h023c, h125c, h234c]
                                  · linarith only [ht, r23.2, r25.1, h013a, h123a, h125c, h234c, h034c]
                                · linarith only [ht, r24.2, r25.1, h024c, h015a, h025b, h014a, h124a, h125c, h045c, h145a]
                            · linarith only [ht, r35.1, r45.2, h035c, h134a, h014a, h045c, h034c]
                        · linarith only [h024c, h045a, h025b, h124a, h014a]
                      · linarith only [ht, h012d, h013c, h023c, h123a]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · rcases h124 with ⟨h124a, h124b, h124c, h124d, h124e⟩ | ⟨h124a, h124b, h124c, h124d, h124e⟩
                        · rcases h125 with ⟨h125a, h125b, h125c, h125d, h125e⟩ | ⟨h125a, h125b, h125c, h125d, h125e⟩
                          · linarith only [ht, r12.1, r23.2, h023c, h025c, h125c]
                          · rcases h134 with ⟨h134a, h134b, h134c, h134d, h134e⟩ | ⟨h134a, h134b, h134c, h134d, h134e⟩
                            · rcases h135 with ⟨h135a, h135b, h135c, h135d, h135e⟩ | ⟨h135a, h135b, h135c, h135d, h135e⟩
                              · linarith only [ht, r25.1, r34.2, h135a, h035c, h123a, h125c, h135b, h034c]
                              · rcases h145 with ⟨h145a, h145b, h145c, h145d, h145e⟩ | ⟨h145a, h145b, h145c, h145d, h145e⟩
                                · linarith only [ht, r04.2, r25.1, h045c, h124a, h125c, h145c]
                                · rcases h234 with ⟨h234a, h234b, h234c, h234d, h234e⟩ | ⟨h234a, h234b, h234c, h234d, h234e⟩
                                  · linarith only [ht, r25.1, r34.2, h012a, h023c, h125c, h234c]
                                  · linarith only [ht, r23.2, r25.1, h013a, h123a, h125c, h034c, h234c]
                            · linarith only [ht, r01.2, r35.1, h014c, h035c, h034c, h134a]
                        · linarith only [ht, r01.2, r25.1, h014c, h024c, h025c, h124a]
                      · linarith only [ht, r25.1, r34.2, h013a, h023c, h025c, h123a, h034c]
                · rcases h035 with ⟨h035a, h035b, h035c, h035d, h035e⟩ | ⟨h035a, h035b, h035c, h035d, h035e⟩
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · rcases h124 with ⟨h124a, h124b, h124c, h124d, h124e⟩ | ⟨h124a, h124b, h124c, h124d, h124e⟩
                        · rcases h125 with ⟨h125a, h125b, h125c, h125d, h125e⟩ | ⟨h125a, h125b, h125c, h125d, h125e⟩
                          · linarith only [ht, r12.1, r23.2, h023c, h025c, h125c]
                          · rcases h134 with ⟨h134a, h134b, h134c, h134d, h134e⟩ | ⟨h134a, h134b, h134c, h134d, h134e⟩
                            · linarith only [ht, r23.2, r25.1, h023c, h125c, h025b, h124a, h034c, h035a, h134b]
                            · rcases h135 with ⟨h135a, h135b, h135c, h135d, h135e⟩ | ⟨h135a, h135b, h135c, h135d, h135e⟩
                              · rcases h145 with ⟨h145a, h145b, h145c, h145d, h145e⟩ | ⟨h145a, h145b, h145c, h145d, h145e⟩
                                · rcases h234 with ⟨h234a, h234b, h234c, h234d, h234e⟩ | ⟨h234a, h234b, h234c, h234d, h234e⟩
                                  · linarith only [h012a, h024c, h125b, h234b, h134c, h135a]
                                  · linarith only [ht, h012a, h024c, h125b, h234e, h134c, h135a]
                                · linarith only [h045c, h014a, h124a, h125b, h145a]
                              · linarith only [ht, r23.2, r34.1, h012a, h013a, h023c, h125b, h035c, h134c, h135a]
                        · linarith only [ht, h012d, h014c, h024c, h124a]
                      · linarith only [h013a, h023c, h025b, h123a, h035a]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · rcases h124 with ⟨h124a, h124b, h124c, h124d, h124e⟩ | ⟨h124a, h124b, h124c, h124d, h124e⟩
                        · rcases h125 with ⟨h125a, h125b, h125c, h125d, h125e⟩ | ⟨h125a, h125b, h125c, h125d, h125e⟩
                          · linarith only [ht, r12.1, r23.2, h023c, h025c, h125c]
                          · rcases h134 with ⟨h134a, h134b, h134c, h134d, h134e⟩ | ⟨h134a, h134b, h134c, h134d, h134e⟩
                            · linarith only [ht, r25.1, r35.2, h124a, h034c, h134b, h035c, h125c]
                            · rcases h135 with ⟨h135a, h135b, h135c, h135d, h135e⟩ | ⟨h135a, h135b, h135c, h135d, h135e⟩
                              · rcases h145 with ⟨h145a, h145b, h145c, h145d, h145e⟩ | ⟨h145a, h145b, h145c, h145d, h145e⟩
                                · linarith only [ht, r34.1, r35.2, h034b, h045c, h145b, h134c, h035c, h135a]
                                · rcases h234 with ⟨h234a, h234b, h234c, h234d, h234e⟩ | ⟨h234a, h234b, h234c, h234d, h234e⟩
                                  · linarith only [ht, r13.2, r25.1, h012a, h024c, h134c, h125c, h234b]
                                  · linarith only [ht, h012a, h024c, h125b, h134c, h234e, h135a]
                              · linarith only [ht, r24.2, r34.1, h012a, h013a, h024c, h125b, h134c, h135a, h035c]
                        · linarith only [ht, h012d, h014c, h024c, h124a]
                      · linarith only [h013a, h023c, h025b, h123a, h035a]
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · rcases h124 with ⟨h124a, h124b, h124c, h124d, h124e⟩ | ⟨h124a, h124b, h124c, h124d, h124e⟩
                        · rcases h125 with ⟨h125a, h125b, h125c, h125d, h125e⟩ | ⟨h125a, h125b, h125c, h125d, h125e⟩
                          · linarith only [ht, r12.1, r23.2, h023c, h025c, h125c]
                          · rcases h134 with ⟨h134a, h134b, h134c, h134d, h134e⟩ | ⟨h134a, h134b, h134c, h134d, h134e⟩
                            · linarith only [ht, h013e, h034c, h134c]
                            · rcases h135 with ⟨h135a, h135b, h135c, h135d, h135e⟩ | ⟨h135a, h135b, h135c, h135d, h135e⟩
                              · linarith only [ht, r03.2, r25.1, h135c, h123a, h125c, h035c]
                              · rcases h145 with ⟨h145a, h145b, h145c, h145d, h145e⟩ | ⟨h145a, h145b, h145c, h145d, h145e⟩
                                · rcases h234 with ⟨h234a, h234b, h234c, h234d, h234e⟩ | ⟨h234a, h234b, h234c, h234d, h234e⟩
                                  · linarith only [ht, r01.2, r25.1, h012a, h013c, h024a, h024b, h134c, h125c, h234b]
                                  · rcases h235 with ⟨h235a, h235b, h235c, h235d, h235e⟩ | ⟨h235a, h235b, h235c, h235d, h235e⟩
                                    · linarith only [ht, r24.2, r34.1, h012a, h013a, h024c, h023b, h134c, h125c, h235a]
                                    · linarith only [ht, h012a, h023c, h125c, h235d]
                                · linarith only [ht, r01.2, r25.1, h012a, h015c, h024a, h125c, h045c, h145a]
                        · linarith only [ht, r25.1, r45.2, h024c, h014a, h025c, h045c, h124a]
                      · linarith only [ht, r01.2, r25.1, h013c, h023c, h025c, h123a]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · rcases h124 with ⟨h124a, h124b, h124c, h124d, h124e⟩ | ⟨h124a, h124b, h124c, h124d, h124e⟩
                        · rcases h125 with ⟨h125a, h125b, h125c, h125d, h125e⟩ | ⟨h125a, h125b, h125c, h125d, h125e⟩
                          · linarith only [ht, r12.1, r23.2, h023c, h125c, h025c]
                          · rcases h134 with ⟨h134a, h134b, h134c, h134d, h134e⟩ | ⟨h134a, h134b, h134c, h134d, h134e⟩
                            · linarith only [ht, h013e, h034c, h134c]
                            · rcases h135 with ⟨h135a, h135b, h135c, h135d, h135e⟩ | ⟨h135a, h135b, h135c, h135d, h135e⟩
                              · linarith only [ht, r23.2, r34.1, h023c, h025b, h035a, h134c, h135c]
                              · rcases h145 with ⟨h145a, h145b, h145c, h145d, h145e⟩ | ⟨h145a, h145b, h145c, h145d, h145e⟩
                                · linarith only [ht, r04.2, r25.1, h145c, h045c, h125c, h124a]
                                · rcases h234 with ⟨h234a, h234b, h234c, h234d, h234e⟩ | ⟨h234a, h234b, h234c, h234d, h234e⟩
                                  · linarith only [ht, r01.2, r02.1, h013c, h024c, h134c, h234b]
                                  · rcases h235 with ⟨h235a, h235b, h235c, h235d, h235e⟩ | ⟨h235a, h235b, h235c, h235d, h235e⟩
                                    · linarith only [ht, r01.2, r34.1, h012c, h013a, h023b, h125c, h134c, h235a]
                                    · linarith only [ht, h023c, h025c, h235d]
                        · linarith only [ht, r01.2, r25.1, h014c, h024c, h025c, h124a]
                      · linarith only [ht, r01.2, r25.1, h013c, h023c, h123a, h025c]
            · rcases h025 with ⟨h025a, h025b, h025c, h025d, h025e⟩ | ⟨h025a, h025b, h025c, h025d, h025e⟩
              · rcases h034 with ⟨h034a, h034b, h034c, h034d, h034e⟩ | ⟨h034a, h034b, h034c, h034d, h034e⟩
                · rcases h035 with ⟨h035a, h035b, h035c, h035d, h035e⟩ | ⟨h035a, h035b, h035c, h035d, h035e⟩
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · rcases h124 with ⟨h124a, h124b, h124c, h124d, h124e⟩ | ⟨h124a, h124b, h124c, h124d, h124e⟩
                        · linarith only [ht, r12.1, r23.2, h023c, h124c, h024c]
                        · rcases h125 with ⟨h125a, h125b, h125c, h125d, h125e⟩ | ⟨h125a, h125b, h125c, h125d, h125e⟩
                          · rcases h134 with ⟨h134a, h134b, h134c, h134d, h134e⟩ | ⟨h134a, h134b, h134c, h134d, h134e⟩
                            · rcases h135 with ⟨h135a, h135b, h135c, h135d, h135e⟩ | ⟨h135a, h135b, h135c, h135d, h135e⟩
                              · rcases h145 with ⟨h145a, h145b, h145c, h145d, h145e⟩ | ⟨h145a, h145b, h145c, h145d, h145e⟩
                                · rcases h234 with ⟨h234a, h234b, h234c, h234d, h234e⟩ | ⟨h234a, h234b, h234c, h234d, h234e⟩
                                  · linarith only [h012a, h023c, h124c, h234a]
                                  · linarith only [ht, r03.1, r23.2, h012a, h023c, h124c, h234a, h034c]
                                · linarith only [ht, h015c, h014d, h045c, h145a]
                              · linarith only [ht, r01.2, r24.1, h012a, h015c, h023a, h124c, h035c, h135a]
                            · linarith only [ht, r24.1, r45.2, h012a, h023a, h124c, h014a, h045c, h034c, h134a]
                          · linarith only [ht, r01.2, r24.1, h012a, h015c, h124c, h025c, h125a]
                      · linarith only [ht, r24.1, r34.2, h013a, h023c, h034c, h024c, h123a]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · rcases h124 with ⟨h124a, h124b, h124c, h124d, h124e⟩ | ⟨h124a, h124b, h124c, h124d, h124e⟩
                        · linarith only [ht, r12.1, r23.2, h023c, h124c, h024c]
                        · rcases h125 with ⟨h125a, h125b, h125c, h125d, h125e⟩ | ⟨h125a, h125b, h125c, h125d, h125e⟩
                          · rcases h134 with ⟨h134a, h134b, h134c, h134d, h134e⟩ | ⟨h134a, h134b, h134c, h134d, h134e⟩
                            · rcases h135 with ⟨h135a, h135b, h135c, h135d, h135e⟩ | ⟨h135a, h135b, h135c, h135d, h135e⟩
                              · rcases h145 with ⟨h145a, h145b, h145c, h145d, h145e⟩ | ⟨h145a, h145b, h145c, h145d, h145e⟩
                                · linarith only [ht, r23.2, r24.1, h023c, h024b, h124c, h125a, h045c, h145b]
                                · rcases h234 with ⟨h234a, h234b, h234c, h234d, h234e⟩ | ⟨h234a, h234b, h234c, h234d, h234e⟩
                                  · linarith only [h012a, h023c, h124c, h234a]
                                  · linarith only [ht, h012c, h013d, h034b, h124c, h034a, h234a]
                              · linarith only [ht, h013d, h015c, h035c, h135a]
                            · linarith only [h012a, h023a, h134a, h124b, h034c]
                          · linarith only [ht, r01.2, r24.1, h012a, h015c, h025c, h124c, h125a]
                      · linarith only [ht, r24.1, r34.2, h013a, h023c, h034c, h123a, h024c]
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · rcases h124 with ⟨h124a, h124b, h124c, h124d, h124e⟩ | ⟨h124a, h124b, h124c, h124d, h124e⟩
                        · linarith only [ht, r12.1, r23.2, h023c, h124c, h024c]
                        · rcases h125 with ⟨h125a, h125b, h125c, h125d, h125e⟩ | ⟨h125a, h125b, h125c, h125d, h125e⟩
                          · rcases h134 with ⟨h134a, h134b, h134c, h134d, h134e⟩ | ⟨h134a, h134b, h134c, h134d, h134e⟩
                            · rcases h135 with ⟨h135a, h135b, h135c, h135d, h135e⟩ | ⟨h135a, h135b, h135c, h135d, h135e⟩
                              · linarith only [ht, r23.2, r24.1, h023c, h024b, h035c, h135b, h125a, h124c, h034a]
                              · rcases h145 with ⟨h145a, h145b, h145c, h145d, h145e⟩ | ⟨h145a, h145b, h145c, h145d, h145e⟩
                                · rcases h234 with ⟨h234a, h234b, h234c, h234d, h234e⟩ | ⟨h234a, h234b, h234c, h234d, h234e⟩
                                  · linarith only [h012a, h023c, h124c, h234a]
                                  · linarith only [h012a, h023a, h034b, h124c, h034a, h234a]
                                · linarith only [ht, r01.2, r24.1, h012a, h015c, h023a, h045c, h124c, h034a, h145a]
                            · linarith only [ht, r24.1, r45.2, h012a, h023a, h045c, h014a, h034c, h134a, h124c]
                          · linarith only [ht, r24.1, r34.2, h012a, h015a, h035b, h025c, h034c, h125a, h124c]
                      · linarith only [h013a, h023c, h024b, h123a, h034a]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · rcases h124 with ⟨h124a, h124b, h124c, h124d, h124e⟩ | ⟨h124a, h124b, h124c, h124d, h124e⟩
                        · linarith only [ht, r12.1, r23.2, h023c, h124c, h024c]
                        · rcases h125 with ⟨h125a, h125b, h125c, h125d, h125e⟩ | ⟨h125a, h125b, h125c, h125d, h125e⟩
                          · rcases h134 with ⟨h134a, h134b, h134c, h134d, h134e⟩ | ⟨h134a, h134b, h134c, h134d, h134e⟩
                            · rcases h135 with ⟨h135a, h135b, h135c, h135d, h135e⟩ | ⟨h135a, h135b, h135c, h135d, h135e⟩
                              · linarith only [ht, r23.2, r24.1, h023c, h024b, h035c, h125a, h124c, h034a, h135b]
                              · rcases h145 with ⟨h145a, h145b, h145c, h145d, h145e⟩ | ⟨h145a, h145b, h145c, h145d, h145e⟩
                                · linarith only [ht, r23.2, r24.1, h023c, h024b, h045c, h125a, h124c, h145b]
                                · rcases h234 with ⟨h234a, h234b, h234c, h234d, h234e⟩ | ⟨h234a, h234b, h234c, h234d, h234e⟩
                                  · linarith only [h012a, h023c, h124c, h234a]
                                  · linarith only [ht, r23.2, r35.1, h013a, h023c, h034b, h034a, h024c, h135c, h234a]
                            · linarith only [ht, r01.2, r35.1, h014c, h035c, h034c, h134a]
                          · linarith only [ht, r34.2, r45.1, h024b, h015a, h035b, h025c, h045c, h034c, h125a]
                      · linarith only [h013a, h023c, h024b, h123a, h034a]
                · rcases h035 with ⟨h035a, h035b, h035c, h035d, h035e⟩ | ⟨h035a, h035b, h035c, h035d, h035e⟩
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · rcases h124 with ⟨h124a, h124b, h124c, h124d, h124e⟩ | ⟨h124a, h124b, h124c, h124d, h124e⟩
                        · linarith only [ht, r12.1, r23.2, h023c, h124c, h024c]
                        · rcases h125 with ⟨h125a, h125b, h125c, h125d, h125e⟩ | ⟨h125a, h125b, h125c, h125d, h125e⟩
                          · rcases h134 with ⟨h134a, h134b, h134c, h134d, h134e⟩ | ⟨h134a, h134b, h134c, h134d, h134e⟩
                            · linarith only [ht, r24.1, r35.2, h035c, h134b, h123a, h124c, h034c, h134a]
                            · rcases h135 with ⟨h135a, h135b, h135c, h135d, h135e⟩ | ⟨h135a, h135b, h135c, h135d, h135e⟩
                              · rcases h145 with ⟨h145a, h145b, h145c, h145d, h145e⟩ | ⟨h145a, h145b, h145c, h145d, h145e⟩
                                · rcases h234 with ⟨h234a, h234b, h234c, h234d, h234e⟩ | ⟨h234a, h234b, h234c, h234d, h234e⟩
                                  · linarith only [h012a, h023c, h234a, h124c]
                                  · linarith only [ht, h012a, h023c, h124c, h234d]
                                · linarith only [ht, h015c, h014d, h145a, h045c]
                              · linarith only [ht, r01.2, r24.1, h013a, h015c, h035c, h123a, h124c, h135a]
                          · linarith only [ht, r01.2, r24.1, h012a, h015c, h025c, h125a, h124c]
                      · linarith only [ht, h012d, h013c, h023c, h123a]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · rcases h124 with ⟨h124a, h124b, h124c, h124d, h124e⟩ | ⟨h124a, h124b, h124c, h124d, h124e⟩
                        · linarith only [ht, r12.1, r23.2, h023c, h024c, h124c]
                        · rcases h125 with ⟨h125a, h125b, h125c, h125d, h125e⟩ | ⟨h125a, h125b, h125c, h125d, h125e⟩
                          · rcases h134 with ⟨h134a, h134b, h134c, h134d, h134e⟩ | ⟨h134a, h134b, h134c, h134d, h134e⟩
                            · linarith only [ht, r24.1, r35.2, h123a, h035c, h134a, h034c, h124c, h134b]
                            · rcases h135 with ⟨h135a, h135b, h135c, h135d, h135e⟩ | ⟨h135a, h135b, h135c, h135d, h135e⟩
                              · rcases h145 with ⟨h145a, h145b, h145c, h145d, h145e⟩ | ⟨h145a, h145b, h145c, h145d, h145e⟩
                                · linarith only [ht, r23.2, r24.1, h023c, h024b, h145b, h125a, h045c, h124c]
                                · rcases h234 with ⟨h234a, h234b, h234c, h234d, h234e⟩ | ⟨h234a, h234b, h234c, h234d, h234e⟩
                                  · linarith only [h012a, h023c, h234a, h124c]
                                  · linarith only [ht, h023c, h234d, h024c]
                              · linarith only [ht, r01.2, r24.1, h013a, h015c, h123a, h035c, h135a, h124c]
                          · linarith only [ht, r01.2, r45.1, h015c, h024b, h025c, h125a, h045c]
                      · linarith only [ht, r35.2, r45.1, h013a, h023c, h024b, h035c, h123a, h045c]
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · rcases h124 with ⟨h124a, h124b, h124c, h124d, h124e⟩ | ⟨h124a, h124b, h124c, h124d, h124e⟩
                        · linarith only [ht, r12.1, r23.2, h023c, h124c, h024c]
                        · rcases h125 with ⟨h125a, h125b, h125c, h125d, h125e⟩ | ⟨h125a, h125b, h125c, h125d, h125e⟩
                          · rcases h134 with ⟨h134a, h134b, h134c, h134d, h134e⟩ | ⟨h134a, h134b, h134c, h134d, h134e⟩
                            · linarith only [ht, r24.1, r45.2, h045c, h123a, h034a, h124c, h134c]
                            · rcases h135 with ⟨h135a, h135b, h135c, h135d, h135e⟩ | ⟨h135a, h135b, h135c, h135d, h135e⟩
                              · linarith only [ht, r03.2, r24.1, h035c, h123a, h135c, h124c]
                              · rcases h145 with ⟨h145a, h145b, h145c, h145d, h145e⟩ | ⟨h145a, h145b, h145c, h145d, h145e⟩
                                · rcases h234 with ⟨h234a, h234b, h234c, h234d, h234e⟩ | ⟨h234a, h234b, h234c, h234d, h234e⟩
                                  · linarith only [h012a, h023c, h124c, h234a]
                                  · linarith only [ht, h012a, h023c, h234d, h124c]
                                · linarith only [ht, h015c, h014d, h045c, h145a]
                          · linarith only [ht, r01.2, r24.1, h012a, h015c, h025c, h125a, h124c]
                      · linarith only [ht, h012d, h013c, h023c, h123a]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · rcases h124 with ⟨h124a, h124b, h124c, h124d, h124e⟩ | ⟨h124a, h124b, h124c, h124d, h124e⟩
                        · linarith only [ht, r12.1, r23.2, h023c, h024c, h124c]
                        · rcases h125 with ⟨h125a, h125b, h125c, h125d, h125e⟩ | ⟨h125a, h125b, h125c, h125d, h125e⟩
                          · rcases h134 with ⟨h134a, h134b, h134c, h134d, h134e⟩ | ⟨h134a, h134b, h134c, h134d, h134e⟩
                            · linarith only [ht, h013e, h134c, h034c]
                            · rcases h135 with ⟨h135a, h135b, h135c, h135d, h135e⟩ | ⟨h135a, h135b, h135c, h135d, h135e⟩
                              · linarith only [ht, r03.2, r34.1, h035c, h134c, h135c]
                              · rcases h145 with ⟨h145a, h145b, h145c, h145d, h145e⟩ | ⟨h145a, h145b, h145c, h145d, h145e⟩
                                · linarith only [ht, r23.2, r24.1, h023c, h024b, h045c, h125a, h124c, h145b]
                                · rcases h234 with ⟨h234a, h234b, h234c, h234d, h234e⟩ | ⟨h234a, h234b, h234c, h234d, h234e⟩
                                  · linarith only [h012a, h023c, h124c, h234a]
                                  · linarith only [ht, h012a, h023c, h124c, h234d]
                          · linarith only [ht, r01.2, r24.1, h012a, h015c, h025c, h125a, h124c]
                      · linarith only [ht, r01.2, r24.1, h013c, h023c, h123a, h024c]
              · rcases h034 with ⟨h034a, h034b, h034c, h034d, h034e⟩ | ⟨h034a, h034b, h034c, h034d, h034e⟩
                · rcases h035 with ⟨h035a, h035b, h035c, h035d, h035e⟩ | ⟨h035a, h035b, h035c, h035d, h035e⟩
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · rcases h124 with ⟨h124a, h124b, h124c, h124d, h124e⟩ | ⟨h124a, h124b, h124c, h124d, h124e⟩
                        · linarith only [ht, r12.1, r23.2, h023c, h124c, h024c]
                        · rcases h125 with ⟨h125a, h125b, h125c, h125d, h125e⟩ | ⟨h125a, h125b, h125c, h125d, h125e⟩
                          · linarith only [ht, r23.2, r24.1, h023c, h025c, h125a, h124c, h125b]
                          · rcases h134 with ⟨h134a, h134b, h134c, h134d, h134e⟩ | ⟨h134a, h134b, h134c, h134d, h134e⟩
                            · rcases h135 with ⟨h135a, h135b, h135c, h135d, h135e⟩ | ⟨h135a, h135b, h135c, h135d, h135e⟩
                              · rcases h145 with ⟨h145a, h145b, h145c, h145d, h145e⟩ | ⟨h145a, h145b, h145c, h145d, h145e⟩
                                · rcases h234 with ⟨h234a, h234b, h234c, h234d, h234e⟩ | ⟨h234a, h234b, h234c, h234d, h234e⟩
                                  · linarith only [h012a, h023c, h124c, h234a]
                                  · linarith only [h012a, h023a, h034c, h124c, h234a]
                                · linarith only [ht, r01.2, r24.1, h012a, h015c, h023a, h045c, h124c, h145a, h034a]
                              · linarith only [h023a, h015a, h025b, h135a, h035c]
                            · linarith only [h012a, h023a, h124b, h034c, h134a]
                      · linarith only [ht, r24.1, r34.2, h013a, h023c, h034c, h123a, h024c]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · rcases h124 with ⟨h124a, h124b, h124c, h124d, h124e⟩ | ⟨h124a, h124b, h124c, h124d, h124e⟩
                        · linarith only [ht, r12.1, r23.2, h023c, h124c, h024c]
                        · rcases h125 with ⟨h125a, h125b, h125c, h125d, h125e⟩ | ⟨h125a, h125b, h125c, h125d, h125e⟩
                          · linarith only [ht, r23.2, r24.1, h023c, h025c, h124c, h125a, h125b]
                          · rcases h134 with ⟨h134a, h134b, h134c, h134d, h134e⟩ | ⟨h134a, h134b, h134c, h134d, h134e⟩
                            · rcases h135 with ⟨h135a, h135b, h135c, h135d, h135e⟩ | ⟨h135a, h135b, h135c, h135d, h135e⟩
                              · rcases h145 with ⟨h145a, h145b, h145c, h145d, h145e⟩ | ⟨h145a, h145b, h145c, h145d, h145e⟩
                                · linarith only [ht, r23.2, r24.1, h023c, h024b, h045c, h135a, h124c, h123a, h145b]
                                · rcases h234 with ⟨h234a, h234b, h234c, h234d, h234e⟩ | ⟨h234a, h234b, h234c, h234d, h234e⟩
                                  · linarith only [h012a, h023c, h124c, h234a]
                                  · linarith only [ht, r03.1, r23.2, h012a, h023c, h034c, h124c, h234a]
                              · linarith only [ht, r23.2, r24.1, h013a, h023c, h015a, h025b, h124c, h123a, h035c, h135a]
                            · linarith only [h012a, h023a, h124b, h034c, h134a]
                      · linarith only [ht, r25.1, r34.2, h013a, h023c, h025c, h034c, h123a]
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · rcases h124 with ⟨h124a, h124b, h124c, h124d, h124e⟩ | ⟨h124a, h124b, h124c, h124d, h124e⟩
                        · linarith only [ht, r12.1, r23.2, h023c, h124c, h024c]
                        · rcases h125 with ⟨h125a, h125b, h125c, h125d, h125e⟩ | ⟨h125a, h125b, h125c, h125d, h125e⟩
                          · linarith only [ht, r23.2, r24.1, h023c, h025c, h125a, h125b, h124c]
                          · rcases h134 with ⟨h134a, h134b, h134c, h134d, h134e⟩ | ⟨h134a, h134b, h134c, h134d, h134e⟩
                            · rcases h135 with ⟨h135a, h135b, h135c, h135d, h135e⟩ | ⟨h135a, h135b, h135c, h135d, h135e⟩
                              · linarith only [ht, r23.2, r24.1, h023c, h024b, h123a, h035c, h135a, h135b, h034a, h124c]
                              · rcases h145 with ⟨h145a, h145b, h145c, h145d, h145e⟩ | ⟨h145a, h145b, h145c, h145d, h145e⟩
                                · rcases h234 with ⟨h234a, h234b, h234c, h234d, h234e⟩ | ⟨h234a, h234b, h234c, h234d, h234e⟩
                                  · linarith only [h012a, h023c, h124c, h234a]
                                  · linarith only [h013a, h123a, h034b, h234a, h034a, h124c]
                                · linarith only [ht, r23.2, r24.1, h013a, h023c, h015a, h123a, h145a, h025b, h045c, h034a, h124c]
                            · linarith only [ht, r24.1, r45.2, h013a, h123a, h014a, h034c, h045c, h134a, h124c]
                      · linarith only [ht, h012d, h013c, h023c, h123a]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · rcases h124 with ⟨h124a, h124b, h124c, h124d, h124e⟩ | ⟨h124a, h124b, h124c, h124d, h124e⟩
                        · linarith only [ht, r12.1, r23.2, h023c, h124c, h024c]
                        · rcases h125 with ⟨h125a, h125b, h125c, h125d, h125e⟩ | ⟨h125a, h125b, h125c, h125d, h125e⟩
                          · linarith only [ht, r23.2, r24.1, h023c, h025c, h125b, h124c, h125a]
                          · rcases h134 with ⟨h134a, h134b, h134c, h134d, h134e⟩ | ⟨h134a, h134b, h134c, h134d, h134e⟩
                            · rcases h135 with ⟨h135a, h135b, h135c, h135d, h135e⟩ | ⟨h135a, h135b, h135c, h135d, h135e⟩
                              · linarith only [ht, r24.1, r34.2, h135b, h034c, h135a, h035c, h124c, h123a]
                              · rcases h145 with ⟨h145a, h145b, h145c, h145d, h145e⟩ | ⟨h145a, h145b, h145c, h145d, h145e⟩
                                · linarith only [ht, r23.2, r24.1, h023c, h024b, h145a, h045c, h134a, h145b, h124c, h123a]
                                · rcases h234 with ⟨h234a, h234b, h234c, h234d, h234e⟩ | ⟨h234a, h234b, h234c, h234d, h234e⟩
                                  · linarith only [h012a, h023c, h234a, h124c]
                                  · linarith only [ht, r23.2, r35.1, h012a, h013a, h023c, h234a, h034b, h135c, h034a, h124c]
                            · linarith only [ht, r01.2, r24.1, h012a, h014c, h023a, h034c, h134a, h124c]
                      · linarith only [ht, r24.1, r34.2, h013a, h023c, h034c, h123a, h024c]
                · rcases h035 with ⟨h035a, h035b, h035c, h035d, h035e⟩ | ⟨h035a, h035b, h035c, h035d, h035e⟩
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · rcases h124 with ⟨h124a, h124b, h124c, h124d, h124e⟩ | ⟨h124a, h124b, h124c, h124d, h124e⟩
                        · linarith only [ht, r12.1, r23.2, h023c, h124c, h024c]
                        · rcases h125 with ⟨h125a, h125b, h125c, h125d, h125e⟩ | ⟨h125a, h125b, h125c, h125d, h125e⟩
                          · linarith only [ht, r23.2, r24.1, h023c, h025c, h125b, h124c, h125a]
                          · rcases h134 with ⟨h134a, h134b, h134c, h134d, h134e⟩ | ⟨h134a, h134b, h134c, h134d, h134e⟩
                            · linarith only [ht, r23.2, r24.1, h134a, h023c, h025b, h123a, h034c, h124c, h134b, h035a]
                            · rcases h135 with ⟨h135a, h135b, h135c, h135d, h135e⟩ | ⟨h135a, h135b, h135c, h135d, h135e⟩
                              · rcases h145 with ⟨h145a, h145b, h145c, h145d, h145e⟩ | ⟨h145a, h145b, h145c, h145d, h145e⟩
                                · rcases h234 with ⟨h234a, h234b, h234c, h234d, h234e⟩ | ⟨h234a, h234b, h234c, h234d, h234e⟩
                                  · linarith only [h012a, h023c, h124c, h234a]
                                  · linarith only [ht, h012a, h023c, h124c, h234d]
                                · linarith only [ht, h015c, h014d, h145a, h045c]
                              · linarith only [ht, r01.2, r24.1, h013a, h015c, h035c, h123a, h124c, h135a]
                      · linarith only [ht, h012d, h013c, h023c, h123a]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · rcases h124 with ⟨h124a, h124b, h124c, h124d, h124e⟩ | ⟨h124a, h124b, h124c, h124d, h124e⟩
                        · linarith only [ht, r12.1, r23.2, h023c, h124c, h024c]
                        · rcases h125 with ⟨h125a, h125b, h125c, h125d, h125e⟩ | ⟨h125a, h125b, h125c, h125d, h125e⟩
                          · linarith only [ht, r23.2, r24.1, h023c, h025c, h124c, h125b, h125a]
                          · rcases h134 with ⟨h134a, h134b, h134c, h134d, h134e⟩ | ⟨h134a, h134b, h134c, h134d, h134e⟩
                            · linarith only [ht, r23.2, r24.1, h023c, h024b, h124c, h123a, h034c, h035a, h134a, h134b, h045b]
                            · rcases h135 with ⟨h135a, h135b, h135c, h135d, h135e⟩ | ⟨h135a, h135b, h135c, h135d, h135e⟩
                              · rcases h145 with ⟨h145a, h145b, h145c, h145d, h145e⟩ | ⟨h145a, h145b, h145c, h145d, h145e⟩
                                · linarith only [ht, r23.2, r24.1, h023c, h024b, h124c, h045c, h123a, h145b, h135a]
                                · rcases h234 with ⟨h234a, h234b, h234c, h234d, h234e⟩ | ⟨h234a, h234b, h234c, h234d, h234e⟩
                                  · linarith only [h012a, h023c, h124c, h234a]
                                  · linarith only [ht, h012a, h023c, h124c, h234d]
                              · linarith only [ht, r23.2, r24.1, h013a, h023c, h024b, h035c, h015a, h124c, h123a, h135a, h045b]
                      · linarith only [ht, r01.2, r45.1, h013c, h023c, h024b, h123a, h045c]
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · rcases h124 with ⟨h124a, h124b, h124c, h124d, h124e⟩ | ⟨h124a, h124b, h124c, h124d, h124e⟩
                        · linarith only [ht, r12.1, r23.2, h023c, h124c, h024c]
                        · rcases h125 with ⟨h125a, h125b, h125c, h125d, h125e⟩ | ⟨h125a, h125b, h125c, h125d, h125e⟩
                          · linarith only [ht, r23.2, r24.1, h023c, h025c, h125b, h124c, h125a]
                          · rcases h134 with ⟨h134a, h134b, h134c, h134d, h134e⟩ | ⟨h134a, h134b, h134c, h134d, h134e⟩
                            · linarith only [ht, r24.1, r45.2, h123a, h124c, h045c, h034a, h134c]
                            · rcases h135 with ⟨h135a, h135b, h135c, h135d, h135e⟩ | ⟨h135a, h135b, h135c, h135d, h135e⟩
                              · linarith only [ht, r03.2, r24.1, h123a, h124c, h035c, h135c]
                              · rcases h145 with ⟨h145a, h145b, h145c, h145d, h145e⟩ | ⟨h145a, h145b, h145c, h145d, h145e⟩
                                · rcases h234 with ⟨h234a, h234b, h234c, h234d, h234e⟩ | ⟨h234a, h234b, h234c, h234d, h234e⟩
                                  · linarith only [h012a, h023c, h124c, h234a]
                                  · linarith only [ht, h012a, h023c, h124c, h234d]
                                · linarith only [ht, h015c, h014d, h045c, h145a]
                      · linarith only [ht, h012d, h013c, h023c, h123a]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · rcases h124 with ⟨h124a, h124b, h124c, h124d, h124e⟩ | ⟨h124a, h124b, h124c, h124d, h124e⟩
                        · linarith only [ht, r12.1, r23.2, h023c, h124c, h024c]
                        · rcases h125 with ⟨h125a, h125b, h125c, h125d, h125e⟩ | ⟨h125a, h125b, h125c, h125d, h125e⟩
                          · linarith only [ht, r23.2, r24.1, h023c, h025c, h125a, h125b, h124c]
                          · rcases h134 with ⟨h134a, h134b, h134c, h134d, h134e⟩ | ⟨h134a, h134b, h134c, h134d, h134e⟩
                            · linarith only [ht, h013e, h034c, h134c]
                            · rcases h135 with ⟨h135a, h135b, h135c, h135d, h135e⟩ | ⟨h135a, h135b, h135c, h135d, h135e⟩
                              · linarith only [ht, r23.2, r24.1, h023c, h035a, h123a, h025b, h124c, h135c]
                              · rcases h145 with ⟨h145a, h145b, h145c, h145d, h145e⟩ | ⟨h145a, h145b, h145c, h145d, h145e⟩
                                · linarith only [ht, r14.1, r23.2, h023c, h024b, h045c, h145c]
                                · rcases h234 with ⟨h234a, h234b, h234c, h234d, h234e⟩ | ⟨h234a, h234b, h234c, h234d, h234e⟩
                                  · linarith only [h012a, h023c, h234a, h124c]
                                  · linarith only [ht, h012a, h023c, h124c, h234d]
                      · linarith only [ht, r01.2, r24.1, h013c, h023c, h123a, h024c]
          · rcases h024 with ⟨h024a, h024b, h024c, h024d, h024e⟩ | ⟨h024a, h024b, h024c, h024d, h024e⟩
            · rcases h025 with ⟨h025a, h025b, h025c, h025d, h025e⟩ | ⟨h025a, h025b, h025c, h025d, h025e⟩
              · rcases h034 with ⟨h034a, h034b, h034c, h034d, h034e⟩ | ⟨h034a, h034b, h034c, h034d, h034e⟩
                · rcases h035 with ⟨h035a, h035b, h035c, h035d, h035e⟩ | ⟨h035a, h035b, h035c, h035d, h035e⟩
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, r12.1, r24.2, h023c, h024c, h123c]
                      · rcases h124 with ⟨h124a, h124b, h124c, h124d, h124e⟩ | ⟨h124a, h124b, h124c, h124d, h124e⟩
                        · rcases h125 with ⟨h125a, h125b, h125c, h125d, h125e⟩ | ⟨h125a, h125b, h125c, h125d, h125e⟩
                          · rcases h134 with ⟨h134a, h134b, h134c, h134d, h134e⟩ | ⟨h134a, h134b, h134c, h134d, h134e⟩
                            · rcases h135 with ⟨h135a, h135b, h135c, h135d, h135e⟩ | ⟨h135a, h135b, h135c, h135d, h135e⟩
                              · rcases h145 with ⟨h145a, h145b, h145c, h145d, h145e⟩ | ⟨h145a, h145b, h145c, h145d, h145e⟩
                                · rcases h234 with ⟨h234a, h234b, h234c, h234d, h234e⟩ | ⟨h234a, h234b, h234c, h234d, h234e⟩
                                  · linarith only [ht, h012a, h024c, h234d, h123c]
                                  · linarith only [h012a, h024c, h234b, h123c]
                                · linarith only [ht, r01.2, r23.1, h012a, h015c, h024a, h045c, h145a, h123c]
                              · linarith only [ht, h013d, h015c, h135a, h035c]
                            · linarith only [ht, h013d, h014c, h034c, h134a]
                          · linarith only [ht, r01.2, r23.1, h012a, h015c, h025c, h123c, h125a]
                        · linarith only [ht, r23.1, r45.2, h012a, h014a, h045c, h124a, h024c, h123c]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, r12.1, r24.2, h023c, h123c, h024c]
                      · rcases h124 with ⟨h124a, h124b, h124c, h124d, h124e⟩ | ⟨h124a, h124b, h124c, h124d, h124e⟩
                        · rcases h125 with ⟨h125a, h125b, h125c, h125d, h125e⟩ | ⟨h125a, h125b, h125c, h125d, h125e⟩
                          · rcases h134 with ⟨h134a, h134b, h134c, h134d, h134e⟩ | ⟨h134a, h134b, h134c, h134d, h134e⟩
                            · rcases h135 with ⟨h135a, h135b, h135c, h135d, h135e⟩ | ⟨h135a, h135b, h135c, h135d, h135e⟩
                              · rcases h145 with ⟨h145a, h145b, h145c, h145d, h145e⟩ | ⟨h145a, h145b, h145c, h145d, h145e⟩
                                · linarith only [ht, h014e, h045c, h145c]
                                · rcases h234 with ⟨h234a, h234b, h234c, h234d, h234e⟩ | ⟨h234a, h234b, h234c, h234d, h234e⟩
                                  · linarith only [ht, h023c, h024c, h234d]
                                  · linarith only [h023c, h024c, h234b]
                              · linarith only [ht, h013d, h015c, h135a, h035c]
                            · linarith only [ht, h013d, h014c, h034c, h134a]
                          · linarith only [ht, r01.2, r23.1, h015c, h023c, h025c, h125a]
                        · linarith only [ht, r01.2, r23.1, h014c, h023c, h124a, h024c]
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, r12.1, r24.2, h023c, h123c, h024c]
                      · rcases h124 with ⟨h124a, h124b, h124c, h124d, h124e⟩ | ⟨h124a, h124b, h124c, h124d, h124e⟩
                        · rcases h125 with ⟨h125a, h125b, h125c, h125d, h125e⟩ | ⟨h125a, h125b, h125c, h125d, h125e⟩
                          · rcases h134 with ⟨h134a, h134b, h134c, h134d, h134e⟩ | ⟨h134a, h134b, h134c, h134d, h134e⟩
                            · rcases h135 with ⟨h135a, h135b, h135c, h135d, h135e⟩ | ⟨h135a, h135b, h135c, h135d, h135e⟩
                              · linarith only [ht, r23.1, r34.2, h034c, h035c, h125a, h135b, h123c]
                              · rcases h145 with ⟨h145a, h145b, h145c, h145d, h145e⟩ | ⟨h145a, h145b, h145c, h145d, h145e⟩
                                · rcases h234 with ⟨h234a, h234b, h234c, h234d, h234e⟩ | ⟨h234a, h234b, h234c, h234d, h234e⟩
                                  · linarith only [ht, h012a, h123c, h234d, h024c]
                                  · linarith only [h012a, h123c, h234b, h024c]
                                · linarith only [ht, h015c, h014d, h045c, h145a]
                            · linarith only [ht, h013d, h014c, h034c, h134a]
                          · linarith only [ht, r01.2, r23.1, h012a, h015c, h025c, h123c, h125a]
                        · linarith only [ht, r23.1, r45.2, h012a, h045c, h014a, h124a, h123c, h024c]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, r12.1, r24.2, h023c, h123c, h024c]
                      · rcases h124 with ⟨h124a, h124b, h124c, h124d, h124e⟩ | ⟨h124a, h124b, h124c, h124d, h124e⟩
                        · rcases h125 with ⟨h125a, h125b, h125c, h125d, h125e⟩ | ⟨h125a, h125b, h125c, h125d, h125e⟩
                          · rcases h134 with ⟨h134a, h134b, h134c, h134d, h134e⟩ | ⟨h134a, h134b, h134c, h134d, h134e⟩
                            · rcases h135 with ⟨h135a, h135b, h135c, h135d, h135e⟩ | ⟨h135a, h135b, h135c, h135d, h135e⟩
                              · linarith only [ht, r23.1, r34.2, h034c, h035c, h123c, h135b, h125a]
                              · rcases h145 with ⟨h145a, h145b, h145c, h145d, h145e⟩ | ⟨h145a, h145b, h145c, h145d, h145e⟩
                                · linarith only [ht, h014e, h045c, h145c]
                                · rcases h234 with ⟨h234a, h234b, h234c, h234d, h234e⟩ | ⟨h234a, h234b, h234c, h234d, h234e⟩
                                  · linarith only [ht, h012a, h123c, h024c, h234d]
                                  · linarith only [h024b, h014a, h123c, h124a, h234b]
                            · linarith only [ht, h013d, h014c, h034c, h134a]
                          · linarith only [ht, r23.1, r34.2, h012a, h015a, h034c, h025c, h123c, h125a, h035b]
                        · linarith only [ht, r01.2, r23.1, h012a, h014c, h123c, h124a, h024c]
                · rcases h035 with ⟨h035a, h035b, h035c, h035d, h035e⟩ | ⟨h035a, h035b, h035c, h035d, h035e⟩
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, r12.1, r24.2, h023c, h123c, h024c]
                      · rcases h124 with ⟨h124a, h124b, h124c, h124d, h124e⟩ | ⟨h124a, h124b, h124c, h124d, h124e⟩
                        · rcases h125 with ⟨h125a, h125b, h125c, h125d, h125e⟩ | ⟨h125a, h125b, h125c, h125d, h125e⟩
                          · rcases h134 with ⟨h134a, h134b, h134c, h134d, h134e⟩ | ⟨h134a, h134b, h134c, h134d, h134e⟩
                            · linarith only [ht, r23.1, r24.2, h023b, h034c, h124a, h024c, h123c, h134b]
                            · rcases h135 with ⟨h135a, h135b, h135c, h135d, h135e⟩ | ⟨h135a, h135b, h135c, h135d, h135e⟩
                              · rcases h145 with ⟨h145a, h145b, h145c, h145d, h145e⟩ | ⟨h145a, h145b, h145c, h145d, h145e⟩
                                · rcases h234 with ⟨h234a, h234b, h234c, h234d, h234e⟩ | ⟨h234a, h234b, h234c, h234d, h234e⟩
                                  · linarith only [ht, r13.2, r23.1, h012a, h234b, h024c, h134c, h123c]
                                  · linarith only [h012a, h234b, h024c, h123c]
                                · linarith only [ht, r01.2, r23.1, h015c, h014a, h045c, h145a, h124a, h123c]
                              · linarith only [ht, r01.2, r34.1, h013a, h015c, h135a, h035c, h134c]
                          · linarith only [ht, r01.2, r23.1, h012a, h015c, h025c, h125a, h123c]
                        · linarith only [ht, r23.1, r35.2, h012a, h124a, h014a, h035c, h034b, h024c, h123c]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, r12.1, r24.2, h023c, h123c, h024c]
                      · rcases h124 with ⟨h124a, h124b, h124c, h124d, h124e⟩ | ⟨h124a, h124b, h124c, h124d, h124e⟩
                        · rcases h125 with ⟨h125a, h125b, h125c, h125d, h125e⟩ | ⟨h125a, h125b, h125c, h125d, h125e⟩
                          · rcases h134 with ⟨h134a, h134b, h134c, h134d, h134e⟩ | ⟨h134a, h134b, h134c, h134d, h134e⟩
                            · linarith only [ht, r23.1, r35.2, h034c, h134b, h035c, h123c, h124a]
                            · rcases h135 with ⟨h135a, h135b, h135c, h135d, h135e⟩ | ⟨h135a, h135b, h135c, h135d, h135e⟩
                              · rcases h145 with ⟨h145a, h145b, h145c, h145d, h145e⟩ | ⟨h145a, h145b, h145c, h145d, h145e⟩
                                · linarith only [ht, r23.1, r35.2, h125a, h045c, h035c, h123c, h034b, h145b]
                                · rcases h234 with ⟨h234a, h234b, h234c, h234d, h234e⟩ | ⟨h234a, h234b, h234c, h234d, h234e⟩
                                  · linarith only [h024b, h014a, h123b, h134c, h124a, h234b]
                                  · linarith only [h012a, h234b, h123c, h024c]
                              · linarith only [ht, r01.2, r34.1, h013a, h015c, h035c, h134c, h135a]
                          · linarith only [ht, r01.2, r23.1, h012a, h015c, h025c, h123c, h125a]
                        · linarith only [h023b, h014a, h124a, h034b, h024c]
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, r12.1, r24.2, h023c, h024c, h123c]
                      · rcases h124 with ⟨h124a, h124b, h124c, h124d, h124e⟩ | ⟨h124a, h124b, h124c, h124d, h124e⟩
                        · rcases h125 with ⟨h125a, h125b, h125c, h125d, h125e⟩ | ⟨h125a, h125b, h125c, h125d, h125e⟩
                          · rcases h134 with ⟨h134a, h134b, h134c, h134d, h134e⟩ | ⟨h134a, h134b, h134c, h134d, h134e⟩
                            · linarith only [ht, r23.1, r24.2, h023b, h034c, h134b, h124a, h024c, h123c]
                            · rcases h135 with ⟨h135a, h135b, h135c, h135d, h135e⟩ | ⟨h135a, h135b, h135c, h135d, h135e⟩
                              · linarith only [ht, r23.1, r24.2, h023b, h125a, h035c, h135b, h024c, h123c]
                              · rcases h145 with ⟨h145a, h145b, h145c, h145d, h145e⟩ | ⟨h145a, h145b, h145c, h145d, h145e⟩
                                · rcases h234 with ⟨h234a, h234b, h234c, h234d, h234e⟩ | ⟨h234a, h234b, h234c, h234d, h234e⟩
                                  · linarith only [ht, r13.2, r23.1, h012a, h134c, h024c, h234b, h123c]
                                  · linarith only [h012a, h234b, h024c, h123c]
                                · linarith only [ht, r01.2, r23.1, h015c, h014a, h124a, h145a, h123c, h045c]
                          · linarith only [h023b, h015a, h025c, h125a, h035b]
                        · linarith only [ht, r23.1, r45.2, h012a, h014a, h124a, h024c, h123c, h045c]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, r12.1, r24.2, h023c, h123c, h024c]
                      · rcases h124 with ⟨h124a, h124b, h124c, h124d, h124e⟩ | ⟨h124a, h124b, h124c, h124d, h124e⟩
                        · rcases h125 with ⟨h125a, h125b, h125c, h125d, h125e⟩ | ⟨h125a, h125b, h125c, h125d, h125e⟩
                          · rcases h134 with ⟨h134a, h134b, h134c, h134d, h134e⟩ | ⟨h134a, h134b, h134c, h134d, h134e⟩
                            · linarith only [ht, r23.1, r25.2, h023b, h034c, h123c, h025c, h124a, h134b]
                            · rcases h135 with ⟨h135a, h135b, h135c, h135d, h135e⟩ | ⟨h135a, h135b, h135c, h135d, h135e⟩
                              · linarith only [ht, r23.1, r25.2, h023b, h123c, h025c, h135b, h035c, h125a]
                              · rcases h145 with ⟨h145a, h145b, h145c, h145d, h145e⟩ | ⟨h145a, h145b, h145c, h145d, h145e⟩
                                · linarith only [ht, r23.1, r25.2, h023b, h123c, h025c, h045c, h125a, h034b, h145b]
                                · rcases h234 with ⟨h234a, h234b, h234c, h234d, h234e⟩ | ⟨h234a, h234b, h234c, h234d, h234e⟩
                                  · linarith only [h024b, h124a, h014a, h134c, h123b, h234b]
                                  · linarith only [h012a, h123c, h024c, h234b]
                          · linarith only [h023b, h015a, h025c, h125a, h035b]
                        · linarith only [ht, r01.2, r34.1, h014c, h124a, h023b, h034c, h024c]
              · rcases h034 with ⟨h034a, h034b, h034c, h034d, h034e⟩ | ⟨h034a, h034b, h034c, h034d, h034e⟩
                · rcases h035 with ⟨h035a, h035b, h035c, h035d, h035e⟩ | ⟨h035a, h035b, h035c, h035d, h035e⟩
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, r12.1, r24.2, h023c, h024c, h123c]
                      · rcases h124 with ⟨h124a, h124b, h124c, h124d, h124e⟩ | ⟨h124a, h124b, h124c, h124d, h124e⟩
                        · rcases h125 with ⟨h125a, h125b, h125c, h125d, h125e⟩ | ⟨h125a, h125b, h125c, h125d, h125e⟩
                          · linarith only [ht, r23.1, r24.2, h025c, h125a, h125b, h024c, h123c]
                          · rcases h134 with ⟨h134a, h134b, h134c, h134d, h134e⟩ | ⟨h134a, h134b, h134c, h134d, h134e⟩
                            · rcases h135 with ⟨h135a, h135b, h135c, h135d, h135e⟩ | ⟨h135a, h135b, h135c, h135d, h135e⟩
                              · rcases h145 with ⟨h145a, h145b, h145c, h145d, h145e⟩ | ⟨h145a, h145b, h145c, h145d, h145e⟩
                                · rcases h234 with ⟨h234a, h234b, h234c, h234d, h234e⟩ | ⟨h234a, h234b, h234c, h234d, h234e⟩
                                  · linarith only [ht, h012a, h024c, h123c, h234d]
                                  · linarith only [h012a, h024c, h234b, h123c]
                                · linarith only [ht, r23.1, r24.2, h025b, h015a, h124a, h014a, h145a, h045c, h024c, h123c]
                              · linarith only [ht, h012c, h013d, h135a, h035c, h125b]
                            · linarith only [ht, h013d, h014c, h134a, h034c]
                        · linarith only [ht, h012d, h014c, h124a, h024c]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, r12.1, r24.2, h023c, h123c, h024c]
                      · rcases h124 with ⟨h124a, h124b, h124c, h124d, h124e⟩ | ⟨h124a, h124b, h124c, h124d, h124e⟩
                        · rcases h125 with ⟨h125a, h125b, h125c, h125d, h125e⟩ | ⟨h125a, h125b, h125c, h125d, h125e⟩
                          · linarith only [ht, r23.1, r24.2, h025c, h123c, h125b, h024c, h125a]
                          · rcases h134 with ⟨h134a, h134b, h134c, h134d, h134e⟩ | ⟨h134a, h134b, h134c, h134d, h134e⟩
                            · rcases h135 with ⟨h135a, h135b, h135c, h135d, h135e⟩ | ⟨h135a, h135b, h135c, h135d, h135e⟩
                              · rcases h145 with ⟨h145a, h145b, h145c, h145d, h145e⟩ | ⟨h145a, h145b, h145c, h145d, h145e⟩
                                · linarith only [ht, r04.2, r23.1, h045c, h123c, h145c, h124a]
                                · rcases h234 with ⟨h234a, h234b, h234c, h234d, h234e⟩ | ⟨h234a, h234b, h234c, h234d, h234e⟩
                                  · linarith only [ht, h012a, h123c, h234d, h024c]
                                  · linarith only [ht, r25.1, r35.2, h012a, h013a, h125c, h123a, h234b, h035c, h024c]
                              · linarith only [ht, h013d, h015c, h135a, h035c]
                            · linarith only [ht, h013d, h014c, h034c, h134a]
                        · linarith only [ht, r01.2, r25.1, h014c, h025c, h124a, h024c]
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, r12.1, r24.2, h023c, h024c, h123c]
                      · rcases h124 with ⟨h124a, h124b, h124c, h124d, h124e⟩ | ⟨h124a, h124b, h124c, h124d, h124e⟩
                        · rcases h125 with ⟨h125a, h125b, h125c, h125d, h125e⟩ | ⟨h125a, h125b, h125c, h125d, h125e⟩
                          · linarith only [ht, r23.1, r34.2, h024a, h123c, h035b, h025c, h125b, h034c, h125a, h045a]
                          · rcases h134 with ⟨h134a, h134b, h134c, h134d, h134e⟩ | ⟨h134a, h134b, h134c, h134d, h134e⟩
                            · rcases h135 with ⟨h135a, h135b, h135c, h135d, h135e⟩ | ⟨h135a, h135b, h135c, h135d, h135e⟩
                              · linarith only [ht, r13.1, r34.2, h034c, h035c, h135c]
                              · rcases h145 with ⟨h145a, h145b, h145c, h145d, h145e⟩ | ⟨h145a, h145b, h145c, h145d, h145e⟩
                                · rcases h234 with ⟨h234a, h234b, h234c, h234d, h234e⟩ | ⟨h234a, h234b, h234c, h234d, h234e⟩
                                  · linarith only [ht, h012a, h123c, h234d, h024c]
                                  · linarith only [h012a, h123c, h024c, h234b]
                                · linarith only [ht, h013c, h014d, h045c, h145a, h135b]
                            · linarith only [ht, h013d, h014c, h134a, h034c]
                        · linarith only [ht, r23.1, r34.2, h012a, h123c, h035b, h124a, h014a, h034c, h024c, h045a]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, r12.1, r24.2, h023c, h123c, h024c]
                      · rcases h124 with ⟨h124a, h124b, h124c, h124d, h124e⟩ | ⟨h124a, h124b, h124c, h124d, h124e⟩
                        · rcases h125 with ⟨h125a, h125b, h125c, h125d, h125e⟩ | ⟨h125a, h125b, h125c, h125d, h125e⟩
                          · linarith only [ht, r23.1, r24.2, h025c, h125b, h123c, h125a, h024c]
                          · rcases h134 with ⟨h134a, h134b, h134c, h134d, h134e⟩ | ⟨h134a, h134b, h134c, h134d, h134e⟩
                            · rcases h135 with ⟨h135a, h135b, h135c, h135d, h135e⟩ | ⟨h135a, h135b, h135c, h135d, h135e⟩
                              · linarith only [ht, r13.1, r34.2, h034c, h035c, h135c]
                              · rcases h145 with ⟨h145a, h145b, h145c, h145d, h145e⟩ | ⟨h145a, h145b, h145c, h145d, h145e⟩
                                · linarith only [ht, h014e, h045c, h145c]
                                · rcases h234 with ⟨h234a, h234b, h234c, h234d, h234e⟩ | ⟨h234a, h234b, h234c, h234d, h234e⟩
                                  · linarith only [ht, h023c, h234d, h024c]
                                  · linarith only [h012a, h234b, h123c, h024c]
                            · linarith only [ht, h013d, h014c, h034c, h134a]
                        · linarith only [ht, h012d, h014c, h124a, h024c]
                · rcases h035 with ⟨h035a, h035b, h035c, h035d, h035e⟩ | ⟨h035a, h035b, h035c, h035d, h035e⟩
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, r12.1, r24.2, h023c, h123c, h024c]
                      · rcases h124 with ⟨h124a, h124b, h124c, h124d, h124e⟩ | ⟨h124a, h124b, h124c, h124d, h124e⟩
                        · rcases h125 with ⟨h125a, h125b, h125c, h125d, h125e⟩ | ⟨h125a, h125b, h125c, h125d, h125e⟩
                          · linarith only [ht, r23.1, r24.2, h025c, h125b, h125a, h123c, h024c]
                          · rcases h134 with ⟨h134a, h134b, h134c, h134d, h134e⟩ | ⟨h134a, h134b, h134c, h134d, h134e⟩
                            · linarith only [ht, r23.1, r24.2, h023b, h034c, h134b, h123c, h024c, h124a]
                            · rcases h135 with ⟨h135a, h135b, h135c, h135d, h135e⟩ | ⟨h135a, h135b, h135c, h135d, h135e⟩
                              · rcases h145 with ⟨h145a, h145b, h145c, h145d, h145e⟩ | ⟨h145a, h145b, h145c, h145d, h145e⟩
                                · rcases h234 with ⟨h234a, h234b, h234c, h234d, h234e⟩ | ⟨h234a, h234b, h234c, h234d, h234e⟩
                                  · linarith only [ht, r13.2, r23.1, h012a, h134c, h123c, h024c, h234b]
                                  · linarith only [h012a, h234b, h123c, h024c]
                                · linarith only [ht, r23.1, r24.2, h025b, h015a, h014a, h123c, h024c, h045c, h145a, h124a]
                              · linarith only [h012a, h024a, h034b, h125b, h035c, h135a]
                        · linarith only [ht, r25.1, r35.2, h025c, h034b, h014a, h124a, h035c, h024c]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, r12.1, r24.2, h023c, h123c, h024c]
                      · rcases h124 with ⟨h124a, h124b, h124c, h124d, h124e⟩ | ⟨h124a, h124b, h124c, h124d, h124e⟩
                        · rcases h125 with ⟨h125a, h125b, h125c, h125d, h125e⟩ | ⟨h125a, h125b, h125c, h125d, h125e⟩
                          · linarith only [ht, r23.1, r24.2, h123c, h025c, h125a, h125b, h024c]
                          · rcases h134 with ⟨h134a, h134b, h134c, h134d, h134e⟩ | ⟨h134a, h134b, h134c, h134d, h134e⟩
                            · linarith only [ht, r23.1, r24.2, h023b, h123c, h034c, h134b, h124a, h024c]
                            · rcases h135 with ⟨h135a, h135b, h135c, h135d, h135e⟩ | ⟨h135a, h135b, h135c, h135d, h135e⟩
                              · rcases h145 with ⟨h145a, h145b, h145c, h145d, h145e⟩ | ⟨h145a, h145b, h145c, h145d, h145e⟩
                                · linarith only [ht, r23.1, r24.2, h045c, h023b, h123c, h034b, h124a, h134b, h024c, h145b, h135a]
                                · rcases h234 with ⟨h234a, h234b, h234c, h234d, h234e⟩ | ⟨h234a, h234b, h234c, h234d, h234e⟩
                                  · linarith only [ht, r13.2, r23.1, h012a, h123c, h134c, h024c, h234b]
                                  · linarith only [h023c, h234b, h024c]
                              · linarith only [ht, r24.2, r34.1, h013a, h025b, h015a, h134c, h035c, h135a, h024c]
                        · linarith only [ht, r23.1, r35.2, h023c, h034b, h014a, h035c, h124a, h024c]
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, r12.1, r24.2, h023c, h123c, h024c]
                      · rcases h124 with ⟨h124a, h124b, h124c, h124d, h124e⟩ | ⟨h124a, h124b, h124c, h124d, h124e⟩
                        · rcases h125 with ⟨h125a, h125b, h125c, h125d, h125e⟩ | ⟨h125a, h125b, h125c, h125d, h125e⟩
                          · linarith only [ht, r23.1, r24.2, h025c, h125b, h123c, h125a, h024c]
                          · rcases h134 with ⟨h134a, h134b, h134c, h134d, h134e⟩ | ⟨h134a, h134b, h134c, h134d, h134e⟩
                            · linarith only [ht, r23.1, r24.2, h023b, h034c, h134b, h124a, h123c, h024c]
                            · rcases h135 with ⟨h135a, h135b, h135c, h135d, h135e⟩ | ⟨h135a, h135b, h135c, h135d, h135e⟩
                              · linarith only [ht, r23.1, r24.2, h023b, h134b, h124a, h123c, h135a, h135b, h024c, h035c]
                              · rcases h145 with ⟨h145a, h145b, h145c, h145d, h145e⟩ | ⟨h145a, h145b, h145c, h145d, h145e⟩
                                · rcases h234 with ⟨h234a, h234b, h234c, h234d, h234e⟩ | ⟨h234a, h234b, h234c, h234d, h234e⟩
                                  · linarith only [ht, r13.2, r23.1, h012a, h134c, h123c, h024c, h234b]
                                  · linarith only [h023b, h034b, h014a, h124a, h123c, h234b, h024c]
                                · linarith only [ht, r23.1, r24.2, h025b, h015a, h014a, h045c, h124a, h123c, h024c, h145a]
                        · linarith only [ht, r23.1, r45.2, h012a, h014a, h045c, h123c, h024c, h124a]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, r12.1, r24.2, h023c, h123c, h024c]
                      · rcases h124 with ⟨h124a, h124b, h124c, h124d, h124e⟩ | ⟨h124a, h124b, h124c, h124d, h124e⟩
                        · rcases h125 with ⟨h125a, h125b, h125c, h125d, h125e⟩ | ⟨h125a, h125b, h125c, h125d, h125e⟩
                          · linarith only [ht, r23.1, r24.2, h125b, h025c, h125a, h123c, h024c]
                          · rcases h134 with ⟨h134a, h134b, h134c, h134d, h134e⟩ | ⟨h134a, h134b, h134c, h134d, h134e⟩
                            · linarith only [ht, r23.1, r24.2, h023b, h034c, h123c, h134b, h124a, h024c]
                            · rcases h135 with ⟨h135a, h135b, h135c, h135d, h135e⟩ | ⟨h135a, h135b, h135c, h135d, h135e⟩
                              · linarith only [ht, r23.1, r24.2, h023b, h135b, h123c, h124a, h024c, h134b, h035c, h135a]
                              · rcases h145 with ⟨h145a, h145b, h145c, h145d, h145e⟩ | ⟨h145a, h145b, h145c, h145d, h145e⟩
                                · linarith only [ht, r23.1, r24.2, h145a, h023b, h034b, h123c, h145b, h045c, h124a, h024c]
                                · rcases h234 with ⟨h234a, h234b, h234c, h234d, h234e⟩ | ⟨h234a, h234b, h234c, h234d, h234e⟩
                                  · linarith only [ht, r13.2, r23.1, h012a, h234b, h123c, h024c, h134c]
                                  · linarith only [h012a, h123c, h024c, h234b]
                        · linarith only [ht, r01.2, r23.1, h012a, h014c, h124a, h123c, h024c]
            · rcases h025 with ⟨h025a, h025b, h025c, h025d, h025e⟩ | ⟨h025a, h025b, h025c, h025d, h025e⟩
              · rcases h034 with ⟨h034a, h034b, h034c, h034d, h034e⟩ | ⟨h034a, h034b, h034c, h034d, h034e⟩
                · rcases h035 with ⟨h035a, h035b, h035c, h035d, h035e⟩ | ⟨h035a, h035b, h035c, h035d, h035e⟩
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, r12.1, r25.2, h023c, h123c, h025c]
                      · rcases h124 with ⟨h124a, h124b, h124c, h124d, h124e⟩ | ⟨h124a, h124b, h124c, h124d, h124e⟩
                        · linarith only [ht, r23.1, r25.2, h025c, h124b, h123c, h124a, h024c]
                        · rcases h125 with ⟨h125a, h125b, h125c, h125d, h125e⟩ | ⟨h125a, h125b, h125c, h125d, h125e⟩
                          · rcases h134 with ⟨h134a, h134b, h134c, h134d, h134e⟩ | ⟨h134a, h134b, h134c, h134d, h134e⟩
                            · rcases h135 with ⟨h135a, h135b, h135c, h135d, h135e⟩ | ⟨h135a, h135b, h135c, h135d, h135e⟩
                              · rcases h145 with ⟨h145a, h145b, h145c, h145d, h145e⟩ | ⟨h145a, h145b, h145c, h145d, h145e⟩
                                · rcases h234 with ⟨h234a, h234b, h234c, h234d, h234e⟩ | ⟨h234a, h234b, h234c, h234d, h234e⟩
                                  · rcases h235 with ⟨h235a, h235b, h235c, h235d, h235e⟩ | ⟨h235a, h235b, h235c, h235d, h235e⟩
                                    · linarith only [ht, h023c, h025c, h235d]
                                    · linarith only [h023c, h025c, h235b]
                                  · linarith only [ht, r03.1, r25.2, h012a, h025c, h234a, h034c, h124c]
                                · linarith only [ht, h015c, h014d, h045c, h145a]
                              · linarith only [ht, h013d, h015c, h035c, h135a]
                            · linarith only [ht, h013d, h014c, h134a, h034c]
                          · linarith only [ht, r01.2, r24.1, h012a, h015c, h025c, h125a, h124c]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, r12.1, r25.2, h023c, h123c, h025c]
                      · rcases h124 with ⟨h124a, h124b, h124c, h124d, h124e⟩ | ⟨h124a, h124b, h124c, h124d, h124e⟩
                        · linarith only [ht, r23.1, r25.2, h124b, h025c, h124a, h123c, h024c]
                        · rcases h125 with ⟨h125a, h125b, h125c, h125d, h125e⟩ | ⟨h125a, h125b, h125c, h125d, h125e⟩
                          · rcases h134 with ⟨h134a, h134b, h134c, h134d, h134e⟩ | ⟨h134a, h134b, h134c, h134d, h134e⟩
                            · rcases h135 with ⟨h135a, h135b, h135c, h135d, h135e⟩ | ⟨h135a, h135b, h135c, h135d, h135e⟩
                              · rcases h145 with ⟨h145a, h145b, h145c, h145d, h145e⟩ | ⟨h145a, h145b, h145c, h145d, h145e⟩
                                · linarith only [ht, r23.1, r25.2, h125a, h024b, h025c, h123c, h045c, h145b]
                                · rcases h234 with ⟨h234a, h234b, h234c, h234d, h234e⟩ | ⟨h234a, h234b, h234c, h234d, h234e⟩
                                  · rcases h235 with ⟨h235a, h235b, h235c, h235d, h235e⟩ | ⟨h235a, h235b, h235c, h235d, h235e⟩
                                    · linarith only [ht, h012a, h025c, h123c, h235d]
                                    · linarith only [h012a, h025c, h123c, h235b]
                                  · linarith only [ht, r03.1, r25.2, h012a, h025c, h124c, h034c, h234a]
                              · linarith only [ht, h013d, h015c, h035c, h135a]
                            · linarith only [ht, h012c, h013d, h134a, h124b, h034c]
                          · linarith only [ht, r01.2, r45.1, h015c, h024b, h025c, h125a, h045c]
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, r12.1, r25.2, h023c, h025c, h123c]
                      · rcases h124 with ⟨h124a, h124b, h124c, h124d, h124e⟩ | ⟨h124a, h124b, h124c, h124d, h124e⟩
                        · linarith only [ht, r23.1, r25.2, h124a, h124b, h025c, h123c, h024c]
                        · rcases h125 with ⟨h125a, h125b, h125c, h125d, h125e⟩ | ⟨h125a, h125b, h125c, h125d, h125e⟩
                          · rcases h134 with ⟨h134a, h134b, h134c, h134d, h134e⟩ | ⟨h134a, h134b, h134c, h134d, h134e⟩
                            · rcases h135 with ⟨h135a, h135b, h135c, h135d, h135e⟩ | ⟨h135a, h135b, h135c, h135d, h135e⟩
                              · linarith only [ht, r23.1, r34.2, h135b, h125a, h035c, h123c, h034c]
                              · rcases h145 with ⟨h145a, h145b, h145c, h145d, h145e⟩ | ⟨h145a, h145b, h145c, h145d, h145e⟩
                                · rcases h234 with ⟨h234a, h234b, h234c, h234d, h234e⟩ | ⟨h234a, h234b, h234c, h234d, h234e⟩
                                  · linarith only [ht, h013a, h125a, h234e, h124c, h135b, h034c]
                                  · linarith only [h012a, h035b, h234a, h124c, h025a, h034c]
                                · linarith only [h014a, h045c, h134a, h145a, h135b]
                            · linarith only [ht, r35.1, r45.2, h134a, h014a, h035c, h045c, h034c]
                          · linarith only [ht, r23.1, r34.2, h012a, h015a, h035b, h025c, h123c, h125a, h034c]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, r12.1, r25.2, h023c, h025c, h123c]
                      · rcases h124 with ⟨h124a, h124b, h124c, h124d, h124e⟩ | ⟨h124a, h124b, h124c, h124d, h124e⟩
                        · linarith only [ht, r23.1, r25.2, h123c, h025c, h124b, h124a, h024c]
                        · rcases h125 with ⟨h125a, h125b, h125c, h125d, h125e⟩ | ⟨h125a, h125b, h125c, h125d, h125e⟩
                          · rcases h134 with ⟨h134a, h134b, h134c, h134d, h134e⟩ | ⟨h134a, h134b, h134c, h134d, h134e⟩
                            · rcases h135 with ⟨h135a, h135b, h135c, h135d, h135e⟩ | ⟨h135a, h135b, h135c, h135d, h135e⟩
                              · linarith only [ht, r23.1, r25.2, h023b, h123c, h025c, h035c, h135b, h125a]
                              · rcases h145 with ⟨h145a, h145b, h145c, h145d, h145e⟩ | ⟨h145a, h145b, h145c, h145d, h145e⟩
                                · linarith only [ht, r23.1, r25.2, h024b, h123c, h045c, h025c, h145b, h125a]
                                · rcases h234 with ⟨h234a, h234b, h234c, h234d, h234e⟩ | ⟨h234a, h234b, h234c, h234d, h234e⟩
                                  · linarith only [ht, h013a, h234e, h135b, h124c, h125a, h034c]
                                  · linarith only [h013a, h135b, h124c, h125a, h034c, h234a]
                            · linarith only [h024b, h035b, h014a, h025a, h134a, h034c]
                          · linarith only [ht, r23.1, r34.2, h023c, h015a, h035b, h025c, h125a, h034c]
                · rcases h035 with ⟨h035a, h035b, h035c, h035d, h035e⟩ | ⟨h035a, h035b, h035c, h035d, h035e⟩
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, r12.1, r25.2, h023c, h025c, h123c]
                      · rcases h124 with ⟨h124a, h124b, h124c, h124d, h124e⟩ | ⟨h124a, h124b, h124c, h124d, h124e⟩
                        · linarith only [ht, r23.1, r25.2, h123c, h025c, h124b, h124a, h024c]
                        · rcases h125 with ⟨h125a, h125b, h125c, h125d, h125e⟩ | ⟨h125a, h125b, h125c, h125d, h125e⟩
                          · rcases h134 with ⟨h134a, h134b, h134c, h134d, h134e⟩ | ⟨h134a, h134b, h134c, h134d, h134e⟩
                            · linarith only [ht, r13.1, r25.2, h023b, h025c, h034c, h134c]
                            · rcases h135 with ⟨h135a, h135b, h135c, h135d, h135e⟩ | ⟨h135a, h135b, h135c, h135d, h135e⟩
                              · rcases h145 with ⟨h145a, h145b, h145c, h145d, h145e⟩ | ⟨h145a, h145b, h145c, h145d, h145e⟩
                                · rcases h234 with ⟨h234a, h234b, h234c, h234d, h234e⟩ | ⟨h234a, h234b, h234c, h234d, h234e⟩
                                  · linarith only [ht, r23.1, r25.2, h013a, h023b, h025c, h234c, h134c]
                                  · linarith only [ht, r25.2, r34.1, h012a, h123c, h025c, h234c]
                                · linarith only [ht, h015c, h014d, h045c, h145a]
                              · linarith only [ht, h013d, h015c, h035c, h135a]
                          · linarith only [ht, r01.2, r23.1, h012a, h015c, h123c, h025c, h125a]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, r12.1, r25.2, h023c, h025c, h123c]
                      · rcases h124 with ⟨h124a, h124b, h124c, h124d, h124e⟩ | ⟨h124a, h124b, h124c, h124d, h124e⟩
                        · linarith only [ht, r23.1, r25.2, h124a, h123c, h025c, h124b, h024c]
                        · rcases h125 with ⟨h125a, h125b, h125c, h125d, h125e⟩ | ⟨h125a, h125b, h125c, h125d, h125e⟩
                          · rcases h134 with ⟨h134a, h134b, h134c, h134d, h134e⟩ | ⟨h134a, h134b, h134c, h134d, h134e⟩
                            · linarith only [ht, r13.1, r35.2, h035c, h134c, h034c]
                            · rcases h135 with ⟨h135a, h135b, h135c, h135d, h135e⟩ | ⟨h135a, h135b, h135c, h135d, h135e⟩
                              · rcases h145 with ⟨h145a, h145b, h145c, h145d, h145e⟩ | ⟨h145a, h145b, h145c, h145d, h145e⟩
                                · linarith only [ht, r23.1, r25.2, h024b, h123c, h025c, h125a, h145b, h045c]
                                · rcases h234 with ⟨h234a, h234b, h234c, h234d, h234e⟩ | ⟨h234a, h234b, h234c, h234d, h234e⟩
                                  · linarith only [ht, r23.1, r35.2, h234c, h013a, h035c, h134c]
                                  · linarith only [ht, r25.2, r34.1, h012a, h123c, h025c, h234c]
                              · linarith only [ht, h013d, h015c, h035c, h135a]
                          · linarith only [ht, r01.2, r23.1, h012a, h015c, h125a, h123c, h025c]
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, r12.1, r25.2, h023c, h123c, h025c]
                      · rcases h124 with ⟨h124a, h124b, h124c, h124d, h124e⟩ | ⟨h124a, h124b, h124c, h124d, h124e⟩
                        · linarith only [ht, r23.1, r25.2, h025c, h123c, h124b, h124a, h024c]
                        · rcases h125 with ⟨h125a, h125b, h125c, h125d, h125e⟩ | ⟨h125a, h125b, h125c, h125d, h125e⟩
                          · rcases h134 with ⟨h134a, h134b, h134c, h134d, h134e⟩ | ⟨h134a, h134b, h134c, h134d, h134e⟩
                            · linarith only [ht, h013e, h134c, h034c]
                            · rcases h135 with ⟨h135a, h135b, h135c, h135d, h135e⟩ | ⟨h135a, h135b, h135c, h135d, h135e⟩
                              · linarith only [ht, r23.1, r25.2, h023b, h025c, h035c, h123c, h135b, h125a]
                              · rcases h145 with ⟨h145a, h145b, h145c, h145d, h145e⟩ | ⟨h145a, h145b, h145c, h145d, h145e⟩
                                · rcases h234 with ⟨h234a, h234b, h234c, h234d, h234e⟩ | ⟨h234a, h234b, h234c, h234d, h234e⟩
                                  · linarith only [ht, r23.1, r25.2, h013a, h023b, h025c, h134c, h234c]
                                  · linarith only [ht, r25.2, r34.1, h012a, h025c, h123c, h234c]
                                · linarith only [ht, h015c, h014d, h045c, h145a]
                          · linarith only [h023b, h035b, h015a, h025c, h125a]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, r12.1, r25.2, h023c, h025c, h123c]
                      · rcases h124 with ⟨h124a, h124b, h124c, h124d, h124e⟩ | ⟨h124a, h124b, h124c, h124d, h124e⟩
                        · linarith only [ht, r23.1, r25.2, h124b, h123c, h025c, h124a, h024c]
                        · rcases h125 with ⟨h125a, h125b, h125c, h125d, h125e⟩ | ⟨h125a, h125b, h125c, h125d, h125e⟩
                          · rcases h134 with ⟨h134a, h134b, h134c, h134d, h134e⟩ | ⟨h134a, h134b, h134c, h134d, h134e⟩
                            · linarith only [ht, r13.1, r25.2, h023b, h025c, h134c, h034c]
                            · rcases h135 with ⟨h135a, h135b, h135c, h135d, h135e⟩ | ⟨h135a, h135b, h135c, h135d, h135e⟩
                              · linarith only [ht, r23.1, r25.2, h023b, h123c, h025c, h035c, h125a, h135b]
                              · rcases h145 with ⟨h145a, h145b, h145c, h145d, h145e⟩ | ⟨h145a, h145b, h145c, h145d, h145e⟩
                                · linarith only [ht, r23.1, r25.2, h024b, h123c, h025c, h045c, h125a, h145b]
                                · rcases h234 with ⟨h234a, h234b, h234c, h234d, h234e⟩ | ⟨h234a, h234b, h234c, h234d, h234e⟩
                                  · linarith only [ht, r23.1, r25.2, h013a, h023b, h025c, h134c, h234c]
                                  · linarith only [ht, r25.2, r34.1, h012a, h123c, h025c, h234c]
                          · linarith only [h023b, h035b, h015a, h025c, h125a]
              · rcases h034 with ⟨h034a, h034b, h034c, h034d, h034e⟩ | ⟨h034a, h034b, h034c, h034d, h034e⟩
                · rcases h035 with ⟨h035a, h035b, h035c, h035d, h035e⟩ | ⟨h035a, h035b, h035c, h035d, h035e⟩
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, h012e, h023c, h123c]
                      · rcases h124 with ⟨h124a, h124b, h124c, h124d, h124e⟩ | ⟨h124a, h124b, h124c, h124d, h124e⟩
                        · linarith only [ht, r02.2, r23.1, h123c, h124c, h024c]
                        · rcases h125 with ⟨h125a, h125b, h125c, h125d, h125e⟩ | ⟨h125a, h125b, h125c, h125d, h125e⟩
                          · linarith only [ht, r02.2, r23.1, h123c, h125c, h025c]
                          · rcases h134 with ⟨h134a, h134b, h134c, h134d, h134e⟩ | ⟨h134a, h134b, h134c, h134d, h134e⟩
                            · rcases h135 with ⟨h135a, h135b, h135c, h135d, h135e⟩ | ⟨h135a, h135b, h135c, h135d, h135e⟩
                              · rcases h145 with ⟨h145a, h145b, h145c, h145d, h145e⟩ | ⟨h145a, h145b, h145c, h145d, h145e⟩
                                · rcases h234 with ⟨h234a, h234b, h234c, h234d, h234e⟩ | ⟨h234a, h234b, h234c, h234d, h234e⟩
                                  · rcases h235 with ⟨h235a, h235b, h235c, h235d, h235e⟩ | ⟨h235a, h235b, h235c, h235d, h235e⟩
                                    · rcases h245 with ⟨h245a, h245b, h245c, h245d, h245e⟩ | ⟨h245a, h245b, h245c, h245d, h245e⟩
                                      · rcases h345 with ⟨h345a, h345b, h345c, h345d, h345e⟩ | ⟨h345a, h345b, h345c, h345d, h345e⟩
                                        · linarith only [ht, h012c, h013d, h034c, h125c, h345c, h245e]
                                        · linarith only [ht, h045c, h014a, h134e, h345c]
                                      · linarith only [ht, h012c, h014d, h045c, h125c, h245a]
                                    · linarith only [ht, h012c, h013d, h125c, h235a, h035c]
                                  · linarith only [ht, h012c, h014d, h034b, h234a, h124c]
                                · linarith only [ht, h012c, h014d, h145a, h045c, h125b]
                              · linarith only [ht, h012c, h013d, h135a, h125b, h035c]
                            · linarith only [ht, h013d, h014c, h034c, h134a]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, h012e, h023c, h123c]
                      · rcases h124 with ⟨h124a, h124b, h124c, h124d, h124e⟩ | ⟨h124a, h124b, h124c, h124d, h124e⟩
                        · linarith only [ht, r02.2, r23.1, h123c, h124c, h024c]
                        · rcases h125 with ⟨h125a, h125b, h125c, h125d, h125e⟩ | ⟨h125a, h125b, h125c, h125d, h125e⟩
                          · linarith only [ht, r02.2, r23.1, h123c, h125c, h025c]
                          · rcases h134 with ⟨h134a, h134b, h134c, h134d, h134e⟩ | ⟨h134a, h134b, h134c, h134d, h134e⟩
                            · rcases h135 with ⟨h135a, h135b, h135c, h135d, h135e⟩ | ⟨h135a, h135b, h135c, h135d, h135e⟩
                              · rcases h145 with ⟨h145a, h145b, h145c, h145d, h145e⟩ | ⟨h145a, h145b, h145c, h145d, h145e⟩
                                · linarith only [ht, h014e, h145c, h045c]
                                · rcases h234 with ⟨h234a, h234b, h234c, h234d, h234e⟩ | ⟨h234a, h234b, h234c, h234d, h234e⟩
                                  · rcases h235 with ⟨h235a, h235b, h235c, h235d, h235e⟩ | ⟨h235a, h235b, h235c, h235d, h235e⟩
                                    · rcases h245 with ⟨h245a, h245b, h245c, h245d, h245e⟩ | ⟨h245a, h245b, h245c, h245d, h245e⟩
                                      · linarith only [ht, h014a, h024e, h145c, h245c]
                                      · linarith only [ht, r01.2, r45.1, h012c, h124c, h245c]
                                    · linarith only [ht, h012b, h013d, h025c, h235a, h035c]
                                  · linarith only [ht, h012c, h014d, h034b, h234a, h124c]
                              · linarith only [ht, h013d, h015c, h035c, h135a]
                            · linarith only [ht, h013d, h014c, h034c, h134a]
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, h012e, h023c, h123c]
                      · rcases h124 with ⟨h124a, h124b, h124c, h124d, h124e⟩ | ⟨h124a, h124b, h124c, h124d, h124e⟩
                        · linarith only [ht, r02.2, r23.1, h123c, h124c, h024c]
                        · rcases h125 with ⟨h125a, h125b, h125c, h125d, h125e⟩ | ⟨h125a, h125b, h125c, h125d, h125e⟩
                          · linarith only [ht, r23.1, r34.2, h123c, h034c, h025a, h035b, h125c]
                          · rcases h134 with ⟨h134a, h134b, h134c, h134d, h134e⟩ | ⟨h134a, h134b, h134c, h134d, h134e⟩
                            · rcases h135 with ⟨h135a, h135b, h135c, h135d, h135e⟩ | ⟨h135a, h135b, h135c, h135d, h135e⟩
                              · linarith only [ht, r13.1, r34.2, h034c, h135c, h035c]
                              · rcases h145 with ⟨h145a, h145b, h145c, h145d, h145e⟩ | ⟨h145a, h145b, h145c, h145d, h145e⟩
                                · rcases h234 with ⟨h234a, h234b, h234c, h234d, h234e⟩ | ⟨h234a, h234b, h234c, h234d, h234e⟩
                                  · rcases h235 with ⟨h235a, h235b, h235c, h235d, h235e⟩ | ⟨h235a, h235b, h235c, h235d, h235e⟩
                                    · linarith only [ht, r01.2, r23.1, h012c, h013a, h034c, h135c, h124c, h235c, h234e]
                                    · linarith only [ht, r01.2, r35.1, h012c, h123c, h235c]
                                  · linarith only [ht, r01.2, r03.1, h012c, h034c, h124c, h234a]
                                · linarith only [ht, h015c, h014d, h145a, h045c]
                            · linarith only [ht, h013d, h014c, h034c, h134a]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, h012e, h023c, h123c]
                      · rcases h124 with ⟨h124a, h124b, h124c, h124d, h124e⟩ | ⟨h124a, h124b, h124c, h124d, h124e⟩
                        · linarith only [ht, r02.2, r23.1, h124c, h024c, h123c]
                        · rcases h125 with ⟨h125a, h125b, h125c, h125d, h125e⟩ | ⟨h125a, h125b, h125c, h125d, h125e⟩
                          · linarith only [ht, r02.2, r24.1, h025c, h125c, h124c]
                          · rcases h134 with ⟨h134a, h134b, h134c, h134d, h134e⟩ | ⟨h134a, h134b, h134c, h134d, h134e⟩
                            · rcases h135 with ⟨h135a, h135b, h135c, h135d, h135e⟩ | ⟨h135a, h135b, h135c, h135d, h135e⟩
                              · linarith only [ht, r13.1, r34.2, h034c, h135c, h035c]
                              · rcases h145 with ⟨h145a, h145b, h145c, h145d, h145e⟩ | ⟨h145a, h145b, h145c, h145d, h145e⟩
                                · linarith only [ht, r04.2, r35.1, h045c, h135c, h134a, h145c]
                                · rcases h234 with ⟨h234a, h234b, h234c, h234d, h234e⟩ | ⟨h234a, h234b, h234c, h234d, h234e⟩
                                  · rcases h235 with ⟨h235a, h235b, h235c, h235d, h235e⟩ | ⟨h235a, h235b, h235c, h235d, h235e⟩
                                    · linarith only [ht, r01.2, r23.1, h012c, h013a, h034c, h135c, h124c, h234e, h235c]
                                    · linarith only [ht, r01.2, r35.1, h012c, h123c, h235c]
                                  · linarith only [ht, r01.2, r03.1, h012c, h034c, h124c, h234a]
                            · linarith only [ht, r01.2, r35.1, h014c, h034c, h035c, h134a]
                · rcases h035 with ⟨h035a, h035b, h035c, h035d, h035e⟩ | ⟨h035a, h035b, h035c, h035d, h035e⟩
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, h012e, h023c, h123c]
                      · rcases h124 with ⟨h124a, h124b, h124c, h124d, h124e⟩ | ⟨h124a, h124b, h124c, h124d, h124e⟩
                        · linarith only [ht, r23.1, r35.2, h024a, h035c, h123c, h124c, h034b]
                        · rcases h125 with ⟨h125a, h125b, h125c, h125d, h125e⟩ | ⟨h125a, h125b, h125c, h125d, h125e⟩
                          · linarith only [ht, r02.2, r23.1, h025c, h123c, h125c]
                          · rcases h134 with ⟨h134a, h134b, h134c, h134d, h134e⟩ | ⟨h134a, h134b, h134c, h134d, h134e⟩
                            · linarith only [ht, r13.1, r35.2, h034c, h035c, h134c]
                            · rcases h135 with ⟨h135a, h135b, h135c, h135d, h135e⟩ | ⟨h135a, h135b, h135c, h135d, h135e⟩
                              · rcases h145 with ⟨h145a, h145b, h145c, h145d, h145e⟩ | ⟨h145a, h145b, h145c, h145d, h145e⟩
                                · rcases h234 with ⟨h234a, h234b, h234c, h234d, h234e⟩ | ⟨h234a, h234b, h234c, h234d, h234e⟩
                                  · linarith only [ht, r23.1, r35.2, h013a, h035c, h134c, h234c]
                                  · linarith only [ht, r01.2, r34.1, h012c, h123c, h234c]
                                · linarith only [ht, h015c, h014d, h045c, h145a]
                              · linarith only [ht, h013d, h015c, h035c, h135a]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, h012e, h023c, h123c]
                      · rcases h124 with ⟨h124a, h124b, h124c, h124d, h124e⟩ | ⟨h124a, h124b, h124c, h124d, h124e⟩
                        · linarith only [ht, r02.2, r23.1, h123c, h124c, h024c]
                        · rcases h125 with ⟨h125a, h125b, h125c, h125d, h125e⟩ | ⟨h125a, h125b, h125c, h125d, h125e⟩
                          · linarith only [ht, r23.1, r35.2, h125c, h035c, h045b, h025a, h123c, h034b]
                          · rcases h134 with ⟨h134a, h134b, h134c, h134d, h134e⟩ | ⟨h134a, h134b, h134c, h134d, h134e⟩
                            · linarith only [ht, r13.1, r35.2, h034c, h035c, h134c]
                            · rcases h135 with ⟨h135a, h135b, h135c, h135d, h135e⟩ | ⟨h135a, h135b, h135c, h135d, h135e⟩
                              · rcases h145 with ⟨h145a, h145b, h145c, h145d, h145e⟩ | ⟨h145a, h145b, h145c, h145d, h145e⟩
                                · linarith only [ht, r34.1, r35.2, h045c, h035c, h135a, h134c, h145b, h034b]
                                · rcases h234 with ⟨h234a, h234b, h234c, h234d, h234e⟩ | ⟨h234a, h234b, h234c, h234d, h234e⟩
                                  · linarith only [ht, r23.1, r35.2, h013a, h035c, h134c, h234c]
                                  · linarith only [ht, r01.2, r34.1, h012c, h123c, h234c]
                              · linarith only [h015a, h035c, h045b, h034b, h135a]
                  · rcases h045 with ⟨h045a, h045b, h045c, h045d, h045e⟩ | ⟨h045a, h045b, h045c, h045d, h045e⟩
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, h012e, h023c, h123c]
                      · rcases h124 with ⟨h124a, h124b, h124c, h124d, h124e⟩ | ⟨h124a, h124b, h124c, h124d, h124e⟩
                        · linarith only [ht, r23.1, r45.2, h024a, h045c, h124c, h123c]
                        · rcases h125 with ⟨h125a, h125b, h125c, h125d, h125e⟩ | ⟨h125a, h125b, h125c, h125d, h125e⟩
                          · linarith only [ht, r02.2, r24.1, h124c, h025c, h125c]
                          · rcases h134 with ⟨h134a, h134b, h134c, h134d, h134e⟩ | ⟨h134a, h134b, h134c, h134d, h134e⟩
                            · linarith only [ht, h013e, h034c, h134c]
                            · rcases h135 with ⟨h135a, h135b, h135c, h135d, h135e⟩ | ⟨h135a, h135b, h135c, h135d, h135e⟩
                              · linarith only [ht, r01.2, r34.1, h012c, h023e, h135c, h123c, h035c, h134c]
                              · rcases h145 with ⟨h145a, h145b, h145c, h145d, h145e⟩ | ⟨h145a, h145b, h145c, h145d, h145e⟩
                                · rcases h234 with ⟨h234a, h234b, h234c, h234d, h234e⟩ | ⟨h234a, h234b, h234c, h234d, h234e⟩
                                  · linarith only [ht, h023e, h034c, h234c]
                                  · linarith only [ht, r01.2, r34.1, h012c, h123c, h234c]
                                · linarith only [ht, h015c, h014d, h045c, h145a]
                    · rcases h123 with ⟨h123a, h123b, h123c, h123d, h123e⟩ | ⟨h123a, h123b, h123c, h123d, h123e⟩
                      · linarith only [ht, h012e, h023c, h123c]
                      · rcases h124 with ⟨h124a, h124b, h124c, h124d, h124e⟩ | ⟨h124a, h124b, h124c, h124d, h124e⟩
                        · linarith only [ht, r02.2, r23.1, h124c, h123c, h024c]
                        · rcases h125 with ⟨h125a, h125b, h125c, h125d, h125e⟩ | ⟨h125a, h125b, h125c, h125d, h125e⟩
                          · linarith only [ht, h023e, h125c, h025a, h123c, h035b]
                          · rcases h134 with ⟨h134a, h134b, h134c, h134d, h134e⟩ | ⟨h134a, h134b, h134c, h134d, h134e⟩
                            · linarith only [ht, h013e, h034c, h134c]
                            · rcases h135 with ⟨h135a, h135b, h135c, h135d, h135e⟩ | ⟨h135a, h135b, h135c, h135d, h135e⟩
                              · linarith only [ht, h135c, h035a, h045b, h134c, h034e]
                              · rcases h145 with ⟨h145a, h145b, h145c, h145d, h145e⟩ | ⟨h145a, h145b, h145c, h145d, h145e⟩
                                · linarith only [ht, h014e, h145c, h045c]
                                · rcases h234 with ⟨h234a, h234b, h234c, h234d, h234e⟩ | ⟨h234a, h234b, h234c, h234d, h234e⟩
                                  · linarith only [ht, h023e, h034c, h234c]
                                  · linarith only [ht, r01.2, r34.1, h012c, h234c, h123c]

#print axioms three_le
end SendovSixDirections
