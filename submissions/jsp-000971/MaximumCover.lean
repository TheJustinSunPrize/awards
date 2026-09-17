import Counting
import Mathlib.Data.Finset.Max
import Mathlib.Algebra.Group.Prod

namespace JSP000971
open Finset

def recenter (j : ℕ) (s : ℕ → ℤ × ℤ) : ℕ → ℤ × ℤ :=
  fun i => s (j + i) - s j

/-- Every path with a large maximum has a time j at which recentering produces
at least as many origin visits in the next n steps. The proof chooses the
first visit to a maximizing site; no stopping-time or probability assumption. -/
theorem maximum_le_shifted_origin (s : ℕ → ℤ × ℤ) (n : ℕ) :
    ∃ j ∈ range (n + 1), maximum s n ≤ visits (recenter j s) n 0 := by
  have hv : (visited s n).Nonempty := ⟨s 0, mem_image.mpr ⟨0, by simp, rfl⟩⟩
  obtain ⟨x, hx, heq⟩ := Finset.sup_mem_of_nonempty (f := visits s n) hv
  have hpos : 0 < visits s n x := (visits_pos_iff s n x).mpr hx
  let hits := (range (n + 1)).filter (fun i => s i = x)
  have hh : hits.Nonempty := card_pos.mp hpos
  let j := hits.min' hh
  have hj : j ∈ hits := min'_mem hits hh
  have hjr : j ∈ range (n + 1) := (mem_filter.mp hj).1
  have hjx : s j = x := (mem_filter.mp hj).2
  refine ⟨j, hjr, ?_⟩
  change (visited s n).sup (visits s n) ≤ _
  rw [← heq]
  change hits.card ≤ ((range (n + 1)).filter (fun i => recenter j s i = 0)).card
  apply card_le_card_of_injOn (fun i => i - j)
  · intro i hi
    change i - j ∈ _
    have hji : j ≤ i := min'_le hits i hi
    obtain ⟨hir, hix⟩ := mem_filter.mp hi
    apply mem_filter.mpr
    refine ⟨mem_range.mpr (by have := mem_range.mp hir; omega), ?_⟩
    simp only [recenter, Nat.add_sub_of_le hji, hix, hjx, sub_self]
  · intro a ha b hb hab
    have hja := min'_le hits a ha
    have hjb := min'_le hits b hb
    change a - j = b - j at hab
    change j ≤ a at hja
    change j ≤ b at hjb
    omega

#print axioms maximum_le_shifted_origin
end JSP000971
