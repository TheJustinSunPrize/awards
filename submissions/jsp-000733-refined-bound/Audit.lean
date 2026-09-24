import LogBound

open scoped BigOperators

namespace Erdos882Trial

/-- The finite bound with the original numerical-image condition expanded explicitly; the logarithmic theorem is separate. -/
theorem finite_bound_explicit (n : ℕ) (A : Finset ℕ)
    (hinterval : A ⊆ Finset.Icc 1 n)
    (hprimitive :
      ∀ x ∈ (A.powerset.filter (fun S ↦ S.Nonempty)).image (fun S ↦ ∑ a ∈ S, a),
      ∀ y ∈ (A.powerset.filter (fun S ↦ S.Nonempty)).image (fun S ↦ ∑ a ∈ S, a),
        x ∣ y → x = y)
    (hk : 2 ≤ A.card) :
    4 ^ A.card ≤ 32 * A.card * n ^ 2 := by
  exact admissible_squared_bound
    ((admissible_iff_interval_image n A).mpr ⟨hinterval, hprimitive⟩) hk

#print HasPrimitiveSubsetSums
#print Admissible
#print PrimitiveImageCondition
#check @admissible_squared_bound
#check @finite_bound_explicit
#check @maximumSize_refined_upper_bound
#check @refined_upper_bound
#print admissibleFamily
#print maximumSize
#check @maximumSize_definition_alignment
#print axioms powerset_centered_sum_sq
#print axioms integer_energy_lower_bound
#print axioms distinct_subset_sums_squared_bound
#print axioms primitive_condition_iff_image
#print axioms admissible_iff_interval_image
#print axioms subset_sum_injective_of_primitive
#print axioms admissible_squared_bound
#print axioms finite_bound_explicit
#print axioms maximumSize_attained
#print axioms maximumSize_characterization
#print axioms maximumSize_definition_alignment
#print axioms logarithmic_bound_of_squared
#print axioms admissible_refined_upper_bound
#print axioms maximumSize_refined_upper_bound
#print axioms refined_upper_bound

end Erdos882Trial
