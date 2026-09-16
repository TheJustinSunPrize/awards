import Mathlib

/-!
# Prime blocks for JSP-001007

Repair revision: explicit finite-block HasSum certificates, including q = 0.
This module is independently compilable. Its two transitive axiom reports
must pass before the downstream sieve construction is accepted.
See VERIFICATION.md for the actual verification status of this revision.
-/

set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

open scoped BigOperators

namespace JSP001007

/-- The primes in the half-open interval [q^2, (q+1)^2). -/
def primeBlock (q : ℕ) : Finset ℕ :=
  (Finset.Ico (q ^ 2) ((q + 1) ^ 2)).filter Nat.Prime

/-- The first square interval contains only 0, which is not prime. -/
@[simp]
lemma primeBlock_zero : primeBlock 0 = ∅ := by
  decide

private noncomputable def blockWeight (q : ℕ) : ℝ :=
  ∑ p ∈ primeBlock q, (1 : ℝ) / p

private lemma blockWeight_nonneg (q : ℕ) : 0 ≤ blockWeight q := by
  exact Finset.sum_nonneg fun _ _ => by positivity

private lemma blockWeight_le (C q : ℕ)
    (hc : (primeBlock q).card ≤ C) :
    blockWeight q ≤ (C : ℝ) * ((q : ℝ) ^ 2)⁻¹ := by
  by_cases hq : q = 0
  · subst q
    simp [blockWeight]
  have hqpos : 0 < (q : ℝ) ^ 2 := by positivity
  calc
    blockWeight q ≤ ∑ _p ∈ primeBlock q, ((q : ℝ) ^ 2)⁻¹ := by
      apply Finset.sum_le_sum
      intro p hp
      have hqp : q ^ 2 ≤ p :=
        (Finset.mem_Ico.mp (Finset.mem_filter.mp hp).1).1
      have hqpR : (q : ℝ) ^ 2 ≤ (p : ℝ) := by exact_mod_cast hqp
      simpa only [one_div] using one_div_le_one_div_of_le hqpos hqpR
    _ = ((primeBlock q).card : ℝ) * ((q : ℝ) ^ 2)⁻¹ := by
      simp only [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (C : ℝ) * ((q : ℝ) ^ 2)⁻¹ := by
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hc) (by positivity)

/-- A uniform bound on the number of primes in square intervals would make
    the sum of prime reciprocals converge. -/
theorem primeBlock_card_unbounded (C : ℕ) :
    ∃ q : ℕ, C < (primeBlock q).card := by
  classical
  by_contra h
  push_neg at h
  have hmajorant : Summable (fun q : ℕ => (C : ℝ) * ((q : ℝ) ^ 2)⁻¹) :=
    (Real.summable_nat_pow_inv.mpr (by norm_num : 1 < (2 : ℕ))).mul_left _
  have hw : Summable blockWeight :=
    hmajorant.of_nonneg_of_le blockWeight_nonneg (fun q => blockWeight_le C q (h q))
  -- Use exactly the indicator appearing in Mathlib's divergence theorem.
  let f : ℕ → ℝ :=
    Set.indicator {n : ℕ | n.Prime} (fun n => (1 : ℝ) / n)
  have hf : 0 ≤ f := by
    intro n
    exact Set.indicator_nonneg (fun _ _ => by positivity) n
  have hpartition : ∀ n : ℕ, ∃! q : ℕ,
      n ∈ (↑(Finset.Ico (q ^ 2) ((q + 1) ^ 2)) : Set ℕ) := by
    intro n
    refine ⟨n.sqrt, ?_, ?_⟩
    · simpa only [Finset.mem_coe, Finset.mem_Ico] using
        (Nat.eq_sqrt'.mp (rfl : n.sqrt = n.sqrt))
    · intro q hq
      exact Nat.eq_sqrt'.mpr (by
        simpa only [Finset.mem_coe, Finset.mem_Ico] using hq)
  -- Finset.hasSum supplies both finite-fiber summability and its exact sum.
  -- No nonexistent `summable_fintype`, no implicit tsum/subtype conversion.
  have hblock (q : ℕ) : HasSum
      (fun n : (↑(Finset.Ico (q ^ 2) ((q + 1) ^ 2)) : Set ℕ) => f n)
      (blockWeight q) := by
    have hsum : (∑ n ∈ Finset.Ico (q ^ 2) ((q + 1) ^ 2), f n) =
        blockWeight q := by
      simp only [f, Set.indicator_apply, Set.mem_setOf_eq,
        blockWeight, primeBlock, Finset.sum_filter]
    rw [← hsum]
    exact (Finset.Ico (q ^ 2) ((q + 1) ^ 2)).hasSum f
  have houter_eq :
      (fun q : ℕ =>
        ∑' n : (↑(Finset.Ico (q ^ 2) ((q + 1) ^ 2)) : Set ℕ), f n) =
      blockWeight := by
    funext q
    exact (hblock q).tsum_eq
  have houter : Summable (fun q : ℕ =>
      ∑' n : (↑(Finset.Ico (q ^ 2) ((q + 1) ^ 2)) : Set ℕ), f n) := by
    rw [houter_eq]
    exact hw
  have hall : Summable f :=
    (summable_partition (f := f) (s := fun q : ℕ =>
      (↑(Finset.Ico (q ^ 2) ((q + 1) ^ 2)) : Set ℕ)) hf hpartition).mpr
      ⟨fun q => (hblock q).summable, houter⟩
  exact not_summable_one_div_on_primes hall

/-- The square interval can be required to lie arbitrarily far out. -/
theorem large_primeBlock (K Q : ℕ) :
    ∃ q : ℕ, Q ≤ q ∧ K ≤ (primeBlock q).card := by
  obtain ⟨q, hq⟩ := primeBlock_card_unbounded (K + (Q + 1) ^ 2)
  refine ⟨q, ?_, by omega⟩
  have hsub : primeBlock q ⊆ Finset.range ((q + 1) ^ 2) := by
    intro p hp
    exact Finset.mem_range.mpr
      (Finset.mem_Ico.mp (Finset.mem_filter.mp hp).1).2
  have hcard : (primeBlock q).card ≤ (q + 1) ^ 2 := by
    simpa only [Finset.card_range] using Finset.card_le_card hsub
  by_contra hsmall
  have hqQ : q + 1 ≤ Q + 1 := by omega
  have hsquares : (q + 1) ^ 2 ≤ (Q + 1) ^ 2 :=
    Nat.pow_le_pow_left hqQ 2
  omega

#print axioms JSP001007.primeBlock_card_unbounded
#print axioms JSP001007.large_primeBlock

end JSP001007
