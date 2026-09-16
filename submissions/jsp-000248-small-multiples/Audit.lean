/-
Copyright (c) 2026 The JSP248 formalization contributors.
Released under Apache 2.0 license as described at
https://www.apache.org/licenses/LICENSE-2.0.
-/
import SmallMultipleObstruction

namespace JSP248

open scoped BigOperators

/-- The principal partial result with the actual denominator predicates expanded.
This quantifies over every finite set of distinct positive denominators. -/
theorem small_multiple_expanded
    (m p k : ℕ) (hm : 0 < m) (hp : p.Prime)
    (hsmall : m * m.factorial < p) (hk : 0 < k) :
    ¬ ∃ S : Finset ℕ,
      (∀ d ∈ S, 1 ≤ d ∧ d ≤ m * p ^ k) ∧
      m * p ^ k ∈ S ∧ (∑ d ∈ S, (1 : ℚ) / d) = 1 := by
  rintro ⟨S, hS, hn, hsum⟩
  apply small_multiple_prime_power_not_largestDenominator m p k hm hp hsmall hk
  exact ⟨S, fun d hd => Finset.mem_Icc.mpr (hS d hd), hn, hsum⟩

/-- A genuinely composite infinite family beyond the prime-power special case. -/
theorem two_mul_five_pow_succ_not_largest (k : ℕ) :
    ¬ IsLargestDenominator (2 * 5 ^ (k + 1)) := by
  apply small_multiple_prime_power_not_largestDenominator 2 5 (k + 1)
  · norm_num
  · norm_num
  · norm_num
  · omega

theorem two_mul_five_pow_succ_injective :
    Function.Injective (fun k : ℕ => 2 * 5 ^ (k + 1)) := by
  intro a b h
  have hp : 5 ^ (a + 1) = 5 ^ (b + 1) := Nat.eq_of_mul_eq_mul_left (by decide) h
  have hs : a + 1 = b + 1 :=
    (pow_right_strictMono₀ (by decide : 1 < (5 : ℕ))).injective hp
  omega

end JSP248

#print JSP248.IsLargestDenominator
#print JSP248.reciprocalSum
#check JSP248.small_multiple_prime_power_not_largestDenominator
#check JSP248.small_multiple_expanded
#print axioms JSP248.small_multiple_expanded
#print axioms JSP248.two_mul_five_pow_succ_not_largest
#print axioms JSP248.two_mul_five_pow_succ_injective
