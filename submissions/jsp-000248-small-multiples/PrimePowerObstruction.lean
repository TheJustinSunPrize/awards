/-
Copyright (c) 2026 The JSP248 formalization contributors.
Released under Apache 2.0 license as described at
https://www.apache.org/licenses/LICENSE-2.0.
Authors: The JSP248 formalization contributors
-/
import Mathlib

/-!
# Prime-power obstructions for largest Egyptian-fraction denominators

New formalization for the exceptional-set branch of Erdős problem 292 / JSP248.
The elementary prime-power observation is attributed to Erdős and Graham in
Greg Martin, *Denser Egyptian fractions*, Acta Arith. 95 (2000), pp. 232–233.
This file does not prove Martin's exceptional-set counting asymptotic.

Only Mathlib is imported. The finite-set definition below includes denominator
1 and has the same mathematical meaning as the existing `Erdos292` definition;
it does not import or repackage that source's density-one proof.

Formalization developed in this workspace with Codex. Runtime validation is
recorded separately; this source does not make a claim about its own execution.
-/

namespace JSP248

open scoped BigOperators

def reciprocalSum (S : Finset ℕ) : ℚ := ∑ n ∈ S, (1 : ℚ) / n

/-- Distinct positive denominators, a maximum that is attained, and sum one.
In particular, the legitimate singleton representation `{1}` is allowed. -/
def IsLargestDenominator (n : ℕ) : Prop :=
  ∃ S : Finset ℕ, S ⊆ Finset.Icc 1 n ∧ n ∈ S ∧ reciprocalSum S = 1

def exceptional : Set ℕ := {n | ¬ IsLargestDenominator n}

/-- The reciprocal's norm is the prime-power part of its denominator. -/
lemma norm_reciprocal_eq (p n : ℕ) [Fact p.Prime] (hn : n ≠ 0) :
    padicNorm p ((1 : ℚ) / n) = (p : ℚ) ^ padicValNat p n := by
  have hnQ : (n : ℚ) ≠ 0 := by exact_mod_cast hn
  rw [padicNorm.eq_zpow_of_nonzero (one_div_ne_zero hnQ)]
  simp only [one_div, padicValRat.inv, padicValRat.of_nat, neg_neg, zpow_natCast]

/-- A unique denominator with maximal `p`-adic valuation determines the norm
of the entire reciprocal sum. Distinctness is supplied by the finite set. -/
theorem reciprocalSum_norm_of_unique_max_valuation
    (S : Finset ℕ) (p d : ℕ) [Fact p.Prime]
    (hpos : ∀ n ∈ S, 0 < n) (hd : d ∈ S)
    (hmax : ∀ n ∈ S, n ≠ d → padicValNat p n < padicValNat p d) :
    padicNorm p (reciprocalSum S) = (p : ℚ) ^ padicValNat p d := by
  classical
  have hpQ : 1 < (p : ℚ) := by
    exact_mod_cast (Fact.out : p.Prime).one_lt
  have hterm : padicNorm p ((1 : ℚ) / d) =
      (p : ℚ) ^ padicValNat p d := norm_reciprocal_eq p d (hpos d hd).ne'
  have hrest : padicNorm p (∑ n ∈ S.erase d, (1 : ℚ) / n) <
      (p : ℚ) ^ padicValNat p d := by
    apply padicNorm.sum_lt'
    · intro n hn
      obtain ⟨hne, hnS⟩ := Finset.mem_erase.mp hn
      rw [norm_reciprocal_eq p n (hpos n hnS).ne']
      exact pow_lt_pow_right₀ hpQ (hmax n hnS hne)
    · positivity
  have hne : padicNorm p (∑ n ∈ S.erase d, (1 : ℚ) / n) ≠
      padicNorm p ((1 : ℚ) / d) := by
    rw [hterm]
    exact ne_of_lt hrest
  calc
    padicNorm p (reciprocalSum S) =
        padicNorm p ((∑ n ∈ S.erase d, (1 : ℚ) / n) + (1 : ℚ) / d) := by
      congr 1
      exact (Finset.sum_erase_add S (fun n : ℕ ↦ (1 : ℚ) / n) hd).symm
    _ = max (padicNorm p (∑ n ∈ S.erase d, (1 : ℚ) / n))
        (padicNorm p ((1 : ℚ) / d)) := padicNorm.add_eq_max_of_ne hne
    _ = (p : ℚ) ^ padicValNat p d := by
      rw [hterm, max_eq_right hrest.le]

/-- If the unique maximal denominator valuation is positive, the reciprocal
sum is not any integer, a stronger conclusion than being different from one. -/
theorem reciprocalSum_not_integer_of_unique_max_valuation
    (S : Finset ℕ) (p d : ℕ) [Fact p.Prime]
    (hpos : ∀ n ∈ S, 0 < n) (hd : d ∈ S)
    (hmax : ∀ n ∈ S, n ≠ d → padicValNat p n < padicValNat p d)
    (hval : 0 < padicValNat p d) :
    ¬ (reciprocalSum S).isInt := by
  apply padicNorm.not_int_of_not_padic_int p
  rw [reciprocalSum_norm_of_unique_max_valuation S p d hpos hd hmax]
  apply one_lt_pow₀
  · exact_mod_cast (Fact.out : p.Prime).one_lt
  · exact hval.ne'

theorem reciprocalSum_ne_one_of_unique_max_valuation
    (S : Finset ℕ) (p d : ℕ) [Fact p.Prime]
    (hpos : ∀ n ∈ S, 0 < n) (hd : d ∈ S)
    (hmax : ∀ n ∈ S, n ≠ d → padicValNat p n < padicValNat p d)
    (hval : 0 < padicValNat p d) :
    reciprocalSum S ≠ 1 := by
  intro hsum
  have hnorm := reciprocalSum_norm_of_unique_max_valuation S p d hpos hd hmax
  rw [hsum, padicNorm.one] at hnorm
  have hpQ : 1 < (p : ℚ) := by
    exact_mod_cast (Fact.out : p.Prime).one_lt
  exact (ne_of_gt (one_lt_pow₀ hpQ hval.ne')) hnorm.symm

/-- Necessary cancellation condition: a denominator with positive valuation
must have another denominator with at least that valuation. -/
theorem exists_other_large_valuation_of_reciprocalSum_eq_one
    (S : Finset ℕ) (p d : ℕ) [Fact p.Prime]
    (hpos : ∀ n ∈ S, 0 < n) (hsum : reciprocalSum S = 1)
    (hd : d ∈ S) (hval : 0 < padicValNat p d) :
    ∃ n ∈ S, n ≠ d ∧ padicValNat p d ≤ padicValNat p n := by
  by_contra h
  have hmax : ∀ n ∈ S, n ≠ d → padicValNat p n < padicValNat p d := by
    intro n hn hne
    apply Nat.lt_of_not_ge
    intro hle
    exact h ⟨n, hn, hne, hle⟩
  exact reciprocalSum_ne_one_of_unique_max_valuation S p d hpos hd hmax hval hsum

lemma valuation_lt_of_lt_prime_power
    (p n k : ℕ) [Fact p.Prime] (hn : 0 < n) (hlt : n < p ^ k) :
    padicValNat p n < k := by
  have hle : p ^ padicValNat p n ≤ n :=
    Nat.le_of_dvd hn pow_padicValNat_dvd
  exact (pow_lt_pow_iff_right₀ (Fact.out : p.Prime).one_lt).mp (hle.trans_lt hlt)

/-- Every positive prime power is impossible as the largest denominator. -/
theorem prime_power_not_largestDenominator
    (p k : ℕ) (hp : p.Prime) (hk : 0 < k) :
    ¬ IsLargestDenominator (p ^ k) := by
  let : Fact p.Prime := ⟨hp⟩
  rintro ⟨S, hS, hd, hsum⟩
  have hpos : ∀ n ∈ S, 0 < n := by
    intro n hn
    exact (Finset.mem_Icc.mp (hS hn)).1
  have hmax : ∀ n ∈ S, n ≠ p ^ k →
      padicValNat p n < padicValNat p (p ^ k) := by
    intro n hn hne
    rw [padicValNat.prime_pow]
    apply valuation_lt_of_lt_prime_power p n k (hpos n hn)
    exact lt_of_le_of_ne (Finset.mem_Icc.mp (hS hn)).2 hne
  have hval : 0 < padicValNat p (p ^ k) := by
    simpa only [padicValNat.prime_pow] using hk
  exact reciprocalSum_ne_one_of_unique_max_valuation
    S p (p ^ k) hpos hd hmax hval hsum

/-- An explicit infinite obstruction family; its first member is `2`, not `1`. -/
theorem two_pow_succ_mem_exceptional (k : ℕ) : 2 ^ (k + 1) ∈ exceptional := by
  exact prime_power_not_largestDenominator 2 (k + 1) Nat.prime_two (by omega)

/-- Infinitely many integers cannot be the largest denominator. This is a
qualitative exceptional-set result, not Martin's counting asymptotic. -/
theorem exceptional_infinite : exceptional.Infinite := by
  apply Set.infinite_of_injective_forall_mem
    (f := fun k : ℕ ↦ 2 ^ (k + 1))
  · intro a b hab
    have hab' : a + 1 = b + 1 :=
      (pow_right_strictMono₀ (by decide : 1 < (2 : ℕ))).injective hab
    omega
  · exact two_pow_succ_mem_exceptional

/-- The boundary case is represented, so excluding exponent zero is necessary. -/
theorem one_isLargestDenominator : IsLargestDenominator 1 := by
  refine ⟨{1}, ?_, by simp, ?_⟩
  · intro n hn
    simp only [Finset.mem_singleton] at hn
    subst n
    simp
  · norm_num [reciprocalSum]

end JSP248

#print axioms JSP248.reciprocalSum_norm_of_unique_max_valuation
#print axioms JSP248.reciprocalSum_not_integer_of_unique_max_valuation
#print axioms JSP248.exists_other_large_valuation_of_reciprocalSum_eq_one
#print axioms JSP248.prime_power_not_largestDenominator
#print axioms JSP248.exceptional_infinite
#print axioms JSP248.one_isLargestDenominator
