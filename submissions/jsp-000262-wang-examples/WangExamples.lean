/-
Copyright (c) 2026 Contributors to this submission.
Released under the MIT license.

Formalization of the explicit nine- and ten-prime-factor examples in Han Wang,
"Port Fillings for Primary Pseudoperfect Numbers", arXiv:2605.21518v1,
Theorems 9.1, 10.1 and 11.1. Mathematical attribution remains with that author.
This file does not prove the infinitude conjecture in Erdős Problem 313.
-/
module
public import Mathlib.NumberTheory.LucasPrimality
public import Mathlib.Data.Nat.Squarefree
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar

@[expose] public section

set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

namespace JSP262

def N9 : ℕ := 5998279018951962402
def P10 : ℕ := 5998279018951962403
def N10 : ℕ := 35979351189199316534587473905773572006

def primes9 : Finset ℕ := {2, 3, 11, 17, 101, 157, 1979, 10093, 16879}
def primes10 : Finset ℕ := insert P10 primes9

/-- The standard reciprocal equation, with all prime divisors included. -/
def PrimaryPseudoperfect (n : ℕ) : Prop :=
  2 ≤ n ∧ Squarefree n ∧ (1 : ℚ) / n + ∑ p ∈ n.primeFactors, (1 : ℚ) / p = 1

lemma squarefree_product {s : Finset ℕ} (hs : ∀ p ∈ s, Nat.Prime p) :
    Squarefree (∏ p ∈ s, p) := by
  apply Finset.squarefree_prod_of_pairwise_isCoprime
  · intro p hp q hq hpq
    exact Nat.coprime_iff_isRelPrime.mp ((Nat.coprime_primes (hs p hp) (hs q hq)).mpr hpq)
  · intro p hp
    exact (hs p hp).squarefree

/-- Rephrase the defining equality in exactly the subtraction form of Erdős 313. -/
theorem original_equation {n : ℕ} (hn : PrimaryPseudoperfect n) :
    ∑ p ∈ n.primeFactors, (1 : ℚ) / p = 1 - (1 : ℚ) / n := by
  apply eq_sub_iff_add_eq.mpr
  simpa only [add_comm] using hn.2.2

theorem primes9_are_prime : ∀ p ∈ primes9, Nat.Prime p := by
  norm_num [primes9]

theorem product9 : (∏ p ∈ primes9, p) = N9 := by
  norm_num [primes9, N9]

theorem primeFactors9 : N9.primeFactors = primes9 := by
  rw [← product9]
  exact Nat.primeFactors_prod primes9_are_prime

theorem nine_prime_factors : N9.primeFactors.card = 9 := by
  rw [primeFactors9]
  decide

theorem nine_primary_pseudoperfect : PrimaryPseudoperfect N9 := by
  refine ⟨by norm_num [N9], ?_, ?_⟩
  · rw [← product9]
    exact squarefree_product primes9_are_prime
  rw [primeFactors9]
  norm_num [N9, primes9]

/-- Lucas/Pratt certification using the paper's base 3 and the complete factorization of p-1. -/
theorem prime_P10 : Nat.Prime P10 := by
  apply lucas_primality P10 (3 : ZMod P10)
  · unfold P10
    reduce_mod_char
  · intro q hq hdiv
    have hmem : q ∈ primes9 := by
      rw [← primeFactors9]
      exact Nat.mem_primeFactors.mpr
        ⟨hq, by simpa only [P10, N9] using hdiv, by norm_num [N9]⟩
    simp only [primes9, Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals
      unfold P10
      reduce_mod_char
      decide

theorem primes10_are_prime : ∀ p ∈ primes10, Nat.Prime p := by
  intro p hp
  rcases Finset.mem_insert.mp hp with rfl | hp
  · exact prime_P10
  · exact primes9_are_prime p hp

theorem product10 : (∏ p ∈ primes10, p) = N10 := by
  norm_num [primes10, primes9, P10, N10]

theorem primeFactors10 : N10.primeFactors = primes10 := by
  rw [← product10]
  exact Nat.primeFactors_prod primes10_are_prime

theorem ten_prime_factors : N10.primeFactors.card = 10 := by
  rw [primeFactors10]
  decide

theorem ten_primary_pseudoperfect : PrimaryPseudoperfect N10 := by
  refine ⟨by norm_num [N10], ?_, ?_⟩
  · rw [← product10]
    exact squarefree_product primes10_are_prime
  rw [primeFactors10]
  norm_num [N10, primes10, primes9, P10]

/-- Both values satisfy the original rational equation and have the asserted number of primes. -/
theorem wang_examples :
    PrimaryPseudoperfect 5998279018951962402 ∧
    (5998279018951962402 : ℕ).primeFactors.card = 9 ∧
    PrimaryPseudoperfect 35979351189199316534587473905773572006 ∧
    (35979351189199316534587473905773572006 : ℕ).primeFactors.card = 10 :=
  ⟨nine_primary_pseudoperfect, nine_prime_factors,
    ten_primary_pseudoperfect, ten_prime_factors⟩

#print axioms prime_P10
#print axioms wang_examples

end JSP262
