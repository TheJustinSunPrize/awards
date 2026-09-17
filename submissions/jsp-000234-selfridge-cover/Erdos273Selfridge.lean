/-
Copyright 2026 James-16.
Licensed under the Apache License, Version 2.0. See LICENSE and NOTICE.
Prepared with substantial OpenAI Codex assistance.
The mathematical construction is attributed to Selfridge. The explicit residues
are from idealombrer/erdos-273-covering-pm1; see the pinned source in NOTICE.
-/
import Erdos273Selfridge.CoveringSystem
import Mathlib.RingTheory.Ideal.Span
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.NormNum

namespace Erdos273Selfridge
open scoped Pointwise
set_option maxRecDepth 100000

def modulus : Fin 12 → ℕ := ![2, 4, 6, 10, 12, 18, 30, 36, 40, 60, 72, 180]
def residue : Fin 12 → ℕ := ![0, 1, 1, 7, 11, 9, 21, 15, 3, 15, 39, 39]

theorem modulus_two_le : ∀ i, 2 ≤ modulus i := by decide
theorem modulus_dvd_period : ∀ i, modulus i ∣ 360 := by decide
theorem modulus_injective : Function.Injective modulus := by decide
theorem modulus_prime : ∀ i, (modulus i + 1).Prime ∧ 3 ≤ modulus i + 1 := by decide

-- Finite checking produces ordinary proof terms checked by the Lean kernel.
set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem covers_period : ∀ n : Fin 360, ∃ i : Fin 12, n.val % modulus i = residue i := by
  decide

theorem covers_nat (n : ℕ) : ∃ i : Fin 12, n % modulus i = residue i := by
  obtain ⟨i, hi⟩ := covers_period ⟨n % 360, Nat.mod_lt n (by decide)⟩
  refine ⟨i, ?_⟩
  simpa only [Nat.mod_mod_of_dvd n (modulus_dvd_period i)] using hi

theorem covers_int (n : ℤ) : ∃ i : Fin 12, n % (modulus i : ℤ) = residue i := by
  have ht : 0 ≤ n % 360 := Int.emod_nonneg n (by decide)
  obtain ⟨i, hi⟩ := covers_nat (n % 360).toNat
  refine ⟨i, ?_⟩
  have hc := congrArg (fun x : ℕ ↦ (x : ℤ)) hi
  rw [Int.natCast_emod, Int.toNat_of_nonneg ht] at hc
  have hd : (modulus i : ℤ) ∣ 360 := by exact_mod_cast modulus_dvd_period i
  simpa only [Int.emod_emod_of_dvd n hd] using hc

/-- The exact strict-covering-system structure used by Formal Conjectures. -/
def selfridge : StrictCoveringSystem ℕ where
  ι := Fin 12
  residue := residue
  moduli := fun i ↦ Ideal.span {modulus i}
  unionCovers := by
    apply Set.eq_univ_of_forall
    intro n
    obtain ⟨i, hi⟩ := covers_nat n
    apply Set.mem_iUnion.mpr
    refine ⟨i, Set.mem_add.mpr ⟨residue i, by simp, modulus i * (n / modulus i), ?_, ?_⟩⟩
    · exact Ideal.mem_span_singleton.mpr (dvd_mul_right _ _)
    · rw [← hi]
      exact Nat.mod_add_div n (modulus i)
  ne_bot := by
    intro i hi
    have hz := Ideal.span_singleton_eq_bot.mp hi
    have := modulus_two_le i
    omega
  ne_top := by
    intro i hi
    have hd : modulus i ∣ 1 := Ideal.mem_span_singleton.mp (by rw [hi]; trivial)
    have := Nat.le_of_dvd (by decide : 0 < 1) hd
    have := modulus_two_le i
    omega
  injective_moduli := by
    intro i j hij
    apply modulus_injective
    change Ideal.span {modulus i} = Ideal.span {modulus j} at hij
    have hji : modulus j ∣ modulus i := Ideal.mem_span_singleton.mp (by
      rw [← hij]
      exact Ideal.mem_span_singleton_self (modulus i))
    have hij' : modulus i ∣ modulus j := Ideal.mem_span_singleton.mp (by
      rw [hij]
      exact Ideal.mem_span_singleton_self (modulus j))
    exact Nat.dvd_antisymm hij' hji

theorem selfridge_prime_moduli : ∀ i : selfridge.ι, ∃ p : ℕ,
    p.Prime ∧ 3 ≤ p ∧ selfridge.moduli i = Ideal.span {p - 1} := by
  intro i
  refine ⟨modulus i + 1, (modulus_prime i).1, (modulus_prime i).2, ?_⟩
  simp [selfridge]

/-- The solved p ≥ 3 variant, without the unproved p ≥ 5 conjecture. -/
theorem variants_three : ∃ c : StrictCoveringSystem ℕ, ∀ i, ∃ p : ℕ,
    p.Prime ∧ 3 ≤ p ∧ c.moduli i = Ideal.span {p - 1} :=
  ⟨selfridge, selfridge_prime_moduli⟩

end Erdos273Selfridge
