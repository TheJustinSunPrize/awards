/-
Copyright (c) 2026 Contributors to this submission.
Released under the MIT license.

General inheritance criteria for primary pseudoperfect numbers.
Mathematical attribution: Han Wang, "Port Fillings for Primary Pseudoperfect
Numbers", arXiv:2605.21518v1, Lemma 5.1 and Corollaries 5.2-5.3.
The reciprocal formulation below avoids an auxiliary arithmetic-derivative
definition. This does not establish infinitude or claim new mathematics.
-/
module
public import WangExamples
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

public section

namespace JSP262

/-- The reciprocal form of Wang's general inheritance equation. -/
theorem inheritance_iff {K C : ℕ} (hK : PrimaryPseudoperfect K) (hC : 0 < C)
    (hsC : Squarefree C) (hcop : K.Coprime C) :
    PrimaryPseudoperfect (K * C) ↔ (1 : ℚ) / C + K * ∑ p ∈ C.primeFactors, (1 : ℚ) / p = 1 := by
  have hK0 : K ≠ 0 := Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hK.1)
  have hC0 : C ≠ 0 := Nat.ne_of_gt hC
  have hKq : (K : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hK0
  have hCq : (C : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hC0
  have hbound : 2 ≤ K * C := le_trans hK.1 (Nat.le_mul_of_pos_right K hC)
  have hsKC : Squarefree (K * C) := (Nat.squarefree_mul hcop).mpr ⟨hK.2.1, hsC⟩
  rw [PrimaryPseudoperfect, and_iff_right hbound, and_iff_right hsKC,
    hcop.primeFactors_mul, Finset.sum_union hcop.disjoint_primeFactors, Nat.cast_mul]
  have hEq := hK.2.2
  constructor
  · intro h
    field_simp at hEq h ⊢
    nlinarith
  · intro h
    field_simp at hEq h ⊢
    nlinarith

/-- A complete criterion, including all the structural requirements on C. -/
theorem complete_inheritance_iff {K C : ℕ} (hK : PrimaryPseudoperfect K) :
    PrimaryPseudoperfect (K * C) ↔ 0 < C ∧ Squarefree C ∧ K.Coprime C ∧
      (1 : ℚ) / C + K * ∑ p ∈ C.primeFactors, (1 : ℚ) / p = 1 := by
  constructor
  · intro h
    have hc : 0 < C := Nat.pos_of_mul_pos_left
      (lt_of_lt_of_le (by decide : 0 < 2) h.1)
    have hs := h.2.1.of_mul_right
    have hcop := Nat.coprime_of_squarefree_mul h.2.1
    exact ⟨hc, hs, hcop, (inheritance_iff hK hc hs hcop).mp h⟩
  · rintro ⟨hc, hs, hcop, heq⟩
    exact (inheritance_iff hK hc hs hcop).mpr heq

/-- One new prime is possible precisely when it is K+1. -/
theorem one_prime_inheritance_iff {K q : ℕ} (hK : PrimaryPseudoperfect K)
    (hq : q.Prime) (hcop : K.Coprime q) :
    PrimaryPseudoperfect (K * q) ↔ q = K + 1 := by
  rw [inheritance_iff hK hq.pos hq.squarefree hcop, hq.primeFactors]
  simp only [Finset.sum_singleton]
  have hq0 : (q : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hq.ne_zero
  constructor
  · intro h
    have hrat : (q : ℚ) = (K : ℚ) + 1 := by
      field_simp at h
      linarith
    exact_mod_cast hrat
  · intro h
    have hrat : (q : ℚ) = (K : ℚ) + 1 := by exact_mod_cast h
    field_simp
    linarith

theorem one_prime_inheritance {K : ℕ} (hK : PrimaryPseudoperfect K)
    (hq : (K + 1).Prime) : PrimaryPseudoperfect (K * (K + 1)) := by
  apply (one_prime_inheritance_iff hK hq ?_).mpr rfl
  simp

/-- A cardinality certificate valid for any coprime extension. -/
theorem prime_factor_count {K C : ℕ} (hcop : K.Coprime C) :
    (K * C).primeFactors.card = K.primeFactors.card + C.primeFactors.card := by
  rw [hcop.primeFactors_mul, Finset.card_union_of_disjoint hcop.disjoint_primeFactors]

theorem one_prime_factor_count {K q : ℕ} (hq : q.Prime) (hcop : K.Coprime q) :
    (K * q).primeFactors.card = K.primeFactors.card + 1 := by
  rw [prime_factor_count hcop, hq.primeFactors]
  simp

/-- Wang's two-prime criterion. Integer subtraction avoids truncated subtraction. -/
theorem two_prime_inheritance_iff {K p q : ℕ} (hK : PrimaryPseudoperfect K)
    (hp : p.Prime) (hq : q.Prime) (hne : p ≠ q) (hcop : K.Coprime (p * q)) :
    PrimaryPseudoperfect (K * (p * q)) ↔ ((p : ℤ) - K) * ((q : ℤ) - K) = (K : ℤ)^2 + 1 := by
  have hpq : p.Coprime q := (Nat.coprime_primes hp hq).mpr hne
  have hsf : Squarefree (p * q) := (Nat.squarefree_mul hpq).mpr ⟨hp.squarefree,hq.squarefree⟩
  rw [inheritance_iff hK (Nat.mul_pos hp.pos hq.pos) hsf hcop,
    hpq.primeFactors_mul, Finset.sum_union hpq.disjoint_primeFactors,
    hp.primeFactors, hq.primeFactors]
  simp only [Finset.sum_singleton, Nat.cast_mul]
  have hp0 : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  have hq0 : (q : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hq.ne_zero
  constructor
  · intro h
    have hrat : ((p : ℚ) - K) * ((q : ℚ) - K) = (K : ℚ)^2 + 1 := by
      field_simp at h
      nlinarith
    exact_mod_cast hrat
  · intro h
    have hrat : ((p : ℚ) - K) * ((q : ℚ) - K) = (K : ℚ)^2 + 1 := by
      exact_mod_cast h
    field_simp
    nlinarith

#print axioms inheritance_iff
#print axioms complete_inheritance_iff
#print axioms one_prime_inheritance
#print axioms two_prime_inheritance_iff

end JSP262
