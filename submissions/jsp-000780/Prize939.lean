/-
Copyright 2025 The Formal Conjectures Authors.
Copyright 2026 inoader.
Licensed under the Apache License, Version 2.0. See LICENSE and NOTICE.

Mathematics: Nitaj (1995), with a specialization of Cohn's (1998) transformation.
Lean proofs: inoader with ChatGPT assistance, 2026.
The definitions and final statement follow Formal Conjectures revision
40e7c98697de6f66b8cbdbf641749ab39ed9c152; its unproved results are not imported.
-/
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Algebra.GCDMonoid.Nat
import Mathlib.Data.Nat.PrimeFin
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Set.Finite.Lemmas
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

namespace Nat

/-- Every prime factor occurs to exponent at least `k`. -/
def Full (k n : ℕ) : Prop := ∀ p ∈ n.primeFactors, p ^ k ∣ n

end Nat

/-- Collective coprimality, exactly as in the source statement. -/
@[reducible] def Finset.Coprime (S : Finset ℕ) : Prop := S.gcd id = 1

namespace Erdos939
open Nat

lemma full_mul_cube {a : ℕ} (ha : 0 < a) (h : Full 3 a) (b : ℕ) :
    Full 3 (a * b ^ 3) := by
  intro p hp
  have hprime := Nat.prime_of_mem_primeFactors hp
  rcases hprime.dvd_mul.mp (Nat.dvd_of_mem_primeFactors hp) with hpa | hpb
  · exact dvd_mul_of_dvd_left (h p (hprime.mem_primeFactors hpa (by omega))) _
  · exact dvd_mul_of_dvd_right (pow_dvd_pow_of_dvd (hprime.dvd_of_dvd_pow hpb) 3) _

/-- A common prime of the two linear factors must be 3; the invariant excludes it. -/
lemma linear_coprime {x y : ℕ} (hxy : x.Coprime y) (h3 : 3 ∣ x*y*(x+y)) :
    (x + 2*y).Coprime (2*x+y) := by
  apply Nat.coprime_of_dvd'
  intro p hp hu hv
  have hx : p ∣ 3*x := by
    convert Nat.dvd_sub (dvd_mul_of_dvd_right hv 2) hu using 1; omega
  have hy : p ∣ 3*y := by
    convert Nat.dvd_sub (dvd_mul_of_dvd_right hu 2) hv using 1; omega
  have hp3 : p ∣ 3 := by
    by_contra hn
    exact (Nat.not_coprime_of_dvd_of_dvd hp.one_lt
      ((hp.dvd_mul.mp hx).resolve_left hn) ((hp.dvd_mul.mp hy).resolve_left hn)) hxy
  have heq : p = 3 := ((Nat.dvd_prime (by decide : Nat.Prime 3)).mp hp3).resolve_left hp.ne_one
  subst p
  have hprod : 3 ∣ x ∨ 3 ∣ y ∨ 3 ∣ x+y := by
    simpa only [Nat.Prime.dvd_mul (by decide : Nat.Prime 3), or_assoc] using h3
  have hx' : 3 ∣ x := by rcases hprod with h | h | h <;> omega
  have hy' : 3 ∣ y := by omega
  exact False.elim ((Nat.not_coprime_of_dvd_of_dvd (by norm_num : 1 < 3) hx' hy') hxy)

/-- Cohn's transformation, arranged to keep all three entries positive.
The invariant `3 ∣ x*y*(x+y)` avoids a common-factor normalization. -/
lemma step {x y : ℕ} (hy : 0 < y) (hyx : y < x) (hxy : x.Coprime y)
    (hx : Full 3 x) (hyf : Full 3 y) (hz : Full 3 (x+y)) (h3 : 3 ∣ x*y*(x+y)) :
    let A := x*(x+2*y)^3
    let B := y*(2*x+y)^3
    let C := (x+y)*(x-y)^3
    B+C=A ∧ 0<B ∧ 0<C ∧ B.Coprime C ∧
      Full 3 B ∧ Full 3 C ∧ Full 3 A ∧ 3 ∣ B*C*A ∧ x+y<A := by
  dsimp
  have hid : y*(2*x+y)^3 + (x+y)*(x-y)^3 = x*(x+2*y)^3 := by
    have hsub : x-y+y=x := Nat.sub_add_cancel (by omega)
    conv_rhs => rw [← hsub]
    conv_lhs => lhs; rw [← hsub]
    conv_lhs => rhs; lhs; rw [← hsub]
    ring
  have hc : (x*(x+2*y)^3).Coprime (y*(2*x+y)^3) := by
    apply Nat.Coprime.mul_left
    · exact hxy.mul_right (((Nat.coprime_mul_right_add_right x y 2).mpr hxy).pow_right 3)
    · apply Nat.Coprime.mul_right
      · exact ((Nat.coprime_add_mul_right_left x y 2).mpr hxy).pow_left 3
      · exact (linear_coprime hxy h3).pow 3 3
  refine ⟨hid, by positivity, by
      have hs : 0 < x-y := by omega
      positivity, ?_, full_mul_cube hy hyf _,
    full_mul_cube (by omega) hz _, full_mul_cube (by omega) hx _, ?_, ?_⟩
  · rw [← hid] at hc
    rw [add_comm] at hc
    exact (Nat.coprime_add_self_left).mp hc |>.symm
  · have hp : Nat.Prime 3 := by decide
    rcases hp.dvd_mul.mp h3 with hab | hz3
    · rcases hp.dvd_mul.mp hab with hx3 | hy3
      · exact dvd_mul_of_dvd_right (dvd_mul_of_dvd_left hx3 _) _
      · exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left hy3 _) _) _
    · exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right (dvd_mul_of_dvd_left hz3 _) _) _
  · have hpow : x+2*y ≤ (x+2*y)^3 := Nat.le_self_pow (by omega) _
    nlinarith

/-- A stronger class of triples, with an invariant preserved by `step`. -/
structure Good (a b c : ℕ) : Prop where
  apos : 0 < a
  bpos : 0 < b
  coprime : a.Coprime b
  afull : Full 3 a
  bfull : Full 3 b
  cfull : Full 3 c
  sum : a+b=c
  div3 : 3 ∣ a*b*c

lemma good_ne {a b c : ℕ} (h : Good a b c) : a ≠ b := by
  intro heq
  have ha : a = 1 := by simpa only [← heq, Nat.coprime_self] using h.coprime
  have hb : b = 1 := by omega
  have hc : c = 2 := by have := h.sum; omega
  have := h.div3
  norm_num [ha, hb, hc] at this

lemma good_swap {a b c : ℕ} (h : Good a b c) : Good b a c :=
  ⟨h.bpos, h.apos, h.coprime.symm, h.bfull, h.afull, h.cfull,
    by simpa [add_comm] using h.sum, by simpa [mul_comm] using h.div3⟩

lemma larger_ordered {a b c : ℕ} (h : Good a b c) (hba : b < a) :
    ∃ a' b' c', Good a' b' c' ∧ c < c' := by
  obtain ⟨hs, hp, hq, hc, hf, hg, hh, hd, hgt⟩ :=
    step h.bpos hba h.coprime h.afull h.bfull
      (by simpa only [h.sum] using h.cfull) (by simpa only [h.sum] using h.div3)
  exact ⟨_, _, _, ⟨hp, hq, hc, hf, hg, hh, hs, hd⟩, by simpa only [h.sum] using hgt⟩

lemma larger {a b c : ℕ} (h : Good a b c) : ∃ a' b' c', Good a' b' c' ∧ c < c' := by
  rcases lt_or_gt_of_ne (good_ne h) with hab | hba
  · exact larger_ordered (good_swap h) hab
  · exact larger_ordered h hba

lemma full_pow (a k : ℕ) (hk : 3 ≤ k) : Full 3 (a^k) := by
  intro p hp
  have hprime := Nat.prime_of_mem_primeFactors hp
  exact (pow_dvd_pow_of_dvd (hprime.dvd_of_dvd_pow (Nat.dvd_of_mem_primeFactors hp)) 3).trans
    (pow_dvd_pow a hk)

lemma cube_full (a : ℕ) : Full 3 (a^3) := by
  simpa using full_mul_cube (by decide : 0 < 1) (by simp [Full] : Full 3 1) a

/-- Nitaj's explicit seed, with every property checked in Lean. -/
lemma seed : Good (2^3*3^5*73^3) (271^3) (919^3) := by
  have h243 : Full 3 243 := full_pow 3 5 (by decide)
  refine ⟨by norm_num, by norm_num, by decide, ?_, cube_full _, cube_full _, by norm_num,
    by norm_num⟩
  convert full_mul_cube (by decide : 0 < 243) h243 (2*73) using 1

/-- A finite nonempty set would have a largest total, contradicted by `larger`. -/
theorem good_triples_infinite : {t : ℕ × ℕ × ℕ | Good t.1 t.2.1 t.2.2}.Infinite := by
  intro hf
  obtain ⟨⟨a,b,c⟩, h, hm⟩ := Set.exists_max_image _ (fun t => t.2.2) hf
    ⟨(_,_,_), seed⟩
  obtain ⟨a', b', c', h', hgt⟩ := larger h
  have := hm (a',b',c') h'
  exact Nat.not_le_of_gt hgt this

theorem triples_infinite :
    {t : ℕ × ℕ × ℕ | ({t.1, t.2.1, t.2.2} : Finset ℕ).Coprime ∧
      0 < t.1 ∧ 0 < t.2.1 ∧ Full 3 t.1 ∧ Full 3 t.2.1 ∧ Full 3 t.2.2 ∧
      t.1 + t.2.1 = t.2.2}.Infinite := by
  apply good_triples_infinite.mono
  rintro ⟨a,b,c⟩ h
  refine ⟨?_, h.apos, h.bpos, h.afull, h.bfull, h.cfull, h.sum⟩
  simp only [Finset.Coprime, Finset.gcd_insert, Finset.gcd_singleton, normalize_eq]
  change Nat.gcd a (Nat.gcd b c) = 1
  rw [← Nat.gcd_assoc, h.coprime.gcd_eq_one, Nat.gcd_one_left]

/-- The exact solved triples variant, with the source's `answer(True)` reduced to `True`.
This does not resolve the separate questions for higher powerful exponents. -/
theorem erdos_939.variants.triples :
    True ↔ {(a,b,c) | ({a, b, c} : Finset ℕ).Coprime ∧
      0 < a ∧ 0 < b ∧
      (3).Full a ∧ (3).Full b ∧ (3).Full c ∧ a + b = c}.Infinite := by
  exact ⟨fun _ => triples_infinite, fun _ => trivial⟩

#print axioms triples_infinite
#print axioms erdos_939.variants.triples
end Erdos939
