/-
Copyright 2026 pcycho.
Licensed under the Apache License, Version 2.0. See LICENSE and NOTICE.

This extends inoader's Apache-2.0 formalization at awards PR #65,
commit b5b70857b2d77d6a060e00956beb8e19918b48f9.
The mathematics and explicit seed are due to J. H. E. Cohn (1998).
The original seed is on page 439 of DOI 10.1090/S0025-5718-98-00881-3.
-/
import Prize939

namespace Erdos939

/-- Not a perfect cube of a natural number. -/
def Noncube (a : ℕ) : Prop := ¬ ∃ r : ℕ, r ^ 3 = a

lemma cube_of_mul_cube {a b c : ℕ} (hb : 0 < b) (h : a * b ^ 3 = c ^ 3) :
    ∃ d : ℕ, d ^ 3 = a := by
  have hdiv : b ^ 3 ∣ c ^ 3 := by
    rw [← h]
    exact dvd_mul_left _ _
  obtain ⟨d, hd⟩ := (Nat.pow_dvd_pow_iff (by decide : 3 ≠ 0)).mp hdiv
  refine ⟨d, ?_⟩
  apply mul_right_cancel₀ (ne_of_gt (pow_pos hb 3))
  calc
    d ^ 3 * b ^ 3 = (b * d) ^ 3 := by ring
    _ = c ^ 3 := by rw [← hd]
    _ = a * b ^ 3 := h.symm

/-- Multiplication by a positive cube preserves failure to be a cube. -/
lemma noncube_mul_cube {a b : ℕ} (ha : Noncube a) (hb : 0 < b) :
    Noncube (a * b ^ 3) := by
  rintro ⟨c, hc⟩
  exact ha (cube_of_mul_cube hb hc.symm)

lemma noncube_of_between {a k : ℕ} (hlo : k ^ 3 < a) (hhi : a < (k + 1) ^ 3) :
    Noncube a := by
  rintro ⟨r, hr⟩
  rcases le_or_gt r k with hrk | hkr
  · have := Nat.pow_le_pow_left hrk 3
    omega
  · have := Nat.pow_le_pow_left (show k + 1 ≤ r by omega) 3
    omega

/-- The full positive coprime construction invariant, including each noncube condition. -/
structure GoodNoncube (a b c : ℕ) : Prop extends Good a b c where
  ancube : Noncube a
  bncube : Noncube b
  cncube : Noncube c

lemma good_noncube_swap {a b c : ℕ} (h : GoodNoncube a b c) : GoodNoncube b a c :=
  ⟨good_swap h.toGood, h.bncube, h.ancube, h.cncube⟩

lemma larger_ordered_noncube {a b c : ℕ} (h : GoodNoncube a b c) (hba : b < a) :
    ∃ a' b' c', GoodNoncube a' b' c' ∧ c < c' := by
  obtain ⟨hs, hp, hq, hc, hf, hg, hh, hd, hgt⟩ :=
    step h.bpos hba h.coprime h.afull h.bfull
      (by simpa only [h.sum] using h.cfull) (by simpa only [h.sum] using h.div3)
  refine ⟨_, _, _, ⟨⟨hp, hq, hc, hf, hg, hh, hs, hd⟩, ?_, ?_, ?_⟩,
    by simpa only [h.sum] using hgt⟩
  · exact noncube_mul_cube h.bncube (by omega)
  · exact noncube_mul_cube (by simpa only [h.sum] using h.cncube) (by omega)
  · exact noncube_mul_cube h.ancube (by omega)

lemma larger_noncube {a b c : ℕ} (h : GoodNoncube a b c) :
    ∃ a' b' c', GoodNoncube a' b' c' ∧ c < c' := by
  rcases lt_or_gt_of_ne (good_ne h.toGood) with hab | hba
  · exact larger_ordered_noncube (good_noncube_swap h) hab
  · exact larger_ordered_noncube h hba

def cohnX : ℕ := 9712247684771506604963490444281
def cohnY : ℕ := 32295800804958334401937923416351
def cohnZ : ℕ := 27474621855216870941749052236511

/-- Cohn's noncube seed; the three entries are 32 X³, 49 Y³, and 81 Z³. -/
lemma cohn_seed : GoodNoncube (32 * cohnX ^ 3) (49 * cohnY ^ 3) (81 * cohnZ ^ 3) := by
  have h32 : Nat.Full 3 32 := by simpa using full_pow 2 5 (by decide)
  have h16807 : Nat.Full 3 16807 := by simpa using full_pow 7 5 (by decide)
  have h81 : Nat.Full 3 81 := by simpa using full_pow 3 4 (by decide)
  have hbfull : Nat.Full 3 (49 * cohnY ^ 3) := by
    convert full_mul_cube (by decide : 0 < 16807) h16807 (cohnY / 7) using 1
    norm_num [cohnY]
  refine ⟨⟨by norm_num [cohnX], by norm_num [cohnY], by decide,
    full_mul_cube (by decide) h32 _, hbfull, full_mul_cube (by decide) h81 _,
    by norm_num [cohnX, cohnY, cohnZ], by norm_num [cohnX, cohnY, cohnZ]⟩,
    ?_, ?_, ?_⟩
  · exact noncube_mul_cube
      (noncube_of_between (k := 3) (by norm_num) (by norm_num)) (by norm_num [cohnX])
  · exact noncube_mul_cube
      (noncube_of_between (k := 3) (by norm_num) (by norm_num)) (by norm_num [cohnY])
  · exact noncube_mul_cube
      (noncube_of_between (k := 4) (by norm_num) (by norm_num)) (by norm_num [cohnZ])

theorem good_noncube_triples_infinite :
    {t : ℕ × ℕ × ℕ | GoodNoncube t.1 t.2.1 t.2.2}.Infinite := by
  intro hf
  obtain ⟨⟨a,b,c⟩, h, hm⟩ := Set.exists_max_image _ (fun t => t.2.2) hf
    ⟨(_,_,_), cohn_seed⟩
  obtain ⟨a', b', c', h', hgt⟩ := larger_noncube h
  have := hm (a',b',c') h'
  exact Nat.not_le_of_gt hgt this

/-- Cohn's strengthening: all three positive entries are separately noncubes.
Pairwise coprimality is explicit in the target, not merely a gcd-of-three condition. -/
theorem noncube_triples_infinite :
    {t : ℕ × ℕ × ℕ |
      0 < t.1 ∧ 0 < t.2.1 ∧ 0 < t.2.2 ∧
      t.1.Coprime t.2.1 ∧ t.1.Coprime t.2.2 ∧ t.2.1.Coprime t.2.2 ∧
      Nat.Full 3 t.1 ∧ Nat.Full 3 t.2.1 ∧ Nat.Full 3 t.2.2 ∧
      t.1 + t.2.1 = t.2.2 ∧ Noncube t.1 ∧ Noncube t.2.1 ∧ Noncube t.2.2}.Infinite := by
  apply good_noncube_triples_infinite.mono
  rintro ⟨a,b,c⟩ h
  refine ⟨h.apos, h.bpos, by have := h.sum; have := h.apos; omega,
    h.coprime, ?_, ?_, h.afull, h.bfull, h.cfull, h.sum, h.ancube, h.bncube, h.cncube⟩
  · rw [← h.sum]
    exact Nat.coprime_self_add_right.mpr h.coprime
  · rw [← h.sum]
    exact Nat.coprime_add_self_right.mpr h.coprime.symm

#print axioms noncube_mul_cube
#print axioms cohn_seed
#print axioms noncube_triples_infinite
end Erdos939
