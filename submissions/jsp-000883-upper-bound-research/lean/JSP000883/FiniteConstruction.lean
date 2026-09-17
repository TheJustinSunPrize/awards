/-
Copyright 2026. Released under Apache-2.0.
Proof-source candidate for the exact finite construction in the original package.
No compiler pass is asserted by this file; see STATUS.json.
-/
import JSP000883.Arithmetic

namespace JSP000883
namespace ProductConstruction

open Finset

variable {k p : ℕ}

lemma Parameters.mod_pos (h : Parameters k p) : 0 < center k p % p := by
  have hn : center k p % p ≠ 0 := by
    intro hz
    exact h.not_dvd_center (Nat.dvd_of_mod_eq_zero hz)
  omega

lemma Parameters.left_multiples (h : Parameters k p)
    (hc : center k p % p ≤ k - p - 1) :
    ∃ a ∈ others k p, ∃ b ∈ others k p, a ≠ b ∧
      p ∣ term false (center k p) a ∧ p ∣ term false (center k p) b := by
  let m := center k p
  let r := m % p
  change r ≤ k - p - 1 at hc
  have hr0 : 0 < r := h.mod_pos
  have hrp : r < p := Nat.mod_lt m h.prime.pos
  have hp0 := h.prime.pos
  have hpI := h.p_lt_k
  have ha : r ∈ others k p := by
    apply Finset.mem_erase.mpr
    exact ⟨by omega, Finset.mem_Icc.mpr ⟨by omega, by omega⟩⟩
  have hb : r + p ∈ others k p := by
    apply Finset.mem_erase.mpr
    exact ⟨by omega, Finset.mem_Icc.mpr ⟨by omega, by omega⟩⟩
  have hd : p ∣ m - r := by
    refine ⟨m / p, ?_⟩
    have hm := Nat.mod_add_div m p
    change m - m % p = p * (m / p)
    omega
  have hd' : p ∣ m - (r + p) := by
    have hh : p ∣ (m - r) - p := Nat.dvd_sub hd (dvd_refl p)
    simpa only [Nat.sub_sub] using hh
  exact ⟨r, ha, r + p, hb, by omega, hd, hd'⟩

lemma Parameters.right_multiples (h : Parameters k p)
    (hc : ¬ center k p % p ≤ k - p - 1) :
    ∃ a ∈ others k p, ∃ b ∈ others k p, a ≠ b ∧
      p ∣ term true (center k p) a ∧ p ∣ term true (center k p) b := by
  let m := center k p
  let r := m % p
  change ¬ r ≤ k - p - 1 at hc
  have hr0 : 0 < r := h.mod_pos
  have hrp : r < p := Nat.mod_lt m h.prime.pos
  have hrm : r ≤ m := Nat.mod_le m p
  have hp0 := h.prime.pos
  have hpI := h.p_lt_k
  have hu := h.upper
  have ha : p - r ∈ others k p := by
    apply Finset.mem_erase.mpr
    exact ⟨by omega, Finset.mem_Icc.mpr ⟨by omega, by omega⟩⟩
  have hb : 2 * p - r ∈ others k p := by
    apply Finset.mem_erase.mpr
    exact ⟨by omega, Finset.mem_Icc.mpr ⟨by omega, by omega⟩⟩
  have hd : p ∣ m - r := by
    refine ⟨m / p, ?_⟩
    have hm := Nat.mod_add_div m p
    change m - m % p = p * (m / p)
    omega
  have hd1 : p ∣ m + (p - r) := by
    rw [show m + (p - r) = (m - r) + p by omega]
    exact Nat.dvd_add hd (dvd_refl p)
  have hd2 : p ∣ m + (2 * p - r) := by
    rw [show m + (2 * p - r) = ((m - r) + p) + p by omega]
    exact Nat.dvd_add (Nat.dvd_add hd (dvd_refl p)) (dvd_refl p)
  exact ⟨p - r, ha, 2 * p - r, hb, by omega, hd1, hd2⟩

/-- Abstract assembly of one side, including the genuine nondivisor. -/
lemma Parameters.side_result (h : Parameters k p) (right : Bool)
    (hmults : ∃ a ∈ others k p, ∃ b ∈ others k p, a ≠ b ∧
      p ∣ term right (center k p) a ∧ p ∣ term right (center k p) b) :
    ¬ center k p ∣ (top right (center k p) k).choose k ∧
      ∀ j ∈ indices k,
        term right (center k p) j ∣ (top right (center k p) k).choose k := by
  let M := cofactor k p
  let m := center k p
  let B := auxiliary right m k
  let C := (top right m k).choose k
  let q := quotient right k M
  have hk0 : 0 < k := by have := h.k_ge; omega
  have hC : C = M * B := coefficient_factor right k M hk0
  have hcross : p * B = term right m p * ∏ j ∈ others k p, q j :=
    h.cross_identity right
  have hqfactor (j : ℕ) (hj : j ∈ others k p) : term right m j = j * q j :=
    term_factor right (h.other_dvd_cofactor hj)
  have hpq (j : ℕ) (hj : j ∈ others k p) (hd : p ∣ term right m j) : p ∣ q j := by
    rw [hqfactor j hj] at hd
    exact (h.prime.dvd_mul.mp hd).resolve_left (h.not_dvd_other hj)
  obtain ⟨a, ha, b, hb, hab, hpa, hpb⟩ := hmults
  have hdivs : term right m p ∣ B ∧ ∀ j ∈ others k p, q j ∣ B :=
    cancel_cross_product h.prime.pos ha hb hab (hpq a ha hpa) (hpq b hb hpb) hcross
  have hcopQ : Nat.Coprime k (∏ j ∈ others k p, q j) := by
    apply Nat.coprime_prod_right_iff.mpr
    intro j hj
    have hj0 : 0 < j := by
      have := (Finset.mem_Icc.mp (Finset.mem_of_mem_erase hj)).1
      omega
    exact quotient_coprime right hk0 h.cofactor_pos hj0 (h.other_dvd_cofactor hj)
  have hcop : Nat.Coprime k (term right m p * ∏ j ∈ others k p, q j) :=
    Nat.coprime_mul_iff_right.mpr ⟨h.exceptional_term_coprime right, hcopQ⟩
  constructor
  · intro hd
    change k * M ∣ C at hd
    rw [hC] at hd
    have hkB : k ∣ B := by
      apply (Nat.mul_dvd_mul_iff_left h.cofactor_pos).mp
      simpa only [Nat.mul_comm k M] using hd
    have hkpB : k ∣ p * B := dvd_mul_of_dvd_right hkB p
    rw [hcross] at hkpB
    have heq : k = 1 := Nat.eq_one_of_dvd_coprimes hcop (dvd_refl k) hkpB
    have := h.k_ge
    omega
  · intro j hj
    change term right m j ∣ C
    rw [hC]
    by_cases hjp : j = p
    · subst j
      exact dvd_mul_of_dvd_right hdivs.1 M
    · have hjJ : j ∈ others k p := Finset.mem_erase.mpr ⟨hjp, hj⟩
      rw [hqfactor j hjJ]
      exact Nat.mul_dvd_mul (h.other_dvd_cofactor hjJ) (hdivs.2 j hjJ)

end ProductConstruction

/-- Universal finite construction, with every original conclusion retained. -/
theorem finiteConstruction : FiniteConstructionClaim := by
  intro k p hk hp hlo hup
  let h : ProductConstruction.Parameters k p := ⟨hk, hp, hlo, hup⟩
  change 2 * k ≤ candidateN k p ∧ candidateOffset k p < k ∧
    candidateN k p - candidateOffset k p = center k p ∧
    ¬ center k p ∣ (candidateN k p).choose k ∧
    (∀ i < k, i ≠ candidateOffset k p →
      (candidateN k p - i) ∣ (candidateN k p).choose k) ∧
    candidateN k p ≤ 3 * lcmInitial k
  by_cases hc : center k p % p ≤ k - p - 1
  · have hn : candidateN k p = center k p := by simp [candidateN, hc]
    have hi : candidateOffset k p = 0 := by simp [candidateOffset, hc]
    rw [hn, hi]
    have hs := h.side_result false (h.left_multiples hc)
    refine ⟨h.center_ge, by omega, by omega, hs.1, ?_, ?_⟩
    · intro i hik hi0
      exact hs.2 i (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
    · exact h.top_le false
  · have hn : candidateN k p = center k p + k - 1 := by simp [candidateN, hc]
    have hi : candidateOffset k p = k - 1 := by simp [candidateOffset, hc]
    rw [hn, hi]
    have hs := h.side_result true (h.right_multiples hc)
    refine ⟨h.top_ge true, by omega, by omega, hs.1, ?_, h.top_le true⟩
    intro i hik hi0
    have hj : k - 1 - i ∈ ProductConstruction.indices k :=
      Finset.mem_Icc.mpr ⟨by omega, by omega⟩
    have heq : center k p + k - 1 - i = center k p + (k - 1 - i) := by omega
    rw [heq]
    exact hs.2 (k - 1 - i) hj

/-- The construction supplies a witness in the exact set defining `leastN`. -/
theorem admissible_candidate {k p : ℕ} (hk : 9 ≤ k) (hp : p.Prime)
    (hlo : k < 2 * p) (hup : 3 * p + 2 ≤ 2 * k) :
    Admissible k (candidateN k p) := by
  obtain ⟨hn, hi, hcenter, hnot, hrest, _⟩ := finiteConstruction k p hk hp hlo hup
  refine ⟨hn, candidateOffset k p, hi, ?_, hrest⟩
  rwa [hcenter]

/-- This bound follows from an actual admissible witness, not an empty infimum. -/
theorem leastN_le_of_prime {k p : ℕ} (hk : 9 ≤ k) (hp : p.Prime)
    (hlo : k < 2 * p) (hup : 3 * p + 2 ≤ 2 * k) :
    (∃ n, Admissible k n) ∧ leastN k ≤ 3 * lcmInitial k := by
  have hadm := admissible_candidate hk hp hlo hup
  have hmin : leastN k ≤ candidateN k p := Nat.sInf_le hadm
  have hb := (finiteConstruction k p hk hp hlo hup).2.2.2.2.2
  exact ⟨⟨candidateN k p, hadm⟩, hmin.trans hb⟩

end JSP000883
