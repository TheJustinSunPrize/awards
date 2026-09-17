/-
Copyright 2026. Released under Apache-2.0; see LICENSE and NOTICE.
Erdős 1063 / JSP-000883: integer-product proof of the two-sided construction.
This is a proof-source candidate, not a recorded successful Lean build.
The quotient/coprimality approach was developed after inspecting pcycho's
formalization of Cambie's older bound; see docs/ATTRIBUTION.md.
-/
import JSP000883.Targets

-- Catch an escaped binder instead of silently generalizing it. Local to this file.
set_option autoImplicit false

namespace JSP000883
namespace ProductConstruction

open Finset

abbrev indices (k : ℕ) : Finset ℕ := Icc 1 (k - 1)
abbrev others (k p : ℕ) : Finset ℕ := (indices k).erase p
abbrev cofactor (k p : ℕ) : ℕ := lcmInitial k / p

def term (right : Bool) (m j : ℕ) : ℕ := if right then m + j else m - j
def quotient (right : Bool) (k M j : ℕ) : ℕ :=
  if right then k * (M / j) + 1 else k * (M / j) - 1
def top (right : Bool) (m k : ℕ) : ℕ := if right then m + k - 1 else m
def auxiliary (right : Bool) (m k : ℕ) : ℕ :=
  if right then (m + k - 1).choose (k - 1) else (m - 1).choose (k - 1)

structure Parameters (k p : ℕ) : Prop where
  k_ge : 9 ≤ k
  prime : p.Prime
  lower : k < 2 * p
  upper : 3 * p + 2 ≤ 2 * k

variable {k p : ℕ}

lemma lcm_pos (k : ℕ) : 0 < lcmInitial k := by
  apply Nat.pos_of_ne_zero
  apply Finset.lcm_ne_zero_iff.mpr
  intro j hj
  have := (Finset.mem_Icc.mp hj).1
  change j ≠ 0
  omega

lemma Parameters.p_ge_five (h : Parameters k p) : 5 ≤ p := by
  have := h.k_ge
  have := h.lower
  omega

lemma Parameters.p_lt_k (h : Parameters k p) : p < k := by
  have := h.upper
  have := h.prime.pos
  omega

lemma Parameters.p_mem (h : Parameters k p) : p ∈ indices k := by
  have := h.p_lt_k
  have := h.prime.pos
  exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩

/-- Below `2*p` the only positive multiple of `p` is `p` itself. -/
lemma not_dvd_of_between {p j : ℕ} (hp : 0 < p) (hj : 0 < j)
    (hjlt : j < 2 * p) (hjne : j ≠ p) : ¬ p ∣ j := by
  rintro ⟨a, ha⟩
  have ha0 : a ≠ 0 := by
    intro hz
    simp only [hz, Nat.mul_zero] at ha
    omega
  have ha1 : a = 1 := by
    by_contra hn
    have ha2 : 2 ≤ a := by omega
    have hmul : 2 * p ≤ p * a := by nlinarith
    omega
  apply hjne
  simpa only [ha1, Nat.mul_one] using ha

lemma Parameters.not_dvd_k (h : Parameters k p) : ¬ p ∣ k :=
  not_dvd_of_between h.prime.pos (by have := h.k_ge; omega) h.lower
    (by have := h.p_lt_k; omega)

lemma Parameters.not_dvd_other (h : Parameters k p) {j : ℕ}
    (hj : j ∈ others k p) : ¬ p ∣ j := by
  obtain ⟨hjp, hjI⟩ := Finset.mem_erase.mp hj
  obtain ⟨hj1, hjk⟩ := Finset.mem_Icc.mp hjI
  exact not_dvd_of_between h.prime.pos (by omega)
    (by have := h.lower; omega) hjp

lemma Parameters.p_mul_cofactor (h : Parameters k p) :
    p * cofactor k p = lcmInitial k := by
  exact Nat.mul_div_cancel' (Finset.dvd_lcm (f := id) h.p_mem)

lemma Parameters.cofactor_pos (h : Parameters k p) : 0 < cofactor k p := by
  have hpL : p ∣ lcmInitial k := Finset.dvd_lcm (f := id) h.p_mem
  exact Nat.div_pos (Nat.le_of_dvd (lcm_pos k) hpL) h.prime.pos

/-- Removing `p` from the LCM removes no divisor indexed by `others`. -/
lemma Parameters.other_dvd_cofactor (h : Parameters k p) {j : ℕ}
    (hj : j ∈ others k p) : j ∣ cofactor k p := by
  have hjL : j ∣ lcmInitial k :=
    Finset.dvd_lcm (f := id) (Finset.mem_of_mem_erase hj)
  have hcop : Nat.Coprime j p :=
    (h.prime.coprime_iff_not_dvd.mpr (h.not_dvd_other hj)).symm
  apply hcop.dvd_of_dvd_mul_left
  rwa [h.p_mul_cofactor]

/-- An elementary substitute for computing `v_p(lcm)`: the cofactor divides
    a product all of whose factors are coprime to `p`. -/
lemma Parameters.coprime_p_cofactor (h : Parameters k p) :
    Nat.Coprime p (cofactor k p) := by
  let P : ℕ := ∏ j ∈ others k p, j
  have hLP : lcmInitial k ∣ p * P := by
    apply Finset.lcm_dvd
    intro j hj
    change j ∣ p * P
    by_cases hjp : j = p
    · subst j
      exact dvd_mul_right p P
    · have hjJ : j ∈ others k p := Finset.mem_erase.mpr ⟨hjp, hj⟩
      exact dvd_mul_of_dvd_right (Finset.dvd_prod_of_mem id hjJ) p
  have hMP : cofactor k p ∣ P := by
    apply (Nat.mul_dvd_mul_iff_left h.prime.pos).mp
    rwa [h.p_mul_cofactor]
  have hcop : Nat.Coprime p P := by
    apply Nat.coprime_prod_right_iff.mpr
    intro j hj
    exact h.prime.coprime_iff_not_dvd.mpr (h.not_dvd_other hj)
  exact hcop.coprime_dvd_right hMP

lemma Parameters.coprime_p_center (h : Parameters k p) :
    Nat.Coprime p (center k p) := by
  change Nat.Coprime p (k * cofactor k p)
  exact Nat.coprime_mul_iff_right.mpr
    ⟨h.prime.coprime_iff_not_dvd.mpr h.not_dvd_k, h.coprime_p_cofactor⟩

lemma Parameters.not_dvd_center (h : Parameters k p) : ¬ p ∣ center k p := by
  intro hd
  have heq := Nat.eq_one_of_dvd_coprimes h.coprime_p_center (dvd_refl p) hd
  exact h.prime.ne_one heq

lemma Parameters.cofactor_ge_two (h : Parameters k p) : 2 ≤ cofactor k p := by
  apply Nat.le_of_dvd h.cofactor_pos
  apply h.other_dvd_cofactor
  have := h.k_ge
  have := h.p_ge_five
  exact Finset.mem_erase.mpr ⟨by omega, Finset.mem_Icc.mpr ⟨by omega, by omega⟩⟩

lemma Parameters.center_ge (h : Parameters k p) : 2 * k ≤ center k p := by
  change 2 * k ≤ k * cofactor k p
  nlinarith [h.cofactor_ge_two]

lemma Parameters.center_lt_two_lcm (h : Parameters k p) :
    center k p < 2 * lcmInitial k := by
  have hh := Nat.mul_lt_mul_of_pos_right h.lower h.cofactor_pos
  change k * cofactor k p < 2 * lcmInitial k
  rw [← h.p_mul_cofactor]
  nlinarith

lemma Parameters.k_sub_one_le_lcm (h : Parameters k p) : k - 1 ≤ lcmInitial k := by
  apply Nat.le_of_dvd (lcm_pos k)
  apply Finset.dvd_lcm (f := id)
  have := h.k_ge
  exact Finset.mem_Icc.mpr ⟨by omega, le_rfl⟩

lemma Parameters.top_ge (h : Parameters k p) (right : Bool) :
    2 * k ≤ top right (center k p) k := by
  have := h.center_ge
  have := h.k_ge
  cases right with
  | false =>
    change 2 * k ≤ center k p
    exact h.center_ge
  | true =>
    change 2 * k ≤ center k p + k - 1
    omega

lemma Parameters.top_le (h : Parameters k p) (right : Bool) :
    top right (center k p) k ≤ 3 * lcmInitial k := by
  have := h.center_lt_two_lcm
  have := h.k_sub_one_le_lcm
  have := h.k_ge
  cases right with
  | false =>
    change center k p ≤ 3 * lcmInitial k
    omega
  | true =>
    change center k p + k - 1 ≤ 3 * lcmInitial k
    omega

lemma term_factor (right : Bool) {k M j : ℕ} (hj : j ∣ M) :
    term right (k * M) j = j * quotient right k M j := by
  have hmul : k * M = j * (k * (M / j)) := by
    calc
      k * M = k * (j * (M / j)) := by rw [Nat.mul_div_cancel' hj]
      _ = j * (k * (M / j)) := by ac_rfl
  cases right with
  | false =>
    change k * M - j = j * (k * (M / j) - 1)
    rw [Nat.mul_sub_left_distrib, Nat.mul_one, hmul]
  | true =>
    change k * M + j = j * (k * (M / j) + 1)
    rw [Nat.mul_add, Nat.mul_one, hmul]

lemma quotient_coprime (right : Bool) {k M j : ℕ} (hk : 0 < k)
    (hM : 0 < M) (hj : 0 < j) (hd : j ∣ M) :
    Nat.Coprime k (quotient right k M j) := by
  have hdiv : 0 < M / j := Nat.div_pos (Nat.le_of_dvd hM hd) hj
  cases right with
  | false =>
    change Nat.Coprime k (k * (M / j) - 1)
    have hpos : 1 ≤ k * (M / j) := Nat.mul_pos hk hdiv
    have hc : Nat.Coprime (k * (M / j)) (k * (M / j) - 1) :=
      (Nat.coprime_self_sub_right hpos).mpr (Nat.coprime_one_right _)
    exact hc.coprime_dvd_left (dvd_mul_right k (M / j))
  | true =>
    change Nat.Coprime k (k * (M / j) + 1)
    simpa using (Nat.coprime_one_right k)

lemma Parameters.exceptional_term_coprime (h : Parameters k p) (right : Bool) :
    Nat.Coprime k (term right (center k p) p) := by
  have hkm : k ∣ center k p := dvd_mul_right k (cofactor k p)
  have hmcop : Nat.Coprime (center k p) p := h.coprime_p_center.symm
  have hpm : p ≤ center k p := by
    have := h.p_lt_k
    have := h.center_ge
    omega
  cases right with
  | false =>
    exact ((Nat.coprime_self_sub_right hpm).mpr hmcop).coprime_dvd_left hkm
  | true =>
    exact (Nat.coprime_self_add_right.mpr hmcop).coprime_dvd_left hkm

lemma prod_Icc_id (r : ℕ) : (∏ j ∈ Icc 1 r, j) = r.factorial := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [Finset.prod_Icc_succ_top (by omega : 1 ≤ r + 1), ih, Nat.factorial_succ]
    ac_rfl

lemma descending_product (m r : ℕ) :
    r.factorial * (m - 1).choose r = ∏ j ∈ Icc 1 r, (m - j) := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [Nat.factorial_succ, Finset.prod_Icc_succ_top (by omega : 1 ≤ r + 1)]
    calc
      (r + 1) * r.factorial * (m - 1).choose (r + 1) =
          r.factorial * ((m - 1).choose (r + 1) * (r + 1)) := by ac_rfl
      _ = r.factorial * ((m - 1).choose r * (m - 1 - r)) := by
        rw [Nat.choose_succ_right_eq]
      _ = (∏ j ∈ Icc 1 r, (m - j)) * (m - (r + 1)) := by
        rw [← Nat.mul_assoc, ih]
        congr 1
        omega

lemma ascFactorial_product (m r : ℕ) :
    (m + 1).ascFactorial r = ∏ j ∈ Icc 1 r, (m + j) := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [Nat.ascFactorial, ih,
      Finset.prod_Icc_succ_top (by omega : 1 ≤ r + 1)]
    rw [show m + 1 + r = m + (r + 1) by omega]
    ac_rfl

lemma ascending_product (m r : ℕ) :
    r.factorial * (m + r).choose r = ∏ j ∈ Icc 1 r, (m + j) := by
  rw [← Nat.ascFactorial_eq_factorial_mul_choose, ascFactorial_product]

lemma auxiliary_product (right : Bool) (m k : ℕ) (hk : 0 < k) :
    (k - 1).factorial * auxiliary right m k =
      ∏ j ∈ indices k, term right m j := by
  cases right with
  | false => exact descending_product m (k - 1)
  | true =>
    change (k - 1).factorial * (m + k - 1).choose (k - 1) =
      ∏ j ∈ Icc 1 (k - 1), (m + j)
    rw [show m + k - 1 = m + (k - 1) by omega]
    exact ascending_product m (k - 1)

lemma coefficient_factor (right : Bool) (k M : ℕ) (hk : 0 < k) :
    (top right (k * M) k).choose k = M * auxiliary right (k * M) k := by
  cases right with
  | false =>
    change (k * M).choose k = M * (k * M - 1).choose (k - 1)
    simpa only [Nat.mul_comm M k] using
      (Nat.choose_mul_right (m := M) (n := k) (Nat.ne_of_gt hk))
  | true =>
    change (k * M + k - 1).choose k = M * (k * M + k - 1).choose (k - 1)
    apply Nat.mul_right_cancel hk
    have hh := Nat.choose_succ_right_eq (k * M + k - 1) (k - 1)
    rw [show k - 1 + 1 = k by omega,
      show k * M + k - 1 - (k - 1) = k * M by omega] at hh
    calc
      (k * M + k - 1).choose k * k =
          (k * M + k - 1).choose (k - 1) * (k * M) := hh
      _ = (M * (k * M + k - 1).choose (k - 1)) * k := by ac_rfl

/-- Splitting a product at a specified member, with its original membership proof. -/
lemma split_prod (S : Finset ℕ) (f : ℕ → ℕ) {a : ℕ} (ha : a ∈ S) :
    (∏ j ∈ S, f j) = f a * ∏ j ∈ S.erase a, f j := by
  calc
    (∏ j ∈ S, f j) = ∏ j ∈ insert a (S.erase a), f j := by
      rw [Finset.insert_erase ha]
    _ = f a * ∏ j ∈ S.erase a, f j := by
      rw [Finset.prod_insert (Finset.notMem_erase a S)]

/-- The one missing factor `p` in the denominator is isolated exactly. -/
lemma Parameters.cross_identity (h : Parameters k p) (right : Bool) :
    p * auxiliary right (center k p) k =
      term right (center k p) p *
        ∏ j ∈ others k p, quotient right k (cofactor k p) j := by
  let P : ℕ := ∏ j ∈ others k p, j
  have hPpos : 0 < P := by
    apply Finset.prod_pos
    intro j hj
    have := (Finset.mem_Icc.mp (Finset.mem_of_mem_erase hj)).1
    omega
  have hfac : (k - 1).factorial = p * P := by
    rw [← prod_Icc_id]
    exact split_prod (indices k) id h.p_mem
  have hprod :
      (∏ j ∈ indices k, term right (center k p) j) =
        term right (center k p) p *
          (P * ∏ j ∈ others k p, quotient right k (cofactor k p) j) := by
    rw [split_prod (indices k) (term right (center k p)) h.p_mem]
    congr 1
    calc
      (∏ j ∈ others k p, term right (center k p) j) =
          ∏ j ∈ others k p, j * quotient right k (cofactor k p) j := by
        apply Finset.prod_congr rfl
        intro j hj
        exact term_factor right (h.other_dvd_cofactor hj)
      _ = P * ∏ j ∈ others k p, quotient right k (cofactor k p) j :=
        Finset.prod_mul_distrib
  have hh := auxiliary_product right (center k p) k (by have := h.k_ge; omega)
  rw [hfac, hprod] at hh
  apply Nat.mul_left_cancel hPpos
  calc
    P * (p * auxiliary right (center k p) k) =
        (p * P) * auxiliary right (center k p) k := by ac_rfl
    _ = term right (center k p) p *
        (P * ∏ j ∈ others k p, quotient right k (cofactor k p) j) := hh
    _ = P * (term right (center k p) p *
        ∏ j ∈ others k p, quotient right k (cofactor k p) j) := by ac_rfl

/-- If two distinct factors of `Q` are divisible by `p`, removing any one
    factor still leaves a multiple of `p`. Exact positive-factor cancellation
    in `p*B=f*Q` then proves all required divisibilities. -/
lemma cancel_cross_product {S : Finset ℕ} {q : ℕ → ℕ} {p B f a b : ℕ}
    (hp : 0 < p) (ha : a ∈ S) (hb : b ∈ S) (hab : a ≠ b)
    (hpa : p ∣ q a) (hpb : p ∣ q b)
    (hcross : p * B = f * ∏ j ∈ S, q j) :
    f ∣ B ∧ ∀ i ∈ S, q i ∣ B := by
  have hpQ : p ∣ ∏ j ∈ S, q j := hpa.trans (Finset.dvd_prod_of_mem q ha)
  constructor
  · obtain ⟨R, hR⟩ := hpQ
    have hB : B = f * R := by
      apply Nat.mul_left_cancel hp
      calc
        p * B = f * ∏ j ∈ S, q j := hcross
        _ = p * (f * R) := by rw [hR]; ac_rfl
    exact ⟨R, hB⟩
  · intro i hi
    have hex : ∃ j ∈ S.erase i, p ∣ q j := by
      by_cases hai : a = i
      · refine ⟨b, Finset.mem_erase.mpr ⟨?_, hb⟩, hpb⟩
        intro hbi
        apply hab
        exact hai.trans hbi.symm
      · exact ⟨a, Finset.mem_erase.mpr ⟨hai, ha⟩, hpa⟩
    obtain ⟨j, hj, hpj⟩ := hex
    have hd : p ∣ ∏ t ∈ S.erase i, q t :=
      hpj.trans (Finset.dvd_prod_of_mem q hj)
    obtain ⟨R, hR⟩ := hd
    have hB : B = q i * (f * R) := by
      apply Nat.mul_left_cancel hp
      calc
        p * B = f * ∏ t ∈ S, q t := hcross
        _ = f * (q i * ∏ t ∈ S.erase i, q t) := by rw [split_prod S q hi]
        _ = p * (q i * (f * R)) := by rw [hR]; ac_rfl
    exact ⟨f * R, hB⟩

end ProductConstruction
end JSP000883
