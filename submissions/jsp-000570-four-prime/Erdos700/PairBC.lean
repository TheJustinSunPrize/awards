import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
Pure integer core of the last pair in the four-prime construction for Erdos 700.

These lemmas do not assert the four-prime theorem, Lucas's theorem, or the
existence of the required primes.  The intended substitution is
`q = P + c`, `d = c - b`, `L = b * (b - a)`.

The hypotheses deliberately expose the size estimates and the two normalized
digit bounds; their derivation from the prime parameters is a separate task.
-/

namespace Erdos700.PairBC

/-- The carry required when a coefficient lies in `[-q,q)`. -/
def lowCarry (K : ℤ) : ℤ := if K < 0 then -1 else 0

/-- One-borrow normalization, valid as a base-`q` digit on `[-q,q)`. -/
def normalizeDigit (q K : ℤ) : ℤ := if K < 0 then q + K else K

theorem lowCarry_bounds (K : ℤ) : -1 ≤ lowCarry K ∧ lowCarry K ≤ 0 := by
  by_cases h : K < 0 <;> simp [lowCarry, h]

theorem lowCarry_balance (q K : ℤ) :
    q * lowCarry K + normalizeDigit q K = K := by
  by_cases h : K < 0 <;> simp [lowCarry, normalizeDigit, h]

theorem normalizeDigit_bounds {q K : ℤ} (hlo : -q ≤ K) (hhi : K < q) :
    0 ≤ normalizeDigit q K ∧ normalizeDigit q K < q := by
  by_cases h : K < 0 <;> simp [normalizeDigit, h] <;> omega

theorem normalizeDigit_eq_emod {q K : ℤ} (hlo : -q ≤ K) (hhi : K < q) :
    normalizeDigit q K = K % q := by
  by_cases h : K < 0
  · have heq : (q + K) % q = q + K :=
      Int.emod_eq_of_lt (by omega) (by omega)
    simpa [normalizeDigit, h, Int.add_emod] using heq.symm
  · simpa [normalizeDigit, h] using (Int.emod_eq_of_lt (by omega) hhi).symm

theorem lowCarry_eq_ediv {q K : ℤ} (hlo : -q ≤ K) (hhi : K < q) :
    lowCarry K = K / q := by
  by_cases h : K < 0
  · simpa [lowCarry, h] using
      (Int.ediv_eq_neg_one_of_neg_of_le h (by omega)).symm
  · simpa [lowCarry, h] using
      (Int.ediv_eq_zero_of_lt (by omega) hhi).symm

theorem polynomial_low_digit (q u M K : ℤ) :
    (u * q ^ 2 + M * q + K) % q = K % q := by
  have heq : u * q ^ 2 + M * q + K = (u * q + M) * q + K := by ring
  rw [heq, Int.mul_add_emod_self_right]

theorem polynomial_middle_digit {q : ℤ} (hq : q ≠ 0) (u M K : ℤ) :
    ((u * q ^ 2 + M * q + K) / q) % q = (M + K / q) % q := by
  have heq : u * q ^ 2 + M * q + K = (u * q + M) * q + K := by ring
  rw [heq, Int.mul_add_ediv_right _ _ hq]
  have hsecond : u * q + M + K / q = u * q + (M + K / q) := by ring
  rw [hsecond, Int.mul_add_emod_self_right]

/-- Both canonical digits of an integer quadratic agree with the one-borrow
normalizations, assuming the two raw coefficients lie in the stated ranges. -/
theorem two_digits_normalize {q u M K : ℤ} (hq : 0 < q)
    (hKlo : -q ≤ K) (hKhi : K < q)
    (hMlo : -q ≤ M + lowCarry K) (hMhi : M + lowCarry K < q) :
    (u * q ^ 2 + M * q + K) % q = normalizeDigit q K ∧
      ((u * q ^ 2 + M * q + K) / q) % q =
        normalizeDigit q (M + lowCarry K) := by
  constructor
  · rw [polynomial_low_digit, normalizeDigit_eq_emod hKlo hKhi]
  · rw [polynomial_middle_digit (ne_of_gt hq),
      ← lowCarry_eq_ediv hKlo hKhi, normalizeDigit_eq_emod hMlo hMhi]

theorem normalizeLow_radix_identity (q u M K : ℤ) :
    u * q ^ 2 + M * q + K =
      u * q ^ 2 + (M + lowCarry K) * q + normalizeDigit q K := by
  have h := lowCarry_balance q K
  nlinarith only [h]

/-- The correction term subtracted from `J` is nonnegative and small. -/
theorem correction_bounds {d u H c epsilon : ℤ}
    (hd : 0 ≤ d) (hu : 0 ≤ u) (hH : 0 ≤ H)
    (hepsilon : -1 ≤ epsilon ∧ epsilon ≤ 0)
    (hbudget : 2 * u * d + 2 * H + 1 ≤ 4 * c ^ 2) :
    0 ≤ 2 * u * d + 2 * H - epsilon ∧
      2 * u * d + 2 * H - epsilon ≤ 4 * c ^ 2 := by
  have hud := mul_nonneg hu hd
  constructor <;> nlinarith

/-- Bounds for the middle coefficient when `H` is positive. -/
theorem positive_H_middle_bounds {q d c L u H J w epsilon E : ℤ}
    (hq : 0 ≤ q) (hd : 0 < d) (hH : 1 ≤ H) (hHd : H < d)
    (hw : 0 ≤ w) (hwL : w ≤ d * L) (hL : L ≤ c ^ 2)
    (hJ : d * J = H * q + w)
    (hcorrection : 0 ≤ 2 * u * d + 2 * H - epsilon ∧
      2 * u * d + 2 * H - epsilon ≤ 4 * c ^ 2)
    (hE : E = J - 2 * u * d - 2 * H + epsilon) :
    q - 4 * c ^ 2 * d ≤ d * E ∧
      d * E ≤ d * q - q + c ^ 2 * d := by
  have hd0 : 0 ≤ d := le_of_lt hd
  have hHq : q ≤ H * q := by
    nlinarith [mul_le_mul_of_nonneg_right hH hq]
  have hHupper : H ≤ d - 1 := by omega
  have hHqUpper := mul_le_mul_of_nonneg_right hHupper hq
  have hwUpper := mul_le_mul_of_nonneg_left hL hd0
  have hdelta0 := mul_nonneg hd0 hcorrection.1
  have hdeltaUpper := mul_le_mul_of_nonneg_left hcorrection.2 hd0
  have hEscaled := congrArg (fun z : ℤ => d * z) hE
  constructor <;> nlinarith

/-- A uniform large-base threshold excludes the whole positive-`H` interval. -/
theorem positive_H_middle_interval {q d c U E : ℤ}
    (hd : 0 < d) (hgap : 7 * c ^ 2 * d < q) (hU : U ≤ 3 * c ^ 2)
    (hlo : q - 4 * c ^ 2 * d ≤ d * E)
    (hhi : d * E ≤ d * q - q + c ^ 2 * d) :
    U - 1 < E ∧ E < q := by
  have hd0 : 0 ≤ d := le_of_lt hd
  have hc2d : 0 ≤ c ^ 2 * d := mul_nonneg (sq_nonneg c) hd0
  constructor
  · by_contra h
    have hEU : E ≤ U - 1 := by omega
    have hEUscaled := mul_le_mul_of_nonneg_left hEU hd0
    have hUscaled := mul_le_mul_of_nonneg_left hU hd0
    nlinarith
  · by_contra h
    have hqE : q ≤ E := by omega
    have hqEscaled := mul_le_mul_of_nonneg_left hqE hd0
    nlinarith

/-- The middle coefficient always lies in the one-borrow normalization range.
The positive-`H` case is actually strictly between `U-1` and `q`. -/
theorem middle_normalization_range {q d c L U u H J w K : ℤ}
    (hq : 0 ≤ q) (hd : 0 < d) (hLsize : L ≤ c ^ 2)
    (hu : 0 ≤ u) (hH : 0 ≤ H) (hHd : H < d)
    (hw : 0 ≤ w) (hwL : w ≤ d * L)
    (hJ : d * J = H * q + w)
    (hbudget : 2 * u * d + 2 * H + 1 ≤ 4 * c ^ 2)
    (hgap : 7 * c ^ 2 * d < q)
    (hUlo : 1 ≤ U) (hUhi : U ≤ 3 * c ^ 2) :
    -q ≤ J - 2 * u * d - 2 * H + lowCarry K ∧
      J - 2 * u * d - 2 * H + lowCarry K < q := by
  have hcarry := lowCarry_bounds K
  by_cases hH0 : H = 0
  · have hJ0 : d * J = w := by simpa [hH0] using hJ
    have hJnonneg : 0 ≤ J := by nlinarith
    have hJL : J ≤ L := by nlinarith
    have hd1 : 1 ≤ d := by omega
    have hc2 : 0 ≤ c ^ 2 := sq_nonneg c
    have hc2d := mul_le_mul_of_nonneg_left hd1 hc2
    have hud : 0 ≤ u * d := mul_nonneg hu (le_of_lt hd)
    simp only [hH0, mul_zero, sub_zero]
    constructor <;> nlinarith
  · have hH1 : 1 ≤ H := by omega
    have hcorrection := correction_bounds (le_of_lt hd) hu hH hcarry hbudget
    obtain ⟨hlo, hhi⟩ := positive_H_middle_bounds hq hd hH1 hHd hw hwL hLsize hJ
      hcorrection (rfl : J - 2 * u * d - 2 * H + lowCarry K = _)
    obtain ⟨hlarge, hsmall⟩ := positive_H_middle_interval hd hgap hUhi hlo hhi
    exact ⟨by omega, hsmall⟩
/-- The `H=0, u>0` branch: the low coefficient is positive and the middle
coefficient requires a borrow, giving a middle digit above its bound. -/
theorem zero_H_positive_u {q d L u t U : ℤ}
    (hd : 0 < d) (hLd : L < d) (hu : 1 ≤ u)
    (ht : 0 ≤ t) (htL : t ≤ L)
    (hmargin : U - 1 < q - 2 * u * d) :
    0 < d * (u * d - t) ∧ t - 2 * u * d < 0 ∧
      U - 1 < normalizeDigit q (t - 2 * u * d) := by
  have hd0 : 0 ≤ d := le_of_lt hd
  have hud : d ≤ u * d := by
    nlinarith [mul_le_mul_of_nonneg_right hu hd0]
  have hpos : 0 < u * d - t := by omega
  have hneg : t - 2 * u * d < 0 := by nlinarith
  refine ⟨mul_pos hd hpos, hneg, ?_⟩
  simp only [normalizeDigit, if_pos hneg]
  omega

/-- The `H=0, u=0, t>0` branch violates the low digit bound. -/
theorem zero_H_zero_u_positive_t {q d L t F : ℤ}
    (hd : 0 < d) (ht : 0 < t) (htL : t ≤ L) (hF : d * L < F) :
    q - F < normalizeDigit q (-d * t) := by
  have hneg : -d * t < 0 := by nlinarith [mul_pos hd ht]
  have hdt := mul_le_mul_of_nonneg_left htL (le_of_lt hd)
  simp only [normalizeDigit, if_pos hneg]
  nlinarith

/-- Exclusion of simultaneous admissible normalized low and middle digits.

`hK` encodes the constant coefficient after moving the second `-H*q`
contribution into the middle coefficient.  Thus the middle correction is
`-2*H`, which is essential.

The conclusion uses only integer arithmetic and exposed size hypotheses.
No binomial coefficient, primality assertion, or existence theorem is assumed
implicitly.  In applications, `hnonzero` follows from the original `k > 0`.
-/
theorem normalized_pair_exclusion {q d c L U F u H J w K : ℤ}
    (hq : 0 ≤ q) (hd : 0 < d)
    (hLd : L < d) (hLsize : L ≤ c ^ 2)
    (hu : 0 ≤ u) (hH : 0 ≤ H) (hHd : H < d)
    (hw : 0 ≤ w) (hwL : w ≤ d * L)
    (hJ : d * J = H * q + w)
    (hK : K = u * d ^ 2 - w + d * H)
    (hbudget : 2 * u * d + 2 * H + 1 ≤ 4 * c ^ 2)
    (hgap : 7 * c ^ 2 * d < q)
    (hUlo : 1 ≤ U) (hUhi : U ≤ 3 * c ^ 2)
    (hmargin : U - 1 < q - 2 * u * d)
    (hF : d * L < F)
    (hnonzero : u ≠ 0 ∨ H ≠ 0 ∨ w ≠ 0)
    (hlow : normalizeDigit q K ≤ q - F)
    (hmiddle : normalizeDigit q
      (J - 2 * u * d - 2 * H + lowCarry K) ≤ U - 1) : False := by
  by_cases hH0 : H = 0
  · have hJ0 : d * J = w := by simpa [hH0] using hJ
    have hJnonneg : 0 ≤ J := by nlinarith
    have hJL : J ≤ L := by nlinarith
    have hK0 : K = d * (u * d - J) := by
      nlinarith [hK, hJ0]
    by_cases hu0 : u = 0
    · have hwne : w ≠ 0 := by simpa [hu0, hH0] using hnonzero
      have hJpos : 0 < J := by
        by_contra h
        have : J = 0 := by omega
        simp [this] at hJ0
        omega
      have hKzero : K = -d * J := by nlinarith [hK0]
      have hviolation := zero_H_zero_u_positive_t hd hJpos hJL hF (q := q)
      rw [← hKzero] at hviolation
      omega
    · have hu1 : 1 ≤ u := by omega
      obtain ⟨hKpos, _, hviolation⟩ :=
        zero_H_positive_u hd hLd hu1 hJnonneg hJL hmargin
      have hKnonneg : ¬ K < 0 := by rw [hK0]; omega
      simp only [lowCarry, if_neg hKnonneg, hH0, mul_zero, sub_zero, add_zero]
        at hmiddle
      omega
  · have hH1 : 1 ≤ H := by omega
    have hcorrection := correction_bounds (le_of_lt hd) hu hH
      (lowCarry_bounds K) hbudget
    obtain ⟨hlo, hhi⟩ := positive_H_middle_bounds hq hd hH1 hHd hw hwL hLsize hJ
      hcorrection (rfl : J - 2 * u * d - 2 * H + lowCarry K = _)
    obtain ⟨hlarge, _⟩ := positive_H_middle_interval hd hgap hUhi hlo hhi
    have hEnonneg : ¬ (J - 2 * u * d - 2 * H + lowCarry K) < 0 := by omega
    simp only [normalizeDigit, if_neg hEnonneg] at hmiddle
    omega

/-- A version with actual Euclidean digits of the integer represented in base
`q`, rather than assumed bounds on a normalization function. -/
theorem radix_pair_exclusion {q d c L U F u H J w K y : ℤ}
    (hq : 0 < q) (hd : 0 < d)
    (hLd : L < d) (hLsize : L ≤ c ^ 2)
    (hu : 0 ≤ u) (hH : 0 ≤ H) (hHd : H < d)
    (hw : 0 ≤ w) (hwL : w ≤ d * L)
    (hJ : d * J = H * q + w)
    (hK : K = u * d ^ 2 - w + d * H)
    (hKlo : -q ≤ K) (hKhi : K < q)
    (hbudget : 2 * u * d + 2 * H + 1 ≤ 4 * c ^ 2)
    (hgap : 7 * c ^ 2 * d < q)
    (hUlo : 1 ≤ U) (hUhi : U ≤ 3 * c ^ 2)
    (hmargin : U - 1 < q - 2 * u * d)
    (hF : d * L < F)
    (hnonzero : u ≠ 0 ∨ H ≠ 0 ∨ w ≠ 0)
    (hy : y = u * q ^ 2 + (J - 2 * u * d - 2 * H) * q + K)
    (hlow : y % q ≤ q - F) (hmiddle : (y / q) % q ≤ U - 1) : False := by
  obtain ⟨hMlo, hMhi⟩ := middle_normalization_range (le_of_lt hq) hd hLsize hu hH
    hHd hw hwL hJ hbudget hgap hUlo hUhi (K := K)
  obtain ⟨hloweq, hmiddleeq⟩ := two_digits_normalize hq hKlo hKhi hMlo hMhi (u := u)
  rw [hy, hloweq] at hlow
  rw [hy, hmiddleeq] at hmiddle
  exact normalized_pair_exclusion (le_of_lt hq) hd hLd hLsize hu hH hHd hw hwL
    hJ hK hbudget hgap hUlo hUhi hmargin hF hnonzero hlow hmiddle

/-- Complete pure-integer exclusion from source-base digits and divisibility.

The intended source base is `x = q-d = P+b`.  Thus `hsource` says that `k/x`
has source digits `u,v,w`, and `hdiv` is the divisibility by the other prime
already extracted from Lucas.  The target assumptions are the actual low and
middle base-`q` digits of `k/q`.  All carries and congruence quotients are
constructed inside the proof.

The remaining size assumptions are explicit polynomial inequalities; they do
not include primality, Lucas, or any claim about the desired conclusion.
-/
theorem source_pair_exclusion {q d c L U F u v w k : ℤ}
    (hq : 0 < q) (hd : 0 < d)
    (hLd : L < d) (hLsize : L ≤ c ^ 2)
    (hu : 0 ≤ u) (hv : 0 ≤ v) (hvq : v < q)
    (hw : 0 ≤ w) (hwL : w ≤ d * L)
    (hsize : u * d ^ 2 + d ^ 2 < q)
    (hbudget : 2 * u * d + 2 * d ≤ 4 * c ^ 2)
    (hgap : 7 * c ^ 2 * d < q)
    (hUlo : 1 ≤ U) (hUhi : U ≤ 3 * c ^ 2)
    (hmargin : U - 1 < q - 2 * u * d)
    (hF : d * L < F) (hk : 0 < k)
    (hsource : k = (q - d) * (u * (q - d) ^ 2 + v * (q - d) + w))
    (hdiv : q ∣ u * (q - d) ^ 2 + v * (q - d) + w)
    (hlow : (k / q) % q ≤ q - F)
    (hmiddle : (k / q / q) % q ≤ U - 1) : False := by
  have hd0 : 0 ≤ d := le_of_lt hd
  have hud2 : 0 ≤ u * d ^ 2 := mul_nonneg hu (sq_nonneg d)
  have hvd : 0 ≤ v * d := mul_nonneg hv hd0
  have hdL : d * L < d ^ 2 := by
    nlinarith only [mul_lt_mul_of_pos_left hLd hd]
  have hRlo : -d * q < u * d ^ 2 - v * d + w := by
    nlinarith only [hud2, hw, mul_lt_mul_of_pos_right hvq hd]
  have hRhi : u * d ^ 2 - v * d + w < q := by
    nlinarith only [hsize, hwL, hdL, hvd]
  have hRdiv : q ∣ u * d ^ 2 - v * d + w := by
    obtain ⟨s, hs⟩ := hdiv
    refine ⟨s - (u * q - 2 * u * d + v), ?_⟩
    calc
      u * d ^ 2 - v * d + w =
        (u * (q - d) ^ 2 + v * (q - d) + w) -
          q * (u * q - 2 * u * d + v) := by ring
      _ = q * (s - (u * q - 2 * u * d + v)) := by rw [hs]; ring
  obtain ⟨h, hh⟩ := hRdiv
  let H : ℤ := -h
  let J : ℤ := v - u * d
  let K : ℤ := u * d ^ 2 - w + d * H
  have hH : 0 ≤ H := by
    have hh1 : h < 1 := by nlinarith only [hh, hRhi, hq]
    dsimp [H]
    omega
  have hHd : H < d := by dsimp [H]; nlinarith only [hh, hRlo, hq]
  have hJ : d * J = H * q + w := by dsimp [J, H]; nlinarith only [hh]
  have hK : K = u * d ^ 2 - w + d * H := rfl
  have hKlo : -q ≤ K := by
    have hdH := mul_nonneg hd0 hH
    dsimp [K]
    nlinarith only [hud2, hdH, hwL, hdL, hsize]
  have hKhi : K < q := by
    have hdH := mul_lt_mul_of_pos_left hHd hd
    dsimp [K]
    nlinarith only [hsize, hdH, hw]
  have hbudgetH : 2 * u * d + 2 * H + 1 ≤ 4 * c ^ 2 := by omega
  have hnonzero : u ≠ 0 ∨ H ≠ 0 ∨ w ≠ 0 := by
    by_contra hzero
    simp only [not_or, not_not] at hzero
    obtain ⟨hu0, hH0, hw0⟩ := hzero
    have hv0 : v = 0 := by
      dsimp [J] at hJ
      simp only [hu0, hH0, hw0, zero_mul, sub_zero, zero_add] at hJ
      exact (mul_eq_zero.mp hJ).resolve_left (ne_of_gt hd)
    simp only [hu0, hv0, hw0, zero_mul, zero_add, mul_zero] at hsource
    omega
  have hwrepr : w = d * J - H * q := by linarith only [hJ]
  have hvrepr : v = u * d + J := by dsimp [J]; ring
  have hkfactor : k = q * (u * q ^ 2 + (J - 2 * u * d - 2 * H) * q + K) := by
    rw [hsource]
    dsimp only [K]
    rw [hvrepr, hwrepr]
    ring
  have hquotient : k / q = u * q ^ 2 + (J - 2 * u * d - 2 * H) * q + K :=
    Int.ediv_eq_of_eq_mul_right (ne_of_gt hq) hkfactor
  exact radix_pair_exclusion hq hd hLd hLsize hu hH hHd hw hwL hJ hK hKlo hKhi
    hbudgetH hgap hUlo hUhi hmargin hF hnonzero hquotient hlow hmiddle

/-- Convenient coarse estimates: a cubic base threshold suffices for every
explicit size condition in `source_pair_exclusion`. -/
theorem large_base_estimates {q d c L U u : ℤ}
    (hd : 0 < d) (hdc : d < c) (hu : 0 ≤ u) (huc : u < c)
    (hLd : L < d) (hUhi : U ≤ 3 * c ^ 2) (hlarge : 10 * c ^ 3 < q) :
    0 < q ∧ L ≤ c ^ 2 ∧ u * d ^ 2 + d ^ 2 < q ∧
      2 * u * d + 2 * d ≤ 4 * c ^ 2 ∧ 7 * c ^ 2 * d < q ∧
      U - 1 < q - 2 * u * d := by
  have hc : 0 < c := lt_trans hd hdc
  have hc1 : 1 ≤ c := by omega
  have hc2pos : 0 < c ^ 2 := sq_pos_of_pos hc
  have hc3nonneg : 0 ≤ c ^ 3 := pow_nonneg (le_of_lt hc) 3
  have hcc2 : c ≤ c ^ 2 := by
    nlinarith only [mul_nonneg (le_of_lt hc) (sub_nonneg.mpr hc1)]
  have hc23 : c ^ 2 ≤ c ^ 3 := by
    nlinarith only [mul_le_mul_of_nonneg_right hc1 (sq_nonneg c)]
  have hd2 : d ^ 2 < c ^ 2 := by
    nlinarith only [mul_pos (sub_pos.mpr hdc) (show 0 < c + d by omega)]
  have hud : u * d < c ^ 2 := by
    nlinarith only [mul_le_mul_of_nonneg_left (le_of_lt hdc) hu,
      mul_lt_mul_of_pos_right huc hc]
  have hud2 : u * d ^ 2 < c ^ 3 := by
    nlinarith only [mul_le_mul_of_nonneg_left (le_of_lt hd2) hu,
      mul_lt_mul_of_pos_right huc hc2pos]
  have hc2d : c ^ 2 * d < c ^ 3 := by
    nlinarith only [mul_lt_mul_of_pos_left hdc hc2pos]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    nlinarith only [hlarge, hc3nonneg, hLd, hdc, hcc2, hc23, hd2, hud,
      hud2, hc2d, hUhi, le_of_lt hc2pos]

/-- Caller-facing last-pair exclusion with only coarse source-size estimates.
The digits supplied here are actual Euclidean digits, not normalized proxies. -/
theorem source_pair_exclusion_of_large_base {q d c L U F u v w k : ℤ}
    (hd : 0 < d) (hdc : d < c) (hLd : L < d)
    (hu : 0 ≤ u) (huc : u < c) (hv : 0 ≤ v) (hvq : v < q)
    (hw : 0 ≤ w) (hwL : w ≤ d * L)
    (hUlo : 1 ≤ U) (hUhi : U ≤ 3 * c ^ 2)
    (hlarge : 10 * c ^ 3 < q) (hF : d * L < F) (hk : 0 < k)
    (hsource : k = (q - d) * (u * (q - d) ^ 2 + v * (q - d) + w))
    (hdiv : q ∣ u * (q - d) ^ 2 + v * (q - d) + w)
    (hlow : (k / q) % q ≤ q - F)
    (hmiddle : (k / q / q) % q ≤ U - 1) : False := by
  obtain ⟨hq, hLsize, hsize, hbudget, hgap, hmargin⟩ :=
    large_base_estimates hd hdc hu huc hLd hUhi hlarge
  exact source_pair_exclusion hq hd hLd hLsize hu hv hvq hw hwL hsize hbudget
    hgap hUlo hUhi hmargin hF hk hsource hdiv hlow hmiddle

end Erdos700.PairBC
