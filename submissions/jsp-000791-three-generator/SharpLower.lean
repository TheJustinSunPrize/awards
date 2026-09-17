import LowerCertificate

/-!
Exact rational lower bound from the comparison strategy in
https://www.erdosproblemaday.com/report/951 (Patrick White + Claude, 2026-07-28).
All numerical signs are supplied by ring-checked Bernstein polynomial identities.
No floating point computation, external solver, or assumed separation cutoff is
used in the proof. This is a three-generator bound, not the full Erdos951 answer.
-/

namespace JSP791

theorem seventh_above_fourth {a b c : ℝ} (ha : 1 < a) (hab : a < b)
    (hbc : b < c) (hs : Separated3 a b c) (hc : c ≤ cutoff) : c^4+1 ≤ a^7 := by
  have hl := le_of_lt (third_generator_gt_43_div_10 ha hab hbc hs)
  have ha0 : 0 ≤ a := by linarith
  have hcp : 0 ≤ c+1 := by linarith
  have hsq := square_above_third ha hab hbc hs (by dsimp [cutoff] at hc; linarith)
  have h := hs ![7,0,0] ![0,0,4] (by decide)
  norm_num [monomial] at h
  rcases le_abs.mp h with h | h
  · linarith
  · have hupper : a^7 ≤ c^4-1 := by linarith
    have hp1 := pow_le_pow_left₀ hcp hsq 7
    have hp2 := pow_le_pow_left₀ (pow_nonneg ha0 7) hupper 2
    have hi : (a^2)^7 = (a^7)^2 := by ring
    rw [hi] at hp1
    have hpos := orientation_positive hl hc
    linarith

/-- Strict rational lower bound on the largest generator of every ordered,
fully one-separated three-generator multiplicative semigroup. -/
theorem third_generator_gt_cutoff {a b c : ℝ} (ha : 1 < a) (hab : a < b)
    (hbc : b < c) (hs : Separated3 a b c) : (4309405275 : ℝ)/1000000000 < c := by
  by_contra hh
  have hc : c ≤ cutoff := by dsimp [cutoff]; linarith
  have hl := le_of_lt (third_generator_gt_43_div_10 ha hab hbc hs)
  have hc0 : 0 ≤ c := by linarith
  have ha0 : 0 ≤ a := by linarith
  have hb0 : 0 ≤ b := by linarith
  have hl0 : 0 ≤ line c := by dsimp [line,cutoff] at *; linarith
  have hp7 := seventh_above_fourth ha hab hbc hs hc
  have hline : line c ≤ a := by
    by_contra hh
    have hpow := pow_le_pow_left₀ ha0 (le_of_lt (lt_of_not_ge hh)) 7
    have hp := affine_below_root hl hc
    linarith
  obtain ⟨hB,hC⟩ := further_comparisons ha hab hbc hs
    (by dsimp [cutoff] at hc; linarith)
  have hpow := pow_le_pow_left₀ (mul_nonneg (sq_nonneg a) hb0)
    (show a^2*b ≤ c^2-1 by linarith) 2
  have hbound : a^4*(a*c+1) ≤ (c^2-1)^2 := calc
    a^4*(a*c+1) ≤ a^4*b^2 := mul_le_mul_of_nonneg_left hB (pow_nonneg ha0 4)
    _ = (a^2*b)^2 := by ring
    _ ≤ (c^2-1)^2 := hpow
  have hline4 := pow_le_pow_left₀ hl0 hline 4
  have hline5 := pow_le_pow_left₀ hl0 hline 5
  have hlast : c*line c^5 + line c^4 ≤ (c^2-1)^2 := calc
    c*line c^5 + line c^4 ≤ c*a^5 + a^4 :=
      add_le_add (mul_le_mul_of_nonneg_left hline5 hc0) hline4
    _ = a^4*(a*c+1) := by ring
    _ ≤ (c^2-1)^2 := hbound
  have hpos := affine_contradiction hl hc
  linarith

end JSP791

#print axioms JSP791.third_generator_gt_cutoff
