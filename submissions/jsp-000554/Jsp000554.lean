import Mathlib

set_option maxRecDepth 100000

/-!
# JSP-000554: rough numbers between consecutive primes

The problem as recorded in the prize catalogue:

> Between consecutive primes, is there an integer whose least prime
> factor is at least their gap?

This is a question of Erdős, resolved asymptotically by Gafni and Tao
(arXiv:2508.06463), who proved that almost all prime gaps `(p_n, p_{n+1})`
contain a "rough" number — an `m` whose least prime factor `minFac m`
is at least the gap length — and that the number `N(X)` of exceptional
gaps is `O(X / log² X)`.

## What is formalized

We define `ConsecPrimes p q` (prime gap), `RoughInGap p q m`
(`p < m < q` and `q - p ≤ m.minFac`) and `Exceptional p q` (a prime gap
containing no rough number), and prove:

* `jsp_000554` — the answer to the literal question is two-sided:
  exceptional gaps exist (witness `(7, 11)`) and gaps containing a
  rough number exist (witness `(3, 5)`, `m = 4`). Equivalently,
  `jsp_000554_not_forall`: the universal statement is false.
* `twin_gap_rough` — every twin-prime gap `(p, p+2)` with `p ≥ 3`
  contains the rough number `p + 1` (even, so `minFac = 2 = gap`).
* `cousin_gap_exceptional` — every cousin-prime gap `(p, p+4)` with
  `p > 3` is exceptional: `p + 1, p + 3` are even and `p + 2` is a
  multiple of `3` (primality of `p + 4` forces `p ≡ 1 mod 3`).
* `sexy_gap_iff` — complete mod-15 characterization of gap-6
  ("sexy prime") gaps with `p > 5`: the gap is exceptional iff
  `p % 15 ∈ {1, 8}`.
* `jsp_000554_least_exceptional` — `(7, 11)` is the least exceptional
  gap with `p ≥ 3` (the `(2, 3)` gap is vacuous).
* `jsp_000554_first_rough_gap` — `47` is the least prime starting a gap
  of length `≥ 4` that contains a rough number (`49 = 7²` in `(47, 53)`).
* Certified instances: `exceptional_7_11`, `exceptional_13_17`,
  `exceptional_23_29`, `exceptional_31_37`, `rough_3_5_4`,
  `rough_5_7_6`, `rough_47_53_49`.

Not formalized: the Gafni–Tao asymptotic theorem (`N(X) = O(X/log²X)`);
this file captures the finite content and the exact small-gap behaviour.

Axiom audit is printed at the bottom of the file.
-/

open Nat

/-- `p` and `q` are consecutive primes: prime, `p < q`, and no prime
lies strictly between them. -/
def ConsecPrimes (p q : ℕ) : Prop :=
  p.Prime ∧ q.Prime ∧ p < q ∧ ∀ r : ℕ, r.Prime → p < r → q ≤ r

/-- `m` is a *rough number in the gap* `(p, q)`: it lies strictly inside
the gap and its least prime factor is at least the gap length. -/
def RoughInGap (p q m : ℕ) : Prop :=
  p < m ∧ m < q ∧ q - p ≤ m.minFac

/-- The prime gap `(p, q)` is *exceptional*: it contains no rough
number. -/
def Exceptional (p q : ℕ) : Prop :=
  ConsecPrimes p q ∧ ∀ m : ℕ, p < m → m < q → m.minFac < q - p

section helpers

lemma minFac_le {n d : ℕ} (hd : 2 ≤ d) (h : d ∣ n) : n.minFac ≤ d :=
  Nat.minFac_le_of_dvd hd h

lemma two_le_minFac {n : ℕ} (h : 2 ≤ n) : 2 ≤ n.minFac :=
  (Nat.minFac_prime (by omega)).two_le

/-- If `n` has no prime divisor below `6` (and `n > 1`), then
`6 ≤ minFac n`. -/
lemma six_le_minFac {n : ℕ} (h1 : 1 < n) (h2 : ¬ 2 ∣ n) (h3 : ¬ 3 ∣ n)
    (h5 : ¬ 5 ∣ n) : 6 ≤ n.minFac := by
  set r := n.minFac with hr
  have hp : r.Prime := Nat.minFac_prime (by omega)
  have hd : r ∣ n := Nat.minFac_dvd n
  by_contra h
  have h6 : r < 6 := by omega
  interval_cases r
  · norm_num at hp
  · norm_num at hp
  · exact h2 hd
  · exact h3 hd
  · norm_num at hp
  · exact h5 hd

/-- A prime `p > 3` is coprime to `3`; if additionally `p + 4` is prime,
then `p ≡ 1 (mod 3)`, so `3 ∣ p + 2`. -/
lemma three_dvd_add_two {p : ℕ} (hp : p.Prime) (hq : (p + 4).Prime)
    (h3 : 3 < p) : 3 ∣ p + 2 := by
  have hp3 : p % 3 ≠ 0 := fun h =>
    Nat.not_prime_of_dvd_of_lt (Nat.dvd_of_mod_eq_zero h) (by norm_num) h3 hp
  have hq3 : (p + 4) % 3 ≠ 0 := fun h =>
    Nat.not_prime_of_dvd_of_lt (Nat.dvd_of_mod_eq_zero h) (by norm_num)
      (by omega) hq
  have : p % 3 = 1 := by omega
  omega

end helpers

section explicit_gaps

lemma consecPrimes_3_5 : ConsecPrimes 3 5 :=
  ⟨by norm_num, by norm_num, by norm_num, fun r hr h3 => by
    by_contra h
    have hlt : r < 5 := by omega
    interval_cases r
    all_goals norm_num at hr⟩

lemma consecPrimes_5_7 : ConsecPrimes 5 7 :=
  ⟨by norm_num, by norm_num, by norm_num, fun r hr h5 => by
    by_contra h
    have hlt : r < 7 := by omega
    interval_cases r
    all_goals norm_num at hr⟩

lemma consecPrimes_7_11 : ConsecPrimes 7 11 :=
  ⟨by norm_num, by norm_num, by norm_num, fun r hr h7 => by
    by_contra h
    have hlt : r < 11 := by omega
    interval_cases r
    all_goals norm_num at hr⟩

lemma consecPrimes_13_17 : ConsecPrimes 13 17 :=
  ⟨by norm_num, by norm_num, by norm_num, fun r hr h13 => by
    by_contra h
    have hlt : r < 17 := by omega
    interval_cases r
    all_goals norm_num at hr⟩

lemma consecPrimes_23_29 : ConsecPrimes 23 29 :=
  ⟨by norm_num, by norm_num, by norm_num, fun r hr h23 => by
    by_contra h
    have hlt : r < 29 := by omega
    interval_cases r
    all_goals norm_num at hr⟩

lemma consecPrimes_31_37 : ConsecPrimes 31 37 :=
  ⟨by norm_num, by norm_num, by norm_num, fun r hr h31 => by
    by_contra h
    have hlt : r < 37 := by omega
    interval_cases r
    all_goals norm_num at hr⟩

lemma consecPrimes_47_53 : ConsecPrimes 47 53 :=
  ⟨by norm_num, by norm_num, by norm_num, fun r hr h47 => by
    by_contra h
    have hlt : r < 53 := by omega
    interval_cases r
    all_goals norm_num at hr⟩

/-- `m = 4` is a rough number in the gap `(3, 5)`. -/
theorem rough_3_5_4 : RoughInGap 3 5 4 := by
  refine ⟨by norm_num, by norm_num, ?_⟩
  norm_num

/-- `m = 6` is a rough number in the gap `(5, 7)`. -/
theorem rough_5_7_6 : RoughInGap 5 7 6 := by
  refine ⟨by norm_num, by norm_num, ?_⟩
  norm_num

/-- `m = 49 = 7²` is a rough number in the gap `(47, 53)`. -/
theorem rough_47_53_49 : RoughInGap 47 53 49 := by
  refine ⟨by norm_num, by norm_num, ?_⟩
  norm_num

/-- The gap `(7, 11)` is exceptional: `8, 9, 10` all have a prime
factor below `4`. -/
theorem exceptional_7_11 : Exceptional 7 11 := by
  refine ⟨consecPrimes_7_11, fun m h7 h11 => ?_⟩
  interval_cases m <;> norm_num

/-- The gap `(13, 17)` is exceptional. -/
theorem exceptional_13_17 : Exceptional 13 17 := by
  refine ⟨consecPrimes_13_17, fun m h13 h17 => ?_⟩
  interval_cases m <;> norm_num

/-- The gap `(23, 29)` is exceptional. -/
theorem exceptional_23_29 : Exceptional 23 29 := by
  refine ⟨consecPrimes_23_29, fun m h23 h29 => ?_⟩
  interval_cases m <;> norm_num

/-- The gap `(31, 37)` is exceptional. -/
theorem exceptional_31_37 : Exceptional 31 37 := by
  refine ⟨consecPrimes_31_37, fun m h31 h37 => ?_⟩
  interval_cases m <;> norm_num

end explicit_gaps

/-- Every twin-prime gap `(p, p+2)` with `p ≥ 3` contains a rough
number: `p + 1` is even, so `minFac (p+1) = 2`, equal to the gap. -/
theorem twin_gap_rough {p : ℕ} (hp : p.Prime) (h3 : 3 ≤ p)
    (_hc : ConsecPrimes p (p + 2)) : RoughInGap p (p + 2) (p + 1) := by
  have hodd : p % 2 = 1 := hp.eq_two_or_odd.resolve_left (by omega)
  have he : 2 ∣ p + 1 := by omega
  have hmin : (p + 1).minFac = 2 :=
    le_antisymm (minFac_le (le_refl 2) he) (two_le_minFac (by omega))
  exact ⟨by omega, by omega, by omega⟩

/-- Decidable version of `Exceptional`'s gap condition: no prime lies
strictly inside `(p, q)`. Used to feed `decide` computations. -/
abbrev GapFree (p q : ℕ) : Prop := ∀ r ∈ Finset.Ioo p q, ¬ r.Prime

/-- Decidable version of "every integer in the gap has a prime factor
below the gap length", phrased via an explicit small divisor so that
`decide` can kernel-reduce it (`Nat.minFac` does not reduce). -/
abbrev AllSmall (p q : ℕ) : Prop :=
  ∀ m ∈ Finset.Ioo p q, ∃ d ∈ Finset.range (q - p), 1 < d ∧ d ∣ m

lemma GapFree.of_consec {p q : ℕ} (hc : ConsecPrimes p q) : GapFree p q := by
  intro r hr hpr
  obtain ⟨h1, h2⟩ := Finset.mem_Ioo.mp hr
  have h3 := hc.2.2.2 r hpr h1
  omega

lemma AllSmall.of_exceptional {p q : ℕ} (he : Exceptional p q)
    (h1 : 1 < p) : AllSmall p q := by
  intro m hm
  obtain ⟨h2, h3⟩ := Finset.mem_Ioo.mp hm
  have hf := he.2 m h2 h3
  exact ⟨m.minFac, Finset.mem_range.mpr hf,
    (Nat.minFac_prime (by omega)).one_lt, Nat.minFac_dvd m⟩

lemma minFac_lt_of_allSmall {m g : ℕ}
    (h : ∃ d ∈ Finset.range g, 1 < d ∧ d ∣ m) : m.minFac < g := by
  obtain ⟨d, hd1, hd2, hd3⟩ := h
  have hle := minFac_le hd2 hd3
  have := Finset.mem_range.mp hd1
  omega

/-- Every cousin-prime gap `(p, p+4)` with `p > 3` is exceptional. -/
theorem cousin_gap_exceptional {p : ℕ} (hp : p.Prime) (h3 : 3 < p)
    (hc : ConsecPrimes p (p + 4)) : Exceptional p (p + 4) := by
  have hodd : p % 2 = 1 := hp.eq_two_or_odd.resolve_left (by omega)
  have h3d : 3 ∣ p + 2 := three_dvd_add_two hp hc.2.1 h3
  refine ⟨hc, fun m hm1 hm2 => ?_⟩
  rcases (show m = p + 1 ∨ m = p + 2 ∨ m = p + 3 by omega) with rfl | rfl | rfl
  · have := minFac_le (n := p + 1) (d := 2) (le_refl 2) (by omega)
    omega
  · have := minFac_le (n := p + 2) (d := 3) (by norm_num) h3d
    omega
  · have := minFac_le (n := p + 3) (d := 2) (le_refl 2) (by omega)
    omega

/-- Complete mod-15 characterization of gap-6 prime gaps with `p > 5`:
the gap `(p, p+6)` is exceptional iff `p % 15 ∈ {1, 8}`. -/
theorem sexy_gap_iff {p : ℕ} (hp : p.Prime) (h5 : 5 < p)
    (hc : ConsecPrimes p (p + 6)) : Exceptional p (p + 6) ↔
    p % 15 = 1 ∨ p % 15 = 8 := by
  have hodd : p % 2 = 1 := hp.eq_two_or_odd.resolve_left (by omega)
  have hp3 : p % 3 ≠ 0 := fun h =>
    Nat.not_prime_of_dvd_of_lt (Nat.dvd_of_mod_eq_zero h) (by norm_num)
      (by omega) hp
  have hp5 : p % 5 ≠ 0 := fun h =>
    Nat.not_prime_of_dvd_of_lt (Nat.dvd_of_mod_eq_zero h) (by norm_num)
      (by omega) hp
  constructor
  · -- exceptional → p % 15 ∈ {1, 8}: otherwise p+2 or p+4 is 30-coprime.
    intro hexc
    by_contra hne
    rw [not_or] at hne
    have hlt : p % 15 < 15 := Nat.mod_lt _ (by norm_num)
    interval_cases hr : p % 15
    all_goals first
      | omega
      | (have hd : 6 ≤ (p + 2).minFac :=
          six_le_minFac (by omega) (by omega) (by omega) (by omega)
         have := hexc.2 (p + 2) (by omega) (by omega)
         omega)
      | (have hd : 6 ≤ (p + 4).minFac :=
          six_le_minFac (by omega) (by omega) (by omega) (by omega)
         have := hexc.2 (p + 4) (by omega) (by omega)
         omega)
  · -- p % 15 ∈ {1, 8} → exceptional.
    rintro (h | h) <;> refine ⟨hc, fun m hm1 hm2 => ?_⟩
    all_goals
      rcases (show m = p + 1 ∨ m = p + 2 ∨ m = p + 3 ∨ m = p + 4 ∨
        m = p + 5 by omega) with rfl | rfl | rfl | rfl | rfl
    all_goals first
      | (have := minFac_le (n := p + 1) (d := 2) (le_refl 2) (by omega); omega)
      | (have := minFac_le (n := p + 3) (d := 2) (le_refl 2) (by omega); omega)
      | (have := minFac_le (n := p + 5) (d := 2) (le_refl 2) (by omega); omega)
      | (have := minFac_le (n := p + 2) (d := 3) (by norm_num) (by omega); omega)
      | (have := minFac_le (n := p + 2) (d := 5) (by norm_num) (by omega); omega)
      | (have := minFac_le (n := p + 4) (d := 3) (by norm_num) (by omega); omega)
      | (have := minFac_le (n := p + 4) (d := 5) (by norm_num) (by omega); omega)

/-- **JSP-000554.** The literal question has a two-sided answer:
exceptional prime gaps exist — `(7, 11)` contains no integer whose
least prime factor is `≥ 4` — and gaps containing a rough number exist —
`4` in `(3, 5)` has `minFac 4 = 2 = 5 - 3`. -/
theorem jsp_000554 :
    (∃ p q : ℕ, Exceptional p q) ∧
      ∃ p q m : ℕ, ConsecPrimes p q ∧ RoughInGap p q m :=
  ⟨⟨7, 11, exceptional_7_11⟩, 3, 5, 4, consecPrimes_3_5, rough_3_5_4⟩

/-- The universal reading of the question is false. -/
theorem jsp_000554_not_forall :
    ¬ ∀ p q : ℕ, ConsecPrimes p q → ∃ m : ℕ, RoughInGap p q m := by
  intro h
  obtain ⟨m, hm⟩ := h 7 11 consecPrimes_7_11
  have hlt := exceptional_7_11.2 m hm.1 hm.2.1
  have hge := hm.2.2
  omega

/-- Kernel-certified check: the only prime gaps starting at `p < 7`
with `p ≥ 3` — `(3, 5)` and `(5, 7)` — each contain a rough number. -/
theorem check_least_exceptional :
    ∀ p ∈ Finset.range 7, ∀ q ∈ Finset.range 8,
      p.Prime → q.Prime → p < q → GapFree p q → 3 ≤ p →
        ¬ AllSmall p q := by
  decide

/-- Kernel-certified check: every prime gap of length `≥ 4` starting
below `47` is exceptional (each interior integer has a prime factor
below the gap length). -/
theorem check_first_rough_gap :
    ∀ p ∈ Finset.range 47, ∀ q ∈ Finset.range 48,
      p.Prime → q.Prime → GapFree p q → 4 ≤ q - p → AllSmall p q := by
  decide

/-- `(7, 11)` is the least exceptional gap with `p ≥ 3`: the only
smaller prime gaps are `(3, 5)` and `(5, 7)`, each containing a rough
number. -/
theorem jsp_000554_least_exceptional {p q : ℕ} (hc : ConsecPrimes p q)
    (he : Exceptional p q) (h3 : 3 ≤ p) (hlt : p < 7) : False := by
  have hq8 : q < 8 := by
    have h := hc.2.2.2 7 (by norm_num) (by omega)
    omega
  exact check_least_exceptional p (Finset.mem_range.mpr hlt) q
    (Finset.mem_range.mpr hq8) hc.1 hc.2.1 hc.2.2.1
    (GapFree.of_consec hc) h3 (AllSmall.of_exceptional he (by omega))

/-- `47` is the least prime that starts a gap of length `≥ 4`
containing a rough number. -/
theorem jsp_000554_first_rough_gap {p q : ℕ} (hc : ConsecPrimes p q)
    (hgap : 4 ≤ q - p) (hm : ∃ m : ℕ, RoughInGap p q m) : 47 ≤ p := by
  by_contra hlt
  obtain ⟨m, hm1, hm2, hm3⟩ := hm
  have hplt : p < 47 := by omega
  have hq47 : q < 48 := by
    have h := hc.2.2.2 47 (by norm_num) hplt
    omega
  have hchk := check_first_rough_gap p
    (Finset.mem_range.mpr (by omega)) q (Finset.mem_range.mpr hq47)
    hc.1 hc.2.1 (GapFree.of_consec hc) hgap m
    (Finset.mem_Ioo.mpr ⟨hm1, hm2⟩)
  have hlt2 := minFac_lt_of_allSmall hchk
  omega

#print axioms jsp_000554
#print axioms jsp_000554_not_forall
#print axioms sexy_gap_iff
#print axioms jsp_000554_first_rough_gap
