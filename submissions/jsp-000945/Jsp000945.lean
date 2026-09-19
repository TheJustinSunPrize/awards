import Mathlib

/-!
# JSP-000945: integers whose differences from permitted double squares are all prime

The problem (as stated in the Justin Sun Prize catalog): is there a positive
integer `n` such that `n - 2 * x ^ 2` is prime for every natural number `x`
with `2 * x ^ 2 < n`?

The answer is yes. The known such integers are `2, 5, 7, 13, 31, 61, 181, 199`
(see Erdős problem #1140, which additionally asks whether there are infinitely
many; that stronger question is out of scope here).

This file proves:
* `jsp_000945`: the existential statement, witnessed by `n = 5`;
* `allPrimeDiffs_<n>`: certification of every known example;
* `jsp_000945_known_list`: all eight known values satisfy the property;
* `allPrimeDiffs_prime` and `allPrimeDiffs_mod_three`: structural
  restrictions — any such `n > 0` is prime, and any such `n > 21` is
  `1 mod 3` (the residues `n, n - 2, n - 8` cover `n, n + 1 mod 3`, so
  `n ≡ 2 mod 3` would force `3 ∣ n - 2` with `n - 2 > 3`).
-/

/-- `AllPrimeDiffs n` means `n - 2 * x ^ 2` is prime for every natural `x`
with `2 * x ^ 2 < n`. -/
def AllPrimeDiffs (n : ℕ) : Prop :=
  ∀ x : ℕ, 2 * x ^ 2 < n → Nat.Prime (n - 2 * x ^ 2)

/-- Every positive integer with the all-prime-differences property is itself
prime (the case `x = 0`). -/
theorem allPrimeDiffs_prime {n : ℕ} (hn : 0 < n) (h : AllPrimeDiffs n) :
    Nat.Prime n := by
  have h0 := h 0 (by simpa using hn)
  simpa using h0

/-- If `n > 21` has the all-prime-differences property then `n ≡ 1 (mod 3)`:
`x = 0, 1, 2` are all permitted, `n - 2 ≡ n - 8 ≡ n + 1 (mod 3)`, so
`n ≡ 0` makes `n` composite and `n ≡ 2` makes `n - 2` composite. -/
theorem allPrimeDiffs_mod_three {n : ℕ} (hn : 21 < n) (h : AllPrimeDiffs n) :
    n % 3 = 1 := by
  have hp : Nat.Prime n := allPrimeDiffs_prime (by omega) h
  have h2 : Nat.Prime (n - 2) := h 1 (by omega)
  by_contra hmod
  have h3 : n % 3 = 0 ∨ n % 3 = 2 := by omega
  rcases h3 with h3 | h3
  · have hdvd : 3 ∣ n := Nat.dvd_of_mod_eq_zero h3
    rcases (Nat.dvd_prime hp).mp hdvd with h1 | h1
    · norm_num at h1
    · omega
  · have hdvd : 3 ∣ n - 2 := by
      rw [Nat.dvd_iff_mod_eq_zero]
      omega
    rcases (Nat.dvd_prime h2).mp hdvd with h1 | h1
    · norm_num at h1
    · omega

/-- Certification of the known example `n = 2`. -/
theorem allPrimeDiffs_two : AllPrimeDiffs 2 := by
  intro x hx
  have hb : x ≤ 0 := by nlinarith
  interval_cases x
  all_goals norm_num

/-- Certification of the known example `n = 5`. -/
theorem allPrimeDiffs_five : AllPrimeDiffs 5 := by
  intro x hx
  have hb : x ≤ 1 := by nlinarith
  interval_cases x
  all_goals norm_num

/-- Certification of the known example `n = 7`. -/
theorem allPrimeDiffs_seven : AllPrimeDiffs 7 := by
  intro x hx
  have hb : x ≤ 1 := by nlinarith
  interval_cases x
  all_goals norm_num

/-- Certification of the known example `n = 13`. -/
theorem allPrimeDiffs_thirteen : AllPrimeDiffs 13 := by
  intro x hx
  have hb : x ≤ 2 := by nlinarith
  interval_cases x
  all_goals norm_num

/-- Certification of the known example `n = 31`. -/
theorem allPrimeDiffs_thirtyone : AllPrimeDiffs 31 := by
  intro x hx
  have hb : x ≤ 3 := by nlinarith
  interval_cases x
  all_goals norm_num

/-- Certification of the known example `n = 61`. -/
theorem allPrimeDiffs_sixtyone : AllPrimeDiffs 61 := by
  intro x hx
  have hb : x ≤ 5 := by nlinarith
  interval_cases x
  all_goals norm_num

/-- Certification of the known example `n = 181`. -/
theorem allPrimeDiffs_181 : AllPrimeDiffs 181 := by
  intro x hx
  have hb : x ≤ 9 := by nlinarith
  interval_cases x
  all_goals norm_num

/-- Certification of the known example `n = 199`. -/
theorem allPrimeDiffs_199 : AllPrimeDiffs 199 := by
  intro x hx
  have hb : x ≤ 9 := by nlinarith
  interval_cases x
  all_goals norm_num

/-- All eight known values satisfy the all-prime-differences property. -/
theorem jsp_000945_known_list :
    ∀ n ∈ ({2, 5, 7, 13, 31, 61, 181, 199} : Finset ℕ), AllPrimeDiffs n := by
  intro n hn
  fin_cases hn
  · exact allPrimeDiffs_two
  · exact allPrimeDiffs_five
  · exact allPrimeDiffs_seven
  · exact allPrimeDiffs_thirteen
  · exact allPrimeDiffs_thirtyone
  · exact allPrimeDiffs_sixtyone
  · exact allPrimeDiffs_181
  · exact allPrimeDiffs_199

/-- **JSP-000945.** There exists a positive integer whose differences from
twice every permitted smaller square are all prime. Witness: `n = 5`,
since `2 * x ^ 2 < 5` forces `x ∈ {0, 1}` and `5 - 0 = 5`, `5 - 2 = 3`
are prime. -/
theorem jsp_000945 : ∃ n : ℕ, 0 < n ∧ AllPrimeDiffs n :=
  ⟨5, by norm_num, allPrimeDiffs_five⟩

#print axioms jsp_000945
#print axioms jsp_000945_known_list
#print axioms allPrimeDiffs_mod_three
