import Mathlib

/-!
# JSP-000947: integers whose differences from permitted powers of two are all prime

The problem (as stated in the Justin Sun Prize catalog): is there a positive
integer `n` such that `n - 2 ^ k` is prime for every `k : ℕ` with
`1 < 2 ^ k < n`?

The answer is yes. The known such integers are `4, 7, 15, 21, 45, 75, 105`
(Erdős problem #1142, OEIS A039669; Mientka–Weitzenkamp verified there are
no others below `2 ^ 44`, and whether any `n > 105` exists is open — that
stronger question is outside the scope of this formalization).

This file proves:
* `jsp_000947`: the existential statement, witnessed by `n = 7`;
* `allPrimePowDiffs_<n>`: certification of every known example;
* `jsp_000947_known_list`: all seven known values satisfy the property;
* structural sieve restrictions: `allPrimePowDiffs_odd` (any such `n > 4`
  is odd), `allPrimePowDiffs_three_dvd` (any such `n > 19` is divisible by
  `3`), `allPrimePowDiffs_five_dvd` (any such `n > 21` is divisible by `5`),
  and `allPrimePowDiffs_fifteen_dvd` (any such `n > 21` is divisible by
  `15`) — the elementary argument behind the observed
  `45, 75, 105 ≡ 0 (mod 15)` pattern.
-/

/-- `AllPrimePowDiffs n` means `n - 2 ^ k` is prime for every `k : ℕ` with
`1 < 2 ^ k < n` (equivalently `k ≥ 1` and `2 ^ k < n`). -/
def AllPrimePowDiffs (n : ℕ) : Prop :=
  ∀ k : ℕ, 1 < 2 ^ k → 2 ^ k < n → Nat.Prime (n - 2 ^ k)

/-- The exponent bound used for the finite case analysis: if `2 ^ k < n ≤ 2 ^ B`
then `k < B`. -/
private theorem pow_two_lt_bound {n k B : ℕ} (hk : 2 ^ k < n) (hn : n ≤ 2 ^ B) :
    k < B := by
  by_contra h
  have hB : B ≤ k := by omega
  have : 2 ^ B ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hB
  omega

/-- Any `n > 4` with the all-prime-differences property is odd:
`n - 2` is prime and even, so `n - 2 = 2`. -/
theorem allPrimePowDiffs_odd {n : ℕ} (hn : 4 < n) (h : AllPrimePowDiffs n) :
    Odd n := by
  have hp : Nat.Prime (n - 2) := h 1 (by norm_num) (by omega)
  by_contra hodd
  have heven : Even n := Nat.not_odd_iff_even.mp hodd
  obtain ⟨m, hm⟩ := heven
  have h2dvd : 2 ∣ n - 2 := ⟨m - 1, by omega⟩
  rcases (Nat.dvd_prime hp).mp h2dvd with h1 | h1
  · norm_num at h1
  · omega

/-- Any `n > 19` with the property is divisible by `3`: the permitted
differences `n - 2, n - 4, n - 8, n - 16` cover `n - 1` and `n + 1` modulo
`3`, so `n ≢ 0 (mod 3)` forces a composite difference. -/
theorem allPrimePowDiffs_three_dvd {n : ℕ} (hn : 19 < n) (h : AllPrimePowDiffs n) :
    3 ∣ n := by
  have p2 : Nat.Prime (n - 2) := h 1 (by norm_num) (by omega)
  have p4 : Nat.Prime (n - 4) := h 2 (by norm_num) (by omega)
  by_contra h3
  have hmod : n % 3 = 1 ∨ n % 3 = 2 := by omega
  rcases hmod with h1 | h1
  · have hd : 3 ∣ n - 4 := by
      rw [Nat.dvd_iff_mod_eq_zero]
      omega
    rcases (Nat.dvd_prime p4).mp hd with e | e
    · norm_num at e
    · omega
  · have hd : 3 ∣ n - 2 := by
      rw [Nat.dvd_iff_mod_eq_zero]
      omega
    rcases (Nat.dvd_prime p2).mp hd with e | e
    · norm_num at e
    · omega

/-- Any `n > 21` with the property is divisible by `5`: the permitted
differences `n - 2, n - 4, n - 8, n - 16` cover all four nonzero residues
`n - 1, n - 2, n - 3, n - 4` modulo `5`, so `n ≢ 0 (mod 5)` forces a
difference divisible by `5` and larger than `5`. -/
theorem allPrimePowDiffs_five_dvd {n : ℕ} (hn : 21 < n) (h : AllPrimePowDiffs n) :
    5 ∣ n := by
  have p2 : Nat.Prime (n - 2) := h 1 (by norm_num) (by omega)
  have p4 : Nat.Prime (n - 4) := h 2 (by norm_num) (by omega)
  have p8 : Nat.Prime (n - 8) := h 3 (by norm_num) (by omega)
  have p16 : Nat.Prime (n - 16) := h 4 (by norm_num) (by omega)
  by_contra h5
  have hmod : n % 5 = 1 ∨ n % 5 = 2 ∨ n % 5 = 3 ∨ n % 5 = 4 := by omega
  rcases hmod with h1 | h1 | h1 | h1
  · have hd : 5 ∣ n - 16 := by
      rw [Nat.dvd_iff_mod_eq_zero]
      omega
    rcases (Nat.dvd_prime p16).mp hd with e | e
    · norm_num at e
    · omega
  · have hd : 5 ∣ n - 2 := by
      rw [Nat.dvd_iff_mod_eq_zero]
      omega
    rcases (Nat.dvd_prime p2).mp hd with e | e
    · norm_num at e
    · omega
  · have hd : 5 ∣ n - 8 := by
      rw [Nat.dvd_iff_mod_eq_zero]
      omega
    rcases (Nat.dvd_prime p8).mp hd with e | e
    · norm_num at e
    · omega
  · have hd : 5 ∣ n - 4 := by
      rw [Nat.dvd_iff_mod_eq_zero]
      omega
    rcases (Nat.dvd_prime p4).mp hd with e | e
    · norm_num at e
    · omega

/-- Combining the previous two lemmas: any `n > 21` with the property is
divisible by `15`. All known examples `45, 75, 105` satisfy this. -/
theorem allPrimePowDiffs_fifteen_dvd {n : ℕ} (hn : 21 < n) (h : AllPrimePowDiffs n) :
    15 ∣ n := by
  have h3 := allPrimePowDiffs_three_dvd (by omega : 19 < n) h
  have h5 := allPrimePowDiffs_five_dvd hn h
  have hlcm : Nat.lcm 3 5 ∣ n := Nat.lcm_dvd h3 h5
  have h15 : Nat.lcm 3 5 = 15 := by norm_num [Nat.lcm]
  rwa [h15] at hlcm

/-- Certification of the known example `n = 4` (`k = 1` only). -/
theorem allPrimePowDiffs_four : AllPrimePowDiffs 4 := by
  intro k h1 h2
  have hb : k < 2 := pow_two_lt_bound h2 (by norm_num)
  have hk0 : 0 < k := by
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp at h1
    · exact hk
  interval_cases k
  all_goals norm_num

/-- Certification of the known example `n = 7`. -/
theorem allPrimePowDiffs_seven : AllPrimePowDiffs 7 := by
  intro k h1 h2
  have hb : k < 3 := pow_two_lt_bound h2 (by norm_num)
  have hk0 : 0 < k := by
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp at h1
    · exact hk
  interval_cases k
  all_goals norm_num

/-- Certification of the known example `n = 15`. -/
theorem allPrimePowDiffs_fifteen : AllPrimePowDiffs 15 := by
  intro k h1 h2
  have hb : k < 4 := pow_two_lt_bound h2 (by norm_num)
  have hk0 : 0 < k := by
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp at h1
    · exact hk
  interval_cases k
  all_goals norm_num

/-- Certification of the known example `n = 21`. -/
theorem allPrimePowDiffs_twentyone : AllPrimePowDiffs 21 := by
  intro k h1 h2
  have hb : k < 5 := pow_two_lt_bound h2 (by norm_num)
  have hk0 : 0 < k := by
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp at h1
    · exact hk
  interval_cases k
  all_goals norm_num

/-- Certification of the known example `n = 45`. -/
theorem allPrimePowDiffs_45 : AllPrimePowDiffs 45 := by
  intro k h1 h2
  have hb : k < 6 := pow_two_lt_bound h2 (by norm_num)
  have hk0 : 0 < k := by
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp at h1
    · exact hk
  interval_cases k
  all_goals norm_num

/-- Certification of the known example `n = 75`. -/
theorem allPrimePowDiffs_75 : AllPrimePowDiffs 75 := by
  intro k h1 h2
  have hb : k < 7 := pow_two_lt_bound h2 (by norm_num)
  have hk0 : 0 < k := by
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp at h1
    · exact hk
  interval_cases k
  all_goals norm_num

/-- Certification of the known example `n = 105`. -/
theorem allPrimePowDiffs_105 : AllPrimePowDiffs 105 := by
  intro k h1 h2
  have hb : k < 7 := pow_two_lt_bound h2 (by norm_num)
  have hk0 : 0 < k := by
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp at h1
    · exact hk
  interval_cases k
  all_goals norm_num

/-- All seven known values satisfy the all-prime-differences property. -/
theorem jsp_000947_known_list :
    ∀ n ∈ ({4, 7, 15, 21, 45, 75, 105} : Finset ℕ), AllPrimePowDiffs n := by
  intro n hn
  fin_cases hn
  · exact allPrimePowDiffs_four
  · exact allPrimePowDiffs_seven
  · exact allPrimePowDiffs_fifteen
  · exact allPrimePowDiffs_twentyone
  · exact allPrimePowDiffs_45
  · exact allPrimePowDiffs_75
  · exact allPrimePowDiffs_105

/-- **JSP-000947.** There exists a positive integer whose differences from
twice every permitted smaller power of two are all prime. Witness: `n = 7`,
since `1 < 2 ^ k < 7` forces `k ∈ {1, 2}` and `7 - 2 = 5`, `7 - 4 = 3`
are prime. -/
theorem jsp_000947 : ∃ n : ℕ, 0 < n ∧ AllPrimePowDiffs n :=
  ⟨7, by norm_num, allPrimePowDiffs_seven⟩

#print axioms jsp_000947
#print axioms jsp_000947_known_list
#print axioms allPrimePowDiffs_fifteen_dvd
