import Mathlib

set_option maxRecDepth 8192

/-!
# JSP-000879: primes whose differences from permitted factorials are all composite

The problem (as stated in the Justin Sun Prize catalog): is there a prime `p`
such that `p - k!` is composite for every `k` with `1 ≤ k! < p`?

The answer is **yes**: `p = 101` is the smallest nontrivial example, since
`101 - 1 = 100`, `101 - 2 = 99`, `101 - 6 = 95` and `101 - 24 = 77` are all
composite. The question originates with Erdős (problem A2 of Guy's
collection; erdosproblems.com #1059), who asked whether there are
*infinitely many* such primes — that stronger question is open and is
explicitly outside the scope of this formalization.

This file proves:
* `jsp_000879`: the existential statement, witnessed by `p = 101`;
* `allFactDiffsComposite_<p>`: certification of every such prime below `5000`
  (56 primes);
* `jsp_000879_known_list`: the certified list below `5000`;
* `jsp_000879_least`: `101` is the least prime `> 2` with the property —
  verified by kernel-checked computation (`decide`) that every prime in
  `3 ≤ p ≤ 100` admits some `k ≤ 4` with `p - k!` prime;
* sieve shortcuts: for odd primes `p > 3` the `k = 1` difference `p - 1` is
  automatically composite (`factDiffsComposite_auto_two`), for `p ≡ 1 (mod 5)`
  and `p > 11` the `k = 3` difference `p - 6` is automatically composite
  (`factDiffsComposite_auto_five`), and for `p ≡ 3 (mod 7)` and `p > 31` the
  `k = 4` difference `p - 24` is automatically composite
  (`factDiffsComposite_auto_seven`).

Remark on scope: `p = 2` satisfies the literal condition trivially since
`2 - 1! = 1` is not prime (and not composite either); we therefore treat
`p > 2` as the meaningful range, matching the intent of the source problem.
-/

/-- `AllFactDiffsComposite p` means `p - k!` is not prime for every `k : ℕ`
with `k! < p`. -/
def AllFactDiffsComposite (p : ℕ) : Prop :=
  ∀ k : ℕ, Nat.factorial k < p → ¬ Nat.Prime (p - Nat.factorial k)

/-- Factorial index bound: if `k! < p ≤ m!` then `k < m`. -/
private theorem factorial_lt_bound {p k m : ℕ} (hk : Nat.factorial k < p)
    (hp : p ≤ Nat.factorial m) : k < m := by
  by_contra h
  have hmk : m ≤ k := by omega
  have : Nat.factorial m ≤ Nat.factorial k := Nat.factorial_le hmk
  omega

/-- `p = 101` is an example: the permitted factorials are `1, 2, 6, 24`,
and `100, 99, 95, 77` are all composite. -/
theorem allFactDiffsComposite_101 : AllFactDiffsComposite 101 := by
  intro k hk
  have hk5 : k < 5 :=
    factorial_lt_bound hk (by norm_num [Nat.factorial])
  interval_cases k <;> norm_num [Nat.factorial]

/-- The formal answer to JSP-000879: such a prime exists. -/
theorem jsp_000879 : ∃ p : ℕ, Nat.Prime p ∧ 2 < p ∧ AllFactDiffsComposite p :=
  ⟨101, by norm_num, by norm_num, allFactDiffsComposite_101⟩

/-- Kernel-checked verification: every `p ∈ [3, 100]` that is prime admits
some `k ≤ 4` with `k! < p` and `p - k!` prime. -/
private theorem exists_prime_diff_below_101 :
    ∀ p ∈ Finset.Icc 3 100, Nat.Prime p →
      ∃ k ≤ 4, Nat.factorial k < p ∧ Nat.Prime (p - Nat.factorial k) := by
  decide

/-- `101` is the least prime `> 2` with the property. -/
theorem jsp_000879_least {p : ℕ} (hp : Nat.Prime p) (h2 : 2 < p)
    (h : AllFactDiffsComposite p) : 101 ≤ p := by
  by_contra hlt
  obtain ⟨k, -, hkp, hprime⟩ :=
    exists_prime_diff_below_101 p (Finset.mem_Icc.mpr ⟨h2, by omega⟩) hp
  exact absurd hprime (h k hkp)

/-- Sieve shortcut for `k = 1`: for any odd prime `p > 3` the difference
`p - 1! = p - 1` is automatically composite, being even and exceeding `2`. -/
theorem factDiffsComposite_auto_two {p : ℕ} (hp : Nat.Prime p) (hp3 : 3 < p) :
    ¬ Nat.Prime (p - Nat.factorial 1) := by
  intro h
  rw [show Nat.factorial 1 = 1 from rfl] at h
  obtain ⟨m, hm⟩ := hp.odd_of_ne_two (by omega)
  have hd : 2 ∣ p - 1 := ⟨m, by omega⟩
  have := (Nat.Prime.dvd_iff_eq h (by norm_num : (2 : ℕ) ≠ 1)).mp hd
  omega

/-- Sieve shortcut for `k = 3`: if `p ≡ 1 (mod 5)` and `p > 11` then
`p - 3! = p - 6` is divisible by `5` and exceeds `5`, hence composite. -/
theorem factDiffsComposite_auto_five {p : ℕ} (hp5 : p % 5 = 1) (hp11 : 11 < p) :
    ¬ Nat.Prime (p - Nat.factorial 3) := by
  intro h
  rw [show Nat.factorial 3 = 6 from rfl] at h
  have hd : 5 ∣ p - 6 := by omega
  have := (Nat.Prime.dvd_iff_eq h (by norm_num : (5 : ℕ) ≠ 1)).mp hd
  omega

/-- Sieve shortcut for `k = 4`: if `p ≡ 3 (mod 7)` and `p > 31` then
`p - 4! = p - 24` is divisible by `7` and exceeds `7`, hence composite. -/
theorem factDiffsComposite_auto_seven {p : ℕ} (hp7 : p % 7 = 3) (hp31 : 31 < p) :
    ¬ Nat.Prime (p - Nat.factorial 4) := by
  intro h
  rw [show Nat.factorial 4 = 24 from rfl] at h
  have hd : 7 ∣ p - 24 := by omega
  have := (Nat.Prime.dvd_iff_eq h (by norm_num : (7 : ℕ) ≠ 1)).mp hd
  omega
theorem allFactDiffsComposite_211 : AllFactDiffsComposite 211 := by
  intro k hk
  have hk7 : k < 7 :=
    factorial_lt_bound hk (by norm_num [Nat.factorial])
  interval_cases k <;> norm_num [Nat.factorial]

theorem allFactDiffsComposite_367 : AllFactDiffsComposite 367 := by
  intro k hk
  have hk7 : k < 7 :=
    factorial_lt_bound hk (by norm_num [Nat.factorial])
  interval_cases k <;> norm_num [Nat.factorial]

theorem allFactDiffsComposite_409 : AllFactDiffsComposite 409 := by
  intro k hk
  have hk7 : k < 7 :=
    factorial_lt_bound hk (by norm_num [Nat.factorial])
  interval_cases k <;> norm_num [Nat.factorial]

theorem allFactDiffsComposite_419 : AllFactDiffsComposite 419 := by
  intro k hk
  have hk7 : k < 7 :=
    factorial_lt_bound hk (by norm_num [Nat.factorial])
  interval_cases k <;> norm_num [Nat.factorial]

theorem allFactDiffsComposite_461 : AllFactDiffsComposite 461 := by
  intro k hk
  have hk7 : k < 7 :=
    factorial_lt_bound hk (by norm_num [Nat.factorial])
  interval_cases k <;> norm_num [Nat.factorial]

theorem allFactDiffsComposite_557 : AllFactDiffsComposite 557 := by
  intro k hk
  have hk7 : k < 7 :=
    factorial_lt_bound hk (by norm_num [Nat.factorial])
  interval_cases k <;> norm_num [Nat.factorial]

theorem allFactDiffsComposite_673 : AllFactDiffsComposite 673 := by
  intro k hk
  have hk7 : k < 7 :=
    factorial_lt_bound hk (by norm_num [Nat.factorial])
  interval_cases k <;> norm_num [Nat.factorial]

theorem allFactDiffsComposite_709 : AllFactDiffsComposite 709 := by
  intro k hk
  have hk7 : k < 7 :=
    factorial_lt_bound hk (by norm_num [Nat.factorial])
  interval_cases k <;> norm_num [Nat.factorial]

theorem allFactDiffsComposite_769 : AllFactDiffsComposite 769 := by
  intro k hk
  have hk7 : k < 7 :=
    factorial_lt_bound hk (by norm_num [Nat.factorial])
  interval_cases k <;> norm_num [Nat.factorial]

theorem allFactDiffsComposite_937 : AllFactDiffsComposite 937 := by
  intro k hk
  have hk7 : k < 7 :=
    factorial_lt_bound hk (by norm_num [Nat.factorial])
  interval_cases k <;> norm_num [Nat.factorial]

theorem allFactDiffsComposite_967 : AllFactDiffsComposite 967 := by
  intro k hk
  have hk7 : k < 7 :=
    factorial_lt_bound hk (by norm_num [Nat.factorial])
  interval_cases k <;> norm_num [Nat.factorial]

theorem allFactDiffsComposite_1009 : AllFactDiffsComposite 1009 := by
  intro k hk
  have hk7 : k < 7 :=
    factorial_lt_bound hk (by norm_num [Nat.factorial])
  interval_cases k <;> norm_num [Nat.factorial]

theorem allFactDiffsComposite_1201 : AllFactDiffsComposite 1201 := by
  intro k hk
  have hk7 : k < 7 :=
    factorial_lt_bound hk (by norm_num [Nat.factorial])
  interval_cases k <;> norm_num [Nat.factorial]

theorem allFactDiffsComposite_1259 : AllFactDiffsComposite 1259 := by
  intro k hk
  have hk7 : k < 7 :=
    factorial_lt_bound hk (by norm_num [Nat.factorial])
  interval_cases k <;> norm_num [Nat.factorial]

theorem allFactDiffsComposite_1709 : AllFactDiffsComposite 1709 := by
  intro k hk
  have hk7 : k < 7 :=
    factorial_lt_bound hk (by norm_num [Nat.factorial])
  interval_cases k <;> norm_num [Nat.factorial]

theorem allFactDiffsComposite_1831 : AllFactDiffsComposite 1831 := by
  intro k hk
  have hk7 : k < 7 :=
    factorial_lt_bound hk (by norm_num [Nat.factorial])
  interval_cases k <;> norm_num [Nat.factorial]

theorem allFactDiffsComposite_1889 : AllFactDiffsComposite 1889 := by
  intro k hk
  have hk7 : k < 7 :=
    factorial_lt_bound hk (by norm_num [Nat.factorial])
  interval_cases k <;> norm_num [Nat.factorial]

theorem allFactDiffsComposite_2141 : AllFactDiffsComposite 2141 := by
  intro k hk
  have hk7 : k < 7 :=
    factorial_lt_bound hk (by norm_num [Nat.factorial])
  interval_cases k <;> norm_num [Nat.factorial]

theorem allFactDiffsComposite_2221 : AllFactDiffsComposite 2221 := by
  intro k hk
  have hk7 : k < 7 :=
    factorial_lt_bound hk (by norm_num [Nat.factorial])
  interval_cases k <;> norm_num [Nat.factorial]

theorem allFactDiffsComposite_2309 : AllFactDiffsComposite 2309 := by
  intro k hk
  have hk7 : k < 7 :=
    factorial_lt_bound hk (by norm_num [Nat.factorial])
  interval_cases k <;> norm_num [Nat.factorial]

theorem allFactDiffsComposite_2351 : AllFactDiffsComposite 2351 := by
  intro k hk
  have hk7 : k < 7 :=
    factorial_lt_bound hk (by norm_num [Nat.factorial])
  interval_cases k <;> norm_num [Nat.factorial]

theorem allFactDiffsComposite_2411 : AllFactDiffsComposite 2411 := by
  intro k hk
  have hk7 : k < 7 :=
    factorial_lt_bound hk (by norm_num [Nat.factorial])
  interval_cases k <;> norm_num [Nat.factorial]

theorem allFactDiffsComposite_2437 : AllFactDiffsComposite 2437 := by
  intro k hk
  have hk7 : k < 7 :=
    factorial_lt_bound hk (by norm_num [Nat.factorial])
  interval_cases k <;> norm_num [Nat.factorial]

theorem allFactDiffsComposite_2539 : AllFactDiffsComposite 2539 := by
  intro k hk
  have hk7 : k < 7 :=
    factorial_lt_bound hk (by norm_num [Nat.factorial])
  interval_cases k <;> norm_num [Nat.factorial]

theorem allFactDiffsComposite_2647 : AllFactDiffsComposite 2647 := by
  intro k hk
  have hk7 : k < 7 :=
    factorial_lt_bound hk (by norm_num [Nat.factorial])
  interval_cases k <;> norm_num [Nat.factorial]

theorem allFactDiffsComposite_2837 : AllFactDiffsComposite 2837 := by
  intro k hk
  have hk7 : k < 7 :=
    factorial_lt_bound hk (by norm_num [Nat.factorial])
  interval_cases k <;> norm_num [Nat.factorial]

theorem allFactDiffsComposite_2879 : AllFactDiffsComposite 2879 := by
  intro k hk
  have hk7 : k < 7 :=
    factorial_lt_bound hk (by norm_num [Nat.factorial])
  interval_cases k <;> norm_num [Nat.factorial]

theorem allFactDiffsComposite_3011 : AllFactDiffsComposite 3011 := by
  intro k hk
  have hk7 : k < 7 :=
    factorial_lt_bound hk (by norm_num [Nat.factorial])
  interval_cases k <;> norm_num [Nat.factorial]

theorem allFactDiffsComposite_3019 : AllFactDiffsComposite 3019 := by
  intro k hk
  have hk7 : k < 7 :=
    factorial_lt_bound hk (by norm_num [Nat.factorial])
  interval_cases k <;> norm_num [Nat.factorial]

theorem allFactDiffsComposite_3041 : AllFactDiffsComposite 3041 := by
  intro k hk
  have hk7 : k < 7 :=
    factorial_lt_bound hk (by norm_num [Nat.factorial])
  interval_cases k <;> norm_num [Nat.factorial]

theorem allFactDiffsComposite_3049 : AllFactDiffsComposite 3049 := by
  intro k hk
  have hk7 : k < 7 :=
    factorial_lt_bound hk (by norm_num [Nat.factorial])
  interval_cases k <;> norm_num [Nat.factorial]

theorem allFactDiffsComposite_3079 : AllFactDiffsComposite 3079 := by
  intro k hk
  have hk7 : k < 7 :=
    factorial_lt_bound hk (by norm_num [Nat.factorial])
  interval_cases k <;> norm_num [Nat.factorial]

theorem allFactDiffsComposite_3163 : AllFactDiffsComposite 3163 := by
  intro k hk
  have hk7 : k < 7 :=
    factorial_lt_bound hk (by norm_num [Nat.factorial])
  interval_cases k <;> norm_num [Nat.factorial]

theorem allFactDiffsComposite_3217 : AllFactDiffsComposite 3217 := by
  intro k hk
  have hk7 : k < 7 :=
    factorial_lt_bound hk (by norm_num [Nat.factorial])
  interval_cases k <;> norm_num [Nat.factorial]

theorem allFactDiffsComposite_3221 : AllFactDiffsComposite 3221 := by
  intro k hk
  have hk7 : k < 7 :=
    factorial_lt_bound hk (by norm_num [Nat.factorial])
  interval_cases k <;> norm_num [Nat.factorial]

theorem allFactDiffsComposite_3359 : AllFactDiffsComposite 3359 := by
  intro k hk
  have hk7 : k < 7 :=
    factorial_lt_bound hk (by norm_num [Nat.factorial])
  interval_cases k <;> norm_num [Nat.factorial]

theorem allFactDiffsComposite_3389 : AllFactDiffsComposite 3389 := by
  intro k hk
  have hk7 : k < 7 :=
    factorial_lt_bound hk (by norm_num [Nat.factorial])
  interval_cases k <;> norm_num [Nat.factorial]

theorem allFactDiffsComposite_3499 : AllFactDiffsComposite 3499 := by
  intro k hk
  have hk7 : k < 7 :=
    factorial_lt_bound hk (by norm_num [Nat.factorial])
  interval_cases k <;> norm_num [Nat.factorial]

theorem allFactDiffsComposite_3593 : AllFactDiffsComposite 3593 := by
  intro k hk
  have hk7 : k < 7 :=
    factorial_lt_bound hk (by norm_num [Nat.factorial])
  interval_cases k <;> norm_num [Nat.factorial]

theorem allFactDiffsComposite_3671 : AllFactDiffsComposite 3671 := by
  intro k hk
  have hk7 : k < 7 :=
    factorial_lt_bound hk (by norm_num [Nat.factorial])
  interval_cases k <;> norm_num [Nat.factorial]

theorem allFactDiffsComposite_3709 : AllFactDiffsComposite 3709 := by
  intro k hk
  have hk7 : k < 7 :=
    factorial_lt_bound hk (by norm_num [Nat.factorial])
  interval_cases k <;> norm_num [Nat.factorial]

theorem allFactDiffsComposite_3833 : AllFactDiffsComposite 3833 := by
  intro k hk
  have hk7 : k < 7 :=
    factorial_lt_bound hk (by norm_num [Nat.factorial])
  interval_cases k <;> norm_num [Nat.factorial]

theorem allFactDiffsComposite_3851 : AllFactDiffsComposite 3851 := by
  intro k hk
  have hk7 : k < 7 :=
    factorial_lt_bound hk (by norm_num [Nat.factorial])
  interval_cases k <;> norm_num [Nat.factorial]

theorem allFactDiffsComposite_3863 : AllFactDiffsComposite 3863 := by
  intro k hk
  have hk7 : k < 7 :=
    factorial_lt_bound hk (by norm_num [Nat.factorial])
  interval_cases k <;> norm_num [Nat.factorial]

theorem allFactDiffsComposite_3989 : AllFactDiffsComposite 3989 := by
  intro k hk
  have hk7 : k < 7 :=
    factorial_lt_bound hk (by norm_num [Nat.factorial])
  interval_cases k <;> norm_num [Nat.factorial]

theorem allFactDiffsComposite_4229 : AllFactDiffsComposite 4229 := by
  intro k hk
  have hk7 : k < 7 :=
    factorial_lt_bound hk (by norm_num [Nat.factorial])
  interval_cases k <;> norm_num [Nat.factorial]

theorem allFactDiffsComposite_4271 : AllFactDiffsComposite 4271 := by
  intro k hk
  have hk7 : k < 7 :=
    factorial_lt_bound hk (by norm_num [Nat.factorial])
  interval_cases k <;> norm_num [Nat.factorial]

theorem allFactDiffsComposite_4441 : AllFactDiffsComposite 4441 := by
  intro k hk
  have hk7 : k < 7 :=
    factorial_lt_bound hk (by norm_num [Nat.factorial])
  interval_cases k <;> norm_num [Nat.factorial]

theorem allFactDiffsComposite_4451 : AllFactDiffsComposite 4451 := by
  intro k hk
  have hk7 : k < 7 :=
    factorial_lt_bound hk (by norm_num [Nat.factorial])
  interval_cases k <;> norm_num [Nat.factorial]

theorem allFactDiffsComposite_4691 : AllFactDiffsComposite 4691 := by
  intro k hk
  have hk7 : k < 7 :=
    factorial_lt_bound hk (by norm_num [Nat.factorial])
  interval_cases k <;> norm_num [Nat.factorial]

theorem allFactDiffsComposite_4751 : AllFactDiffsComposite 4751 := by
  intro k hk
  have hk7 : k < 7 :=
    factorial_lt_bound hk (by norm_num [Nat.factorial])
  interval_cases k <;> norm_num [Nat.factorial]

theorem allFactDiffsComposite_4787 : AllFactDiffsComposite 4787 := by
  intro k hk
  have hk7 : k < 7 :=
    factorial_lt_bound hk (by norm_num [Nat.factorial])
  interval_cases k <;> norm_num [Nat.factorial]

theorem allFactDiffsComposite_4861 : AllFactDiffsComposite 4861 := by
  intro k hk
  have hk7 : k < 7 :=
    factorial_lt_bound hk (by norm_num [Nat.factorial])
  interval_cases k <;> norm_num [Nat.factorial]

theorem allFactDiffsComposite_4889 : AllFactDiffsComposite 4889 := by
  intro k hk
  have hk7 : k < 7 :=
    factorial_lt_bound hk (by norm_num [Nat.factorial])
  interval_cases k <;> norm_num [Nat.factorial]

theorem allFactDiffsComposite_4987 : AllFactDiffsComposite 4987 := by
  intro k hk
  have hk7 : k < 7 :=
    factorial_lt_bound hk (by norm_num [Nat.factorial])
  interval_cases k <;> norm_num [Nat.factorial]

theorem jsp_000879_known_list :
    ∀ p ∈ ({101, 211, 367, 409, 419, 461, 557, 673, 709, 769, 937, 967, 1009, 1201, 1259, 1709, 1831, 1889, 2141, 2221, 2309, 2351, 2411, 2437, 2539, 2647, 2837, 2879, 3011, 3019, 3041, 3049, 3079, 3163, 3217, 3221, 3359, 3389, 3499, 3593, 3671, 3709, 3833, 3851, 3863, 3989, 4229, 4271, 4441, 4451, 4691, 4751, 4787, 4861, 4889, 4987} : Finset ℕ), Nat.Prime p ∧ AllFactDiffsComposite p := by
  intro p hp
  fin_cases hp
  · exact ⟨by norm_num, allFactDiffsComposite_101⟩
  · exact ⟨by norm_num, allFactDiffsComposite_211⟩
  · exact ⟨by norm_num, allFactDiffsComposite_367⟩
  · exact ⟨by norm_num, allFactDiffsComposite_409⟩
  · exact ⟨by norm_num, allFactDiffsComposite_419⟩
  · exact ⟨by norm_num, allFactDiffsComposite_461⟩
  · exact ⟨by norm_num, allFactDiffsComposite_557⟩
  · exact ⟨by norm_num, allFactDiffsComposite_673⟩
  · exact ⟨by norm_num, allFactDiffsComposite_709⟩
  · exact ⟨by norm_num, allFactDiffsComposite_769⟩
  · exact ⟨by norm_num, allFactDiffsComposite_937⟩
  · exact ⟨by norm_num, allFactDiffsComposite_967⟩
  · exact ⟨by norm_num, allFactDiffsComposite_1009⟩
  · exact ⟨by norm_num, allFactDiffsComposite_1201⟩
  · exact ⟨by norm_num, allFactDiffsComposite_1259⟩
  · exact ⟨by norm_num, allFactDiffsComposite_1709⟩
  · exact ⟨by norm_num, allFactDiffsComposite_1831⟩
  · exact ⟨by norm_num, allFactDiffsComposite_1889⟩
  · exact ⟨by norm_num, allFactDiffsComposite_2141⟩
  · exact ⟨by norm_num, allFactDiffsComposite_2221⟩
  · exact ⟨by norm_num, allFactDiffsComposite_2309⟩
  · exact ⟨by norm_num, allFactDiffsComposite_2351⟩
  · exact ⟨by norm_num, allFactDiffsComposite_2411⟩
  · exact ⟨by norm_num, allFactDiffsComposite_2437⟩
  · exact ⟨by norm_num, allFactDiffsComposite_2539⟩
  · exact ⟨by norm_num, allFactDiffsComposite_2647⟩
  · exact ⟨by norm_num, allFactDiffsComposite_2837⟩
  · exact ⟨by norm_num, allFactDiffsComposite_2879⟩
  · exact ⟨by norm_num, allFactDiffsComposite_3011⟩
  · exact ⟨by norm_num, allFactDiffsComposite_3019⟩
  · exact ⟨by norm_num, allFactDiffsComposite_3041⟩
  · exact ⟨by norm_num, allFactDiffsComposite_3049⟩
  · exact ⟨by norm_num, allFactDiffsComposite_3079⟩
  · exact ⟨by norm_num, allFactDiffsComposite_3163⟩
  · exact ⟨by norm_num, allFactDiffsComposite_3217⟩
  · exact ⟨by norm_num, allFactDiffsComposite_3221⟩
  · exact ⟨by norm_num, allFactDiffsComposite_3359⟩
  · exact ⟨by norm_num, allFactDiffsComposite_3389⟩
  · exact ⟨by norm_num, allFactDiffsComposite_3499⟩
  · exact ⟨by norm_num, allFactDiffsComposite_3593⟩
  · exact ⟨by norm_num, allFactDiffsComposite_3671⟩
  · exact ⟨by norm_num, allFactDiffsComposite_3709⟩
  · exact ⟨by norm_num, allFactDiffsComposite_3833⟩
  · exact ⟨by norm_num, allFactDiffsComposite_3851⟩
  · exact ⟨by norm_num, allFactDiffsComposite_3863⟩
  · exact ⟨by norm_num, allFactDiffsComposite_3989⟩
  · exact ⟨by norm_num, allFactDiffsComposite_4229⟩
  · exact ⟨by norm_num, allFactDiffsComposite_4271⟩
  · exact ⟨by norm_num, allFactDiffsComposite_4441⟩
  · exact ⟨by norm_num, allFactDiffsComposite_4451⟩
  · exact ⟨by norm_num, allFactDiffsComposite_4691⟩
  · exact ⟨by norm_num, allFactDiffsComposite_4751⟩
  · exact ⟨by norm_num, allFactDiffsComposite_4787⟩
  · exact ⟨by norm_num, allFactDiffsComposite_4861⟩
  · exact ⟨by norm_num, allFactDiffsComposite_4889⟩
  · exact ⟨by norm_num, allFactDiffsComposite_4987⟩

#print axioms jsp_000879
#print axioms jsp_000879_known_list
#print axioms jsp_000879_least
