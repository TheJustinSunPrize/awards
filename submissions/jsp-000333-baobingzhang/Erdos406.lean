import Mathlib

/-!
# Erdős Problem 406: Narkiewicz's upper bound

Erdős asked whether only finitely many powers of `2` have only the digits `0` and `1` in base `3`.
Narkiewicz (1980) proved that the number of `n ≤ x` for which `2 ^ n` has only ternary digits
`0` and `1` is `≪ x ^ (log 2 / log 3)`. We prove this with the explicit constant
`2 ^ (1 - log 2 / log 3) ≈ 1.29` for all real `x ≥ 1` (`n = 0` is counted, since `2 ^ 0 = 1`);
the constant is attained at `x = 2`, where `n = 0, 2` qualify.

The digit condition `Nat.digits 3 m ⊆ [0, 1]` is copied verbatim from Google DeepMind's
formal-conjectures project (`FormalConjectures/ErdosProblems/406.lean`, Apache-2.0).
-/

namespace Erdos406

/-! ### Ternary digits -/

/-- If all base-`3` digits of `a` are `0` or `1`, then so is its `i`-th digit `a / 3 ^ i % 3`. -/
theorem digit_le_one {a : ℕ} (h : Nat.digits 3 a ⊆ [0, 1]) (i : ℕ) : a / 3 ^ i % 3 ≤ 1 := by
  rw [← Nat.getD_digits a i (by norm_num)]
  rw [List.getD_eq_getElem?_getD]
  rcases hd : (Nat.digits 3 a)[i]? with _ | d
  · simp
  · have hmem : d ∈ Nat.digits 3 a := List.mem_of_getElem? hd
    have := h hmem
    simp only [List.mem_cons, List.not_mem_nil, or_false] at this
    simp only [Option.getD_some]
    omega

/-- Two numbers whose lowest `k` base-`3` digits agree are congruent modulo `3 ^ k`. -/
theorem mod_pow_eq_of_digits_eq {a b : ℕ} :
    ∀ k : ℕ, (∀ i < k, a / 3 ^ i % 3 = b / 3 ^ i % 3) → a % 3 ^ k = b % 3 ^ k
  | 0, _ => by simp [Nat.mod_one]
  | k + 1, h => by
    rw [Nat.mod_pow_succ, Nat.mod_pow_succ, mod_pow_eq_of_digits_eq k (fun i hi => h i (by omega)),
      h k (by omega)]

/-- `3` never divides `2 ^ n`. -/
theorem two_pow_mod_three_ne_zero (n : ℕ) : 2 ^ n % 3 ≠ 0 := by
  intro h
  have h3 : 3 ∣ 2 ^ n := Nat.dvd_of_mod_eq_zero h
  have := (Nat.prime_three.dvd_of_dvd_pow h3)
  omega

/-! ### The order of `2` modulo `3 ^ (j + 1)` -/

/-- If `2 ^ m ≡ 1 (mod 3 ^ (j + 1))` then `m` is even. -/
theorem even_of_two_pow_eq_one {j m : ℕ} (h : (2 : ZMod (3 ^ (j + 1))) ^ m = 1) : Even m := by
  have h' : ((2 ^ m : ℕ) : ZMod (3 ^ (j + 1))) = ((1 : ℕ) : ZMod (3 ^ (j + 1))) := by
    push_cast; exact h
  rw [ZMod.natCast_eq_natCast_iff'] at h'
  have h3 : 2 ^ m % 3 = 1 % 3 := by
    have hd : 3 ∣ 3 ^ (j + 1) := dvd_pow_self 3 (Nat.succ_ne_zero j)
    rw [← Nat.mod_mod_of_dvd (2 ^ m) hd, h', Nat.mod_mod_of_dvd 1 hd]
  rcases Nat.even_or_odd m with he | ⟨t, rfl⟩
  · exact he
  · exfalso
    have h4 : 4 ^ t % 3 = 1 := by
      rw [Nat.pow_mod]; norm_num
    have : 2 ^ (2 * t + 1) = 4 ^ t * 2 := by
      rw [pow_succ, pow_mul]; norm_num
    rw [this, Nat.mul_mod, h4] at h3
    norm_num at h3

/-- The multiplicative order of `2` modulo `3 ^ (j + 1)` is `2 * 3 ^ j`. -/
theorem orderOf_two (j : ℕ) : orderOf (2 : ZMod (3 ^ (j + 1))) = 2 * 3 ^ j := by
  have hsq : orderOf ((2 : ZMod (3 ^ (j + 1))) ^ 2) = 3 ^ j := by
    have h4 : (2 : ZMod (3 ^ (j + 1))) ^ 2 = 1 + ((3 : ℕ) : ZMod (3 ^ (j + 1))) := by norm_num
    rw [h4]
    exact ZMod.orderOf_one_add_prime Nat.prime_three (by norm_num) j
  apply Nat.dvd_antisymm
  · apply orderOf_dvd_of_pow_eq_one
    rw [pow_mul, ← hsq, pow_orderOf_eq_one]
  · have h2 : 2 ∣ orderOf (2 : ZMod (3 ^ (j + 1))) :=
      even_iff_two_dvd.mp (even_of_two_pow_eq_one (pow_orderOf_eq_one _))
    have h3 : 3 ^ j ∣ orderOf (2 : ZMod (3 ^ (j + 1))) := hsq ▸ orderOf_pow_dvd 2
    exact Nat.Coprime.mul_dvd_of_dvd_of_dvd (Nat.Coprime.pow_right _ (by norm_num)) h2 h3

/-- `n ↦ 2 ^ n mod 3 ^ (j + 1)` is injective on `[0, 2 * 3 ^ j)`. -/
theorem eq_of_two_pow_mod_eq {j a b : ℕ} (ha : a < 2 * 3 ^ j) (hb : b < 2 * 3 ^ j)
    (h : 2 ^ a % 3 ^ (j + 1) = 2 ^ b % 3 ^ (j + 1)) : a = b := by
  have hcop : Nat.Coprime 2 (3 ^ (j + 1)) := Nat.Coprime.pow_right _ (by norm_num)
  set u : (ZMod (3 ^ (j + 1)))ˣ := ZMod.unitOfCoprime 2 hcop with hu
  have hu2 : (u : ZMod (3 ^ (j + 1))) = 2 := by
    rw [hu, ZMod.coe_unitOfCoprime]; norm_num
  have hord : orderOf u = 2 * 3 ^ j := by
    rw [← orderOf_units, hu2, orderOf_two]
  have hz : ((2 ^ a : ℕ) : ZMod (3 ^ (j + 1))) = ((2 ^ b : ℕ) : ZMod (3 ^ (j + 1))) :=
    (ZMod.natCast_eq_natCast_iff' _ _ _).mpr h
  have hpow : u ^ a = u ^ b := by
    ext
    push_cast [Units.val_pow_eq_pow_val, hu2] at hz ⊢
    exact hz
  rw [pow_inj_mod, hord, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at hpow
  exact hpow

/-! ### The discrete bound -/

/-- Narkiewicz's counting bound in discrete form: among `0 ≤ n < 2 * 3 ^ j`, at most `2 ^ j`
exponents `n` have `2 ^ n` with only the ternary digits `0` and `1`. -/
theorem card_filter_range_le (j : ℕ) :
    ((Finset.range (2 * 3 ^ j)).filter (fun n => Nat.digits 3 (2 ^ n) ⊆ [0, 1])).card ≤ 2 ^ j := by
  classical
  let f : ℕ → (Fin j → Bool) := fun n i => decide (2 ^ n / 3 ^ (i.val + 1) % 3 = 1)
  have hcard : (Finset.univ : Finset (Fin j → Bool)).card = 2 ^ j := by simp
  rw [← hcard]
  refine Finset.card_le_card_of_injOn f (fun _ _ => Finset.mem_coe.mpr (Finset.mem_univ _)) ?_
  intro n hn m hm hfnm
  simp only [Finset.coe_filter, Finset.mem_range, Set.mem_ofPred_eq] at hn hm
  apply eq_of_two_pow_mod_eq hn.1 hm.1
  apply mod_pow_eq_of_digits_eq
  intro i hi
  have hdn := digit_le_one hn.2 i
  have hdm := digit_le_one hm.2 i
  rcases i with _ | i
  · have h0n := two_pow_mod_three_ne_zero n
    have h0m := two_pow_mod_three_ne_zero m
    simp only [pow_zero, Nat.div_one] at hdn hdm ⊢
    omega
  · have := congrFun hfnm ⟨i, by omega⟩
    simp only [f, decide_eq_decide] at this
    omega

/-- Monotone version of `card_filter_range_le`: if `N ≤ 2 * 3 ^ j` then among `0 ≤ n < N` at most
`2 ^ j` exponents qualify. -/
theorem card_filter_range_le_of_le {N j : ℕ} (hN : N ≤ 2 * 3 ^ j) :
    ((Finset.range N).filter (fun n => Nat.digits 3 (2 ^ n) ⊆ [0, 1])).card ≤ 2 ^ j :=
  (Finset.card_le_card (Finset.filter_subset_filter _ (Finset.range_subset_range.mpr hN))).trans
    (card_filter_range_le j)

/-! ### The real-exponent bound -/

/-- `3 ^ (log 2 / log 3) = 2`. -/
theorem three_rpow_alpha : (3 : ℝ) ^ (Real.log 2 / Real.log 3) = 2 := by
  have h3 : Real.log 3 ≠ 0 := (Real.log_pos (by norm_num)).ne'
  rw [Real.rpow_def_of_pos (by norm_num), mul_div_cancel₀ _ h3, Real.exp_log (by norm_num)]

/-- `0 ≤ log 2 / log 3 ≤ 1`. -/
theorem alpha_mem : 0 ≤ Real.log 2 / Real.log 3 ∧ Real.log 2 / Real.log 3 ≤ 1 := by
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  refine ⟨div_nonneg h2.le h3.le, (div_le_one h3).mpr ?_⟩
  exact Real.log_le_log (by norm_num) (by norm_num)

/-- The counted set, for real `x ≥ 0`, is the filter of `range (⌊x⌋₊ + 1)`. -/
theorem set_eq_filter {x : ℝ} (hx : 0 ≤ x) :
    {n : ℕ | (n : ℝ) ≤ x ∧ Nat.digits 3 (2 ^ n) ⊆ [0, 1]} =
      ↑((Finset.range (⌊x⌋₊ + 1)).filter (fun n => Nat.digits 3 (2 ^ n) ⊆ [0, 1])) := by
  ext n
  simp only [Set.mem_ofPred_eq, Finset.coe_filter, Finset.mem_range, Nat.lt_succ_iff,
    Nat.le_floor_iff hx]

/-- **Narkiewicz (1980)**, explicit form. For every real `x ≥ 1`, the number of natural numbers
`n ≤ x` such that every base-`3` digit of `2 ^ n` is `0` or `1` is at most
`2 ^ (1 - log 2 / log 3) * x ^ (log 2 / log 3)`, where `2 ^ (1 - log 2 / log 3) ≈ 1.2915`. -/
theorem erdos_406_narkiewicz (x : ℝ) (hx : 1 ≤ x) :
    ({n : ℕ | (n : ℝ) ≤ x ∧ Nat.digits 3 (2 ^ n) ⊆ [0, 1]}.ncard : ℝ) ≤
      2 ^ (1 - Real.log 2 / Real.log 3) * x ^ (Real.log 2 / Real.log 3) := by
  classical
  obtain ⟨hα0, hα1⟩ := alpha_mem
  set α := Real.log 2 / Real.log 3
  rw [set_eq_filter (by linarith), Set.ncard_coe_finset]
  set N := ⌊x⌋₊
  have hex : ∃ j, N < 2 * 3 ^ j := ⟨N, by
    have : N < 3 ^ N := Nat.lt_pow_self (by norm_num)
    omega⟩
  set j := Nat.find hex with hj
  have hcount := card_filter_range_le_of_le (Nat.find_spec hex)
  rw [← hj] at hcount
  rcases hjc : j with _ | i
  · rw [hjc] at hcount
    have h1 : (1 : ℝ) ≤ 2 ^ (1 - α) := Real.one_le_rpow (by norm_num) (by linarith)
    have h2 : (1 : ℝ) ≤ x ^ α := Real.one_le_rpow hx hα0
    calc ((Finset.filter _ _).card : ℝ) ≤ ((2 ^ 0 : ℕ) : ℝ) := by exact_mod_cast hcount
      _ = 1 := by norm_num
      _ ≤ 2 ^ (1 - α) * x ^ α := one_le_mul_of_one_le_of_one_le h1 h2
  · rw [hjc] at hcount
    have hmin : ¬ N < 2 * 3 ^ i := Nat.find_min hex (by omega)
    have hNx : (N : ℝ) ≤ x := Nat.floor_le (by linarith)
    have hle : ((2 * 3 ^ i : ℕ) : ℝ) ≤ x := le_trans (by exact_mod_cast (not_lt.mp hmin)) hNx
    have hxα : ((2 * 3 ^ i : ℕ) : ℝ) ^ α ≤ x ^ α :=
      Real.rpow_le_rpow (by positivity) hle hα0
    have hlow : ((2 * 3 ^ i : ℕ) : ℝ) ^ α = 2 ^ α * 2 ^ i := by
      push_cast
      rw [Real.mul_rpow (by norm_num) (by positivity), ← Real.rpow_natCast_mul (by norm_num),
        mul_comm (i : ℝ) α, Real.rpow_mul_natCast (by norm_num), three_rpow_alpha]
    have hsplit : (2 : ℝ) ^ (1 - α) * 2 ^ α = 2 := by
      rw [← Real.rpow_add (by norm_num), sub_add_cancel, Real.rpow_one]
    calc ((Finset.filter _ _).card : ℝ) ≤ ((2 ^ (i + 1) : ℕ) : ℝ) := by exact_mod_cast hcount
      _ = 2 ^ (1 - α) * (2 ^ α * 2 ^ i) := by
        push_cast
        rw [← mul_assoc, hsplit, pow_succ, mul_comm]
      _ ≤ 2 ^ (1 - α) * x ^ α := by
        rw [← hlow]
        exact mul_le_mul_of_nonneg_left hxα (by positivity)

/-- **Narkiewicz (1980)**, asymptotic form: the number of `n ≤ x` such that `2 ^ n` has only the
ternary digits `0` and `1` is `O(x ^ (log 2 / log 3))` as `x → ∞`. -/
theorem erdos_406_isBigO :
    (fun x : ℝ => ({n : ℕ | (n : ℝ) ≤ x ∧ Nat.digits 3 (2 ^ n) ⊆ [0, 1]}.ncard : ℝ))
      =O[Filter.atTop] (fun x : ℝ => x ^ (Real.log 2 / Real.log 3)) := by
  refine Asymptotics.IsBigO.of_bound (2 ^ (1 - Real.log 2 / Real.log 3)) ?_
  filter_upwards [Filter.eventually_ge_atTop 1] with x hx
  rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity)]
  exact erdos_406_narkiewicz x hx

/-! ### Sanity checks: the counted set is not trivial -/

/-- `2 ^ 0 = 1`, `2 ^ 2 = 11₃` and `2 ^ 8 = 100111₃` have only the ternary digits `0` and `1`. -/
example : Nat.digits 3 (2 ^ 0) ⊆ [0, 1] ∧ Nat.digits 3 (2 ^ 2) ⊆ [0, 1] ∧
    Nat.digits 3 (2 ^ 8) ⊆ [0, 1] := by
  norm_num

/-- `2 ^ 1 = 2₃` does not qualify. -/
example : ¬ Nat.digits 3 (2 ^ 1) ⊆ [0, 1] := by
  norm_num

end Erdos406
