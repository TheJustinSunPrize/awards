import Mathlib
open Nat Finset
def lcmUpTo : ℕ → ℕ
  | 0 => 1
  | n + 1 => Nat.lcm (lcmUpTo n) (n + 1)
theorem lcmUpTo_succ (n : ℕ) : lcmUpTo (n + 1) = Nat.lcm (lcmUpTo n) (n + 1) := rfl
theorem lcmUpTo_mono (n : ℕ) : lcmUpTo n ∣ lcmUpTo (n + 1) := by
  rw [lcmUpTo_succ]; exact Nat.dvd_lcm_left _ _
theorem dvd_lcmUpTo : ∀ (n k : ℕ), 1 ≤ k → k ≤ n → k ∣ lcmUpTo n := by
  intro n
  induction n with
  | zero => intro k hk1 hk2; omega
  | succ m ih =>
    intro k hk1 hk2
    rcases Nat.lt_or_ge k m with h | h
    · exact Nat.dvd_trans (ih k hk1 (Nat.le_of_lt h)) (lcmUpTo_mono m)
    · have hkm : k = m ∨ k = m + 1 := by omega
      rcases hkm with h2 | h2
      · have h3 : m ∣ lcmUpTo m := ih m (by omega) (Nat.le_refl m)
        have h4 : m ∣ lcmUpTo (m + 1) := Nat.dvd_trans h3 (lcmUpTo_mono m)
        exact h2 ▸ h4
      · have h6 : (m + 1 : ℕ) ∣ Nat.lcm (lcmUpTo m) (m + 1) := Nat.dvd_lcm_right _ _
        exact by rw [h2, lcmUpTo_succ]; exact h6
/-- m = Σ_{k=1}^n eps k * (L/k) -/
def signedNum (L : ℕ) (n : ℕ) (eps : ℕ → ℤ) : ℤ :=
  ∑ k ∈ Finset.range n, eps (k + 1) * ((lcmUpTo n / (k + 1) : ℕ) : ℤ)
theorem div_half_lt {n p : ℕ} (h : n / 2 < p) : n < p * 2 := by
  have hdm : 2 * (n / 2) + n % 2 = n := Nat.div_add_mod n 2
  have hmod : n % 2 < 2 := Nat.mod_lt n (by norm_num)
  have h1 : n < 2 * (n / 2) + 2 := by omega
  have h2 : 2 * (n / 2) + 2 ≤ p * 2 := by
    have h4 : n / 2 < p := h
    omega
  omega
theorem notDvdWindow {n p k : ℕ} (hp : p.Prime) (hpn : n / 2 < p) (hpn' : p ≤ n)
    (hk1 : 1 ≤ k) (hkn : k ≤ n) (hkp : k ≠ p) : ¬ p ∣ k := by
  rintro ⟨j, hj⟩
  have hk0 : k = p * j := by omega
  have hjpos : 1 ≤ j := by
    have hkpos : 0 < k := hk1
    by_contra hc
    have hj0 : j = 0 := by omega
    rw [hj0] at hk0
    omega
  rcases Nat.lt_or_ge j 2 with h1 | h1
  · have hj1 : j = 1 := by omega
    rw [hj1] at hk0
    omega
  · have h2j : 2 ≤ j := h1
    have hbound : p * 2 ≤ p * j := by
      calc p * 2 = 2 * p := by ring
        _ ≤ j * p := Nat.mul_le_mul_right p h2j
        _ = p * j := by ring
    have hgt : n < p * 2 := div_half_lt hpn
    have hle : p * j ≤ n := by omega
    omega
theorem div_dvd_of {L k p : ℕ} (hp : p.Prime) (hL : p ∣ L) (hk : ¬ p ∣ k) (hd : k ∣ L)
    (hkz : k ≠ 0) : p ∣ L / k := by
  have hEq : L / k * k = L := Nat.div_mul_cancel hd
  have h1 : p ∣ L / k * k := by rw [hEq]; exact hL
  rcases hp.dvd_mul.mp h1 with h2 | h2
  · exact h2
  · exact absurd h2 hk
theorem half_lt_of_lt_mul {m p : ℕ} (h : m + 1 < p * 2) : m / 2 < p := by
  have hdm : 2 * (m / 2) + m % 2 = m := Nat.div_add_mod m 2
  have hmod : m % 2 < 2 := Nat.mod_lt m (by norm_num)
  have h1 : 2 * (m / 2) + 2 ≤ m + 1 + 1 := by omega
  have h2 : m + 1 + 1 ≤ p * 2 := by omega
  omega
theorem sq_iff {L p : ℕ} (hp : p.Prime) (hL : p ∣ L) : p ∣ L / p ↔ p ^ 2 ∣ L := by
  constructor
  · rintro ⟨j, hj⟩
    refine ⟨j, ?_⟩
    have hEq : L = L / p * p := (Nat.div_mul_cancel hL).symm
    calc L = L / p * p := hEq
      _ = (p * j) * p := by rw [hj]
      _ = p ^ 2 * j := by ring
  · rintro ⟨j, hj⟩
    refine ⟨j, ?_⟩
    have hEq : L / p * p = L := Nat.div_mul_cancel hL
    have h2 : L / p * p = p * j * p := by rw [hEq, hj]; ring
    have hpz : 0 < p := hp.pos
    exact (Nat.eq_of_mul_eq_mul_right hpz h2)
theorem sq_not_dvd_small (m p : ℕ) (hp : p.Prime) (h : m + 1 < p * 2) :
    ¬ (p^2 ∣ m + 1) := by
  intro h2
  have hle : p^2 ≤ m + 1 := Nat.le_of_dvd (by positivity) h2
  have hp2 : 2 ≤ p := hp.two_le
  have hpp2 : p * 2 ≤ p^2 := by
    calc p * 2 ≤ p * p := Nat.mul_le_mul_left p hp2
      _ = p^2 := by ring
  omega
theorem lcmUpTo_pos (n : ℕ) : 0 < lcmUpTo n := by
  induction n with
  | zero => norm_num [lcmUpTo]
  | succ m ih =>
    have h1 : (0 : ℕ) < Nat.lcm (lcmUpTo m) (m + 1) := Nat.lcm_pos (by omega) (by omega)
    rw [lcmUpTo_succ]
    exact h1
theorem split_sq (a b p : ℕ) (hp : p.Prime) (ha : 0 < a) (hb : 0 < b)
    (h : p^2 ∣ Nat.lcm a b) : p^2 ∣ a ∨ p^2 ∣ b := by
  have key : (a.lcm b).factorization = a.factorization ⊔ b.factorization :=
    Nat.factorization_lcm ha.ne' hb.ne'
  have hdvd : p^2 ∣ a.lcm b := h
  have hpow : 2 ≤ (a.lcm b).factorization p :=
    (hp.pow_dvd_iff_le_factorization (n := a.lcm b)
      (Nat.lcm_ne_zero ha.ne' hb.ne')).mp hdvd
  rw [key] at hpow
  have hsup : (a.factorization ⊔ b.factorization) p = max (a.factorization p) (b.factorization p) :=
    rfl
  rw [hsup] at hpow
  rcases le_total (a.factorization p) (b.factorization p) with hle | hle
  · right
    have h3 : 2 ≤ b.factorization p := by omega
    exact (hp.pow_dvd_iff_le_factorization (n := b) hb.ne').mpr h3
  · left
    have h3 : 2 ≤ a.factorization p := by omega
    exact (hp.pow_dvd_iff_le_factorization (n := a) ha.ne').mpr h3
theorem padic_sq_not_dvd : ∀ (n p : ℕ), p.Prime → n / 2 < p → ¬ (p^2 ∣ lcmUpTo n) := by
  intro n
  induction n with
  | zero =>
    intro p hp _
    intro h
    have h1 : p^2 ≤ 1 := Nat.le_of_dvd (by positivity) h
    have h2 : 2 ≤ p := hp.two_le
    have h3 : 4 ≤ p^2 := by
      calc 4 = 2^2 := by norm_num
        _ ≤ p^2 := Nat.pow_le_pow_left h2 2
    omega
  | succ m ih =>
    intro p hp hpn
    rw [lcmUpTo_succ]
    intro h
    have hposL : 0 < lcmUpTo m := lcmUpTo_pos m
    have hposm : 0 < m + 1 := Nat.succ_pos m
    rcases split_sq (lcmUpTo m) (m+1) p hp hposL hposm h with h1 | h1
    · exact ih p hp (half_lt_of_lt_mul (div_half_lt hpn)) h1
    · exact sq_not_dvd_small m p hp (div_half_lt hpn) h1
/-- **c_p ≠ 0**: p ∤ L/p -/
theorem cp_neq_zero (n p : ℕ) (hp : p.Prime) (hpn : n / 2 < p) (hpn' : p ≤ n) :
    (lcmUpTo n / p) % p ≠ 0 := by
  have hdvd : p ∣ lcmUpTo n := dvd_lcmUpTo n p (by omega) hpn'
  have key : p ∣ lcmUpTo n / p ↔ p ^ 2 ∣ lcmUpTo n := sq_iff hp hdvd
  intro h
  have h1 : p ∣ lcmUpTo n / p := by
    have hkey : (lcmUpTo n / p) % p = 0 := h
    have hd : p ∣ lcmUpTo n / p ↔ (lcmUpTo n / p) % p = 0 := Nat.dvd_iff_mod_eq_zero
    exact hd.mpr hkey
  have h2 : p ^ 2 ∣ lcmUpTo n := key.mp h1
  exact padic_sq_not_dvd n p hp hpn h2
/-- **Lemma 1 主体**: m ≡ ε_p · (L/p) (mod p) -/
theorem padic_obstruction_core (n p : ℕ) (hp : p.Prime) (hpn : n / 2 < p) (hpn' : p ≤ n)
    (eps : ℕ → ℤ) :
    signedNum (lcmUpTo n) n eps
      ≡ eps p * (((lcmUpTo n / p : ℕ) : ℤ) % (p : ℤ)) [ZMOD (p : ℤ)] := by
  -- 各项: k ≠ p ⟹ p ∣ L/k ⟹ (L/k : ℤ) % p = 0
  have hp1 : 1 ≤ p := hp.pos
  have hzero : ∀ k ∈ Finset.range n, k + 1 ≠ p →
      ((lcmUpTo n / (k + 1) : ℕ) : ℤ) % (p : ℤ) = 0 := by
    intro k hk hne
    have hklt : k < n := Finset.mem_range.mp hk
    have hk1 : 1 ≤ k + 1 := by omega
    have hkn : k + 1 ≤ n := by omega
    have hkp : k + 1 ≠ p := hne
    have hdvd : (k + 1) ∣ lcmUpTo n := dvd_lcmUpTo n (k+1) hk1 hkn
    have hnotk : ¬ p ∣ (k + 1) := notDvdWindow hp hpn hpn' hk1 hkn hkp
    have hLdvd : p ∣ lcmUpTo n := dvd_lcmUpTo n p hp1 hpn'
    have hkz : k + 1 ≠ 0 := by omega
    have h1 : p ∣ lcmUpTo n / (k + 1) := div_dvd_of hp hLdvd hnotk hdvd hkz
    have h2 : ((lcmUpTo n / (k + 1) : ℕ) : ℤ) % (p : ℤ) = 0 := by
      have hstep := congrArg (fun m => ((m : ℕ) : ℤ) % (p : ℤ))
        (Nat.dvd_iff_mod_eq_zero.mp h1)
      simpa using hstep
    exact h2
  -- 主求和改写
  unfold signedNum
  -- 每项 ≡ eps_k * ((L/k) % p) [ZMOD p]: 因为 ↑x ≡ ↑x % ↑p
  have hterm : ∀ k ∈ Finset.range n,
      eps (k + 1) * (((lcmUpTo n / (k + 1) : ℕ) : ℤ))
        ≡ eps (k + 1) * (((lcmUpTo n / (k + 1) : ℕ) : ℤ) % (p : ℤ)) [ZMOD (p : ℤ)] := by
    intro k hk
    rw [Int.modEq_iff_dvd]
    -- 目标: (p:ℤ) ∣ eps_k * x - eps_k * (x % p) = eps_k * (x - x%p)
    have h1 : ((lcmUpTo n / (k + 1) : ℕ) : ℤ) - ((lcmUpTo n / (k + 1) : ℕ) : ℤ) % (p : ℤ)
        = (p : ℤ) * (((lcmUpTo n / (k + 1) : ℕ) : ℤ) / (p : ℤ)) := by
      have hbase := Int.mul_ediv_add_emod ((lcmUpTo n / (k + 1) : ℕ) : ℤ) (p : ℤ)
      linarith [hbase]
    refine ⟨-((eps (k + 1) : ℤ) * (((lcmUpTo n / (k + 1) : ℕ) : ℤ) / (p : ℤ))), ?_⟩
    have hre : (eps (k + 1) : ℤ) * (((lcmUpTo n / (k + 1) : ℕ) : ℤ) % (p : ℤ))
        - (eps (k + 1) : ℤ) * ((lcmUpTo n / (k + 1) : ℕ) : ℤ)
        = -((eps (k + 1) : ℤ) * (((lcmUpTo n / (k + 1) : ℕ) : ℤ)
          - ((lcmUpTo n / (k + 1) : ℕ) : ℤ) % (p : ℤ))) := by ring
    rw [hre, h1]
    ring
  -- 现在 sum ≡ Σ eps_k * ((L/k) % p)
  have hsum : ∑ k ∈ Finset.range n, eps (k + 1) * (((lcmUpTo n / (k + 1) : ℕ) : ℤ))
      ≡ ∑ k ∈ Finset.range n, eps (k + 1) * (((lcmUpTo n / (k + 1) : ℕ) : ℤ) % (p : ℤ))
        [ZMOD (p : ℤ)] := Int.ModEq.sum hterm
  -- 右边只剩 k = p 项
  have hsingle : ∑ k ∈ Finset.range n, eps (k + 1) * (((lcmUpTo n / (k + 1) : ℕ) : ℤ) % (p : ℤ))
      = eps p * (((lcmUpTo n / p : ℕ) : ℤ) % (p : ℤ)) := by
    rw [Finset.sum_eq_single_of_mem (a := p - 1) (Finset.mem_range.mpr (by omega))
      (fun b hb hne => by
        have hb1 : b + 1 ≠ p := by omega
        rw [hzero b hb hb1]
        ring)]
    have hpid : p - 1 + 1 = p := by omega
    rw [hpid]
  rw [hsingle] at hsum
  exact hsum
theorem proj_zero (n p : ℕ) (hp : p.Prime) (hpn : n / 2 < p) (hpn' : p ≤ n)
    (e : ℕ → ℤ) (hp3 : 3 ≤ p)
    (hmod : (signedNum (lcmUpTo n) n e) % (p : ℤ) = 0) :
    (p : ℤ) ∣ e p := by
  have hcore := padic_obstruction_core n p hp hpn hpn' e
  -- 1) p ∣ e_p · c_p (ℤ)
  have hmul : (p:ℤ) ∣ (e p : ℤ) * (((lcmUpTo n / p : ℕ) : ℤ) % (p : ℤ)) := by
    obtain ⟨s, hs⟩ := Int.dvd_iff_emod_eq_zero.mpr hmod
    obtain ⟨t, ht⟩ := Int.modEq_iff_dvd.mp hcore
    refine ⟨s + t, ?_⟩
    have heq : (e p : ℤ) * (((lcmUpTo n / p : ℕ) : ℤ) % (p : ℤ))
        = signedNum (lcmUpTo n) n e + (p:ℤ) * t := by linarith
    rw [heq, hs]
    ring
  -- 2) c_p (ℤ) 不被 p 整除
  have hcp : ¬ ((p:ℤ) ∣ (((lcmUpTo n / p : ℕ) : ℤ) % (p : ℤ))) := by
    intro hc
    -- ↑(L/p) % ↑p = ↑((L/p) % p) (natCast_mod), 所以 hc 即 (p:ℕ) ∣ (L/p) % p
    have hcast : ((lcmUpTo n / p : ℕ) : ℤ) % (p : ℤ)
        = (((lcmUpTo n / p) % p : ℕ) : ℤ) := by
      rw [Int.natCast_mod]
    have hdvd_nat : p ∣ (lcmUpTo n / p) % p := by
      rw [hcast] at hc
      exact Int.natCast_dvd.mp hc
    have hzero : (lcmUpTo n / p) % p % p = 0 := Nat.dvd_iff_mod_eq_zero.mp hdvd_nat
    have hsimp : (lcmUpTo n / p) % p % p = (lcmUpTo n / p) % p :=
      Nat.mod_mod_of_dvd _ (dvd_refl p)
    rw [hsimp] at hzero
    exact cp_neq_zero n p hp hpn hpn' hzero
  -- 3) 素性消去 (ℤ): p ∣ e_p·c_p, ¬p ∣ c_p ⟹ p ∣ e_p
  have h1 : p ∣ ((e p : ℤ) * (((lcmUpTo n / p : ℕ) : ℤ) % (p : ℤ))).natAbs :=
    Int.natCast_dvd.mp hmul
  rw [Int.natAbs_mul] at h1
  have h2 : ¬ p ∣ (((lcmUpTo n / p : ℕ) : ℤ) % (p : ℤ)).natAbs := by
    intro h2
    exact hcp (Int.natCast_dvd.mpr h2)
  rcases hp.dvd_mul.mp h1 with h3 | h3
  · exact Int.natCast_dvd.mpr h3
  · exact absurd h3 h2
/-- signedNum 的线性性: m(e₁) - m(e₂) = m(e₁ - e₂) -/
theorem signedNum_sub (L n : ℕ) (e₁ e₂ : ℕ → ℤ) :
    signedNum L n e₁ - signedNum L n e₂ = signedNum L n (fun k => e₁ k - e₂ k) := by
  unfold signedNum
  congr 1
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl (fun k _ => by ring)
/-- **单射性核心**: 若 m(e₁) ≡ m(e₂) (mod p) 对窗口素数 p, 且 |e₁p - e₂p| ≤ 1, p ≥ 3,
则 e₁ p = e₂ p -/
theorem proj_inj (n p : ℕ) (hp : p.Prime) (hpn : n / 2 < p) (hpn' : p ≤ n)
    (hp3 : 3 ≤ p) (e₁ e₂ : ℕ → ℤ)
    (hmod : (signedNum (lcmUpTo n) n e₁ - signedNum (lcmUpTo n) n e₂) % (p : ℤ) = 0)
    (hdiff : (e₁ p - e₂ p).natAbs ≤ 1) :
    e₁ p = e₂ p := by
  -- δ := e₁ - e₂; m(δ) = m(e₁) - m(e₂) ≡ 0 (mod p)
  set δ : ℕ → ℤ := fun k => e₁ k - e₂ k with hδ
  have hlin := signedNum_sub (lcmUpTo n) n e₁ e₂
  -- hlin: m(e₁) - m(e₂) = m(fun k => e₁k - e₂k) = m(δ) (δ 定义展开)
  have hmodδ : (signedNum (lcmUpTo n) n δ) % (p : ℤ) = 0 := by
    rw [hδ]
    rw [← hlin]  -- m(fun...) 变成 m(e₁) - m(e₂)
    exact hmod
  -- proj_zero: p ∣ δ_p
  have hdvd := proj_zero n p hp hpn hpn' δ hp3 hmodδ
  -- p ∣ δ_p (ℤ), |δ_p| ≤ 1, p ≥ 3 ⟹ δ_p = 0
  obtain ⟨q, hq⟩ := hdvd
  have hdp : δ p = (p:ℤ) * q := hq
  have hq0 : q = 0 := by
    by_contra hne
    have habs : ((p:ℤ) * q).natAbs ≤ 1 := hdp ▸ hdiff
    have h1 : ((p:ℤ) * q).natAbs = p * q.natAbs := by
      rw [Int.natAbs_mul, Int.natAbs_natCast]
    have h2 : 1 ≤ q.natAbs := by omega
    -- p ≥ 2, |q| ≥ 1 ⟹ p * |q| ≥ 2 > 1
    have hp2 : 2 ≤ p := hp.two_le
    have hle : p * 1 ≤ p * q.natAbs := Nat.mul_le_mul_left p h2
    omega
  rw [hq0] at hq
  simp at hq
  -- δ p = 0
  rw [hδ] at hq
  linarith


-- ========== CRT 下界 ==========

def windowPrimes (n : ℕ) : Finset ℕ := Finset.filter Nat.Prime (Finset.Ioc (n / 2) n)

def windowSize (n : ℕ) : ℕ := (windowPrimes n).card

theorem mem_windowPrimes {n p : ℕ} : p ∈ windowPrimes n ↔ n / 2 < p ∧ p ≤ n ∧ Nat.Prime p := by
  simp [windowPrimes, Finset.mem_filter, Finset.mem_Ioc, and_assoc]

theorem window_prime_ge_three {n : ℕ} (hn : 4 ≤ n) {p : ℕ} (hp : p ∈ windowPrimes n) : 3 ≤ p := by
  obtain ⟨h1, h2, h3⟩ := mem_windowPrimes.mp hp
  by_cases heq : p = 2; subst heq; omega; omega

theorem window_prime_prime {n p : ℕ} (hp : p ∈ windowPrimes n) : Nat.Prime p :=
  (mem_windowPrimes.mp hp).2.2

theorem window_prime_hpn {n p : ℕ} (hp : p ∈ windowPrimes n) : n / 2 < p :=
  (mem_windowPrimes.mp hp).1

theorem window_prime_hle {n p : ℕ} (hp : p ∈ windowPrimes n) : p ≤ n :=
  (mem_windowPrimes.mp hp).2.1

theorem window_prime_dvd {n p : ℕ} (hp : p ∈ windowPrimes n) : p ∣ lcmUpTo n :=
  dvd_lcmUpTo n p (window_prime_prime hp).pos (window_prime_hle hp)

theorem window_primes_coprime {n p q : ℕ} (hp : p ∈ windowPrimes n) (hq : q ∈ windowPrimes n)
    (hne : p ≠ q) : Nat.Coprime p q := by
  have hpp := window_prime_prime hp; have hqp := window_prime_prime hq
  rw [hpp.coprime_iff_not_dvd]; intro hdvd
  have : p = q := (prime_dvd_prime_iff_eq hpp hqp).mp hdvd
  exact hne this

/-- ∏ p∈W p ∣ lcmUpTo n -/
theorem prod_window_dvd_lcm {n : ℕ} (hn : 4 ≤ n) :
    ∏ p ∈ windowPrimes n, p ∣ lcmUpTo n := by
  -- 用 Nat 层面的归纳: 对 windowPrimes n 的 list 排序后归纳
  -- 或者直接用 Finset.induction_on 不需要 subset 传递
  have key : ∀ (s : Finset ℕ) (hsub : s ⊆ windowPrimes n), ∏ p ∈ s, p ∣ lcmUpTo n := by
    intro s hs
    induction s using Finset.induction_on with
    | empty => simp
    | insert a r har ih =>
      rw [Finset.prod_insert har]
      have ha : a ∣ lcmUpTo n := window_prime_dvd (hs (Finset.mem_insert_self a r))
      have hr : ∏ p ∈ r, p ∣ lcmUpTo n := ih (Finset.Subset.trans (Finset.subset_insert a r) hs)
      have hcop_a : Nat.Coprime a (∏ p ∈ r, p) := by
        apply Nat.Coprime.prod_right; intro p hp
        exact window_primes_coprime (hs (Finset.mem_insert_self a r))
          (hs (Finset.mem_insert_of_mem hp)) (fun heq => har (heq ▸ hp))
      exact Nat.Coprime.mul_dvd_of_dvd_of_dvd hcop_a ha hr
  exact key (windowPrimes n) (Finset.Subset.refl _)

/-- 3^|W| ≤ ∏ p∈W p -/
theorem three_pow_le_prod_window {n : ℕ} (hn : 4 ≤ n) :
    3 ^ (windowPrimes n).card ≤ ∏ p ∈ windowPrimes n, p := by
  have key : ∀ (s : Finset ℕ) (hsub : s ⊆ windowPrimes n), 3 ^ s.card ≤ ∏ p ∈ s, p := by
    intro s hs
    induction s using Finset.induction_on with
    | empty => simp
    | insert a r har ih =>
      have ha3 : (3 : ℕ) ≤ a := window_prime_ge_three hn (hs (Finset.mem_insert_self a r))
      have hIH := ih (Finset.Subset.trans (Finset.subset_insert a r) hs)
      rw [Finset.card_insert_of_notMem har, Finset.prod_insert har]
      calc 3 ^ (r.card + 1) = 3 * 3 ^ r.card := by ring
        _ ≤ 3 * ∏ p ∈ r, p := Nat.mul_le_mul_left 3 hIH
        _ ≤ a * ∏ p ∈ r, p := Nat.mul_le_mul_right (∏ p ∈ r, p) ha3
  exact key (windowPrimes n) (Finset.Subset.refl _)

/-- **CRT 下界主定理**: 3 ^ windowSize n ≤ lcmUpTo n

对 n ≥ 4, 设 W = {p ∈ (n/2, n] : p 素数}, 则 3^|W| ≤ lcm(1,...,n).

证明:
1. 每个 p ∈ W 满足 p ≥ 3 ⟹ 3^|W| ≤ ∏_{p∈W} p
2. 每个 p ∈ W 整除 lcm(1,...,n), 且互素 ⟹ ∏_{p∈W} p ∣ lcm(1,...,n)
3. 综合得 3^|W| ≤ lcm(1,...,n)
-/
theorem crt_lower_bound (n : ℕ) (hn : 4 ≤ n) :
    3 ^ windowSize n ≤ lcmUpTo n := by
  unfold windowSize
  exact Nat.le_trans (three_pow_le_prod_window hn)
    (Nat.le_of_dvd (lcmUpTo_pos n) (prod_window_dvd_lcm hn))
