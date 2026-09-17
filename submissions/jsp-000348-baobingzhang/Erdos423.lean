import Mathlib

/-!
# Erdős Problem 423: the Hofstadter consecutive-sum sequence

Let `a₁ = 1`, `a₂ = 2`, and for `k ≥ 3` let `a_k` be the least integer `> a_{k-1}` which is a sum
of at least two consecutive earlier terms (OEIS A005243: `1, 2, 3, 5, 6, 8, 10, 11, 14, …`).
Hofstadter (see Erdős [Er77c, p. 71], Erdős–Graham [ErGr80, p. 83]) asked for the asymptotic
behaviour of `a_n`; it is conjectured that `a_n = n + o(n)`, which remains open. Bolan [Bolan]
and Tang [Ta26] independently proved that the sequence omits infinitely many positive integers,
and Tang proved `a_n - n` is nondecreasing and unbounded, and in fact `a_n = n + Ω(log log n)`.

## Statements proved

The definitions `IsConsecutiveBlockSum`, `IsHofstadterSeq` and the statements of the following
theorems (category "research solved", resp. "test", there) are copied verbatim from Google
DeepMind's formal-conjectures project (`FormalConjectures/ErdosProblems/423.lean`, Apache-2.0),
with the same names in the namespace `Erdos423`:

* `erdos_423.variants.nondecreasing`: `a_n - n` is nondecreasing;
* `erdos_423.variants.unbounded`: for every `M`, eventually `M + n ≤ a n`;
* `erdos_423.variants.infinite_complement`: `(Set.range a)ᶜ` is infinite;
* `erdos_423.variants.lower_bound`: `log log n = O(a_n - n)`, i.e. `a_n = n + Ω(log log n)`;
* `erdos_423.test.unbounded_iff_infinite_complement` (immediate once both sides are proved).

In addition, `exists_isHofstadterSeq` shows that a sequence with `IsHofstadterSeq a` exists (so
the statements are not vacuous), and `Hofstadter.eq_of_isHofstadterSeq` shows that
`IsHofstadterSeq` determines `a n` for every `n ≥ 1`, so it pins down A005243 exactly (the value
`a 0` is unconstrained; it adds at most one element to `Set.range a`).

## Proof

Write `b_n = a_n - n`.

* **Monotonicity** (`Hofstadter.add_sub_le`). `a_{n+1} > a_n`, so `b_{n+1} ≥ b_n`.
* **Shape of representations in a plateau** (`Hofstadter.plateau_rep`, Tang's Lemma 4.2). Suppose
  `b_l = B` for `n1 ≤ l ≤ n2` and put `T = B + n1 = a_{n1}`. Let `2^r = a_i` with
  `n1 ≤ i ≤ n2` and `2^r > T²`, and write `2^r = a_p + ⋯ + a_q` with `p < q < i`. If `p ≥ n1`
  this is a sum of at least two consecutive positive integers, impossible for a power of two
  (`Hofstadter.not_two_pow_consec`). Since `a_1 + ⋯ + a_{n1-1} ≤ T²`, we get `p < n1 ≤ q`, and
  with `C = a_p + ⋯ + a_{n1-1} ≤ T²` and `x = 2(B + q) + 1` (odd):
  `x² + 8C + 4T = 8·2^r + 4T² + 1`.
* **Short plateaus** (`Hofstadter.sq_contra`, `Hofstadter.plateau_bound`). If the plateau
  reached `512 T⁴`, it would contain `2^r` and `2^(r+2)` with `64 T⁴ < 2^r ≤ 128 T⁴`. Their
  relations give `4x² + 32C + 12T = y² + 8C' + 12T² + 3` with `y` odd, so `y ≠ 2x` and
  `|y² - 4x²| ≥ 2x`; hence `x ≤ 16T²` and `8·2^r ≤ x² + 8C + 4T ≤ 268 T⁴`, a contradiction.
  So `B + n2 < 512 (B + n1)⁴` whenever `b_{n1} = b_{n2} = B`.
* **Iteration** (`Hofstadter.lt_of_le_add`). By induction on `B`, `b_n ≤ B` implies
  `n < 2^(2^(3B+4))`: the plateau of value `B + 1` starts at an index `n1` with
  `n1 - 1 < 2^(2^(3B+4))`, and `512 (B + 1 + n1)⁴ ≤ 2^(2^(3B+7))`.
* **Conclusions.** This gives `b_n → ∞` (`unbounded`) and `log log n < 3 b_n + 4 ≤ 7 b_n` for large
  `n` (`lower_bound`). Finally, if only finitely many integers were omitted, all integers in
  `[X, a_n]` would be among `a_1, …, a_n`, forcing `b_n < X` (`infinite_complement`).

The overall structure (monotonicity, plateaus, the representation of powers of two in a plateau)
follows Tang [Ta26, §3–4]. Tang closes the argument with the Schinzel–Tijdeman theorem
(qualitative part) and Beukers' bound for `x² + D = 2^m` (quantitative part), and Bolan [Bolan]
uses a pigeonhole argument on pairs of powers of two with the same `C`. Neither deep result is
available in Mathlib; the comparison of `2^r` with `2^(r+2)` above is an elementary replacement
chosen for this formalization (it gives the recursion `M(B) ≪ M(B-1)⁴` in place of Tang's
`M(B) ≪ M(B-1)^20`).

## What remains open

The main question (`a_n = n + o(n)`?) is open. Tang's polynomial upper bound
`a_n ≪ n^(4175/2506 + o(1))` and its improvement `a_n ≪ n^(688/413 + o(1))` via Cushman's bound
(`erdos_423.variants.upper_bound` in formal-conjectures) are not proved in this file.

## References

* [Er77c] Erdős, P., _Problems and results on combinatorial number theory. III_, Number theory day
  (Proc. Conf., Rockefeller Univ., New York, 1976), 1977, pp. 43–72.
* [ErGr80] Erdős, P. and Graham, R., _Old and new problems and results in combinatorial number
  theory_, Monographies de L'Enseignement Mathématique (1980).
* [Ta26] Tang, Q., _The Hofstadter consecutive-sum sequence omits infinitely many positive
  integers_, arXiv:2603.09939 (2026).
* [Bolan] Bolan, M., _Hofstader–Ulam Sequence_ (January 2026),
  https://github.com/mjtb49/HofstaderUlam/blob/main/HofstaderUlamSequence.pdf
* [erdosproblems.com/423](https://www.erdosproblems.com/423)
* [OEIS A005243](https://oeis.org/A005243)
-/

open Finset BigOperators Filter Asymptotics

namespace Erdos423

/-! ### Definitions

Copied verbatim from formal-conjectures, `FormalConjectures/ErdosProblems/423.lean`. -/

/-- `IsConsecutiveBlockSum a k m` means that $m$ equals the sum of at least two
    consecutive terms of the sequence $a$, using indices from $\{1, \ldots, k - 1\}$.
    That is, there exist $i, j$ with $1 \le i$, $i + 1 \le j$, $j \le k - 1$ such that
    $m = a(i) + a(i+1) + \cdots + a(j)$. -/
def IsConsecutiveBlockSum (a : ℕ → ℕ) (k : ℕ) (m : ℕ) : Prop :=
  ∃ i j : ℕ, 1 ≤ i ∧ i + 1 ≤ j ∧ j + 1 ≤ k ∧
    m = ∑ l ∈ Finset.Icc i j, a l

/-- The Hofstadter sequence (OEIS A005243): $a(1) = 1$, $a(2) = 2$, and for $k \ge 3$,
$a(k)$ is the least integer $> a(k-1)$ that equals the sum of at least two consecutive terms from
$\{a(1), \ldots, a(k-1)\}$. The sequence begins $1, 2, 3, 5, 6, 8, 10, 11, \ldots$. -/
def IsHofstadterSeq (a : ℕ → ℕ) : Prop :=
  a 1 = 1 ∧ a 2 = 2 ∧
  ∀ k : ℕ, 3 ≤ k →
    IsConsecutiveBlockSum a k (a k) ∧
    a (k - 1) < a k ∧
    ∀ m : ℕ, a (k - 1) < m → m < a k → ¬IsConsecutiveBlockSum a k m

namespace Hofstadter

/-! ### Arithmetic lemmas -/

/-- An odd divisor of a power of two is `1`. -/
theorem eq_one_of_odd_of_dvd_two_pow {d k : ℕ} (hd : Odd d) (h : d ∣ 2 ^ k) : d = 1 :=
  Nat.Coprime.eq_one_of_dvd (hd.coprime_two_right.pow_right k) h

/-- Closed form of `∑_{l=x}^{y} (c + l)`, written without subtraction. -/
theorem two_mul_sum_Icc_add (c x y : ℕ) (hxy : x ≤ y) :
    2 * ∑ l ∈ Icc x y, (c + l) + (c + x) * (c + x) = (c + y) * (c + y + 1) + (c + x) := by
  induction y, hxy using Nat.le_induction with
  | base => simp; ring
  | succ y hxy ih =>
    rw [Finset.sum_Icc_succ_top (by omega)]
    nlinarith [ih]

/-- A power of two is not a sum `s + (s + 1) + ⋯ + (s + 1 + t)` of at least two consecutive
positive integers (normalized form `2·2^r + s² = v(v+1) + s` with `v = s + 1 + t`). -/
theorem not_two_pow_consec {r s t : ℕ} (hs : 1 ≤ s)
    (h : 2 * 2 ^ r + s * s = (s + 1 + t) * (s + 1 + t + 1) + s) : False := by
  have key : (t + 2) * (2 * s + t + 1) = 2 ^ (r + 1) := by
    rw [pow_succ]; nlinarith [h]
  rcases Nat.even_or_odd (t + 2) with ⟨u, hu⟩ | ho
  · have ho' : Odd (2 * s + t + 1) := ⟨s + u - 1, by omega⟩
    have := eq_one_of_odd_of_dvd_two_pow ho' (Dvd.intro_left _ key)
    omega
  · have := eq_one_of_odd_of_dvd_two_pow ho (Dvd.intro _ key)
    omega

/-! ### Elementary properties of the sequence -/

variable {a : ℕ → ℕ}

theorem lt_succ (h : IsHofstadterSeq a) {k : ℕ} (hk : 1 ≤ k) : a k < a (k + 1) := by
  obtain ⟨h1, h2, h3⟩ := h
  rcases Nat.lt_or_ge k 2 with hk2 | hk2
  · obtain rfl : k = 1 := by omega
    show a 1 < a 2
    omega
  · simpa using (h3 (k + 1) (by omega)).2.1

/-- `a_n - n` is nondecreasing, in the form `a i + (j - i) ≤ a j`. -/
theorem add_sub_le (h : IsHofstadterSeq a) {i j : ℕ} (hi : 1 ≤ i) (hij : i ≤ j) :
    a i + (j - i) ≤ a j := by
  induction j, hij using Nat.le_induction with
  | base => simp
  | succ j hij ih =>
    have := lt_succ h (le_trans hi hij)
    omega

theorem lt_of_lt (h : IsHofstadterSeq a) {i j : ℕ} (hi : 1 ≤ i) (hij : i < j) : a i < a j := by
  have := add_sub_le h hi hij.le
  omega

theorem le_self (h : IsHofstadterSeq a) {n : ℕ} (hn : 1 ≤ n) : n ≤ a n := by
  have := add_sub_le h le_rfl hn
  have h1 := h.1
  omega

/-! ### Plateaus of `a_n - n` are short -/

/-- The terms before index `n1` sum (from any starting index `p ≥ 1`) to at most `a_{n1}²`. -/
theorem sum_Ico_le (h : IsHofstadterSeq a) {p n1 : ℕ} (hp : 1 ≤ p) :
    ∑ l ∈ Ico p n1, a l ≤ a n1 * a n1 := by
  have hle : ∑ l ∈ Ico p n1, a l ≤ (Ico p n1).card • a n1 :=
    Finset.sum_le_card_nsmul _ _ _ fun l hl => by
      rw [Finset.mem_Ico] at hl
      exact (lt_of_lt h (by omega) hl.2).le
  have hcard : (Ico p n1).card ≤ a n1 := by
    rw [Nat.card_Ico]
    rcases Nat.lt_or_ge n1 1 with h0 | h0
    · omega
    · have := le_self h h0
      omega
  rw [smul_eq_mul] at hle
  exact hle.trans (Nat.mul_le_mul_right _ hcard)

/-- A power of two `a i = 2^r` inside a plateau `a l = B + l` (`n1 ≤ l ≤ n2`), larger than
`T² = (B + n1)²`, yields an odd `x` and `C ≤ T²` with `x² + 8C + 4T = 8·2^r + 4T² + 1`
(Tang's Lemma 4.2, in a subtraction-free form). -/
theorem plateau_rep (h : IsHofstadterSeq a) {n1 n2 B i r : ℕ} (hn1 : 1 ≤ n1)
    (hplat : ∀ l, n1 ≤ l → l ≤ n2 → a l = B + l) (hi1 : n1 ≤ i) (hi2 : i ≤ n2) (hi3 : 3 ≤ i)
    (hair : a i = 2 ^ r) (hS : (B + n1) * (B + n1) < 2 ^ r) :
    ∃ C x, C ≤ (B + n1) * (B + n1) ∧ Odd x ∧
      x * x + 8 * C + 4 * (B + n1) = 8 * 2 ^ r + 4 * (B + n1) * (B + n1) + 1 := by
  have han1 : a n1 = B + n1 := hplat n1 le_rfl (hi1.trans hi2)
  obtain ⟨⟨p, q, hp, hpq, hqi, hsum⟩, -, -⟩ := h.2.2 i hi3
  rw [hair] at hsum
  by_cases hpn : n1 ≤ p
  · -- all summands lie in the plateau: a sum of consecutive integers
    exfalso
    have hcongr : ∑ l ∈ Icc p q, a l = ∑ l ∈ Icc p q, (B + l) :=
      Finset.sum_congr rfl fun l hl => hplat l (by rw [Finset.mem_Icc] at hl; omega)
        (by rw [Finset.mem_Icc] at hl; omega)
    have hid := two_mul_sum_Icc_add B p q (by omega)
    rw [← hcongr, ← hsum] at hid
    obtain ⟨t, rfl⟩ : ∃ t, q = p + 1 + t := ⟨q - p - 1, by omega⟩
    exact not_two_pow_consec (r := r) (s := B + p) (t := t) (by omega) (by
      rw [show B + (p + 1 + t) = B + p + 1 + t by ring] at hid
      linarith)
  · push Not at hpn
    have hC := sum_Ico_le h (n1 := n1) hp
    rw [han1] at hC
    have hqn : n1 ≤ q := by
      by_contra hq
      push Not at hq
      have : ∑ l ∈ Icc p q, a l ≤ ∑ l ∈ Ico p n1, a l := by
        rw [← Finset.Ico_add_one_right_eq_Icc]
        exact Finset.sum_le_sum_of_subset (Finset.Ico_subset_Ico_right (by omega))
      omega
    refine ⟨∑ l ∈ Ico p n1, a l, 2 * (B + q) + 1, hC, ⟨B + q, rfl⟩, ?_⟩
    have hsplit : ∑ l ∈ Icc p q, a l = ∑ l ∈ Ico p n1, a l + ∑ l ∈ Icc n1 q, a l := by
      rw [← Finset.Ico_add_one_right_eq_Icc, ← Finset.Ico_add_one_right_eq_Icc]
      exact (Finset.sum_Ico_consecutive _ (by omega) (by omega)).symm
    have hcongr : ∑ l ∈ Icc n1 q, a l = ∑ l ∈ Icc n1 q, (B + l) :=
      Finset.sum_congr rfl fun l hl => hplat l (by rw [Finset.mem_Icc] at hl; omega)
        (by rw [Finset.mem_Icc] at hl; omega)
    have hid := two_mul_sum_Icc_add B n1 q hqn
    rw [hsplit, hcongr] at hsum
    nlinarith [hid, hsum]

/-- The elementary replacement for Beukers' bound: the relations coming from `2^r` and
`2^(r+2)` in the same plateau are incompatible once `2^r > 64 T⁴`. Indeed
`4x² + 32C + 12T = y² + 8C' + 12T² + 3`, and `y ≠ 2x` (as `y` is odd) forces
`|y² - 4x²| ≥ 2x`, whence `x ≤ 16T²` and `8·2^r ≤ x² + 8C + 4T ≤ 268 T⁴`. -/
theorem sq_contra {x y C C' T R : ℕ} (hT : 1 ≤ T) (hC : C ≤ T * T) (hC' : C' ≤ T * T)
    (hy : Odd y) (hxe : x * x + 8 * C + 4 * T = 8 * R + 4 * T * T + 1)
    (hye : y * y + 8 * C' + 4 * T = 32 * R + 4 * T * T + 1)
    (hR : 64 * (T * T) * (T * T) < R) : False := by
  have hne : y ≠ 2 * x := by
    rintro rfl
    exact (Nat.not_even_iff_odd.2 hy) (even_two_mul x)
  have hkey : 4 * x * x + 32 * C + 12 * T = y * y + 8 * C' + 12 * T * T + 3 := by
    linarith
  have hTT : T ≤ T * T := Nat.le_mul_self T
  have hxb : x ≤ 16 * (T * T) := by
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have h1 : (y + 1) * (2 * x) ≤ 2 * x * (2 * x) := Nat.mul_le_mul_right _ hlt
      have h2 : y * y ≤ y * (2 * x) := Nat.mul_le_mul_left _ hlt.le
      nlinarith
    · have h1 : (2 * x + 1) * y ≤ y * y := Nat.mul_le_mul_right _ hgt
      have h2 : 2 * x * (2 * x) ≤ 2 * x * y := Nat.mul_le_mul_left _ hgt.le
      nlinarith
  have hxx : x * x ≤ 16 * (T * T) * (16 * (T * T)) := Nat.mul_le_mul hxb hxb
  have hT1 : 1 ≤ T * T := Nat.one_le_iff_ne_zero.2 (by positivity)
  have hT4 : T * T ≤ T * T * (T * T) := Nat.le_mul_self (T * T)
  nlinarith

/-- **Plateau bound.** If `a_n - n = B` at both ends of `[n1, n2]`, then
`B + n2 < 512 (B + n1)⁴`. -/
theorem plateau_bound (h : IsHofstadterSeq a) {n1 n2 B : ℕ} (hn1 : 1 ≤ n1)
    (ha1 : a n1 = B + n1) (ha2 : a n2 = B + n2) :
    B + n2 < 512 * ((B + n1) * (B + n1) * ((B + n1) * (B + n1))) := by
  by_contra hcon
  push Not at hcon
  have hplat : ∀ l, n1 ≤ l → l ≤ n2 → a l = B + l := by
    intro l hl1 hl2
    have := add_sub_le h hn1 hl1
    have := add_sub_le h (hn1.trans hl1) hl2
    omega
  obtain ⟨T, hT⟩ : ∃ T, T = B + n1 := ⟨_, rfl⟩
  obtain ⟨W, hW⟩ : ∃ W, W = T * T := ⟨_, rfl⟩
  obtain ⟨Q, hQ⟩ : ∃ Q, Q = W * W := ⟨_, rfl⟩
  rw [← hT, ← hW, ← hQ] at hcon
  have hT1 : 1 ≤ T := by omega
  have hTW : T ≤ W := hW ▸ Nat.le_mul_self T
  have hWQ : W ≤ Q := hQ ▸ Nat.le_mul_self W
  -- choose `r` with `64 T⁴ < 2^r ≤ 128 T⁴`
  obtain ⟨r, hr1, hr2⟩ : ∃ r, 64 * Q < 2 ^ r ∧ 2 ^ r ≤ 128 * Q := by
    refine ⟨Nat.log 2 (64 * Q) + 1, Nat.lt_pow_succ_log_self (by norm_num) _, ?_⟩
    rw [pow_succ]
    have := Nat.pow_log_le_self 2 (x := 64 * Q) (by omega)
    omega
  have hpow2 : 2 ^ (r + 2) = 4 * 2 ^ r := by ring
  obtain ⟨C, x, hC, -, hx⟩ := plateau_rep (i := 2 ^ r - B) (r := r) h hn1 hplat (by omega)
    (by omega) (by omega) (by rw [hplat _ (by omega) (by omega)]; omega)
    (by rw [← hT, ← hW]; omega)
  obtain ⟨C', y, hC', hy, hy'⟩ := plateau_rep (i := 2 ^ (r + 2) - B) (r := r + 2) h hn1 hplat
    (by omega) (by omega) (by omega) (by rw [hplat _ (by omega) (by omega)]; omega)
    (by rw [← hT, ← hW]; omega)
  rw [← hT] at hC hx hC' hy'
  rw [hpow2] at hy'
  exact sq_contra hT1 hC hC' hy hx (by linarith) (by rw [← hW, mul_assoc, ← hQ]; exact hr1)

/-- **Quantitative form.** If `a n ≤ B + n` (i.e. `a_n - n ≤ B`) then `n < 2^(2^(3B+4))`. -/
theorem lt_of_le_add (h : IsHofstadterSeq a) (B : ℕ) :
    ∀ n, 1 ≤ n → a n ≤ B + n → n < 2 ^ 2 ^ (3 * B + 4) := by
  induction B with
  | zero =>
    intro n hn hle
    have := le_self h hn
    have hb := plateau_bound h (n1 := 1) (n2 := n) (B := 0) le_rfl (by simp [h.1])
      (by omega)
    norm_num at hb ⊢
    omega
  | succ B ih =>
    intro n hn hle
    obtain ⟨X, hX⟩ : ∃ X, X = 2 ^ 2 ^ (3 * B + 4) := ⟨_, rfl⟩
    by_cases hB : a n ≤ B + n
    · calc n < X := hX ▸ ih n hn hB
        _ ≤ 2 ^ 2 ^ (3 * (B + 1) + 4) := hX ▸ Nat.pow_le_pow_right (by norm_num)
            (Nat.pow_le_pow_right (by norm_num) (by omega))
    · push Not at hB
      classical
      have hex : ∃ i, 1 ≤ i ∧ B + i < a i := ⟨n, hn, hB⟩
      obtain ⟨hn1, hlt1⟩ := Nat.find_spec hex
      have hn1n : Nat.find hex ≤ n := Nat.find_min' hex ⟨hn, hB⟩
      have ha1 : a (Nat.find hex) = (B + 1) + Nat.find hex := by
        have := add_sub_le h hn1 hn1n
        omega
      have hpl := plateau_bound h (n2 := n) hn1 ha1 (by omega)
      have hXB : B + 1 ≤ X := by
        have h1 : 3 * B + 4 < 2 ^ (3 * B + 4) := Nat.lt_two_pow_self
        have h2 : 2 ^ (3 * B + 4) < 2 ^ 2 ^ (3 * B + 4) := Nat.lt_two_pow_self
        omega
      have hn1X : Nat.find hex ≤ X := by
        rcases Nat.lt_or_ge (Nat.find hex) 2 with h2 | h2
        · omega
        · have hmin := Nat.find_min hex (show Nat.find hex - 1 < Nat.find hex by omega)
          push Not at hmin
          have := ih (Nat.find hex - 1) (by omega) (hmin (by omega))
          omega
      obtain ⟨Y, hY⟩ : ∃ Y, Y = B + 1 + Nat.find hex := ⟨_, rfl⟩
      rw [← hY] at hpl
      have hY2 : Y ≤ 2 * X := by omega
      have hY4 : Y * Y * (Y * Y) ≤ 2 * X * (2 * X) * (2 * X * (2 * X)) := by
        have := Nat.mul_le_mul hY2 hY2
        exact Nat.mul_le_mul this this
      have hXX : X * X * (X * X) = 2 ^ 2 ^ (3 * B + 6) := by
        rw [hX, ← pow_add, ← pow_add]
        congr 1
        rw [show 3 * B + 6 = (3 * B + 4) + 2 by ring, pow_add]
        ring
      have hfin : 2 ^ 13 * 2 ^ 2 ^ (3 * B + 6) ≤ 2 ^ 2 ^ (3 * (B + 1) + 4) := by
        rw [← pow_add]
        apply Nat.pow_le_pow_right (by norm_num)
        rw [show 3 * (B + 1) + 4 = (3 * B + 6) + 1 by ring, pow_succ 2 (3 * B + 6)]
        have : 13 ≤ 2 ^ (3 * B + 6) := by
          calc 13 ≤ 2 ^ 6 := by norm_num
            _ ≤ 2 ^ (3 * B + 6) := Nat.pow_le_pow_right (by norm_num) (by omega)
        omega
      nlinarith

end Hofstadter

/-! ### Main statements (verbatim from formal-conjectures) -/

/--
Bolan and Tang [Ta26] independently proved that $a_n-n$ is nondecreasing.
-/
theorem erdos_423.variants.nondecreasing :
    ∀ a : ℕ → ℕ, IsHofstadterSeq a →
    ∀ n m : ℕ, 1 ≤ n → n ≤ m → a n - n ≤ a m - m := by
  intro a h n m hn hnm
  have := Hofstadter.add_sub_le h hn hnm
  omega

/--
Bolan and Tang [Ta26] independently proved that $a_n-n\to\infty$.
-/
theorem erdos_423.variants.unbounded :
    ∀ a : ℕ → ℕ, IsHofstadterSeq a →
    ∀ M : ℕ, ∀ᶠ n in atTop, M + n ≤ a n := by
  intro a h M
  filter_upwards [eventually_ge_atTop (2 ^ 2 ^ (3 * M + 4))] with n hn
  by_contra hlt
  push Not at hlt
  have h1 : 1 ≤ 2 ^ 2 ^ (3 * M + 4) := Nat.one_le_two_pow
  have := Hofstadter.lt_of_le_add h M n (by omega) (by omega)
  omega

/--
Bolan and Tang [Ta26] independently proved that infinitely many positive integers do not occur in
the Hofstadter sequence.
-/
theorem erdos_423.variants.infinite_complement :
    ∀ a : ℕ → ℕ, IsHofstadterSeq a → Set.Infinite (Set.range a)ᶜ := by
  intro a h hfin
  obtain ⟨X, hX⟩ := hfin.bddAbove
  obtain ⟨n, hn, hn1⟩ :=
    ((erdos_423.variants.unbounded a h (X + a 0 + 1)).and (eventually_ge_atTop 1)).exists
  have hsub : Finset.Icc (X + a 0 + 1) (a n) ⊆ (Finset.Icc 1 n).image a := by
    intro x hx
    rw [Finset.mem_Icc] at hx
    have hxr : x ∈ Set.range a := by
      by_contra hxn
      have : x ≤ X := hX hxn
      omega
    obtain ⟨k, rfl⟩ := hxr
    rw [Finset.mem_image]
    refine ⟨k, ?_, rfl⟩
    rw [Finset.mem_Icc]
    have hk1 : 1 ≤ k := by
      rcases Nat.eq_zero_or_pos k with rfl | hk
      · omega
      · exact hk
    refine ⟨hk1, ?_⟩
    by_contra hkn
    push Not at hkn
    have := Hofstadter.lt_of_lt h hn1 hkn
    omega
  have h1 := Finset.card_le_card hsub
  have h2 := Finset.card_image_le (s := Finset.Icc 1 n) (f := a)
  simp only [Nat.card_Icc] at h1 h2
  omega

/--
Tang [Ta26] proved the lower bound $a_n=n+\Omega(\log\log n)$.
-/
theorem erdos_423.variants.lower_bound :
    ∀ a : ℕ → ℕ, IsHofstadterSeq a →
    (fun n : ℕ => Real.log (Real.log n)) =O[atTop]
      (fun n : ℕ => (a n : ℝ) - n) := by
  intro a h
  refine Asymptotics.IsBigO.of_bound 7 ?_
  filter_upwards [erdos_423.variants.unbounded a h 1, eventually_ge_atTop 3] with n hb hn
  obtain ⟨B, hB⟩ : ∃ B, a n = B + n := ⟨a n - n, by omega⟩
  have hB1 : 1 ≤ B := by omega
  have hlt := Hofstadter.lt_of_le_add h B n (by omega) hB.le
  have hg : ‖(a n : ℝ) - n‖ = B := by
    rw [hB, Nat.cast_add, add_sub_cancel_right, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  rw [hg]
  have hn3 : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hlogn : 1 < Real.log n := by
    rw [Real.lt_log_iff_exp_lt (by linarith)]
    have := Real.exp_one_lt_d9
    linarith
  have hloglog : 0 < Real.log (Real.log n) := Real.log_pos hlogn
  rw [Real.norm_eq_abs, abs_of_pos hloglog]
  have hlog2 : Real.log 2 < 1 := by
    have := Real.log_two_lt_d9
    linarith
  have hlog2' : 0 < Real.log 2 := Real.log_pos (by norm_num)
  -- `log n < 2^(3B+4)`
  have h1 : Real.log n < (2 : ℝ) ^ (3 * B + 4) := by
    have hcast : (n : ℝ) < (2 : ℝ) ^ 2 ^ (3 * B + 4) := by exact_mod_cast hlt
    have := Real.log_lt_log (by linarith) hcast
    rw [Real.log_pow] at this
    push_cast at this
    have hp : (0 : ℝ) < (2 : ℝ) ^ (3 * B + 4) := by positivity
    nlinarith
  have h2 : Real.log (Real.log n) < (3 * B + 4 : ℕ) := by
    have := Real.log_lt_log (by linarith) h1
    rw [Real.log_pow] at this
    have hE : (0 : ℝ) < ((3 * B + 4 : ℕ) : ℝ) := by positivity
    nlinarith
  have hB1' : (1 : ℝ) ≤ B := by exact_mod_cast hB1
  push_cast at h2
  linarith

/-- The unboundedness of $a_n-n$ is equivalent to the sequence omitting infinitely many positive
integers. -/
theorem erdos_423.test.unbounded_iff_infinite_complement :
    type_of% erdos_423.variants.unbounded ↔
      type_of% erdos_423.variants.infinite_complement :=
  ⟨fun _ => erdos_423.variants.infinite_complement, fun _ => erdos_423.variants.unbounded⟩

/-! ### Existence and uniqueness of the sequence -/

namespace Hofstadter

theorem block_iff {f g : ℕ → ℕ} {k m : ℕ} (hfg : ∀ i, 1 ≤ i → i + 1 ≤ k → f i = g i) :
    IsConsecutiveBlockSum f k m ↔ IsConsecutiveBlockSum g k m := by
  constructor
  · rintro ⟨i, j, hi, hij, hjk, hm⟩
    refine ⟨i, j, hi, hij, hjk, hm.trans (Finset.sum_congr rfl fun l hl => ?_)⟩
    rw [Finset.mem_Icc] at hl
    exact hfg l (by omega) (by omega)
  · rintro ⟨i, j, hi, hij, hjk, hm⟩
    refine ⟨i, j, hi, hij, hjk, hm.trans (Finset.sum_congr rfl fun l hl => ?_)⟩
    rw [Finset.mem_Icc] at hl
    exact (hfg l (by omega) (by omega)).symm

/-- `IsHofstadterSeq` determines the sequence at every index `n ≥ 1`. -/
theorem eq_of_isHofstadterSeq {a b : ℕ → ℕ} (ha : IsHofstadterSeq a) (hb : IsHofstadterSeq b) :
    ∀ n, 1 ≤ n → a n = b n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    rcases Nat.lt_or_ge n 3 with hn3 | hn3
    · rcases (show n = 1 ∨ n = 2 by omega) with rfl | rfl
      · rw [ha.1, hb.1]
      · rw [ha.2.1, hb.2.1]
    · have hiff : ∀ x, IsConsecutiveBlockSum a n x ↔ IsConsecutiveBlockSum b n x := fun x =>
        block_iff fun i hi hin => ih i (by omega) hi
      have hprev : a (n - 1) = b (n - 1) := ih (n - 1) (by omega) (by omega)
      obtain ⟨hab, hal, ham⟩ := ha.2.2 n hn3
      obtain ⟨hbb, hbl, hbm⟩ := hb.2.2 n hn3
      rcases lt_trichotomy (a n) (b n) with hlt | heq | hgt
      · exact absurd ((hiff _).1 hab) (hbm _ (by omega) hlt)
      · exact heq
      · exact absurd ((hiff _).2 hbb) (ham _ (by omega) hgt)

/-- One greedy step: the least `m > f (k - 1)` which is a block sum of `f` below index `k`. -/
noncomputable def next (f : ℕ → ℕ) (k : ℕ) : ℕ :=
  sInf {m | f (k - 1) < m ∧ IsConsecutiveBlockSum f k m}

/-- `pre n` agrees with the sequence on the indices `1, …, n + 2`. -/
noncomputable def pre : ℕ → ℕ → ℕ
  | 0 => fun i => if i = 1 then 1 else if i = 2 then 2 else 0
  | n + 1 => Function.update (pre n) (n + 3) (next (pre n) (n + 3))

/-- The Hofstadter sequence A005243 (with the unconstrained value `hof 0 = 0`). -/
noncomputable def hof (k : ℕ) : ℕ := pre k k

theorem pre_stable {n i : ℕ} (hi : i ≤ n + 2) : ∀ n', n ≤ n' → pre n' i = pre n i := by
  intro n' hn'
  induction n', hn' using Nat.le_induction with
  | base => rfl
  | succ n' hn' ih =>
    show Function.update (pre n') (n' + 3) (next (pre n') (n' + 3)) i = pre n i
    rw [Function.update_of_ne (by omega), ih]

theorem hof_eq_pre {n i : ℕ} (hi : i ≤ n + 2) : hof i = pre n i := by
  unfold hof
  rcases le_total i n with h | h
  · exact (pre_stable (n := i) (by omega) n h).symm
  · exact pre_stable hi i h

theorem hof_one : hof 1 = 1 := by
  rw [hof_eq_pre (n := 0) (by norm_num)]
  rfl

theorem hof_two : hof 2 = 2 := by
  rw [hof_eq_pre (n := 0) (by norm_num)]
  rfl

theorem hof_add_three (n : ℕ) :
    hof (n + 3) = sInf {m | hof (n + 2) < m ∧ IsConsecutiveBlockSum hof (n + 3) m} := by
  have h1 : hof (n + 3) = next (pre n) (n + 3) := by
    rw [hof_eq_pre (n := n + 1) (by omega)]
    exact Function.update_self ..
  rw [h1, next, show n + 3 - 1 = n + 2 by omega, hof_eq_pre (n := n) le_rfl]
  congr 1
  ext m
  simp only [Set.mem_ofPred_eq]
  exact and_congr_right fun _ => block_iff fun i _ hi => (hof_eq_pre (by omega)).symm

/-- The Hofstadter sequence exists, so the statements above are not vacuous. -/
theorem isHofstadterSeq_hof : IsHofstadterSeq hof := by
  refine ⟨hof_one, hof_two, fun k hk => ?_⟩
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 3 := ⟨k - 3, by omega⟩
  rw [show n + 3 - 1 = n + 2 by omega]
  have hne : {m | hof (n + 2) < m ∧ IsConsecutiveBlockSum hof (n + 3) m}.Nonempty := by
    refine ⟨∑ l ∈ Finset.Icc 1 (n + 2), hof l, ?_, 1, n + 2, le_rfl, by omega, by omega, rfl⟩
    have hsub : ({1, n + 2} : Finset ℕ) ⊆ Finset.Icc 1 (n + 2) := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rw [Finset.mem_Icc]
      omega
    have := Finset.sum_le_sum_of_subset (f := hof) hsub
    rw [Finset.sum_pair (by omega), hof_one] at this
    omega
  have hmem := Nat.sInf_mem hne
  rw [← hof_add_three] at hmem
  simp only [Set.mem_ofPred_eq] at hmem
  refine ⟨hmem.2, hmem.1, fun m hm1 hm2 hblock => ?_⟩
  rw [hof_add_three] at hm2
  exact Nat.notMem_of_lt_sInf hm2 ⟨hm1, hblock⟩

end Hofstadter

/-- Non-vacuity: a sequence satisfying `IsHofstadterSeq` exists. -/
theorem exists_isHofstadterSeq : ∃ a : ℕ → ℕ, IsHofstadterSeq a :=
  ⟨Hofstadter.hof, Hofstadter.isHofstadterSeq_hof⟩

end Erdos423
