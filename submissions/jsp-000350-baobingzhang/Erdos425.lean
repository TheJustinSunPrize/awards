import Mathlib

/-!
# Erdős Problem 425, real variant: Alexander's construction

Erdős Problem 425 (https://www.erdosproblems.com/425; [Er69], [Er70b], [Er73], [Er77], [Er77c],
[Er80], [ErGr80]) asks for the largest `A ⊆ {1, …, n}` all of whose products `ab` (`a < b`) are
distinct. The problem page also states a real-number variant:

> what is the size of the largest `A ⊂ [1, x]` such that for any distinct `a, b, c, d ∈ A` we have
> `|ab - cd| ≥ 1`? Erdős had conjectured (see [Er73] and [Er77c]) that `|A| = o(x)`. In [ErGr80]
> Erdős and Graham report that Alexander had given a construction disproving this conjecture,
> establishing that `|A| ≫ x` is possible. [...] Furthermore, a simple modification allows for
> `A` to also be `1`-separated.

This file proves Alexander's result: for every `x ≥ 18` there is a finite `1`-separated
`A ⊆ [1, x]` with `|A| ≥ x / 18` and `|ab - cd| ≥ 1` for all admissible `a, b, c, d`. Hence
Erdős's `o(x)` conjecture for the real variant is false. The integer problem (the asymptotics of
`F(n)`, and the `r`-fold product question) is not addressed.

## Credit

The result is due to Alexander, as reported by Erdős and Graham [ErGr80]; his construction is
given in [Er80]. The proof here follows the simplified version sketched on the problem page
(`A = {X e^{b/X²} : b ∈ B}` for a Sidon set `B ⊆ [1, X²]` with `|B| ≫ X`), using the Sidon set
`{2pk + (k² mod p) : 0 ≤ k < p}` of Erdős and Turán [ErTu41] and Bertrand's postulate (from
Mathlib). This Lean formalization was written with AI assistance.

## Statements and faithfulness

* `PairwiseDistinctProductSep A`: for all pairwise distinct `a, b, c, d ∈ A`, `1 ≤ |ab - cd|`.
  This is the condition on the problem page.
* `ProductSep A`: `1 ≤ |ab - cd|` for all `a, b, c, d ∈ A` unless `(a, b) = (c, d)` or
  `(a, b) = (d, c)`. It implies `PairwiseDistinctProductSep A` (`ProductSep.pairwiseDistinct`)
  and also covers `a = b` and pairs sharing one element, so it implies every reading of
  "distinct" (for example `a < b`, `c < d`, `(a, b) ≠ (c, d)`, as in the integer problem).
* `OneSeparated A`: `1 ≤ |a - b|` for distinct `a, b ∈ A` (the "simple modification").
* Sets are `Finset ℝ` with `(A : Set ℝ) ⊆ Set.Icc 1 x`, and `|A|` is `A.card`.

## Main results

* `Erdos425.exists_large_set`: for `x ≥ 18` there is `A ⊆ [1, x]` with `x / 18 ≤ |A|`,
  `OneSeparated A` and `ProductSep A`.
* `Erdos425.erdos_425_real`: `∃ c > 0, ∀ᶠ x in atTop, ∃ A ⊆ [1, x], c x ≤ |A|`, with
  `OneSeparated A` and `ProductSep A`.
* `Erdos425.erdos_425_real_page`: the same with the page's condition `PairwiseDistinctProductSep`.
* `Erdos425.erdos_425_real_conjecture_false`: the negation of
  `∀ ε > 0, ∀ᶠ x in atTop, ∀ A ⊆ [1, x], PairwiseDistinctProductSep A → |A| ≤ ε x`,
  which is the statement `|A| = o(x)`.
* `Erdos425.erdos_425_real_not_isLittleO`: no `f` with `|A| ≤ f x` for every admissible
  `A ⊆ [1, x]` (for all large `x`) satisfies `f =o[atTop] id`.

## Proof

Let `p` be a prime and `b_k = 2pk + (k² mod p)` for `k < p`. If `b_i + b_j = b_k + b_l`, then,
since the residues are `< p`, `i + j = k + l` and `i² + j² ≡ k² + l² (mod p)`; hence
`p ∣ 2 (i - k)(i - l)`, so `{i, j} = {k, l}` (`sidon_sum_eq`; the case `p = 2` is direct).
Moreover `b_i + p ≤ b_j` for `i < j`, and `b_k < 2p²`. Put `a_k = p · exp(b_k / p²) ∈ [p, 9p)`.
Since `|e^u - e^v| ≥ |u - v|` for `u, v ≥ 0`, we get
`|a_i a_j - a_k a_l| = p² |e^{(b_i + b_j)/p²} - e^{(b_k + b_l)/p²}| ≥ |b_i + b_j - b_k - b_l| ≥ 1`
whenever the index multisets differ, and `|a_i - a_j| ≥ p · p / p² = 1` for `i ≠ j`.
For `x ≥ 18` take `n = ⌊x / 18⌋ ≥ 1` and a prime `n < p ≤ 2n`. Then `A ⊆ [2, 18n] ⊆ [1, x]`
and `|A| = p ≥ n + 1 > x / 18`.

## References

* [Er73] Erdős, P., _Problems and results on combinatorial number theory_. A survey of
  combinatorial theory (1973), 117–138.
* [Er77c] Erdős, P., _Problems and results on combinatorial number theory. III_. Number theory
  day (1977), 43–72.
* [Er80] Erdős, P., _A survey of problems in combinatorial number theory_. Ann. Discrete Math.
  (1980), 89–115.
* [ErGr80] Erdős, P. and Graham, R., _Old and new problems and results in combinatorial number
  theory_. Monographies de L'Enseignement Mathématique (1980).
* [ErTu41] Erdős, P. and Turán, P., _On a problem of Sidon in additive number theory, and on
  some related problems_. J. London Math. Soc. 16 (1941), 212–215.
-/

namespace Erdos425

open Filter Finset

/-- The condition of the real variant as stated on the problem page. -/
def PairwiseDistinctProductSep (A : Finset ℝ) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, ∀ d ∈ A,
    a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d → 1 ≤ |a * b - c * d|

/-- Strong form: `|ab - cd| ≥ 1` whenever `{a, b} ≠ {c, d}` as multisets. -/
def ProductSep (A : Finset ℝ) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, ∀ d ∈ A,
    ¬ (a = c ∧ b = d) → ¬ (a = d ∧ b = c) → 1 ≤ |a * b - c * d|

/-- `A` is `1`-separated. -/
def OneSeparated (A : Finset ℝ) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, a ≠ b → 1 ≤ |a - b|

theorem ProductSep.pairwiseDistinct {A : Finset ℝ} (h : ProductSep A) :
    PairwiseDistinctProductSep A := by
  intro a ha b hb c hc d hd _ hac had _ _ _
  exact h a ha b hb c hc d hd (fun h' => hac h'.1) (fun h' => had h'.1)

/-! ### The Erdős–Turán Sidon set -/

/-- `sidon p k = 2pk + (k² mod p)`. -/
def sidon (p k : ℕ) : ℕ := 2 * p * k + k ^ 2 % p

lemma sidon_add_le {p i j : ℕ} (hp : 0 < p) (hij : i < j) : sidon p i + p ≤ sidon p j := by
  unfold sidon
  have h1 : i ^ 2 % p < p := Nat.mod_lt _ hp
  have h2 : 2 * p * (i + 1) ≤ 2 * p * j := Nat.mul_le_mul_left _ hij
  nlinarith [Nat.zero_le (j ^ 2 % p)]

lemma sidon_strictMono {p : ℕ} (hp : 0 < p) : StrictMono (sidon p) := fun i j hij => by
  have := sidon_add_le hp hij
  omega

lemma sidon_lt {p k : ℕ} (hp : 0 < p) (hk : k < p) : sidon p k < 2 * p ^ 2 := by
  unfold sidon
  have h1 : k ^ 2 % p < p := Nat.mod_lt _ hp
  have h2 : 2 * p * (k + 1) ≤ 2 * p * p := Nat.mul_le_mul_left _ hk
  nlinarith

/-- The Sidon property, including the case `i = j`. -/
lemma sidon_sum_eq {p i j k l : ℕ} (hp : p.Prime) (hi : i < p) (hj : j < p)
    (hk : k < p) (hl : l < p) (h : sidon p i + sidon p j = sidon p k + sidon p l) :
    (i = k ∧ j = l) ∨ (i = l ∧ j = k) := by
  have hp0 := hp.pos
  unfold sidon at h
  have ri := Nat.mod_lt (i ^ 2) hp0
  have rj := Nat.mod_lt (j ^ 2) hp0
  have rk := Nat.mod_lt (k ^ 2) hp0
  have rl := Nat.mod_lt (l ^ 2) hp0
  have ri0 := Nat.zero_le (i ^ 2 % p)
  have rj0 := Nat.zero_le (j ^ 2 % p)
  have rk0 := Nat.zero_le (k ^ 2 % p)
  have rl0 := Nat.zero_le (l ^ 2 % p)
  have hs : i + j = k + l := by
    rcases lt_trichotomy (i + j) (k + l) with hlt | heq | hgt
    · have := Nat.mul_le_mul_left (2 * p) hlt
      nlinarith
    · exact heq
    · have := Nat.mul_le_mul_left (2 * p) hgt
      nlinarith
  have hr : i ^ 2 % p + j ^ 2 % p = k ^ 2 % p + l ^ 2 % p := by
    have : 2 * p * i + 2 * p * j = 2 * p * k + 2 * p * l := by
      rw [← mul_add, ← mul_add, hs]
    omega
  have hmod : (i ^ 2 + j ^ 2) % p = (k ^ 2 + l ^ 2) % p := by
    rw [Nat.add_mod, hr, ← Nat.add_mod]
  have hdvd := Nat.ModEq.dvd hmod.symm
  push_cast at hdvd
  have hs' : (j : ℤ) = k + l - i := by
    have : (i : ℤ) + j = k + l := by exact_mod_cast hs
    linarith
  have key : ((i : ℤ) ^ 2 + j ^ 2) - (k ^ 2 + l ^ 2) = 2 * ((i - k) * (i - l)) := by
    rw [hs']; ring
  rw [key] at hdvd
  have hpz : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  rcases hpz.dvd_or_dvd hdvd with h2 | h2
  · -- `p ∣ 2` forces `p = 2`, and then all indices lie in `{0, 1}`
    have := Int.le_of_dvd (by norm_num) h2
    have := hp.two_le
    omega
  rcases hpz.dvd_or_dvd h2 with h3 | h3
  · have := Int.eq_zero_of_abs_lt_dvd h3 (by rw [abs_lt]; constructor <;> omega)
    left; omega
  · have := Int.eq_zero_of_abs_lt_dvd h3 (by rw [abs_lt]; constructor <;> omega)
    right; omega

/-! ### Real analysis -/

lemma sub_le_exp_sub {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) :
    v - u ≤ Real.exp v - Real.exp u := by
  have h1 : Real.exp v = Real.exp u * Real.exp (v - u) := by
    rw [← Real.exp_add]; congr 1; ring
  have h2 := Real.add_one_le_exp (v - u)
  have h3 : 1 ≤ Real.exp u := Real.one_le_exp hu
  rw [h1]
  nlinarith [mul_nonneg (sub_nonneg.2 h3) (sub_nonneg.2 huv),
    mul_le_mul_of_nonneg_left h2 (le_trans zero_le_one h3)]

lemma abs_sub_le_abs_exp_sub {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) :
    |u - v| ≤ |Real.exp u - Real.exp v| := by
  rcases le_total u v with h | h
  · have := sub_le_exp_sub hu h
    have := Real.exp_le_exp.mpr h
    rwa [abs_sub_comm, abs_sub_comm (Real.exp u), abs_of_nonneg (by linarith),
      abs_of_nonneg (by linarith)]
  · have := sub_le_exp_sub hv h
    have := Real.exp_le_exp.mpr h
    rwa [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]

/-! ### Alexander's construction -/

/-- `point p k = p · exp(sidon p k / p²)`. -/
noncomputable def point (p k : ℕ) : ℝ := p * Real.exp (sidon p k / (p : ℝ) ^ 2)

/-- The set `{p · exp(b / p²) : b ∈ B}` for the Erdős–Turán Sidon set `B`. -/
noncomputable def alexander (p : ℕ) : Finset ℝ := (Finset.range p).image (point p)

lemma point_mul (p i j : ℕ) :
    point p i * point p j =
      (p : ℝ) ^ 2 * Real.exp (((sidon p i + sidon p j : ℕ) : ℝ) / (p : ℝ) ^ 2) := by
  simp only [point]
  push_cast
  rw [add_div, Real.exp_add]
  ring

lemma one_le_abs_point_mul_sub {p : ℕ} (hp : 0 < p) {i j k l : ℕ}
    (h : sidon p i + sidon p j ≠ sidon p k + sidon p l) :
    1 ≤ |point p i * point p j - point p k * point p l| := by
  have hpp : (0 : ℝ) < (p : ℝ) ^ 2 := by positivity
  rw [point_mul, point_mul, ← mul_sub, abs_mul, abs_of_pos hpp]
  set S := sidon p i + sidon p j
  set T := sidon p k + sidon p l
  have h1 : 1 ≤ |(S : ℝ) - T| := by
    rcases Nat.lt_or_gt_of_ne h with h' | h'
    · have : (S : ℝ) + 1 ≤ T := by exact_mod_cast h'
      exact le_abs.mpr (Or.inr (by linarith))
    · have : (T : ℝ) + 1 ≤ S := by exact_mod_cast h'
      exact le_abs.mpr (Or.inl (by linarith))
  have h2 := abs_sub_le_abs_exp_sub (u := (S : ℝ) / (p : ℝ) ^ 2) (v := (T : ℝ) / (p : ℝ) ^ 2)
    (by positivity) (by positivity)
  rw [← sub_div, abs_div, abs_of_pos hpp] at h2
  calc (1 : ℝ) ≤ |(S : ℝ) - T| := h1
    _ = (p : ℝ) ^ 2 * (|(S : ℝ) - T| / (p : ℝ) ^ 2) := by field_simp
    _ ≤ _ := by gcongr

lemma one_le_abs_point_sub {p : ℕ} (hp : 0 < p) {i j : ℕ} (h : i ≠ j) :
    1 ≤ |point p i - point p j| := by
  have hp' : (0 : ℝ) < p := by exact_mod_cast hp
  have hpp : (0 : ℝ) < (p : ℝ) ^ 2 := by positivity
  simp only [point]
  rw [← mul_sub, abs_mul, abs_of_pos hp']
  have hij : (p : ℝ) ≤ |(sidon p i : ℝ) - sidon p j| := by
    rcases Nat.lt_or_gt_of_ne h with h' | h'
    · have : (sidon p i : ℝ) + p ≤ sidon p j := by exact_mod_cast sidon_add_le hp h'
      exact le_abs.mpr (Or.inr (by linarith))
    · have : (sidon p j : ℝ) + p ≤ sidon p i := by exact_mod_cast sidon_add_le hp h'
      exact le_abs.mpr (Or.inl (by linarith))
  have h2 := abs_sub_le_abs_exp_sub (u := (sidon p i : ℝ) / (p : ℝ) ^ 2)
    (v := (sidon p j : ℝ) / (p : ℝ) ^ 2) (by positivity) (by positivity)
  rw [← sub_div, abs_div, abs_of_pos hpp] at h2
  calc (1 : ℝ) = p * (p / (p : ℝ) ^ 2) := by field_simp
    _ ≤ p * (|(sidon p i : ℝ) - sidon p j| / (p : ℝ) ^ 2) := by gcongr
    _ ≤ _ := by gcongr

lemma point_strictMono {p : ℕ} (hp : 0 < p) : StrictMono (point p) := fun i j hij => by
  have hp' : (0 : ℝ) < p := by exact_mod_cast hp
  simp only [point]
  apply mul_lt_mul_of_pos_left _ hp'
  apply Real.exp_lt_exp.mpr
  apply (div_lt_div_iff_of_pos_right (by positivity)).mpr
  exact_mod_cast sidon_strictMono hp hij

lemma le_point {p : ℕ} (k : ℕ) : (p : ℝ) ≤ point p k := by
  simp only [point]
  have := Real.one_le_exp (by positivity : (0 : ℝ) ≤ sidon p k / (p : ℝ) ^ 2)
  exact le_mul_of_one_le_right (by positivity) this

lemma point_lt {p k : ℕ} (hp : 0 < p) (hk : k < p) : point p k < 9 * p := by
  have hp' : (0 : ℝ) < p := by exact_mod_cast hp
  simp only [point]
  have h1 : (sidon p k : ℝ) / (p : ℝ) ^ 2 < 2 := by
    rw [div_lt_iff₀ (by positivity)]
    exact_mod_cast sidon_lt hp hk
  have h2 : Real.exp ((sidon p k : ℝ) / (p : ℝ) ^ 2) < 9 := by
    calc _ < Real.exp 2 := Real.exp_lt_exp.mpr h1
      _ = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
      _ < 3 * 3 := by
          have := Real.exp_one_lt_three
          have := Real.exp_pos 1
          nlinarith
      _ = 9 := by norm_num
  nlinarith

theorem alexander_spec {p : ℕ} (hp : p.Prime) :
    (alexander p : Set ℝ) ⊆ Set.Ico (p : ℝ) (9 * p) ∧ (alexander p).card = p ∧
      OneSeparated (alexander p) ∧ ProductSep (alexander p) := by
  have hp0 := hp.pos
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a ha
    simp only [alexander, coe_image, coe_range, Set.mem_image, Set.mem_Iio] at ha
    obtain ⟨k, hk, rfl⟩ := ha
    exact ⟨le_point k, point_lt hp0 hk⟩
  · rw [alexander, card_image_of_injective _ (point_strictMono hp0).injective, card_range]
  · intro a ha b hb hab
    simp only [alexander, mem_image, mem_range] at ha hb
    obtain ⟨i, -, rfl⟩ := ha
    obtain ⟨j, -, rfl⟩ := hb
    exact one_le_abs_point_sub hp0 (fun h => hab (h ▸ rfl))
  · intro a ha b hb c hc d hd hac had
    simp only [alexander, mem_image, mem_range] at ha hb hc hd
    obtain ⟨i, hi, rfl⟩ := ha
    obtain ⟨j, hj, rfl⟩ := hb
    obtain ⟨k, hk, rfl⟩ := hc
    obtain ⟨l, hl, rfl⟩ := hd
    apply one_le_abs_point_mul_sub hp0
    intro hsum
    rcases sidon_sum_eq hp hi hj hk hl hsum with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hac ⟨rfl, rfl⟩
    · exact had ⟨rfl, rfl⟩

/-! ### Main results -/

theorem exists_large_set (x : ℝ) (hx : 18 ≤ x) :
    ∃ A : Finset ℝ, (A : Set ℝ) ⊆ Set.Icc 1 x ∧ x / 18 ≤ A.card ∧
      OneSeparated A ∧ ProductSep A := by
  set n := ⌊x / 18⌋₊ with hn
  have hn1 : 1 ≤ n := Nat.le_floor (by norm_num; linarith)
  obtain ⟨p, hp, hnp, hp2n⟩ := Nat.exists_prime_lt_and_le_two_mul n (by omega)
  obtain ⟨hsub, hcard, hsep, hprod⟩ := alexander_spec hp
  have hnx : (n : ℝ) ≤ x / 18 := Nat.floor_le (by positivity)
  refine ⟨alexander p, ?_, ?_, hsep, hprod⟩
  · intro a ha
    obtain ⟨h1, h2⟩ := hsub ha
    have : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
    have : (p : ℝ) ≤ 2 * n := by exact_mod_cast hp2n
    constructor <;> linarith
  · rw [hcard]
    have := Nat.lt_floor_add_one (x / 18)
    have : (n : ℝ) + 1 ≤ p := by exact_mod_cast hnp
    linarith

/-- Alexander's theorem, strong form: for all large `x` there is a `1`-separated `A ⊆ [1, x]`
with `|A| ≥ x / 18` and `|ab - cd| ≥ 1` whenever `{a, b} ≠ {c, d}`. -/
theorem erdos_425_real :
    ∃ c > (0 : ℝ), ∀ᶠ x in atTop, ∃ A : Finset ℝ, (A : Set ℝ) ⊆ Set.Icc 1 x ∧
      c * x ≤ A.card ∧ OneSeparated A ∧ ProductSep A :=
  ⟨1 / 18, by norm_num, eventually_atTop.mpr ⟨18, fun x hx => by
    obtain ⟨A, h1, h2, h3, h4⟩ := exists_large_set x hx
    exact ⟨A, h1, by linarith, h3, h4⟩⟩⟩

/-- Alexander's theorem with the condition exactly as on the problem page. -/
theorem erdos_425_real_page :
    ∃ c > (0 : ℝ), ∀ᶠ x in atTop, ∃ A : Finset ℝ, (A : Set ℝ) ⊆ Set.Icc 1 x ∧
      c * x ≤ A.card ∧ PairwiseDistinctProductSep A := by
  obtain ⟨c, hc, h⟩ := erdos_425_real
  exact ⟨c, hc, h.mono fun x ⟨A, h1, h2, _, h4⟩ => ⟨A, h1, h2, h4.pairwiseDistinct⟩⟩

/-- Erdős's conjecture `|A| = o(x)` for the real variant is false. -/
theorem erdos_425_real_conjecture_false :
    ¬ ∀ ε > (0 : ℝ), ∀ᶠ x in atTop, ∀ A : Finset ℝ, (A : Set ℝ) ⊆ Set.Icc 1 x →
      PairwiseDistinctProductSep A → (A.card : ℝ) ≤ ε * x := by
  intro h
  obtain ⟨x, hx⟩ := ((h (1 / 36) (by norm_num)).and (eventually_ge_atTop 18)).exists
  obtain ⟨A, h1, h2, -, h4⟩ := exists_large_set x hx.2
  have := hx.1 A h1 h4.pairwiseDistinct
  linarith [hx.2]

/-- No function bounding `|A|` for admissible `A ⊆ [1, x]` (for all large `x`) is `o(x)`. -/
theorem erdos_425_real_not_isLittleO (f : ℝ → ℝ)
    (hf : ∀ᶠ x in atTop, ∀ A : Finset ℝ, (A : Set ℝ) ⊆ Set.Icc 1 x →
      PairwiseDistinctProductSep A → (A.card : ℝ) ≤ f x) :
    ¬ f =o[atTop] id := by
  intro hlo
  have h := hlo.bound (by norm_num : (0 : ℝ) < 1 / 36)
  obtain ⟨x, hx⟩ := ((h.and hf).and (eventually_ge_atTop 18)).exists
  obtain ⟨⟨h5, h6⟩, h7⟩ := hx
  obtain ⟨A, h1, h2, -, h4⟩ := exists_large_set x h7
  have h8 := h6 A h1 h4.pairwiseDistinct
  simp only [id, Real.norm_eq_abs] at h5
  rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ x)] at h5
  linarith [le_abs_self (f x)]

end Erdos425
