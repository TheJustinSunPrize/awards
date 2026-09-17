import Mathlib

/-!
# Erdős Problem 791: Mrose's construction, `g(n) ~ 2√n` is false

Let `g(n)` be the minimal size of a set `A ⊆ {0, …, n}` with `{0, …, n} ⊆ A + A`
(a *finite additive 2-basis*). Erdős asked to estimate `g(n)`, and in particular whether
`g(n) ~ 2 n^{1/2}`. The general estimation problem is open. Mrose (1979) disproved
`g(n) ~ 2√n` with an explicit construction giving `g(n)² ≤ (7/2 + o(1)) n`. This file
formalizes that construction and its consequences.

The formal-conjectures project (checked locally) has no file for Problem 791, so `g` is defined
from the wording on erdosproblems.com: "Let $g(n)$ be minimal such that there exists
$A\subseteq \{0,\ldots,n\}$ of size $g(n)$ with $\{0,\ldots,n\}\subseteq A+A$."

## Construction

We use the form of Mrose's basis given by Kohonen (*An improved lower bound for finite additive
2-bases*, J. Number Theory 2017, arXiv:1606.04770, Section 2, Example 2). Kohonen assumes
`t ≥ 2`; everything below works for `t ≥ 1`. Let

* `V = [0, t]`,
* `H = [0, (t), t² - t] = {0, t, 2t, …, t² - t}`,
* `S = [0, (t + 1), t² - 1] = {0, t + 1, 2(t + 1), …, t² - 1}`,

and `A = (V + t²·{0, 6, 10}) ∪ (H + t²·{0, 1, 2}) ∪ (S + t²·{3})`.
Then `|A| ≤ 3(t + 1) + 3t + t = 7t + 3` and `A ⊆ [0, 10t² + t] ⊆ [0, 14t² - 1]`.
Write `Q = [0, t² - 1]`.

* Fact 1: `V + H ⊇ Q` and `V + S ⊇ Q` (`fact1_VH`, `fact1_VS`).
* Fact 2: every `r ∈ Q` has `r ∈ H + S` or `r + t² ∈ H + S` (`fact2`).

So `A + A` contains `Q + t²·c` for `c ∈ {0, 6, 10} + {0, 1, 2} = {0, 1, 2, 6, 7, 8, 10, 11, 12}`
(from `V + H`), for `c ∈ {0, 6, 10} + 3 = {3, 9, 13}` (from `V + S`), and for `c ∈ {4, 5}`
(from `H + S`, using Fact 2 with the two neighbouring translates `H + t²·{0, 1, 2}`).
Hence `[0, 14t² - 1] ⊆ A + A` (`mroseBasis_cover`).

## Main results

* `mrose_construction`: for every `t ≥ 1` there is `A ⊆ {0, …, 14t² - 1}` with `|A| ≤ 7t + 7`
  and `{0, …, 14t² - 1} ⊆ A + A`.
* `g_fourteen_mul_sq_sub_one_le`: `g(14t² - 1) ≤ 7t + 7`.
* `eventually_g_sq_le`: `g` is monotone, so for every `ε > 0`, eventually
  `g(n)² ≤ (7/2 + ε) n`.
* `erdos_791`: `¬ g(n) ~ 2√n`; also `not_tendsto_g_div_sqrt`: `g(n)/√n` does not tend to `2`.
-/

open Filter
open scoped Pointwise Topology Asymptotics Finset

namespace Erdos791

/-- `g n` is the minimal size of a set `A ⊆ {0, …, n}` such that `{0, …, n} ⊆ A + A`. -/
noncomputable def g (n : ℕ) : ℕ :=
  sInf {k | ∃ A : Finset ℕ, A ⊆ Finset.Icc 0 n ∧ Finset.Icc 0 n ⊆ A + A ∧ #A = k}

/-- The set defining `g n` is nonempty: `A = {0, …, n}` works. -/
theorem g_set_nonempty (n : ℕ) :
    {k | ∃ A : Finset ℕ, A ⊆ Finset.Icc 0 n ∧ Finset.Icc 0 n ⊆ A + A ∧ #A = k}.Nonempty :=
  ⟨_, Finset.Icc 0 n, subset_rfl,
    fun x hx => Finset.mem_add.2 ⟨x, hx, 0, by simp, add_zero x⟩, rfl⟩

/-- `g n` is attained by some admissible set. -/
theorem exists_card_eq_g (n : ℕ) :
    ∃ A : Finset ℕ, A ⊆ Finset.Icc 0 n ∧ Finset.Icc 0 n ⊆ A + A ∧ #A = g n :=
  Nat.sInf_mem (g_set_nonempty n)

/-- `g n` is at most the size of any admissible set. -/
theorem g_le_card {n : ℕ} {A : Finset ℕ} (hA : A ⊆ Finset.Icc 0 n)
    (hcov : Finset.Icc 0 n ⊆ A + A) : g n ≤ #A :=
  Nat.sInf_le ⟨A, hA, hcov, rfl⟩

/-- `g` is monotone: intersecting a basis for `{0, …, m}` with `{0, …, n}` gives one for
`{0, …, n}`, since both summands of a natural number `x ≤ n` are at most `n`. -/
theorem g_mono : Monotone g := by
  intro n m hnm
  obtain ⟨A, -, hcov, hcard⟩ := exists_card_eq_g m
  rw [← hcard]
  refine (g_le_card (A := A.filter (· ≤ n)) ?_ ?_).trans (Finset.card_filter_le _ _)
  · intro x hx
    rw [Finset.mem_filter] at hx
    exact Finset.mem_Icc.2 ⟨Nat.zero_le x, hx.2⟩
  · intro x hx
    rw [Finset.mem_Icc] at hx
    obtain ⟨a, ha, b, hb, rfl⟩ :=
      Finset.mem_add.1 (hcov (Finset.mem_Icc.2 ⟨Nat.zero_le _, hx.2.trans hnm⟩))
    exact Finset.mem_add.2
      ⟨a, Finset.mem_filter.2 ⟨ha, by omega⟩, b, Finset.mem_filter.2 ⟨hb, by omega⟩, rfl⟩

/-! ### The construction -/

/-- Kohonen's elementary segment `V = [0, t]`. -/
def V (t : ℕ) : Finset ℕ := Finset.range (t + 1)

/-- Kohonen's elementary segment `H = [0, (t), t² - t] = {0, t, …, t² - t}`. -/
def H (t : ℕ) : Finset ℕ := (Finset.range t).image (· * t)

/-- Kohonen's elementary segment `S = [0, (t + 1), t² - 1] = {0, t + 1, …, t² - 1}`. -/
def S (t : ℕ) : Finset ℕ := (Finset.range t).image (· * (t + 1))

/-- The Mrose-type basis of Kohonen's Example 2:
`A = (V + t²·{0, 6, 10}) ∪ (H + t²·{0, 1, 2}) ∪ (S + t²·{3})`. -/
def mroseBasis (t : ℕ) : Finset ℕ :=
  (V t + ({0, 6, 10} : Finset ℕ).image (· * t ^ 2)) ∪
    (H t + ({0, 1, 2} : Finset ℕ).image (· * t ^ 2)) ∪
    (S t + ({3} : Finset ℕ).image (· * t ^ 2))

theorem V_mem {t v c : ℕ} (hv : v ≤ t) (hc : c ∈ ({0, 6, 10} : Finset ℕ)) :
    v + c * t ^ 2 ∈ mroseBasis t :=
  Finset.mem_union_left _ <| Finset.mem_union_left _ <| Finset.mem_add.2
    ⟨v, Finset.mem_range.2 (Nat.lt_succ_of_le hv), c * t ^ 2, Finset.mem_image_of_mem _ hc, rfl⟩

theorem H_mem {t k c : ℕ} (hk : k < t) (hc : c ∈ ({0, 1, 2} : Finset ℕ)) :
    k * t + c * t ^ 2 ∈ mroseBasis t :=
  Finset.mem_union_left _ <| Finset.mem_union_right _ <| Finset.mem_add.2
    ⟨k * t, Finset.mem_image_of_mem _ (Finset.mem_range.2 hk), c * t ^ 2,
      Finset.mem_image_of_mem _ hc, rfl⟩

theorem S_mem {t k : ℕ} (hk : k < t) : k * (t + 1) + 3 * t ^ 2 ∈ mroseBasis t :=
  Finset.mem_union_right _ <| Finset.mem_add.2
    ⟨k * (t + 1), Finset.mem_image_of_mem _ (Finset.mem_range.2 hk), 3 * t ^ 2,
      Finset.mem_image_of_mem _ (Finset.mem_singleton_self 3), rfl⟩

/-- Every element of the basis is at most `10t² + t`. -/
theorem le_of_mem_mroseBasis {t x : ℕ} (hx : x ∈ mroseBasis t) : x ≤ 10 * t ^ 2 + t := by
  simp only [mroseBasis, V, H, S, Finset.mem_union, Finset.mem_add, Finset.mem_image,
    Finset.mem_range, Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with (⟨v, hv, _, ⟨c, hc, rfl⟩, rfl⟩ | ⟨_, ⟨k, hk, rfl⟩, _, ⟨c, hc, rfl⟩, rfl⟩) |
      ⟨_, ⟨k, hk, rfl⟩, _, ⟨c, rfl, rfl⟩, rfl⟩
  · rcases hc with rfl | rfl | rfl <;> nlinarith
  · rcases hc with rfl | rfl | rfl <;> nlinarith
  · nlinarith

/-- `|A| ≤ 3(t + 1) + 3t + t = 7t + 3`. -/
theorem card_mroseBasis_le (t : ℕ) : #(mroseBasis t) ≤ 7 * t + 3 := by
  have hI : #(({0, 6, 10} : Finset ℕ).image (· * t ^ 2)) ≤ 3 :=
    Finset.card_image_le.trans Finset.card_le_three
  have hJ : #(({0, 1, 2} : Finset ℕ).image (· * t ^ 2)) ≤ 3 :=
    Finset.card_image_le.trans Finset.card_le_three
  have hK : #(({3} : Finset ℕ).image (· * t ^ 2)) ≤ 1 :=
    Finset.card_image_le.trans (Finset.card_singleton 3).le
  have hV : #(V t) = t + 1 := Finset.card_range _
  have hH : #(H t) ≤ t := Finset.card_image_le.trans (Finset.card_range t).le
  have hS : #(S t) ≤ t := Finset.card_image_le.trans (Finset.card_range t).le
  unfold mroseBasis
  calc _ ≤ #(V t + ({0, 6, 10} : Finset ℕ).image (· * t ^ 2)) +
        #(H t + ({0, 1, 2} : Finset ℕ).image (· * t ^ 2)) +
        #(S t + ({3} : Finset ℕ).image (· * t ^ 2)) :=
        (Finset.card_union_le _ _).trans (Nat.add_le_add_right (Finset.card_union_le _ _) _)
    _ ≤ (t + 1) * 3 + t * 3 + t * 1 := by
        gcongr
        · exact Finset.card_add_le.trans (hV ▸ Nat.mul_le_mul_left _ hI)
        · exact Finset.card_add_le.trans (Nat.mul_le_mul hH hJ)
        · exact Finset.card_add_le.trans (Nat.mul_le_mul hS hK)
    _ = 7 * t + 3 := by ring

/-- Fact 1 (first half): `V + H ⊇ [0, t² - 1]`. -/
theorem fact1_VH {t r : ℕ} (hr : r < t ^ 2) : ∃ v ≤ t, ∃ k < t, v + k * t = r := by
  have ht : 0 < t := by
    rcases Nat.eq_zero_or_pos t with rfl | h
    · simp at hr
    · exact h
  exact ⟨r % t, (Nat.mod_lt _ ht).le, r / t, Nat.div_lt_of_lt_mul (by rwa [← sq]),
    Nat.mod_add_div' r t⟩

/-- Fact 1 (second half): `V + S ⊇ [0, t² - 1]`. -/
theorem fact1_VS {t r : ℕ} (hr : r < t ^ 2) : ∃ v ≤ t, ∃ k < t, v + k * (t + 1) = r :=
  ⟨r % (t + 1), Nat.lt_succ_iff.1 (Nat.mod_lt _ (Nat.succ_pos t)), r / (t + 1),
    Nat.div_lt_of_lt_mul (by nlinarith), Nat.mod_add_div' r (t + 1)⟩

/-- Fact 2: every `r ∈ [0, t² - 1]` satisfies `r ∈ H + S` or `r + t² ∈ H + S`; i.e. two
consecutive parallelograms `P = H + S` and `P + t²` cover the square `[t², 2t² - 1]`. -/
theorem fact2 {t r : ℕ} (hr : r < t ^ 2) :
    (∃ j < t, ∃ k < t, j * t + k * (t + 1) = r) ∨
      (∃ j < t, ∃ k < t, j * t + k * (t + 1) = r + t ^ 2) := by
  have ht : 0 < t := by
    rcases Nat.eq_zero_or_pos t with rfl | h
    · simp at hr
    · exact h
  have hs : r % t < t := Nat.mod_lt _ ht
  have hq : r / t < t := Nat.div_lt_of_lt_mul (by rwa [← sq])
  have hrq := Nat.mod_add_div' r t
  rcases le_or_gt (r % t) (r / t) with hle | hlt
  · obtain ⟨j, hj⟩ := Nat.exists_eq_add_of_le hle
    left
    refine ⟨j, by omega, r % t, hs, ?_⟩
    rw [hj] at hrq
    linarith
  · obtain ⟨j, hj⟩ := Nat.exists_eq_add_of_le (hs.le.trans (Nat.le_add_left t (r / t)))
    right
    refine ⟨j, by omega, r % t, hs, ?_⟩
    have hj' : (r / t + t) * t = (r % t + j) * t := by rw [hj]
    nlinarith

/-- Squares from `V + H`: `Q + t²·(cv + ch) ⊆ A + A`. -/
theorem VH_cover {t cv ch m r : ℕ} (hcv : cv ∈ ({0, 6, 10} : Finset ℕ))
    (hch : ch ∈ ({0, 1, 2} : Finset ℕ)) (hm : cv + ch = m) (hr : r < t ^ 2) :
    m * t ^ 2 + r ∈ mroseBasis t + mroseBasis t := by
  obtain ⟨v, hv, k, hk, rfl⟩ := fact1_VH hr
  exact Finset.mem_add.2 ⟨v + cv * t ^ 2, V_mem hv hcv, k * t + ch * t ^ 2, H_mem hk hch,
    by subst hm; ring⟩

/-- Squares from `V + S`: `Q + t²·(cv + 3) ⊆ A + A`. -/
theorem VS_cover {t cv m r : ℕ} (hcv : cv ∈ ({0, 6, 10} : Finset ℕ)) (hm : cv + 3 = m)
    (hr : r < t ^ 2) : m * t ^ 2 + r ∈ mroseBasis t + mroseBasis t := by
  obtain ⟨v, hv, k, hk, rfl⟩ := fact1_VS hr
  exact Finset.mem_add.2 ⟨v + cv * t ^ 2, V_mem hv hcv, k * (t + 1) + 3 * t ^ 2, S_mem hk,
    by subst hm; ring⟩

/-- Squares from two consecutive parallelograms `H + S`: `Q + t²·(ch + 4) ⊆ A + A` when
`ch, ch + 1 ∈ {0, 1, 2}`. -/
theorem HS_cover {t ch m r : ℕ} (hch : ch ∈ ({0, 1, 2} : Finset ℕ))
    (hch' : ch + 1 ∈ ({0, 1, 2} : Finset ℕ)) (hm : ch + 4 = m) (hr : r < t ^ 2) :
    m * t ^ 2 + r ∈ mroseBasis t + mroseBasis t := by
  subst hm
  rcases fact2 hr with ⟨j, hj, k, hk, hjk⟩ | ⟨j, hj, k, hk, hjk⟩
  · exact Finset.mem_add.2 ⟨j * t + (ch + 1) * t ^ 2, H_mem hj hch', k * (t + 1) + 3 * t ^ 2,
      S_mem hk, by rw [← hjk]; ring⟩
  · exact Finset.mem_add.2 ⟨j * t + ch * t ^ 2, H_mem hj hch, k * (t + 1) + 3 * t ^ 2,
      S_mem hk, by linarith⟩

/-- The basis covers `[0, 14t² - 1]`. -/
theorem mroseBasis_cover {t n : ℕ} (hn : n < 14 * t ^ 2) :
    n ∈ mroseBasis t + mroseBasis t := by
  have hT : 0 < t ^ 2 := by
    rcases Nat.eq_zero_or_pos (t ^ 2) with h | h
    · rw [h] at hn; omega
    · exact h
  obtain ⟨m, r, hr, rfl⟩ : ∃ m r, r < t ^ 2 ∧ n = m * t ^ 2 + r :=
    ⟨n / t ^ 2, n % t ^ 2, Nat.mod_lt _ hT, (Nat.div_add_mod' n (t ^ 2)).symm⟩
  have hm : m < 14 := by
    by_contra h
    nlinarith [not_lt.1 h]
  interval_cases m
  · exact VH_cover (cv := 0) (ch := 0) (by simp) (by simp) rfl hr
  · exact VH_cover (cv := 0) (ch := 1) (by simp) (by simp) rfl hr
  · exact VH_cover (cv := 0) (ch := 2) (by simp) (by simp) rfl hr
  · exact VS_cover (cv := 0) (by simp) rfl hr
  · exact HS_cover (ch := 0) (by simp) (by simp) rfl hr
  · exact HS_cover (ch := 1) (by simp) (by simp) rfl hr
  · exact VH_cover (cv := 6) (ch := 0) (by simp) (by simp) rfl hr
  · exact VH_cover (cv := 6) (ch := 1) (by simp) (by simp) rfl hr
  · exact VH_cover (cv := 6) (ch := 2) (by simp) (by simp) rfl hr
  · exact VS_cover (cv := 6) (by simp) rfl hr
  · exact VH_cover (cv := 10) (ch := 0) (by simp) (by simp) rfl hr
  · exact VH_cover (cv := 10) (ch := 1) (by simp) (by simp) rfl hr
  · exact VH_cover (cv := 10) (ch := 2) (by simp) (by simp) rfl hr
  · exact VS_cover (cv := 10) (by simp) rfl hr

/-! ### Main results -/

/-- **Mrose's construction** (1979), in the form of Kohonen's Example 2: for every `t ≥ 1` there
is `A ⊆ {0, …, 14t² - 1}` with `|A| ≤ 7t + 7` and `{0, …, 14t² - 1} ⊆ A + A`. -/
theorem mrose_construction (t : ℕ) (ht : 0 < t) :
    ∃ A : Finset ℕ, A ⊆ Finset.Icc 0 (14 * t ^ 2 - 1) ∧ #A ≤ 7 * t + 7 ∧
      Finset.Icc 0 (14 * t ^ 2 - 1) ⊆ A + A := by
  have htt : t ≤ t ^ 2 := Nat.le_self_pow two_ne_zero t
  have hT : 1 ≤ t ^ 2 := Nat.one_le_pow _ _ ht
  refine ⟨mroseBasis t, fun x hx => ?_, (card_mroseBasis_le t).trans (by omega), fun n hn => ?_⟩
  · have := le_of_mem_mroseBasis hx
    exact Finset.mem_Icc.2 ⟨Nat.zero_le x, by omega⟩
  · rw [Finset.mem_Icc] at hn
    exact mroseBasis_cover (by omega)

/-- `g(14t² - 1) ≤ 7t + 7` for every `t ≥ 1`. -/
theorem g_fourteen_mul_sq_sub_one_le (t : ℕ) (ht : 0 < t) : g (14 * t ^ 2 - 1) ≤ 7 * t + 7 := by
  obtain ⟨A, hA, hcard, hcov⟩ := mrose_construction t ht
  exact (g_le_card hA hcov).trans hcard

/-- **Mrose (1979)**: `g(n)² ≤ (7/2 + o(1)) n`, i.e. for every `ε > 0`, eventually
`g(n)² ≤ (7/2 + ε) n`. -/
theorem eventually_g_sq_le {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, (g n : ℝ) ^ 2 ≤ (7 / 2 + ε) * n := by
  obtain ⟨M, hM⟩ := exists_nat_ge (28 / ε)
  refine Filter.eventually_atTop.2 ⟨14 * (M + 1) ^ 2, fun n hn => ?_⟩
  obtain ⟨s, hs⟩ : ∃ s, s = Nat.sqrt (n / 14) := ⟨_, rfl⟩
  have h1 : 14 * s ^ 2 ≤ n := by
    have := Nat.sqrt_le' (n / 14)
    rw [← hs] at this
    omega
  have h2 : n < 14 * (s + 1) ^ 2 := by
    have := Nat.lt_succ_sqrt' (n / 14)
    rw [← hs, Nat.succ_eq_add_one] at this
    omega
  have h3 : M + 1 ≤ s := hs ▸ Nat.le_sqrt'.2 (by omega)
  have hg : g n ≤ 7 * s + 14 :=
    calc g n ≤ g (14 * (s + 1) ^ 2 - 1) := g_mono (by omega)
      _ ≤ 7 * (s + 1) + 7 := g_fourteen_mul_sq_sub_one_le (s + 1) (Nat.succ_pos s)
      _ = 7 * s + 14 := by ring
  have hgR : (g n : ℝ) ≤ 7 * s + 14 := by exact_mod_cast hg
  have h1R : 14 * (s : ℝ) ^ 2 ≤ n := by exact_mod_cast h1
  have hsR : 28 / ε ≤ s := hM.trans (by exact_mod_cast (by omega : M ≤ s))
  have hes : 28 ≤ s * ε := (div_le_iff₀ hε).1 hsR
  have hs1 : (1 : ℝ) ≤ s := by exact_mod_cast (by omega : 1 ≤ s)
  calc (g n : ℝ) ^ 2 ≤ (7 * s + 14) ^ 2 := by gcongr
    _ ≤ (7 / 2 + ε) * n := by
        nlinarith [mul_le_mul_of_nonneg_left h1R hε.le,
          mul_le_mul_of_nonneg_left hes (Nat.cast_nonneg (α := ℝ) s)]

/-- Eventually `g(n) ≤ (39/20) √n` (from `g(n)² ≤ (15/4) n` and `(39/20)² > 15/4`). -/
theorem eventually_g_le : ∀ᶠ n in atTop, (g n : ℝ) ≤ 39 / 20 * √(n : ℝ) := by
  filter_upwards [eventually_g_sq_le (by norm_num : (0 : ℝ) < 1 / 4)] with n hn
  have hsq : (√(n : ℝ)) ^ 2 = n := Real.sq_sqrt (Nat.cast_nonneg n)
  have hpos : 0 ≤ √(n : ℝ) := Real.sqrt_nonneg _
  nlinarith [Nat.cast_nonneg (α := ℝ) (g n)]

/-- `g(n) / √n` does not tend to `2`. -/
theorem not_tendsto_g_div_sqrt : ¬ Tendsto (fun n => (g n : ℝ) / √(n : ℝ)) atTop (𝓝 2) := by
  intro h
  have h1 := h.eventually (lt_mem_nhds (by norm_num : (39 / 20 : ℝ) < 2))
  obtain ⟨n, hn1, hn2, hn3⟩ :=
    (h1.and (eventually_g_le.and (eventually_gt_atTop 0))).exists
  have hpos : 0 < √(n : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hn3)
  rw [lt_div_iff₀ hpos] at hn1
  linarith

/-- **Erdős Problem 791** (Mrose 1979): the answer to "is `g(n) ~ 2 n^{1/2}`?" is no. -/
theorem erdos_791 : ¬ (fun n => (g n : ℝ)) ~[atTop] (fun n => 2 * √(n : ℝ)) := by
  intro h
  have hz : ∀ᶠ n : ℕ in atTop, 2 * √(n : ℝ) ≠ 0 := by
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    have : 0 < √(n : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hn)
    positivity
  have h1 := ((Asymptotics.isEquivalent_iff_tendsto_one hz).1 h).const_mul 2
  rw [mul_one] at h1
  refine not_tendsto_g_div_sqrt (h1.congr fun n => ?_)
  simp only [Pi.div_apply]
  ring

end Erdos791
