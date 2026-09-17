import Mathlib

/-!
# Erdős Problem 176: Spencer's exact value of `N(k,1)`, and `N(k,2)` for even `k`

Erdős Problem 176 ([Er63d], [ErGr80], https://www.erdosproblems.com/176) reads:

> Let `N(k,ℓ)` be the minimal `N` such that for any `f : {1, …, N} → {-1, 1}` there must
> exist a `k`-term arithmetic progression `P` such that `|∑_{n ∈ P} f(n)| ≥ ℓ`. Find good
> upper bounds for `N(k,ℓ)`. Is it true that for any `c > 0` there exists some `C > 1` such
> that `N(k,ck) ≤ C^k`? What about `N(k,2) ≤ C^k` or `N(k,√k) ≤ C^k`?

The page records that Spencer [Sp73] proved: if `k = 2^t m` with `m` odd, then
`N(k,1) = 2^t (k-1) + 1`. Adenwalla observed in the forum thread of the problem that a sum of
`k` signs has the parity of `k`, so `N(k,2) = N(k,1)` for even `k`.

This file proves both statements, for every `k ≥ 1`:

* `discrepancyAPNumber_one`: `N(k,1) = 2^t (k-1) + 1` whenever `k = 2^t m` with `m` odd;
  `discrepancyAPNumber_one_padicValNat` states the same with `t = v₂(k)`;
* `discrepancyAPNumber_two_eq_one`: `N(k,2) = N(k,1)` for even `k ≥ 2`, and
  `discrepancyAPNumber_two`: `N(k,2) = 2^t (k-1) + 1` when `k = 2^t m`, `m` odd, `t ≥ 1`.

The questions of the problem itself (`N(k,ck) ≤ C^k`, `N(k,2) ≤ C^k` for odd `k`,
`N(k,√k) ≤ C^k`) are not addressed.

## Definitions and faithfulness

`Set.IsAPOfLengthWith` and `Set.IsAPOfLength` are copied from formal-conjectures
(`FormalConjecturesForMathlib/Combinatorics/AP/Basic.lean`, Apache-2.0). `ForcesDiscrepancy`
and `discrepancyAPNumber` are copied from the statement-only formal-conjectures pull request
#4693 (`FormalConjectures/ErdosProblems/176.lean`, open at the time of writing). Their
docstrings here are our own.

* `ForcesDiscrepancy N k ℓ`: for every `f : Finset.Icc 1 N → ℤ` with values in `{-1, 1}`
  there is a finset `P` of elements of `{1, …, N}` whose underlying set of naturals is an
  arithmetic progression with exactly `k` elements (`Set.IsAPOfLength`, which includes
  `ENat.card = k`, so a constant progression only counts when `k = 1`), such that
  `ℓ ≤ |∑_{n ∈ P} f n|`. The sum is computed in `ℤ` and compared in `ℝ`.
* `discrepancyAPNumber k ℓ = sInf {N | ForcesDiscrepancy N k ℓ}`, taken in `ℕ∞`, so it is
  `⊤` (not `0`) when no `N` works.

For the proofs we use the elementary form `ForcesDiscrepancyAP N k ℓ`: for every `f : ℕ → ℤ`
that takes values in `{-1, 1}` on `{1, …, N}` there are `a ≥ 1`, `d ≥ 1` with
`a + (k-1) d ≤ N` and `ℓ ≤ |∑_{i < k} f (a + i d)|`. For `k ≥ 1` the two are equivalent
(`forcesDiscrepancy_iff`), so every result is stated for the formal-conjectures quantity
`discrepancyAPNumber`.

## Non-vacuity

`isLeast_forcesDiscrepancy_one` shows that `2^t (k-1) + 1` is the least element of
`{N | ForcesDiscrepancy N k 1}`, and `forcesDiscrepancy_one_iff` shows that
`ForcesDiscrepancy N k 1` holds exactly for `N ≥ 2^t (k-1) + 1`. Both directions are proved
outright: the upper bound (`forcesDiscrepancyAP_one`) for every colouring, and the lower bound
through one explicit colouring (`exists_balanced_colouring`) under which every `k`-term
progression in `{1, …, 2^t (k-1)}` has sum exactly `0`.

## Proof

* **Upper bound** (`forcesDiscrepancyAP_one`). Let `N = 2^t (k-1) + 1` and suppose every
  `k`-term progression in `{1, …, N}` has sum `0` (for `k` signs, `|s| < 1` means `s = 0`).
  Comparing the progressions `a, …, a+k-1` and `a+1, …, a+k` gives `f(a + k) = f(a)` whenever
  `a + k ≤ N`. The progression `1, 1 + 2^t, …, 1 + (k-1) 2^t` ends at `N`. Its terms with
  indices `i` and `i + m` differ by `m 2^t = k`, so its sum splits into `2^t` equal blocks of
  length `m`: it is `2^t · s`, where `s` is a sum of `m` signs. As `m` is odd, `s` is odd, so the
  sum is not `0`.
* **Lower bound** (`exists_balanced_colouring`). If `t = 0` there is no `k`-term progression in
  `{1, …, k-1}`. If `t ≥ 1`, let `h = k/2 = 2^(t-1) m` and colour `n` by `(-1)^⌊n/h⌋`
  (`col`), so shifting `n` by `h` flips the sign and shifting by `2h = k` keeps it. A progression
  in `{1, …, 2^t (k-1)}` has difference `d < 2^t`, so `d = 2^u e` with `u ≤ t-1` and `e` odd.
  With `s = 2^(t-1-u) m` one has `s d = e h`, so moving `s` steps along the progression flips
  every sign. The sequence `i ↦ col (a + i d)` has period `k`, so shifting the `k` indices by `s`
  does not change the sum. Hence the sum equals its own negative and is `0`
  (`sum_col_eq_zero`).
* **Parity** (`forcesDiscrepancyAP_two_iff`). For even `k` a sum of `k` signs is even
  (`even_sum_iff`), so `|s| ≥ 1` iff `|s| ≥ 2`.

The source [Sp73] was not available to us. The argument above was written for this
formalization, and the formula was also checked by exhaustive search for `k ≤ 8`, for both
`ℓ = 1` and (for even `k`) `ℓ = 2`.

## Main results

* `Erdos176.discrepancyAPNumber_one :
    Odd m → k = 2 ^ t * m → discrepancyAPNumber k 1 = ↑(2 ^ t * (k - 1) + 1)`
* `Erdos176.discrepancyAPNumber_one_padicValNat :
    k ≠ 0 → discrepancyAPNumber k 1 = ↑(2 ^ padicValNat 2 k * (k - 1) + 1)`
* `Erdos176.discrepancyAPNumber_two_eq_one :
    Even k → k ≠ 0 → discrepancyAPNumber k 2 = discrepancyAPNumber k 1`
* `Erdos176.discrepancyAPNumber_two :
    1 ≤ t → Odd m → k = 2 ^ t * m → discrepancyAPNumber k 2 = ↑(2 ^ t * (k - 1) + 1)`
* `Erdos176.forcesDiscrepancy_one_iff`, `Erdos176.isLeast_forcesDiscrepancy_one`,
  `Erdos176.exists_balanced_colouring`, `Erdos176.forcesDiscrepancy_iff`.

## References

* [Er63d] Erdős, P., _On combinatorial questions connected with a theorem of Ramsey and
  van der Waerden_. Mat. Lapok 14 (1963), 29-37.
* [ErGr80] Erdős, P. and Graham, R., _Old and new problems and results in combinatorial number
  theory_. Monographies de L'Enseignement Mathématique 28 (1980).
* [Sp73] Spencer, J., _Problems 185_ (solution). Canad. Math. Bull. (1973); cited on
  erdosproblems.com as "Bull. Canad. Math. Soc. (1973), 185".
* formal-conjectures pull request #4693 (statement only):
  https://github.com/google-deepmind/formal-conjectures/pull/4693
* [erdosproblems.com/176](https://www.erdosproblems.com/176) and its forum thread.
-/

/-! ## Arithmetic progressions (copied from formal-conjectures) -/

section APDefs

variable {α : Type*} [AddCommMonoid α]

/-- `s` is the set `{a, a + d, …, a + (l - 1) d}` (all `a + n • d` with `n < l`) and has exactly
`l` elements. -/
def Set.IsAPOfLengthWith (s : Set α) (l : ℕ∞) (a d : α) : Prop :=
  ENat.card s = l ∧ s = {a + n • d | (n : ℕ) (_ : n < l)}

/-- `s` is an arithmetic progression with exactly `l` elements. -/
def Set.IsAPOfLength (s : Set α) (l : ℕ∞) : Prop :=
  ∃ a d : α, s.IsAPOfLengthWith l a d

end APDefs

open Finset

namespace Erdos176

/-! ## The problem (definitions copied from formal-conjectures PR #4693) -/

/-- Every colouring of `{1, …, N}` by `{-1, 1}` has a `k`-term arithmetic progression on which
the absolute value of the sum is at least `ℓ`. -/
def ForcesDiscrepancy (N k : ℕ) (ℓ : ℝ) : Prop :=
  ∀ f : Finset.Icc 1 N → ℤ, (∀ n, f n = -1 ∨ f n = 1) →
    ∃ P : Finset (Finset.Icc 1 N),
      ({(n : ℕ) | n ∈ P} : Set ℕ).IsAPOfLength k ∧
        ℓ ≤ |((∑ n ∈ P, f n : ℤ) : ℝ)|

/-- `N(k,ℓ)`: the least `N` with `ForcesDiscrepancy N k ℓ`, or `⊤` if there is none. -/
noncomputable def discrepancyAPNumber (k : ℕ) (ℓ : ℝ) : ℕ∞ :=
  sInf ((fun N : ℕ ↦ (N : ℕ∞)) '' {N : ℕ | ForcesDiscrepancy N k ℓ})

/-! ## An elementary equivalent form -/

/-- `ForcesDiscrepancy` with the progression given by its first term `a ≥ 1` and its difference
`d ≥ 1`, and the colouring given as a function on `ℕ` that is `±1` on `{1, …, N}`. -/
def ForcesDiscrepancyAP (N k : ℕ) (ℓ : ℝ) : Prop :=
  ∀ f : ℕ → ℤ, (∀ n ∈ Icc 1 N, f n = 1 ∨ f n = -1) →
    ∃ a d : ℕ, 1 ≤ a ∧ 1 ≤ d ∧ a + (k - 1) * d ≤ N ∧
      ℓ ≤ |((∑ i ∈ range k, f (a + i * d) : ℤ) : ℝ)|

theorem ForcesDiscrepancyAP.mono {N N' k : ℕ} {ℓ : ℝ} (h : ForcesDiscrepancyAP N k ℓ)
    (hN : N ≤ N') : ForcesDiscrepancyAP N' k ℓ := by
  intro f hf
  obtain ⟨a, d, ha, hd, hle, hS⟩ :=
    h f fun n hn => hf n (by simp only [mem_Icc] at hn ⊢; omega)
  exact ⟨a, d, ha, hd, hle.trans hN, hS⟩

/-- A sum over `P : Finset (Icc 1 N)` is the sum over the image of `P` in `ℕ`. -/
theorem sum_eq_of_map_eq {N : ℕ} (P : Finset (Icc 1 N)) (T : Finset ℕ)
    (hP : P.map (Function.Embedding.subtype _) = T) (g : ℕ → ℤ) :
    ∑ n ∈ P, g n = ∑ x ∈ T, g x := by
  rw [← hP, sum_map]
  rfl

/-- For `k ≥ 1`, `ForcesDiscrepancy` and `ForcesDiscrepancyAP` agree. -/
theorem forcesDiscrepancy_iff {N k : ℕ} (hk : 1 ≤ k) (ℓ : ℝ) :
    ForcesDiscrepancy N k ℓ ↔ ForcesDiscrepancyAP N k ℓ := by
  constructor
  · intro h g hg
    obtain ⟨P, ⟨a, d, hcard, hS⟩, hsum⟩ := h (fun n => g n) fun n => (hg n n.2).symm
    have hS' : ∀ x, (∃ n ∈ P, (n : ℕ) = x) ↔ ∃ i < k, a + i * d = x := by
      intro x
      have := Set.ext_iff.1 hS x
      simpa [smul_eq_mul, Nat.cast_lt] using this
    have hPT : P.map (Function.Embedding.subtype _) = (range k).image fun i => a + i * d := by
      ext x
      simpa [Finset.mem_map, Finset.mem_image] using hS' x
    have hmem : ∀ i < k, a + i * d ∈ Icc 1 N := by
      intro i hi
      obtain ⟨n, -, hn⟩ := (hS' _).2 ⟨i, hi, rfl⟩
      rw [← hn]
      exact n.2
    have hd : k = 1 ∨ 1 ≤ d := by
      rcases Nat.eq_zero_or_pos d with rfl | hd
      · left
        have h1 : {x | ∃ n ∈ P, (n : ℕ) = x} = ({a} : Set ℕ) := by
          ext x
          simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff, hS', mul_zero, add_zero]
          exact ⟨fun ⟨_, _, h⟩ => h.symm, fun h => ⟨0, hk, h.symm⟩⟩
        rw [h1] at hcard
        simp at hcard
        exact_mod_cast hcard.symm
      · exact Or.inr hd
    have hinj : Set.InjOn (fun i => a + i * d) (range k) := by
      intro i hi j hj hij
      simp only [coe_range, Set.mem_Iio] at hi hj
      simp only at hij
      rcases hd with rfl | hd
      · omega
      · exact Nat.eq_of_mul_eq_mul_right hd (by omega)
    have hsum' : ∑ n ∈ P, g n = ∑ i ∈ range k, g (a + i * d) := by
      rw [sum_eq_of_map_eq P _ hPT, sum_image hinj]
    obtain ⟨d', hd', hle', hsum''⟩ : ∃ d', 1 ≤ d' ∧ (k - 1) * d' = (k - 1) * d ∧
        ∑ i ∈ range k, g (a + i * d') = ∑ i ∈ range k, g (a + i * d) := by
      rcases hd with rfl | hd
      · exact ⟨1, le_rfl, by simp, by simp⟩
      · exact ⟨d, hd, rfl, rfl⟩
    have h0 := hmem 0 (by omega)
    have hlast := hmem (k - 1) (by omega)
    simp only [mem_Icc] at h0 hlast
    refine ⟨a, d', by omega, hd', by omega, ?_⟩
    rw [hsum'', ← hsum']
    exact hsum
  · intro h f hf
    classical
    let g : ℕ → ℤ := fun n => if hn : n ∈ Icc 1 N then f ⟨n, hn⟩ else 1
    have hg : ∀ n ∈ Icc 1 N, g n = 1 ∨ g n = -1 := by
      intro n hn
      simp only [g, hn, ↓reduceDIte]
      exact (hf _).symm
    obtain ⟨a, d, ha, hd, hle, hsum⟩ := h g hg
    have hmem : ∀ i < k, a + i * d ∈ Icc 1 N := by
      intro i hi
      have : i * d ≤ (k - 1) * d := Nat.mul_le_mul_right _ (by omega)
      simp only [mem_Icc]
      omega
    let T : Finset ℕ := (range k).image fun i => a + i * d
    let P : Finset (Icc 1 N) := univ.filter fun n => (n : ℕ) ∈ T
    have hPT : P.map (Function.Embedding.subtype _) = T := by
      ext x
      simp only [P, T, mem_map, mem_filter, mem_univ, true_and, Function.Embedding.coe_subtype]
      constructor
      · rintro ⟨n, hn, rfl⟩
        exact hn
      · intro hx
        obtain ⟨i, hi, rfl⟩ := mem_image.1 hx
        exact ⟨⟨_, hmem i (mem_range.1 hi)⟩, hx, rfl⟩
    have hinj : Set.InjOn (fun i => a + i * d) (range k) := by
      intro i _ j _ hij
      exact Nat.eq_of_mul_eq_mul_right hd (by simp only at hij; omega)
    have hset : {x | ∃ n ∈ P, (n : ℕ) = x} = (T : Set ℕ) := by
      rw [← hPT]
      ext x
      simp
    refine ⟨P, ⟨a, d, ?_, ?_⟩, ?_⟩
    · rw [hset]
      change Set.encard _ = _
      rw [Set.encard_coe_eq_coe_finsetCard, card_image_of_injOn hinj, card_range]
    · rw [hset]
      ext x
      simp [T, smul_eq_mul, Nat.cast_lt]
    · have : ∑ n ∈ P, f n = ∑ n ∈ P, g n := by
        refine sum_congr rfl fun n _ => ?_
        simp only [g]
        split_ifs with hn
        · rfl
        · exact absurd n.2 hn
      rw [this, sum_eq_of_map_eq P T hPT, sum_image hinj]
      exact hsum

/-- If `M` is the least `N` with `ForcesDiscrepancy N k ℓ`, then `N(k,ℓ) = M`. -/
theorem discrepancyAPNumber_eq_of_isLeast {k M : ℕ} {ℓ : ℝ}
    (h : IsLeast {N | ForcesDiscrepancy N k ℓ} M) : discrepancyAPNumber k ℓ = M :=
  (Nat.mono_cast.map_isLeast h).csInf_eq

/-! ## Signs and sums -/

/-- A sum of `k` signs is even iff `k` is even. -/
theorem even_sum_iff (g : ℕ → ℤ) (k : ℕ) (hg : ∀ i < k, g i = 1 ∨ g i = -1) :
    Even (∑ i ∈ range k, g i) ↔ Even k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [sum_range_succ, Nat.even_add_one, ← ih fun i hi => hg i (by omega)]
    rcases hg k (by omega) with h | h <;> rw [h] <;> simp [Int.even_add, parity_simps]

theorem one_le_abs_cast_iff (S : ℤ) : (1 : ℝ) ≤ |(S : ℝ)| ↔ S ≠ 0 := by
  rw [← Int.cast_abs]
  constructor
  · rintro h rfl
    norm_num at h
  · intro h
    exact_mod_cast Int.one_le_abs h

/-! ## Upper bound: `N(k,1) ≤ 2^t (k-1) + 1` -/

/-- **Upper bound.** If `k = 2^t m` with `m` odd, every `±1` colouring of
`{1, …, 2^t (k-1) + 1}` has a `k`-term progression with nonzero sum. -/
theorem forcesDiscrepancyAP_one {k t m : ℕ} (hm : Odd m) (hk : k = 2 ^ t * m) :
    ForcesDiscrepancyAP (2 ^ t * (k - 1) + 1) k 1 := by
  intro f hf
  have hm0 : 0 < m := hm.pos
  have hP : 0 < 2 ^ t := by positivity
  have hk0 : 0 < k := by rw [hk]; positivity
  by_contra hcon
  push Not at hcon
  -- every `k`-term progression in `{1, …, N}` has sum `0`
  have hz : ∀ a d, 1 ≤ a → 1 ≤ d → a + (k - 1) * d ≤ 2 ^ t * (k - 1) + 1 →
      ∑ i ∈ range k, f (a + i * d) = 0 := by
    intro a d ha hd hle
    by_contra hne
    exact absurd (hcon a d ha hd hle) (not_lt.2 ((one_le_abs_cast_iff _).2 hne))
  -- hence `f` is `k`-periodic on `{1, …, N}`
  have hper : ∀ a, 1 ≤ a → a + k ≤ 2 ^ t * (k - 1) + 1 → f (a + k) = f a := by
    intro a ha hak
    obtain ⟨k', hk'⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    have h1 := hz a 1 ha le_rfl (by omega)
    have h2 := hz (a + 1) 1 (by omega) le_rfl (by omega)
    rw [hk'] at h1 h2 ⊢
    have e1 := sum_range_succ (fun i => f (a + i * 1)) (k' + 1)
    have e2 := sum_range_succ' (fun i => f (a + i * 1)) (k' + 1)
    have e3 : ∑ i ∈ range (k' + 1), f (a + (i + 1) * 1) =
        ∑ i ∈ range (k' + 1), f (a + 1 + i * 1) :=
      sum_congr rfl fun i _ => by congr 1; ring
    rw [e3, h2] at e2
    rw [h1] at e1
    simp only [mul_one, add_zero, zero_add] at e1 e2
    linarith
  have hperj : ∀ j a, 1 ≤ a → a + j * k ≤ 2 ^ t * (k - 1) + 1 → f (a + j * k) = f a := by
    intro j
    induction j with
    | zero => intro a _ _; simp
    | succ j ih =>
      intro a ha hle
      have e : a + (j + 1) * k = a + j * k + k := by ring
      rw [e] at hle ⊢
      rw [hper _ (by omega) hle, ih a ha (by omega)]
  -- the progression `1, 1 + 2^t, …` splits into blocks of length `m` with equal sums
  have hblock : ∀ j, j ≤ 2 ^ t → ∑ i ∈ range (j * m), f (1 + i * 2 ^ t) =
      j * ∑ i ∈ range m, f (1 + i * 2 ^ t) := by
    intro j
    induction j with
    | zero => intro _; simp
    | succ j ih =>
      intro hj
      rw [add_one_mul j m, sum_range_add, ih (by omega)]
      have : ∑ x ∈ range m, f (1 + (j * m + x) * 2 ^ t) =
          ∑ i ∈ range m, f (1 + i * 2 ^ t) := by
        refine sum_congr rfl fun x hx => ?_
        rw [mem_range] at hx
        have e : 1 + (j * m + x) * 2 ^ t = 1 + x * 2 ^ t + j * k := by rw [hk]; ring
        rw [e]
        apply hperj j (1 + x * 2 ^ t) (Nat.le_add_right 1 _)
        have h1 : (j + 1) * m ≤ 2 ^ t * m := Nat.mul_le_mul_right m hj
        have h2 : j * m + x ≤ k - 1 := by rw [hk]; rw [add_one_mul] at h1; omega
        have h3 : 2 ^ t * (j * m + x) ≤ 2 ^ t * (k - 1) := Nat.mul_le_mul_left _ h2
        have h4 : x * 2 ^ t + j * k = 2 ^ t * (j * m + x) := by rw [hk]; ring
        omega
      rw [this]
      push_cast
      ring
  -- a block is a sum of `m` signs with `m` odd, so it is not `0`
  have hT : ∑ i ∈ range m, f (1 + i * 2 ^ t) ≠ 0 := by
    intro h0
    have hmem : ∀ i < m, f (1 + i * 2 ^ t) = 1 ∨ f (1 + i * 2 ^ t) = -1 := by
      intro i hi
      apply hf
      have h1 : m ≤ k := by rw [hk]; exact Nat.le_mul_of_pos_left m hP
      have h2 : i * 2 ^ t ≤ (k - 1) * 2 ^ t := Nat.mul_le_mul_right _ (by omega)
      rw [mul_comm (k - 1)] at h2
      simp only [mem_Icc]
      omega
    have := (even_sum_iff (fun i => f (1 + i * 2 ^ t)) m hmem).1 (by rw [h0]; exact ⟨0, rfl⟩)
    exact (Nat.not_even_iff_odd.2 hm) this
  have hS := hz 1 (2 ^ t) le_rfl hP (by rw [mul_comm]; omega)
  rw [hk, hblock (2 ^ t) le_rfl] at hS
  exact hT ((mul_eq_zero.1 hS).resolve_left (by positivity))

/-! ## Lower bound: an explicit colouring of `{1, …, 2^t (k-1)}` -/

/-- A shift of the summation window does not change the sum of a `p`-periodic sequence. -/
theorem sum_range_shift (G : ℕ → ℤ) (p : ℕ) (hG : ∀ i, G (i + p) = G i) (s : ℕ) :
    ∑ i ∈ range p, G (i + s) = ∑ i ∈ range p, G i := by
  induction s with
  | zero => simp
  | succ s ih =>
    have h1 := sum_range_succ (fun i => G (i + s)) p
    have h2 := sum_range_succ' (fun i => G (i + s)) p
    have h3 : G (p + s) = G s := by rw [add_comm]; exact hG s
    have e : ∑ i ∈ range p, G (i + (s + 1)) = ∑ i ∈ range p, G (i + 1 + s) :=
      sum_congr rfl fun i _ => by rw [add_right_comm, add_assoc]
    simp only [zero_add] at h1 h2
    rw [e, ← ih]
    linarith

/-- The colouring `n ↦ (-1)^⌊n/h⌋`: alternating blocks of length `h`. -/
def col (h n : ℕ) : ℤ := (-1) ^ (n / h)

theorem col_add_mul {h : ℕ} (hh : 0 < h) (n j : ℕ) :
    col h (n + j * h) = (-1) ^ j * col h n := by
  unfold col
  rw [Nat.add_mul_div_right _ _ hh, pow_add, mul_comm]

/-- If `s d = e h` with `e` odd, every `2h`-term progression with difference `d` has sum `0`
under `col h`. -/
theorem sum_col_eq_zero {h : ℕ} (hh : 0 < h) (a d s e : ℕ) (hsd : s * d = e * h)
    (he : Odd e) : ∑ i ∈ range (2 * h), col h (a + i * d) = 0 := by
  let G : ℕ → ℤ := fun i => col h (a + i * d)
  have hper : ∀ i, G (i + 2 * h) = G i := by
    intro i
    have : a + (i + 2 * h) * d = a + i * d + (2 * d) * h := by ring
    simp only [G]
    rw [this, col_add_mul hh, Even.neg_one_pow ⟨d, by ring⟩, one_mul]
  have hanti : ∀ i, G (i + s) = - G i := by
    intro i
    have : a + (i + s) * d = a + i * d + e * h := by rw [← hsd]; ring
    simp only [G]
    rw [this, col_add_mul hh, he.neg_one_pow, neg_one_mul]
  have h1 := sum_range_shift G (2 * h) hper s
  simp only [hanti, sum_neg_distrib] at h1
  change ∑ i ∈ range (2 * h), G i = 0
  linarith

/-- **Lower bound.** If `k = 2^t m` with `m` odd, some `±1` colouring gives sum exactly `0` on
every `k`-term progression in `{1, …, 2^t (k-1)}`. -/
theorem exists_balanced_colouring {k t m : ℕ} (hm : Odd m) (hk : k = 2 ^ t * m) :
    ∃ f : ℕ → ℤ, (∀ n, f n = 1 ∨ f n = -1) ∧
      ∀ a d : ℕ, 1 ≤ a → 1 ≤ d → a + (k - 1) * d ≤ 2 ^ t * (k - 1) →
        ∑ i ∈ range k, f (a + i * d) = 0 := by
  have hm0 : 0 < m := hm.pos
  rcases t with _ | v
  · refine ⟨fun _ => 1, fun _ => Or.inl rfl, fun a d ha hd hle => ?_⟩
    exfalso
    have : k - 1 ≤ (k - 1) * d := Nat.le_mul_of_pos_right _ hd
    simp only [pow_zero, one_mul] at hle hk
    omega
  · have hpos : 0 < 2 ^ v * m := by positivity
    have hk2 : k = 2 * (2 ^ v * m) := by rw [hk]; ring
    refine ⟨col (2 ^ v * m), fun n => neg_one_pow_eq_or ℤ _, fun a d ha hd hle => ?_⟩
    have hdlt : d < 2 ^ (v + 1) := by
      by_contra hc
      push Not at hc
      have : (k - 1) * 2 ^ (v + 1) ≤ (k - 1) * d := Nat.mul_le_mul_left _ hc
      rw [mul_comm] at this
      omega
    obtain ⟨u, e, he, rfl⟩ := Nat.exists_eq_two_pow_mul_odd (n := d) (by omega)
    have hu : u ≤ v := by
      have h1 : 2 ^ u < 2 ^ (v + 1) := lt_of_le_of_lt (Nat.le_mul_of_pos_right _ he.pos) hdlt
      have := (Nat.pow_lt_pow_iff_right (by norm_num)).1 h1
      omega
    rw [hk2]
    apply sum_col_eq_zero hpos a _ (2 ^ (v - u) * m) e _ he
    calc 2 ^ (v - u) * m * (2 ^ u * e) = (2 ^ (v - u) * 2 ^ u) * m * e := by ring
      _ = 2 ^ v * m * e := by rw [← pow_add, Nat.sub_add_cancel hu]
      _ = e * (2 ^ v * m) := by ring

theorem not_forcesDiscrepancyAP_one {k t m : ℕ} (hm : Odd m) (hk : k = 2 ^ t * m) :
    ¬ ForcesDiscrepancyAP (2 ^ t * (k - 1)) k 1 := by
  obtain ⟨f, hf, hsum⟩ := exists_balanced_colouring hm hk
  intro h
  obtain ⟨a, d, ha, hd, hle, hS⟩ := h f fun n _ => hf n
  rw [hsum a d ha hd hle] at hS
  norm_num at hS

/-! ## Spencer's theorem -/

theorem forcesDiscrepancyAP_one_iff {k t m : ℕ} (hm : Odd m) (hk : k = 2 ^ t * m) (N : ℕ) :
    ForcesDiscrepancyAP N k 1 ↔ 2 ^ t * (k - 1) + 1 ≤ N := by
  refine ⟨fun h => ?_, fun h => (forcesDiscrepancyAP_one hm hk).mono h⟩
  by_contra hlt
  exact not_forcesDiscrepancyAP_one hm hk (h.mono (by omega))

/-- `ForcesDiscrepancy N k 1` holds exactly for `N ≥ 2^t (k-1) + 1`. -/
theorem forcesDiscrepancy_one_iff {k t m : ℕ} (hm : Odd m) (hk : k = 2 ^ t * m) (N : ℕ) :
    ForcesDiscrepancy N k 1 ↔ 2 ^ t * (k - 1) + 1 ≤ N := by
  have hk1 : 1 ≤ k := by
    rw [hk]; exact Nat.one_le_iff_ne_zero.2 (mul_ne_zero (by positivity) hm.pos.ne')
  exact (forcesDiscrepancy_iff hk1 1).trans (forcesDiscrepancyAP_one_iff hm hk N)

theorem isLeast_forcesDiscrepancy_one {k t m : ℕ} (hm : Odd m) (hk : k = 2 ^ t * m) :
    IsLeast {N | ForcesDiscrepancy N k 1} (2 ^ t * (k - 1) + 1) :=
  ⟨(forcesDiscrepancy_one_iff hm hk _).2 le_rfl,
    fun _ hN => (forcesDiscrepancy_one_iff hm hk _).1 hN⟩

/-- **Spencer [Sp73].** If `k = 2^t m` with `m` odd, then `N(k,1) = 2^t (k-1) + 1`. -/
theorem discrepancyAPNumber_one {k t m : ℕ} (hm : Odd m) (hk : k = 2 ^ t * m) :
    discrepancyAPNumber k 1 = (2 ^ t * (k - 1) + 1 : ℕ) :=
  discrepancyAPNumber_eq_of_isLeast (isLeast_forcesDiscrepancy_one hm hk)

/-- **Spencer [Sp73]**, with `t` the `2`-adic valuation of `k`. -/
theorem discrepancyAPNumber_one_padicValNat {k : ℕ} (hk : k ≠ 0) :
    discrepancyAPNumber k 1 = (2 ^ padicValNat 2 k * (k - 1) + 1 : ℕ) := by
  obtain ⟨t, m, hm, rfl⟩ := Nat.exists_eq_two_pow_mul_odd hk
  rw [discrepancyAPNumber_one hm rfl, padicValNat.mul (by positivity) hm.pos.ne',
    padicValNat.prime_pow, padicValNat.eq_zero_of_not_dvd hm.not_two_dvd_nat, add_zero]

/-! ## `N(k,2) = N(k,1)` for even `k` -/

theorem forcesDiscrepancyAP_two_iff {k : ℕ} (hk : Even k) (N : ℕ) :
    ForcesDiscrepancyAP N k 2 ↔ ForcesDiscrepancyAP N k 1 := by
  constructor
  · intro h f hf
    obtain ⟨a, d, ha, hd, hle, hS⟩ := h f hf
    exact ⟨a, d, ha, hd, hle, le_trans (by norm_num) hS⟩
  · intro h f hf
    obtain ⟨a, d, ha, hd, hle, hS⟩ := h f hf
    refine ⟨a, d, ha, hd, hle, ?_⟩
    have hne := (one_le_abs_cast_iff _).1 hS
    have hev : Even (∑ i ∈ range k, f (a + i * d)) := by
      refine (even_sum_iff _ k fun i hi => hf _ ?_).2 hk
      have : i * d ≤ (k - 1) * d := Nat.mul_le_mul_right _ (by omega)
      simp only [mem_Icc]
      omega
    obtain ⟨r, hr⟩ := hev
    have h2 : (2 : ℤ) ≤ |∑ i ∈ range k, f (a + i * d)| := by
      rw [hr] at hne ⊢
      rcases abs_cases (r + r) with ⟨h1, _⟩ | ⟨h1, _⟩ <;> omega
    rw [← Int.cast_abs]
    exact_mod_cast h2

/-- **Parity.** For even `k ≥ 2`, `N(k,2) = N(k,1)`. -/
theorem discrepancyAPNumber_two_eq_one {k : ℕ} (hk : Even k) (hk0 : k ≠ 0) :
    discrepancyAPNumber k 2 = discrepancyAPNumber k 1 := by
  have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.2 hk0
  unfold discrepancyAPNumber
  congr 2
  ext N
  simp only [Set.mem_ofPred_eq]
  rw [forcesDiscrepancy_iff hk1, forcesDiscrepancy_iff hk1]
  exact forcesDiscrepancyAP_two_iff hk N

/-- If `k = 2^t m` with `m` odd and `t ≥ 1`, then `N(k,2) = 2^t (k-1) + 1`. -/
theorem discrepancyAPNumber_two {k t m : ℕ} (ht : 1 ≤ t) (hm : Odd m) (hk : k = 2 ^ t * m) :
    discrepancyAPNumber k 2 = (2 ^ t * (k - 1) + 1 : ℕ) := by
  have hev : Even k := hk ▸ (Nat.even_pow.2 ⟨even_two, by omega⟩).mul_right m
  have hk0 : k ≠ 0 := by rw [hk]; exact mul_ne_zero (by positivity) hm.pos.ne'
  rw [discrepancyAPNumber_two_eq_one hev hk0, discrepancyAPNumber_one hm hk]

/-! ## Sample values -/

example : discrepancyAPNumber 3 1 = 3 := by
  rw [discrepancyAPNumber_one (t := 0) (m := 3) ⟨1, by norm_num⟩ (by norm_num)]
  norm_num

example : discrepancyAPNumber 4 1 = 13 := by
  rw [discrepancyAPNumber_one (t := 2) (m := 1) odd_one (by norm_num)]
  norm_num

example : discrepancyAPNumber 12 2 = 45 := by
  rw [discrepancyAPNumber_two (t := 2) (m := 3) (by norm_num) ⟨1, by norm_num⟩ (by norm_num)]
  norm_num

end Erdos176
