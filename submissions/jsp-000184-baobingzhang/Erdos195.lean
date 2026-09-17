import Mathlib

/-!
# Erdős Problem 195: a permutation of `ℤ` with no monotone 5-term arithmetic progression

Erdős and Graham asked for the largest `k` such that every permutation of `ℤ` contains a
monotone `k`-term arithmetic progression. Here a permutation of `ℤ` is an arrangement
`a₀, a₁, a₂, …` of all integers (a bijection `ℕ ≃ ℤ`), and a monotone `k`-term arithmetic
progression is a subsequence `a_{i₁}, …, a_{i_k}` with `i₁ < ⋯ < i_k` whose values form an
increasing or decreasing arithmetic progression. Davis, Entringer, Graham and Simmons [DEGS77]
showed that every such permutation contains a monotone 3-term progression; Geneson [Ge19] proved
`k ≤ 5` and Adenwalla [Ad22, Theorem 1] proved `k ≤ 4` by constructing a permutation of `ℤ` with
no monotone 5-term progression. This file proves Adenwalla's bound:

* `Erdos195.erdos_195.variants.leq_4_bound :
    4 ≥ sSup {k : ℕ | ∀ f : ℕ ≃ ℤ, HasMonotoneAP f k}`
* `Erdos195.erdos_195.variants.leq_5_bound :
    5 ≥ sSup {k : ℕ | ∀ f : ℕ ≃ ℤ, HasMonotoneAP f k}` (Geneson's bound, as a corollary)

The key statement is `Erdos195.not_hasMonotoneAP_perm`: an explicit `perm : ℕ ≃ ℤ` has no
monotone `k`-term progression for any `k ≥ 5`. Hence every `k` in the set above is at most `4`.
So the set is bounded above, its supremum is its largest element, and the bound is not an
artifact of the convention `sSup s = 0` for sets `s ⊆ ℕ` that are not bounded above.

The definitions `List.IsAPOfLengthWith`, `List.IsAPOfLength` and `HasMonotoneAP` are copied
verbatim from Google DeepMind's formal-conjectures project
(`FormalConjecturesForMathlib/Combinatorics/AP/Basic.lean`, Apache-2.0), and the statements of
`erdos_195.variants.leq_5_bound` and `erdos_195.variants.leq_4_bound` (category "research
solved") are copied verbatim from `FormalConjectures/ErdosProblems/195.lean` of the same project,
with the same namespace and names. `HasMonotoneAP f k` asks for a strictly increasing list of
positions whose values under `f` are `a, a + d, …, a + (k - 1) d` or the same list reversed; a
negative `d` gives a decreasing progression, and `d = 0` cannot occur for `k ≥ 2` because `f` is
injective.

## The permutation

For `i ≥ 1` let `Xᵢ` be the set of integers in `[-8^i, -8^(i-1) - 1] ∪ [8^(i-1), 8^i - 1]`, and
let `X₀ = {-1, 0}`. Order `X₀` as `-1, 0`. For `i ≥ 1` every `x ∈ Xᵢ` satisfies `⌊x / 8⌋ ∈ Xᵢ₋₁`,
and `Xᵢ` is ordered first by the residue `x mod 8` and then by the position of `⌊x / 8⌋` in
`Xᵢ₋₁`. For odd `i` the residues come in the order `0, 4, 2, 6, 1, 5, 3, 7` (3-bit reversal),
for even `i` in the reverse order `7, 3, 5, 1, 6, 2, 4, 0`. The permutation lists
`X₀, X₁, X₂, …` block by block. (`rank k x` is the position of `x` inside `X_k`, `level x` is the
block index and `key x = 16 ^ level x + rank (level x) x`; `perm` enumerates `ℤ` in increasing
order of `key`.)

For `i ≥ 1` these blocks and orders are exactly Adenwalla's: `X₁` is
`-8, -4, 4, -6, 2, -2, 6, -7, 1, -3, 5, -5, 3, 7`, and `X_{i+1}` is the concatenation of
`8 Xᵢ + r` over the residues `r` in the order above. Adenwalla's permutation is
`0, X₁, -1, X₂, X₃, …`; here the two extra terms are put first as `-1, 0`, which removes the
separate case for them in the proof. As a numerical sanity check (not used in the proof), both
versions were checked by computer to have no monotone 5-term progression among their first
`2 · 8^5` terms.

## Proof

* **Finite residue checks** (`finA_aux`, `finB_aux`, `tau_double_aux`, by `decide`). With `τ` the
  residue order of the current level and `τ'` that of the next level, there are no residues `r`
  and `e ≢ 0 (mod 8)` with `τ(r) < τ(r + e) < τ(r + 2e)`, and none with `τ(r) < τ(r + e)` and
  `τ'(r + 2e) < τ'(r + 3e)`.
* **No increasing 3-term progression in one level** (`no_three_AP_rank`, induction on the level,
  for all integers). If `8 ∣ d` the three terms share a residue and their quotients by `8` form
  a progression one level down; otherwise consecutive residues differ, and the residue order
  gives a forbidden pattern.
* **No 4-term progression with two terms in `Xᵢ` and two in `Xᵢ₊₁`** (`no_four_AP_rank`). The same
  induction; the case `8 ∣ d` descends from level `i + 1` to level `i`, and at the bottom level
  the only candidate is `-d, 0, d, 2d`, excluded by `tau_double_aux`.
* **Size argument** (`no_five_AP_key`, Adenwalla's Cases 1 and 2). Let `a₁, …, a₅` appear in this
  order with common difference `d` and `a₂ ∈ Xᵢ`. Then `|a₁|, |a₂| ≤ 8^i`, so `|d| ≤ 2 · 8^i` and
  all terms lie in `X₀ ∪ ⋯ ∪ Xᵢ₊₁`. If `a₃ ∉ Xᵢ` then `a₃, a₄, a₅ ∈ Xᵢ₊₁`, a 3-term
  progression. If `a₃ ∈ Xᵢ` then `a₄ ∉ Xᵢ`, so `a₄, a₅ ∈ Xᵢ₊₁`, and `a₂, a₃, a₄, a₅` is a
  4-term progression split between `Xᵢ` and `Xᵢ₊₁`.
* **The bijection** (`perm`). `key` is injective, so `ℤ` is order-isomorphic to the infinite
  set `range key ⊆ ℕ`, which Mathlib identifies with `ℕ` (`Nat.Subtype.orderIsoOfNat`).
* **Conclusion.** A monotone progression of length `k ≥ 5` in `perm` gives five consecutive terms
  `a, a + d, …, a + 4d` whose keys increase, which is impossible.

## What remains open

Erdős Problem 195 itself (`erdos_195` in formal-conjectures) is open: the answer is `3` or `4`,
depending on whether some permutation of `ℤ` avoids monotone 4-term arithmetic progressions.
The lower bound `k ≥ 3` of [DEGS77] is not formalized here, and neither is Adenwalla's
doubly infinite construction [Ad22, Theorem 2], which concerns a different notion of
permutation.

## References

* [Ad22] Adenwalla, S., _Avoiding Monotone Arithmetic Progressions in Permutations of Integers_.
  arXiv:2211.04451 (2022; v7, 2024).
* [DEGS77] Davis, J. A., Entringer, R. C., Graham, R. L. and Simmons, G. J., _On permutations
  containing no long arithmetic progressions_. Acta Arith. 34 (1977), 81-90.
* [Ge19] Geneson, J., _Forbidden arithmetic progressions in permutations of subsets of the
  integers_. Discrete Math. (2019), 1489-1491. arXiv:1803.06334.
* [erdosproblems.com/195](https://www.erdosproblems.com/195)
-/

-- Copied verbatim from formal-conjectures,
-- `FormalConjecturesForMathlib/Combinatorics/AP/Basic.lean`.
variable {α : Type*} [AddCommMonoid α]

/--
A list version of `Set.IsAPOfLengthWith`. Useful when order preservation is required, for example
when considering images under arbitrary functions.
-/
def List.IsAPOfLengthWith (s : List α) (l : ℕ) (a d : α) : Prop :=
  s = (List.range l).map (fun n ↦ a + n • d) ∨ s = (List.range l).reverse.map (fun n ↦ a + n • d)

/--
A list version of `Set.IsAPOfLength`. Useful when order preservation is required, for example
when considering images under arbitrary functions.
-/
def List.IsAPOfLength (s : List α) (l : ℕ) : Prop :=
  ∃ a d : α, s.IsAPOfLengthWith l a d

/--
A function `f : β → α` has a monotone `k`-term arithmetic progression if there exists a choice
of indices `b 1 < b 2 < ... < b k` such that the subsequence `f (b i)` forms an increasing or
decreasing arithmetic progression of length `k`.
-/
def HasMonotoneAP {β : Type*} [Preorder β] (f : β → α) (k : ℕ) : Prop :=
  ∃ l : List β, (l.map f).IsAPOfLength k ∧ l.Pairwise (· < ·)

namespace Erdos195

/-! ### Residues modulo `8` and their orders -/

/-- Reversal of the three binary digits of `r < 8`. -/
def bitrev (r : ℕ) : ℕ := 4 * (r % 2) + 2 * (r / 2 % 2) + r / 4 % 2

/-- Position of the residue `r` in the residue order of level `k`: `0, 4, 2, 6, 1, 5, 3, 7` for
odd `k` and the reverse order for even `k`. -/
def tau (k r : ℕ) : ℕ := if k % 2 = 1 then bitrev r else 7 - bitrev r

/-- The residue of `x` modulo `8`, as a natural number. -/
def res (x : ℤ) : ℕ := (x % 8).toNat

theorem res_lt (x : ℤ) : res x < 8 := by unfold res; omega

theorem res_add1 (x d : ℤ) : res (x + d) = (res x + res d) % 8 := by unfold res; omega

theorem res_add2 (x d : ℤ) : res (x + 2 * d) = (res x + 2 * res d) % 8 := by unfold res; omega

theorem res_add3 (x d : ℤ) : res (x + 3 * d) = (res x + 3 * res d) % 8 := by unfold res; omega

theorem res_eq01 (x d : ℤ) : res x = res (x + d) ↔ d % 8 = 0 := by unfold res; omega

theorem res_eq12 (x d : ℤ) : res (x + d) = res (x + 2 * d) ↔ d % 8 = 0 := by unfold res; omega

theorem res_eq23 (x d : ℤ) : res (x + 2 * d) = res (x + 3 * d) ↔ d % 8 = 0 := by
  unfold res; omega

theorem tau_mod (k r : ℕ) : tau k r = tau (k % 2) r := by simp [tau]

theorem tau_le (k r : ℕ) : tau k r ≤ 7 := by
  unfold tau bitrev; split_ifs <;> omega

theorem tau_inj_aux : ∀ p < 2, ∀ r < 8, ∀ s < 8, tau p r = tau p s → r = s := by decide

theorem tau_inj {k r s : ℕ} (hr : r < 8) (hs : s < 8) (h : tau k r = tau k s) : r = s := by
  rw [tau_mod, tau_mod k s] at h
  exact tau_inj_aux _ (Nat.mod_lt _ (by norm_num)) r hr s hs h

/-- The residue orders contain no increasing 3-term progression with nonzero difference. -/
theorem finA_aux : ∀ p < 2, ∀ r < 8, ∀ e < 8, e ≠ 0 →
    ¬ (tau p r < tau p ((r + e) % 8) ∧ tau p ((r + e) % 8) < tau p ((r + 2 * e) % 8)) := by
  decide

/-- No 4-term progression mod `8` with nonzero difference has its first two terms increasing in
one residue order and its last two terms increasing in the other one. -/
theorem finB_aux : ∀ p < 2, ∀ r < 8, ∀ e < 8, e ≠ 0 →
    ¬ (tau p r < tau p ((r + e) % 8) ∧
      tau (p + 1) ((r + 2 * e) % 8) < tau (p + 1) ((r + 3 * e) % 8)) := by
  decide

/-- In the odd residue order, doubling a nonzero residue moves it strictly earlier. -/
theorem tau_double_aux : ∀ r < 8, r ≠ 0 → tau 1 ((2 * r) % 8) < tau 1 r := by decide

theorem finA {k : ℕ} {x d : ℤ} (hd : d % 8 ≠ 0) :
    ¬ (tau k (res x) < tau k (res (x + d)) ∧ tau k (res (x + d)) < tau k (res (x + 2 * d))) := by
  rw [res_add1, res_add2, tau_mod, tau_mod k, tau_mod k]
  exact finA_aux _ (Nat.mod_lt _ (by norm_num)) _ (res_lt x) _ (res_lt d) (by unfold res; omega)

theorem finB {k : ℕ} {x d : ℤ} (hd : d % 8 ≠ 0) :
    ¬ (tau k (res x) < tau k (res (x + d)) ∧
      tau (k + 1) (res (x + 2 * d)) < tau (k + 1) (res (x + 3 * d))) := by
  rw [res_add1, res_add2, res_add3, tau_mod, tau_mod k, tau_mod (k + 1), tau_mod (k + 1)]
  rcases Nat.mod_two_eq_zero_or_one k with hk | hk
  · have h1 : (k + 1) % 2 = 0 + 1 := by omega
    rw [hk, h1]
    exact finB_aux 0 (by norm_num) _ (res_lt x) _ (res_lt d) (by unfold res; omega)
  · have h1 : (k + 1) % 2 = 0 := by omega
    have hA := finB_aux 1 (by norm_num) _ (res_lt x) _ (res_lt d) (by unfold res; omega)
    rw [hk, h1]
    simpa [tau] using hA

/-! ### The order inside a level -/

/-- `rank k x` is the position of `x` in the level-`k` order: `-1` before `0` at level `0`, and
at level `k + 1` first by the residue order of `x mod 8`, then by the rank of `⌊x / 8⌋`. It is
defined for all integers and is injective on `[-8^k, 8^k)` (`rank_inj`). -/
def rank : ℕ → ℤ → ℕ
  | 0, x => if x = 0 then 1 else 0
  | k + 1, x => tau (k + 1) (res x) * (2 * 8 ^ k) + rank k (x / 8)

theorem rank_lt (k : ℕ) (x : ℤ) : rank k x < 2 * 8 ^ k := by
  induction k generalizing x with
  | zero => simp only [rank]; split_ifs <;> norm_num
  | succ k ih =>
    simp only [rank]
    have h1 := tau_le (k + 1) (res x)
    have h2 := ih (x / 8)
    rw [pow_succ]
    nlinarith

theorem lex_lt {a b c e M : ℕ} (he : e < M) (h : a * M + b < c * M + e) :
    a < c ∨ (a = c ∧ b < e) := by
  rcases lt_trichotomy a c with hac | rfl | hac
  · exact Or.inl hac
  · exact Or.inr ⟨rfl, by omega⟩
  · exfalso
    have : (c + 1) * M ≤ a * M := Nat.mul_le_mul_right _ hac
    nlinarith

theorem lex_eq {a b c e M : ℕ} (hb : b < M) (he : e < M) (h : a * M + b = c * M + e) :
    a = c ∧ b = e := by
  rcases lt_trichotomy a c with hac | rfl | hac
  · exfalso
    have : (a + 1) * M ≤ c * M := Nat.mul_le_mul_right _ hac
    nlinarith
  · exact ⟨rfl, by omega⟩
  · exfalso
    have : (c + 1) * M ≤ a * M := Nat.mul_le_mul_right _ hac
    nlinarith

theorem rank_succ_lt {k : ℕ} {x y : ℤ} (h : rank (k + 1) x < rank (k + 1) y) :
    tau (k + 1) (res x) < tau (k + 1) (res y) ∨
      (res x = res y ∧ rank k (x / 8) < rank k (y / 8)) := by
  simp only [rank] at h
  rcases lex_lt (rank_lt k _) h with h' | ⟨h1, h2⟩
  · exact Or.inl h'
  · exact Or.inr ⟨tau_inj (res_lt x) (res_lt y) h1, h2⟩

/-- No level order contains an increasing 3-term arithmetic progression. -/
theorem no_three_AP_rank (k : ℕ) :
    ∀ x d : ℤ, ¬ (rank k x < rank k (x + d) ∧ rank k (x + d) < rank k (x + 2 * d)) := by
  induction k with
  | zero => intro x d; simp only [rank]; split_ifs <;> omega
  | succ k ih =>
    rintro x d ⟨h1, h2⟩
    have r1 := res_eq01 x d
    have r2 := res_eq12 x d
    rcases rank_succ_lt h1 with h1 | ⟨e1, h1⟩ <;> rcases rank_succ_lt h2 with h2 | ⟨e2, h2⟩
    · have hd : d % 8 ≠ 0 := fun hd => by rw [r1.2 hd] at h1; exact lt_irrefl _ h1
      exact finA hd ⟨h1, h2⟩
    · rw [r1.2 (r2.1 e2)] at h1; exact lt_irrefl _ h1
    · rw [r2.2 (r1.1 e1)] at h2; exact lt_irrefl _ h2
    · have hd := r1.1 e1
      have q1 : (x + d) / 8 = x / 8 + d / 8 := by omega
      have q2 : (x + 2 * d) / 8 = x / 8 + 2 * (d / 8) := by omega
      rw [q1] at h1 h2; rw [q2] at h2
      exact ih (x / 8) (d / 8) ⟨h1, h2⟩

/-- No 4-term arithmetic progression has its first two terms increasing in the level-`k` order
and its last two terms increasing in the level-`(k + 1)` order. -/
theorem no_four_AP_rank (k : ℕ) :
    ∀ x d : ℤ,
      ¬ (rank k x < rank k (x + d) ∧ rank (k + 1) (x + 2 * d) < rank (k + 1) (x + 3 * d)) := by
  induction k with
  | zero =>
    rintro x d ⟨h1, h2⟩
    simp only [rank, zero_add, pow_zero, mul_one] at h1 h2
    split_ifs at h1 with ha hb <;> try omega
    have e2 : x + 2 * d = d := by omega
    have e3 : x + 3 * d = 2 * d := by omega
    rw [e2, e3] at h2
    have hr2 : res (2 * d) = (2 * res d) % 8 := by unfold res; omega
    rw [hr2] at h2
    by_cases hd : res d = 0
    · have hd8 : d / 8 ≠ 0 := by unfold res at hd; omega
      have h28 : 2 * d / 8 ≠ 0 := by unfold res at hd; omega
      simp [hd8, h28, hd] at h2
    · have := tau_double_aux (res d) (res_lt d) hd
      split_ifs at h2 <;> omega
  | succ k ih =>
    rintro x d ⟨h1, h2⟩
    have r1 := res_eq01 x d
    have r3 := res_eq23 x d
    rcases rank_succ_lt h1 with h1 | ⟨e1, h1⟩ <;> rcases rank_succ_lt h2 with h2 | ⟨e2, h2⟩
    · have hd : d % 8 ≠ 0 := fun hd => by rw [r1.2 hd] at h1; exact lt_irrefl _ h1
      exact finB hd ⟨h1, h2⟩
    · rw [r1.2 (r3.1 e2)] at h1; exact lt_irrefl _ h1
    · rw [r3.2 (r1.1 e1)] at h2; exact lt_irrefl _ h2
    · have hd := r1.1 e1
      have q1 : (x + d) / 8 = x / 8 + d / 8 := by omega
      have q2 : (x + 2 * d) / 8 = x / 8 + 2 * (d / 8) := by omega
      have q3 : (x + 3 * d) / 8 = x / 8 + 3 * (d / 8) := by omega
      rw [q1] at h1; rw [q2, q3] at h2
      exact ih (x / 8) (d / 8) ⟨h1, h2⟩

/-! ### Levels and the key -/

/-- `Win k x`: `x` lies in `[-8^k, 8^k)`, the union of the blocks `X₀, …, X_k`. -/
abbrev Win (k : ℕ) (x : ℤ) : Prop := -(8 : ℤ) ^ k ≤ x ∧ x < 8 ^ k

theorem win_exists (x : ℤ) : ∃ k, Win k x := by
  refine ⟨x.natAbs, ?_⟩
  have h : x.natAbs < 8 ^ x.natAbs := Nat.lt_pow_self (by norm_num)
  have h' : ((x.natAbs : ℕ) : ℤ) < (8 : ℤ) ^ x.natAbs := by exact_mod_cast h
  constructor <;> omega

/-- The block index of `x`: `x ∈ X_(level x)`. -/
noncomputable def level (x : ℤ) : ℕ := Nat.find (win_exists x)

theorem win_mono {i j : ℕ} {x : ℤ} (hij : i ≤ j) (h : Win i x) : Win j x := by
  have : (8 : ℤ) ^ i ≤ 8 ^ j := pow_le_pow_right₀ (by norm_num) hij
  exact ⟨by linarith [h.1], by linarith [h.2]⟩

theorem level_le_iff {x : ℤ} {i : ℕ} : level x ≤ i ↔ Win i x := by
  unfold level
  rw [Nat.find_le_iff]
  exact ⟨fun ⟨m, hm, h⟩ => win_mono hm h, fun h => ⟨i, le_rfl, h⟩⟩

theorem win_level (x : ℤ) : Win (level x) x := level_le_iff.1 le_rfl

theorem win_succ {k : ℕ} {x : ℤ} : Win (k + 1) x ↔ Win k (x / 8) := by
  simp only [Win, pow_succ]
  constructor <;> intro h <;> constructor <;> omega

theorem rank_inj (k : ℕ) : ∀ x y : ℤ, Win k x → Win k y → rank k x = rank k y → x = y := by
  induction k with
  | zero =>
    intro x y hx hy h
    simp only [rank] at h
    simp only [Win, pow_zero] at hx hy
    split_ifs at h <;> omega
  | succ k ih =>
    intro x y hx hy h
    simp only [rank] at h
    obtain ⟨h1, h2⟩ := lex_eq (rank_lt k _) (rank_lt k _) h
    have e1 := tau_inj (res_lt x) (res_lt y) h1
    have e2 := ih _ _ (win_succ.1 hx) (win_succ.1 hy) h2
    unfold res at e1
    omega

/-- The position key: block index first, then the rank inside the block. -/
noncomputable def key (x : ℤ) : ℕ := 16 ^ level x + rank (level x) x

theorem key_lt_of_level_lt {x y : ℤ} (h : level x < level y) : key x < key y := by
  unfold key
  have h1 := rank_lt (level x) x
  have h2 : 8 ^ level x ≤ 16 ^ level x := Nat.pow_le_pow_left (by norm_num) _
  have h3 : 16 ^ (level x + 1) ≤ 16 ^ level y := Nat.pow_le_pow_right (by norm_num) h
  rw [pow_succ] at h3
  omega

theorem level_le_of_key_lt {x y : ℤ} (h : key x < key y) : level x ≤ level y :=
  not_lt.1 fun h' => lt_asymm h (key_lt_of_level_lt h')

theorem rank_lt_of_key_lt {x y : ℤ} (h : key x < key y) (hb : level x = level y) :
    rank (level y) x < rank (level y) y := by
  unfold key at h
  rw [hb] at h
  omega

theorem key_inj : Function.Injective key := by
  intro x y h
  have hb : level x = level y := by
    rcases lt_trichotomy (level x) (level y) with h' | h' | h'
    · exact absurd h (key_lt_of_level_lt h').ne
    · exact h'
    · exact absurd h (key_lt_of_level_lt h').ne'
  unfold key at h
  rw [hb] at h
  exact rank_inj _ x y (hb ▸ win_level x) (win_level y) (by omega)

/-- The key order has no increasing 5-term arithmetic progression. -/
theorem no_five_AP_key (a d : ℤ) :
    ¬ (key a < key (a + d) ∧ key (a + d) < key (a + 2 * d) ∧
      key (a + 2 * d) < key (a + 3 * d) ∧ key (a + 3 * d) < key (a + 4 * d)) := by
  rintro ⟨h0, h1, h2, h3⟩
  have b0 := level_le_of_key_lt h0
  have b1 := level_le_of_key_lt h1
  have b2 := level_le_of_key_lt h2
  have b3 := level_le_of_key_lt h3
  obtain ⟨sa1, sa2⟩ : Win (level (a + d)) a := level_le_iff.1 b0
  obtain ⟨s11, s12⟩ : Win (level (a + d)) (a + d) := win_level _
  have p8 : (8 : ℤ) ^ (level (a + d) + 1) = 8 ^ level (a + d) * 8 := pow_succ _ _
  by_cases hb2 : level (a + 2 * d) = level (a + d)
  · -- `a + d` and `a + 2d` lie in the same block
    obtain ⟨s21, s22⟩ : Win (level (a + d)) (a + 2 * d) := level_le_iff.1 hb2.le
    have s3 : Win (level (a + d) + 1) (a + 3 * d) := by
      simp only [Win, p8]; constructor <;> omega
    have s4 : Win (level (a + d) + 1) (a + 4 * d) := by
      simp only [Win, p8]; constructor <;> omega
    have c3 := level_le_iff.2 s3
    have c4 := level_le_iff.2 s4
    have q1 := rank_lt_of_key_lt h1 hb2.symm
    rw [hb2] at q1
    have e2 : a + d + d = a + 2 * d := by ring
    have e3 : a + d + 2 * d = a + 3 * d := by ring
    by_cases hb3 : level (a + 3 * d) = level (a + d)
    · have q2 := rank_lt_of_key_lt h2 (hb2.trans hb3.symm)
      rw [hb3] at q2
      have := no_three_AP_rank (level (a + d)) (a + d) d
      rw [e2, e3] at this
      exact this ⟨q1, q2⟩
    · have hb3' : level (a + 3 * d) = level (a + d) + 1 := by omega
      have hb4 : level (a + 4 * d) = level (a + d) + 1 := by omega
      have q3 := rank_lt_of_key_lt h3 (hb3'.trans hb4.symm)
      rw [hb4] at q3
      have := no_four_AP_rank (level (a + d)) (a + d) d
      have e4 : a + d + 3 * d = a + 4 * d := by ring
      rw [e2, e3, e4] at this
      exact this ⟨q1, q3⟩
  · -- `a + 2d`, `a + 3d`, `a + 4d` lie in the next block
    have s2 : Win (level (a + d) + 1) (a + 2 * d) := by
      simp only [Win, p8]; constructor <;> omega
    have s3 : Win (level (a + d) + 1) (a + 3 * d) := by
      simp only [Win, p8]; constructor <;> omega
    have s4 : Win (level (a + d) + 1) (a + 4 * d) := by
      simp only [Win, p8]; constructor <;> omega
    have c2 := level_le_iff.2 s2
    have c3 := level_le_iff.2 s3
    have c4 := level_le_iff.2 s4
    have hb2' : level (a + 2 * d) = level (a + d) + 1 := by omega
    have hb3 : level (a + 3 * d) = level (a + d) + 1 := by omega
    have hb4 : level (a + 4 * d) = level (a + d) + 1 := by omega
    have q2 := rank_lt_of_key_lt h2 (hb2'.trans hb3.symm)
    have q3 := rank_lt_of_key_lt h3 (hb3.trans hb4.symm)
    rw [hb3] at q2
    rw [hb4] at q3
    have := no_three_AP_rank (level (a + d) + 1) (a + 2 * d) d
    have e3 : a + 2 * d + d = a + 3 * d := by ring
    have e4 : a + 2 * d + 2 * d = a + 4 * d := by ring
    rw [e3, e4] at this
    exact this ⟨q2, q3⟩

/-! ### The permutation -/

instance : Infinite (Set.range key) := (Set.infinite_range_of_injective key_inj).to_subtype

/-- The permutation `ℕ ≃ ℤ`: its `n`-th term is the integer with the `n`-th smallest key. -/
noncomputable def perm : ℕ ≃ ℤ :=
  (Nat.Subtype.orderIsoOfNat (Set.range key)).toEquiv.trans (Equiv.ofInjective key key_inj).symm

theorem key_perm (n : ℕ) : key (perm n) = Nat.Subtype.orderIsoOfNat (Set.range key) n := by
  simp [perm, Equiv.apply_ofInjective_symm]

theorem key_perm_lt {m n : ℕ} (h : m < n) : key (perm m) < key (perm n) := by
  rw [key_perm, key_perm]
  exact (Nat.Subtype.orderIsoOfNat (Set.range key)).strictMono h

/-- Adenwalla's theorem: `perm` has no monotone `k`-term arithmetic progression for `k ≥ 5`. -/
theorem not_hasMonotoneAP_perm {k : ℕ} (hk : 5 ≤ k) : ¬ HasMonotoneAP perm k := by
  rintro ⟨l, ⟨a, d, hAP⟩, hl⟩
  have hlen : l.length = k := by
    rcases hAP with h | h <;> simpa using congrArg List.length h
  obtain ⟨a', d', hval⟩ : ∃ a' d' : ℤ, ∀ j (hj : j < l.length), perm l[j] = a' + j * d' := by
    rcases hAP with h | h
    · refine ⟨a, d, fun j hj => ?_⟩
      have := List.getElem_of_eq h (by simpa using hj)
      simpa using this
    · refine ⟨a + (k - 1 : ℕ) * d, -d, fun j hj => ?_⟩
      have := List.getElem_of_eq h (by simpa using hj)
      simp only [List.getElem_map, List.getElem_reverse, List.getElem_range, List.length_range,
        nsmul_eq_mul] at this
      rw [this, show ((k - 1 - j : ℕ) : ℤ) = (k : ℤ) - 1 - j by omega,
        show ((k - 1 : ℕ) : ℤ) = (k : ℤ) - 1 by omega]
      ring
  have hp := List.pairwise_iff_getElem.1 hl
  have t : ∀ j (hj : j + 1 < l.length),
      key (a' + j * d') < key (a' + (j + 1 : ℕ) * d') := by
    intro j hj
    have := key_perm_lt (hp j (j + 1) (by omega) hj (by omega))
    rwa [hval j (by omega), hval (j + 1) hj] at this
  have t0 := t 0 (by omega)
  have t1 := t 1 (by omega)
  have t2 := t 2 (by omega)
  have t3 := t 3 (by omega)
  norm_num at t0 t1 t2 t3
  exact no_five_AP_key a' d' ⟨t0, t1, t2, t3⟩

theorem exists_perm_not_hasMonotoneAP_five : ∃ f : ℕ ≃ ℤ, ¬ HasMonotoneAP f 5 :=
  ⟨perm, not_hasMonotoneAP_perm le_rfl⟩

/-- Every `k` such that all permutations of `ℤ` contain a monotone `k`-term progression is at
most `4`; in particular this set of natural numbers is bounded above. -/
theorem le_four_of_mem {k : ℕ} (hk : k ∈ {k : ℕ | ∀ f : ℕ ≃ ℤ, HasMonotoneAP f k}) : k ≤ 4 := by
  by_contra h
  exact not_hasMonotoneAP_perm (by omega) (hk perm)

/-- For contrast, the enumeration `0, -1, 1, -2, 2, …` does contain a monotone 5-term
progression (`0, 1, 2, 3, 4` at positions `0, 2, 4, 6, 8`). -/
theorem hasMonotoneAP_intEquivNat_symm : HasMonotoneAP Equiv.intEquivNat.symm 5 :=
  ⟨[0, 2, 4, 6, 8], ⟨0, 1, Or.inl (by decide)⟩, by decide⟩

theorem erdos_195.variants.leq_5_bound :
    5 ≥ sSup {k : ℕ | ∀ f : ℕ ≃ ℤ, HasMonotoneAP f k} :=
  csSup_le' fun _ hk => (le_four_of_mem hk).trans (by norm_num)

theorem erdos_195.variants.leq_4_bound :
    4 ≥ sSup {k : ℕ | ∀ f : ℕ ≃ ℤ, HasMonotoneAP f k} :=
  csSup_le' fun _ hk => le_four_of_mem hk

end Erdos195
