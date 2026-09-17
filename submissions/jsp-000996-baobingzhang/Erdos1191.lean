import Mathlib

/-!
# Erdős Problem 1191: Erdős's bound `liminf |A ∩ [1, x]| (log x)^{1/2} / x^{1/2} < ∞`

Erdős Problem 1191 (erdosproblems.com/1191, a \$1000 problem from [Er80, p. 98]) asks:

> Let `A ⊂ ℕ` be an infinite Sidon set. Is it true that
> `liminf_{x → ∞} |A ∩ [1, x]| / x^{1/2} · (log x)^{1/2} = 0`?
> Does there exist an infinite Sidon set `A` such that
> `liminf_{x → ∞} |A ∩ [1, x]| / x^{1/2} · (log x)^c > 0` for some `c > 0`?

Both questions are open. The problem page records the known result: "Erdős proved (see for
example [HaRo66]) that if `A` is an infinite Sidon set then
`liminf_{x → ∞} |A ∩ [1, x]| / x^{1/2} · (log x)^{1/2} ≤ c` for some constant `c > 0`."
This file proves that theorem of Erdős, in the normalisation of the problem page:

* `erdos_1191.variants.erdos_upper_bound`: for every infinite Sidon set `A ⊆ ℕ`,
  `liminf_{x → ∞} ENNReal.ofReal (|A ∩ [1, x]| / x^(1/2) · (log x)^(1/2)) < ⊤`.
  The liminf is taken in `ℝ≥0∞`, where it always exists, so finiteness is a genuine statement
  (it fails, for example, if the expression tends to `∞`);
* `erdos_1191.variants.erdos_upper_bound_explicit`: the same in explicit form,
  `∃ C, ∃ᶠ x in atTop, |A ∩ [1, x]| ≤ C √x / √(log x)` (with `C = 200`).

Here `x` ranges over `ℕ`. For an upper bound this loses nothing: the liminf over real `x → ∞`
takes infima over a larger set of points, so it is at most the liminf along `ℕ`.

`IsSidon` is copied verbatim from Google DeepMind's formal-conjectures project,
`FormalConjecturesForMathlib/Combinatorics/Basic.lean` (Apache-2.0). The same theorem, in the
`[0, N)` normalisation, is formal-conjectures' `erdos_158.variants.isSidon'`; this file is
self-contained and repeats that proof.

References: [HaRo66] H. Halberstam and K. F. Roth, *Sequences*, Vol. I (1966), Ch. II;
[Er80] P. Erdős, *A survey of problems in combinatorial number theory* (1980).

## Proof (Erdős's argument)

Write `A(M) = #(A ∩ [0, M))`. The core estimate `exists_ncard_mul_sqrt_log_le` says: if
`L = log N ≥ 2`, some `M ≥ N` has `A(M) √(log M) ≤ 100 √M`. Suppose instead
`A(M) √(log M) > 100 √M` for all `M ≥ N`.

* **Blocks.** Split `[0, N²)` into the blocks `[ℓN, (ℓ+1)N)`, `ℓ < N`, with `F_ℓ` elements of `A`.
  For ordered pairs `a ≠ b` of elements of `A` in a common block, the differences `b - a` are
  pairwise distinct (if `b - a = d - c` then `b + c = d + a`, and the Sidon property forces
  `(a, b) = (c, d)`) and lie in `(-N, N)`. So `∑ F_ℓ (F_ℓ - 1) ≤ 2N`, and since
  `F² ≤ 2F(F - 1) + 1`, `∑_{ℓ<N} F_ℓ² ≤ 5N` (`sum_sq_card_block_le`).
* **Upper bound.** With `w_ℓ = 1/√(ℓ+1)` and `T = ∑_{ℓ<N} F_ℓ w_ℓ`, Cauchy–Schwarz and
  `H_N ≤ 1 + log N` give `T² ≤ 5N(1 + L)`.
* **Lower bound.** Summation by parts (`abel_identity`) with `A(jN) = ∑_{ℓ<j} F_ℓ` gives
  `T ≥ ∑_{j<N} A((j+1)N) (w_j - w_{j+1})`. For `j < N`, `log((j+1)N) ≤ 2L`, so the assumption at
  `M = (j+1)N ≥ N` gives `√2 √L · A((j+1)N) > 100 √(j+1) √N`; together with
  `w_j - w_{j+1} ≥ 1/(2 √(j+1) (j+2))` (`inv_sqrt_sub_inv_sqrt_ge`) each term is at least
  `50 √N / (j+2)` after multiplying by `√2 √L`. As `∑_{j<N} 1/(j+2) ≥ L - 1`,
  `50 √N (L - 1) ≤ √2 √L · T`.
* **Contradiction.** Squaring, `2500 N (L-1)² ≤ 2L T² ≤ 10 N L (1 + L)`, i.e.
  `250 (L-1)² ≤ L (1 + L)`, which is false for `L ≥ 2`.

To pass to `[1, x]`, take `x = M - 1 ≥ 2`: `|A ∩ [1, x]| ≤ A(M)`, `log x ≤ log M` and
`√M ≤ 2 √x`, so `|A ∩ [1, x]| √(log x) ≤ 200 √x`. Since `log N → ∞`, this happens for arbitrarily
large `x`, which gives both statements.

## What remains open

Both questions of Erdős Problem 1191 remain open: whether the liminf above is always `0`, and
whether some infinite Sidon set has `liminf |A ∩ [1, x]| x^{-1/2} (log x)^c > 0` for some `c > 0`.
Only Erdős's upper bound (`< ∞`) is proved here.
-/

open Filter Real

section IsSidonDef

-- Copied verbatim from formal-conjectures,
-- `FormalConjecturesForMathlib/Combinatorics/Basic.lean` (Apache-2.0).
variable {α : Type*} [AddCommMonoid α]

/-- A Sidon set is a set, such that such that all pairwise sums of elements are distinct apart from
coincidences forced by the commutativity of addition. -/
def IsSidon (A : Set α) : Prop := ∀ᵉ (i₁ ∈ A) (j₁ ∈ A) (i₂ ∈ A) (j₂ ∈ A),
  i₁ + i₂ = j₁ + j₂ → (i₁ = j₁ ∧ i₂ = j₂) ∨ (i₁ = j₂ ∧ i₂ = j₁)

end IsSidonDef

namespace Erdos1191

open Classical in
/-- The elements of `A` in the block `[ℓN, (ℓ+1)N)`, for `ℓ < N`. -/
noncomputable def block (A : Set ℕ) (N ℓ : ℕ) : Finset ℕ :=
  {a ∈ Finset.range (N * N) | a ∈ A ∧ a / N = ℓ}

open Classical in
/-- Sidon: the differences `b - a` of ordered pairs `a ≠ b` lying in a common block are pairwise
distinct and lie in `(-N, N)`, so `∑ F_ℓ (F_ℓ - 1) < 2N`, whence `∑ F_ℓ² ≤ 5N`. -/
theorem sum_sq_card_block_le {A : Set ℕ} (hA : IsSidon A) {N : ℕ} (hN : 0 < N) :
    ∑ ℓ ∈ Finset.range N, (block A N ℓ).card ^ 2 ≤ 5 * N := by
  set P : Finset (ℕ × ℕ) :=
    {p ∈ ({a ∈ Finset.range (N * N) | a ∈ A} : Finset ℕ).offDiag | p.1 / N = p.2 / N} with hP
  have h1 : P.card = ∑ ℓ ∈ Finset.range N,
      ((block A N ℓ).card * (block A N ℓ).card - (block A N ℓ).card) := by
    rw [Finset.card_eq_sum_card_fiberwise (f := fun p : ℕ × ℕ => p.1 / N) (t := Finset.range N)]
    · refine Finset.sum_congr rfl fun ℓ _ => ?_
      rw [← Finset.offDiag_card]
      congr 1
      ext ⟨a, b⟩
      simp only [hP, block, Finset.mem_filter, Finset.mem_offDiag, Finset.mem_range]
      grind
    · intro p hp
      simp only [hP, Finset.coe_filter, Finset.mem_offDiag, Finset.mem_filter, Finset.mem_range,
        Set.mem_ofPred_eq] at hp
      simp only [Finset.coe_range, Set.mem_Iio]
      exact (Nat.div_lt_iff_lt_mul hN).2 hp.1.1.1
  have h2 : P.card ≤ 2 * N := by
    have := Finset.card_le_card_of_injOn (s := P) (t := Finset.Ioo (-(N : ℤ)) N)
      (fun p => (p.2 : ℤ) - p.1) ?_ ?_
    · simp only [Int.card_Ioo] at this
      omega
    · intro p hp
      simp only [hP, Finset.coe_filter, Finset.mem_offDiag, Finset.mem_filter, Finset.mem_range,
        Set.mem_ofPred_eq] at hp
      simp only [Finset.coe_Ioo, Set.mem_Ioo]
      obtain ⟨-, h⟩ := hp
      have e1 := Nat.div_add_mod p.1 N
      have e2 := Nat.div_add_mod p.2 N
      have m1 := Nat.mod_lt p.1 hN
      have m2 := Nat.mod_lt p.2 hN
      rw [h] at e1
      generalize N * (p.2 / N) = t at e1 e2
      omega
    · intro p hp q hq hpq
      simp only [hP, Finset.coe_filter, Finset.mem_offDiag, Finset.mem_filter, Finset.mem_range,
        Set.mem_ofPred_eq] at hp hq
      simp only at hpq
      have hsum : p.2 + q.1 = q.2 + p.1 := by omega
      rcases hA p.2 hp.1.2.1.2 q.2 hq.1.2.1.2 q.1 hq.1.1.2 p.1 hp.1.1.2 hsum with
        ⟨h1, h2⟩ | ⟨h1, -⟩
      · exact Prod.ext h2.symm h1
      · exact absurd h1.symm hp.1.2.2
  have h3 : ∀ F : ℕ, F ^ 2 ≤ 2 * (F * F - F) + 1 := by
    intro F
    rcases Nat.lt_or_ge F 2 with h | h
    · interval_cases F <;> simp
    · have := Nat.mul_le_mul_right F h
      have : F ^ 2 = F * F := sq F
      omega
  calc ∑ ℓ ∈ Finset.range N, (block A N ℓ).card ^ 2
      ≤ ∑ ℓ ∈ Finset.range N,
          (2 * ((block A N ℓ).card * (block A N ℓ).card - (block A N ℓ).card) + 1) :=
        Finset.sum_le_sum fun ℓ _ => h3 _
    _ = 2 * P.card + N := by rw [Finset.sum_add_distrib, ← Finset.mul_sum, h1]; simp
    _ ≤ 5 * N := by omega

open Classical in
/-- `#(A ∩ [0, mN)) = ∑_{ℓ < m} #(A ∩ [ℓN, (ℓ+1)N))` for `m ≤ N`. -/
theorem ncard_inter_Iio_eq_sum_block {A : Set ℕ} {N m : ℕ} (hN : 0 < N) (hm : m ≤ N) :
    (A ∩ Set.Iio (m * N)).ncard = ∑ ℓ ∈ Finset.range m, (block A N ℓ).card := by
  have e : A ∩ Set.Iio (m * N) = ↑({a ∈ Finset.range (m * N) | a ∈ A} : Finset ℕ) := by
    ext a; simp [and_comm]
  rw [e, Set.ncard_coe_finset,
    Finset.card_eq_sum_card_fiberwise (f := fun a => a / N) (t := Finset.range m)]
  · refine Finset.sum_congr rfl fun ℓ hℓ => ?_
    congr 1
    ext a
    simp only [block, Finset.mem_filter, Finset.mem_range] at hℓ ⊢
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨lt_of_lt_of_le h1 (Nat.mul_le_mul_right _ hm), h2, h3⟩
    · rintro ⟨-, h2, h3⟩
      refine ⟨⟨?_, h2⟩, h3⟩
      rw [← h3] at hℓ
      exact (Nat.div_lt_iff_lt_mul hN).1 hℓ
  · intro a ha
    simp only [Finset.coe_filter, Finset.mem_range, Set.mem_ofPred_eq, Finset.coe_range,
      Set.mem_Iio] at ha ⊢
    exact (Nat.div_lt_iff_lt_mul hN).2 ha.1

/-- Summation by parts, in the form used below. -/
theorem abel_identity (F w : ℕ → ℝ) (n : ℕ) :
    ∑ j ∈ Finset.range n, (∑ ℓ ∈ Finset.range (j + 1), F ℓ) * (w j - w (j + 1)) +
      (∑ ℓ ∈ Finset.range n, F ℓ) * w n = ∑ ℓ ∈ Finset.range n, F ℓ * w ℓ := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ (fun j => (∑ ℓ ∈ Finset.range (j + 1), F ℓ) * (w j - w (j + 1))),
      Finset.sum_range_succ (fun ℓ => F ℓ * w ℓ), ← ih, Finset.sum_range_succ F n]
    ring

/-- `1/√(j+1) - 1/√(j+2) ≥ 1/(2√(j+1)(j+2))`. -/
theorem inv_sqrt_sub_inv_sqrt_ge (j : ℕ) :
    1 / (2 * √((j : ℝ) + 1) * ((j : ℝ) + 2)) ≤
      1 / √((j : ℝ) + 1) - 1 / √(((j + 1 : ℕ) : ℝ) + 1) := by
  push_cast
  have ha : 0 < √((j : ℝ) + 1) := Real.sqrt_pos.2 (by positivity)
  have hb : 0 < √((j : ℝ) + 1 + 1) := Real.sqrt_pos.2 (by positivity)
  have ha2 : √((j : ℝ) + 1) ^ 2 = (j : ℝ) + 1 := Real.sq_sqrt (by positivity)
  have hb2 : √((j : ℝ) + 1 + 1) ^ 2 = (j : ℝ) + 1 + 1 := Real.sq_sqrt (by positivity)
  generalize √((j : ℝ) + 1) = a at ha ha2 ⊢
  generalize √((j : ℝ) + 1 + 1) = b at hb hb2 ⊢
  have hj : (j : ℝ) + 2 = b ^ 2 := by rw [hb2]; ring
  rw [hj, div_sub_div _ _ ha.ne' hb.ne', div_le_div_iff₀ (by positivity) (by positivity)]
  have key : (1 * b - a * 1) * (2 * a * b ^ 2) - 1 * (a * b) = a * b * (b - a) ^ 2 := by
    linear_combination (a * b) * (hb2 - ha2)
  nlinarith [mul_nonneg (mul_pos ha hb).le (sq_nonneg (b - a))]

/-- `∑_{j < N} 1/(j+2) ≥ log N - 1`. -/
theorem log_sub_one_le_sum {N : ℕ} (hN : 0 < N) :
    Real.log N - 1 ≤ ∑ j ∈ Finset.range N, 1 / ((j : ℝ) + 2) := by
  have h1 := log_add_one_le_harmonic (N + 1)
  have h2 : (harmonic (N + 1) : ℝ) = ∑ j ∈ Finset.range N, 1 / ((j : ℝ) + 2) + 1 := by
    rw [harmonic, Finset.sum_range_succ']
    push_cast
    congr 1
    · exact Finset.sum_congr rfl fun j _ => by ring
    · simp
  have h3 : Real.log N ≤ Real.log ((N + 1 + 1 : ℕ) : ℝ) :=
    Real.log_le_log (by exact_mod_cast hN) (by push_cast; linarith)
  linarith

/-- Real-arithmetic step of the pointwise lower bound. -/
theorem pointwise_aux {a s X R D : ℝ} {j : ℕ} (ha : 0 < a) (hX : 0 ≤ X)
    (hR : 0 ≤ R) (hD : 1 / (2 * a * ((j : ℝ) + 2)) ≤ D) (h : 100 * (a * s) < X * R) :
    50 * s / ((j : ℝ) + 2) ≤ R * (X * D) := by
  have ht : (0 : ℝ) < (j : ℝ) + 2 := by positivity
  calc 50 * s / ((j : ℝ) + 2) = (100 * (a * s)) * (1 / (2 * a * ((j : ℝ) + 2))) := by
        field_simp
        ring
    _ ≤ (X * R) * (1 / (2 * a * ((j : ℝ) + 2))) :=
        mul_le_mul_of_nonneg_right h.le (by positivity)
    _ ≤ (X * R) * D := mul_le_mul_of_nonneg_left hD (by positivity)
    _ = R * (X * D) := by ring

/-- The core estimate (Erdős): if `log N ≥ 2`, then some `M ≥ N` has
`#(A ∩ [0, M)) · √(log M) ≤ 100 √M`. -/
theorem exists_ncard_mul_sqrt_log_le {A : Set ℕ} (hA : IsSidon A) {N : ℕ}
    (hL : 2 ≤ Real.log N) :
    ∃ M : ℕ, N ≤ M ∧ ((A ∩ Set.Iio M).ncard : ℝ) * √(Real.log M) ≤ 100 * √(M : ℝ) := by
  by_contra! H
  have hN : 0 < N := by
    rcases Nat.eq_zero_or_pos N with h | h
    · rw [h] at hL; simp at hL; linarith
    · exact h
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  set L := Real.log N with hLdef
  set F : ℕ → ℝ := fun ℓ => ((block A N ℓ).card : ℝ) with hF
  set w : ℕ → ℝ := fun ℓ => 1 / √((ℓ : ℝ) + 1) with hw
  set T := ∑ ℓ ∈ Finset.range N, F ℓ * w ℓ with hT
  have hF0 : ∀ ℓ, 0 ≤ F ℓ := fun ℓ => by positivity
  have hw0 : ∀ ℓ, 0 ≤ w ℓ := fun ℓ => by positivity
  -- Upper bound: Cauchy–Schwarz.
  have hT2 : T ^ 2 ≤ 5 * N * (1 + L) := by
    calc T ^ 2 ≤ (∑ ℓ ∈ Finset.range N, F ℓ ^ 2) * ∑ ℓ ∈ Finset.range N, w ℓ ^ 2 :=
          Finset.sum_mul_sq_le_sq_mul_sq _ _ _
      _ ≤ (5 * N) * (1 + L) := by
        apply mul_le_mul
        · have := sum_sq_card_block_le hA hN
          have : ((∑ ℓ ∈ Finset.range N, (block A N ℓ).card ^ 2 : ℕ) : ℝ) ≤ ((5 * N : ℕ) : ℝ) :=
            by exact_mod_cast this
          push_cast at this
          exact this
        · have : ∑ ℓ ∈ Finset.range N, w ℓ ^ 2 = harmonic N := by
            rw [harmonic]
            push_cast
            refine Finset.sum_congr rfl fun ℓ _ => ?_
            simp only [hw, div_pow, one_pow]
            rw [Real.sq_sqrt (by positivity), one_div]
          rw [this]
          exact harmonic_le_one_add_log N
        · exact Finset.sum_nonneg fun ℓ _ => sq_nonneg _
        · positivity
  -- Summation by parts.
  have habel := abel_identity F w N
  have hSw : 0 ≤ (∑ ℓ ∈ Finset.range N, F ℓ) * w N :=
    mul_nonneg (Finset.sum_nonneg fun ℓ _ => hF0 ℓ) (hw0 N)
  -- Pointwise lower bound from the assumption `H`.
  have hpt : ∀ j ∈ Finset.range N, 50 * √(N : ℝ) / ((j : ℝ) + 2) ≤
      √2 * √L * ((∑ ℓ ∈ Finset.range (j + 1), F ℓ) * (w j - w (j + 1))) := by
    intro j hj
    have hjN : j + 1 ≤ N := Finset.mem_range.1 hj
    have hM := H ((j + 1) * N) (Nat.le_mul_of_pos_left N (Nat.succ_pos j))
    have hS : (((A ∩ Set.Iio ((j + 1) * N)).ncard : ℕ) : ℝ) =
        ∑ ℓ ∈ Finset.range (j + 1), F ℓ := by
      rw [ncard_inter_Iio_eq_sum_block hN hjN]
      push_cast
      rfl
    rw [hS] at hM
    have hlogM : Real.log (((j + 1) * N : ℕ) : ℝ) ≤ 2 * L := by
      rw [hLdef, ← Real.log_rpow hNr]
      apply Real.log_le_log (by positivity)
      push_cast
      rw [Real.rpow_two]
      have : ((j : ℝ) + 1) ≤ N := by exact_mod_cast hjN
      nlinarith [mul_le_mul_of_nonneg_right this hNr.le]
    have hsq : √(Real.log (((j + 1) * N : ℕ) : ℝ)) ≤ √2 * √L := by
      rw [← Real.sqrt_mul (by norm_num)]
      exact Real.sqrt_le_sqrt hlogM
    have hsqrtM : √((((j + 1) * N : ℕ) : ℝ)) = √((j : ℝ) + 1) * √(N : ℝ) := by
      push_cast
      exact Real.sqrt_mul (by positivity) _
    rw [hsqrtM] at hM
    have hS0 : 0 ≤ ∑ ℓ ∈ Finset.range (j + 1), F ℓ := Finset.sum_nonneg fun ℓ _ => hF0 ℓ
    exact pointwise_aux (Real.sqrt_pos.2 (by positivity)) hS0
      (by positivity) (inv_sqrt_sub_inv_sqrt_ge j)
      (hM.trans_le (mul_le_mul_of_nonneg_left hsq hS0))
  have hsum : 50 * √(N : ℝ) * (L - 1) ≤ √2 * √L * T := by
    calc 50 * √(N : ℝ) * (L - 1)
        ≤ 50 * √(N : ℝ) * ∑ j ∈ Finset.range N, 1 / ((j : ℝ) + 2) :=
          mul_le_mul_of_nonneg_left (log_sub_one_le_sum hN) (by positivity)
      _ = ∑ j ∈ Finset.range N, 50 * √(N : ℝ) / ((j : ℝ) + 2) := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun j _ => by ring
      _ ≤ ∑ j ∈ Finset.range N,
            √2 * √L * ((∑ ℓ ∈ Finset.range (j + 1), F ℓ) * (w j - w (j + 1))) :=
          Finset.sum_le_sum hpt
      _ = √2 * √L * ∑ j ∈ Finset.range N,
            (∑ ℓ ∈ Finset.range (j + 1), F ℓ) * (w j - w (j + 1)) := by
          rw [Finset.mul_sum]
      _ ≤ √2 * √L * T := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  -- Squaring gives `2500 N (L-1)² ≤ 2 L T² ≤ 10 N L (1 + L)`, impossible for `L ≥ 2`.
  have hsq := pow_le_pow_left₀ (by nlinarith [Real.sqrt_nonneg (N : ℝ)]) hsum 2
  rw [mul_pow, mul_pow, Real.sq_sqrt hNr.le, mul_pow, mul_pow, Real.sq_sqrt (by norm_num),
    Real.sq_sqrt (by linarith)] at hsq
  have h10 : 10 * N * (250 * (L - 1) ^ 2) ≤ 10 * N * (L * (1 + L)) := by
    nlinarith
  have h11 := le_of_mul_le_mul_left h10 (by positivity)
  nlinarith

-- The hypothesis `hAinf` matches the wording of Erdős Problem 1191; the bound holds for every
-- Sidon set, so it is not used.
set_option linter.unusedVariables false in
/-- Erdős's bound in explicit form: for every infinite Sidon set `A ⊆ ℕ` there is a constant `C`
such that `|A ∩ [1, x]| ≤ C √x / √(log x)` for arbitrarily large `x` (here `C = 200`). -/
theorem erdos_1191.variants.erdos_upper_bound_explicit {A : Set ℕ} (hAinf : A.Infinite)
    (hAsid : IsSidon A) :
    ∃ C : ℝ, ∃ᶠ x : ℕ in atTop, ((A ∩ Set.Icc 1 x).ncard : ℝ) ≤ C * √(x : ℝ) / √(Real.log x) := by
  refine ⟨200, frequently_atTop.2 fun a => ?_⟩
  obtain ⟨N1, hN1⟩ := eventually_atTop.1
    ((Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 2)
  obtain ⟨M, hM, hbound⟩ :=
    exists_ncard_mul_sqrt_log_le hAsid (hN1 (max (max (a + 1) 3) N1) (le_max_right _ _))
  have hM3 : 3 ≤ M := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hM
  refine ⟨M - 1, by have := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hM; omega, ?_⟩
  have hx : ((M - 1 : ℕ) : ℝ) + 1 = M := by
    rw [Nat.cast_sub (by omega)]; ring
  have hx2 : (2 : ℝ) ≤ ((M - 1 : ℕ) : ℝ) := by
    have : 2 ≤ M - 1 := by omega
    exact_mod_cast this
  have hlogx : 0 < Real.log ((M - 1 : ℕ) : ℝ) := Real.log_pos (by linarith)
  -- `A ∩ [1, M - 1] ⊆ A ∩ [0, M)`
  have hsub : ((A ∩ Set.Icc 1 (M - 1)).ncard : ℝ) ≤ (A ∩ Set.Iio M).ncard := by
    have : (A ∩ Set.Icc 1 (M - 1)).ncard ≤ (A ∩ Set.Iio M).ncard :=
      Set.ncard_le_ncard
        (Set.inter_subset_inter_right _ fun n hn => by simp only [Set.mem_Icc] at hn; simp; omega)
        ((Set.finite_Iio M).inter_of_right _)
    exact_mod_cast this
  have hlog : √(Real.log ((M - 1 : ℕ) : ℝ)) ≤ √(Real.log M) :=
    Real.sqrt_le_sqrt (Real.log_le_log (by linarith) (by linarith))
  have hsqrt : √(M : ℝ) ≤ 2 * √((M - 1 : ℕ) : ℝ) := by
    rw [show (2 : ℝ) = √4 by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)],
      ← Real.sqrt_mul (by norm_num)]
    exact Real.sqrt_le_sqrt (by linarith)
  rw [le_div_iff₀ (Real.sqrt_pos.2 hlogx)]
  calc ((A ∩ Set.Icc 1 (M - 1)).ncard : ℝ) * √(Real.log ((M - 1 : ℕ) : ℝ))
      ≤ (A ∩ Set.Iio M).ncard * √(Real.log M) :=
        mul_le_mul hsub hlog (Real.sqrt_nonneg _) (by positivity)
    _ ≤ 100 * √(M : ℝ) := hbound
    _ ≤ 200 * √((M - 1 : ℕ) : ℝ) := by linarith

-- The hypothesis `hAinf` matches the wording of Erdős Problem 1191; the bound holds for every
-- Sidon set, so it is not used.
set_option linter.unusedVariables false in
/-- **Erdős** (see Halberstam–Roth [HaRo66]): if `A ⊆ ℕ` is an infinite Sidon set, then
`liminf_{x → ∞} |A ∩ [1, x]| / x^{1/2} · (log x)^{1/2} ≤ c` for some constant `c`, i.e. the
liminf (taken in `ℝ≥0∞`, where it always exists) is finite. -/
theorem erdos_1191.variants.erdos_upper_bound {A : Set ℕ} (hAinf : A.Infinite)
    (hAsid : IsSidon A) :
    liminf (fun x : ℕ ↦ ENNReal.ofReal
      ((A ∩ Set.Icc 1 x).ncard / (x : ℝ) ^ (1 / 2 : ℝ) * Real.log x ^ (1 / 2 : ℝ))) atTop < ⊤ := by
  obtain ⟨C, hC⟩ := erdos_1191.variants.erdos_upper_bound_explicit hAinf hAsid
  refine lt_of_le_of_lt (liminf_le_of_frequently_le' (x := ENNReal.ofReal C) ?_)
    ENNReal.ofReal_lt_top
  refine (hC.and_eventually (eventually_ge_atTop 2)).mono fun x ⟨hx, hx2⟩ => ?_
  apply ENNReal.ofReal_le_ofReal
  have hxr : (2 : ℝ) ≤ x := by exact_mod_cast hx2
  have hlog : 0 < √(Real.log x) := Real.sqrt_pos.2 (Real.log_pos (by linarith))
  have hsx : 0 < √(x : ℝ) := Real.sqrt_pos.2 (by linarith)
  rw [← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow, div_mul_eq_mul_div, div_le_iff₀ hsx]
  rw [le_div_iff₀ hlog] at hx
  exact hx

end Erdos1191
