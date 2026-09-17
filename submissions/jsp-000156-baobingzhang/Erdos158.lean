import Mathlib

/-!
# Erdős Problem 158, Sidon case: `liminf A(N) √(log N) / √N < ∞`

Erdős Problem 158 asks whether every infinite `B₂[2]` set `A ⊆ ℕ` (every `n` has at most two
representations `n = a + a'` with `a ≤ a'`, `a, a' ∈ A`) satisfies
`liminf |A ∩ {1, …, N}| / N^{1/2} = 0`. That question is open. For Sidon sets (`B₂[1]`) Erdős
proved the stronger statement `liminf |A ∩ [1, N]| N^{-1/2} (log N)^{1/2} < ∞`; see Halberstam and
Roth, *Sequences*, Vol. I (1966), Ch. II, and Erdős, Sárközy and Sós, *On sum sets of Sidon
sets I*, J. Number Theory (1994) [ESS94].

This file proves both Sidon variants, stated without proof in Google DeepMind's
formal-conjectures project, `FormalConjectures/ErdosProblems/158.lean` (Apache-2.0):

* `erdos_158.variants.isSidon'` (category "research solved"): for every infinite Sidon set `A ⊆ ℕ`,
  `liminf_{N → ∞} ENNReal.ofReal (#(A ∩ [0, N)) · N^(-1/2) · (log N)^(1/2)) < ⊤`;
* `erdos_158.variants.isSidon`: for every infinite Sidon set `A ⊆ ℕ`,
  `liminf_{N → ∞} #(A ∩ [0, N)) · N^(-1/2) = 0` (in `ℝ`).

The definition `IsSidon` (from `FormalConjecturesForMathlib/Combinatorics/Basic.lean`) and both
statements are copied verbatim; the proof of `erdos_158.variants.isSidon` from
`erdos_158.variants.isSidon'` is also formal-conjectures' own. Only the category/AMS attributes
(which need the formal-conjectures build environment) are omitted. The bound actually proved is
`liminf ≤ 100`, and infinitude of `A` is not needed.

## Proof of `erdos_158.variants.isSidon'` (Erdős's argument)

Write `A(M) = #(A ∩ [0, M))`. It suffices that `A(M) √(log M) ≤ 100 √M` for arbitrarily large `M`.
Suppose instead `A(M) √(log M) > 100 √M` for all `M ≥ N`, where `L = log N ≥ 2`.

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

Since `log N → ∞`, this gives `A(M) M^(-1/2) (log M)^(1/2) ≤ 100` frequently, hence the `ENNReal`
liminf is at most `100 < ⊤`.

## What remains open

The main question of Erdős Problem 158, for `B₂[2]` sets, is not addressed here. Whether the
Sidon liminf above is in fact `0` is Erdős Problem 1191 and is also open.
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

namespace Erdos158

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

-- The hypothesis `hAinf` is kept verbatim from formal-conjectures; the bound holds for every
-- Sidon set, so it is not used.
set_option linter.unusedVariables false in
/-- Let `A` be an infinite Sidon set. Then
`liminf |A ∩ {1, ..., N}| * N ^ (- 1 / 2) * (log N) ^ (1 / 2) < ∞`. This is proved in [ESS94]. -/
theorem erdos_158.variants.isSidon' {A : Set ℕ} (hAinf : A.Infinite) (hAsid : IsSidon A) :
    liminf (fun N ↦ ENNReal.ofReal ((A ∩ .Iio N).ncard * N ^ (- 1 / 2 : ℝ) * log N ^ (1 / 2 : ℝ)))
      atTop < ⊤ := by
  refine lt_of_le_of_lt (liminf_le_of_frequently_le' (x := ENNReal.ofReal 100) ?_)
    ENNReal.ofReal_lt_top
  rw [frequently_atTop]
  intro a
  obtain ⟨N1, hN1⟩ := eventually_atTop.1
    ((Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 2)
  obtain ⟨M, hM, hbound⟩ := exists_ncard_mul_sqrt_log_le hAsid (hN1 (max a N1) (le_max_right _ _))
  refine ⟨M, le_trans (le_max_left _ _) hM, ENNReal.ofReal_le_ofReal ?_⟩
  have hlogM : 2 ≤ Real.log M := hN1 M (le_trans (le_max_right _ _) hM)
  have hMpos : (0 : ℝ) < M := by
    rcases Nat.eq_zero_or_pos M with h | h
    · rw [h] at hlogM; simp at hlogM; linarith
    · exact_mod_cast h
  rw [show (-1 / 2 : ℝ) = -(1 / 2) by norm_num, Real.rpow_neg hMpos.le, ← Real.sqrt_eq_rpow,
    ← Real.sqrt_eq_rpow, mul_right_comm, ← div_eq_mul_inv,
    div_le_iff₀ (Real.sqrt_pos.2 hMpos)]
  exact hbound

/-- As a corollary of `erdos_158.isSidon'`, we can prove that
`liminf |A ∩ {1, ..., N}| * N ^ (- 1 / 2) = 0` for any infinite Sidon set `A`. -/
theorem erdos_158.variants.isSidon {A : Set ℕ} (hAinf : A.Infinite) (hAsid : IsSidon A) :
    liminf (fun N : ℕ => (A ∩ .Iio N).ncard * (N : ℝ) ^ (- 1 / 2 : ℝ)) atTop = 0 := by
  have := erdos_158.variants.isSidon' hAinf hAsid
  contrapose! this with h
  rw [Tendsto.liminf_eq]
  refine ENNReal.tendsto_ofReal_atTop.comp ?_
  obtain ⟨c, hc_pos, hc⟩ :
      ∃ c > (0 : ℝ), ∀ᶠ N in atTop, c ≤ (A ∩ .Iio N).ncard * N ^ (- 1 / 2 : ℝ) := by
    suffices
      ∃ a ∈ {a | ∃ c : ℕ, ∀ b ≥ c, a ≤ ↑(A ∩ .Iio b).ncard * (b : ℝ) ^ (-1 / 2 : ℝ)}, 0 < a by aesop
    by_contra! ha
    simp only [liminf_eq, eventually_atTop] at h
    exact h <| le_antisymm (csSup_le ⟨0, 0, fun n hn => by positivity⟩ ha) <|
      (le_csSup ⟨0, ha⟩ ⟨0, fun n hn => by positivity⟩)
  refine tendsto_atTop_mono' atTop (f₁ := fun N : ℕ => c * log N ^ (1 / 2 : ℝ)) ?_ ?_
  · filter_upwards [hc] with n hn
    grw [hn]
  · refine .const_mul_atTop hc_pos ?_
    simpa [Function.comp_def] using (tendsto_rpow_atTop (by linarith : 0 < 1 / (2 : ℝ))).comp
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)

end Erdos158
