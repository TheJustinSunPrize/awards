/-
Copyright 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# JSP-001007: assembly of the counterexample

Putting the proved ingredients together:

* `JSP001007.clustering` — `k` primes in `(n, 2n]` with span `≤ 1024 k² log (2n) + 4`,
* `JSP001007.counterexample_core` — the Price–GPT construction,

with the numerical input `n = ⌊N^(9/10)/4⌋` and `log N ≤ c N^(4/5)`
(`JSP001007.eventually_log_le_rpow`).  The result is the final theorem:

for every `k ≥ 1` and every sufficiently large `N` there are `k` distinct primes below
`N^(9/10)` and forbidden class sets of size `(p i - 1)/2` with more than `N/10` surviving
integers in `[1, N]` — the negative answer to Green's problem 44 / Erdős problem #1202.
-/

import Mathlib
import Jsp.Jsp001007Proof
import Jsp.Jsp001007Cluster

set_option maxHeartbeats 1000000

open scoped BigOperators
open Filter

namespace JSP001007

/-- `(N^(9/10)) ^ 10 = N ^ 9`. -/
theorem rpow_nine_tenth_pow_ten {N : ℕ} :
    (((N : ℝ) ^ (9 / 10 : ℝ)) ^ 10) = (N : ℝ) ^ 9 := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
  norm_num

/-- **JSP-001007: the Price–GPT counterexample (final form).**

For every `k ≥ 1` and all sufficiently large `N`, there are `k` distinct primes `p i` with
`p i ^ 10 < N ^ 9` and forbidden residue classes `A i` modulo `p i` of size `(p i - 1)/2`
such that more than `N/10` integers in `[1, N]` avoid all the `A i`. -/
theorem green44_counterexample (k : ℕ) [NeZero k] (hk : 0 < k) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∃ (p : Fin k → ℕ) (A : (i : Fin k) → Finset (ZMod (p i))),
      (∀ i, (p i).Prime) ∧ StrictMono p ∧ (∀ i, (p i) ^ 10 < N ^ 9) ∧
      (∀ i, (A i).card = (p i - 1) / 2) ∧ N / 10 < (survivors N p A).card := by
  obtain ⟨n₁, hn₁⟩ := eventually_atTop.mp (clustering k hk)
  obtain ⟨n₂, hn₂⟩ := eventually_atTop.mp
    (eventually_log_le_rpow (1 / (1572864 * (k : ℝ) ^ 2)) (by positivity))
  refine ⟨max (max (n₁ ^ 2 + 1) (n₂ + 1)) (10 ^ 20), fun N hN => ?_⟩
  have hNn1 : n₁ ^ 2 + 1 ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN
  have hNn2 : n₂ + 1 ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
  have hNbig : 10 ^ 20 ≤ N := le_trans (le_max_right _ _) hN
  have hNpos : (0 : ℝ) < (N : ℝ) := by positivity
  have hNten : ((10 ^ 20 : ℕ) : ℝ) ≤ (N : ℝ) := by exact_mod_cast hNbig
  have hten : ((10 : ℝ)) ^ 20 = ((10 ^ 20 : ℕ) : ℝ) := by norm_num
  have htenbig : (4194304 : ℝ) ≤ (10 : ℝ) ^ 20 := by norm_num
  set X : ℝ := (N : ℝ) ^ (9 / 10 : ℝ) with hX
  have hXpos : 0 < X := Real.rpow_pos_of_pos hNpos _
  have hX10 : X ^ 10 = (N : ℝ) ^ 9 := by rw [hX]; exact rpow_nine_tenth_pow_ten
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by
    have : (1 : ℕ) ≤ N := by omega
    exact_mod_cast this
  have hXle : X ≤ (N : ℝ) := by
    rw [hX]
    calc (N : ℝ) ^ (9 / 10 : ℝ) ≤ (N : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hN1 (by norm_num)
      _ = (N : ℝ) := Real.rpow_one _
  -- `2048 ≤ N^(4/5)`
  have hX45 : (2048 : ℝ) ≤ (N : ℝ) ^ (4 / 5 : ℝ) := by
    have hbase : (2048 : ℝ) ^ (5 / 4 : ℝ) ≤ (N : ℝ) := by
      calc (2048 : ℝ) ^ (5 / 4 : ℝ) ≤ (2048 : ℝ) ^ 2 :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
        _ = 4194304 := by norm_num
        _ ≤ (10 : ℝ) ^ 20 := htenbig
        _ = ((10 ^ 20 : ℕ) : ℝ) := hten
        _ ≤ (N : ℝ) := hNten
    have h2 : ((2048 : ℝ) ^ (5 / 4 : ℝ)) ^ (4 / 5 : ℝ) ≤ (N : ℝ) ^ (4 / 5 : ℝ) :=
      Real.rpow_le_rpow (by positivity) hbase (by norm_num)
    have h3 : ((2048 : ℝ) ^ (5 / 4 : ℝ)) ^ (4 / 5 : ℝ) = 2048 := by
      rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2048)]
      norm_num
    rwa [h3] at h2
  -- `8 ≤ X`
  have hX8 : 8 ≤ X := by
    have hbase : (8 : ℝ) ^ (10 / 9 : ℝ) ≤ (N : ℝ) := by
      calc (8 : ℝ) ^ (10 / 9 : ℝ) ≤ (8 : ℝ) ^ 2 :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
        _ = 64 := by norm_num
        _ ≤ (10 : ℝ) ^ 20 := by linarith [htenbig]
        _ = ((10 ^ 20 : ℕ) : ℝ) := hten
        _ ≤ (N : ℝ) := hNten
    have h2 : ((8 : ℝ) ^ (10 / 9 : ℝ)) ^ (9 / 10 : ℝ) ≤ (N : ℝ) ^ (9 / 10 : ℝ) :=
      Real.rpow_le_rpow (by positivity) hbase (by norm_num)
    have h3 : ((8 : ℝ) ^ (10 / 9 : ℝ)) ^ (9 / 10 : ℝ) = 8 := by
      rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 8)]
      norm_num
    rw [hX]
    rwa [h3] at h2
  -- `√N ≤ X / 8`
  have hsqrtX : (N : ℝ) ^ (1 / 2 : ℝ) ≤ X / 8 := by
    have hbase : (8 : ℝ) ^ (5 / 2 : ℝ) ≤ (N : ℝ) := by
      calc (8 : ℝ) ^ (5 / 2 : ℝ) ≤ (8 : ℝ) ^ 3 :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
        _ = 512 := by norm_num
        _ ≤ (10 : ℝ) ^ 20 := by linarith [htenbig]
        _ = ((10 ^ 20 : ℕ) : ℝ) := hten
        _ ≤ (N : ℝ) := hNten
    have h2 : ((8 : ℝ) ^ (5 / 2 : ℝ)) ^ (2 / 5 : ℝ) ≤ (N : ℝ) ^ (2 / 5 : ℝ) :=
      Real.rpow_le_rpow (by positivity) hbase (by norm_num)
    have h3 : ((8 : ℝ) ^ (5 / 2 : ℝ)) ^ (2 / 5 : ℝ) = 8 := by
      rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 8)]
      norm_num
    rw [h3] at h2
    have hsplit : X = (N : ℝ) ^ (1 / 2 : ℝ) * (N : ℝ) ^ (2 / 5 : ℝ) := by
      rw [hX, ← Real.rpow_add hNpos]
      norm_num
    rw [hsplit]
    have hpos : 0 < (N : ℝ) ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hNpos _
    nlinarith [h2, hpos]
  set n : ℕ := ⌊X / 4⌋₊ with hn
  have hn_le : (n : ℝ) ≤ X / 4 := Nat.floor_le (by positivity)
  have hn_gt : X / 4 - 1 < (n : ℝ) := by
    have := Nat.lt_floor_add_one (X / 4)
    rw [← hn] at this
    linarith
  have hn_ge : X / 8 ≤ (n : ℝ) := by linarith
  have hn_large₁ : n₁ ≤ n := by
    have h1 : (n₁ : ℝ) ≤ (N : ℝ) ^ (1 / 2 : ℝ) := by
      rw [← Real.sqrt_eq_rpow]
      refine (Real.le_sqrt (by positivity) (by positivity)).mpr ?_
      have h2 : n₁ ^ 2 ≤ N := by omega
      exact_mod_cast h2
    have h2 : (n₁ : ℝ) ≤ (n : ℝ) := by linarith [h1, hsqrtX, hn_ge]
    exact_mod_cast h2
  obtain ⟨p, hmono, hprime, hbounds, hspan⟩ := hn₁ n hn_large₁
  -- basic facts about the cluster
  have hp_lo : ∀ i, (n : ℝ) < (p i : ℝ) := fun i => by exact_mod_cast (hbounds i).1
  have hp_hi : ∀ i, (p i : ℝ) ≤ X / 2 := fun i => by
    have h := (hbounds i).2
    have : (p i : ℝ) ≤ 2 * (n : ℝ) := by exact_mod_cast h
    linarith
  have hMpos : 0 < p 0 := by
    have := (hbounds 0).1
    omega
  have hM_ge : X / 8 ≤ (p 0 : ℝ) := by linarith [hp_lo 0, hn_ge]
  have hMn : n ≤ p 0 := by
    have := (hbounds 0).1
    omega
  -- the log bound at `n`
  have hlog : Real.log (2 * (n : ℝ)) ≤
      (1 / (1572864 * (k : ℝ) ^ 2)) * (N : ℝ) ^ (4 / 5 : ℝ) := by
    have h2n : 2 * (n : ℝ) ≤ (N : ℝ) := by linarith [hn_le]
    have hlogN := hn₂ N (by omega)
    have hmono : Real.log (2 * (n : ℝ)) ≤ Real.log (N : ℝ) :=
      Real.log_le_log (by linarith [hX8, hn_ge, hn_le]) h2n
    linarith
  have hD_le : (((Finset.univ.sup p : ℕ) - p 0 : ℕ) : ℝ) ≤
      (N : ℝ) ^ (4 / 5 : ℝ) / 1536 + 4 := by
    have h1 : (((Finset.univ.sup p : ℕ) - p 0 : ℕ) : ℝ) ≤
        1024 * (k : ℝ) ^ 2 * Real.log (2 * (n : ℝ)) + 4 := by
      have hle_sup : p 0 ≤ Finset.univ.sup p := Finset.le_sup (Finset.mem_univ _)
      have hcast := Nat.cast_sub (R := ℝ) hle_sup
      rw [hcast]
      linarith [hspan]
    have h2 : 1024 * (k : ℝ) ^ 2 * Real.log (2 * (n : ℝ)) ≤
        (N : ℝ) ^ (4 / 5 : ℝ) / 1536 := by
      have hk2 : (0 : ℝ) < 1572864 * (k : ℝ) ^ 2 := by positivity
      calc 1024 * (k : ℝ) ^ 2 * Real.log (2 * (n : ℝ))
          ≤ 1024 * (k : ℝ) ^ 2 *
              ((1 / (1572864 * (k : ℝ) ^ 2)) * (N : ℝ) ^ (4 / 5 : ℝ)) :=
            mul_le_mul_of_nonneg_left hlog (by positivity)
        _ = (N : ℝ) ^ (4 / 5 : ℝ) / 1536 := by
            field_simp
            ring
    linarith
  -- the construction's numeric hypotheses
  have hX24 : 24 ≤ X := by
    have hbase : (24 : ℝ) ^ (10 / 9 : ℝ) ≤ (N : ℝ) := by
      calc (24 : ℝ) ^ (10 / 9 : ℝ) ≤ (24 : ℝ) ^ 2 :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
        _ = 576 := by norm_num
        _ ≤ (10 : ℝ) ^ 20 := by linarith [htenbig]
        _ = ((10 ^ 20 : ℕ) : ℝ) := hten
        _ ≤ (N : ℝ) := hNten
    have h2 : ((24 : ℝ) ^ (10 / 9 : ℝ)) ^ (9 / 10 : ℝ) ≤ (N : ℝ) ^ (9 / 10 : ℝ) :=
      Real.rpow_le_rpow (by positivity) hbase (by norm_num)
    have h3 : ((24 : ℝ) ^ (10 / 9 : ℝ)) ^ (9 / 10 : ℝ) = 24 := by
      rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 24)]
      norm_num
    rw [hX]
    rwa [h3] at h2
  have hM3 : 3 ≤ p 0 := by
    have h1 : (3 : ℝ) ≤ (p 0 : ℝ) := by
      have h2 : (3 : ℝ) ≤ X / 8 := by linarith
      linarith [hp_lo 0]
    exact_mod_cast h1
  have hKD : 6 * ((N / p 0) * ((Finset.univ.sup p) - p 0)) ≤ p 0 := by
    have hdiv : ((N / p 0 : ℕ) : ℝ) ≤ (N : ℝ) / (p 0 : ℝ) := Nat.cast_div_le
    have hquot : (N : ℝ) / (p 0 : ℝ) ≤ 8 * (N : ℝ) / X := by
      rw [div_le_iff₀ (by positivity : (0 : ℝ) < (p 0 : ℝ))]
      rw [show 8 * (N : ℝ) / X * (p 0 : ℝ) = 8 * (N : ℝ) * (p 0 : ℝ) / X by ring]
      rw [le_div_iff₀ hXpos]
      nlinarith [hM_ge, hNpos]
    have hstep : ((N / p 0 : ℕ) : ℝ) * (((Finset.univ.sup p : ℕ) - p 0 : ℕ) : ℝ) ≤
        (8 * (N : ℝ) / X) * ((N : ℝ) ^ (4 / 5 : ℝ) / 1536 + 4) := by
      have hnn : (0 : ℝ) ≤ ((Finset.univ.sup p : ℕ) - p 0 : ℕ) := Nat.cast_nonneg _
      have hpos : (0 : ℝ) ≤ 8 * (N : ℝ) / X := by positivity
      exact mul_le_mul (le_trans hdiv hquot) hD_le hnn hpos
    have hsplit : (N : ℝ) = (N : ℝ) ^ (9 / 10 : ℝ) * (N : ℝ) ^ (1 / 10 : ℝ) := by
      have h : (N : ℝ) ^ ((9 / 10 : ℝ) + 1 / 10) =
          (N : ℝ) ^ (9 / 10 : ℝ) * (N : ℝ) ^ (1 / 10 : ℝ) := Real.rpow_add hNpos _ _
      rw [show (9 / 10 : ℝ) + 1 / 10 = 1 by norm_num, Real.rpow_one] at h
      exact h
    have h45 : (N : ℝ) ^ (4 / 5 : ℝ) * (N : ℝ) ^ (1 / 10 : ℝ) = (N : ℝ) ^ (9 / 10 : ℝ) := by
      have h : (N : ℝ) ^ ((4 / 5 : ℝ) + 1 / 10) =
          (N : ℝ) ^ (4 / 5 : ℝ) * (N : ℝ) ^ (1 / 10 : ℝ) := Real.rpow_add hNpos _ _
      rw [show (4 / 5 : ℝ) + 1 / 10 = 9 / 10 by norm_num] at h
      exact h.symm
    have h8 : 8 * (N : ℝ) / X = 8 * (N : ℝ) ^ (1 / 10 : ℝ) := by
      rw [hX]
      nth_rewrite 1 [hsplit]
      rw [mul_div_assoc]
      rw [mul_div_cancel_left₀ _ (ne_of_gt (Real.rpow_pos_of_pos hNpos _))]
    have hsimp : (8 * (N : ℝ) / X) * ((N : ℝ) ^ (4 / 5 : ℝ) / 1536 + 4) =
        (N : ℝ) ^ (9 / 10 : ℝ) / 192 + 32 * (N : ℝ) ^ (1 / 10 : ℝ) := by
      have h45' : (N : ℝ) ^ (1 / 10 : ℝ) * (N : ℝ) ^ (4 / 5 : ℝ) =
          (N : ℝ) ^ (9 / 10 : ℝ) := by
        rw [mul_comm, h45]
      rw [h8]
      have h1 : 8 * (N : ℝ) ^ (1 / 10 : ℝ) * ((N : ℝ) ^ (4 / 5 : ℝ) / 1536 + 4) =
          8 * ((N : ℝ) ^ (1 / 10 : ℝ) * (N : ℝ) ^ (4 / 5 : ℝ)) / 1536 +
            32 * (N : ℝ) ^ (1 / 10 : ℝ) := by ring
      rw [h1, h45']
      ring
    have hsmall : 6 * ((N : ℝ) ^ (9 / 10 : ℝ) / 192 + 32 * (N : ℝ) ^ (1 / 10 : ℝ)) ≤ X / 8 := by
      rw [hX]
      have h5 : (N : ℝ) ^ (9 / 10 : ℝ) =
          (N : ℝ) ^ (4 / 5 : ℝ) * (N : ℝ) ^ (1 / 10 : ℝ) := by
        have h : (N : ℝ) ^ ((4 / 5 : ℝ) + 1 / 10) =
            (N : ℝ) ^ (4 / 5 : ℝ) * (N : ℝ) ^ (1 / 10 : ℝ) := Real.rpow_add hNpos _ _
        rw [show (4 / 5 : ℝ) + 1 / 10 = 9 / 10 by norm_num] at h
        exact h
      rw [h5]
      have h6 : (0 : ℝ) < (N : ℝ) ^ (1 / 10 : ℝ) := Real.rpow_pos_of_pos hNpos _
      nlinarith [hX45, h6]
    have hgoal : 6 * ((8 * (N : ℝ) / X) * ((N : ℝ) ^ (4 / 5 : ℝ) / 1536 + 4)) ≤ (p 0 : ℝ) := by
      rw [hsimp]
      linarith [hsmall, hM_ge]
    have hfinal : ((6 * ((N / p 0) * ((Finset.univ.sup p) - p 0)) : ℕ) : ℝ) ≤ (p 0 : ℝ) := by
      push_cast
      nlinarith [hstep, hgoal]
    exact_mod_cast hfinal
  have hMN : 10 * p 0 < 7 * N := by
    have h1 : (10 : ℝ) * (p 0 : ℝ) ≤ 5 * X := by
      have := hp_hi 0
      linarith
    have h2 : (5 : ℝ) * X < 7 * (N : ℝ) := by
      have h3 : X ≤ (N : ℝ) := hXle
      have h4 : (7 : ℝ) * (N : ℝ) - 5 * X ≥ 2 * (N : ℝ) := by linarith
      linarith
    exact_mod_cast (by linarith : (10 : ℝ) * (p 0 : ℝ) < 7 * (N : ℝ))
  obtain ⟨A, hAcard, hsurv⟩ := counterexample_core hk p hprime hmono hM3 hKD hMN
  have hp10 : ∀ i, (p i) ^ 10 < N ^ 9 := by
    intro i
    have h1 : ((p i : ℕ) : ℝ) ^ 10 < (N : ℝ) ^ 9 := by
      have h2 := hp_hi i
      calc ((p i : ℕ) : ℝ) ^ 10 ≤ (X / 2) ^ 10 := pow_le_pow_left₀ (by positivity) h2 10
        _ = X ^ 10 / 1024 := by ring
        _ = (N : ℝ) ^ 9 / 1024 := by rw [hX10]
        _ < (N : ℝ) ^ 9 := by
            have := pow_pos hNpos 9
            linarith
    exact_mod_cast h1
  exact ⟨p, A, hprime, hmono, hp10, hAcard, hsurv⟩

end JSP001007
