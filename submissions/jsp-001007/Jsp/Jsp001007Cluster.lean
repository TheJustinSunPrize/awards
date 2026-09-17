/-
Copyright 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# JSP-001007: clustering the primes

From the prime count lower bound (`JSP001007.primeCount_lower`) we extract, for every `k ≥ 1`
and all sufficiently large `n`, `k` primes in `(n, 2n]` whose span is at most
`1024 k² log (2n) + 4`.

The argument is a pigeonhole on blocks of length `D = ⌈1024 k² log (2n)⌉ + 2`: if every block
`(n + iD, n + (i+1)D]` contained at most `k - 1` primes, then `(n, 2n]` would contain at most
`(n/D + 1)(k - 1) < n / (4 log 2n)` primes, contradicting `primeCount_lower`.
-/

import Mathlib
import Jsp.Jsp001007Chebyshev

open scoped BigOperators
open Filter

namespace JSP001007

theorem clustering (k : ℕ) [NeZero k] (hk : 0 < k) :
    ∀ᶠ n : ℕ in atTop, ∃ p : Fin k → ℕ,
      StrictMono p ∧ (∀ i, (p i).Prime) ∧ (∀ i, n < p i ∧ p i ≤ 2 * n) ∧
      (((Finset.univ.sup p : ℕ) : ℝ) - (p 0 : ℝ)) ≤ 1024 * (k : ℝ) ^ 2 * Real.log (2 * n) + 4 := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  filter_upwards [primeCount_lower,
    eventually_log_two_mul_le (1 / (1000 * (k : ℝ))) (by positivity),
    eventually_ge_atTop 1000000] with n hcount hlog hn
  set L : ℝ := Real.log (2 * (n : ℝ)) with hLdef
  have hLpos : 0 < L := by
    rw [hLdef]
    apply Real.log_pos
    have : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (show 1 ≤ n by omega)
    linarith
  set S : Finset ℕ := (Finset.Ioc n (2 * n)).filter Nat.Prime with hSdef
  have hScard : (n : ℝ) / (4 * L) ≤ (S.card : ℝ) := by
    rw [hSdef, hLdef]
    exact hcount
  set D : ℕ := ⌈1024 * (k : ℝ) ^ 2 * L⌉₊ + 2 with hDdef
  have hDpos : 0 < D := by omega
  have hDge : 1024 * (k : ℝ) ^ 2 * L + 1 ≤ (D : ℝ) := by
    rw [hDdef]
    push_cast
    have := Nat.le_ceil (1024 * (k : ℝ) ^ 2 * L)
    linarith
  -- some block contains at least `k` primes
  have hex : ∃ i ∈ Finset.range (n / D + 1),
      k ≤ (S.filter fun p => (p - n - 1) / D = i).card := by
    by_contra h
    push_neg at h
    have hcover : S ⊆ (Finset.range (n / D + 1)).biUnion
        (fun i => S.filter fun p => (p - n - 1) / D = i) := by
      intro p hp
      rw [Finset.mem_biUnion]
      refine ⟨(p - n - 1) / D, ?_, ?_⟩
      · rw [Finset.mem_range]
        have h1 := Finset.mem_filter.mp hp
        have h2 := Finset.mem_Ioc.mp h1.1
        have h3 : (p - n - 1) / D ≤ n / D := by
          apply Nat.div_le_div_right
          omega
        omega
      · exact Finset.mem_filter.mpr ⟨hp, rfl⟩
    have hchain : S.card ≤ (n / D + 1) * (k - 1) := by
      calc S.card ≤ ((Finset.range (n / D + 1)).biUnion
            (fun i => S.filter fun p => (p - n - 1) / D = i)).card :=
            Finset.card_le_card hcover
        _ ≤ ∑ i ∈ Finset.range (n / D + 1),
              (S.filter fun p => (p - n - 1) / D = i).card := Finset.card_biUnion_le
        _ ≤ ∑ _i ∈ Finset.range (n / D + 1), (k - 1) := by
              refine Finset.sum_le_sum fun i hi => ?_
              have := h i hi
              omega
        _ = (n / D + 1) * (k - 1) := by
              rw [Finset.sum_const, Finset.card_range, smul_eq_mul]
    -- arithmetic: `(n/D + 1) * (k-1) < n / (4L)`
    have hquot : (n : ℝ) / (D : ℝ) ≤ (n : ℝ) / (1024 * (k : ℝ) ^ 2 * L) := by
      refine div_le_div_of_nonneg_left (Nat.cast_nonneg (α := ℝ) n) (by positivity) ?_
      linarith [hDge]
    have hA : (n : ℝ) / (D : ℝ) * ((k : ℝ) - 1) ≤ (n : ℝ) / (1024 * L) := by
      have h1 : (n : ℝ) / (D : ℝ) * ((k : ℝ) - 1) ≤
          (n : ℝ) / (1024 * (k : ℝ) ^ 2 * L) * (k : ℝ) := by
        have h2 : ((k : ℝ) - 1) ≤ (k : ℝ) := by linarith
        have h3 : (0 : ℝ) ≤ (n : ℝ) / (D : ℝ) := by positivity
        calc (n : ℝ) / (D : ℝ) * ((k : ℝ) - 1) ≤ (n : ℝ) / (D : ℝ) * (k : ℝ) := by
              nlinarith [h3, h2]
          _ ≤ (n : ℝ) / (1024 * (k : ℝ) ^ 2 * L) * (k : ℝ) := by
              have h4 : (0 : ℝ) ≤ (k : ℝ) := hkR.le
              nlinarith [hquot, h4]
      have h5 : (n : ℝ) / (1024 * (k : ℝ) ^ 2 * L) * (k : ℝ) =
          (n : ℝ) / (1024 * (k : ℝ) * L) := by
        field_simp
      have h6 : (n : ℝ) / (1024 * (k : ℝ) * L) ≤ (n : ℝ) / (1024 * L) := by
        have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
        have hden : (1024 : ℝ) * L ≤ 1024 * (k : ℝ) * L := by
          calc (1024 : ℝ) * L = 1024 * (1 * L) := by ring
            _ ≤ 1024 * ((k : ℝ) * L) :=
                mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hk1 hLpos.le) (by norm_num)
            _ = 1024 * (k : ℝ) * L := by ring
        exact div_le_div_of_nonneg_left (Nat.cast_nonneg (α := ℝ) n) (by positivity) hden
      linarith
    have hB : ((k : ℝ) - 1) < (n : ℝ) / (4 * L) - (n : ℝ) / (1024 * L) := by
      have h6 : 1000 * (k : ℝ) * L ≤ (n : ℝ) := by
        have h7 : L ≤ 1 / (1000 * (k : ℝ)) * (n : ℝ) := hlog
        have h8 : (0 : ℝ) < 1000 * (k : ℝ) := by positivity
        calc 1000 * (k : ℝ) * L ≤ 1000 * (k : ℝ) * (1 / (1000 * (k : ℝ)) * (n : ℝ)) := by
              nlinarith [h7, h8]
          _ = (n : ℝ) := by field_simp
      have h8 : ((k : ℝ) - 1) * L < (k : ℝ) * L := by nlinarith [hLpos, hkR]
      have h9 : (k : ℝ) * L ≤ (n : ℝ) / 1000 := by
        rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 1000)]
        nlinarith [h6]
      have h11 : ((k : ℝ) - 1) * (4096 * L) < 1020 * (n : ℝ) := by
        have h12 : ((k : ℝ) - 1) * L ≤ (n : ℝ) / 1000 := le_of_lt (lt_of_lt_of_le h8 h9)
        nlinarith [h12, hLpos]
      have h10 : (n : ℝ) / (4 * L) - (n : ℝ) / (1024 * L) = 1020 * (n : ℝ) / (4096 * L) := by
        field_simp
        ring
      rw [h10, lt_div_iff₀ (by positivity : (0 : ℝ) < 4096 * L)]
      linarith [h11]
    have harith : (((n / D + 1) * (k - 1) : ℕ) : ℝ) < (n : ℝ) / (4 * L) := by
      have hnat : (((n / D + 1) * (k - 1) : ℕ) : ℝ) ≤
          ((n : ℝ) / (D : ℝ) + 1) * ((k : ℝ) - 1) := by
        have h1 : (((n / D : ℕ)) : ℝ) ≤ (n : ℝ) / D := Nat.cast_div_le
        have h2 : (((k - 1 : ℕ)) : ℝ) = (k : ℝ) - 1 := by
          rw [Nat.cast_sub (by omega : 1 ≤ k)]
          norm_num
        have h3 : (0 : ℝ) ≤ (k : ℝ) - 1 := by linarith
        push_cast
        rw [h2]
        nlinarith [h1, h3, Nat.cast_nonneg (α := ℝ) n]
      have hexp : ((n : ℝ) / (D : ℝ) + 1) * ((k : ℝ) - 1) =
          (n : ℝ) / (D : ℝ) * ((k : ℝ) - 1) + ((k : ℝ) - 1) := by ring
      linarith [hnat, hA, hB, hexp]
    have hle : (S.card : ℝ) ≤ (((n / D + 1) * (k - 1) : ℕ) : ℝ) := by exact_mod_cast hchain
    linarith [hScard, harith, hle]
  obtain ⟨i, -, hik⟩ := hex
  obtain ⟨T, hTsub, hTcard⟩ := Finset.exists_subset_card_eq hik
  have hTne : T.Nonempty := Finset.card_pos.mp (by omega)
  have hTblock : ∀ x ∈ T, (x - n - 1) / D = i := by
    intro x hx
    exact (Finset.mem_filter.mp (hTsub hx)).2
  have hTprime : ∀ x ∈ T, Nat.Prime x := by
    intro x hx
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp (hTsub hx)).1).2
  have hTbound : ∀ x ∈ T, n < x ∧ x ≤ 2 * n := by
    intro x hx
    exact Finset.mem_Ioc.mp (Finset.mem_filter.mp (Finset.mem_filter.mp (hTsub hx)).1).1
  refine ⟨T.orderEmbOfFin hTcard, ?_, ?_, ?_, ?_⟩
  · exact (T.orderEmbOfFin hTcard).strictMono
  · intro j
    exact hTprime _ (Finset.orderEmbOfFin_mem T hTcard j)
  · intro j
    exact hTbound _ (Finset.orderEmbOfFin_mem T hTcard j)
  · have hidx : k - 1 < k := Nat.sub_lt hk (by norm_num)
    have hmin : (T.orderEmbOfFin hTcard) 0 = T.min' hTne :=
      Finset.orderEmbOfFin_zero hTcard hk
    have hmax : (T.orderEmbOfFin hTcard) ⟨k - 1, hidx⟩ = T.max' hTne :=
      Finset.orderEmbOfFin_last hTcard hk
    have hsup : (Finset.univ.sup (T.orderEmbOfFin hTcard)) = T.max' hTne := by
      apply le_antisymm
      · refine Finset.sup_le fun j _ => Finset.le_max' T _ (Finset.orderEmbOfFin_mem T hTcard j)
      · rw [← hmax]
        exact Finset.le_sup (Finset.mem_univ (⟨k - 1, hidx⟩ : Fin k))
    rw [hsup, hmin]
    have h1 : i * D ≤ T.min' hTne - n - 1 := by
      have := Nat.div_mul_le_self (T.min' hTne - n - 1) D
      rwa [hTblock _ (Finset.min'_mem T hTne)] at this
    have h2 : T.max' hTne - n - 1 < (i + 1) * D := by
      exact (Nat.div_lt_iff_lt_mul hDpos).mp
        (by rw [hTblock _ (Finset.max'_mem T hTne)]; exact Nat.lt_succ_self i)
    have hminle : T.min' hTne ≤ T.max' hTne := Finset.min'_le T _ (Finset.max'_mem T hTne)
    have hmin_lo : n < T.min' hTne := (hTbound _ (Finset.min'_mem T hTne)).1
    have hmax_lo : n < T.max' hTne := (hTbound _ (Finset.max'_mem T hTne)).1
    have hspan : T.max' hTne - T.min' hTne ≤ D := by
      rw [add_mul, one_mul] at h2
      omega
    calc (((T.max' hTne : ℕ)) : ℝ) - ((T.min' hTne : ℕ) : ℝ)
        = (((T.max' hTne - T.min' hTne : ℕ)) : ℝ) := by
          rw [Nat.cast_sub hminle]
      _ ≤ (D : ℝ) := by exact_mod_cast hspan
      _ ≤ 1024 * (k : ℝ) ^ 2 * L + 4 := by
          have hDup : (D : ℝ) ≤ 1024 * (k : ℝ) ^ 2 * L + 3 := by
            rw [hDdef]
            push_cast
            have := Nat.ceil_lt_add_one (show (0 : ℝ) ≤ 1024 * (k : ℝ) ^ 2 * L by positivity)
            linarith
          linarith

end JSP001007
