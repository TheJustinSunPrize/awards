/-
Copyright 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# JSP-001007: the Price–GPT-5.4 half-residue sieve counterexample (combinatorial core)

Source: *A Counterexample to a Half-Residue Sieve Bound* (Liam Price and GPT-5.4 Pro),
<https://www.overleaf.com/read/qyhdmrchqnvb>; Erdős problem #1202 / Ben Green, *100 open
problems*, Problem 44.

Given `k` primes `p 0 < ⋯ < p (k-1)` in a cluster (`D = max p - p 0` small compared with
`M = p 0`), the construction forbids the residue classes

`R i = complement of { -K*D + r mod p i : 1 ≤ r ≤ (p i + 1)/2 }`

and exhibits the explicit block set

`T = { j*M + t : 0 ≤ j < K, 1 ≤ t ≤ L },  K = N / M,  L = (M+1)/2 - K*D,`

every element of which survives: for `n = j*M + t` and `p i = M + d i` one has
`n ≡ t - j*d i (mod p i)` and `1 ≤ t + K*D - j*d i ≤ (p i + 1)/2`, so the residue of `n`
lies in the allowed half-interval.

Hence `|S| ≥ |T| = K*L > N/10` as soon as `M < 7N/10` and `6*K*D ≤ M`.

This file proves the construction and the counting from scratch; the clustering input (k
primes in a window of width `C log x` inside `[x, 2x]`, a Chebyshev/PNT consequence) is
proved in `Jsp.Jsp001007Chebyshev` and `Jsp.Jsp001007Cluster`.
-/

import Mathlib
import Jsp.Jsp001007

namespace JSP001007

open scoped BigOperators

/-- Allowed residue classes modulo `p`: the half-interval `{-K*D + 1, …, -K*D + (p+1)/2}`. -/
def allowedSet (KD p : ℕ) : Finset (ZMod p) :=
  ((Finset.Icc 1 ((p + 1) / 2) : Finset ℕ)).image fun r : ℕ => (r : ZMod p) - (KD : ZMod p)

/-- The block set `T = {j*M + t : 0 ≤ j < K, 1 ≤ t ≤ L}`. -/
def blockSet (K M L : ℕ) : Finset ℕ :=
  ((Finset.range K) ×ˢ (Finset.Icc 1 L)).image fun jt => jt.1 * M + jt.2

/-- Translation by `-K*D` is injective modulo `p`, so the allowed set has `(p+1)/2` elements
for `p ≥ 2`. -/
theorem allowedSet_card {KD p : ℕ} (hp : 2 ≤ p) : (allowedSet KD p).card = (p + 1) / 2 := by
  rw [allowedSet, Finset.card_image_of_injOn]
  · simp
  intro a ha b hb hab
  have ha : a ∈ Finset.Icc 1 ((p + 1) / 2) := by simpa using ha
  have hb : b ∈ Finset.Icc 1 ((p + 1) / 2) := by simpa using hb
  rw [Finset.mem_Icc] at ha hb
  have ha' : a < p := by omega
  have hb' : b < p := by omega
  have h2 : (a : ZMod p) = (b : ZMod p) := sub_left_injective hab
  have h3 := congrArg (fun x : ZMod p => x.val) h2
  simpa [ZMod.val_natCast, Nat.mod_eq_of_lt ha', Nat.mod_eq_of_lt hb'] using h3

/-- `T` does not wrap around: if `L < M` then `j ↦ j*M + t` is injective on
`range K × Icc 1 L`, so `|T| = K*L`. -/
theorem blockSet_card {K M L : ℕ} (hL : L < M) : (blockSet K M L).card = K * L := by
  rw [blockSet, Finset.card_image_of_injOn]
  · simp [Finset.card_product]
  intro a ha b hb hab
  beta_reduce at hab
  have ha : a ∈ (Finset.range K) ×ˢ (Finset.Icc 1 L) := by simpa using ha
  have hb : b ∈ (Finset.range K) ×ˢ (Finset.Icc 1 L) := by simpa using hb
  rw [Finset.mem_product, Finset.mem_range, Finset.mem_Icc] at ha hb
  obtain ⟨ha1, ha2, ha3⟩ := ha
  obtain ⟨hb1, hb2, hb3⟩ := hb
  have hfst : a.1 = b.1 := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · have hle : a.1 + 1 ≤ b.1 := by omega
      have hmul : (a.1 + 1) * M ≤ b.1 * M := Nat.mul_le_mul_right M hle
      rw [add_mul, one_mul] at hmul
      have hlt1 : a.1 * M + a.2 < b.1 * M :=
        calc a.1 * M + a.2 < a.1 * M + M := by omega
          _ ≤ b.1 * M := hmul
      omega
    · have hle : b.1 + 1 ≤ a.1 := by omega
      have hmul : (b.1 + 1) * M ≤ a.1 * M := Nat.mul_le_mul_right M hle
      rw [add_mul, one_mul] at hmul
      have hlt1 : b.1 * M + b.2 < a.1 * M :=
        calc b.1 * M + b.2 < b.1 * M + M := by omega
          _ ≤ a.1 * M := hmul
      omega
  have hsnd : a.2 = b.2 := by
    rw [hfst] at hab
    omega
  exact Prod.ext hfst hsnd

/-- **Combinatorial core of the Price–GPT counterexample.**

For `k ≥ 1` clustered primes `p`, if `6*K*D ≤ M` and `M < 7N/10`, then there are forbidden
class sets `A i` with `|A i| = (p i - 1)/2` such that more than `N/10` integers in `[1,N]`
survive.  (`M = p 0`, `D = max p - p 0`, `K = N / M`.) -/
theorem counterexample_core {k : ℕ} [NeZero k] (hk : 0 < k) {N : ℕ} (p : Fin k → ℕ)
    (hprime : ∀ i, (p i).Prime) (hmono : StrictMono p)
    (hM3 : 3 ≤ p 0)
    (hKD : 6 * ((N / p 0) * ((Finset.univ.sup p) - p 0)) ≤ p 0)
    (hMN : 10 * p 0 < 7 * N) :
    ∃ A : (i : Fin k) → Finset (ZMod (p i)),
      (∀ i, (A i).card = (p i - 1) / 2) ∧ N / 10 < (survivors N p A).card := by
  classical
  haveI : ∀ i, NeZero (p i) := fun i => ⟨(hprime i).ne_zero⟩
  have hMpos : 0 < p 0 := by omega
  have hKDle : (N / p 0) * ((Finset.univ.sup p) - p 0) ≤ (p 0 + 1) / 2 := by omega
  have hLdef : (p 0 + 1) / 2 - (N / p 0) * ((Finset.univ.sup p) - p 0) +
      (N / p 0) * ((Finset.univ.sup p) - p 0) = (p 0 + 1) / 2 :=
    Nat.sub_add_cancel hKDle
  have hLltM : (p 0 + 1) / 2 - (N / p 0) * ((Finset.univ.sup p) - p 0) < p 0 := by omega
  refine ⟨fun i => Finset.univ \ allowedSet ((N / p 0) * ((Finset.univ.sup p) - p 0)) (p i),
    ?_, ?_⟩
  · -- cardinality of the forbidden sets
    intro i
    have hp2 : 2 ≤ p i := (hprime i).two_le
    obtain ⟨m, hm⟩ : ∃ m, p i = 2 * m + 1 := by
      rcases (hprime i).eq_two_or_odd with h | h
      · have hle : p 0 ≤ p i := hmono.monotone (Fin.zero_le i)
        omega
      · exact ⟨p i / 2, by omega⟩
    rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, ZMod.card,
      allowedSet_card hp2]
    omega
  · -- the block set survives
    set M := p 0 with hMdef
    set D := (Finset.univ.sup p) - p 0 with hDdef
    set K := N / M with hKdef
    set L := (M + 1) / 2 - K * D with hLdef
    have hKD' : 6 * (K * D) ≤ M := by rw [hKdef, hMdef, hDdef]; exact hKD
    have hKDle : K * D ≤ (M + 1) / 2 := by omega
    have hLKD : L + K * D = (M + 1) / 2 := by
      rw [hLdef]; exact Nat.sub_add_cancel hKDle
    have hLltM : L < M := by omega
    have hsub : blockSet K M L ⊆ survivors N p
        (fun i => Finset.univ \ allowedSet (K * D) (p i)) := by
      intro n hn
      simp only [blockSet, Finset.mem_image, Finset.mem_product, Finset.mem_range,
        Finset.mem_Icc] at hn
      obtain ⟨⟨j, t⟩, ⟨hjr, ht1, htL⟩, rfl⟩ := hn
      simp only [survivors, Finset.mem_filter, Finset.mem_Icc]
      refine ⟨⟨by omega, ?_⟩, ?_⟩
      · -- j*M + t ≤ N
        have hKMle : K * M ≤ N := by rw [hKdef]; exact Nat.div_mul_le_self N M
        have h1 : j ≤ K - 1 := by omega
        have h2 : j * M ≤ (K - 1) * M := Nat.mul_le_mul_right M h1
        have h3 : (K - 1) * M + L < K * M := by
          have hK1 : (K - 1 + 1) * M = K * M := by
            rw [Nat.sub_add_cancel (by omega : 1 ≤ K)]
          rw [← hK1, add_mul, one_mul]
          omega
        omega
      · intro i
        have hle : M ≤ p i := by rw [hMdef]; exact hmono.monotone (Fin.zero_le i)
        have hdle : p i - M ≤ D := by
          have : p i ≤ Finset.univ.sup p := Finset.le_sup (Finset.mem_univ i)
          rw [hDdef, hMdef]; omega
        have hKpos : 1 ≤ K := by
          have : K * M ≤ N := by rw [hKdef]; exact Nat.div_mul_le_self N M
          omega
        have hjd : j * (p i - M) ≤ K * D := by
          have h1 : j ≤ K - 1 := by omega
          calc j * (p i - M) ≤ (K - 1) * (p i - M) := Nat.mul_le_mul_right _ h1
            _ ≤ (K - 1) * D := Nat.mul_le_mul_left _ hdle
            _ ≤ K * D := Nat.mul_le_mul_right _ (by omega)
        obtain ⟨r, hrdef⟩ : ∃ r, r = t + K * D - j * (p i - M) := ⟨_, rfl⟩
        have hr1 : 1 ≤ r := by omega
        have hr2 : r ≤ (p i + 1) / 2 := by
          have : r ≤ L + K * D := by omega
          omega
        have hMpi : M + (p i - M) = p i := Nat.add_sub_cancel' hle
        have hkey : j * p i + r = (j * M + t) + K * D := by
          have h1 : j * p i = j * M + j * (p i - M) := by rw [← Nat.mul_add, hMpi]
          omega
        have hmem : ((j * M + t : ℕ) : ZMod (p i)) ∈ allowedSet (K * D) (p i) := by
          simp only [allowedSet, Finset.mem_image, Finset.mem_Icc]
          refine ⟨r, ⟨hr1, hr2⟩, ?_⟩
          show (r : ZMod (p i)) - ((K * D : ℕ) : ZMod (p i)) =
            ((j * M + t : ℕ) : ZMod (p i))
          have h := congrArg (fun x : ℕ => (x : ZMod (p i))) hkey
          push_cast at h
          simp only [ZMod.natCast_self, mul_zero, zero_add] at h
          rw [h]
          push_cast
          ring
        simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, not_not]
        exact hmem
    have hcard : (blockSet K M L).card = K * L := blockSet_card hLltM
    have hKL : K * L ≤ (survivors N p
        (fun i => Finset.univ \ allowedSet (K * D) (p i))).card := by
      rw [← hcard]
      exact Finset.card_le_card hsub
    have h1 : N < K * M + M := by
      have hdiv := Nat.div_add_mod N M
      rw [← hKdef, mul_comm] at hdiv
      have hmod := Nat.mod_lt N hMpos
      omega
    have h3 : K * M ≤ 3 * (K * L) := by
      have h2 : M ≤ 3 * L := by omega
      calc K * M ≤ K * (3 * L) := Nat.mul_le_mul_left K h2
        _ = 3 * (K * L) := by ring
    rw [Nat.div_lt_iff_lt_mul (by norm_num : 0 < 10)]
    nlinarith [h1, h3, hMN, hKL]

end JSP001007
