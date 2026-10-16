/-
Interval counterexample for a short cluster of primes.

If `k` primes lie in an interval `[B, B + H)` and `H` is small compared with `B`,
the integers `q B + r` with `r` in a long initial half-interval avoid an upper
half of the residue classes modulo every one of those primes. The resulting
set is a positive-density subset of `[1, N]`. This is the Price–GPT-5.4 Pro
construction, written out for explicit parameters.
-/

import Mathlib.Data.Finset.Card
import Mathlib.Data.ZMod.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic

open Finset

namespace JSP001007

variable {p : ℕ} [NeZero p]

/-- Residue classes in the upper half of `0, …, p - 1`. -/
def upperHalf (p : ℕ) [NeZero p] : Finset (ZMod p) :=
  univ.filter fun a => (p + 1) / 2 ≤ a.val

lemma card_lowHalf {p : ℕ} [NeZero p] :
    (univ.filter fun a : ZMod p => a.val < (p + 1) / 2).card = (p + 1) / 2 := by
  classical
  let half := (p + 1) / 2
  have hinj : Function.Injective fun i : Fin half => (i.1 : ZMod p) := by
    intro a b h
    have ha : a.1 < p := by
      have : a.1 < half := a.2
      omega
    have hb : b.1 < p := by
      have : b.1 < half := b.2
      omega
    have hval := congrArg ZMod.val h
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt ha, ZMod.val_natCast, Nat.mod_eq_of_lt hb] at hval
    exact Fin.ext hval
  have himage :
      (univ.filter fun a : ZMod p => a.val < half) =
        (univ : Finset (Fin half)).image fun i => (i.1 : ZMod p) := by
    ext a
    constructor
    · intro ha
      rw [mem_image]
      have hv : a.val < half := (mem_filter.mp ha).2
      exact ⟨⟨a.val, hv⟩, mem_univ _, by simp⟩
    · intro ha
      obtain ⟨i, -, hi⟩ := mem_image.mp ha
      have hi' : (i.1 : ZMod p) = a := hi
      have hval : a.val = i.1 := by
        have hiLt : i.1 < p := by
          have : i.1 < half := i.2
          omega
        have := congrArg ZMod.val hi'
        rw [ZMod.val_natCast, Nat.mod_eq_of_lt hiLt] at this
        exact this.symm
      rw [mem_filter, hval]
      exact ⟨mem_univ _, i.2⟩
  rw [himage, card_image_of_injective _ hinj, card_univ, Fintype.card_fin]

lemma upperHalf_card {p : ℕ} [NeZero p] (hp : p.Prime) (h2 : 2 < p) :
    (upperHalf p).card = (p - 1) / 2 := by
  have hcompl :
      upperHalf p = univ \ univ.filter fun a : ZMod p => a.val < (p + 1) / 2 := by
    ext a
    simp only [upperHalf, mem_filter, mem_univ, true_and, mem_sdiff, not_lt]
  rw [hcompl, card_sdiff_of_subset (filter_subset _ _), card_univ, ZMod.card, card_lowHalf]
  obtain ⟨m, hm⟩ := hp.odd_of_ne_two (by omega)
  rw [hm]
  omega

/-- `q B + r` for `0 ≤ q < Q` and `lo ≤ r ≤ hi`. -/
def blockSet (B Q lo hi : ℕ) : Finset ℕ :=
  (range Q ×ˢ Icc lo hi).image fun qr => B * qr.1 + qr.2

lemma blockSet_card {B Q lo hi : ℕ} (hB : hi < B) (_hlo : lo ≤ hi) :
    (blockSet B Q lo hi).card = Q * (hi + 1 - lo) := by
  classical
  have hB0 : 0 < B := by omega
  have hinj : Set.InjOn (fun qr : ℕ × ℕ => B * qr.1 + qr.2) ↑(range Q ×ˢ Icc lo hi) := by
    intro a ha b hb h
    have ha2 : a.2 < B := by
      have hr : a.2 ≤ hi := (mem_Icc.mp (mem_product.mp ha).2).2
      omega
    have hb2 : b.2 < B := by
      have hr : b.2 ≤ hi := (mem_Icc.mp (mem_product.mp hb).2).2
      omega
    have hmod := congrArg (fun n => n % B) h
    have hsecond : a.2 = b.2 := by
      simpa [Nat.add_mod, Nat.mul_mod_right, Nat.zero_mod, Nat.mod_eq_of_lt ha2,
        Nat.mod_eq_of_lt hb2] using hmod
    have hfirst : a.1 = b.1 := by
      have hmul : B * a.1 + a.2 = B * b.1 + a.2 := by simpa [hsecond] using h
      exact Nat.eq_of_mul_eq_mul_left hB0 (Nat.add_right_cancel hmul)
    exact Prod.ext hfirst hsecond
  rw [blockSet, card_image_of_injOn hinj, card_product, card_range, Nat.card_Icc]

lemma block_residue_le_half {B H Q M p q r : ℕ}
    (hB : 0 < B) (hpB : B ≤ p) (hpH : p < B + H) (hq : q < Q)
    (hQH : (Q - 1) * H ≤ M / 16) (hrlo : M / 16 ≤ r) (hrhi : r ≤ (B - 1) / 2)
    (_hp : p.Prime) (hp2 : 2 < p) :
    (q * B + r) % p ≤ (p - 1) / 2 := by
  have hd : p - B < H := by omega
  have hqd : q * (p - B) ≤ (Q - 1) * (H - 1) := by
    have hqle : q ≤ Q - 1 := by omega
    have hdle : p - B ≤ H - 1 := by omega
    exact Nat.mul_le_mul hqle hdle
  have hsmall : q * (p - B) ≤ M / 16 := hqd.trans (by
    have hH : (Q - 1) * (H - 1) ≤ (Q - 1) * H := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
    exact hH.trans hQH)
  have hqdr : q * (p - B) ≤ r := hsmall.trans hrlo
  have hhalf : (B - 1) / 2 ≤ (p - 1) / 2 := Nat.div_le_div_right (by omega)
  have hremp : r - q * (p - B) < p := by
    have hr : r ≤ (p - 1) / 2 := hrhi.trans hhalf
    omega
  have hrewrite : q * B + r = q * p + (r - q * (p - B)) := by
    have hp_split : B + (p - B) = p := Nat.add_sub_of_le hpB
    calc
      q * B + r = q * B + (q * (p - B) + (r - q * (p - B))) := by
        rw [Nat.add_sub_of_le hqdr]
      _ = q * B + q * (p - B) + (r - q * (p - B)) := by omega
      _ = q * (B + (p - B)) + (r - q * (p - B)) := by rw [Nat.mul_add]
      _ = q * p + (r - q * (p - B)) := by rw [hp_split]
  have hmod : (q * p + (r - q * (p - B))) % p = r - q * (p - B) := by
    rw [Nat.mul_comm q p, Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hremp]
  rw [hrewrite, hmod]
  exact (Nat.sub_le _ _).trans (hrhi.trans hhalf)

lemma not_mem_upperHalf_of_mod_le {p x : ℕ} [NeZero p] (hp : p.Prime)
    (hx : x % p ≤ (p - 1) / 2) :
    (x : ZMod p) ∉ upperHalf p := by
  simp only [upperHalf, mem_filter, mem_univ, true_and, ZMod.val_natCast, not_le]
  have hstep : (p - 1) / 2 + 1 = (p + 1) / 2 := by
    have h1 : (p - 1) + 1 = p := Nat.sub_add_cancel hp.pos
    have h2 : (1 : ℕ) + 1 = 2 := by norm_num
    have hsum : (p - 1) + 2 = p + 1 := by
      calc
        (p - 1) + 2 = (p - 1) + (1 + 1) := by rw [← h2]
        _ = (p - 1) + 1 + 1 := by rw [← Nat.add_assoc]
        _ = p + 1 := by rw [h1]
    have hdiv :=
      Nat.add_div_of_dvd_left (a := p - 1) (b := 2) (c := 2) (dvd_refl 2)
    rw [hsum, show (2 : ℕ) / 2 = 1 by norm_num] at hdiv
    exact hdiv.symm
  have hlt : x % p < (p - 1) / 2 + 1 := Nat.lt_succ_of_le hx
  simpa [hstep] using hlt

end JSP001007
