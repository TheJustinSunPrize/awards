import KorskyBalancedDefs
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.Sum
import Mathlib.Tactic.FinCases

/-! Cardinality of the balanced part of Samuel Korsky's ordered ternary family.
The proof encodes even Boolean supports and uses a parity-determined first bit. -/
namespace Erdos882Korsky

private abbrev Bits (k : ℕ) := Fin k → Bool
private def bitCount {k : ℕ} (b : Bits k) : ℕ := ∑ i, if b i then 1 else 0
private def zeroCount {k : ℕ} (w : Word k) : ℕ := ∑ i, if w i = 0 then 1 else 0
private def supportBits {k : ℕ} (w : Word k) : Bits k := fun i => decide (w i ≠ 1)

private lemma bitCount_cons {k : ℕ} (h : Bool) (b : Bits k) :
    bitCount (Fin.cons h b) = (if h then 1 else 0) + bitCount b := by
  unfold bitCount
  rw [Fin.sum_univ_succ]
  simp

private lemma zeroCount_cons {k : ℕ} (h : Fin 3) (w : Word k) :
    zeroCount (Fin.cons h w) = (if h = 0 then 1 else 0) + zeroCount w := by
  unfold zeroCount
  rw [Fin.sum_univ_succ]
  simp

private lemma supportBits_cons {k : ℕ} (h : Fin 3) (w : Word k) :
    supportBits (Fin.cons h w) = Fin.cons (decide (h ≠ 1)) (supportBits w) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i <;> simp [supportBits]

private lemma sum_zero_support {k : ℕ} (w : Word k) :
    (∑ i, (w i).val) + 2 * zeroCount w = k + bitCount (supportBits w) := by
  calc
    _ = ∑ i, ((w i).val + 2 * (if w i = 0 then 1 else 0)) := by
      unfold zeroCount
      rw [Finset.mul_sum, Finset.sum_add_distrib]
    _ = ∑ i, (1 + if w i ≠ 1 then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro i _
      generalize w i = x
      fin_cases x <;> norm_num
    _ = k + bitCount (supportBits w) := by
      simp [bitCount, supportBits, Finset.sum_add_distrib]

private lemma zeroCount_eq_zero_iff {k : ℕ} (w : Word k) :
    zeroCount w = 0 ↔ ∀ i, w i ≠ 0 := by
  simp [zeroCount]

private lemma ordered_cons_iff {k : ℕ} (h : Fin 3) (w : Word k) :
    Ordered (Fin.cons h w) ↔ Ordered w ∧ (h = 2 → ∀ i, w i ≠ 0) := by
  constructor
  · intro hw
    constructor
    · intro i j hij hi
      exact hw i.succ j.succ (by simpa using hij) (by simpa using hi)
    · intro hh i
      exact hw 0 i.succ (by simp) (by simpa using hh)
  · rintro ⟨hw, hh⟩ i
    refine Fin.cases ?_ (fun i => ?_) i
    · intro j
      refine Fin.cases ?_ (fun j => ?_) j
      · simp
      · intro hij hi
        exact hh (by simpa using hi) j
    · intro j
      refine Fin.cases ?_ (fun j => ?_) j
      · simp
      · intro hij hi
        exact hw i j (by simpa using hij) (by simpa using hi)

private def encode : {k : ℕ} → ℕ → Bits k → Word k
  | 0, _, _ => Fin.elim0
  | k+1, r, b =>
    if b 0 then
      match r with
      | 0 => Fin.cons 2 (encode 0 (fun i : Fin k => b i.succ))
      | r+1 => Fin.cons 0 (encode r (fun i : Fin k => b i.succ))
    else Fin.cons 1 (encode r (fun i : Fin k => b i.succ))

private lemma encode_succ {k : ℕ} (r : ℕ) (b : Bits (k+1)) :
    encode r b =
      if b 0 then
        match r with
        | 0 => Fin.cons 2 (encode 0 (fun i : Fin k => b i.succ))
        | r+1 => Fin.cons 0 (encode r (fun i : Fin k => b i.succ))
      else Fin.cons 1 (encode r (fun i : Fin k => b i.succ)) := rfl

private lemma support_encode {k : ℕ} (r : ℕ) (b : Bits k) :
    supportBits (encode r b) = b := by
  induction k generalizing r with
  | zero => exact Subsingleton.elim _ _
  | succ k ih =>
    by_cases hb : b 0 = true
    · cases r with
      | zero =>
        rw [encode_succ, ite_eq_left hb, supportBits_cons, ih]
        funext i
        refine Fin.cases ?_ (fun i => ?_) i <;> simp [hb]
      | succ r =>
        rw [encode_succ, ite_eq_left hb, supportBits_cons, ih]
        funext i
        refine Fin.cases ?_ (fun i => ?_) i <;> simp [hb]
    · rw [encode_succ, ite_eq_right hb, supportBits_cons, ih]
      funext i
      refine Fin.cases ?_ (fun i => ?_) i <;> simp [hb]

private lemma zeroCount_encode {k : ℕ} (r : ℕ) (b : Bits k) :
    zeroCount (encode r b) = min r (bitCount b) := by
  induction k generalizing r with
  | zero => simp [encode, zeroCount, bitCount]
  | succ k ih =>
    have hc : bitCount b = (if b 0 then 1 else 0) + bitCount (fun i : Fin k => b i.succ) := by
      unfold bitCount
      rw [Fin.sum_univ_succ]
    by_cases hb : b 0 = true
    · cases r with
      | zero => simp [encode, hb, zeroCount_cons, ih]
      | succ r =>
        simp only [encode, hb, zeroCount_cons, ite_true, ih]
        rw [hc]
        simp only [hb, ite_true]
        omega
    · simp [encode, hb, zeroCount_cons, ih, hc]

private lemma ordered_encode {k : ℕ} (r : ℕ) (b : Bits k) :
    Ordered (encode r b) := by
  induction k generalizing r with
  | zero => intro i; exact Fin.elim0 i
  | succ k ih =>
    by_cases hb : b 0 = true
    · cases r with
      | zero =>
        rw [encode_succ, ite_eq_left hb, ordered_cons_iff]
        refine ⟨ih 0 _, ?_⟩
        intro _
        apply (zeroCount_eq_zero_iff _).mp
        simp [zeroCount_encode]
      | succ r =>
        rw [encode_succ, ite_eq_left hb, ordered_cons_iff]
        exact ⟨ih r _, by norm_num⟩
    · rw [encode_succ, ite_eq_right hb, ordered_cons_iff]
      exact ⟨ih r _, by norm_num⟩

private lemma encode_reconstruct {k : ℕ} (w : Word k) (hw : Ordered w) :
    encode (zeroCount w) (supportBits w) = w := by
  induction k with
  | zero => exact Subsingleton.elim _ _
  | succ k ih =>
    let t : Word k := fun i => w i.succ
    have hwcons : w = Fin.cons (w 0) t := by
      funext i
      refine Fin.cases ?_ (fun i => ?_) i <;> simp [t]
    rw [hwcons] at hw ⊢
    have ht := (ordered_cons_iff _ _).mp hw
    rw [zeroCount_cons, supportBits_cons]
    generalize h0 : w 0 = c at ht ⊢
    fin_cases c
    · change encode (1 + zeroCount t) (Fin.cons true (supportBits t)) = Fin.cons 0 t
      rw [Nat.add_comm 1, encode_succ]
      simp [ih t ht.1]
    · simp [encode, ih t ht.1]
    · have hz : zeroCount t = 0 := (zeroCount_eq_zero_iff t).mpr (ht.2 rfl)
      have hir := ih t ht.1
      rw [hz] at hir
      simp [encode, hz, hir]

private abbrev EvenBits (k : ℕ) := {b : Bits k // bitCount b % 2 = 0}

private def balancedEncode (k : ℕ) (b : EvenBits k) :
    {w : Word k // Balanced w} :=
  ⟨encode (bitCount b.val / 2) b.val, ordered_encode _ _, by
    have hs := sum_zero_support (encode (bitCount b.val / 2) b.val)
    rw [support_encode, zeroCount_encode, min_eq_left (Nat.div_le_self _ _)] at hs
    have hm := b.property
    omega⟩

private lemma balancedEncode_injective (k : ℕ) : Function.Injective (balancedEncode k) := by
  intro x y h
  apply Subtype.ext
  have hv := congrArg (fun z : {w : Word k // Balanced w} => supportBits z.val) h
  simpa only [balancedEncode, support_encode] using hv

private lemma balancedEncode_surjective (k : ℕ) : Function.Surjective (balancedEncode k) := by
  intro w
  have hs := sum_zero_support w.val
  have hw := w.property.2
  have hn : bitCount (supportBits w.val) = 2 * zeroCount w.val := by omega
  let b : EvenBits k := ⟨supportBits w.val, by rw [hn]; omega⟩
  refine ⟨b, ?_⟩
  apply Subtype.ext
  change encode (bitCount b.val / 2) b.val = w.val
  have hr : bitCount b.val / 2 = zeroCount w.val := by dsimp [b]; omega
  rw [hr]
  exact encode_reconstruct w.val w.property.1

private lemma parity_even {k : ℕ} (b : Bits k) :
    bitCount (Fin.cons (decide (bitCount b % 2 = 1)) b) % 2 = 0 := by
  rw [bitCount_cons]
  by_cases h : bitCount b % 2 = 1
  · simp only [h, decide_true, ite_true]
    omega
  · simp only [h, decide_false, Bool.false_eq_true, ite_false]
    omega

private def parityEncode (k : ℕ) (b : Bits k) : EvenBits (k+1) :=
  ⟨Fin.cons (decide (bitCount b % 2 = 1)) b, parity_even b⟩

private lemma parityEncode_injective (k : ℕ) : Function.Injective (parityEncode k) := by
  intro x y h
  funext i
  have hv := congrFun (congrArg Subtype.val h) i.succ
  simpa only [parityEncode, Fin.cons_succ] using hv

private lemma parityEncode_surjective (k : ℕ) : Function.Surjective (parityEncode k) := by
  intro b
  let t : Bits k := fun i => b.val i.succ
  have hbcons : b.val = Fin.cons (b.val 0) t := by
    funext i
    refine Fin.cases ?_ (fun i => ?_) i <;> simp [t]
  have hm := b.property
  rw [hbcons, bitCount_cons] at hm
  have hh : decide (bitCount t % 2 = 1) = b.val 0 := by
    cases h : b.val 0
    · simp only [h, Bool.false_eq_true, ite_false, zero_add] at hm
      simp [hm]
    · simp only [h, ite_true] at hm
      have hp : bitCount t % 2 = 1 := by omega
      simp [hp]
  refine ⟨t, ?_⟩
  apply Subtype.ext
  change Fin.cons (decide (bitCount t % 2 = 1)) t = b.val
  rw [hh, ← hbcons]

private lemma evenBits_card_succ (k : ℕ) : Fintype.card (EvenBits (k+1)) = 2^k := by
  have h := Fintype.card_of_bijective (f := parityEncode k)
    ⟨parityEncode_injective k, parityEncode_surjective k⟩
  simpa only [Bits, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin] using h.symm

theorem balanced_card (k : ℕ) (hk : 0 < k) :
    Fintype.card {w : Word k // Balanced w} = 2^(k-1) := by
  cases k with
  | zero => omega
  | succ k =>
    have h := Fintype.card_of_bijective (f := balancedEncode (k+1))
      ⟨balancedEncode_injective (k+1), balancedEncode_surjective (k+1)⟩
    rw [← h, evenBits_card_succ]
    simp

end Erdos882Korsky
