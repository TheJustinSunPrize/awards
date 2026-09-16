import Graph29

namespace Erdos82Finite
open RegularCertificate

def adjBits (v : Fin 29) : Nat :=
  match v.val with
  | 0 => 67192832
  | 1 => 437784576
  | 2 => 73565184
  | 3 => 343952128
  | 4 => 517996672
  | 5 => 395583552
  | 6 => 488386592
  | 7 => 484606992
  | 8 => 465895944
  | 9 => 255150344
  | 10 => 427468932
  | 11 => 464274953
  | 12 => 533536834
  | 13 => 466556000
  | 14 => 389515785
  | 15 => 469451908
  | 16 => 509276929
  | 17 => 468575364
  | 18 => 530742112
  | 19 => 399752258
  | 20 => 535414370
  | 21 => 529976980
  | 22 => 261862804
  | 23 => 528398776
  | 24 => 486473568
  | 25 => 486538034
  | 26 => 469586685
  | 27 => 133677010
  | 28 => 130022906
  | _ => 0

def decode (x : Nat) : Finset (Fin 29) := Finset.univ.filter (fun v => x.testBit v.val)
def full : Nat := 536870911

theorem mem_decode (x : Nat) (v : Fin 29) : v ∈ decode x ↔ x.testBit v.val = true := by
  simp [decode]

theorem decode_and (x y : Nat) : decode (x &&& y) = decode x ∩ decode y := by
  ext v
  simp [mem_decode, Nat.testBit_and]

theorem decode_or (x y : Nat) : decode (x ||| y) = decode x ∪ decode y := by
  ext v
  simp [mem_decode, Nat.testBit_or]

theorem full_bits : ∀ v : Fin 29, full.testBit v.val = true := by decide +kernel

theorem decode_diff (x y : Nat) : decode (x &&& (full ^^^ y)) = decode x \ decode y := by
  ext v
  simp [mem_decode, Nat.testBit_and, Nat.testBit_xor, full_bits]

theorem decode_bit (v : Fin 29) : decode (2 ^ v.val) = {v} := by
  ext w
  simp [mem_decode, Nat.testBit_two_pow, Fin.ext_iff, eq_comm]

theorem decode_adj : ∀ v : Fin 29, decode (adjBits v) = neighbors v := by decide +kernel

theorem decode_zero : decode 0 = ∅ := by ext v; simp [mem_decode]
theorem decode_full : decode full = Finset.univ := by ext v; simp [mem_decode, full_bits]

def bitcount : Nat → Nat → Nat → Nat
  | 0, _, _ => 0
  | n + 1, offset, x => (if x.testBit offset then 1 else 0) + bitcount n (offset + 1) x

theorem bitcount_eq (n offset x : Nat) : bitcount n offset x =
    (Finset.univ.filter (fun v : Fin n => x.testBit (offset + v.val))).card := by
  induction n generalizing offset with
  | zero => simp [bitcount]
  | succ n ih =>
    rw [bitcount, Fin.card_filter_univ_succ']
    simp only [Fin.val_zero, Nat.add_zero, Fin.val_succ]
    rw [ih]
    congr 1
    congr 1
    ext v
    simp [Nat.add_comm, Nat.add_left_comm]

theorem bitcount_decode (x : Nat) : bitcount 29 0 x = (decode x).card := by
  simpa only [Nat.zero_add, decode] using bitcount_eq 29 0 x

def mdegree (S : Nat) (v : Fin 29) : Nat := bitcount 29 0 (adjBits v &&& S)

theorem mdegree_eq (S : Nat) (v : Fin 29) : mdegree S v = degree neighbors (decode S) v := by
  simp only [mdegree, bitcount_decode, decode_and, decode_adj, degree]

def mincompatible (d S U : Nat) (v : Fin 29) : Bool :=
  decide (d < mdegree S v ∨ mdegree U v < d)

def mcheck (k d S U : Nat) : Cert (Fin 29) → Bool
  | .small => decide (bitcount 29 0 U < k)
  | .bad v => S.testBit v.val && mincompatible d S U v
  | .drop v next => mincompatible d S U v && mcheck k d S (U &&& (full ^^^ (2^v.val))) next
  | .fill v next => (S.testBit v.val && decide (mdegree U v = d)) &&
      mcheck k d (S ||| (adjBits v &&& U)) U next
  | .empty v next => (S.testBit v.val && decide (mdegree S v = d)) &&
      mcheck k d S (U &&& (full ^^^ (adjBits v &&& (full ^^^ S)))) next
  | .split v yes no => mcheck k d (S ||| 2^v.val) U yes &&
      mcheck k d S (U &&& (full ^^^ (2^v.val))) no

theorem mcheck_eq (k d : Nat) (c : Cert (Fin 29)) : ∀ S U,
    mcheck k d S U c = check neighbors k d (decode S) (decode U) c := by
  induction c with
  | small => intro S U; simp only [mcheck, check, bitcount_decode]
  | bad v =>
    intro S U
    simp [mcheck, check, mincompatible, incompatible, mdegree_eq, mem_decode]
  | drop v next ih =>
    intro S U
    simp [mcheck, check, mincompatible, incompatible, mdegree_eq, ih, decode_diff, decode_bit, Finset.sdiff_singleton_eq_erase]
  | fill v next ih =>
    intro S U
    simp [mcheck, check, mdegree_eq, ih, decode_or,
      decode_and, decode_adj, mem_decode]
  | empty v next ih =>
    intro S U
    simp [mcheck, check, mdegree_eq, ih, decode_diff,
      decode_adj, mem_decode]
  | split v yes no ihy ihn =>
    intro S U
    simp [mcheck, check, ihy, ihn, decode_or, decode_bit, decode_diff,
      Finset.sdiff_singleton_eq_erase]

theorem mcheck_sound (d : Nat) (c : Cert (Fin 29)) (h : mcheck 7 d 0 full c = true)
    (T : Finset (Fin 29)) (hT : 7 ≤ T.card) : ¬ RegularOn neighbors T d := by
  have hc : check neighbors 7 d ∅ Finset.univ c = true := by
    simpa only [mcheck_eq, decode_zero, decode_full] using h
  exact check_sound neighbors 7 d c ∅ Finset.univ hc T (Finset.empty_subset T)
    (Finset.subset_univ T) hT

#print axioms mcheck_sound
end Erdos82Finite
