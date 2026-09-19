/- Local 20-vertex adaptation of PR #190, commit 4022d2df0f941a12f497d5045b75995e0cf8f883.
   Upstream formalization: jinkaizhang236-sketch / Justin Sun Prize contributors.
   Original mathematical construction: Paul W. Dyson and Brendan D. McKay.
   See THIRD_PARTY_NOTICES.md for exact reuse and changes. -/
import Graph20

namespace Graph20Proof
open RegularCertificate

def adjBits (v : Fin 20) : Nat :=
  match v.val with
  | 0 => 141312
  | 1 => 348160
  | 2 => 624128
  | 3 => 795008
  | 4 => 822368
  | 5 => 1002064
  | 6 => 959792
  | 7 => 881416
  | 8 => 760008
  | 9 => 447652
  | 10 => 772692
  | 11 => 894257
  | 12 => 1008514
  | 13 => 497865
  | 14 => 956066
  | 15 => 1011540
  | 16 => 966054
  | 17 => 915297
  | 18 => 785146
  | 19 => 515580
  | _ => 0

def decode (x : Nat) : Finset (Fin 20) := Finset.univ.filter (fun v => x.testBit v.val)
def full : Nat := 1048575

theorem mem_decode (x : Nat) (v : Fin 20) : v ∈ decode x ↔ x.testBit v.val = true := by
  simp [decode]

theorem decode_and (x y : Nat) : decode (x &&& y) = decode x ∩ decode y := by
  ext v
  simp [mem_decode, Nat.testBit_and]

theorem decode_or (x y : Nat) : decode (x ||| y) = decode x ∪ decode y := by
  ext v
  simp [mem_decode, Nat.testBit_or]

theorem full_bits : ∀ v : Fin 20, full.testBit v.val = true := by decide +kernel

theorem decode_diff (x y : Nat) : decode (x &&& (full ^^^ y)) = decode x \ decode y := by
  ext v
  simp [mem_decode, Nat.testBit_and, Nat.testBit_xor, full_bits]

theorem decode_bit (v : Fin 20) : decode (2 ^ v.val) = {v} := by
  ext w
  simp [mem_decode, Nat.testBit_two_pow, Fin.ext_iff, eq_comm]

theorem decode_adj : ∀ v : Fin 20, decode (adjBits v) = neighbors v := by decide +kernel

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

theorem bitcount_decode (x : Nat) : bitcount 20 0 x = (decode x).card := by
  simpa only [Nat.zero_add, decode] using bitcount_eq 20 0 x

def mdegree (S : Nat) (v : Fin 20) : Nat := bitcount 20 0 (adjBits v &&& S)

theorem mdegree_eq (S : Nat) (v : Fin 20) : mdegree S v = degree neighbors (decode S) v := by
  simp only [mdegree, bitcount_decode, decode_and, decode_adj, degree]

def mincompatible (d S U : Nat) (v : Fin 20) : Bool :=
  decide (d < mdegree S v ∨ mdegree U v < d)

def mcheck (k d S U : Nat) : Cert (Fin 20) → Bool
  | .small => decide (bitcount 20 0 U < k)
  | .bad v => S.testBit v.val && mincompatible d S U v
  | .drop v next => mincompatible d S U v && mcheck k d S (U &&& (full ^^^ (2^v.val))) next
  | .fill v next => (S.testBit v.val && decide (mdegree U v = d)) &&
      mcheck k d (S ||| (adjBits v &&& U)) U next
  | .empty v next => (S.testBit v.val && decide (mdegree S v = d)) &&
      mcheck k d S (U &&& (full ^^^ (adjBits v &&& (full ^^^ S)))) next
  | .split v yes no => mcheck k d (S ||| 2^v.val) U yes &&
      mcheck k d S (U &&& (full ^^^ (2^v.val))) no

theorem mcheck_eq (k d : Nat) (c : Cert (Fin 20)) : ∀ S U,
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

theorem mcheck_sound (d : Nat) (c : Cert (Fin 20)) (h : mcheck 6 d 0 full c = true)
    (T : Finset (Fin 20)) (hT : 6 ≤ T.card) : ¬ RegularOn neighbors T d := by
  have hc : check neighbors 6 d ∅ Finset.univ c = true := by
    simpa only [mcheck_eq, decode_zero, decode_full] using h
  exact check_sound neighbors 6 d c ∅ Finset.univ hc T (Finset.empty_subset T)
    (Finset.subset_univ T) hT

#print axioms mcheck_sound
end Graph20Proof
