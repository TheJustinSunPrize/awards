/-
Licensed under Apache-2.0; see LICENSE and NOTICE.
Adapted from Arthur Freitas Ramos, David Barros Hulak, and Ruy J. G. B. de Queiroz,
Arthur742Ramos/hadamard-668-lean at 78fbae8d69b6fdb66705b662469692d60e346ef0.
Modification: certify the distinct order-716 matrix with fresh certificate data.
Matrix discovery belongs to the original Alpoge/Voinov/Reynolds-Haertle team.
-/
import Hadamard716.ListCorrelationProof
import Mathlib

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Hadamard716

theorem hammingInt_append {xs ys us vs : List ℤ}
    (h : xs.length = ys.length) :
    hammingInt (xs ++ us) (ys ++ vs) =
      hammingInt xs ys + hammingInt us vs := by
  unfold hammingInt
  rw [List.zipWith_append h]
  simp [List.sum_append]

theorem hammingInt_rotate_common {xs ys : List ℤ}
    (hlen : xs.length = ys.length) (k : Nat) :
    hammingInt (xs.rotate k) (ys.rotate k) = hammingInt xs ys := by
  unfold hammingInt
  rw [← List.zipWith_rotate_distrib
    (fun x y : ℤ => if x == y then 0 else 1) xs ys k hlen]
  exact (List.rotate_perm _ _).sum_eq

def relativeOffset (d1 d2 : Bool) (n i j : Nat) : Nat :=
  if d1 then
    if d2 then (n - j) + i else j + i
  else
    if d2 then (n - j) + (n - i) else j + (n - i)

theorem hammingInt_shift_reduced {xs ys : List ℤ}
    (hx : xs.length = n) (hy : ys.length = n)
    (hi : i ≤ n) (d1 d2 : Bool) :
    hammingInt (shiftList d1 i xs) (shiftList d2 j ys) =
      hammingInt xs (ys.rotate (relativeOffset d1 d2 n i j)) := by
  cases d1 <;> cases d2
  · have h := hammingInt_rotate_common (xs := shiftList false i xs)
      (ys := shiftList false j ys) (k := n - i) (by simp [shiftList, hx, hy])
    have hxrot : xs.rotate n = xs := by simp [← hx]
    simpa [shiftList, relativeOffset, hx, hy, List.rotate_rotate,
      Nat.add_sub_of_le hi, hxrot] using h.symm
  · have h := hammingInt_rotate_common (xs := shiftList false i xs)
      (ys := shiftList true j ys) (k := n - i) (by simp [shiftList, hx, hy])
    have hxrot : xs.rotate n = xs := by simp [← hx]
    simpa [shiftList, relativeOffset, hx, hy, List.rotate_rotate,
      Nat.add_sub_of_le hi, hxrot] using h.symm
  · have h := hammingInt_rotate_common (xs := shiftList true i xs)
      (ys := shiftList false j ys) (k := i) (by simp [shiftList, hx, hy])
    have hxrot : xs.rotate n = xs := by simp [← hx]
    simpa [shiftList, relativeOffset, hx, hy, List.rotate_rotate,
      Nat.sub_add_cancel hi, hxrot] using h.symm
  · have h := hammingInt_rotate_common (xs := shiftList true i xs)
      (ys := shiftList true j ys) (k := i) (by simp [shiftList, hx, hy])
    have hxrot : xs.rotate n = xs := by simp [← hx]
    simpa [shiftList, relativeOffset, hx, hy, List.rotate_rotate,
      Nat.sub_add_cancel hi, hxrot] using h.symm

def baseDistanceList (a b q : Nat) (right : Bool) (k : Nat) : Nat :=
  (baseListTable a b q right)[k]!

def baseLookupList (a b q : Nat) (right : Bool) (k : Nat) : Nat :=
  (baseExpectedTable a b q right)[k % 178]!

theorem baseDistanceList_eq_hamming {a b q k : Nat} {right : Bool}
    (hk : k < 178) :
    baseDistanceList a b q right k =
      hammingInt ((bases716[a]!)[q]!)
        (shiftList right k ((bases716[b]!)[q]!)) := by
  simp [baseDistanceList, baseListTable, hk]

theorem baseDistanceList_eq_lookup {a b q k : Nat} {right : Bool}
    (ha : a < 4) (hb : b < 4) (hq : q < 4) (hk : k < 178) :
    baseDistanceList a b q right k = baseLookupList a b q right k := by
  interval_cases a <;> interval_cases b <;> interval_cases q <;>
    cases right <;>
    simp [baseDistanceList, baseLookupList, Nat.mod_eq_of_lt hk,
      baseListTable_0_0_0_left,
      baseListTable_0_0_0_right,
      baseListTable_0_0_1_left,
      baseListTable_0_0_1_right,
      baseListTable_0_0_2_left,
      baseListTable_0_0_2_right,
      baseListTable_0_0_3_left,
      baseListTable_0_0_3_right,
      baseListTable_0_1_0_left,
      baseListTable_0_1_0_right,
      baseListTable_0_1_1_left,
      baseListTable_0_1_1_right,
      baseListTable_0_1_2_left,
      baseListTable_0_1_2_right,
      baseListTable_0_1_3_left,
      baseListTable_0_1_3_right,
      baseListTable_0_2_0_left,
      baseListTable_0_2_0_right,
      baseListTable_0_2_1_left,
      baseListTable_0_2_1_right,
      baseListTable_0_2_2_left,
      baseListTable_0_2_2_right,
      baseListTable_0_2_3_left,
      baseListTable_0_2_3_right,
      baseListTable_0_3_0_left,
      baseListTable_0_3_0_right,
      baseListTable_0_3_1_left,
      baseListTable_0_3_1_right,
      baseListTable_0_3_2_left,
      baseListTable_0_3_2_right,
      baseListTable_0_3_3_left,
      baseListTable_0_3_3_right,
      baseListTable_1_0_0_left,
      baseListTable_1_0_0_right,
      baseListTable_1_0_1_left,
      baseListTable_1_0_1_right,
      baseListTable_1_0_2_left,
      baseListTable_1_0_2_right,
      baseListTable_1_0_3_left,
      baseListTable_1_0_3_right,
      baseListTable_1_1_0_left,
      baseListTable_1_1_0_right,
      baseListTable_1_1_1_left,
      baseListTable_1_1_1_right,
      baseListTable_1_1_2_left,
      baseListTable_1_1_2_right,
      baseListTable_1_1_3_left,
      baseListTable_1_1_3_right,
      baseListTable_1_2_0_left,
      baseListTable_1_2_0_right,
      baseListTable_1_2_1_left,
      baseListTable_1_2_1_right,
      baseListTable_1_2_2_left,
      baseListTable_1_2_2_right,
      baseListTable_1_2_3_left,
      baseListTable_1_2_3_right,
      baseListTable_1_3_0_left,
      baseListTable_1_3_0_right,
      baseListTable_1_3_1_left,
      baseListTable_1_3_1_right,
      baseListTable_1_3_2_left,
      baseListTable_1_3_2_right,
      baseListTable_1_3_3_left,
      baseListTable_1_3_3_right,
      baseListTable_2_0_0_left,
      baseListTable_2_0_0_right,
      baseListTable_2_0_1_left,
      baseListTable_2_0_1_right,
      baseListTable_2_0_2_left,
      baseListTable_2_0_2_right,
      baseListTable_2_0_3_left,
      baseListTable_2_0_3_right,
      baseListTable_2_1_0_left,
      baseListTable_2_1_0_right,
      baseListTable_2_1_1_left,
      baseListTable_2_1_1_right,
      baseListTable_2_1_2_left,
      baseListTable_2_1_2_right,
      baseListTable_2_1_3_left,
      baseListTable_2_1_3_right,
      baseListTable_2_2_0_left,
      baseListTable_2_2_0_right,
      baseListTable_2_2_1_left,
      baseListTable_2_2_1_right,
      baseListTable_2_2_2_left,
      baseListTable_2_2_2_right,
      baseListTable_2_2_3_left,
      baseListTable_2_2_3_right,
      baseListTable_2_3_0_left,
      baseListTable_2_3_0_right,
      baseListTable_2_3_1_left,
      baseListTable_2_3_1_right,
      baseListTable_2_3_2_left,
      baseListTable_2_3_2_right,
      baseListTable_2_3_3_left,
      baseListTable_2_3_3_right,
      baseListTable_3_0_0_left,
      baseListTable_3_0_0_right,
      baseListTable_3_0_1_left,
      baseListTable_3_0_1_right,
      baseListTable_3_0_2_left,
      baseListTable_3_0_2_right,
      baseListTable_3_0_3_left,
      baseListTable_3_0_3_right,
      baseListTable_3_1_0_left,
      baseListTable_3_1_0_right,
      baseListTable_3_1_1_left,
      baseListTable_3_1_1_right,
      baseListTable_3_1_2_left,
      baseListTable_3_1_2_right,
      baseListTable_3_1_3_left,
      baseListTable_3_1_3_right,
      baseListTable_3_2_0_left,
      baseListTable_3_2_0_right,
      baseListTable_3_2_1_left,
      baseListTable_3_2_1_right,
      baseListTable_3_2_2_left,
      baseListTable_3_2_2_right,
      baseListTable_3_2_3_left,
      baseListTable_3_2_3_right,
      baseListTable_3_3_0_left,
      baseListTable_3_3_0_right,
      baseListTable_3_3_1_left,
      baseListTable_3_3_1_right,
      baseListTable_3_3_2_left,
      baseListTable_3_3_2_right,
      baseListTable_3_3_3_left,
      baseListTable_3_3_3_right]

def topDistanceList (t a q k : Nat) : Nat :=
  (topListTable t a q)[k]!

def topLookupList (t a q k : Nat) : Nat :=
  (topExpectedTable t a q)[k % 178]!

theorem topDistanceList_eq_hamming {t a q k : Nat}
    (hk : k < 178) :
    topDistanceList t a q k =
      hammingInt (topChunkList t q)
        (shiftList ((dirs716[a]!)[q]!) k ((bases716[a]!)[q]!)) := by
  simp [topDistanceList, topListTable, hk]

theorem topDistanceList_eq_lookup {t a q k : Nat}
    (ht : t < 4) (ha : a < 4) (hq : q < 4) (hk : k < 178) :
    topDistanceList t a q k = topLookupList t a q k := by
  interval_cases t <;> interval_cases a <;> interval_cases q <;>
    simp [topDistanceList, topLookupList, Nat.mod_eq_of_lt hk,
      topListTable_0_0_0,
      topListTable_0_0_1,
      topListTable_0_0_2,
      topListTable_0_0_3,
      topListTable_0_1_0,
      topListTable_0_1_1,
      topListTable_0_1_2,
      topListTable_0_1_3,
      topListTable_0_2_0,
      topListTable_0_2_1,
      topListTable_0_2_2,
      topListTable_0_2_3,
      topListTable_0_3_0,
      topListTable_0_3_1,
      topListTable_0_3_2,
      topListTable_0_3_3,
      topListTable_1_0_0,
      topListTable_1_0_1,
      topListTable_1_0_2,
      topListTable_1_0_3,
      topListTable_1_1_0,
      topListTable_1_1_1,
      topListTable_1_1_2,
      topListTable_1_1_3,
      topListTable_1_2_0,
      topListTable_1_2_1,
      topListTable_1_2_2,
      topListTable_1_2_3,
      topListTable_1_3_0,
      topListTable_1_3_1,
      topListTable_1_3_2,
      topListTable_1_3_3,
      topListTable_2_0_0,
      topListTable_2_0_1,
      topListTable_2_0_2,
      topListTable_2_0_3,
      topListTable_2_1_0,
      topListTable_2_1_1,
      topListTable_2_1_2,
      topListTable_2_1_3,
      topListTable_2_2_0,
      topListTable_2_2_1,
      topListTable_2_2_2,
      topListTable_2_2_3,
      topListTable_2_3_0,
      topListTable_2_3_1,
      topListTable_2_3_2,
      topListTable_2_3_3,
      topListTable_3_0_0,
      topListTable_3_0_1,
      topListTable_3_0_2,
      topListTable_3_0_3,
      topListTable_3_1_0,
      topListTable_3_1_1,
      topListTable_3_1_2,
      topListTable_3_1_3,
      topListTable_3_2_0,
      topListTable_3_2_1,
      topListTable_3_2_2,
      topListTable_3_2_3,
      topListTable_3_3_0,
      topListTable_3_3_1,
      topListTable_3_3_2,
      topListTable_3_3_3]

def topPrefixList (t : Nat) : List ℤ :=
  (top716[t]!).take 4

def leftRowList (a : Nat) : List ℤ :=
  left716[a]!

def baseBlockList (a q : Nat) : List ℤ :=
  (bases716[a]!)[q]!

def directionBit (a q : Nat) : Bool :=
  (dirs716[a]!)[q]!

def topRowList (t : Nat) : List ℤ :=
  topPrefixList t ++ topChunkList t 0 ++ topChunkList t 1 ++
    topChunkList t 2 ++ topChunkList t 3

def coreRowList (a i : Nat) : List ℤ :=
  leftRowList a ++
    shiftList (directionBit a 0) i (baseBlockList a 0) ++
    shiftList (directionBit a 1) i (baseBlockList a 1) ++
    shiftList (directionBit a 2) i (baseBlockList a 2) ++
    shiftList (directionBit a 3) i (baseBlockList a 3)

def leftDistanceList (a b : Nat) : Nat :=
  hammingInt (leftRowList a) (leftRowList b)

def coreDistanceReducedList (a i b j : Nat) : Nat :=
  leftDistanceList a b +
    baseLookupList a b 0 false
      (relativeOffset (directionBit a 0) (directionBit b 0) 178 i j) +
    baseLookupList a b 1 false
      (relativeOffset (directionBit a 1) (directionBit b 1) 178 i j) +
    baseLookupList a b 2 false
      (relativeOffset (directionBit a 2) (directionBit b 2) 178 i j) +
    baseLookupList a b 3 false
      (relativeOffset (directionBit a 3) (directionBit b 3) 178 i j)

def topCoreDistanceList (t a i : Nat) : Nat :=
  hammingInt (topPrefixList t) (leftRowList a) +
    topLookupList t a 0 i + topLookupList t a 1 i +
    topLookupList t a 2 i + topLookupList t a 3 i

def topTopDistanceList (t u : Nat) : Nat :=
  hammingInt (topPrefixList t) (topPrefixList u) +
    hammingInt (topChunkList t 0) (topChunkList u 0) +
    hammingInt (topChunkList t 1) (topChunkList u 1) +
    hammingInt (topChunkList t 2) (topChunkList u 2) +
    hammingInt (topChunkList t 3) (topChunkList u 3)

def corePairCheckList (a b : Nat) : Bool :=
  (List.range 178).all (fun i =>
    (List.range 178).all (fun j =>
      if a < b || (a == b && i < j) then
        coreDistanceReducedList a i b j == 358
      else true))

def topCoreCheckList : Bool :=
  (List.range 4).all (fun t =>
    (List.range 4).all (fun a =>
      (List.range 178).all (fun i =>
        topCoreDistanceList t a i == 358)))

def topTopCheckList : Bool :=
  (List.range 4).all (fun t =>
    (List.range 4).all (fun u =>
      if t < u then topTopDistanceList t u == 358 else true))

end Hadamard716
