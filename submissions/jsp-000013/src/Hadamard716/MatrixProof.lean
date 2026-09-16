/-
Licensed under Apache-2.0; see LICENSE and NOTICE.
Adapted from Arthur Freitas Ramos, David Barros Hulak, and Ruy J. G. B. de Queiroz,
Arthur742Ramos/hadamard-668-lean at 78fbae8d69b6fdb66705b662469692d60e346ef0.
Modification: certify the distinct order-716 matrix with fresh certificate data.
Matrix discovery belongs to the original Alpoge/Voinov/Reynolds-Haertle team.
-/
import Hadamard716.CompactDistanceProof

set_option maxHeartbeats 0
set_option maxRecDepth 100000

open scoped BigOperators

namespace Hadamard716

theorem topPrefixList_length {t : Nat} (ht : t < 4) :
    (topPrefixList t).length = 4 := by
  interval_cases t <;> decide +kernel

theorem topChunkList_length {t q : Nat} (ht : t < 4) (hq : q < 4) :
    (topChunkList t q).length = 178 := by
  interval_cases t <;> interval_cases q <;> decide +kernel

theorem leftRowList_length {a : Nat} (ha : a < 4) :
    (leftRowList a).length = 4 := by
  interval_cases a <;> decide +kernel

theorem baseBlockList_length {a q : Nat} (ha : a < 4) (hq : q < 4) :
    (baseBlockList a q).length = 178 := by
  interval_cases a <;> interval_cases q <;> decide +kernel

theorem topRowList_length {t : Nat} (ht : t < 4) :
    (topRowList t).length = 716 := by
  have h0 := topChunkList_length ht (by omega : 0 < 4)
  have h1 := topChunkList_length ht (by omega : 1 < 4)
  have h2 := topChunkList_length ht (by omega : 2 < 4)
  have h3 := topChunkList_length ht (by omega : 3 < 4)
  simp [topRowList, topPrefixList_length ht, h0, h1, h2, h3]

theorem coreRowList_length {a i : Nat} (ha : a < 4) :
    (coreRowList a i).length = 716 := by
  have h0 := baseBlockList_length ha (by omega : 0 < 4)
  have h1 := baseBlockList_length ha (by omega : 1 < 4)
  have h2 := baseBlockList_length ha (by omega : 2 < 4)
  have h3 := baseBlockList_length ha (by omega : 3 < 4)
  have hs0 : (shiftList (directionBit a 0) i (baseBlockList a 0)).length = 178 := by
    unfold shiftList
    split <;> simp [List.length_rotate, h0]
  have hs1 : (shiftList (directionBit a 1) i (baseBlockList a 1)).length = 178 := by
    unfold shiftList
    split <;> simp [List.length_rotate, h1]
  have hs2 : (shiftList (directionBit a 2) i (baseBlockList a 2)).length = 178 := by
    unfold shiftList
    split <;> simp [List.length_rotate, h2]
  have hs3 : (shiftList (directionBit a 3) i (baseBlockList a 3)).length = 178 := by
    unfold shiftList
    split <;> simp [List.length_rotate, h3]
  simp [coreRowList, leftRowList_length ha, hs0, hs1, hs2, hs3]

theorem coreDistance_from_pair {a b i j : Nat}
    (hpair : corePairCheckList a b = true)
    (hi : i < 178) (hj : j < 178)
    (hcond : (decide (a < b) || (a == b && decide (i < j))) = true) :
    coreDistanceReducedList a i b j = 358 := by
  have hrow := (List.all_eq_true.mp hpair) i (by simp [hi])
  have hcell := (List.all_eq_true.mp hrow) j (by simp [hj])
  have hbeq : (coreDistanceReducedList a i b j == 358) = true := by
    rw [if_pos hcond] at hcell
    exact hcell
  exact beq_iff_eq.mp hbeq

theorem coreDistance_reduced_358 {a b i j : Nat}
    (ha : a < 4) (hb : b < 4)
    (hi : i < 178) (hj : j < 178)
    (hcond : a < b ∨ (a = b ∧ i < j)) :
    coreDistanceReducedList a i b j = 358 := by
  have hcondBool :
      (decide (a < b) || (a == b && decide (i < j))) = true := by
    rcases hcond with hab | ⟨hab, hij⟩
    · simp [hab]
    · subst b
      simp [hij]
  interval_cases a
  · interval_cases b
    · exact coreDistance_from_pair corePairList_0_0 hi hj hcondBool
    · exact coreDistance_from_pair corePairList_0_1 hi hj hcondBool
    · exact coreDistance_from_pair corePairList_0_2 hi hj hcondBool
    · exact coreDistance_from_pair corePairList_0_3 hi hj hcondBool
  · interval_cases b
    · simp at hcondBool
    · exact coreDistance_from_pair corePairList_1_1 hi hj hcondBool
    · exact coreDistance_from_pair corePairList_1_2 hi hj hcondBool
    · exact coreDistance_from_pair corePairList_1_3 hi hj hcondBool
  · interval_cases b
    · simp at hcondBool
    · simp at hcondBool
    · exact coreDistance_from_pair corePairList_2_2 hi hj hcondBool
    · exact coreDistance_from_pair corePairList_2_3 hi hj hcondBool
  · interval_cases b
    · simp at hcondBool
    · simp at hcondBool
    · simp at hcondBool
    · exact coreDistance_from_pair corePairList_3_3 hi hj hcondBool

def intDot (xs ys : List ℤ) : ℤ :=
  (xs.zipWith (fun x y => x * y) ys).sum

theorem intDot_cons (x y : ℤ) (xs ys : List ℤ) :
    intDot (x :: xs) (y :: ys) = x * y + intDot xs ys := by
  rfl

theorem hammingInt_cons (x y : ℤ) (xs ys : List ℤ) :
    hammingInt (x :: xs) (y :: ys) =
      (if x == y then 0 else 1) + hammingInt xs ys := by
  rfl

theorem fin_sum_intDot {xs ys : List ℤ} {n : Nat}
    (hx : xs.length = n) (hy : ys.length = n) :
    (∑ i : Fin n, xs[i.1]! * ys[i.1]!) = intDot xs ys := by
  subst n
  induction xs generalizing ys with
  | nil => simp [intDot]
  | cons x xs ih =>
      cases ys with
      | nil => simp at hy
      | cons y ys =>
          simp only [List.length_cons] at hy ⊢
          rw [Fin.sum_univ_succ]
          have hget : ∀ i : Fin xs.length,
              (y :: ys)[i.succ.val]! = ys[i.val]! := by
            intro i
            have hxy : xs.length = ys.length := by omega
            have hleft : i.succ.val < (y :: ys).length := by
              simpa [hxy] using i.succ.isLt
            have hright : i.val < ys.length := by
              simpa [hxy] using i.isLt
            rw [getElem!_pos (y :: ys) i.succ.val hleft]
            rw [getElem!_pos ys i.val hright]
            rfl
          simp only [Fin.val_zero]
          simp only [hget]
          simp only [intDot]
          rw [List.zipWith]
          congr 1
          apply ih
          omega

theorem intDot_hamming_signs {xs ys : List ℤ}
    (hx : ∀ x ∈ xs, x = -1 ∨ x = 1)
    (hy : ∀ y ∈ ys, y = -1 ∨ y = 1)
    (h : xs.length = ys.length) :
    intDot xs ys = (xs.length : ℤ) - 2 * hammingInt xs ys := by
  induction xs generalizing ys with
  | nil => simp [intDot, hammingInt]
  | cons x xs ih =>
      cases ys with
      | nil => simp at h
      | cons y ys =>
          simp only [List.length_cons] at h ⊢
          have hx' := hx x (by simp)
          have hy' := hy y (by simp)
          have hxs : ∀ z ∈ xs, z = -1 ∨ z = 1 := by
            intro z hz
            exact hx z (by simp [hz])
          have hys : ∀ z ∈ ys, z = -1 ∨ z = 1 := by
            intro z hz
            exact hy z (by simp [hz])
          have ih' := ih hxs hys (by omega)
          have hlenz : (xs.length : ℤ) = (ys.length : ℤ) := by
            exact_mod_cast (by omega : xs.length = ys.length)
          rcases hx' with rfl | rfl <;> rcases hy' with rfl | rfl <;>
            rw [intDot_cons, hammingInt_cons, ih'] <;>
            simp [hlenz] <;>
            ring

def signOK (x : ℤ) : Bool := x == -1 || x == 1

theorem signs_of_all {xs : List ℤ}
    (h : xs.all signOK = true) : ∀ x ∈ xs, x = -1 ∨ x = 1 := by
  intro x hx
  have h' := (List.all_eq_true.mp h) x hx
  simpa [signOK] using h'

theorem signs_of_rotate {xs : List ℤ}
    (h : ∀ x ∈ xs, x = -1 ∨ x = 1) (k : Nat) :
    ∀ x ∈ xs.rotate k, x = -1 ∨ x = 1 := by
  intro x hx
  exact h x (List.mem_rotate.mp hx)

theorem signs_of_shift {xs : List ℤ}
    (h : ∀ x ∈ xs, x = -1 ∨ x = 1) (right : Bool) (k : Nat) :
    ∀ x ∈ shiftList right k xs, x = -1 ∨ x = 1 := by
  cases right
  · simpa [shiftList] using signs_of_rotate h k
  · simpa [shiftList] using signs_of_rotate h (xs.length - k)

theorem source_signs_top {t : Nat} (ht : t < 4) :
    ∀ x ∈ topRowList t, x = -1 ∨ x = 1 := by
  have h : (topRowList t).all signOK = true := by
    interval_cases t <;> decide +kernel
  exact signs_of_all h

theorem source_signs_left {a : Nat} (ha : a < 4) :
    ∀ x ∈ leftRowList a, x = -1 ∨ x = 1 := by
  have h : (leftRowList a).all signOK = true := by
    interval_cases a <;> decide +kernel
  exact signs_of_all h

theorem source_signs_base {a q : Nat} (ha : a < 4) (hq : q < 4) :
    ∀ x ∈ baseBlockList a q, x = -1 ∨ x = 1 := by
  have h : (baseBlockList a q).all signOK = true := by
    interval_cases a <;> interval_cases q <;> decide +kernel
  exact signs_of_all h

theorem source_signs_core {a i : Nat} (ha : a < 4) :
    ∀ x ∈ coreRowList a i, x = -1 ∨ x = 1 := by
  intro x hx
  simp only [coreRowList, List.mem_append] at hx
  rcases hx with (((hleft | h0) | h1) | h2) | h3
  · exact source_signs_left ha x hleft
  · exact signs_of_shift (source_signs_base ha (by omega)) _ _ x h0
  · exact signs_of_shift (source_signs_base ha (by omega)) _ _ x h1
  · exact signs_of_shift (source_signs_base ha (by omega)) _ _ x h2
  · exact signs_of_shift (source_signs_base ha (by omega)) _ _ x h3

theorem base_shift_distance_eq_lookup {a b q i j : Nat}
    (ha : a < 4) (hb : b < 4) (hq : q < 4)
    (hi : i < 178) :
    hammingInt (shiftList (directionBit a q) i (baseBlockList a q))
        (shiftList (directionBit b q) j (baseBlockList b q)) =
      baseLookupList a b q false
        (relativeOffset (directionBit a q) (directionBit b q) 178 i j) := by
  let r := relativeOffset (directionBit a q) (directionBit b q) 178 i j
  have hred := hammingInt_shift_reduced
    (xs := baseBlockList a q) (ys := baseBlockList b q)
    (n := 178) (i := i) (j := j)
    (baseBlockList_length ha hq) (baseBlockList_length hb hq)
    (by omega) (directionBit a q) (directionBit b q)
  have hr : r % 178 < 178 := Nat.mod_lt _ (by omega)
  have hrot : (baseBlockList b q).rotate (r % 178) =
      (baseBlockList b q).rotate r := by
    simpa [r, baseBlockList_length hb hq] using
      (List.rotate_mod (baseBlockList b q) r)
  calc
    hammingInt (shiftList (directionBit a q) i (baseBlockList a q))
        (shiftList (directionBit b q) j (baseBlockList b q)) =
      hammingInt (baseBlockList a q)
        ((baseBlockList b q).rotate r) := hred
    _ = hammingInt (baseBlockList a q)
        (shiftList false (r % 178) (baseBlockList b q)) := by
      have h := congrArg (hammingInt (baseBlockList a q)) hrot.symm
      simpa [shiftList] using h
    _ = baseDistanceList a b q false (r % 178) := by
      symm
      exact baseDistanceList_eq_hamming hr
    _ = baseLookupList a b q false (r % 178) := by
      exact baseDistanceList_eq_lookup ha hb hq hr
    _ = baseLookupList a b q false r := by
      simp [baseLookupList, r]

theorem top_shift_distance_eq_lookup {t a q i : Nat}
    (ht : t < 4) (ha : a < 4) (hq : q < 4) (hi : i < 178) :
    hammingInt (topChunkList t q)
        (shiftList (directionBit a q) i (baseBlockList a q)) =
      topLookupList t a q i := by
  calc
    hammingInt (topChunkList t q)
        (shiftList (directionBit a q) i (baseBlockList a q)) =
      topDistanceList t a q i := by
        symm
        exact topDistanceList_eq_hamming hi
    _ = topLookupList t a q i :=
      topDistanceList_eq_lookup ht ha hq hi

theorem coreRow_hamming_eq_distance {a b i j : Nat}
    (ha : a < 4) (hb : b < 4)
    (hi : i < 178) :
    hammingInt (coreRowList a i) (coreRowList b j) =
      coreDistanceReducedList a i b j := by
  have hlefta := leftRowList_length ha
  have hleftb := leftRowList_length hb
  have hleft : (leftRowList a).length = (leftRowList b).length := by omega
  have hs0a := baseBlockList_length ha (by omega : 0 < 4)
  have hs1a := baseBlockList_length ha (by omega : 1 < 4)
  have hs2a := baseBlockList_length ha (by omega : 2 < 4)
  have hs3a := baseBlockList_length ha (by omega : 3 < 4)
  have hs0b := baseBlockList_length hb (by omega : 0 < 4)
  have hs1b := baseBlockList_length hb (by omega : 1 < 4)
  have hs2b := baseBlockList_length hb (by omega : 2 < 4)
  have hs3b := baseBlockList_length hb (by omega : 3 < 4)
  have hsha0 :
      (shiftList (directionBit a 0) i (baseBlockList a 0)).length = 178 := by
    unfold shiftList
    split <;> simp [List.length_rotate, hs0a]
  have hsha1 :
      (shiftList (directionBit a 1) i (baseBlockList a 1)).length = 178 := by
    unfold shiftList
    split <;> simp [List.length_rotate, hs1a]
  have hsha2 :
      (shiftList (directionBit a 2) i (baseBlockList a 2)).length = 178 := by
    unfold shiftList
    split <;> simp [List.length_rotate, hs2a]
  have hsha3 :
      (shiftList (directionBit a 3) i (baseBlockList a 3)).length = 178 := by
    unfold shiftList
    split <;> simp [List.length_rotate, hs3a]
  have hshb0 :
      (shiftList (directionBit b 0) j (baseBlockList b 0)).length = 178 := by
    unfold shiftList
    split <;> simp [List.length_rotate, hs0b]
  have hshb1 :
      (shiftList (directionBit b 1) j (baseBlockList b 1)).length = 178 := by
    unfold shiftList
    split <;> simp [List.length_rotate, hs1b]
  have hshb2 :
      (shiftList (directionBit b 2) j (baseBlockList b 2)).length = 178 := by
    unfold shiftList
    split <;> simp [List.length_rotate, hs2b]
  have hshb3 :
      (shiftList (directionBit b 3) j (baseBlockList b 3)).length = 178 := by
    unfold shiftList
    split <;> simp [List.length_rotate, hs3b]
  have hsh0 :
      (shiftList (directionBit a 0) i (baseBlockList a 0)).length =
        (shiftList (directionBit b 0) j (baseBlockList b 0)).length := by omega
  have hsh1 :
      (shiftList (directionBit a 1) i (baseBlockList a 1)).length =
        (shiftList (directionBit b 1) j (baseBlockList b 1)).length := by omega
  have hsh2 :
      (shiftList (directionBit a 2) i (baseBlockList a 2)).length =
        (shiftList (directionBit b 2) j (baseBlockList b 2)).length := by omega
  have hsh3 :
      (shiftList (directionBit a 3) i (baseBlockList a 3)).length =
        (shiftList (directionBit b 3) j (baseBlockList b 3)).length := by omega
  rw [coreRowList, coreRowList]
  simp only [List.append_assoc]
  rw [hammingInt_append hleft]
  rw [hammingInt_append hsh0]
  rw [hammingInt_append hsh1]
  rw [hammingInt_append hsh2]
  rw [base_shift_distance_eq_lookup ha hb (by omega) hi]
  rw [base_shift_distance_eq_lookup ha hb (by omega) hi]
  rw [base_shift_distance_eq_lookup ha hb (by omega) hi]
  rw [base_shift_distance_eq_lookup ha hb (by omega) hi]
  simp [coreDistanceReducedList, leftDistanceList]
  omega

theorem topRow_hamming_eq_distance {t u : Nat}
    (ht : t < 4) (hu : u < 4) :
    hammingInt (topRowList t) (topRowList u) =
      topTopDistanceList t u := by
  have hpt := topPrefixList_length ht
  have hpu := topPrefixList_length hu
  have hp : (topPrefixList t).length = (topPrefixList u).length := by omega
  have h0t := topChunkList_length ht (by omega : 0 < 4)
  have h1t := topChunkList_length ht (by omega : 1 < 4)
  have h2t := topChunkList_length ht (by omega : 2 < 4)
  have h3t := topChunkList_length ht (by omega : 3 < 4)
  have h0u := topChunkList_length hu (by omega : 0 < 4)
  have h1u := topChunkList_length hu (by omega : 1 < 4)
  have h2u := topChunkList_length hu (by omega : 2 < 4)
  have h3u := topChunkList_length hu (by omega : 3 < 4)
  have h0 : (topChunkList t 0).length = (topChunkList u 0).length := by omega
  have h1 : (topChunkList t 1).length = (topChunkList u 1).length := by omega
  have h2 : (topChunkList t 2).length = (topChunkList u 2).length := by omega
  have h3 : (topChunkList t 3).length = (topChunkList u 3).length := by omega
  rw [topRowList, topRowList]
  simp only [List.append_assoc]
  rw [hammingInt_append hp]
  rw [hammingInt_append h0]
  rw [hammingInt_append h1]
  rw [hammingInt_append h2]
  simp [topTopDistanceList]
  omega

theorem topCore_hamming_eq_distance {t a i : Nat}
    (ht : t < 4) (ha : a < 4) (hi : i < 178) :
    hammingInt (topRowList t) (coreRowList a i) =
      topCoreDistanceList t a i := by
  have hpt := topPrefixList_length ht
  have hla := leftRowList_length ha
  have hp : (topPrefixList t).length = (leftRowList a).length := by omega
  have h0t := topChunkList_length ht (by omega : 0 < 4)
  have h1t := topChunkList_length ht (by omega : 1 < 4)
  have h2t := topChunkList_length ht (by omega : 2 < 4)
  have h3t := topChunkList_length ht (by omega : 3 < 4)
  have hs0 := baseBlockList_length ha (by omega : 0 < 4)
  have hs1 := baseBlockList_length ha (by omega : 1 < 4)
  have hs2 := baseBlockList_length ha (by omega : 2 < 4)
  have hs3 := baseBlockList_length ha (by omega : 3 < 4)
  have h0 : (topChunkList t 0).length =
      (shiftList (directionBit a 0) i (baseBlockList a 0)).length := by
    unfold shiftList
    split <;> simp [List.length_rotate, h0t, hs0]
  have h1 : (topChunkList t 1).length =
      (shiftList (directionBit a 1) i (baseBlockList a 1)).length := by
    unfold shiftList
    split <;> simp [List.length_rotate, h1t, hs1]
  have h2 : (topChunkList t 2).length =
      (shiftList (directionBit a 2) i (baseBlockList a 2)).length := by
    unfold shiftList
    split <;> simp [List.length_rotate, h2t, hs2]
  have h3 : (topChunkList t 3).length =
      (shiftList (directionBit a 3) i (baseBlockList a 3)).length := by
    unfold shiftList
    split <;> simp [List.length_rotate, h3t, hs3]
  rw [topRowList, coreRowList]
  simp only [List.append_assoc]
  rw [hammingInt_append hp]
  rw [hammingInt_append h0]
  rw [hammingInt_append h1]
  rw [hammingInt_append h2]
  rw [top_shift_distance_eq_lookup ht ha (by omega) hi]
  rw [top_shift_distance_eq_lookup ht ha (by omega) hi]
  rw [top_shift_distance_eq_lookup ht ha (by omega) hi]
  rw [top_shift_distance_eq_lookup ht ha (by omega) hi]
  simp [topCoreDistanceList]
  omega

theorem topCoreDistance_358 {t a i : Nat}
    (ht : t < 4) (ha : a < 4) (hi : i < 178) :
    topCoreDistanceList t a i = 358 := by
  have houter := (List.all_eq_true.mp topCoreList_check) t (by simp [ht])
  have hrow := (List.all_eq_true.mp houter) a (by simp [ha])
  have hcell := (List.all_eq_true.mp hrow) i (by simp [hi])
  norm_num at hcell
  exact hcell

theorem topTopDistance_358 {t u : Nat}
    (ht : t < 4) (hu : u < 4) (htu : t < u) :
    topTopDistanceList t u = 358 := by
  have houter := (List.all_eq_true.mp topTopList_check) t (by simp [ht])
  have hcell := (List.all_eq_true.mp houter) u (by simp [hu])
  have hbeq : (topTopDistanceList t u == 358) = true := by
    rw [if_pos (by simp [htu])] at hcell
    exact hcell
  exact beq_iff_eq.mp hbeq

theorem hammingInt_self (xs : List ℤ) : hammingInt xs xs = 0 := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      rw [hammingInt_cons, ih]
      simp

theorem hammingInt_comm {xs ys : List ℤ} :
    hammingInt xs ys = hammingInt ys xs := by
  unfold hammingInt
  rw [List.zipWith_comm]
  have hfun : (fun (b a : ℤ) => if a == b then 0 else 1) =
      (fun (x y : ℤ) => if x == y then 0 else 1) := by
    funext b a
    by_cases h : a = b
    · simp [h]
    · have h' : b ≠ a := Ne.symm h
      simp [h, h']
  rw [hfun]

def rowOfIndex (r : Nat) : List ℤ :=
  if r < 4 then topRowList r
  else coreRowList ((r - 4) / 178) ((r - 4) % 178)

def matrix716 (r c : Fin 716) : ℤ :=
  (rowOfIndex r.1)[c.1]!

theorem row_core_bounds {r : Nat} (hr4 : 4 ≤ r) (hr : r < 716) :
    (r - 4) / 178 < 4 ∧ (r - 4) % 178 < 178 := by
  omega

theorem div_mod_lex_order {x y : Nat} (hxy : x < y) :
    x / 178 < y / 178 ∨
      (x / 178 = y / 178 ∧ x % 178 < y % 178) := by
  have hx := Nat.div_add_mod x 178
  have hy := Nat.div_add_mod y 178
  have hxm := Nat.mod_lt x (by omega : 0 < 178)
  have hym := Nat.mod_lt y (by omega : 0 < 178)
  by_cases hq : x / 178 < y / 178
  · exact Or.inl hq
  · right
    have hqle : y / 178 ≤ x / 178 := by omega
    have heq : x / 178 = y / 178 := by omega
    have hrem : x % 178 < y % 178 := by omega
    exact ⟨heq, hrem⟩

theorem rowOfIndex_length {r : Nat} (hr : r < 716) :
    (rowOfIndex r).length = 716 := by
  by_cases htop : r < 4
  · simp [rowOfIndex, htop, topRowList_length htop]
  · have hb := row_core_bounds (by omega) hr
    simp [rowOfIndex, htop, coreRowList_length hb.1]

theorem source_signs_rowOfIndex {r : Nat} (hr : r < 716) :
    ∀ x ∈ rowOfIndex r, x = -1 ∨ x = 1 := by
  by_cases htop : r < 4
  · simpa [rowOfIndex, htop] using source_signs_top htop
  · have hb := row_core_bounds (by omega) hr
    simpa [rowOfIndex, htop] using source_signs_core hb.1

theorem matrix716_entry_sign (r c : Fin 716) :
    matrix716 r c = -1 ∨ matrix716 r c = 1 := by
  have hrow := rowOfIndex_length r.isLt
  have hc : c.1 < (rowOfIndex r.1).length := by
    rw [hrow]
    exact c.isLt
  have hmem : (rowOfIndex r.1)[c.1]'hc ∈ rowOfIndex r.1 :=
    List.getElem_mem hc
  have hs := source_signs_rowOfIndex r.isLt _ hmem
  change (rowOfIndex r.1)[c.1]! = -1 ∨ (rowOfIndex r.1)[c.1]! = 1
  rw [getElem!_pos (rowOfIndex r.1) c.1 hc]
  exact hs

theorem rowOfIndex_hamming_of_ne {r s : Nat}
    (hr : r < 716) (hs : s < 716) (hne : r ≠ s) :
    hammingInt (rowOfIndex r) (rowOfIndex s) = 358 := by
  by_cases hrt : r < 4
  · by_cases hst : s < 4
    · have horder : r < s ∨ s < r := by omega
      rcases horder with hrs | hsr
      · calc
          hammingInt (rowOfIndex r) (rowOfIndex s) =
              hammingInt (topRowList r) (topRowList s) := by
                simp [rowOfIndex, hrt, hst]
          _ = topTopDistanceList r s := topRow_hamming_eq_distance hrt hst
          _ = 358 := topTopDistance_358 hrt hst hrs
      · rw [hammingInt_comm]
        calc
          hammingInt (rowOfIndex s) (rowOfIndex r) =
              hammingInt (topRowList s) (topRowList r) := by
                simp [rowOfIndex, hrt, hst]
          _ = topTopDistanceList s r := topRow_hamming_eq_distance hst hrt
          _ = 358 := topTopDistance_358 hst hrt hsr
    · have hb := row_core_bounds (by omega) hs
      calc
        hammingInt (rowOfIndex r) (rowOfIndex s) =
            hammingInt (topRowList r)
              (coreRowList ((s - 4) / 178) ((s - 4) % 178)) := by
                simp [rowOfIndex, hrt, hst]
        _ = topCoreDistanceList r ((s - 4) / 178) ((s - 4) % 178) :=
          topCore_hamming_eq_distance hrt hb.1 hb.2
        _ = 358 := topCoreDistance_358 hrt hb.1 hb.2
  · by_cases hst : s < 4
    · have hb := row_core_bounds (by omega) hr
      rw [hammingInt_comm]
      calc
        hammingInt (rowOfIndex s) (rowOfIndex r) =
            hammingInt (topRowList s)
              (coreRowList ((r - 4) / 178) ((r - 4) % 178)) := by
                simp [rowOfIndex, hrt, hst]
        _ = topCoreDistanceList s ((r - 4) / 178) ((r - 4) % 178) :=
          topCore_hamming_eq_distance hst hb.1 hb.2
        _ = 358 := topCoreDistance_358 hst hb.1 hb.2
    · have hbr := row_core_bounds (by omega) hr
      have hbs := row_core_bounds (by omega) hs
      by_cases hrs : r < s
      · have horder := div_mod_lex_order (by omega : r - 4 < s - 4)
        have hforward :
            hammingInt
                (coreRowList ((r - 4) / 178) ((r - 4) % 178))
                (coreRowList ((s - 4) / 178) ((s - 4) % 178)) = 358 := by
          exact (coreRow_hamming_eq_distance hbr.1 hbs.1 hbr.2).trans
            (coreDistance_reduced_358 hbr.1 hbs.1 hbr.2 hbs.2 horder)
        simpa [rowOfIndex, hrt, hst] using hforward
      · have hsr : s < r := by omega
        rw [hammingInt_comm]
        have horder' := div_mod_lex_order (by omega : s - 4 < r - 4)
        have hreverse :
            hammingInt
                (coreRowList ((s - 4) / 178) ((s - 4) % 178))
                (coreRowList ((r - 4) / 178) ((r - 4) % 178)) = 358 := by
          exact (coreRow_hamming_eq_distance hbs.1 hbr.1 hbs.2).trans
            (coreDistance_reduced_358 hbs.1 hbr.1 hbs.2 hbr.2 horder')
        simpa [rowOfIndex, hrt, hst] using hreverse

theorem matrix716_row_dot {r s : Fin 716} :
    (∑ c : Fin 716, matrix716 r c * matrix716 s c) =
      intDot (rowOfIndex r.1) (rowOfIndex s.1) := by
  change (∑ c : Fin 716,
      (rowOfIndex r.1)[c.1]! * (rowOfIndex s.1)[c.1]!) = _
  exact fin_sum_intDot (rowOfIndex_length r.isLt)
    (rowOfIndex_length s.isLt)

theorem matrix716_row_dot_eq_hamming {r s : Fin 716} :
    (∑ c : Fin 716, matrix716 r c * matrix716 s c) =
      (716 : ℤ) - 2 * hammingInt (rowOfIndex r.1) (rowOfIndex s.1) := by
  rw [matrix716_row_dot]
  have hrl := rowOfIndex_length r.isLt
  have hsl := rowOfIndex_length s.isLt
  have hdot := intDot_hamming_signs
    (source_signs_rowOfIndex r.isLt)
    (source_signs_rowOfIndex s.isLt) (by omega)
  simpa [hrl, hsl] using hdot

theorem matrix716_row_norm (r : Fin 716) :
    (∑ c : Fin 716, matrix716 r c * matrix716 r c) = 716 := by
  rw [matrix716_row_dot_eq_hamming, hammingInt_self]
  norm_num

theorem matrix716_row_orthogonal {r s : Fin 716} (hne : r ≠ s) :
    (∑ c : Fin 716, matrix716 r c * matrix716 s c) = 0 := by
  rw [matrix716_row_dot_eq_hamming]
  have hd := rowOfIndex_hamming_of_ne r.isLt s.isLt (by
    intro h
    apply hne
    exact Fin.ext h)
  simp [hd]

end Hadamard716
