/-
Licensed under Apache-2.0; see LICENSE and NOTICE.
Adapted from Arthur Freitas Ramos, David Barros Hulak, and Ruy J. G. B. de Queiroz,
Arthur742Ramos/hadamard-668-lean at 78fbae8d69b6fdb66705b662469692d60e346ef0.
Modification: certify the distinct order-716 matrix with fresh certificate data.
Matrix discovery belongs to the original Alpoge/Voinov/Reynolds-Haertle team.
-/
import Hadamard716.CertificateData
import Hadamard716.CorrelationData
import Mathlib

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Hadamard716

/-- Hamming distance on the integer sign rows of the compact order-716 certificate. -/
def hammingInt (xs ys : List ℤ) : Nat :=
  (xs.zipWith (fun x y => if x == y then 0 else 1) ys).sum

def shiftList (right : Bool) (k : Nat) (xs : List ℤ) : List ℤ :=
  if right then xs.rotate (xs.length - k) else xs.rotate k

def baseListTable (a b q : Nat) (right : Bool) : List Nat :=
  (List.range 178).map (fun k =>
    hammingInt ((bases716[a]!)[q]!)
      (shiftList right k ((bases716[b]!)[q]!)))

def baseExpectedTable (a b q : Nat) (right : Bool) : List Nat :=
  (((baseCorrelationExpected716[a]!)[b]!)[q]!)[if right then 1 else 0]!

def topChunkList (t q : Nat) : List ℤ :=
  ((top716[t]!).drop 4).drop (178 * q) |>.take 178

def topListTable (t a q : Nat) : List Nat :=
  (List.range 178).map (fun k =>
    hammingInt (topChunkList t q)
      (shiftList ((dirs716[a]!)[q]!) k ((bases716[a]!)[q]!)))

def topExpectedTable (t a q : Nat) : List Nat :=
  ((topCorrelationExpected716[t]!)[a]!)[q]!

theorem baseListTable_0_0_0_left :
    baseListTable 0 0 0 false = baseExpectedTable 0 0 0 false := by
  decide

theorem baseListTable_0_0_0_right :
    baseListTable 0 0 0 true = baseExpectedTable 0 0 0 true := by
  decide

theorem baseListTable_0_0_1_left :
    baseListTable 0 0 1 false = baseExpectedTable 0 0 1 false := by
  decide

theorem baseListTable_0_0_1_right :
    baseListTable 0 0 1 true = baseExpectedTable 0 0 1 true := by
  decide

theorem baseListTable_0_0_2_left :
    baseListTable 0 0 2 false = baseExpectedTable 0 0 2 false := by
  decide

theorem baseListTable_0_0_2_right :
    baseListTable 0 0 2 true = baseExpectedTable 0 0 2 true := by
  decide

theorem baseListTable_0_0_3_left :
    baseListTable 0 0 3 false = baseExpectedTable 0 0 3 false := by
  decide

theorem baseListTable_0_0_3_right :
    baseListTable 0 0 3 true = baseExpectedTable 0 0 3 true := by
  decide

theorem baseListTable_0_1_0_left :
    baseListTable 0 1 0 false = baseExpectedTable 0 1 0 false := by
  decide

theorem baseListTable_0_1_0_right :
    baseListTable 0 1 0 true = baseExpectedTable 0 1 0 true := by
  decide

theorem baseListTable_0_1_1_left :
    baseListTable 0 1 1 false = baseExpectedTable 0 1 1 false := by
  decide

theorem baseListTable_0_1_1_right :
    baseListTable 0 1 1 true = baseExpectedTable 0 1 1 true := by
  decide

theorem baseListTable_0_1_2_left :
    baseListTable 0 1 2 false = baseExpectedTable 0 1 2 false := by
  decide

theorem baseListTable_0_1_2_right :
    baseListTable 0 1 2 true = baseExpectedTable 0 1 2 true := by
  decide

theorem baseListTable_0_1_3_left :
    baseListTable 0 1 3 false = baseExpectedTable 0 1 3 false := by
  decide

theorem baseListTable_0_1_3_right :
    baseListTable 0 1 3 true = baseExpectedTable 0 1 3 true := by
  decide

theorem baseListTable_0_2_0_left :
    baseListTable 0 2 0 false = baseExpectedTable 0 2 0 false := by
  decide

theorem baseListTable_0_2_0_right :
    baseListTable 0 2 0 true = baseExpectedTable 0 2 0 true := by
  decide

theorem baseListTable_0_2_1_left :
    baseListTable 0 2 1 false = baseExpectedTable 0 2 1 false := by
  decide

theorem baseListTable_0_2_1_right :
    baseListTable 0 2 1 true = baseExpectedTable 0 2 1 true := by
  decide

theorem baseListTable_0_2_2_left :
    baseListTable 0 2 2 false = baseExpectedTable 0 2 2 false := by
  decide

theorem baseListTable_0_2_2_right :
    baseListTable 0 2 2 true = baseExpectedTable 0 2 2 true := by
  decide

theorem baseListTable_0_2_3_left :
    baseListTable 0 2 3 false = baseExpectedTable 0 2 3 false := by
  decide

theorem baseListTable_0_2_3_right :
    baseListTable 0 2 3 true = baseExpectedTable 0 2 3 true := by
  decide

theorem baseListTable_0_3_0_left :
    baseListTable 0 3 0 false = baseExpectedTable 0 3 0 false := by
  decide

theorem baseListTable_0_3_0_right :
    baseListTable 0 3 0 true = baseExpectedTable 0 3 0 true := by
  decide

theorem baseListTable_0_3_1_left :
    baseListTable 0 3 1 false = baseExpectedTable 0 3 1 false := by
  decide

theorem baseListTable_0_3_1_right :
    baseListTable 0 3 1 true = baseExpectedTable 0 3 1 true := by
  decide

theorem baseListTable_0_3_2_left :
    baseListTable 0 3 2 false = baseExpectedTable 0 3 2 false := by
  decide

theorem baseListTable_0_3_2_right :
    baseListTable 0 3 2 true = baseExpectedTable 0 3 2 true := by
  decide

theorem baseListTable_0_3_3_left :
    baseListTable 0 3 3 false = baseExpectedTable 0 3 3 false := by
  decide

theorem baseListTable_0_3_3_right :
    baseListTable 0 3 3 true = baseExpectedTable 0 3 3 true := by
  decide

theorem baseListTable_1_0_0_left :
    baseListTable 1 0 0 false = baseExpectedTable 1 0 0 false := by
  decide

theorem baseListTable_1_0_0_right :
    baseListTable 1 0 0 true = baseExpectedTable 1 0 0 true := by
  decide

theorem baseListTable_1_0_1_left :
    baseListTable 1 0 1 false = baseExpectedTable 1 0 1 false := by
  decide

theorem baseListTable_1_0_1_right :
    baseListTable 1 0 1 true = baseExpectedTable 1 0 1 true := by
  decide

theorem baseListTable_1_0_2_left :
    baseListTable 1 0 2 false = baseExpectedTable 1 0 2 false := by
  decide

theorem baseListTable_1_0_2_right :
    baseListTable 1 0 2 true = baseExpectedTable 1 0 2 true := by
  decide

theorem baseListTable_1_0_3_left :
    baseListTable 1 0 3 false = baseExpectedTable 1 0 3 false := by
  decide

theorem baseListTable_1_0_3_right :
    baseListTable 1 0 3 true = baseExpectedTable 1 0 3 true := by
  decide

theorem baseListTable_1_1_0_left :
    baseListTable 1 1 0 false = baseExpectedTable 1 1 0 false := by
  decide

theorem baseListTable_1_1_0_right :
    baseListTable 1 1 0 true = baseExpectedTable 1 1 0 true := by
  decide

theorem baseListTable_1_1_1_left :
    baseListTable 1 1 1 false = baseExpectedTable 1 1 1 false := by
  decide

theorem baseListTable_1_1_1_right :
    baseListTable 1 1 1 true = baseExpectedTable 1 1 1 true := by
  decide

theorem baseListTable_1_1_2_left :
    baseListTable 1 1 2 false = baseExpectedTable 1 1 2 false := by
  decide

theorem baseListTable_1_1_2_right :
    baseListTable 1 1 2 true = baseExpectedTable 1 1 2 true := by
  decide

theorem baseListTable_1_1_3_left :
    baseListTable 1 1 3 false = baseExpectedTable 1 1 3 false := by
  decide

theorem baseListTable_1_1_3_right :
    baseListTable 1 1 3 true = baseExpectedTable 1 1 3 true := by
  decide

theorem baseListTable_1_2_0_left :
    baseListTable 1 2 0 false = baseExpectedTable 1 2 0 false := by
  decide

theorem baseListTable_1_2_0_right :
    baseListTable 1 2 0 true = baseExpectedTable 1 2 0 true := by
  decide

theorem baseListTable_1_2_1_left :
    baseListTable 1 2 1 false = baseExpectedTable 1 2 1 false := by
  decide

theorem baseListTable_1_2_1_right :
    baseListTable 1 2 1 true = baseExpectedTable 1 2 1 true := by
  decide

theorem baseListTable_1_2_2_left :
    baseListTable 1 2 2 false = baseExpectedTable 1 2 2 false := by
  decide

theorem baseListTable_1_2_2_right :
    baseListTable 1 2 2 true = baseExpectedTable 1 2 2 true := by
  decide

theorem baseListTable_1_2_3_left :
    baseListTable 1 2 3 false = baseExpectedTable 1 2 3 false := by
  decide

theorem baseListTable_1_2_3_right :
    baseListTable 1 2 3 true = baseExpectedTable 1 2 3 true := by
  decide

theorem baseListTable_1_3_0_left :
    baseListTable 1 3 0 false = baseExpectedTable 1 3 0 false := by
  decide

theorem baseListTable_1_3_0_right :
    baseListTable 1 3 0 true = baseExpectedTable 1 3 0 true := by
  decide

theorem baseListTable_1_3_1_left :
    baseListTable 1 3 1 false = baseExpectedTable 1 3 1 false := by
  decide

theorem baseListTable_1_3_1_right :
    baseListTable 1 3 1 true = baseExpectedTable 1 3 1 true := by
  decide

theorem baseListTable_1_3_2_left :
    baseListTable 1 3 2 false = baseExpectedTable 1 3 2 false := by
  decide

theorem baseListTable_1_3_2_right :
    baseListTable 1 3 2 true = baseExpectedTable 1 3 2 true := by
  decide

theorem baseListTable_1_3_3_left :
    baseListTable 1 3 3 false = baseExpectedTable 1 3 3 false := by
  decide

theorem baseListTable_1_3_3_right :
    baseListTable 1 3 3 true = baseExpectedTable 1 3 3 true := by
  decide

theorem baseListTable_2_0_0_left :
    baseListTable 2 0 0 false = baseExpectedTable 2 0 0 false := by
  decide

theorem baseListTable_2_0_0_right :
    baseListTable 2 0 0 true = baseExpectedTable 2 0 0 true := by
  decide

theorem baseListTable_2_0_1_left :
    baseListTable 2 0 1 false = baseExpectedTable 2 0 1 false := by
  decide

theorem baseListTable_2_0_1_right :
    baseListTable 2 0 1 true = baseExpectedTable 2 0 1 true := by
  decide

theorem baseListTable_2_0_2_left :
    baseListTable 2 0 2 false = baseExpectedTable 2 0 2 false := by
  decide

theorem baseListTable_2_0_2_right :
    baseListTable 2 0 2 true = baseExpectedTable 2 0 2 true := by
  decide

theorem baseListTable_2_0_3_left :
    baseListTable 2 0 3 false = baseExpectedTable 2 0 3 false := by
  decide

theorem baseListTable_2_0_3_right :
    baseListTable 2 0 3 true = baseExpectedTable 2 0 3 true := by
  decide

theorem baseListTable_2_1_0_left :
    baseListTable 2 1 0 false = baseExpectedTable 2 1 0 false := by
  decide

theorem baseListTable_2_1_0_right :
    baseListTable 2 1 0 true = baseExpectedTable 2 1 0 true := by
  decide

theorem baseListTable_2_1_1_left :
    baseListTable 2 1 1 false = baseExpectedTable 2 1 1 false := by
  decide

theorem baseListTable_2_1_1_right :
    baseListTable 2 1 1 true = baseExpectedTable 2 1 1 true := by
  decide

theorem baseListTable_2_1_2_left :
    baseListTable 2 1 2 false = baseExpectedTable 2 1 2 false := by
  decide

theorem baseListTable_2_1_2_right :
    baseListTable 2 1 2 true = baseExpectedTable 2 1 2 true := by
  decide

theorem baseListTable_2_1_3_left :
    baseListTable 2 1 3 false = baseExpectedTable 2 1 3 false := by
  decide

theorem baseListTable_2_1_3_right :
    baseListTable 2 1 3 true = baseExpectedTable 2 1 3 true := by
  decide

theorem baseListTable_2_2_0_left :
    baseListTable 2 2 0 false = baseExpectedTable 2 2 0 false := by
  decide

theorem baseListTable_2_2_0_right :
    baseListTable 2 2 0 true = baseExpectedTable 2 2 0 true := by
  decide

theorem baseListTable_2_2_1_left :
    baseListTable 2 2 1 false = baseExpectedTable 2 2 1 false := by
  decide

theorem baseListTable_2_2_1_right :
    baseListTable 2 2 1 true = baseExpectedTable 2 2 1 true := by
  decide

theorem baseListTable_2_2_2_left :
    baseListTable 2 2 2 false = baseExpectedTable 2 2 2 false := by
  decide

theorem baseListTable_2_2_2_right :
    baseListTable 2 2 2 true = baseExpectedTable 2 2 2 true := by
  decide

theorem baseListTable_2_2_3_left :
    baseListTable 2 2 3 false = baseExpectedTable 2 2 3 false := by
  decide

theorem baseListTable_2_2_3_right :
    baseListTable 2 2 3 true = baseExpectedTable 2 2 3 true := by
  decide

theorem baseListTable_2_3_0_left :
    baseListTable 2 3 0 false = baseExpectedTable 2 3 0 false := by
  decide

theorem baseListTable_2_3_0_right :
    baseListTable 2 3 0 true = baseExpectedTable 2 3 0 true := by
  decide

theorem baseListTable_2_3_1_left :
    baseListTable 2 3 1 false = baseExpectedTable 2 3 1 false := by
  decide

theorem baseListTable_2_3_1_right :
    baseListTable 2 3 1 true = baseExpectedTable 2 3 1 true := by
  decide

theorem baseListTable_2_3_2_left :
    baseListTable 2 3 2 false = baseExpectedTable 2 3 2 false := by
  decide

theorem baseListTable_2_3_2_right :
    baseListTable 2 3 2 true = baseExpectedTable 2 3 2 true := by
  decide

theorem baseListTable_2_3_3_left :
    baseListTable 2 3 3 false = baseExpectedTable 2 3 3 false := by
  decide

theorem baseListTable_2_3_3_right :
    baseListTable 2 3 3 true = baseExpectedTable 2 3 3 true := by
  decide

theorem baseListTable_3_0_0_left :
    baseListTable 3 0 0 false = baseExpectedTable 3 0 0 false := by
  decide

theorem baseListTable_3_0_0_right :
    baseListTable 3 0 0 true = baseExpectedTable 3 0 0 true := by
  decide

theorem baseListTable_3_0_1_left :
    baseListTable 3 0 1 false = baseExpectedTable 3 0 1 false := by
  decide

theorem baseListTable_3_0_1_right :
    baseListTable 3 0 1 true = baseExpectedTable 3 0 1 true := by
  decide

theorem baseListTable_3_0_2_left :
    baseListTable 3 0 2 false = baseExpectedTable 3 0 2 false := by
  decide

theorem baseListTable_3_0_2_right :
    baseListTable 3 0 2 true = baseExpectedTable 3 0 2 true := by
  decide

theorem baseListTable_3_0_3_left :
    baseListTable 3 0 3 false = baseExpectedTable 3 0 3 false := by
  decide

theorem baseListTable_3_0_3_right :
    baseListTable 3 0 3 true = baseExpectedTable 3 0 3 true := by
  decide

theorem baseListTable_3_1_0_left :
    baseListTable 3 1 0 false = baseExpectedTable 3 1 0 false := by
  decide

theorem baseListTable_3_1_0_right :
    baseListTable 3 1 0 true = baseExpectedTable 3 1 0 true := by
  decide

theorem baseListTable_3_1_1_left :
    baseListTable 3 1 1 false = baseExpectedTable 3 1 1 false := by
  decide

theorem baseListTable_3_1_1_right :
    baseListTable 3 1 1 true = baseExpectedTable 3 1 1 true := by
  decide

theorem baseListTable_3_1_2_left :
    baseListTable 3 1 2 false = baseExpectedTable 3 1 2 false := by
  decide

theorem baseListTable_3_1_2_right :
    baseListTable 3 1 2 true = baseExpectedTable 3 1 2 true := by
  decide

theorem baseListTable_3_1_3_left :
    baseListTable 3 1 3 false = baseExpectedTable 3 1 3 false := by
  decide

theorem baseListTable_3_1_3_right :
    baseListTable 3 1 3 true = baseExpectedTable 3 1 3 true := by
  decide

theorem baseListTable_3_2_0_left :
    baseListTable 3 2 0 false = baseExpectedTable 3 2 0 false := by
  decide

theorem baseListTable_3_2_0_right :
    baseListTable 3 2 0 true = baseExpectedTable 3 2 0 true := by
  decide

theorem baseListTable_3_2_1_left :
    baseListTable 3 2 1 false = baseExpectedTable 3 2 1 false := by
  decide

theorem baseListTable_3_2_1_right :
    baseListTable 3 2 1 true = baseExpectedTable 3 2 1 true := by
  decide

theorem baseListTable_3_2_2_left :
    baseListTable 3 2 2 false = baseExpectedTable 3 2 2 false := by
  decide

theorem baseListTable_3_2_2_right :
    baseListTable 3 2 2 true = baseExpectedTable 3 2 2 true := by
  decide

theorem baseListTable_3_2_3_left :
    baseListTable 3 2 3 false = baseExpectedTable 3 2 3 false := by
  decide

theorem baseListTable_3_2_3_right :
    baseListTable 3 2 3 true = baseExpectedTable 3 2 3 true := by
  decide

theorem baseListTable_3_3_0_left :
    baseListTable 3 3 0 false = baseExpectedTable 3 3 0 false := by
  decide

theorem baseListTable_3_3_0_right :
    baseListTable 3 3 0 true = baseExpectedTable 3 3 0 true := by
  decide

theorem baseListTable_3_3_1_left :
    baseListTable 3 3 1 false = baseExpectedTable 3 3 1 false := by
  decide

theorem baseListTable_3_3_1_right :
    baseListTable 3 3 1 true = baseExpectedTable 3 3 1 true := by
  decide

theorem baseListTable_3_3_2_left :
    baseListTable 3 3 2 false = baseExpectedTable 3 3 2 false := by
  decide

theorem baseListTable_3_3_2_right :
    baseListTable 3 3 2 true = baseExpectedTable 3 3 2 true := by
  decide

theorem baseListTable_3_3_3_left :
    baseListTable 3 3 3 false = baseExpectedTable 3 3 3 false := by
  decide

theorem baseListTable_3_3_3_right :
    baseListTable 3 3 3 true = baseExpectedTable 3 3 3 true := by
  decide

theorem topListTable_0_0_0 :
    topListTable 0 0 0 = topExpectedTable 0 0 0 := by
  decide

theorem topListTable_0_0_1 :
    topListTable 0 0 1 = topExpectedTable 0 0 1 := by
  decide

theorem topListTable_0_0_2 :
    topListTable 0 0 2 = topExpectedTable 0 0 2 := by
  decide

theorem topListTable_0_0_3 :
    topListTable 0 0 3 = topExpectedTable 0 0 3 := by
  decide

theorem topListTable_0_1_0 :
    topListTable 0 1 0 = topExpectedTable 0 1 0 := by
  decide

theorem topListTable_0_1_1 :
    topListTable 0 1 1 = topExpectedTable 0 1 1 := by
  decide

theorem topListTable_0_1_2 :
    topListTable 0 1 2 = topExpectedTable 0 1 2 := by
  decide

theorem topListTable_0_1_3 :
    topListTable 0 1 3 = topExpectedTable 0 1 3 := by
  decide

theorem topListTable_0_2_0 :
    topListTable 0 2 0 = topExpectedTable 0 2 0 := by
  decide

theorem topListTable_0_2_1 :
    topListTable 0 2 1 = topExpectedTable 0 2 1 := by
  decide

theorem topListTable_0_2_2 :
    topListTable 0 2 2 = topExpectedTable 0 2 2 := by
  decide

theorem topListTable_0_2_3 :
    topListTable 0 2 3 = topExpectedTable 0 2 3 := by
  decide

theorem topListTable_0_3_0 :
    topListTable 0 3 0 = topExpectedTable 0 3 0 := by
  decide

theorem topListTable_0_3_1 :
    topListTable 0 3 1 = topExpectedTable 0 3 1 := by
  decide

theorem topListTable_0_3_2 :
    topListTable 0 3 2 = topExpectedTable 0 3 2 := by
  decide

theorem topListTable_0_3_3 :
    topListTable 0 3 3 = topExpectedTable 0 3 3 := by
  decide

theorem topListTable_1_0_0 :
    topListTable 1 0 0 = topExpectedTable 1 0 0 := by
  decide

theorem topListTable_1_0_1 :
    topListTable 1 0 1 = topExpectedTable 1 0 1 := by
  decide

theorem topListTable_1_0_2 :
    topListTable 1 0 2 = topExpectedTable 1 0 2 := by
  decide

theorem topListTable_1_0_3 :
    topListTable 1 0 3 = topExpectedTable 1 0 3 := by
  decide

theorem topListTable_1_1_0 :
    topListTable 1 1 0 = topExpectedTable 1 1 0 := by
  decide

theorem topListTable_1_1_1 :
    topListTable 1 1 1 = topExpectedTable 1 1 1 := by
  decide

theorem topListTable_1_1_2 :
    topListTable 1 1 2 = topExpectedTable 1 1 2 := by
  decide

theorem topListTable_1_1_3 :
    topListTable 1 1 3 = topExpectedTable 1 1 3 := by
  decide

theorem topListTable_1_2_0 :
    topListTable 1 2 0 = topExpectedTable 1 2 0 := by
  decide

theorem topListTable_1_2_1 :
    topListTable 1 2 1 = topExpectedTable 1 2 1 := by
  decide

theorem topListTable_1_2_2 :
    topListTable 1 2 2 = topExpectedTable 1 2 2 := by
  decide

theorem topListTable_1_2_3 :
    topListTable 1 2 3 = topExpectedTable 1 2 3 := by
  decide

theorem topListTable_1_3_0 :
    topListTable 1 3 0 = topExpectedTable 1 3 0 := by
  decide

theorem topListTable_1_3_1 :
    topListTable 1 3 1 = topExpectedTable 1 3 1 := by
  decide

theorem topListTable_1_3_2 :
    topListTable 1 3 2 = topExpectedTable 1 3 2 := by
  decide

theorem topListTable_1_3_3 :
    topListTable 1 3 3 = topExpectedTable 1 3 3 := by
  decide

theorem topListTable_2_0_0 :
    topListTable 2 0 0 = topExpectedTable 2 0 0 := by
  decide

theorem topListTable_2_0_1 :
    topListTable 2 0 1 = topExpectedTable 2 0 1 := by
  decide

theorem topListTable_2_0_2 :
    topListTable 2 0 2 = topExpectedTable 2 0 2 := by
  decide

theorem topListTable_2_0_3 :
    topListTable 2 0 3 = topExpectedTable 2 0 3 := by
  decide

theorem topListTable_2_1_0 :
    topListTable 2 1 0 = topExpectedTable 2 1 0 := by
  decide

theorem topListTable_2_1_1 :
    topListTable 2 1 1 = topExpectedTable 2 1 1 := by
  decide

theorem topListTable_2_1_2 :
    topListTable 2 1 2 = topExpectedTable 2 1 2 := by
  decide

theorem topListTable_2_1_3 :
    topListTable 2 1 3 = topExpectedTable 2 1 3 := by
  decide

theorem topListTable_2_2_0 :
    topListTable 2 2 0 = topExpectedTable 2 2 0 := by
  decide

theorem topListTable_2_2_1 :
    topListTable 2 2 1 = topExpectedTable 2 2 1 := by
  decide

theorem topListTable_2_2_2 :
    topListTable 2 2 2 = topExpectedTable 2 2 2 := by
  decide

theorem topListTable_2_2_3 :
    topListTable 2 2 3 = topExpectedTable 2 2 3 := by
  decide

theorem topListTable_2_3_0 :
    topListTable 2 3 0 = topExpectedTable 2 3 0 := by
  decide

theorem topListTable_2_3_1 :
    topListTable 2 3 1 = topExpectedTable 2 3 1 := by
  decide

theorem topListTable_2_3_2 :
    topListTable 2 3 2 = topExpectedTable 2 3 2 := by
  decide

theorem topListTable_2_3_3 :
    topListTable 2 3 3 = topExpectedTable 2 3 3 := by
  decide

theorem topListTable_3_0_0 :
    topListTable 3 0 0 = topExpectedTable 3 0 0 := by
  decide

theorem topListTable_3_0_1 :
    topListTable 3 0 1 = topExpectedTable 3 0 1 := by
  decide

theorem topListTable_3_0_2 :
    topListTable 3 0 2 = topExpectedTable 3 0 2 := by
  decide

theorem topListTable_3_0_3 :
    topListTable 3 0 3 = topExpectedTable 3 0 3 := by
  decide

theorem topListTable_3_1_0 :
    topListTable 3 1 0 = topExpectedTable 3 1 0 := by
  decide

theorem topListTable_3_1_1 :
    topListTable 3 1 1 = topExpectedTable 3 1 1 := by
  decide

theorem topListTable_3_1_2 :
    topListTable 3 1 2 = topExpectedTable 3 1 2 := by
  decide

theorem topListTable_3_1_3 :
    topListTable 3 1 3 = topExpectedTable 3 1 3 := by
  decide

theorem topListTable_3_2_0 :
    topListTable 3 2 0 = topExpectedTable 3 2 0 := by
  decide

theorem topListTable_3_2_1 :
    topListTable 3 2 1 = topExpectedTable 3 2 1 := by
  decide

theorem topListTable_3_2_2 :
    topListTable 3 2 2 = topExpectedTable 3 2 2 := by
  decide

theorem topListTable_3_2_3 :
    topListTable 3 2 3 = topExpectedTable 3 2 3 := by
  decide

theorem topListTable_3_3_0 :
    topListTable 3 3 0 = topExpectedTable 3 3 0 := by
  decide

theorem topListTable_3_3_1 :
    topListTable 3 3 1 = topExpectedTable 3 3 1 := by
  decide

theorem topListTable_3_3_2 :
    topListTable 3 3 2 = topExpectedTable 3 3 2 := by
  decide

theorem topListTable_3_3_3 :
    topListTable 3 3 3 = topExpectedTable 3 3 3 := by
  decide


end Hadamard716
