/- Local 20-vertex adaptation of PR #190, commit 4022d2df0f941a12f497d5045b75995e0cf8f883.
   Upstream formalization: jinkaizhang236-sketch / Justin Sun Prize contributors.
   Original mathematical construction: Paul W. Dyson and Brendan D. McKay.
   See THIRD_PARTY_NOTICES.md for exact reuse and changes. -/
import RegularCertificate
import Mathlib.Data.Fintype.Fin
namespace Graph20Proof

def neighbors (v : Fin 20) : Finset (Fin 20) :=
  match v.val with
  | 0 => {11, 13, 17}
  | 1 => {12, 14, 16, 18}
  | 2 => {9, 10, 15, 16, 19}
  | 3 => {7, 8, 13, 18, 19}
  | 4 => {5, 6, 10, 11, 15, 18, 19}
  | 5 => {4, 6, 9, 11, 14, 16, 17, 18, 19}
  | 6 => {4, 5, 8, 10, 13, 15, 17, 18, 19}
  | 7 => {3, 8, 9, 12, 13, 14, 16, 18, 19}
  | 8 => {3, 6, 7, 11, 12, 15, 16, 17, 19}
  | 9 => {2, 5, 7, 10, 12, 14, 15, 17, 18}
  | 10 => {2, 4, 6, 9, 11, 14, 15, 16, 17, 19}
  | 11 => {0, 4, 5, 8, 10, 13, 15, 16, 18, 19}
  | 12 => {1, 7, 8, 9, 13, 14, 16, 17, 18, 19}
  | 13 => {0, 3, 6, 7, 11, 12, 15, 16, 17, 18}
  | 14 => {1, 5, 7, 9, 10, 12, 15, 17, 18, 19}
  | 15 => {2, 4, 6, 8, 9, 10, 11, 13, 14, 16, 17, 18, 19}
  | 16 => {1, 2, 5, 7, 8, 10, 11, 12, 13, 15, 17, 18, 19}
  | 17 => {0, 5, 6, 8, 9, 10, 12, 13, 14, 15, 16, 18, 19}
  | 18 => {1, 3, 4, 5, 6, 7, 9, 11, 12, 13, 14, 15, 16, 17, 19}
  | 19 => {2, 3, 4, 5, 6, 7, 8, 10, 11, 12, 14, 15, 16, 17, 18}
  | _ => ∅

end Graph20Proof
