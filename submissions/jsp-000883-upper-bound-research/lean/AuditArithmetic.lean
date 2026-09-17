import JSP000883.Arithmetic

-- These are expected TYPES checked by Lean, not text matches or extra premises.
-- An accidentally generalized `j` changes the type and fails these examples.
set_option autoImplicit false
open Finset
open JSP000883.ProductConstruction

example : ∀ m r : ℕ,
    r.factorial * (m - 1).choose r = ∏ j ∈ Icc 1 r, (m - j) :=
  descending_product

example : ∀ m r : ℕ,
    (m + 1).ascFactorial r = ∏ j ∈ Icc 1 r, (m + j) :=
  ascFactorial_product

example : ∀ m r : ℕ,
    r.factorial * (m + r).choose r = ∏ j ∈ Icc 1 r, (m + j) :=
  ascending_product

example (right : Bool) (m k : ℕ) (hk : 0 < k) :
    (k - 1).factorial * auxiliary right m k =
      ∏ j ∈ indices k, term right m j :=
  auxiliary_product right m k hk

example (S : Finset ℕ) (f : ℕ → ℕ) (a : ℕ) (ha : a ∈ S) :
    (∏ j ∈ S, f j) = f a * (∏ j ∈ S.erase a, f j) :=
  split_prod S f ha

#print axioms JSP000883.ProductConstruction.descending_product
#print axioms JSP000883.ProductConstruction.ascFactorial_product
#print axioms JSP000883.ProductConstruction.ascending_product
#print axioms JSP000883.ProductConstruction.auxiliary_product
#print axioms JSP000883.ProductConstruction.coefficient_factor
#print axioms JSP000883.ProductConstruction.split_prod
#print axioms JSP000883.ProductConstruction.Parameters.cross_identity
#print axioms JSP000883.ProductConstruction.cancel_cross_product
