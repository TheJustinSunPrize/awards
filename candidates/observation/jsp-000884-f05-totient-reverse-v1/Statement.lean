import Mathlib

set_option autoImplicit false

namespace JSP000884

noncomputable section

/-- The reverse strict inequality set in the public formalization of Erdős 1064. -/
def reverseTotientSet : Set ℕ :=
  {n | Nat.totient n < Nat.totient (n - Nat.totient n)}

/-- Exact proposition reproduced from `Erdos1064.erdos_1064.variants.k2`. -/
def target : Prop := reverseTotientSet.Infinite

end
end JSP000884
