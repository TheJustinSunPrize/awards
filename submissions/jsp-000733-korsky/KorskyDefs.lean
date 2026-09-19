import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
Definitions for a formalization of Samuel Korsky's July 26, 2026
primitive-subset-sums upper bound. The modular packing presentation is an
equivalent finite rearrangement of the author's ordered ternary packing.
-/
namespace Erdos882Korsky

abbrev Word (k : ℕ) := Fin k → Fin 3

def Ordered {k : ℕ} (w : Word k) : Prop :=
  ∀ i j, i < j → w i = 2 → w j ≠ 0

def Good {k : ℕ} (w : Word k) : Prop := Ordered w ∧ ∃ i, w i = 2

noncomputable instance goodFintype (k : ℕ) : Fintype {w : Word k // Good w} :=
  Fintype.ofFinite _

def NoDouble {k : ℕ} (a : Fin k → ℕ) : Prop :=
  ∀ I J : Finset (Fin k), I.Nonempty → J.Nonempty →
    (∑ i ∈ I, a i) ≠ 2 * ∑ j ∈ J, a j

def value {k : ℕ} (a : Fin k → ℕ) (w : Word k) : ℤ :=
  ∑ i, (w i : ℤ) * (a i : ℤ)

def total {k : ℕ} (a : Fin k → ℕ) : ℕ := ∑ i, a i

end Erdos882Korsky
