import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

namespace FCC

open Finset

/-- The four parity classes of the face-centred cubic lattice. -/
def offset (a : Fin 4) : Fin 3 → ℤ :=
  if a = 0 then ![0, 0, 0]
  else if a = 1 then ![0, 1, 1]
  else if a = 2 then ![1, 0, 1]
  else ![1, 1, 0]

abbrev Cell (m : ℕ) := Fin m × Fin m × Fin m
abbrev Vertex (m : ℕ) := Fin 4 × Cell m

def cellCoord {m : ℕ} (v : Vertex m) : Fin 3 → ℤ :=
  ![(v.2.1 : ℤ), (v.2.2.1 : ℤ), (v.2.2.2 : ℤ)]

/-- Unscaled integer coordinates in the even-parity box of side `2*m`. -/
def coord {m : ℕ} (v : Vertex m) (i : Fin 3) : ℤ :=
  2 * cellCoord v i + offset v.1 i

/-- Squared Euclidean distance before scaling by `1 / sqrt 2`. -/
def sqDist {m : ℕ} (u v : Vertex m) : ℤ :=
  (coord u 0 - coord v 0) ^ 2 +
  (coord u 1 - coord v 1) ^ 2 +
  (coord u 2 - coord v 2) ^ 2

def Contact {m : ℕ} (u v : Vertex m) : Prop := sqDist u v = 2

instance {m : ℕ} : DecidableRel (@Contact m) :=
  fun u v => inferInstanceAs (Decidable (sqDist u v = 2))

/-- Contact pairs oriented by their distinct parity-class labels. -/
def contactPairs (m : ℕ) : Finset (Vertex m × Vertex m) :=
  univ.filter fun p => p.1.1 < p.2.1 ∧ Contact p.1 p.2

/-- The actual point in three-dimensional Euclidean space. -/
noncomputable def point {m : ℕ} (v : Vertex m) : EuclideanSpace ℝ (Fin 3) :=
  WithLp.toLp 2 (fun i => (coord v i : ℝ) / Real.sqrt 2)

theorem vertex_card (m : ℕ) : Fintype.card (Vertex m) = 4 * m ^ 3 := by
  simp [Vertex, Cell]
  ring

end FCC
