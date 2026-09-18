import JSP000853.GridGraph
import Mathlib.Data.Fin.Embedding
import Mathlib.Data.Nat.Sqrt

/-!
# The upper bound for every finite size

Embed `Fin N` into the least convenient square grid, restrict the grid mapping
back to the embedded copy, and transfer the forest bound.  We use
`sqrt N + 1` instead of an exact ceiling square root; this only changes the
absolute constant.
-/

namespace JSP000853

/-- A square side strictly larger than the natural square root. -/
def gridSide (N : ℕ) : ℕ := Nat.sqrt N + 1

theorem le_gridSide_sq (N : ℕ) : N ≤ gridSide N ^ 2 :=
  (Nat.lt_succ_sqrt' N).le

theorem gridSide_sq_le_four_mul {N : ℕ} (hN : 0 < N) :
    gridSide N ^ 2 ≤ 4 * N := by
  have hspos : 0 < Nat.sqrt N := (Nat.sqrt_pos).2 hN
  have hside : gridSide N ≤ 2 * Nat.sqrt N := by
    unfold gridSide
    rw [two_mul]
    exact Nat.add_le_add_left hspos (Nat.sqrt N)
  calc
    gridSide N ^ 2 ≤ (2 * Nat.sqrt N) ^ 2 := Nat.pow_le_pow_left hside 2
    _ = 4 * (Nat.sqrt N) ^ 2 := by simp only [pow_two]; ac_rfl
    _ ≤ 4 * N := Nat.mul_le_mul_left 4 (Nat.sqrt_le' N)

/-- The initial segment of a square grid large enough to contain `Fin N`. -/
def finGridEmbedding (N : ℕ) : Fin N ↪ Grid (gridSide N) :=
  (Fin.castLEEmb (by simpa only [pow_two] using le_gridSide_sq N)).trans
    finProdFinEquiv.symm.toEmbedding

/-- The construction half of Erdős Problem #1025, with the explicit universal
constant `16`. -/
theorem erdos1025_upperBound : UpperBoundTarget := by
  refine ⟨16, by decide, ?_⟩
  intro N hN
  have h2N : 2 < N := lt_of_lt_of_le (by decide) hN
  have hNpos : 0 < N := lt_trans (by decide : 0 < 2) h2N
  have hgridCard : 2 < Fintype.card (Grid (gridSide N)) := by
    have hsq : 2 < gridSide N ^ 2 := lt_of_lt_of_le h2N (le_gridSide_sq N)
    simpa [Fintype.card_prod, Fintype.card_fin, pow_two] using hsq
  have hfinCard : 2 < Fintype.card (Fin N) := by
    simpa using h2N
  let e : Fin N ↪ Grid (gridSide N) := finGridEmbedding N
  let ambient : PairMapping (Grid (gridSide N)) := gridMapping hgridCard
  let restricted : PairMapping (Fin N) := PairMapping.restrict hfinCard e ambient
  refine ⟨restricted, ?_⟩
  intro S hfree
  have himage : ambient.IsFree (S.image e) :=
    PairMapping.isFree_image_of_restrict_isFree hfinCard e ambient hfree
  have hgrid := free_card_sq_le_four_mul_sq hgridCard himage
  rw [Finset.card_image_of_injective S e.injective] at hgrid
  calc
    S.card ^ 2 ≤ 4 * gridSide N ^ 2 := hgrid
    _ ≤ 4 * (4 * N) := Nat.mul_le_mul_left 4 (gridSide_sq_le_four_mul hNpos)
    _ = 16 * N := by rw [← Nat.mul_assoc]

end JSP000853
