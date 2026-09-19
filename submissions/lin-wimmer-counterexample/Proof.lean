import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic

/-!
Original mathematical counterexample: Shuo Shi, Juan Zhang, Yun Zhang,
arXiv:2609.07113v1 (7 September 2026), Section 3.
This independently written formalization uses Mathlib matrix rank.
-/
namespace LinWimmer
variable (K : Type*) [Field K]

def A : Matrix (Fin 3) (Fin 3) K := !![0,1,0; 0,0,0; 0,0,0]
def C : Matrix (Fin 3) (Fin 3) K := !![1,0,0; 0,0,0; 0,0,1]
def residual (X : Matrix (Fin 3) (Fin 3) K) := A K * X - X * A K - C K

theorem residual_formula (X : Matrix (Fin 3) (Fin 3) K) :
    residual K X = !![X 1 0 - 1, X 1 1 - X 0 0, X 1 2;
                     0, -X 1 0, 0; 0, -X 2 0, -1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [residual, A, C, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_succ]

theorem residual_rank_ge_two (X : Matrix (Fin 3) (Fin 3) K) :
    2 ≤ (residual K X).rank := by
  classical
  by_cases h : X 1 0 = 1
  · let r : Fin 2 → Fin 3 := ![1,2]
    have hd : ((residual K X).submatrix r r).det ≠ 0 := by
      simp [residual_formula, r, Matrix.det_fin_two, Matrix.submatrix, h]
    have hr := Matrix.rank_of_det_ne_zero hd
    have hb := (residual K X).rank_submatrix_le r r
    rw [hr] at hb
    exact hb
  · let r : Fin 2 → Fin 3 := ![0,2]
    have hd : ((residual K X).submatrix r r).det ≠ 0 := by
      simp [residual_formula, r, Matrix.det_fin_two, Matrix.submatrix, sub_ne_zero, Ne.symm h]
    have hr := Matrix.rank_of_det_ne_zero hd
    have hb := (residual K X).rank_submatrix_le r r
    rw [hr] at hb
    exact hb

abbrev Six := Fin 3 ⊕ Fin 3
def block (D : Matrix (Fin 3) (Fin 3) K) : Matrix Six Six K :=
  Matrix.fromBlocks (A K) D 0 (A K)

def P : Matrix Six Six K := Matrix.fromBlocks
  !![1,0,0; 0,1,0; 0,0,0] !![0,0,0; 1,0,0; 0,1,0]
  !![0,0,1; 0,0,0; 0,1,0] !![0,0,0; 0,0,1; 0,0,0]
def Q : Matrix Six Six K := Matrix.fromBlocks
  !![1,0,0; 0,0,0; 0,0,0] !![0,0,0; 0,0,1; 1,0,0]
  !![0,1,0; 0,0,1; 0,0,0] !![0,0,-1; 0,0,0; 0,1,0]

theorem pq : P K * Q K = 1 := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    fin_cases i <;> fin_cases j <;>
    norm_num [P, Q, Matrix.mul_apply, Matrix.submatrix,
      Fintype.sum_sum_type, Fin.sum_univ_succ, Matrix.fromBlocks, Matrix.vecMul, dotProduct, Matrix.one_apply] <;> decide

theorem qp : Q K * P K = 1 := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    fin_cases i <;> fin_cases j <;>
    norm_num [P, Q, Matrix.mul_apply, Matrix.submatrix,
      Fintype.sum_sum_type, Fin.sum_univ_succ, Matrix.fromBlocks, Matrix.vecMul, dotProduct, Matrix.one_apply] <;> decide

theorem P_isUnit : IsUnit (P K) :=
  ⟨⟨P K, Q K, pq K, qp K⟩, rfl⟩

def commutator (U : Matrix Six Six K) := U * block K (C K) - block K 0 * U

theorem commutator_P : commutator K (P K) =
    Matrix.vecMulVec
      (fun i : Six => if i = Sum.inl 1 then 1 else 0)
      (fun j : Six => if j = Sum.inr 1 then 1 else 0) := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    fin_cases i <;> fin_cases j <;>
    norm_num [commutator, block, A, C, P, Matrix.mul_apply, Matrix.fromBlocks,
      Matrix.vecMulVec, Fintype.sum_sum_type, Fin.sum_univ_succ, Matrix.vecMul, dotProduct] <;> decide

theorem commutator_P_rank_le_one : (commutator K (P K)).rank ≤ 1 := by
  rw [commutator_P]
  exact Matrix.rank_vecMulVec_le _ _

theorem rank_pos_of_entry {m n : Type*} [Fintype n]
    (D : Matrix m n K) (i : m) (j : n) (h : D i j ≠ 0) : 1 ≤ D.rank := by
  classical
  let r : Fin 1 → m := fun _ => i
  let c : Fin 1 → n := fun _ => j
  have hd : (D.submatrix r c).det ≠ 0 := by
    simpa [Matrix.det_fin_one, Matrix.submatrix, r, c] using h
  have hr := Matrix.rank_of_det_ne_zero hd
  have hb := D.rank_submatrix_le r c
  rw [hr] at hb
  exact hb

theorem rank_pos_of_ne_zero {m n : Type*} [Fintype n]
    (D : Matrix m n K) (h : D ≠ 0) : 1 ≤ D.rank := by
  classical
  obtain ⟨i, j, hij⟩ : ∃ i j, D i j ≠ 0 := by
    contrapose! h
    ext i j
    exact h i j
  exact rank_pos_of_entry K D i j hij

theorem block_zero_sq : block K 0 * block K 0 = 0 := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    fin_cases i <;> fin_cases j <;>
    norm_num [block, A, Matrix.mul_apply, Matrix.fromBlocks,
      Fintype.sum_sum_type, Fin.sum_univ_succ, Matrix.vecMul, dotProduct]

theorem block_C_sq_ne_zero : block K (C K) * block K (C K) ≠ 0 := by
  intro h
  have he := congrArg (fun D : Matrix Six Six K => D (Sum.inl 0) (Sum.inr 1)) h
  norm_num [block, A, C, Matrix.mul_apply, Matrix.fromBlocks,
    Fintype.sum_sum_type, Fin.sum_univ_succ, Matrix.vecMul, dotProduct] at he

theorem commutator_ne_zero (U : Matrix Six Six K) (hu : IsUnit U) :
    commutator K U ≠ 0 := by
  intro h
  have he : U * block K (C K) = block K 0 * U := sub_eq_zero.mp h
  have hs : U * (block K (C K) * block K (C K)) = 0 := by
    calc
      _ = (U * block K (C K)) * block K (C K) := (mul_assoc _ _ _).symm
      _ = (block K 0 * U) * block K (C K) := by rw [he]
      _ = block K 0 * (U * block K (C K)) := mul_assoc _ _ _
      _ = block K 0 * (block K 0 * U) := by rw [he]
      _ = (block K 0 * block K 0) * U := (mul_assoc _ _ _).symm
      _ = 0 := by rw [block_zero_sq, zero_mul]
  obtain ⟨u, rfl⟩ := hu
  have hh := congrArg (fun D => (↑(u⁻¹) : Matrix Six Six K) * D) hs
  have hz : block K (C K) * block K (C K) = 0 := by
    simpa [← mul_assoc] using hh
  exact block_C_sq_ne_zero K hz

theorem commutator_rank_ge_one (U : Matrix Six Six K) (hu : IsUnit U) :
    1 ≤ (commutator K U).rank := rank_pos_of_ne_zero K _ (commutator_ne_zero K U hu)

theorem commutator_P_rank : (commutator K (P K)).rank = 1 :=
  le_antisymm (commutator_P_rank_le_one K) (commutator_rank_ge_one K _ (P_isUnit K))

theorem residual_zero_rank : (residual K 0).rank = 2 := by
  classical
  apply le_antisymm _ (residual_rank_ge_two K 0)
  have hb := (residual K 0).rank_le_card_of_support_subset ({0, 2} : Finset (Fin 3))
  have hs : Function.support (residual K 0).row ⊆ (↑({0, 2} : Finset (Fin 3)) : Set (Fin 3)) := by
    intro i hi
    fin_cases i
    · simp
    · exfalso
      apply hi
      funext j
      fin_cases j <;> simp [Matrix.row, residual_formula]
    · simp
  simpa using hb hs

theorem left_minimum : IsLeast (Set.range (fun X => (residual K X).rank)) 2 := by
  constructor
  · exact ⟨0, residual_zero_rank K⟩
  · rintro r ⟨X, rfl⟩
    exact residual_rank_ge_two K X

theorem right_minimum : IsLeast {r : ℕ | ∃ U : Matrix Six Six K,
    IsUnit U ∧ (commutator K U).rank = r} 1 := by
  constructor
  · exact ⟨P K, P_isUnit K, commutator_P_rank K⟩
  · rintro r ⟨U, hu, rfl⟩
    exact commutator_rank_ge_one K U hu

#print axioms left_minimum
#print axioms right_minimum

/- The minima below are over nonempty subsets of natural numbers. The two
`IsLeast` theorems above certify attainment and the universal lower bounds. -/
theorem minima_values :
    sInf (Set.range (fun X => (residual K X).rank)) = 2 ∧
    sInf {r : ℕ | ∃ U : Matrix Six Six K, IsUnit U ∧ (commutator K U).rank = r} = 1 :=
  ⟨(left_minimum K).csInf_eq, (right_minimum K).csInf_eq⟩

/-- The rank-minimization conjecture on page 443 of Lin--Wimmer (2011).
The same unknown `X` and the same invertible matrix `U` occur on both sides
of their respective differences. No spectral hypotheses are inserted. -/
def SimilarityRankConjecture : Prop :=
  ∀ (m n : ℕ), 0 < m → 0 < n →
  ∀ (a : Matrix (Fin m) (Fin m) K) (b : Matrix (Fin n) (Fin n) K)
    (c : Matrix (Fin m) (Fin n) K),
    sInf (Set.range (fun X : Matrix (Fin m) (Fin n) K => (a * X - X * b - c).rank)) =
    sInf {r : ℕ | ∃ U : Matrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) K,
      IsUnit U ∧ (U * Matrix.fromBlocks a c 0 b - Matrix.fromBlocks a 0 0 b * U).rank = r}

/-- The universal conjecture is false over every field, including
characteristic two. This is the counterexample, not dimensional minimality. -/
theorem refutation : ¬ SimilarityRankConjecture K := by
  intro h
  have he := h 3 3 (by decide) (by decide) (A K) (A K) (C K)
  change sInf (Set.range (fun X => (residual K X).rank)) =
    sInf {r : ℕ | ∃ U : Matrix Six Six K, IsUnit U ∧ (commutator K U).rank = r} at he
  rw [(minima_values K).1, (minima_values K).2] at he
  exact (by decide : (2 : ℕ) ≠ 1) he

#print axioms minima_values
#print axioms refutation

end LinWimmer
