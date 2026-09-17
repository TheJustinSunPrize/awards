import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace JSP000327

private theorem successor (n : ℕ) :
    (Nat.centralBinom (n + 1) : ℚ) =
      2 * (2 * n + 1) / (n + 1) * Nat.centralBinom n := by
  have h := Nat.succ_mul_centralBinom_succ n
  have hc : (n + 1 : ℚ) * Nat.centralBinom (n + 1) =
      2 * (2 * n + 1) * Nat.centralBinom n := by exact_mod_cast h
  have hn : (n + 1 : ℚ) ≠ 0 := by positivity
  field_simp
  nlinarith

/-- Necessary and sufficient arithmetic criterion for three-factor collisions. -/
theorem three_factor_iff (a b c : ℕ) :
    Nat.centralBinom a * Nat.centralBinom (b + 2) * Nat.centralBinom c =
      Nat.centralBinom (a + 1) * Nat.centralBinom b * Nat.centralBinom (c + 1) ↔
    (a + 1) * (2 * b + 1) * (2 * b + 3) * (c + 1) =
      (2 * a + 1) * (b + 1) * (b + 2) * (2 * c + 1) := by
  have ha : (a + 1 : ℚ) ≠ 0 := by positivity
  have hb : (b + 1 : ℚ) ≠ 0 := by positivity
  have hb' : (b + 2 : ℚ) ≠ 0 := by positivity
  have hc : (c + 1 : ℚ) ≠ 0 := by positivity
  have hA : (Nat.centralBinom a : ℚ) ≠ 0 := by exact_mod_cast Nat.centralBinom_ne_zero a
  have hB : (Nat.centralBinom b : ℚ) ≠ 0 := by exact_mod_cast Nat.centralBinom_ne_zero b
  have hC : (Nat.centralBinom c : ℚ) ≠ 0 := by exact_mod_cast Nat.centralBinom_ne_zero c
  rw [← Nat.cast_inj (R := ℚ), ← Nat.cast_inj (R := ℚ)]
  push_cast
  rw [show b + 2 = (b + 1) + 1 by omega, successor a, successor c,
    successor (b + 1), successor b]
  push_cast
  field_simp
  constructor <;> intro h <;> nlinarith

/-- The known quadratic family is the only collision in the doubled-middle pattern. -/
theorem doubled_middle_iff (a c : ℕ) :
    Nat.centralBinom a * Nat.centralBinom (2 * a + 2) * Nat.centralBinom c =
      Nat.centralBinom (a + 1) * Nat.centralBinom (2 * a) * Nat.centralBinom (c + 1) ↔
    c = 8 * a ^ 2 + 8 * a + 1 := by
  rw [three_factor_iff]
  constructor
  · intro h
    have hf : (a + 1) * c = (a + 1) * (8 * a ^ 2 + 8 * a + 1) := by nlinarith [h]
    exact Nat.eq_of_mul_eq_mul_left (by omega : 0 < a + 1) hf
  · rintro rfl
    ring

def leftIndices (a : ℕ) : Finset ℕ := {a, 2 * a + 2, 8 * a ^ 2 + 8 * a + 1}
def rightIndices (a : ℕ) : Finset ℕ := {a + 1, 2 * a, 8 * a ^ 2 + 8 * a + 2}

/-- Nonempty disjoint index sets with equal central-binomial products. -/
def Solution (M N : Finset ℕ) : Prop :=
  Disjoint M N ∧ M.Nonempty ∧ N.Nonempty ∧
    M.prod Nat.centralBinom = N.prod Nat.centralBinom

theorem family_properties (a : ℕ) (ha : 2 ≤ a) :
    Solution (leftIndices a) (rightIndices a) ∧
      (leftIndices a).card = 3 ∧ (rightIndices a).card = 3 ∧
      ∀ i ∈ leftIndices a ∪ rightIndices a, a ≤ i := by
  have hlarge : 2 * a + 2 < 8 * a ^ 2 + 8 * a + 1 := by omega
  have heq := (doubled_middle_iff a (8 * a ^ 2 + 8 * a + 1)).2 rfl
  have hd : Disjoint (leftIndices a) (rightIndices a) := by
    simp [leftIndices, rightIndices, Finset.disjoint_left]
    omega
  have hprod : (leftIndices a).prod Nat.centralBinom =
      (rightIndices a).prod Nat.centralBinom := by
    simpa (disch := simp only [Finset.mem_insert, Finset.mem_singleton]; omega)
      [leftIndices, rightIndices, Finset.prod_insert, mul_assoc, add_assoc] using heq
  refine ⟨⟨hd, by simp [leftIndices], by simp [rightIndices], hprod⟩, ?_, ?_, ?_⟩
  · rw [leftIndices, Finset.card_triple_eq_three_iff]; omega
  · rw [rightIndices, Finset.card_triple_eq_three_iff]; omega
  · intro i hi
    simp only [leftIndices, rightIndices, Finset.mem_union, Finset.mem_insert,
      Finset.mem_singleton] at hi
    rcases hi with (rfl | rfl | rfl) | (rfl | rfl | rfl) <;> omega

theorem unbounded_solutions (B : ℕ) :
    ∃ M N : Finset ℕ, Solution M N ∧ M.card = 3 ∧ N.card = 3 ∧
      ∀ i ∈ M ∪ N, B < i := by
  obtain ⟨hs, hl, hr, hmin⟩ := family_properties (B + 2) (by omega)
  exact ⟨leftIndices (B + 2), rightIndices (B + 2), hs, hl, hr,
    fun i hi => lt_of_lt_of_le (by omega) (hmin i hi)⟩

/-- Direct answer to the original finite-set finiteness question. -/
theorem jsp_000327 :
    ¬ {s : Finset ℕ × Finset ℕ | Disjoint s.1 s.2 ∧
      s.1.prod Nat.centralBinom = s.2.prod Nat.centralBinom}.Finite := by
  apply Set.Infinite.mono (s := Set.range fun k =>
    (leftIndices (k + 2), rightIndices (k + 2)))
  · rintro s ⟨k, rfl⟩
    have h := (family_properties (k + 2) (by omega)).1
    exact ⟨h.1, h.2.2.2⟩
  · apply Set.infinite_range_of_injective
    intro k l h
    have hsets : leftIndices (k + 2) = leftIndices (l + 2) := congrArg Prod.fst h
    have hk : k + 2 ∈ leftIndices (l + 2) := by
      rw [← hsets]; simp [leftIndices]
    have hl : l + 2 ∈ leftIndices (k + 2) := by
      rw [hsets]; simp [leftIndices]
    have hkl := (family_properties (l + 2) (by omega)).2.2.2 (k + 2)
      (Finset.mem_union_left _ hk)
    have hlk := (family_properties (k + 2) (by omega)).2.2.2 (l + 2)
      (Finset.mem_union_left _ hl)
    omega

#print axioms three_factor_iff
#print axioms doubled_middle_iff
#print axioms family_properties
#print axioms unbounded_solutions
#print axioms jsp_000327

end JSP000327
