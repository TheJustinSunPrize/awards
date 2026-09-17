/-
A formalization contribution for The Justin Sun Prize, entry JSP-000718
("How far above one half must density be to force all pairwise sums of a
large set?"), corresponding to Erdős Problem 866
(https://www.erdosproblems.com/866).

Erdős Problem 866 (Choi–Erdős–Szemerédi [CES75]). Let `g_k(N)` be minimal
such that every `A ⊆ {1, ..., 2N}` with `|A| ≥ N + g_k(N)` contains all
`C(k,2)` pairwise sums of some `k` distinct positive integers
(the integers themselves need not lie in `A`).

This file formalizes the sharp lower-bound examples for `k = 3`:

* `not_pairwise_sums_all_odd`: no three integers have all three pairwise
  sums odd — among any three integers two share a parity, and their sum is
  even.
* `oddsIn_avoid` / `insert_two_oddsIn_avoid`: the odd numbers in `[1, 2N]`,
  and that set together with `2`, contain no such triple.
* `g3_lower` / `g3_lower'`: consequently there is an avoiding set of size
  `N + 1`, i.e. density `1/2 + 1/(2N)` does not force the configuration;
  in the notation of erdosproblems.com/866 this says `g_3(N) ≥ 2`.

The matching upper bound `g_3(N) ≤ 2` is the theorem of Choi, Erdős and
Szemerédi [CES75]; it is NOT claimed here (see the README).

Reference: Choi, S. L. G., Erdős, P. and Szemerédi, E., "Some additive and
multiplicative problems in number theory", Acta Arith. (1975), 37–50.
-/

import Mathlib

open Finset

namespace Erdos866

/-- The set of odd integers in `[1, 2N]`. -/
def oddsIn (N : ℕ) : Finset ℕ := (Finset.Icc 1 (2 * N)).filter Odd

lemma mem_oddsIn {N x : ℕ} : x ∈ oddsIn N ↔ 1 ≤ x ∧ x ≤ 2 * N ∧ Odd x := by
  simp only [oddsIn, mem_filter, mem_Icc]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨h1, h2, h3⟩
  · rintro ⟨h1, h2, h3⟩; exact ⟨⟨h1, h2⟩, h3⟩

/-- The odd numbers in `[1, 2N]` are exactly `{1, 3, ..., 2N - 1}`, the image of
`range N` under `i ↦ 2i + 1`. -/
lemma oddsIn_eq_image (N : ℕ) :
    oddsIn N = (Finset.range N).image (fun i => 2 * i + 1) := by
  ext x
  simp only [mem_oddsIn, mem_image, mem_range]
  constructor
  · rintro ⟨h1, h2, h3⟩
    have h3' : x % 2 = 1 := Nat.odd_iff.mp h3
    exact ⟨x / 2, by omega, by omega⟩
  · rintro ⟨i, hi, rfl⟩
    refine ⟨by omega, by omega, Nat.odd_iff.mpr (by omega)⟩

/-- There are exactly `N` odd numbers in `[1, 2N]`. -/
lemma card_oddsIn (N : ℕ) : (oddsIn N).card = N := by
  rw [oddsIn_eq_image, card_image_of_injOn]
  · exact card_range N
  · intro i _ j _ hij
    dsimp only at hij
    omega

/-- `2` is not odd, hence not in `oddsIn N`. -/
lemma two_notMem_oddsIn (N : ℕ) : 2 ∉ oddsIn N := by
  intro h
  have h2 := Nat.odd_iff.mp (mem_oddsIn.mp h).2.2
  omega

/-- `HasTripleSumConfig A` : there are three distinct positive integers whose
three pairwise sums all lie in `A`. (The three integers themselves need not
lie in `A`, following erdosproblems.com/866.) -/
def HasTripleSumConfig (A : Finset ℕ) : Prop :=
  ∃ x y z : ℕ, 1 ≤ x ∧ x < y ∧ y < z ∧ x + y ∈ A ∧ x + z ∈ A ∧ y + z ∈ A

/-- Among any three integers, two share a parity; equivalently one of the three
pairwise sums is even. -/
lemma exists_even_pairwise_sum (x y z : ℕ) :
    Even (x + y) ∨ Even (x + z) ∨ Even (y + z) := by
  have h : (x + y) % 2 = 0 ∨ (x + z) % 2 = 0 ∨ (y + z) % 2 = 0 := by omega
  simpa only [Nat.even_iff] using h

/-- Three integers cannot have all three pairwise sums odd. -/
theorem not_pairwise_sums_all_odd {x y z : ℕ}
    (hxy : Odd (x + y)) (hxz : Odd (x + z)) (hyz : Odd (y + z)) : False := by
  rcases exists_even_pairwise_sum x y z with h | h | h
  · exact (Nat.not_even_iff_odd.mpr hxy) h
  · exact (Nat.not_even_iff_odd.mpr hxz) h
  · exact (Nat.not_even_iff_odd.mpr hyz) h

/-- The odd numbers contain no triple with all pairwise sums in the set:
every pairwise sum in `oddsIn N` is odd, but three pairwise sums cannot all
be odd. -/
theorem oddsIn_avoid (N : ℕ) : ¬ HasTripleSumConfig (oddsIn N) := by
  rintro ⟨x, y, z, hx, hxy, hyz, h1, h2, h3⟩
  exact not_pairwise_sums_all_odd
    (mem_oddsIn.mp h1).2.2 (mem_oddsIn.mp h2).2.2 (mem_oddsIn.mp h3).2.2

/-- The odd numbers together with `2` still contain no such triple: a pairwise
sum equal to `2` would have to be a sum of two distinct positive integers
(at least `1 + 2 = 3`), so all three pairwise sums must be odd, which is
impossible. -/
theorem insert_two_oddsIn_avoid (N : ℕ) :
    ¬ HasTripleSumConfig (insert 2 (oddsIn N)) := by
  rintro ⟨x, y, z, hx, hxy, hyz, h1, h2, h3⟩
  have e1 : Odd (x + y) ∨ x + y = 2 := by
    rcases mem_insert.mp h1 with h | h
    · exact Or.inr h
    · exact Or.inl (mem_oddsIn.mp h).2.2
  have e2 : Odd (x + z) ∨ x + z = 2 := by
    rcases mem_insert.mp h2 with h | h
    · exact Or.inr h
    · exact Or.inl (mem_oddsIn.mp h).2.2
  have e3 : Odd (y + z) ∨ y + z = 2 := by
    rcases mem_insert.mp h3 with h | h
    · exact Or.inr h
    · exact Or.inl (mem_oddsIn.mp h).2.2
  have n1 : x + y ≠ 2 := by omega
  have n2 : x + z ≠ 2 := by omega
  have n3 : y + z ≠ 2 := by omega
  exact not_pairwise_sums_all_odd
    (e1.resolve_right n1) (e2.resolve_right n2) (e3.resolve_right n3)

/-- Lower bound for the Choi–Erdős–Szemerédi problem (erdosproblems.com/866,
JSP-000718): the odd numbers in `[1, 2N]` give `N` elements with no triple
whose pairwise sums all lie in the set, so `g_3(N) ≥ 1`. -/
theorem g3_lower (N : ℕ) :
    ∃ A : Finset ℕ, A ⊆ Finset.Icc 1 (2 * N) ∧ A.card = N ∧
      ¬ HasTripleSumConfig A := by
  refine ⟨oddsIn N, ?_, card_oddsIn N, oddsIn_avoid N⟩
  intro x hx
  exact mem_Icc.mpr ⟨(mem_oddsIn.mp hx).1, (mem_oddsIn.mp hx).2.1⟩

/-- The sharp lower-bound example: for `N ≥ 1` the odd numbers in `[1, 2N]`
together with `2` give `N + 1` elements — density `1/2 + 1/(2N)` — with no
triple whose pairwise sums all lie in the set, so `g_3(N) ≥ 2`. -/
theorem g3_lower' (N : ℕ) (hN : 1 ≤ N) :
    ∃ A : Finset ℕ, A ⊆ Finset.Icc 1 (2 * N) ∧ A.card = N + 1 ∧
      ¬ HasTripleSumConfig A := by
  refine ⟨insert 2 (oddsIn N), ?_, ?_, insert_two_oddsIn_avoid N⟩
  · intro x hx
    rcases mem_insert.mp hx with rfl | hx
    · exact mem_Icc.mpr ⟨by omega, by omega⟩
    · exact mem_Icc.mpr ⟨(mem_oddsIn.mp hx).1, (mem_oddsIn.mp hx).2.1⟩
  · rw [card_insert_of_notMem (two_notMem_oddsIn N), card_oddsIn]

end Erdos866

-- Axiom audit: every theorem below must depend only on the standard axioms
-- `propext`, `Classical.choice`, `Quot.sound`.
#print axioms Erdos866.not_pairwise_sums_all_odd
#print axioms Erdos866.oddsIn_avoid
#print axioms Erdos866.insert_two_oddsIn_avoid
#print axioms Erdos866.g3_lower
#print axioms Erdos866.g3_lower'
