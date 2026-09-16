import Mathlib.RingTheory.IntegralDomain
import Mathlib.Algebra.GroupWithZero.Units.Fintype

/-!
# Full-field distinct partial sums (JSP-000387)

This proves the literal full-nonzero-field statement discussed in awards issue
#46. It does not prove the Graham--Erdos conjecture for arbitrary subsets.
The construction by powers of a multiplicative generator is the elementary
argument recorded in that issue; the contribution here is its formalization.
-/

namespace JSP000387

open Finset

/-- The sum of the first `m` entries of a sequence. -/
def prefixSum {K : Type*} [AddCommMonoid K] (a : ℕ → K) (m : ℕ) : K :=
  ∑ j ∈ range m, a j

/-- A nonrepeating enumeration of all nonzero field elements, with distinct
nonempty prefix sums. The meaningful part of `a` has length `card K - 1`. -/
def IsFullFieldOrdering (K : Type*) [Field K] [Fintype K] (a : ℕ → K) : Prop :=
  (∀ i : Fin (Fintype.card K - 1), a i ≠ 0) ∧
  Function.Injective (fun i : Fin (Fintype.card K - 1) => a i) ∧
  (∀ x : K, x ≠ 0 → ∃ i : Fin (Fintype.card K - 1), a i = x) ∧
  Function.Injective (fun i : Fin (Fintype.card K - 1) => prefixSum a (i.val + 1))

variable {K : Type*} [Field K]

/-- Equality of two geometric prefix sums implies equality of the corresponding
powers. Multiplication, rather than division by `g - 1`, also covers `g = 1`. -/
theorem powers_eq_of_prefixSum_eq (g : Kˣ) {m n : ℕ}
    (h : prefixSum (fun j => (g : K) ^ j) (m + 1) =
      prefixSum (fun j => (g : K) ^ j) (n + 1)) : g ^ m = g ^ n := by
  have hmul := congrArg (fun s : K => s * ((g : K) - 1)) h
  simp only [prefixSum, geom_sum_mul] at hmul
  have hpow : (g : K) ^ (m + 1) = (g : K) ^ (n + 1) := by
    simpa only [sub_left_inj] using hmul
  rw [pow_succ, pow_succ] at hpow
  apply Units.ext
  simpa only [Units.val_pow_eq_pow_val] using mul_right_cancel₀ g.ne_zero hpow

/-- The geometric prefix sums indexed by `1, ..., orderOf g` are distinct. -/
theorem geometric_prefix_sums_injective (g : Kˣ) :
    Function.Injective (fun i : Fin (orderOf g) =>
      prefixSum (fun j => (g : K) ^ j) (i.val + 1)) := by
  intro i j h
  exact Fin.ext (pow_injOn_Iio_orderOf i.isLt j.isLt (powers_eq_of_prefixSum_eq g h))

/-- Every finite field admits an ordering of all its nonzero elements with
pairwise distinct nonempty prefix sums. This includes the two-element field. -/
theorem exists_full_field_ordering (K : Type*) [Field K] [Fintype K] :
    ∃ a : ℕ → K, IsFullFieldOrdering K a := by
  classical
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := Kˣ)
  have horder : orderOf g = Fintype.card Kˣ := by
    simpa only [Nat.card_eq_fintype_card] using hg
  have hinj : Function.Injective (fun i : Fin (Fintype.card Kˣ) => g ^ i.val) := by
    intro i j h
    apply Fin.ext
    exact pow_injOn_Iio_orderOf (x := g)
      (by simpa only [Set.mem_Iio, horder] using i.isLt)
      (by simpa only [Set.mem_Iio, horder] using j.isLt) h
  have hbij : Function.Bijective (fun i : Fin (Fintype.card Kˣ) => g ^ i.val) :=
    (Fintype.bijective_iff_injective_and_card _).2 ⟨hinj, Fintype.card_fin _⟩
  refine ⟨fun j => (g : K) ^ j, ?_⟩
  unfold IsFullFieldOrdering
  rw [← Fintype.card_units]
  refine ⟨fun i => pow_ne_zero _ g.ne_zero, ?_, ?_, ?_⟩
  · intro i j h
    apply hinj
    apply Units.ext
    simpa only [Units.val_pow_eq_pow_val] using h
  · intro x hx
    obtain ⟨i, hi⟩ := hbij.2 (Units.mk0 x hx)
    exact ⟨i, by simpa using congrArg (fun u : Kˣ => (u : K)) hi⟩
  · intro i j h
    exact hinj (powers_eq_of_prefixSum_eq g h)

end JSP000387
