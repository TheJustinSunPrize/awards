import Mathlib

/-!
# Erdős Problem 18: Erdős's bound `h(n!) < n`

For a practical number `m`, `h(m)` is the least `k` such that every `1 ≤ t ≤ m` is a sum of
distinct divisors drawn from some set of at most `k` divisors of `m`. Erdős asked whether
`h(n!) < n^{o(1)}` or even `h(n!) < (log n)^{O(1)}`; he showed `h(n!) < n`.

This file proves `erdos_18_upper_bound`, which is stated with `sorry` (category "research solved")
in Google DeepMind's formal-conjectures project, `FormalConjectures/ErdosProblems/18.lean`.
The definitions `subsetSums` (from `FormalConjecturesForMathlib/NumberTheory/AdditivelyComplete.lean`)
and `practicalH` are copied verbatim from that project (Apache-2.0).
-/

open Filter

section FormalConjectures

variable {M : Type*} [AddCommMonoid M]

/-- The set of subset sums of a set `A ⊆ M`. -/
def subsetSums (A : Set M) : Set M :=
  {n | ∃ B : Finset M, ↑B ⊆ A ∧ n = ∑ i ∈ B, i}

end FormalConjectures

namespace Erdos18

/-- For a practical number $n$, $h(n)$ is the maximum over all $1 ≤ m ≤ n$ of
the minimum number of divisors of $n$ needed to represent $m$ as a sum of
distinct divisors. -/
noncomputable def practicalH (n : ℕ) : ℕ :=
  Finset.sup (Finset.Icc 1 n) fun m =>
    sInf {k | ∃ D : Finset ℕ, D ⊆ n.divisors ∧ D.card = k ∧ m ∈ subsetSums D}

/-- Erdős's inductive construction: for `n ≥ 1`, every `m < n!` is the sum of a set of at most
`n - 1` distinct divisors of `n!`. -/
theorem exists_divisors_sum_of_lt_factorial {n : ℕ} (hn : 1 ≤ n) :
    ∀ m < n.factorial, ∃ S : Finset ℕ, S ⊆ n.factorial.divisors ∧ S.card ≤ n - 1 ∧
      m = ∑ i ∈ S, i := by
  induction n, hn using Nat.le_induction with
  | base =>
    intro m hm
    refine ⟨∅, by simp, by simp, ?_⟩
    simp only [Nat.factorial_one] at hm
    simp; omega
  | succ n hn ih =>
    intro m hm
    have hn1 : 0 < n + 1 := Nat.succ_pos n
    set q := m / (n + 1) with hq
    set r := m % (n + 1) with hr
    have hdecomp : m = (n + 1) * q + r := (Nat.div_add_mod m (n + 1)).symm
    have hrlt : r < n + 1 := Nat.mod_lt m hn1
    have hqlt : q < n.factorial := by
      rw [Nat.factorial_succ] at hm
      exact Nat.div_lt_of_lt_mul hm
    obtain ⟨S', hS'sub, hS'card, hS'sum⟩ := ih q hqlt
    -- scale the divisors of `n!` by `n + 1`
    set T := S'.image (· * (n + 1)) with hT
    have hinj : Set.InjOn (· * (n + 1)) (S' : Set ℕ) :=
      fun a _ b _ h => Nat.eq_of_mul_eq_mul_right hn1 h
    have hTcard : T.card = S'.card := Finset.card_image_of_injOn hinj
    have hTsum : ∑ i ∈ T, i = (n + 1) * q := by
      rw [Finset.sum_image hinj, hS'sum, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    have hTsub : T ⊆ (n + 1).factorial.divisors := by
      intro x hx
      obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hx
      have hd' := Nat.dvd_of_mem_divisors (hS'sub hd)
      refine Nat.mem_divisors.mpr ⟨?_, Nat.factorial_ne_zero _⟩
      rw [Nat.factorial_succ, mul_comm (n + 1)]
      exact Nat.mul_dvd_mul_right hd' _
    -- every element of `T` is at least `n + 1 > r`
    have hTge : ∀ x ∈ T, n + 1 ≤ x := by
      intro x hx
      obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hx
      have hdpos : 0 < d := Nat.pos_of_mem_divisors (hS'sub hd)
      simpa using Nat.mul_le_mul_right (n + 1) hdpos
    by_cases hr0 : r = 0
    · refine ⟨T, hTsub, ?_, ?_⟩
      · rw [hTcard]; omega
      · rw [hTsum]; omega
    · have hrT : r ∉ T := fun h => by have := hTge r h; omega
      refine ⟨insert r T, ?_, ?_, ?_⟩
      · refine Finset.insert_subset ?_ hTsub
        refine Nat.mem_divisors.mpr ⟨?_, Nat.factorial_ne_zero _⟩
        exact Nat.dvd_factorial (Nat.pos_of_ne_zero hr0) (by omega)
      · rw [Finset.card_insert_of_notMem hrT, hTcard]; omega
      · rw [Finset.sum_insert hrT, hTsum]; omega

/-- For `n ≥ 2`, `h(n!) ≤ n - 1`. -/
theorem practicalH_factorial_le {n : ℕ} (hn : 2 ≤ n) : practicalH n.factorial ≤ n - 1 := by
  unfold practicalH
  apply Finset.sup_le
  intro m hm
  obtain ⟨hm1, hm2⟩ := Finset.mem_Icc.mp hm
  rcases lt_or_eq_of_le hm2 with hlt | heq
  · obtain ⟨S, hSsub, hScard, hSsum⟩ := exists_divisors_sum_of_lt_factorial (by omega) m hlt
    refine (Nat.sInf_le ?_).trans hScard
    exact ⟨S, hSsub, rfl, S, subset_rfl, hSsum⟩
  · have hmem : m ∈ n.factorial.divisors :=
      Nat.mem_divisors.mpr ⟨heq ▸ dvd_rfl, Nat.factorial_ne_zero _⟩
    refine (Nat.sInf_le (m := ({m} : Finset ℕ).card) ?_).trans ?_
    · exact ⟨{m}, by simpa using hmem, rfl, {m}, subset_rfl, by simp⟩
    · simp; omega

/-- **Erdős's theorem** (`erdos_18_upper_bound` in formal-conjectures): `h(n!) < n` for all
sufficiently large `n` (in fact for all `n ≥ 2`). -/
theorem erdos_18_upper_bound :
    ∀ᶠ n : ℕ in atTop, practicalH (Nat.factorial n) < n := by
  refine eventually_atTop.mpr ⟨2, fun n hn => ?_⟩
  have := practicalH_factorial_le hn
  omega

end Erdos18
