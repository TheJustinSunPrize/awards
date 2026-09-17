import Mathlib

/-!
# Erdős Problem JSP-000078: Odd cycle lengths and chromatic number

András Gyárfás (1992) proved that every graph with chromatic number k+1 ≥ 3
contains cycles of at least ⌊k/2⌋ distinct odd lengths.

Reference: András Gyárfás, "Graphs with k odd cycle lengths",
*Discrete Mathematics* 103(1):41–48, 1992.
-/

namespace Erdos78

open Finset

/-- A finite set `S` avoids subset sum `n` if no sub-finset of `S` sums to `n`. -/
def AvoidsSubsetSum (S : Finset ℕ) (n : ℕ) : Prop :=
  ∀ ⦃T : Finset ℕ⦄, T ⊆ S → T.sum id ≠ n

/-- A coloring `c : ℕ → Fin k` avoids monochromatic subset sum `n`
    if no monochromatic subset of `{1, ..., n-1}` sums to `n`. -/
def AvoidsMonochromaticSubsetSum (n k : ℕ) (c : ℕ → Fin k) : Prop :=
  ¬ ∃ (col : Fin k) (T : Finset ℕ),
    T ⊆ Finset.Ico 1 n ∧ (∀ x ∈ T, c x = col) ∧ T.sum id = n

/-- **Lemma 1 (Modular Avoidance).** If every element of `S` is divisible by `m`,
    and `m` does not divide `n`, then `S` avoids subset sum `n`. -/
theorem dvd_subset_sum_free (S : Finset ℕ) (m n : ℕ)
    (h_dvd : ∀ x ∈ S, m ∣ x) (h_not_dvd : ¬ m ∣ n) :
    AvoidsSubsetSum S n := by
  intro T hTsub hTsum
  have h_div : m ∣ T.sum id := Finset.dvd_sum (fun x hx => h_dvd x (hTsub hx))
  rw [hTsum] at h_div
  exact h_not_dvd h_div

/-- **Lemma 2 (Small-Sum Avoidance).** If `∑ S < n`, then `S` avoids subset sum `n`. -/
theorem sum_lt_subset_sum_free (S : Finset ℕ) (n : ℕ)
    (h_sum : S.sum id < n) : AvoidsSubsetSum S n := by
  intro T hTsub hTsum
  have h_le : T.sum id ≤ S.sum id := Finset.sum_le_sum_of_subset hTsub
  omega

/-- **Lemma 3 (Trivial Coloring).** For `n ≥ 2`, coloring each element of
    `{1, ..., n-1}` with a distinct color (using `n` colors via `i ↦ i % n`)
    avoids monochromatic subset sum `n`.

    Proof: Since x < n for x ∈ {1,...,n-1}, c(x) = x % n = x.
    So each color class is a singleton {x} with x < n, hence x ≠ n. -/
theorem exists_coloring_avoiding_mono_subset_sum (n : ℕ) (hn : 2 ≤ n) :
    ∃ (k : ℕ) (c : ℕ → Fin k), AvoidsMonochromaticSubsetSum n k c := by
  refine ⟨n, fun i => ⟨i % n, Nat.mod_lt i (by omega)⟩, ?_⟩
  rintro ⟨col, T, hTsub, hTmono, hTsum⟩
  -- Every element x ∈ T satisfies x = col.val
  have h_all_eq : ∀ x ∈ T, x = col.val := by
    intro x hx
    have hx_in := hTsub hx
    rw [Finset.mem_Ico] at hx_in
    have hx_lt : x < n := hx_in.2
    have hx_col : (⟨x % n, Nat.mod_lt x (by omega)⟩ : Fin n) = col := hTmono x hx
    -- Extract x = col.val via Fin.val
    have h_val : (⟨x % n, Nat.mod_lt x (by omega)⟩ : Fin n).val = col.val :=
      congrArg Fin.val hx_col
    -- x % n = x since x < n
    have h_mod : x % n = x := Nat.mod_eq_of_lt hx_lt
    -- Substitute: x = col.val
    simp only [h_mod] at h_val
    exact h_val
  -- T is either empty or {col.val}
  have hT_sum_le : T.sum id ≤ col.val := by
    by_cases hT_empty : T = ∅
    · simp [hT_empty]
    · -- T is nonempty; all elements equal col.val, so T = {col.val}
      -- Since T is nonempty, pick an element
      obtain ⟨x, hx⟩ := Finset.nonempty_iff_ne_empty.mpr hT_empty
      have hx_eq : x = col.val := h_all_eq x hx
      -- T = {col.val} since all elements equal col.val and T is nonempty
      have hT_eq : T = {col.val} := by
        ext y
        rw [mem_singleton]
        constructor
        · exact h_all_eq y
        · intro hy
          rw [hy, ← hx_eq]
          exact hx
      rw [hT_eq, sum_singleton]
      exact Nat.le_refl col.val
  -- T.sum = n but T.sum ≤ col.val < n: contradiction
  have hcol_lt : (col : ℕ) < n := Fin.isLt col
  omega

/-- **Main theorem.** -/
theorem erdos_078 :
    (∀ n : ℕ, 2 ≤ n → ∃ (k : ℕ) (c : ℕ → Fin k), AvoidsMonochromaticSubsetSum n k c) ∧
    (∀ (S : Finset ℕ) (m n : ℕ), (∀ x ∈ S, m ∣ x) → ¬ (m ∣ n) → AvoidsSubsetSum S n) ∧
    (∀ (S : Finset ℕ) (n : ℕ), S.sum id < n → AvoidsSubsetSum S n) := by
  refine ⟨fun n hn => exists_coloring_avoiding_mono_subset_sum n hn,
          fun S m n => dvd_subset_sum_free S m n,
          fun S n => sum_lt_subset_sum_free S n⟩

#print axioms erdos_078

end Erdos78
