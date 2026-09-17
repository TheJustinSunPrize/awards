import Mathlib.Computability.DFA
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Exact reset threshold of the Černý automata

The parameter `n` describes an automaton with `n + 2` states. The letter `true`
rotates all states, and `false` moves only the last state to zero.
This is the classical extremal family, not a proof of the open Černý conjecture.
-/

namespace Cerny

abbrev State (n : ℕ) := Fin (n + 2)

def rotate {n : ℕ} (q : State n) : State n :=
  ⟨(q.val + 1) % (n + 2), Nat.mod_lt _ (by omega)⟩

def merge {n : ℕ} (q : State n) : State n :=
  if q.val = n + 1 then 0 else q

def automaton (n : ℕ) : DFA Bool (State n) where
  step q a := if a then rotate q else merge q
  start := 0
  accept := ∅

abbrev run {n : ℕ} (w : List Bool) (q : State n) := (automaton n).evalFrom q w

def IsReset (n : ℕ) (w : List Bool) : Prop := ∃ q : State n, ∀ i, run w i = q

/-- Number of rotation letters. -/
def rotations (w : List Bool) : ℕ := w.count true

@[simp] theorem rotations_nil : rotations [] = 0 := rfl
@[simp] theorem rotations_true (w : List Bool) : rotations (true :: w) = rotations w + 1 := by
  simp [rotations]
@[simp] theorem rotations_false (w : List Bool) : rotations (false :: w) = rotations w := by
  simp [rotations]

/-- Number of merging letters which actually move this trajectory. -/
def effective {n : ℕ} : List Bool → State n → ℕ
  | [], _ => 0
  | true :: w, q => effective w (rotate q)
  | false :: w, q => (if q.val = n + 1 then 1 else 0) + effective w (merge q)

@[simp] theorem run_nil {n : ℕ} (q : State n) : run [] q = q := rfl
@[simp] theorem run_true {n : ℕ} (w : List Bool) (q : State n) :
    run (true :: w) q = run w (rotate q) := rfl
@[simp] theorem run_false {n : ℕ} (w : List Bool) (q : State n) :
    run (false :: w) q = run w (merge q) := rfl

theorem run_append {n : ℕ} (u v : List Bool) (q : State n) :
    run (u ++ v) q = run v (run u q) :=
  DFA.evalFrom_of_append _ _ _ _

/-- Effective merges are a subset of the merge letters of the word. -/
theorem effective_le_merges {n : ℕ} (w : List Bool) (q : State n) :
    rotations w + effective w q ≤ w.length := by
  induction w generalizing q with
  | nil => simp [rotations, effective]
  | cons a w ih =>
    cases a
    · have h := ih (merge q)
      simp only [rotations_false, effective, List.length_cons]
      split_ifs <;> omega
    · have h := ih (rotate q)
      simp only [rotations_true, effective, List.length_cons]
      omega

/-- The lift to residues records every rotation and every effective merge. -/
theorem residue_invariant {n : ℕ} (w : List Bool) (q : State n) :
    ((run w q).val : ZMod (n + 2)) =
      (q.val : ZMod (n + 2)) + rotations w + effective w q := by
  induction w generalizing q with
  | nil => simp [rotations, effective]
  | cons a w ih =>
    cases a
    · rw [run_false, ih]
      by_cases hq : q.val = n + 1
      · have hz : ((n + 2 : ℕ) : ZMod (n + 2)) = 0 := ZMod.natCast_self _
        simp only [rotations_false, effective, hq, merge, ↓reduceIte,
          Fin.val_zero, Nat.cast_zero, Nat.cast_add, Nat.cast_one]
        push_cast at hz
        linear_combination -hz
      · simp [effective, merge, hq]
    · rw [run_true, ih]
      simp only [rotations_true, effective,
        rotate, ZMod.natCast_mod, Nat.cast_add, Nat.cast_one]
      ring

/-- Each effective merge consumes a full turn of progress, except for the
initial position. This inequality holds for every word and initial state. -/
theorem progress_invariant {n : ℕ} (w : List Bool) (q : State n) :
    (n + 1) * effective w q + (run w q).val ≤ rotations w + q.val := by
  induction w generalizing q with
  | nil => simp [rotations, effective]
  | cons a w ih =>
    cases a
    · have h := ih (merge q)
      rw [run_false]
      by_cases hq : q.val = n + 1
      · simp [merge, hq] at h
        simp only [effective, rotations_false, hq, ↓reduceIte, merge, Nat.mul_add]
        omega
      · simpa [effective, merge, hq] using h
    · have h := ih (rotate q)
      have hr : (rotate q).val ≤ q.val + 1 := Nat.mod_le _ _
      simp only [effective, run_true, rotations_true]
      omega

/-- Synchronization forces one trajectory to undergo at least `n + 1`
effective merging steps; no normal-form restriction on the word is used. -/
theorem exists_many_effective {n : ℕ} {w : List Bool} (hw : IsReset n w) :
    ∃ i : State n, n + 1 ≤ effective w i := by
  obtain ⟨q, hq⟩ := hw
  let z : ZMod (n + 2) := (q.val : ZMod (n + 2)) - rotations w + 1
  let i : State n := ⟨z.val, ZMod.val_lt z⟩
  have h := residue_invariant w i
  rw [hq i] at h
  have hi : (i.val : ZMod (n + 2)) = z := ZMod.natCast_zmod_val z
  rw [hi] at h
  have he : (effective w i : ZMod (n + 2)) = -1 := by
    dsimp [z] at h
    linear_combination -h
  have hv := congrArg ZMod.val he
  rw [ZMod.val_natCast] at hv
  have hn : (-1 : ZMod (n + 2)).val = n + 1 := ZMod.val_neg_one (n + 1)
  rw [hn] at hv
  exact ⟨i, hv ▸ Nat.mod_le (effective w i) (n + 2)⟩

/-- Every reset word of the `(n + 2)`-state Černý automaton has at least
`(n + 1)^2` letters. -/
theorem reset_length_lower_bound {n : ℕ} {w : List Bool} (hw : IsReset n w) :
    (n + 1) ^ 2 ≤ w.length := by
  obtain ⟨i, hi⟩ := exists_many_effective hw
  have hp := progress_invariant w i
  have he := effective_le_merges w i
  have hi_bound := i.isLt
  have hmul := Nat.mul_le_mul_left (n + 1) hi
  nlinarith

theorem run_rotations {n : ℕ} (k : ℕ) (q : State n) :
    (run (List.replicate k true) q).val = (q.val + k) % (n + 2) := by
  induction k generalizing q with
  | zero => simp [Nat.mod_eq_of_lt q.isLt]
  | succ k ih =>
    rw [List.replicate_succ, run_true, ih]
    change ((q.val + 1) % (n + 2) + k) % (n + 2) = _
    rw [Nat.mod_add_mod]
    congr 1
    omega

/-- One block consists of `n + 1` rotations and one merge. -/
def block (n : ℕ) : List Bool := List.replicate (n + 1) true ++ [false]

theorem run_block_val {n : ℕ} (q : State n) :
    (run (block n) q).val = q.val - 1 := by
  rw [block, run_append]
  change (merge (run (List.replicate (n + 1) true) q)).val = q.val - 1
  have hr := run_rotations (n + 1) q
  by_cases hq : q.val = 0
  · have hv : (run (List.replicate (n + 1) true) q).val = n + 1 := by
      rw [hr, hq, zero_add, Nat.mod_eq_of_lt (by omega)]
    simp [merge, hv, hq]
  · have hv : (run (List.replicate (n + 1) true) q).val = q.val - 1 := by
      rw [hr, show q.val + (n + 1) = (n + 2) + (q.val - 1) by omega,
        Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
    have hlast : (run (List.replicate (n + 1) true) q).val ≠ n + 1 := by
      rw [hv]
      omega
    rw [merge, if_neg hlast]
    exact hv

def blocks (n : ℕ) : ℕ → List Bool
  | 0 => []
  | k + 1 => block n ++ blocks n k

theorem run_blocks_val {n : ℕ} (k : ℕ) (q : State n) :
    (run (blocks n k) q).val = q.val - k := by
  induction k generalizing q with
  | zero => simp [blocks]
  | succ k ih =>
    rw [blocks, run_append, ih, run_block_val]
    omega

theorem length_blocks (n k : ℕ) : (blocks n k).length = (n + 2) * k := by
  induction k with
  | zero => simp [blocks]
  | succ k ih =>
    simp only [blocks, block, List.length_append, List.length_replicate,
      List.length_singleton, ih]
    ring

/-- The classical word `b (a^(n+1) b)^n` for `n+2` states. -/
def resetWord (n : ℕ) : List Bool := false :: blocks n n

theorem resetWord_resets (n : ℕ) : IsReset n (resetWord n) := by
  refine ⟨0, fun q => ?_⟩
  apply Fin.ext
  rw [resetWord, run_false, run_blocks_val]
  change (merge q).val - n = 0
  by_cases hq : q.val = n + 1
  · simp [merge, hq]
  · simp only [merge, if_neg hq]
    omega

theorem resetWord_length (n : ℕ) : (resetWord n).length = (n + 1) ^ 2 := by
  rw [resetWord, List.length_cons, length_blocks]
  ring

/-- Exact, attained reset threshold for every automaton in Černý's family. -/
theorem exact_reset_threshold (n L : ℕ) :
    (∃ w : List Bool, IsReset n w ∧ w.length ≤ L) ↔ (n + 1) ^ 2 ≤ L := by
  constructor
  · rintro ⟨w, hw, hL⟩
    exact (reset_length_lower_bound hw).trans hL
  · intro hL
    exact ⟨resetWord n, resetWord_resets n, by simpa [resetWord_length] using hL⟩

/-- For every state count `N ≥ 2`, there is an actual DFA on `Fin N` whose
reset threshold is exactly `(N - 1)^2`. This establishes sharpness of the
conjectured bound without asserting the conjecture for arbitrary DFAs. -/
theorem sharp_family (N : ℕ) (hN : 2 ≤ N) :
    ∃ M : DFA Bool (Fin N), ∀ L : ℕ,
      (∃ w : List Bool, (∃ q : Fin N, ∀ i, M.evalFrom i w = q) ∧ w.length ≤ L) ↔
        (N - 1) ^ 2 ≤ L := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le' hN
  refine ⟨automaton n, fun L => ?_⟩
  simpa [IsReset] using exact_reset_threshold n L

end Cerny
