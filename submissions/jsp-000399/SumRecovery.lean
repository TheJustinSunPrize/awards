/-
SPDX-License-Identifier: Apache-2.0
JSP-000399 / Erdos 494: two non-uniqueness branches.
Prepared 2026-09-16. This is a formalization of known mathematical phenomena,
not a claim of new discovery or first formalization.
References:
https://www.erdosproblems.com/494
https://github.com/TheJustinSunPrize/awards/blob/f4e7173d89dfe91022a185427d63452c8ffbf6ae/problems/catalog-0301-0400.md#JSP-000399
Scope: all power-of-two cardinalities for pair sums, and cardinality six for
triple sums (including all nonnegative translations). This does not prove a
uniqueness theorem for other cardinalities or solve every variant of #494.
Representation: duplicate-free lists denote finite sets; List.Perm compares
multisets including multiplicity. All witnesses are natural numbers.
-/
import Std
namespace SumRecovery

def pairSums : List Nat → List Nat
  | [] => []
  | a :: xs => xs.map (a + ·) ++ pairSums xs

def cross (xs ys : List Nat) : List Nat := xs.flatMap (fun a => ys.map (a + ·))
def shift (t : Nat) (xs : List Nat) := xs.map (t + ·)

theorem shuffle (a b c d : List Nat) :
    ((a ++ b) ++ (c ++ d)).Perm ((a ++ c) ++ (b ++ d)) := by
  simpa only [List.append_assoc] using
    (List.perm_append_comm_assoc b c d).append_left a

theorem cross_cons_right (a : Nat) (xs ys : List Nat) :
    (cross xs (a :: ys)).Perm (xs.map (· + a) ++ cross xs ys) := by
  induction xs with
  | nil => simp [cross]
  | cons x xs ih =>
    simp only [cross, List.flatMap_cons, List.map_cons] at *
    -- A leading x+a is followed by the row for x, then all remaining rows.
    have h1 := ih.append_left ((x+a) :: ys.map (x + ·))
    exact h1.trans (by
      simpa only [List.cons_append, List.append_assoc] using
        (shuffle [x+a] (ys.map (x+·)) (xs.map (·+a))
          (xs.flatMap (fun b => ys.map (b+·)))))

theorem cross_comm (xs ys : List Nat) : (cross xs ys).Perm (cross ys xs) := by
  induction xs with
  | nil => simp [cross]
  | cons a xs ih =>
    have h := ih.append_left (ys.map (a+·))
    have hm : ys.map (a+·) = ys.map (·+a) := by
      apply List.map_congr_left
      intro b hb
      omega
    simpa only [cross, List.flatMap_cons, hm] using
      h.trans (by simpa only [hm] using (cross_cons_right a ys xs).symm)

theorem pairSums_append (xs ys : List Nat) :
    (pairSums (xs++ys)).Perm (pairSums xs ++ cross xs ys ++ pairSums ys) := by
  induction xs with
  | nil => simp [pairSums, cross]
  | cons a xs ih =>
    simp only [List.cons_append, pairSums, List.map_append]
    have h := ih.append_left (xs.map (a+·) ++ ys.map (a+·))
    exact h.trans (by
      simpa only [cross, List.flatMap_cons, List.append_assoc] using
        shuffle (xs.map (a+·)) (ys.map (a+·)) (pairSums xs)
          (cross xs ys ++ pairSums ys))

theorem pairSums_shift (t : Nat) (xs : List Nat) :
    pairSums (shift t xs) = shift (2*t) (pairSums xs) := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    simp only [shift, List.map_cons, pairSums, List.map_append, List.map_map] at *
    rw [ih]
    congr 1
    apply List.map_congr_left
    intro b hb
    simp only [Function.comp_apply]
    omega

theorem cross_shift_right (t : Nat) (xs ys : List Nat) :
    cross xs (shift t ys) = shift t (cross xs ys) := by
  simp only [cross, shift, List.map_flatMap, List.map_map]
  congr 1
  funext a
  apply List.map_congr_left
  intro b hb
  simp only [Function.comp_apply]
  omega

theorem doubling_preserves (t : Nat) (xs ys : List Nat)
    (h : (pairSums xs).Perm (pairSums ys)) :
    (pairSums (xs ++ shift t ys)).Perm (pairSums (ys ++ shift t xs)) := by
  have hc : (cross xs (shift t ys)).Perm (cross ys (shift t xs)) := by
    rw [cross_shift_right, cross_shift_right]
    exact (cross_comm xs ys).map (t+·)
  have hp : (pairSums (shift t ys)).Perm (pairSums (shift t xs)) := by
    rw [pairSums_shift, pairSums_shift]
    exact h.symm.map (2*t+·)
  exact (pairSums_append xs (shift t ys)).trans
    (((h.append hc).append hp).trans (pairSums_append ys (shift t xs)).symm)

def family : Nat → List Nat × List Nat
  | 0 => ([0], [1])
  | m+1 =>
    let (xs, ys) := family m
    (xs ++ shift (2^(m+1)) ys, ys ++ shift (2^(m+1)) xs)

abbrev A (m : Nat) := (family m).1
abbrev B (m : Nat) := (family m).2

theorem A_succ (m : Nat) : A (m+1) = A m ++ shift (2^(m+1)) (B m) := rfl
theorem B_succ (m : Nat) : B (m+1) = B m ++ shift (2^(m+1)) (A m) := rfl

theorem nodup_shift (t : Nat) (xs : List Nat) (h : xs.Nodup) : (shift t xs).Nodup := by
  induction xs with
  | nil => simp [shift]
  | cons a xs ih =>
    obtain ⟨ha, hr⟩ := List.nodup_cons.mp h
    apply List.nodup_cons.mpr
    constructor
    · intro hm
      obtain ⟨b, hb, he⟩ := List.mem_map.mp hm
      have heq : b=a := by
        change t+b=t+a at he
        omega
      exact ha (heq ▸ hb)
    · exact ih hr

theorem nodup_join (t : Nat) (xs ys : List Nat) (hx : xs.Nodup) (hy : ys.Nodup)
    (hb : ∀ x ∈ xs, x<t) : (xs ++ shift t ys).Nodup := by
  apply List.nodup_append.mpr
  refine ⟨hx, nodup_shift t ys hy, ?_⟩
  intro a ha b hb'
  obtain ⟨c, hc, he⟩ := List.mem_map.mp hb'
  have := hb a ha
  omega

structure Invariant (m : Nat) : Prop where
  nodupA : (A m).Nodup
  nodupB : (B m).Nodup
  sizeA : (A m).length = 2^m
  sizeB : (B m).length = 2^m
  boundA : ∀ x ∈ A m, x < 2^(m+1)
  boundB : ∀ x ∈ B m, x < 2^(m+1)
  zeroA : 0 ∈ A m
  zeroB : 0 ∉ B m
  sameSums : (pairSums (A m)).Perm (pairSums (B m))

theorem invariant (m : Nat) : Invariant m := by
  induction m with
  | zero =>
    constructor <;> simp [A, B, family, pairSums]
  | succ m ih =>
    have ht : 0 < 2^(m+1) := Nat.pow_pos (by decide)
    have hnext : 2^(m+1+1) = 2^(m+1) + 2^(m+1) := by
      rw [Nat.pow_succ]; omega
    constructor
    · rw [A_succ]
      exact nodup_join _ _ _ ih.nodupA ih.nodupB ih.boundA
    · rw [B_succ]
      exact nodup_join _ _ _ ih.nodupB ih.nodupA ih.boundB
    · rw [A_succ]
      simp only [List.length_append, shift, List.length_map, ih.sizeA, ih.sizeB,
        Nat.pow_succ]
      omega
    · rw [B_succ]
      simp only [List.length_append, shift, List.length_map, ih.sizeA, ih.sizeB,
        Nat.pow_succ]
      omega
    · intro x hx
      rw [A_succ] at hx
      rcases List.mem_append.mp hx with hx | hx
      · have := ih.boundA x hx; omega
      · obtain ⟨y, hy, he⟩ := List.mem_map.mp hx
        have := ih.boundB y hy; omega
    · intro x hx
      rw [B_succ] at hx
      rcases List.mem_append.mp hx with hx | hx
      · have := ih.boundB x hx; omega
      · obtain ⟨y, hy, he⟩ := List.mem_map.mp hx
        have := ih.boundA y hy; omega
    · rw [A_succ]
      exact List.mem_append.mpr (Or.inl ih.zeroA)
    · rw [B_succ]
      intro hx
      rcases List.mem_append.mp hx with hx | hx
      · exact ih.zeroB hx
      · obtain ⟨y, hy, he⟩ := List.mem_map.mp hx
        omega
    · rw [A_succ, B_succ]
      exact doubling_preserves _ _ _ ih.sameSums

/-- For every m, two different finite sets of cardinality 2^m have identical
multisets of sums of two distinct elements. Nodup ensures these lists are sets;
Perm of the sums retains multiplicities, and non-Perm ensures distinct sets. -/
theorem power_two_counterexamples (m : Nat) :
    ∃ xs ys : List Nat, xs.Nodup ∧ ys.Nodup ∧
      xs.length = 2^m ∧ ys.length = 2^m ∧
      ¬ xs.Perm ys ∧ (pairSums xs).Perm (pairSums ys) := by
  have h := invariant m
  refine ⟨A m, B m, h.nodupA, h.nodupB, h.sizeA, h.sizeB, ?_, h.sameSums⟩
  intro he
  exact h.zeroB (he.mem_iff.mp h.zeroA)


/-- Enumerate sums over k-element subcollections of a list, one entry per
choice of positions. For a Nodup input, these are choices of distinct elements.
Entries of equal value are deliberately retained rather than deduplicated. -/
def sums : Nat → List Nat → List Nat
  | 0, _ => [0]
  | _+1, [] => []
  | k+1, a::xs => (sums k xs).map (a+·) ++ sums (k+1) xs

theorem sums_one (xs : List Nat) : sums 1 xs = xs := by
  induction xs with
  | nil => rfl
  | cons a xs ih => simp [sums, ih]

theorem sums_two (xs : List Nat) : sums 2 xs = pairSums xs := by
  induction xs with
  | nil => rfl
  | cons a xs ih => simp [sums, sums_one, pairSums, ih]

theorem sums_shift (k t : Nat) (xs : List Nat) :
    sums k (shift t xs) = shift (k*t) (sums k xs) := by
  induction xs generalizing k with
  | nil => cases k <;> simp [shift, sums]
  | cons a xs ih =>
    cases k with
    | zero => simp [sums, shift]
    | succ k =>
      simp only [shift, List.map_cons, sums] at *
      rw [ih k, ih (k+1)]
      simp [List.map_append, List.map_map, Function.comp_def, Nat.add_mul,
        Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

def tripleA : List Nat := [1,5,6,7,8,9]
def tripleB : List Nat := [3,4,5,6,7,11]

theorem triple_multisets : (sums 3 tripleA).Perm (sums 3 tripleB) := by decide

theorem triple_twenty : (sums 3 tripleA).length = 20 ∧
    (sums 3 tripleB).length = 20 := by decide

/-- A complete six-element counterexample to unconditional unique recovery
from triple sums, for each nonnegative translation t. -/
theorem triple_counterexamples (t : Nat) :
    ∃ xs ys : List Nat, xs.Nodup ∧ ys.Nodup ∧
      xs.length = 6 ∧ ys.length = 6 ∧
      (∀ x ∈ xs, 0<x) ∧ (∀ y ∈ ys, 0<y) ∧
      ¬ xs.Perm ys ∧ (sums 3 xs).Perm (sums 3 ys) := by
  refine ⟨shift t tripleA, shift t tripleB,
    nodup_shift _ _ (by decide), nodup_shift _ _ (by decide), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [shift, tripleA]
  · simp [shift, tripleB]
  · intro x hx
    simp only [shift, List.mem_map] at hx
    obtain ⟨y, hy, he⟩ := hx
    have hp : 0<y := by
      simp [tripleA] at hy
      omega
    omega
  · intro x hx
    simp only [shift, List.mem_map] at hx
    obtain ⟨y, hy, he⟩ := hx
    have hp : 0<y := by
      simp [tripleB] at hy
      omega
    omega
  · intro h
    have ha : t+1 ∈ shift t tripleA := by simp [shift, tripleA]
    have hb := h.mem_iff.mp ha
    simp [shift, tripleB] at hb
  · rw [sums_shift, sums_shift]
    exact triple_multisets.map (3*t+·)

/-- The power-of-two family can be chosen entirely among positive integers. -/
theorem power_two_positive_counterexamples (m : Nat) :
    ∃ xs ys : List Nat, xs.Nodup ∧ ys.Nodup ∧
      xs.length = 2^m ∧ ys.length = 2^m ∧
      (∀ x ∈ xs, 0<x) ∧ (∀ y ∈ ys, 0<y) ∧
      ¬ xs.Perm ys ∧ (sums 2 xs).Perm (sums 2 ys) := by
  have h := invariant m
  refine ⟨shift 1 (A m), shift 1 (B m), nodup_shift _ _ h.nodupA,
    nodup_shift _ _ h.nodupB, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [shift] using h.sizeA
  · simpa [shift] using h.sizeB
  · intro x hx
    simp only [shift, List.mem_map] at hx
    obtain ⟨y, hy, he⟩ := hx
    omega
  · intro x hx
    simp only [shift, List.mem_map] at hx
    obtain ⟨y, hy, he⟩ := hx
    omega
  · intro he
    have ha : 1 ∈ shift 1 (A m) := List.mem_map.mpr ⟨0,h.zeroA,rfl⟩
    have hb := he.mem_iff.mp ha
    obtain ⟨y, hy, hye⟩ := List.mem_map.mp hb
    have hz : y=0 := by change 1+y=1 at hye; omega
    exact h.zeroB (hz ▸ hy)
  · rw [sums_two, sums_two, pairSums_shift, pairSums_shift]
    exact h.sameSums.map (2*1+·)

/-- Explicit equality for the translated witnesses, not merely an existential. -/
theorem translated_triple_multisets (t : Nat) :
    (sums 3 (shift t tripleA)).Perm (sums 3 (shift t tripleB)) := by
  rw [sums_shift, sums_shift]
  exact triple_multisets.map (3*t+·)

theorem triple_count_equal (v : Nat) :
    (sums 3 tripleA).count v = (sums 3 tripleB).count v :=
  triple_multisets.count_eq v

#print axioms translated_triple_multisets
#print axioms triple_multisets
#print axioms triple_count_equal
#print axioms triple_counterexamples
#print axioms power_two_positive_counterexamples
end SumRecovery
