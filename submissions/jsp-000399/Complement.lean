/-
SPDX-License-Identifier: Apache-2.0
JSP-000399 / Erdos #494, additional formalized branches, 2026-09-16.
Known-result formalization; no discovery or priority claim.
Scope: all k >= 3, cardinality 2k counterexamples in positive integers;
unique recovery of three integer entries from pair-sum multisets.
Finite sets are represented by Nodup lists, multiset equality by List.Perm.
No formal bridge to mathlib Finset Complex is included.
Reference: https://www.erdosproblems.com/494
-/
import Std
namespace Recovery

def ksums : Nat → List Int → List Int
  | 0, _ => [0]
  | _+1, [] => []
  | k+1, a::xs => (ksums k xs).map (a+·) ++ ksums (k+1) xs

theorem ksums_too_large (xs : List Int) (k : Nat) (h : xs.length < k) :
    ksums k xs = [] := by
  induction xs generalizing k with
  | nil => cases k <;> simp_all [ksums]
  | cons a xs ih =>
    cases k with
    | zero => simp at h
    | succ k =>
      have h1 : xs.length < k := by simp at h; omega
      have h2 : xs.length < k+1 := by omega
      simp [ksums, ih k h1, ih (k+1) h2]

theorem ksums_full (xs : List Int) : ksums xs.length xs = [xs.sum] := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    simp [ksums, ih, ksums_too_large xs (xs.length+1) (by omega)]

theorem complement (n m : Nat) (xs : List Int) (hlen : xs.length = n+m) :
    (ksums n xs).Perm ((ksums m xs).map (xs.sum - ·)) := by
  induction xs generalizing n m with
  | nil =>
    have hn : n=0 := by simp at hlen; omega
    have hm : m=0 := by simp at hlen; omega
    subst n; subst m
    simp [ksums]
  | cons a xs ih =>
    cases n with
    | zero =>
      have hm : m = (a::xs).length := by omega
      subst m
      rw [ksums_full]
      simp [ksums]
    | succ n =>
      cases m with
      | zero =>
        have hn : n+1 = (a::xs).length := by omega
        rw [hn, ksums_full]
        simp [ksums]
      | succ m =>
        have h1 : xs.length = n+(m+1) := by simp at hlen; omega
        have h2 : xs.length = (n+1)+m := by omega
        have hi1 := (ih n (m+1) h1).map (a+·)
        have hi2 := ih (n+1) m h2
        have ht := hi1.append hi2
        have hc := List.perm_append_comm (l₁ := ((ksums (m+1) xs).map (xs.sum-·)).map (a+·))
          (l₂ := (ksums m xs).map (xs.sum-·))
        have hh := ht.trans hc
        have cancel : (fun x : Int => a + (xs.sum - (a+x))) =
            (fun x : Int => xs.sum-x) := by funext x; omega
        simpa [ksums, List.map_append, List.map_map, Function.comp_def,
          Int.add_sub_assoc, cancel] using hh

#print axioms complement
end Recovery

namespace Recovery

theorem ksums_neg (k : Nat) (xs : List Int) :
    ksums k (xs.map (-·)) = (ksums k xs).map (-·) := by
  induction xs generalizing k with
  | nil => cases k <;> simp [ksums]
  | cons a xs ih =>
    cases k with
    | zero => simp [ksums]
    | succ k => simp [ksums, ih, List.map_append, List.map_map, Function.comp_def, Int.neg_add]

theorem balanced_reflection (k : Nat) (xs : List Int)
    (hlen : xs.length = k+k) (hsum : xs.sum=0) :
    (ksums k xs).Perm (ksums k (xs.map (-·))) := by
  rw [ksums_neg]
  simpa [hsum] using complement k k xs hlen

def balancedFamily : Nat → List Int
  | 0 => [-5,-1,0,1,2,3]
  | n+1 => (10+(n:Int)) :: (-(10+(n:Int))) :: balancedFamily n

structure BalancedInvariant (n : Nat) : Prop where
  distinct : (balancedFamily n).Nodup
  size : (balancedFamily n).length = 6+2*n
  total : (balancedFamily n).sum = 0
  bound : ∀ x ∈ balancedFamily n, -(10+(n:Int)) < x ∧ x < 10+(n:Int)
  negFive : -5 ∈ balancedFamily n
  notFive : 5 ∉ balancedFamily n

theorem balanced_invariant (n : Nat) : BalancedInvariant n := by
  induction n with
  | zero =>
    constructor
    · decide
    · rfl
    · rfl
    · intro x hx
      simp [balancedFamily] at hx
      omega
    · decide
    · decide
  | succ n ih =>
    constructor
    · simp only [balancedFamily, List.nodup_cons, List.mem_cons]
      refine ⟨?_, ?_, ih.distinct⟩
      · intro h
        rcases h with h | h
        · omega
        · have := ih.bound _ h; omega
      · intro h
        have := ih.bound _ h; omega
    · simp only [balancedFamily, List.length_cons, ih.size]
      omega
    · simp only [balancedFamily, List.sum_cons, ih.total]
      omega
    · intro x hx
      simp only [balancedFamily, List.mem_cons] at hx
      rcases hx with hx | hx | hx
      · subst x; omega
      · subst x; omega
      · have := ih.bound _ hx; omega
    · simp only [balancedFamily, List.mem_cons]
      exact Or.inr (Or.inr ih.negFive)
    · simp only [balancedFamily, List.mem_cons]
      intro h
      rcases h with h | h | h
      · omega
      · omega
      · exact ih.notFive h

theorem neg_nodup (xs : List Int) (hx : xs.Nodup) : (xs.map (-·)).Nodup := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    obtain ⟨ha,hr⟩ := List.nodup_cons.mp hx
    apply List.nodup_cons.mpr
    refine ⟨?_, ih hr⟩
    intro he
    simp only [List.mem_map] at he
    obtain ⟨b,hb,he⟩ := he
    have hba : b=a := by omega
    exact ha (hba ▸ hb)

theorem family_not_reflection (n : Nat) :
    ¬ (balancedFamily n).Perm ((balancedFamily n).map (-·)) := by
  intro h
  have hi := balanced_invariant n
  have he := h.mem_iff.mp hi.negFive
  simp only [List.mem_map] at he
  obtain ⟨b,hb,he⟩ := he
  have hb5 : b=5 := by omega
  exact hi.notFive (hb5 ▸ hb)

/-- For every k >= 3, distinct sets of 2k integers have identical k-sum multisets. -/
theorem all_k_counterexamples (k : Nat) (hk : 3 ≤ k) :
    ∃ xs ys : List Int, xs.Nodup ∧ ys.Nodup ∧
      xs.length=2*k ∧ ys.length=2*k ∧
      ¬ xs.Perm ys ∧ (ksums k xs).Perm (ksums k ys) := by
  let n := k-3
  have hi := balanced_invariant n
  have hl : (balancedFamily n).length=2*k := by
    have hs := hi.size
    dsimp [n] at *
    omega
  refine ⟨balancedFamily n, (balancedFamily n).map (-·), hi.distinct,
    neg_nodup _ hi.distinct, hl, ?_, family_not_reflection n, ?_⟩
  · simpa using hl
  · exact balanced_reflection k _ (by omega) hi.total

#print axioms all_k_counterexamples
end Recovery

namespace Recovery

theorem ksums_shift (k : Nat) (t : Int) (xs : List Int) :
    ksums k (xs.map (t+·)) = (ksums k xs).map ((k:Int)*t+·) := by
  induction xs generalizing k with
  | nil => cases k <;> simp [ksums]
  | cons a xs ih =>
    cases k with
    | zero => simp [ksums]
    | succ k =>
      simp only [List.map_cons, ksums]
      rw [ih k, ih (k+1)]
      simp [List.map_append, List.map_map, Function.comp_def, Int.add_mul,
        Int.add_assoc, Int.add_left_comm, Int.add_comm]

theorem shift_nodup (t : Int) (xs : List Int) (hx : xs.Nodup) :
    (xs.map (t+·)).Nodup := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    obtain ⟨ha, hr⟩ := List.nodup_cons.mp hx
    apply List.nodup_cons.mpr
    refine ⟨?_, ih hr⟩
    intro h
    simp only [List.mem_map] at h
    obtain ⟨b,hb,he⟩ := h
    have hba : b=a := by omega
    exact ha (hba ▸ hb)

theorem unshift_perm (t : Int) (xs ys : List Int)
    (h : (xs.map (t+·)).Perm (ys.map (t+·))) : xs.Perm ys := by
  have hi := h.map (fun x => x-t)
  have cancel : (fun x : Int => (t+x)-t) = id := by funext x; simp; omega
  simpa only [List.map_map, Function.comp_def, cancel, List.map_id] using hi

/-- Counterexamples can be chosen entirely among positive integers. -/
theorem all_k_positive_counterexamples (k : Nat) (hk : 3 ≤ k) :
    ∃ xs ys : List Int, xs.Nodup ∧ ys.Nodup ∧
      xs.length=2*k ∧ ys.length=2*k ∧
      (∀ x ∈ xs, 0<x) ∧ (∀ y ∈ ys, 0<y) ∧
      ¬ xs.Perm ys ∧ (ksums k xs).Perm (ksums k ys) := by
  let n := k-3
  let t : Int := 11+(n:Int)
  let a := balancedFamily n
  let b := a.map (-·)
  have hi := balanced_invariant n
  have hl : a.length=2*k := by
    have hs := hi.size
    dsimp [a,n] at *
    omega
  refine ⟨a.map (t+·), b.map (t+·), shift_nodup _ _ hi.distinct,
    shift_nodup _ _ (neg_nodup _ hi.distinct), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa using hl
  · simpa [b] using hl
  · intro x hx
    simp only [List.mem_map] at hx
    obtain ⟨y,hy,he⟩ := hx
    have hb := hi.bound y hy
    dsimp [t] at he
    omega
  · intro x hx
    simp only [b, List.mem_map] at hx
    obtain ⟨y,⟨z,hz,hzy⟩,hyx⟩ := hx
    have hb := hi.bound z hz
    dsimp [t] at hyx
    omega
  · intro he
    exact family_not_reflection n (unshift_perm t a b he)
  · rw [ksums_shift, ksums_shift]
    exact (balanced_reflection k a (by omega) hi.total).map ((k:Int)*t+·)

theorem perm_sum {xs ys : List Int} (h : xs.Perm ys) : xs.sum=ys.sum := by
  induction h with
  | nil => rfl
  | cons a h ih => simpa using congrArg (a+·) ih
  | swap a b xs => simp [Int.add_left_comm]
  | trans h1 h2 ih1 ih2 => exact ih1.trans ih2

/-- Three integer entries are recoverable from the multiset of pair sums.
The theorem even permits repeated entries. -/
theorem recover_three (a b c d e f : Int)
    (h : [a+b,a+c,b+c].Perm [d+e,d+f,e+f]) :
    [a,b,c].Perm [d,e,f] := by
  have hs := perm_sum h
  simp only [List.sum_cons, List.sum_nil] at hs
  have total : a+b+c=d+e+f := by omega
  have hm := h.map (fun x => a+b+c-x)
  have left : [a+b,a+c,b+c].map (fun x => a+b+c-x) = [c,b,a] := by
    simp only [List.map_cons, List.map_nil]
    congr 1 <;> (try congr 1) <;> (try congr 1) <;> omega
  have right : [d+e,d+f,e+f].map (fun x => a+b+c-x) = [f,e,d] := by
    simp only [List.map_cons, List.map_nil]
    congr 1 <;> (try congr 1) <;> (try congr 1) <;> omega
  rw [left,right] at hm
  exact (List.reverse_perm [a,b,c]).symm.trans (hm.trans (List.reverse_perm [d,e,f]))

theorem length_three (xs : List Int) (h : xs.length=3) :
    ∃ a b c : Int, xs=[a,b,c] := by
  cases xs with
  | nil => simp at h
  | cons a xs =>
    cases xs with
    | nil => simp at h
    | cons b xs =>
      cases xs with
      | nil => simp at h
      | cons c xs =>
        have hz : xs.length=0 := by simpa using h
        have he : xs=[] := List.length_eq_zero_iff.mp hz
        subst xs
        exact ⟨a,b,c,rfl⟩

/-- Same enumeration function and multiset semantics as the counterexamples. -/
theorem three_element_unique (xs ys : List Int)
    (hx : xs.length=3) (hy : ys.length=3)
    (h : (ksums 2 xs).Perm (ksums 2 ys)) : xs.Perm ys := by
  obtain ⟨a,b,c,rfl⟩ := length_three xs hx
  obtain ⟨d,e,f,rfl⟩ := length_three ys hy
  apply recover_three a b c d e f
  simpa [ksums] using h

#print axioms all_k_positive_counterexamples
#print axioms three_element_unique
end Recovery
