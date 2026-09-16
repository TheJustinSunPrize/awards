import Std

/-!
A finite counterexample to the additional exact formula in Erdős Problem 795
(JSP-000653). This does not prove the separate asymptotic upper bound.
The fact that the exact formula is false was already established by Raghavan.
All concrete certificates below are checked by the Lean kernel.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

namespace JSP653

/-- One entry for each positional subset, including the empty subset. -/
def subsetProducts : List Nat → List Nat
  | [] => [1]
  | a :: xs => subsetProducts xs ++ (subsetProducts xs).map (a * ·)

theorem subsetProducts_length (xs : List Nat) :
    (subsetProducts xs).length = 2 ^ xs.length := by
  induction xs with
  | nil => rfl
  | cons a xs ih => simp [subsetProducts, ih, Nat.pow_succ, Nat.mul_two]

theorem subsetProducts_dvd {xs : List Nat} {p : Nat}
    (hp : p ∈ subsetProducts xs) : p ∣ xs.prod := by
  induction xs generalizing p with
  | nil => simp [subsetProducts] at hp; subst p; exact Nat.one_dvd _
  | cons a xs ih =>
    simp only [subsetProducts, List.mem_append, List.mem_map] at hp
    rcases hp with hp | ⟨q, hq, rfl⟩
    · exact Nat.dvd_trans (ih hp) (Nat.dvd_mul_left _ _)
    · exact Nat.mul_dvd_mul_left a (ih hq)

/-- A factor coprime to the entire old product can be added independently. -/
theorem extend_coprime {xs : List Nat} {a : Nat}
    (ha : 1 < a) (hg : Nat.gcd a xs.prod = 1)
    (hx : (subsetProducts xs).Nodup) :
    (subsetProducts (a :: xs)).Nodup := by
  rw [subsetProducts, List.nodup_append]
  refine ⟨hx, ?_, ?_⟩
  · exact hx.map (a * ·)
      (fun _ _ h h' => h (Nat.eq_of_mul_eq_mul_left (by omega) h'))
  · intro p hp q hq heq
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hq
    have had : a ∣ p := heq ▸ Nat.dvd_mul_right a r
    have ht : a ∣ xs.prod := Nat.dvd_trans had (subsetProducts_dvd hp)
    have he : a = 1 := Nat.gcd_eq_one_iff.mp hg a (Nat.dvd_refl a) ht
    omega

def core : List Nat := [5, 25, 6, 16, 27, 32, 36, 48]

theorem core_verified : (subsetProducts core).Nodup := by decide

def witness : List Nat :=
  [7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47] ++ core

theorem witness_products_distinct : (subsetProducts witness).Nodup := by
  unfold witness
  apply extend_coprime (by decide) (by decide)
  apply extend_coprime (by decide) (by decide)
  apply extend_coprime (by decide) (by decide)
  apply extend_coprime (by decide) (by decide)
  apply extend_coprime (by decide) (by decide)
  apply extend_coprime (by decide) (by decide)
  apply extend_coprime (by decide) (by decide)
  apply extend_coprime (by decide) (by decide)
  apply extend_coprime (by decide) (by decide)
  apply extend_coprime (by decide) (by decide)
  apply extend_coprime (by decide) (by decide)
  apply extend_coprime (by decide) (by decide)
  exact core_verified

theorem witness_size : witness.length = 20 := by decide
theorem witness_nodup : witness.Nodup := by decide
theorem witness_range : ∀ a ∈ witness, 1 ≤ a ∧ a ≤ 48 := by decide

/-- Every ordinary subset (given by its characteristic function) is enumerated. -/
theorem selected_product_mem (xs : List Nat) (s : Nat → Bool) :
    (xs.filter s).prod ∈ subsetProducts xs := by
  induction xs with
  | nil => simp [subsetProducts]
  | cons a xs ih =>
    cases hs : s a <;> simp [subsetProducts, hs]
    · exact Or.inl ih
    · exact Or.inr ⟨(xs.filter s).prod, ih, rfl⟩

/-- The certificate implies injectivity for arbitrary subsets, not only a
particular collection of test inputs. -/
theorem subset_products_injective (xs : List Nat)
    (hpos : ∀ a ∈ xs, 0 < a) (hn : (subsetProducts xs).Nodup)
    (s t : Nat → Bool) (heq : (xs.filter s).prod = (xs.filter t).prod) :
    ∀ a ∈ xs, s a = t a := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    obtain ⟨hold, _, hcross⟩ := List.nodup_append.mp hn
    have ha := hpos a (by simp)
    have hp : ∀ b ∈ xs, 0 < b := fun b hb => hpos b (by simp [hb])
    have hs := selected_product_mem xs s
    have ht := selected_product_mem xs t
    have hhead : s a = t a := by
      cases hsa : s a <;> cases hta : t a
      · rfl
      · simp [hsa, hta] at heq
        exact False.elim (hcross _ hs _ (List.mem_map.mpr ⟨_, ht, rfl⟩) heq)
      · simp [hsa, hta] at heq
        exact False.elim (hcross _ ht _ (List.mem_map.mpr ⟨_, hs, rfl⟩) heq.symm)
      · rfl
    have htail : (xs.filter s).prod = (xs.filter t).prod := by
      cases hta : t a
      · simp [hhead, hta] at heq
        exact heq
      · simp [hhead, hta] at heq
        exact Nat.eq_of_mul_eq_mul_left ha heq
    intro b hb
    rcases List.mem_cons.mp hb with rfl | hb
    · exact hhead
    · exact ih hp hold htail b hb

theorem witness_arbitrary_subsets (s t : Nat → Bool)
    (heq : (witness.filter s).prod = (witness.filter t).prod) :
    ∀ a ∈ witness, s a = t a :=
  subset_products_injective witness
    (fun a ha => (witness_range a ha).1) witness_products_distinct s t heq

def subsets : List Nat → List (List Nat)
  | [] => [[]]
  | a :: xs => subsets xs ++ (subsets xs).map (a :: ·)

def subsetSums : List Nat → List Nat
  | [] => [0]
  | a :: xs => subsetSums xs ++ (subsetSums xs).map (a + ·)

/-- Maximum size of an additively dissociated subset of {1,...,k}. -/
def F (k : Nat) : Nat :=
  ((subsets (List.range' 1 k)).filter
    (fun xs => decide (subsetSums xs).Nodup)).foldr
      (fun xs best => max xs.length best) 0

/-- Elementary primality predicate: no proper nontrivial divisor. -/
def isPrime (p : Nat) : Bool :=
  decide (2 ≤ p) && (List.range' 2 (p - 2)).all (fun d => p % d != 0)

/-- π(N^(1/k)), avoiding any real-number rounding. -/
def primeRootCount (N k : Nat) : Nat :=
  ((List.range (N + 1)).filter (fun p => isPrime p && decide (p ^ k ≤ N))).length

/-- Erdős's additional exact formula. Terms above floor(log₂ N) vanish. -/
def predicted (N : Nat) : Nat :=
  ((List.range' 1 (Nat.log2 N)).map
    (fun k => (if F (k - 1) < F k then primeRootCount N k else 0))).sum

theorem additive_extrema : [F 0, F 1, F 2, F 3, F 4, F 5] = [0,1,2,2,3,3] := by
  decide

theorem prime_root_counts :
    [primeRootCount 48 1, primeRootCount 48 2, primeRootCount 48 4] = [15,3,1] := by
  decide

theorem predicted_48 : predicted 48 = 19 := by decide

/-- A list here represents a finite set; Nodup fixes its cardinality. -/
def Admissible (N : Nat) (xs : List Nat) : Prop :=
  xs.Nodup ∧ (∀ a ∈ xs, 1 ≤ a ∧ a ≤ N) ∧ (subsetProducts xs).Nodup

/-- Definition of the extremal number without choosing a particular enumeration. -/
def IsExtremalValue (N m : Nat) : Prop :=
  (∀ xs, Admissible N xs → xs.length ≤ m) ∧
    ∃ xs, Admissible N xs ∧ xs.length = m

def ExactFormulaConjecture : Prop := ∀ N, IsExtremalValue N (predicted N)

theorem witness_admissible : Admissible 48 witness :=
  ⟨witness_nodup, witness_range, witness_products_distinct⟩

/-- Complete disproof of the additional exact formula, at N = 48. -/
theorem exact_formula_false : ¬ ExactFormulaConjecture := by
  intro h
  have hb := (h 48).1 witness witness_admissible
  rw [witness_size, predicted_48] at hb
  omega

theorem finite_counterexample :
    ∃ xs, Admissible 48 xs ∧ xs.length = 20 ∧ predicted 48 = 19 :=
  ⟨witness, witness_admissible, witness_size, predicted_48⟩

end JSP653

#print axioms JSP653.exact_formula_false
#print axioms JSP653.finite_counterexample
#print axioms JSP653.witness_arbitrary_subsets
