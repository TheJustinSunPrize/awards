/- leanprover/lean4:v4.35.0-rc2  mathlib v4.35.0-rc2 -/
/-
JSP-000967 — Observation record: S₃ has exactly six subgroups, and their
orders are distributed as {1 ↦ 1, 2 ↦ 3, 3 ↦ 1, 6 ↦ 1}.

Catalog question (TheJustinSunPrize/awards, problems/catalog-0901-1000.md,
#JSP-000967):
  "How many subgroups does a symmetric group have, and how are their orders
   distributed?"

Scope of this file
------------------
This file records a complete, machine-checked Lean proof of the exact S₃
instance of the catalog question: the symmetric group
`S3 = Equiv.Perm (Fin 3)` has exactly six subgroups, and the number of
subgroups of order `1, 2, 3, 6` is respectively `1, 3, 1, 1`.

It does NOT address the question for general `Sₙ` (n ≥ 4), does not resolve
the catalogued open problem, and makes no award claim.

Method
------
Mathlib (v4.35.0-rc2) has no `Fintype (Subgroup G)` instance, so the counting
theorems are proved by an explicit construction: the six subgroups are given
explicitly by their carriers (decidable predicates on concrete permutations
presented by value tables `![·,·,·]`), the list is certified complete (every
subgroup is in the list, by Lagrange's theorem and an element-wise analysis),
and explicit `Fintype` instances with literal element lists make the
cardinality statements reduce definitionally.  Small concrete facts
(multiplication and inversion of the explicit permutations) are discharged by
`decide`.  No `sorry`, `admit`, `native_decide`, or added unproved
assumptions are used.

Mathematical area: Group theory.
Problem posed: no later than 1999 (bibliographic evidence).

Formalization author: Yaohua-Leo (AI-assisted via ZCode (GLM)).
-/

import Mathlib

/-- The symmetric group on three letters, as `Equiv.Perm (Fin 3)`. -/
abbrev S3 := Equiv.Perm (Fin 3)

section Perms

/-- The identity permutation, presented by its value table. -/
def e : S3 := ⟨![0, 1, 2], ![0, 1, 2], by decide, by decide⟩

/-- The 3-cycle `0 ↦ 1 ↦ 2 ↦ 0`. -/
def r : S3 := ⟨![1, 2, 0], ![2, 0, 1], by decide, by decide⟩

/-- The 3-cycle `0 ↦ 2 ↦ 1 ↦ 0`. -/
def r2 : S3 := ⟨![2, 0, 1], ![1, 2, 0], by decide, by decide⟩

/-- The transposition `0 ↔ 1`. -/
def p1 : S3 := ⟨![1, 0, 2], ![1, 0, 2], by decide, by decide⟩

/-- The transposition `0 ↔ 2`. -/
def p2 : S3 := ⟨![2, 1, 0], ![2, 1, 0], by decide, by decide⟩

/-- The transposition `1 ↔ 2`. -/
def p3 : S3 := ⟨![0, 2, 1], ![0, 2, 1], by decide, by decide⟩

end Perms

/-- Decidable equality on `Equiv.Perm (Fin 3)`: two permutations are equal
exactly when they agree on every point (decidable by finite enumeration). -/
instance decidableEqS3 : DecidableEq S3 :=
  fun a b =>
    decidable_of_iff (∀ i : Fin 3, a i = b i)
      ⟨fun h => Equiv.ext h, fun h i => by rw [h]⟩

/-- `e` is the identity element of `S3`. -/
theorem e_eq_one : e = (1 : S3) := Equiv.ext fun x => by fin_cases x <;> rfl

/-- Every element of `S3` is one of the six explicit permutations. -/
theorem hsix (z : S3) :
    z = e ∨ z = r ∨ z = r2 ∨ z = p1 ∨ z = p2 ∨ z = p3 := by
  fin_cases z
  all_goals decide

section PermFacts

@[simp] theorem r_ne_e : r ≠ e := by decide
@[simp] theorem r2_ne_e : r2 ≠ e := by decide
@[simp] theorem p1_ne_e : p1 ≠ e := by decide
@[simp] theorem p2_ne_e : p2 ≠ e := by decide
@[simp] theorem p3_ne_e : p3 ≠ e := by decide
@[simp] theorem r2_ne_r : r2 ≠ r := by decide
@[simp] theorem p1_ne_r : p1 ≠ r := by decide
@[simp] theorem p2_ne_r : p2 ≠ r := by decide
@[simp] theorem p3_ne_r : p3 ≠ r := by decide
@[simp] theorem p1_ne_r2 : p1 ≠ r2 := by decide
@[simp] theorem p2_ne_r2 : p2 ≠ r2 := by decide
@[simp] theorem p3_ne_r2 : p3 ≠ r2 := by decide
@[simp] theorem p2_ne_p1 : p2 ≠ p1 := by decide
@[simp] theorem p3_ne_p1 : p3 ≠ p1 := by decide
@[simp] theorem p3_ne_p2 : p3 ≠ p2 := by decide

end PermFacts

/-! ## Closure properties of the six carriers -/

theorem bot_mul : ∀ x y : S3, x = e → y = e → x * y = e := by
  rintro _ _ rfl rfl
  decide

theorem bot_inv : ∀ x : S3, x = e → x⁻¹ = e := by
  rintro _ rfl
  decide

theorem p1_mul : ∀ x y : S3, (x = e ∨ x = p1) → (y = e ∨ y = p1) →
    x * y = e ∨ x * y = p1 := by
  rintro _ _ (rfl | rfl) (rfl | rfl) <;> decide

theorem p1_inv : ∀ x : S3, (x = e ∨ x = p1) → x⁻¹ = e ∨ x⁻¹ = p1 := by
  rintro _ (rfl | rfl) <;> decide

theorem p2_mul : ∀ x y : S3, (x = e ∨ x = p2) → (y = e ∨ y = p2) →
    x * y = e ∨ x * y = p2 := by
  rintro _ _ (rfl | rfl) (rfl | rfl) <;> decide

theorem p2_inv : ∀ x : S3, (x = e ∨ x = p2) → x⁻¹ = e ∨ x⁻¹ = p2 := by
  rintro _ (rfl | rfl) <;> decide

theorem p3_mul : ∀ x y : S3, (x = e ∨ x = p3) → (y = e ∨ y = p3) →
    x * y = e ∨ x * y = p3 := by
  rintro _ _ (rfl | rfl) (rfl | rfl) <;> decide

theorem p3_inv : ∀ x : S3, (x = e ∨ x = p3) → x⁻¹ = e ∨ x⁻¹ = p3 := by
  rintro _ (rfl | rfl) <;> decide

theorem a_mul : ∀ x y : S3, (x = e ∨ x = r ∨ x = r2) → (y = e ∨ y = r ∨ y = r2) →
    x * y = e ∨ x * y = r ∨ x * y = r2 := by
  rintro _ _ (rfl | rfl | rfl) (rfl | rfl | rfl) <;> decide

theorem a_inv : ∀ x : S3, (x = e ∨ x = r ∨ x = r2) → x⁻¹ = e ∨ x⁻¹ = r ∨ x⁻¹ = r2 := by
  rintro _ (rfl | rfl | rfl) <;> decide

theorem t_mul : ∀ x y : S3,
    (x = e ∨ x = r ∨ x = r2 ∨ x = p1 ∨ x = p2 ∨ x = p3) →
    (y = e ∨ y = r ∨ y = r2 ∨ y = p1 ∨ y = p2 ∨ y = p3) →
    x * y = e ∨ x * y = r ∨ x * y = r2 ∨ x * y = p1 ∨ x * y = p2 ∨ x * y = p3 := by
  rintro _ _ (rfl | rfl | rfl | rfl | rfl | rfl) (rfl | rfl | rfl | rfl | rfl | rfl) <;> decide

theorem t_inv : ∀ x : S3,
    (x = e ∨ x = r ∨ x = r2 ∨ x = p1 ∨ x = p2 ∨ x = p3) →
    x⁻¹ = e ∨ x⁻¹ = r ∨ x⁻¹ = r2 ∨ x⁻¹ = p1 ∨ x⁻¹ = p2 ∨ x⁻¹ = p3 := by
  rintro _ (rfl | rfl | rfl | rfl | rfl | rfl) <;> decide

/-! ## The six subgroups -/

/-- The trivial subgroup `{e}`. -/
def sBot : Subgroup S3 where
  carrier := {x | x = e}
  one_mem' := e_eq_one.symm
  mul_mem' := fun hx hy => bot_mul _ _ hx hy
  inv_mem' := fun hx => bot_inv _ hx

/-- The order-two subgroup `{e, p1}` generated by the transposition `p1`. -/
def sP1 : Subgroup S3 where
  carrier := {x | x = e ∨ x = p1}
  one_mem' := Or.inl e_eq_one.symm
  mul_mem' := fun hx hy => p1_mul _ _ hx hy
  inv_mem' := fun hx => p1_inv _ hx

/-- The order-two subgroup `{e, p2}` generated by the transposition `p2`. -/
def sP2 : Subgroup S3 where
  carrier := {x | x = e ∨ x = p2}
  one_mem' := Or.inl e_eq_one.symm
  mul_mem' := fun hx hy => p2_mul _ _ hx hy
  inv_mem' := fun hx => p2_inv _ hx

/-- The order-two subgroup `{e, p3}` generated by the transposition `p3`. -/
def sP3 : Subgroup S3 where
  carrier := {x | x = e ∨ x = p3}
  one_mem' := Or.inl e_eq_one.symm
  mul_mem' := fun hx hy => p3_mul _ _ hx hy
  inv_mem' := fun hx => p3_inv _ hx

/-- The alternating subgroup `A₃ = {e, r, r2}` of order three. -/
def sA : Subgroup S3 where
  carrier := {x | x = e ∨ x = r ∨ x = r2}
  one_mem' := Or.inl e_eq_one.symm
  mul_mem' := fun hx hy => a_mul _ _ hx hy
  inv_mem' := fun hx => a_inv _ hx

/-- The full group `S3` itself, as a subgroup. -/
def sT : Subgroup S3 where
  carrier := {x | x = e ∨ x = r ∨ x = r2 ∨ x = p1 ∨ x = p2 ∨ x = p3}
  one_mem' := Or.inl e_eq_one.symm
  mul_mem' := fun hx hy => t_mul _ _ hx hy
  inv_mem' := fun hx => t_inv _ hx

section MemLemmas

theorem mem_sBot {z : S3} : z ∈ sBot ↔ z = e := by simp [sBot]
theorem mem_sP1 {z : S3} : z ∈ sP1 ↔ z = e ∨ z = p1 := by simp [sP1]
theorem mem_sP2 {z : S3} : z ∈ sP2 ↔ z = e ∨ z = p2 := by simp [sP2]
theorem mem_sP3 {z : S3} : z ∈ sP3 ↔ z = e ∨ z = p3 := by simp [sP3]
theorem mem_sA {z : S3} : z ∈ sA ↔ z = e ∨ z = r ∨ z = r2 := by simp [sA]
theorem mem_sT {z : S3} :
    z ∈ sT ↔ z = e ∨ z = r ∨ z = r2 ∨ z = p1 ∨ z = p2 ∨ z = p3 := by simp [sT]

end MemLemmas

/-! ## The six subgroups are pairwise distinct -/

section PairwiseDistinct

theorem sBot_ne_sP1 : sBot ≠ sP1 := by
  intro h
  have h1 : p1 ∈ sP1 := mem_sP1.mpr (Or.inr rfl)
  rw [← h] at h1
  rw [mem_sBot] at h1
  exact p1_ne_e h1

theorem sBot_ne_sP2 : sBot ≠ sP2 := by
  intro h
  have h1 : p2 ∈ sP2 := mem_sP2.mpr (Or.inr rfl)
  rw [← h] at h1
  rw [mem_sBot] at h1
  exact p2_ne_e h1

theorem sBot_ne_sP3 : sBot ≠ sP3 := by
  intro h
  have h1 : p3 ∈ sP3 := mem_sP3.mpr (Or.inr rfl)
  rw [← h] at h1
  rw [mem_sBot] at h1
  exact p3_ne_e h1

theorem sBot_ne_sA : sBot ≠ sA := by
  intro h
  have h1 : r ∈ sA := mem_sA.mpr (Or.inr (Or.inl rfl))
  rw [← h] at h1
  rw [mem_sBot] at h1
  exact r_ne_e h1

theorem sBot_ne_sT : sBot ≠ sT := by
  intro h
  have h1 : p1 ∈ sT := mem_sT.mpr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  rw [← h] at h1
  rw [mem_sBot] at h1
  exact p1_ne_e h1

theorem sP1_ne_sP2 : sP1 ≠ sP2 := by
  intro h
  have h1 : p1 ∈ sP1 := mem_sP1.mpr (Or.inr rfl)
  rw [h] at h1
  rw [mem_sP2] at h1
  rcases h1 with h2 | h2
  · exact p1_ne_e h2
  · exact p2_ne_p1 h2.symm

theorem sP1_ne_sP3 : sP1 ≠ sP3 := by
  intro h
  have h1 : p1 ∈ sP1 := mem_sP1.mpr (Or.inr rfl)
  rw [h] at h1
  rw [mem_sP3] at h1
  rcases h1 with h2 | h2
  · exact p1_ne_e h2
  · exact p3_ne_p1 h2.symm

theorem sP1_ne_sA : sP1 ≠ sA := by
  intro h
  have h1 : p1 ∈ sP1 := mem_sP1.mpr (Or.inr rfl)
  rw [h] at h1
  rw [mem_sA] at h1
  rcases h1 with h2 | h2 | h2
  · exact p1_ne_e h2
  · exact p1_ne_r h2
  · exact p1_ne_r2 h2

theorem sP1_ne_sT : sP1 ≠ sT := by
  intro h
  have h1 : p2 ∈ sT := mem_sT.mpr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  rw [← h] at h1
  rw [mem_sP1] at h1
  rcases h1 with h2 | h2
  · exact p2_ne_e h2
  · exact p2_ne_p1 h2

theorem sP2_ne_sP3 : sP2 ≠ sP3 := by
  intro h
  have h1 : p2 ∈ sP2 := mem_sP2.mpr (Or.inr rfl)
  rw [h] at h1
  rw [mem_sP3] at h1
  rcases h1 with h2 | h2
  · exact p2_ne_e h2
  · exact p3_ne_p2 h2.symm

theorem sP2_ne_sA : sP2 ≠ sA := by
  intro h
  have h1 : p2 ∈ sP2 := mem_sP2.mpr (Or.inr rfl)
  rw [h] at h1
  rw [mem_sA] at h1
  rcases h1 with h2 | h2 | h2
  · exact p2_ne_e h2
  · exact p2_ne_r h2
  · exact p2_ne_r2 h2

theorem sP2_ne_sT : sP2 ≠ sT := by
  intro h
  have h1 : p1 ∈ sT := mem_sT.mpr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  rw [← h] at h1
  rw [mem_sP2] at h1
  rcases h1 with h2 | h2
  · exact p1_ne_e h2
  · exact p2_ne_p1 h2.symm

theorem sP3_ne_sA : sP3 ≠ sA := by
  intro h
  have h1 : p3 ∈ sP3 := mem_sP3.mpr (Or.inr rfl)
  rw [h] at h1
  rw [mem_sA] at h1
  rcases h1 with h2 | h2 | h2
  · exact p3_ne_e h2
  · exact p3_ne_r h2
  · exact p3_ne_r2 h2

theorem sP3_ne_sT : sP3 ≠ sT := by
  intro h
  have h1 : p1 ∈ sT := mem_sT.mpr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  rw [← h] at h1
  rw [mem_sP3] at h1
  rcases h1 with h2 | h2
  · exact p1_ne_e h2
  · exact p3_ne_p1 h2.symm

theorem sA_ne_sT : sA ≠ sT := by
  intro h
  have h1 : p1 ∈ sT := mem_sT.mpr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  rw [← h] at h1
  rw [mem_sA] at h1
  rcases h1 with h2 | h2 | h2
  · exact p1_ne_e h2
  · exact p1_ne_r h2
  · exact p1_ne_r2 h2

end PairwiseDistinct

/-- The complete list of the six subgroups of `S3`, as a finset. -/
def elems6 : Finset (Subgroup S3) :=
  ⟨[sBot, sP1, sP2, sP3, sA, sT], by
    refine List.nodup_cons.mpr ⟨?_, List.nodup_cons.mpr ⟨?_, List.nodup_cons.mpr ⟨?_,
      List.nodup_cons.mpr ⟨?_, List.nodup_cons.mpr ⟨?_, List.nodup_singleton _⟩⟩⟩⟩⟩
    · intro hmem
      simp only [List.mem_cons] at hmem
      rcases hmem with h | h | h | h | h | h
      · exact sBot_ne_sP1 h
      · exact sBot_ne_sP2 h
      · exact sBot_ne_sP3 h
      · exact sBot_ne_sA h
      · exact sBot_ne_sT h
      · exact List.not_mem_nil h
    · intro hmem
      simp only [List.mem_cons] at hmem
      rcases hmem with h | h | h | h | h
      · exact sP1_ne_sP2 h
      · exact sP1_ne_sP3 h
      · exact sP1_ne_sA h
      · exact sP1_ne_sT h
      · exact List.not_mem_nil h
    · intro hmem
      simp only [List.mem_cons] at hmem
      rcases hmem with h | h | h | h
      · exact sP2_ne_sP3 h
      · exact sP2_ne_sA h
      · exact sP2_ne_sT h
      · exact List.not_mem_nil h
    · intro hmem
      simp only [List.mem_cons] at hmem
      rcases hmem with h | h | h
      · exact sP3_ne_sA h
      · exact sP3_ne_sT h
      · exact List.not_mem_nil h
    · intro hmem
      simp only [List.mem_cons] at hmem
      rcases hmem with h | h
      · exact sA_ne_sT h
      · exact List.not_mem_nil h⟩

theorem mem_elems6_bot : sBot ∈ elems6 := by
  simp only [elems6]
  exact List.mem_cons.mpr (Or.inl rfl)
theorem mem_elems6_sP1 : sP1 ∈ elems6 := by
  simp only [elems6]
  exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))
theorem mem_elems6_sP2 : sP2 ∈ elems6 := by
  simp only [elems6]
  exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))
theorem mem_elems6_sP3 : sP3 ∈ elems6 := by
  simp only [elems6]
  exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr
    (List.mem_cons.mpr (Or.inl rfl)))))))
theorem mem_elems6_sA : sA ∈ elems6 := by
  simp only [elems6]
  exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr
    (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))))))
theorem mem_elems6_sT : sT ∈ elems6 := by
  simp only [elems6]
  exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr
    (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr
      (Or.inl rfl)))))))))))

/-! ## Explicit `Fintype` instances for the subgroup carriers
The element lists are literal, so cardinalities reduce definitionally. -/

instance : Fintype ↥sBot := by
  refine { elems := ?_, complete := ?_ }
  . refine ⟨(↑([⟨e, mem_sBot.mpr rfl⟩] : List ↥sBot) : Multiset ↥sBot), ?_⟩
    rw [Multiset.coe_nodup]
    exact List.nodup_singleton _
  . rintro ⟨x, hx⟩
    rw [mem_sBot] at hx
    subst hx
    simp [Finset.mem_mk]
instance : Fintype ↥sP1 := by
  refine { elems := ?_, complete := ?_ }
  . refine ⟨(↑([⟨e, mem_sP1.mpr (Or.inl rfl)⟩, ⟨p1, mem_sP1.mpr (Or.inr rfl)⟩] :
        List ↥sP1) : Multiset ↥sP1), ?_⟩
    rw [Multiset.coe_nodup]
    refine List.nodup_cons.mpr ⟨?_, List.nodup_singleton _⟩
    intro hmem
    simp only [List.mem_cons, Subtype.mk.injEq] at hmem
    rcases hmem with h | h
    . exact p1_ne_e h.symm
    . exact List.not_mem_nil h
  . rintro ⟨x, hx⟩
    rw [mem_sP1] at hx
    rcases hx with rfl | rfl <;> simp [Finset.mem_mk]
instance : Fintype ↥sP2 := by
  refine { elems := ?_, complete := ?_ }
  . refine ⟨(↑([⟨e, mem_sP2.mpr (Or.inl rfl)⟩, ⟨p2, mem_sP2.mpr (Or.inr rfl)⟩] :
        List ↥sP2) : Multiset ↥sP2), ?_⟩
    rw [Multiset.coe_nodup]
    refine List.nodup_cons.mpr ⟨?_, List.nodup_singleton _⟩
    intro hmem
    simp only [List.mem_cons, Subtype.mk.injEq] at hmem
    rcases hmem with h | h
    . exact p2_ne_e h.symm
    . exact List.not_mem_nil h
  . rintro ⟨x, hx⟩
    rw [mem_sP2] at hx
    rcases hx with rfl | rfl <;> simp [Finset.mem_mk]
instance : Fintype ↥sP3 := by
  refine { elems := ?_, complete := ?_ }
  . refine ⟨(↑([⟨e, mem_sP3.mpr (Or.inl rfl)⟩, ⟨p3, mem_sP3.mpr (Or.inr rfl)⟩] :
        List ↥sP3) : Multiset ↥sP3), ?_⟩
    rw [Multiset.coe_nodup]
    refine List.nodup_cons.mpr ⟨?_, List.nodup_singleton _⟩
    intro hmem
    simp only [List.mem_cons, Subtype.mk.injEq] at hmem
    rcases hmem with h | h
    . exact p3_ne_e h.symm
    . exact List.not_mem_nil h
  . rintro ⟨x, hx⟩
    rw [mem_sP3] at hx
    rcases hx with rfl | rfl <;> simp [Finset.mem_mk]

instance : Fintype ↥sA := by
  refine { elems := ?_, complete := ?_ }
  . refine ⟨(↑([⟨e, mem_sA.mpr (Or.inl rfl)⟩, ⟨r, mem_sA.mpr (Or.inr (Or.inl rfl))⟩,
        ⟨r2, mem_sA.mpr (Or.inr (Or.inr rfl))⟩] : List ↥sA) : Multiset ↥sA), ?_⟩
    rw [Multiset.coe_nodup]
    refine List.nodup_cons.mpr ⟨?_, List.nodup_cons.mpr ⟨?_, List.nodup_singleton _⟩⟩
    . intro hmem
      simp only [List.mem_cons, Subtype.mk.injEq] at hmem
      rcases hmem with h | h | h
      . exact r_ne_e h.symm
      . exact r2_ne_e h.symm
      . exact List.not_mem_nil h
    . intro hmem
      simp only [List.mem_cons, Subtype.mk.injEq] at hmem
      rcases hmem with h | h
      . exact r2_ne_r h.symm
      . exact List.not_mem_nil h
  . rintro ⟨x, hx⟩
    rw [mem_sA] at hx
    rcases hx with rfl | rfl | rfl <;> simp [Finset.mem_mk]

instance : Fintype ↥sT := by
  refine { elems := ?_, complete := ?_ }
  . refine ⟨(↑([⟨e, mem_sT.mpr (Or.inl rfl)⟩, ⟨r, mem_sT.mpr (Or.inr (Or.inl rfl))⟩,
        ⟨r2, mem_sT.mpr (Or.inr (Or.inr (Or.inl rfl)))⟩,
        ⟨p1, mem_sT.mpr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))⟩,
        ⟨p2, mem_sT.mpr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))⟩,
        ⟨p3, mem_sT.mpr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))⟩] :
        List ↥sT) : Multiset ↥sT), ?_⟩
    rw [Multiset.coe_nodup]
    refine List.nodup_cons.mpr ⟨?_, List.nodup_cons.mpr ⟨?_, List.nodup_cons.mpr ⟨?_,
      List.nodup_cons.mpr ⟨?_, List.nodup_cons.mpr ⟨?_, List.nodup_singleton _⟩⟩⟩⟩⟩
    . intro hmem
      simp only [List.mem_cons, Subtype.mk.injEq] at hmem
      rcases hmem with h | h | h | h | h | h
      . exact r_ne_e h.symm
      . exact r2_ne_e h.symm
      . exact p1_ne_e h.symm
      . exact p2_ne_e h.symm
      . exact p3_ne_e h.symm
      . exact List.not_mem_nil h
    . intro hmem
      simp only [List.mem_cons, Subtype.mk.injEq] at hmem
      rcases hmem with h | h | h | h | h
      . exact r2_ne_r h.symm
      . exact p1_ne_r h.symm
      . exact p2_ne_r h.symm
      . exact p3_ne_r h.symm
      . exact List.not_mem_nil h
    . intro hmem
      simp only [List.mem_cons, Subtype.mk.injEq] at hmem
      rcases hmem with h | h | h | h
      . exact p1_ne_r2 h.symm
      . exact p2_ne_r2 h.symm
      . exact p3_ne_r2 h.symm
      . exact List.not_mem_nil h
    . intro hmem
      simp only [List.mem_cons, Subtype.mk.injEq] at hmem
      rcases hmem with h | h | h
      . exact p2_ne_p1 h.symm
      . exact p3_ne_p1 h.symm
      . exact List.not_mem_nil h
    . intro hmem
      simp only [List.mem_cons, Subtype.mk.injEq] at hmem
      rcases hmem with h | h
      . exact p3_ne_p2 h.symm
      . exact List.not_mem_nil h
  . rintro ⟨x, hx⟩
    rw [mem_sT] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [Finset.mem_mk]

/-- The cardinalities of the explicit subgroups. -/
theorem card_sBot : Nat.card ↥sBot = 1 := by rw [Nat.card_eq_fintype_card]; rfl
theorem card_sP1 : Nat.card ↥sP1 = 2 := by rw [Nat.card_eq_fintype_card]; rfl
theorem card_sP2 : Nat.card ↥sP2 = 2 := by rw [Nat.card_eq_fintype_card]; rfl
theorem card_sP3 : Nat.card ↥sP3 = 2 := by rw [Nat.card_eq_fintype_card]; rfl
theorem card_sA : Nat.card ↥sA = 3 := by rw [Nat.card_eq_fintype_card]; rfl
theorem card_sT : Nat.card ↥sT = 6 := by rw [Nat.card_eq_fintype_card]; rfl

/-! ## Completeness: every subgroup of `S3` is one of the six -/

section Completeness

/-- `S3` has exactly six elements. -/
theorem card_S3 : Nat.card S3 = 6 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
  norm_num

/-- Lagrange for `S3`: the order of a subgroup divides six. -/
theorem card_dvd_six (H : Subgroup S3) : Nat.card ↥H ∣ Nat.card S3 :=
  ⟨Subgroup.index H, (Subgroup.card_mul_index H).symm⟩

/-- Two distinct elements of a subgroup force its order to be at least two. -/
theorem card_ge_of_mem2 {H : Subgroup S3} {a b : S3} (ha : a ∈ H) (hb : b ∈ H)
    (hab : a ≠ b) : 2 ≤ Nat.card ↥H := by
  have hfin : Finite ↥H :=
    Finite.of_injective (Subtype.val : ↥H → S3) Subtype.val_injective
  let : Fintype ↥H := Fintype.ofFinite ↥H
  have hcard : Fintype.card (Fin 2) ≤ Fintype.card ↥H :=
    Fintype.card_le_of_injective (fun i : Fin 2 =>
      if i = 0 then (⟨a, ha⟩ : ↥H) else ⟨b, hb⟩) (by
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all)
  rw [Nat.card_eq_fintype_card]
  simpa using hcard

/-- Three distinct elements of a subgroup force its order to be at least
three. -/
theorem card_ge_of_mem3 {H : Subgroup S3} {a b c : S3} (ha : a ∈ H) (hb : b ∈ H)
    (hc : c ∈ H) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) : 3 ≤ Nat.card ↥H := by
  have hfin : Finite ↥H :=
    Finite.of_injective (Subtype.val : ↥H → S3) Subtype.val_injective
  let : Fintype ↥H := Fintype.ofFinite ↥H
  have hcard : Fintype.card (Fin 3) ≤ Fintype.card ↥H :=
    Fintype.card_le_of_injective (fun i : Fin 3 =>
      if i = 0 then (⟨a, ha⟩ : ↥H) else if i = 1 then ⟨b, hb⟩ else ⟨c, hc⟩) (by
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all)
  rw [Nat.card_eq_fintype_card]
  simpa using hcard

/-- Four distinct elements of a subgroup force its order to be at least
four. -/
theorem card_ge_of_mem4 {H : Subgroup S3} {a b c d : S3} (ha : a ∈ H) (hb : b ∈ H)
    (hc : c ∈ H) (hd : d ∈ H) (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) : 4 ≤ Nat.card ↥H := by
  have hfin : Finite ↥H :=
    Finite.of_injective (Subtype.val : ↥H → S3) Subtype.val_injective
  let : Fintype ↥H := Fintype.ofFinite ↥H
  have hcard : Fintype.card (Fin 4) ≤ Fintype.card ↥H :=
    Fintype.card_le_of_injective (fun i : Fin 4 =>
      if i = 0 then (⟨a, ha⟩ : ↥H) else if i = 1 then ⟨b, hb⟩
      else if i = 2 then ⟨c, hc⟩ else ⟨d, hd⟩) (by
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all)
  rw [Nat.card_eq_fintype_card]
  simpa using hcard

/-- Helper: `1 ≠ x` from `x ≠ 1`. -/
theorem one_ne_of_ne {x : S3} (hx : x ≠ 1) : (1 : S3) ≠ x := fun h => hx h.symm

/-- Left cancellation in a group, avoiding the `MonoidWithZero`-flavoured
`mul_left_cancel₀`. -/
theorem mul_left_cancel' {x y z : S3} (_hx : x ≠ 1) (h : x * y = x * z) : y = z := by
  have h2 : x⁻¹ * (x * y) = x⁻¹ * (x * z) := congrArg (fun w => x⁻¹ * w) h
  rw [inv_mul_cancel_left, inv_mul_cancel_left] at h2
  exact h2

/-- Helper: cancel `x` in `x * x = x` to derive `x = 1`. -/
theorem eq_one_of_mul_self {x : S3} (hx1 : x ≠ 1) (h : x * x = x) : False :=
  hx1 (mul_left_cancel' hx1 (by rw [mul_one, h]))

/-- **Completeness of the list of subgroups of S₃.**  Every subgroup of
`S3 = Equiv.Perm (Fin 3)` is one of `sBot`, `sP1`, `sP2`, `sP3`, `sA`, `sT`. -/
theorem complete_cases (H : Subgroup S3) :
    H = sBot ∨ H = sP1 ∨ H = sP2 ∨ H = sP3 ∨ H = sA ∨ H = sT := by
  have hdvd : Nat.card ↥H ∣ Nat.card S3 := card_dvd_six H
  have hpos : 0 < Nat.card ↥H := by
    have : Nonempty ↥H := ⟨⟨(1 : S3), Subgroup.one_mem H⟩⟩
    exact Nat.card_pos
  have hle : Nat.card ↥H ≤ 6 := by
    have h6 : 0 < Nat.card S3 := by rw [card_S3]; norm_num
    have hle' := Nat.le_of_dvd h6 hdvd
    rwa [card_S3] at hle'
  have hN : Nat.card ↥H = 1 ∨ Nat.card ↥H = 2 ∨ Nat.card ↥H = 3 ∨ Nat.card ↥H = 6 := by
    rcases Nat.lt_or_ge (Nat.card ↥H) 4 with hlt | hge
    . rcases Nat.lt_or_ge (Nat.card ↥H) 3 with h3 | h3
      . rcases Nat.lt_or_ge (Nat.card ↥H) 2 with h2 | h2
        . omega
        . omega
      . omega
    . rcases Nat.lt_or_ge (Nat.card ↥H) 6 with h4 | h6
      . rcases Nat.lt_or_ge (Nat.card ↥H) 5 with h5 | h5
        . have h45 : Nat.card ↥H = 4 ∨ Nat.card ↥H = 5 := by omega
          rcases h45 with h | h
          . rw [h, card_S3] at hdvd; norm_num at hdvd
          . rw [h, card_S3] at hdvd; norm_num at hdvd
        . have h56 : Nat.card ↥H = 5 ∨ Nat.card ↥H = 6 := by omega
          rcases h56 with h | h
          . rw [h, card_S3] at hdvd; norm_num at hdvd
          . exact Or.inr (Or.inr (Or.inr h))
      . omega
  rcases hN with hN | hN | hN | hN
  . -- order 1: H = bottom = sBot
    have hbot : H = ⊥ := Subgroup.eq_bot_of_card_eq H hN
    have hHeq : H = sBot := by
      rw [hbot]
      apply SetLike.ext
      intro z
      simp only [Subgroup.mem_bot, mem_sBot, e_eq_one]
    exact Or.inl hHeq
  . -- order 2: H = sP1 or sP2 or sP3
    have hnebot : H ≠ ⊥ := by
      intro hbot
      rw [hbot, Subgroup.card_bot] at hN
      norm_num at hN
    obtain ⟨x, hx, hx1⟩ : ∃ x : S3, x ∈ H ∧ x ≠ 1 := by
      by_contra hall
      refine hnebot ?_
      apply SetLike.ext
      intro z
      refine ⟨fun hz => ?_, fun hz => ?_⟩
      . by_contra hz1
        exact hall ⟨z, hz, hz1⟩
      . rw [hz]; exact Subgroup.one_mem H
    have hx2mem : x * x ∈ H := Subgroup.mul_mem H hx hx
    have hx2 : x * x = 1 := by
      by_contra hx2ne
      have h3 := card_ge_of_mem3 (a := (1 : S3)) (b := x) (c := x * x)
        (Subgroup.one_mem H) hx hx2mem
        (one_ne_of_ne hx1)
        (fun hc => hx2ne hc.symm)
        (fun hc => eq_one_of_mul_self hx1 hc.symm)
      omega
    rcases hsix x with rfl | rfl | rfl | rfl | rfl | rfl
    . exact absurd e_eq_one hx1
    . exact ((by decide : ¬ ((r : S3) * r = 1)) hx2).elim
    . exact ((by decide : ¬ ((r2 : S3) * r2 = 1)) hx2).elim
    . -- x = p1: H = sP1
      have hHP : H = sP1 := by
        apply SetLike.ext
        intro z
        constructor
        . intro hz
          by_contra hz9
          have hz9p : z ≠ p1 := fun hc => hz9 (Or.inr hc)
          have hz9e : z ≠ (1 : S3) := fun hc => hz9 (Or.inl (hc.trans e_eq_one.symm))
          have h3 := card_ge_of_mem3 (a := (1 : S3)) (b := p1) (c := z)
            (Subgroup.one_mem H) hx hz
            (one_ne_of_ne hx1)
            (one_ne_of_ne hz9e)
            (fun hc => hz9p hc.symm)
          omega
        . rintro (rfl | rfl)
          . rw [e_eq_one]; exact Subgroup.one_mem H
          . exact hx
      exact Or.inr (Or.inl hHP)
    . -- x = p2: H = sP2
      have hHP : H = sP2 := by
        apply SetLike.ext
        intro z
        constructor
        . intro hz
          by_contra hz9
          have hz9p : z ≠ p2 := fun hc => hz9 (Or.inr hc)
          have hz9e : z ≠ (1 : S3) := fun hc => hz9 (Or.inl (hc.trans e_eq_one.symm))
          have h3 := card_ge_of_mem3 (a := (1 : S3)) (b := p2) (c := z)
            (Subgroup.one_mem H) hx hz
            (one_ne_of_ne hx1)
            (one_ne_of_ne hz9e)
            (fun hc => hz9p hc.symm)
          omega
        . rintro (rfl | rfl)
          . rw [e_eq_one]; exact Subgroup.one_mem H
          . exact hx
      exact Or.inr (Or.inr (Or.inl hHP))
    . -- x = p3: H = sP3
      have hHP : H = sP3 := by
        apply SetLike.ext
        intro z
        constructor
        . intro hz
          by_contra hz9
          have hz9p : z ≠ p3 := fun hc => hz9 (Or.inr hc)
          have hz9e : z ≠ (1 : S3) := fun hc => hz9 (Or.inl (hc.trans e_eq_one.symm))
          have h3 := card_ge_of_mem3 (a := (1 : S3)) (b := p3) (c := z)
            (Subgroup.one_mem H) hx hz
            (one_ne_of_ne hx1)
            (one_ne_of_ne hz9e)
            (fun hc => hz9p hc.symm)
          omega
        . rintro (rfl | rfl)
          . rw [e_eq_one]; exact Subgroup.one_mem H
          . exact hx
      exact Or.inr (Or.inr (Or.inr (Or.inl hHP)))
  . -- order 3: H = sA
    have hnebot : H ≠ ⊥ := by
      intro hbot
      rw [hbot, Subgroup.card_bot] at hN
      norm_num at hN
    obtain ⟨x, hx, hx1⟩ : ∃ x : S3, x ∈ H ∧ x ≠ 1 := by
      by_contra hall
      refine hnebot ?_
      apply SetLike.ext
      intro z
      refine ⟨fun hz => ?_, fun hz => ?_⟩
      . by_contra hz1
        exact hall ⟨z, hz, hz1⟩
      . rw [hz]; exact Subgroup.one_mem H
    have hx2mem : x * x ∈ H := Subgroup.mul_mem H hx hx
    have hx2ne : x * x ≠ 1 := by
      intro hx2
      have hd2 : orderOf x ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr (by rw [pow_two]; exact hx2)
      have h1 : orderOf x ≠ 1 := fun h1 => hx1 (orderOf_eq_one_iff.mp h1)
      have hzp := Subgroup.card_dvd_of_le (Subgroup.zpowers_le.mpr hx)
      have hzc : Nat.card ↥(Subgroup.zpowers x) = orderOf x :=
        Nat.card_eq_fintype_card.trans Fintype.card_zpowers
      rw [hzc, hN] at hzp
      have hgcd : orderOf x ∣ Nat.gcd 2 3 := Nat.dvd_gcd hd2 hzp
      rw [show Nat.gcd 2 3 = 1 from by norm_num, Nat.dvd_one] at hgcd
      exact h1 hgcd
    have hx2x : x * x ≠ x := fun hc => eq_one_of_mul_self hx1 hc
    have hx3mem : x * x * x ∈ H := Subgroup.mul_mem H hx2mem hx
    have hx3 : x * x * x = 1 := by
      by_contra hx3ne
      have h4 := card_ge_of_mem4 (a := (1 : S3)) (b := x) (c := x * x) (d := x * x * x)
        (Subgroup.one_mem H) hx hx2mem hx3mem
        (one_ne_of_ne hx1)
        (one_ne_of_ne hx2ne)
        (fun hc => hx3ne hc.symm)
        (fun hc => hx2x hc.symm)
        (fun hc => hx2ne (mul_left_cancel' hx1 (by rw [mul_one]; exact hc)).symm)
        (fun hc => hx1 (mul_left_cancel' hx2ne (by rw [mul_one]; exact hc)).symm)
      omega
    rcases hsix x with rfl | rfl | rfl | rfl | rfl | rfl
    . exact absurd e_eq_one hx1
    . -- x = r: H = sA
      have hHA : H = sA := by
        have hr2mem : r2 ∈ H := by
          have h := hx2mem
          rwa [show (r : S3) * r = r2 from by decide] at h
        have h1r2 : (1 : S3) ≠ r2 := fun hc => r2_ne_e (by rw [← hc, e_eq_one])
        apply SetLike.ext
        intro z
        constructor
        . intro hz
          by_contra hz9
          have hz9e : z ≠ (1 : S3) := by
            intro hc
            refine hz9 (Or.inl ?_)
            rw [hc, e_eq_one]
          have hz9r : z ≠ r := fun hc => hz9 (Or.inr (Or.inl hc))
          have hz9r2 : z ≠ r2 := fun hc => hz9 (Or.inr (Or.inr hc))
          have h4 := card_ge_of_mem4 (a := (1 : S3)) (b := r) (c := r2) (d := z)
            (Subgroup.one_mem H) hx hr2mem hz
            (one_ne_of_ne hx1)
            h1r2
            (one_ne_of_ne hz9e)
            (fun hc => r2_ne_r hc.symm)
            (fun hc => hz9r hc.symm)
            (fun hc => hz9r2 hc.symm)
          omega
        . rintro (rfl | rfl | rfl)
          . rw [e_eq_one]; exact Subgroup.one_mem H
          . exact hx
          . exact hr2mem
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hHA))))
    . -- x = r2: H = sA
      have hHA : H = sA := by
        have hrmem : r ∈ H := by
          have h := hx2mem
          rwa [show (r2 : S3) * r2 = r from by decide] at h
        have h1r : (1 : S3) ≠ r := fun hc => r_ne_e (by rw [← hc, e_eq_one])
        apply SetLike.ext
        intro z
        constructor
        . intro hz
          by_contra hz9
          have hz9e : z ≠ (1 : S3) := by
            intro hc
            refine hz9 (Or.inl ?_)
            rw [hc, e_eq_one]
          have hz9r : z ≠ r := fun hc => hz9 (Or.inr (Or.inl hc))
          have hz9r2 : z ≠ r2 := fun hc => hz9 (Or.inr (Or.inr hc))
          have h4 := card_ge_of_mem4 (a := (1 : S3)) (b := r) (c := r2) (d := z)
            (Subgroup.one_mem H) hrmem hx hz
            h1r
            (one_ne_of_ne hx1)
            (one_ne_of_ne hz9e)
            (fun hc => r2_ne_r hc.symm)
            (fun hc => hz9r hc.symm)
            (fun hc => hz9r2 hc.symm)
          omega
        . rintro (rfl | rfl | rfl)
          . rw [e_eq_one]; exact Subgroup.one_mem H
          . exact hrmem
          . exact hx
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hHA))))
    . exact absurd (by decide : (p1 : S3) * p1 = 1) hx2ne
    . exact absurd (by decide : (p2 : S3) * p2 = 1) hx2ne
    . exact absurd (by decide : (p3 : S3) * p3 = 1) hx2ne
  . -- order 6: H = top = sT
    have htop : H = ⊤ := Subgroup.eq_top_of_card_eq H (by rw [hN, card_S3])
    have hHeq : H = sT := by
      rw [htop]
      apply SetLike.ext
      intro z
      exact ⟨fun _ => mem_sT.mpr (hsix z), fun _ => Subgroup.mem_top z⟩
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hHeq))))

theorem complete (H : Subgroup S3) : H ∈ elems6 := by
  rcases complete_cases H with h | h | h | h | h | h
  . rw [h]; exact mem_elems6_bot
  . rw [h]; exact mem_elems6_sP1
  . rw [h]; exact mem_elems6_sP2
  . rw [h]; exact mem_elems6_sP3
  . rw [h]; exact mem_elems6_sA
  . rw [h]; exact mem_elems6_sT

end Completeness

/-! ## The main theorems -/

instance instFintypeSubgroupS3 : Fintype (Subgroup S3) :=
  ⟨elems6, complete⟩

/-- The group `S3 = Equiv.Perm (Fin 3)` has exactly six subgroups. -/
theorem jsp000967_count : Fintype.card (Subgroup S3) = 6 := rfl

instance instFintypeOrder1 : Fintype {H : Subgroup S3 // Nat.card ↥H = 1} := by
  refine { elems := ?_, complete := ?_ }
  . refine ⟨(↑([⟨sBot, card_sBot⟩] : List {H : Subgroup S3 // Nat.card ↥H = 1}) :
      Multiset {H : Subgroup S3 // Nat.card ↥H = 1}), ?_⟩
    rw [Multiset.coe_nodup]
    exact List.nodup_singleton _
  . rintro ⟨H, hH⟩
    rcases complete_cases H with rfl | rfl | rfl | rfl | rfl | rfl
    . simp [Finset.mem_mk]
    . rw [card_sP1] at hH; norm_num at hH
    . rw [card_sP2] at hH; norm_num at hH
    . rw [card_sP3] at hH; norm_num at hH
    . rw [card_sA] at hH; norm_num at hH
    . rw [card_sT] at hH; norm_num at hH

instance instFintypeOrder2 : Fintype {H : Subgroup S3 // Nat.card ↥H = 2} := by
  refine { elems := ?_, complete := ?_ }
  . refine ⟨(↑([⟨sP1, card_sP1⟩, ⟨sP2, card_sP2⟩, ⟨sP3, card_sP3⟩] :
      List {H : Subgroup S3 // Nat.card ↥H = 2}) :
      Multiset {H : Subgroup S3 // Nat.card ↥H = 2}), ?_⟩
    rw [Multiset.coe_nodup]
    refine List.nodup_cons.mpr ⟨?_, List.nodup_cons.mpr ⟨?_, List.nodup_singleton _⟩⟩
    . intro hmem
      simp only [List.mem_cons] at hmem
      rcases hmem with h | h | h
      . exact sP1_ne_sP2 (congrArg Subtype.val h)
      . exact sP1_ne_sP3 (congrArg Subtype.val h)
      . exact List.not_mem_nil h
    . intro hmem
      simp only [List.mem_cons] at hmem
      rcases hmem with h | h
      . exact sP2_ne_sP3 (congrArg Subtype.val h)
      . exact List.not_mem_nil h
  . rintro ⟨H, hH⟩
    rcases complete_cases H with rfl | rfl | rfl | rfl | rfl | rfl
    . rw [card_sBot] at hH; norm_num at hH
    . simp [Finset.mem_mk]
    . simp [Finset.mem_mk]
    . simp [Finset.mem_mk]
    . rw [card_sA] at hH; norm_num at hH
    . rw [card_sT] at hH; norm_num at hH

instance instFintypeOrder3 : Fintype {H : Subgroup S3 // Nat.card ↥H = 3} := by
  refine { elems := ?_, complete := ?_ }
  . refine ⟨(↑([⟨sA, card_sA⟩] : List {H : Subgroup S3 // Nat.card ↥H = 3}) :
      Multiset {H : Subgroup S3 // Nat.card ↥H = 3}), ?_⟩
    rw [Multiset.coe_nodup]
    exact List.nodup_singleton _
  . rintro ⟨H, hH⟩
    rcases complete_cases H with rfl | rfl | rfl | rfl | rfl | rfl
    . rw [card_sBot] at hH; norm_num at hH
    . rw [card_sP1] at hH; norm_num at hH
    . rw [card_sP2] at hH; norm_num at hH
    . rw [card_sP3] at hH; norm_num at hH
    . simp [Finset.mem_mk]
    . rw [card_sT] at hH; norm_num at hH

instance instFintypeOrder6 : Fintype {H : Subgroup S3 // Nat.card ↥H = 6} := by
  refine { elems := ?_, complete := ?_ }
  . refine ⟨(↑([⟨sT, card_sT⟩] : List {H : Subgroup S3 // Nat.card ↥H = 6}) :
      Multiset {H : Subgroup S3 // Nat.card ↥H = 6}), ?_⟩
    rw [Multiset.coe_nodup]
    exact List.nodup_singleton _
  . rintro ⟨H, hH⟩
    rcases complete_cases H with rfl | rfl | rfl | rfl | rfl | rfl
    . rw [card_sBot] at hH; norm_num at hH
    . rw [card_sP1] at hH; norm_num at hH
    . rw [card_sP2] at hH; norm_num at hH
    . rw [card_sP3] at hH; norm_num at hH
    . rw [card_sA] at hH; norm_num at hH
    . simp [Finset.mem_mk]

/-- **JSP-000967 (S₃ instance):** the number of subgroups of `S3 =
Equiv.Perm (Fin 3)` of order `1, 2, 3, 6` is respectively `1, 3, 1, 1`.
Together with `jsp000967_count` this gives the full order distribution:
exactly one subgroup of order 1 (the trivial group), exactly three of
order 2, exactly one of order 3 (the alternating group `A₃`), and exactly
one of order 6 (`S3` itself). -/
theorem jsp000967_orders :
    Fintype.card {H : Subgroup S3 // Nat.card ↥H = 1} = 1 ∧
    Fintype.card {H : Subgroup S3 // Nat.card ↥H = 2} = 3 ∧
    Fintype.card {H : Subgroup S3 // Nat.card ↥H = 3} = 1 ∧
    Fintype.card {H : Subgroup S3 // Nat.card ↥H = 6} = 1 :=
  ⟨rfl, rfl, rfl, rfl⟩

#print axioms jsp000967_count
#print axioms jsp000967_orders
