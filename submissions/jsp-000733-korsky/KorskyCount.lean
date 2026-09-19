import KorskyDefs

/-! Cardinality of Samuel Korsky's ordered ternary packing. -/
namespace Erdos882Korsky

noncomputable section


private theorem good_cons_small {k : ℕ} (h : Fin 2) (t : {w : Word k // Good w}) :
    Good (Fin.cons h.castSucc t.val) := by
  constructor
  · intro i
    refine Fin.cases ?_ (fun i => ?_) i
    · intro j hij hi
      simp only [Fin.cons_zero] at hi
      have hh := h.isLt
      have hv := congrArg Fin.val hi
      simp at hv
      omega
    · intro j
      refine Fin.cases ?_ (fun j => ?_) j
      · intro hij
        simp at hij
      · intro hij hi
        exact t.property.1 i j (by simpa using hij) (by simpa using hi)
  · obtain ⟨i, hi⟩ := t.property.2
    exact ⟨i.succ, by simpa using hi⟩

private theorem good_cons_two {k : ℕ} (t : Fin k → Fin 2) :
    Good (Fin.cons 2 (fun i => (t i).succ)) := by
  constructor
  · intro i j
    refine Fin.cases ?_ (fun j => ?_) j
    · intro hij
      simp at hij
    · intro hij hi
      simp
  · exact ⟨0, by simp⟩

private def goodStep (k : ℕ) :
    (Fin 2 × {w : Word k // Good w}) ⊕ (Fin k → Fin 2) →
      {w : Word (k+1) // Good w}
  | .inl ⟨h, t⟩ => ⟨Fin.cons h.castSucc t.val, good_cons_small h t⟩
  | .inr t => ⟨Fin.cons 2 (fun i => (t i).succ), good_cons_two t⟩

private theorem goodStep_injective (k : ℕ) : Function.Injective (goodStep k) := by
  intro x y hxy
  have hv := congrArg Subtype.val hxy
  cases x with
  | inl a =>
    cases y with
    | inl b =>
      apply congrArg Sum.inl
      apply Prod.ext
      · apply Fin.ext
        have hh := congrFun hv 0
        simpa [goodStep] using congrArg (fun z : Fin 3 => z.val) hh
      · apply Subtype.ext
        funext i
        have hh := congrFun hv i.succ
        simpa [goodStep] using hh
    | inr b =>
      have hh := congrArg Fin.val (congrFun hv 0)
      simp [goodStep] at hh
      have ha := a.1.isLt
      omega
  | inr a =>
    cases y with
    | inl b =>
      have hh := congrArg Fin.val (congrFun hv 0)
      simp [goodStep] at hh
      have hb := b.1.isLt
      omega
    | inr b =>
      apply congrArg Sum.inr
      funext i
      apply Fin.ext
      have hh := congrArg Fin.val (congrFun hv i.succ)
      simpa [goodStep] using hh

private theorem goodStep_surjective (k : ℕ) : Function.Surjective (goodStep k) := by
  intro w
  by_cases h : w.val 0 = 2
  · have hnz (i : Fin k) : w.val i.succ ≠ 0 :=
      w.property.1 0 i.succ (by simp) h
    let t : Fin k → Fin 2 := fun i => ⟨(w.val i.succ).val - 1, by
      have hlt := (w.val i.succ).isLt
      have hpos : 0 < (w.val i.succ).val := by
        have := hnz i
        by_contra hh
        apply this
        apply Fin.ext
        simp
        omega
      omega⟩
    refine ⟨Sum.inr t, ?_⟩
    apply Subtype.ext
    funext i
    refine Fin.cases ?_ (fun i => ?_) i
    · simpa [goodStep] using h.symm
    · apply Fin.ext
      have hpos : 0 < (w.val i.succ).val := by
        have := hnz i
        by_contra hh
        apply this
        apply Fin.ext
        simp
        omega
      simp [goodStep, t]
      omega
  · have hlt : (w.val 0).val < 2 := by
      have hb := (w.val 0).isLt
      have hne : (w.val 0).val ≠ 2 := by
        intro hh
        apply h
        apply Fin.ext
        simpa using hh
      omega
    let a : Fin 2 := ⟨(w.val 0).val, hlt⟩
    have ht : Good (fun i : Fin k => w.val i.succ) := by
      constructor
      · intro i j hij hi
        exact w.property.1 i.succ j.succ (by simpa using hij) hi
      · obtain ⟨i, hi⟩ := w.property.2
        cases i using Fin.cases with
        | zero => exact False.elim (h hi)
        | succ i => exact ⟨i, hi⟩
    refine ⟨Sum.inl (a, ⟨_, ht⟩), ?_⟩
    apply Subtype.ext
    funext i
    refine Fin.cases ?_ (fun i => ?_) i
    · apply Fin.ext
      simp [goodStep, a]
    · simp [goodStep]

private theorem good_card_step (k : ℕ) :
    Fintype.card {w : Word (k+1) // Good w} =
      2 * Fintype.card {w : Word k // Good w} + 2^k := by
  have h := Fintype.card_of_bijective (f := goodStep k)
    ⟨goodStep_injective k, goodStep_surjective k⟩
  simpa using h.symm

theorem good_card (k : ℕ) (hk : 0 < k) :
    Fintype.card {w : Word k // Good w} = k * 2^(k-1) := by
  cases k with
  | zero => omega
  | succ k =>
    induction k with
    | zero =>
      have hz : Fintype.card {w : Word 0 // Good w} = 0 := by
        let : IsEmpty {w : Word 0 // Good w} :=
          ⟨fun w => by obtain ⟨i, _⟩ := w.property.2; exact Fin.elim0 i⟩
        exact Fintype.card_eq_zero
      simp [good_card_step, hz]
    | succ k ih =>
      rw [good_card_step, ih (by omega)]
      simp only [Nat.add_sub_cancel]
      rw [pow_succ]
      ring

end

end Erdos882Korsky
