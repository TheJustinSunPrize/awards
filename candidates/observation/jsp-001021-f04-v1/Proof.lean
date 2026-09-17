import Statement

set_option autoImplicit false

namespace JSP001021
open scoped BigOperators

def outNeighbors {α : Type*} [Fintype α] [DecidableEq α]
    (T : Tournament α) (v : α) : Finset α :=
  Finset.univ.filter (fun w => T.edge v w)

 def inNeighbors {α : Type*} [Fintype α] [DecidableEq α]
    (T : Tournament α) (v : α) : Finset α :=
  Finset.univ.filter (fun w => T.edge w v)

abbrev outDegree {α : Type*} [Fintype α] [DecidableEq α]
    (T : Tournament α) (v : α) : Nat :=
  (outNeighbors T v).card

abbrev inDegree {α : Type*} [Fintype α] [DecidableEq α]
    (T : Tournament α) (v : α) : Nat :=
  (inNeighbors T v).card

lemma out_in_union {α : Type*} [Fintype α] [DecidableEq α]
    (T : Tournament α) (v : α) :
    outNeighbors T v ∪ inNeighbors T v = Finset.univ.erase v := by
  ext w
  simp only [outNeighbors, inNeighbors, Finset.mem_union, Finset.mem_filter,
    Finset.mem_univ, true_and, Finset.mem_erase]
  by_cases h : w = v
  · subst w
    constructor
    · rintro (h | h)
      exact (T.antisymm h h).elim
      exact (T.antisymm h h).elim
    · intro h
      exact (h.1 rfl).elim
  · simp only [h, and_true]
    constructor
    · intro _
      trivial
    · intro _
      exact T.complete (Ne.symm h)

lemma out_in_disjoint {α : Type*} [Fintype α] [DecidableEq α]
    (T : Tournament α) (v : α) :
    Disjoint (outNeighbors T v) (inNeighbors T v) := by
  rw [Finset.disjoint_left]
  intro w h₁ h₂
  have h₁' : T.edge v w := by simpa [outNeighbors] using h₁
  have h₂' : T.edge w v := by simpa [inNeighbors] using h₂
  exact T.antisymm h₁' h₂'

lemma out_add_in_degree {α : Type*} [Fintype α] [DecidableEq α]
    (T : Tournament α) (v : α) :
    outDegree T v + inDegree T v = Fintype.card α - 1 := by
  have hcard := congrArg Finset.card (out_in_union T v)
  rw [Finset.card_union_of_disjoint (out_in_disjoint T v)] at hcard
  simpa [outDegree, inDegree] using hcard

lemma sum_inDegree_eq_sum_outDegree {α : Type*} [Fintype α] [DecidableEq α]
    (T : Tournament α) :
    ∑ v : α, inDegree T v = ∑ v : α, outDegree T v := by
  simp only [inDegree, inNeighbors, outDegree, outNeighbors, Finset.card_filter]
  rw [Finset.sum_comm]

def restrict {α : Type*} [DecidableEq α]
    (T : Tournament α) (s : Finset α) : Tournament s where
  edge a b := T.edge a.1 b.1
  complete := by
    intro a b hab
    exact T.complete (by
      intro h
      exact hab (Subtype.ext h))
  antisymm := by
    intro a b hab
    exact T.antisymm hab
  edge_decidable := by infer_instance

def rootedCount {α : Type*} [Fintype α] [DecidableEq α]
    (T : Tournament α) : Nat → Nat
  | 0 => 1
  | k + 1 => ∑ v : α, rootedCount (restrict T (outNeighbors T v)) k

lemma rootedCount_zero {α : Type*} [Fintype α] [DecidableEq α]
    (T : Tournament α) : rootedCount T 0 = 1 := rfl

lemma rootedCount_succ {α : Type*} [Fintype α] [DecidableEq α]
    (T : Tournament α) (k : Nat) :
    rootedCount T (k + 1) =
      ∑ v : α, rootedCount (restrict T (outNeighbors T v)) k := rfl

lemma outdegree_sum {α : Type*} [Fintype α] [DecidableEq α]
    (T : Tournament α) :
    ∑ v : α, outDegree T v = (Fintype.card α).choose 2 := by
  have hsum :
      (∑ v : α, outDegree T v) + ∑ v : α, inDegree T v =
        Fintype.card α * (Fintype.card α - 1) := by
    rw [← Finset.sum_add_distrib]
    calc
      (∑ v : α, (outDegree T v + inDegree T v)) =
          ∑ v : α, (Fintype.card α - 1) := by
            apply Finset.sum_congr rfl
            intro v hv
            exact out_add_in_degree T v
      _ = Fintype.card α * (Fintype.card α - 1) := by simp
  rw [sum_inDegree_eq_sum_outDegree T] at hsum
  have hchoose :
      2 * (Fintype.card α).choose 2 =
        Fintype.card α * (Fintype.card α - 1) := by
    rw [Nat.choose_two_right]
    exact Nat.mul_div_cancel' (Nat.even_mul_pred_self _).two_dvd
  apply Nat.eq_of_mul_eq_mul_left (by decide : 0 < 2)
  rw [Nat.two_mul]
  exact hsum.trans hchoose.symm

lemma exists_transitive_of_rootedCount_pos :
    ∀ {α : Type*} [Fintype α] [DecidableEq α]
      (T : Tournament α) (k : Nat),
      0 < rootedCount T k →
        ∃ f : Fin k → α, TransitiveEmbedding T k f := by
  intro α _ _ T k
  induction k generalizing α with
  | zero =>
      intro _
      refine ⟨Fin.elim0, ?_⟩
      constructor
      · intro i j hij
        exact Fin.elim0 i
      · intro i j hij
        exact Fin.elim0 i
  | succ k ih =>
      intro hpos
      rw [rootedCount_succ] at hpos
      obtain ⟨v, hv⟩ :
          ∃ v : α, 0 < rootedCount (restrict T (outNeighbors T v)) k := by
        by_contra h
        push_neg at h
        have hz :
            ∑ v : α, rootedCount (restrict T (outNeighbors T v)) k = 0 := by
          apply Finset.sum_eq_zero
          intro v hv
          have hv' : rootedCount (restrict T (outNeighbors T v)) k ≤ 0 := h v
          omega
        omega
      obtain ⟨g, hg⟩ :=
        ih (T := restrict T (outNeighbors T v)) hv
      refine ⟨Fin.cons v (fun i => (g i).1), ?_⟩
      constructor
      · intro i j
        refine Fin.cases ?_ (fun i => ?_) i <;>
          refine Fin.cases ?_ (fun j => ?_) j
        · intro _
          exact rfl
        · intro hij
          have hij' : v = (g j).1 := by simpa using hij
          have he : T.edge v (g j).1 := by
            exact (Finset.mem_filter.mp (g j).2).2
          exact (T.antisymm he (hij' ▸ he)).elim
        · intro hij
          have hij' : (g i).1 = v := by simpa using hij
          have he : T.edge v (g i).1 := by
            exact (Finset.mem_filter.mp (g i).2).2
          rw [hij'] at he
          exact (T.antisymm he he).elim
        · intro hij
          have hgg : (g i).1 = (g j).1 := by
            simpa using hij
          exact congrArg Fin.succ (hg.1 (Subtype.ext hgg))
      · intro i j
        refine Fin.cases ?_ (fun i => ?_) i <;>
          refine Fin.cases ?_ (fun j => ?_) j
        · intro hij
          exact (lt_irrefl _ hij).elim
        · intro _
          exact (Finset.mem_filter.mp (g j).2).2
        · intro hij
          exact (Fin.not_lt_zero _ hij).elim
        · intro hij
          exact hg.2 (Fin.succ_lt_succ_iff.mp hij)

def root (i : Nat) : ℝ := (2 : ℝ)^i - 1

 def rawPoly (k : Nat) (x : ℝ) : ℝ :=
  ∏ i ∈ Finset.range k, (x - root i)

lemma differentiable_rawPoly (k : Nat) :
    Differentiable ℝ (rawPoly k) := by
  unfold rawPoly
  fun_prop

lemma deriv_rawPoly (k : Nat) (x : ℝ) :
    deriv (rawPoly k) x =
      ∑ i ∈ Finset.range k, ∏ j ∈ (Finset.range k).erase i, (x - root j) := by
  unfold rawPoly
  rw [deriv_fun_finsetProd]
  · simp
  · intro i hi
    fun_prop

lemma root_mono {i k : Nat} (hik : i ≤ k) : root i ≤ root k := by
  unfold root
  exact sub_le_sub_right (pow_le_pow_right₀ (by norm_num) hik) 1

lemma monotoneOn_deriv_rawPoly_succ (k : Nat) :
    MonotoneOn (deriv (rawPoly (k + 1))) (Set.Ioi (root k)) := by
  intro a ha b hb hab
  rw [deriv_rawPoly, deriv_rawPoly]
  gcongr with i hi
  intro j hj
  rw [Finset.mem_erase, Finset.mem_range] at hj
  apply sub_nonneg_of_le
  exact (root_mono (Nat.lt_succ_iff.mp hj.2)).trans ha.le

lemma convexOn_rawPoly_succ (k : Nat) :
    ConvexOn ℝ (Set.Ici (root k)) (rawPoly (k + 1)) := by
  apply MonotoneOn.convexOn_of_deriv (convex_Ici _)
      (differentiable_rawPoly (k + 1)).continuous.continuousOn
      (differentiable_rawPoly (k + 1)).differentiableOn
  rw [interior_Ici]
  exact monotoneOn_deriv_rawPoly_succ k

 noncomputable def denom (k : Nat) : ℝ :=
  ∏ i ∈ Finset.range k, (2 : ℝ)^i

lemma denom_pos (k : Nat) : 0 < denom k := by
  unfold denom
  positivity

 noncomputable def poly (k : Nat) (x : ℝ) : ℝ := rawPoly k x / denom k

lemma convexOn_poly_succ (k : Nat) :
    ConvexOn ℝ (Set.Ici (root k)) (poly (k + 1)) := by
  have h := (convexOn_rawPoly_succ k).smul
    (le_of_lt (inv_pos.mpr (denom_pos (k + 1))))
  have heq : poly (k + 1) =
      fun x => (denom (k + 1))⁻¹ * rawPoly (k + 1) x := by
    funext x
    simp [poly, div_eq_mul_inv, mul_comm]
  rw [heq]
  simpa only [smul_eq_mul] using h

lemma monotoneOn_poly_succ (k : Nat) :
    MonotoneOn (poly (k + 1)) (Set.Ici (root k)) := by
  intro a ha b hb hab
  rw [show poly (k + 1) a = (denom (k + 1))⁻¹ * rawPoly (k + 1) a by
    simp [poly, div_eq_mul_inv, mul_comm]]
  rw [show poly (k + 1) b = (denom (k + 1))⁻¹ * rawPoly (k + 1) b by
    simp [poly, div_eq_mul_inv, mul_comm]]
  apply mul_le_mul_of_nonneg_left
  · unfold rawPoly
    apply Finset.prod_le_prod
    · intro i hi
      exact sub_nonneg_of_le
        ((root_mono (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))).trans ha)
    · intro i hi
      exact sub_le_sub_right hab _
  · exact (inv_pos.mpr (denom_pos (k + 1))).le

lemma rawPoly_succ (k : Nat) (x : ℝ) :
    rawPoly (k + 1) x = rawPoly k x * (x - root k) := by
  unfold rawPoly
  rw [Finset.prod_range_succ]

lemma denom_succ (k : Nat) :
    denom (k + 1) = denom k * (2 : ℝ)^k := by
  unfold denom
  rw [Finset.prod_range_succ]

lemma poly_succ (k : Nat) (x : ℝ) :
    poly (k + 1) x = poly k x * ((x - root k) / (2 : ℝ)^k) := by
  rw [poly, rawPoly_succ, denom_succ, poly]
  field_simp [denom_pos k]

lemma poly_shift_identity (k : Nat) (n : ℝ) :
    n * poly (k + 1) ((n - 1) / 2) = poly (k + 2) n := by
  induction k with
  | zero =>
      rw [poly_succ 0 ((n - 1) / 2), poly_succ 1 n]
      norm_num [poly, root, rawPoly, denom]
  | succ k ih =>
      calc
        n * poly (k + 2) ((n - 1) / 2) =
            (n * poly (k + 1) ((n - 1) / 2)) *
              (((n - 1) / 2 - root (k + 1)) / (2 : ℝ)^(k + 1)) := by
                rw [poly_succ (k + 1) ((n - 1) / 2)]
                ring
        _ = poly (k + 2) n *
              (((n - 1) / 2 - root (k + 1)) / (2 : ℝ)^(k + 1)) := by
                rw [ih]
        _ = poly (k + 3) n := by
                rw [poly_succ (k + 2) n]
                have hroot : root (k + 2) = 2 * root (k + 1) + 1 := by
                  unfold root
                  rw [show (2 : ℝ) ^ (k + 2) = 2 ^ (k + 1) * 2 by
                    rw [pow_succ]]
                  ring
                rw [hroot]
                have hpow : (2 : ℝ) ^ (k + 2) = 2 ^ (k + 1) * 2 := by
                  rw [pow_succ]
                rw [hpow]
                field_simp
                ring

lemma poly_at_root (k : Nat) : poly (k + 1) (root k) = 0 := by
  unfold poly rawPoly
  rw [Finset.prod_eq_zero (Finset.mem_range.2 (Nat.lt_succ_self k))]
  simp
  ring

 noncomputable def piece (k : Nat) (x : ℝ) : ℝ :=
  (Set.Ici (root k)).piecewise (poly (k + 1)) 0 x

lemma convexOn_piece (k : Nat) : ConvexOn ℝ Set.univ (piece k) := by
  unfold piece
  apply convexOn_univ_piecewise_Ici_of_monotoneOn_Ici_antitoneOn_Iic
    (convexOn_poly_succ k) (convexOn_const 0 (convex_Iic _))
    (monotoneOn_poly_succ k) antitoneOn_const
  simp [poly_at_root]

noncomputable def moonFun : Nat → ℝ → ℝ
  | 0 => fun _ => 1
  | k + 1 => fun x => if root k ≤ x then poly (k + 1) x else 0

lemma convexOn_moonFun (k : Nat) : ConvexOn ℝ Set.univ (moonFun k) := by
  cases k with
  | zero =>
      simpa [moonFun] using (convexOn_const (1 : ℝ) (convex_univ : Convex ℝ Set.univ))
  | succ k =>
      have h := convexOn_piece k
      have heq : piece k =
          (fun x => if root k ≤ x then poly (k + 1) x else 0) := by
        funext x
        simp [piece, Set.piecewise, Set.mem_Ici]
      rw [heq] at h
      simpa [moonFun] using h

lemma moonFun_nonneg {k : Nat} {x : ℝ} : 0 ≤ moonFun k x := by
  cases k with
  | zero => simp [moonFun]
  | succ k =>
      dsimp [moonFun]
      split_ifs with h
      · apply div_nonneg
        · unfold rawPoly
          apply Finset.prod_nonneg
          intro i hi
          exact sub_nonneg_of_le
            ((root_mono (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))).trans h)
        · exact (denom_pos (k + 1)).le
      · exact le_rfl

lemma moonFun_shift {k : Nat} {n : ℝ} (hn : 0 ≤ n) :
    n * moonFun k ((n - 1) / 2) ≥ moonFun (k + 1) n := by
  cases k with
  | zero =>
      have hroot : root 0 ≤ n := by simpa [root] using hn
      rw [show moonFun 0 ((n - 1) / 2) = 1 by rfl, show moonFun 1 n =
        if root 0 ≤ n then poly 1 n else 0 by rfl, if_pos hroot]
      norm_num [poly, rawPoly, denom, root]
  | succ k =>
      have hroot : root (k + 1) = 2 * root k + 1 := by
        unfold root
        rw [show (2 : ℝ) ^ (k + 1) = 2 ^ k * 2 by rw [pow_succ]]
        ring
      by_cases h : root (k + 1) ≤ n
      · have havg : root k ≤ (n - 1) / 2 := by
          rw [hroot] at h
          linarith
        rw [show moonFun (k + 1) ((n - 1) / 2) =
            if root k ≤ (n - 1) / 2 then poly (k + 1) ((n - 1) / 2) else 0 by rfl,
          if_pos havg,
          show moonFun (k + 2) n =
            if root (k + 1) ≤ n then poly (k + 2) n else 0 by rfl,
          if_pos h]
        rw [poly_shift_identity k n]
      · rw [show moonFun (k + 2) n =
            if root (k + 1) ≤ n then poly (k + 2) n else 0 by rfl,
          if_neg h]
        exact mul_nonneg hn (moonFun_nonneg (k := k + 1) (x := (n - 1) / 2))

abbrev EmbeddingFiber {α : Type*} [Fintype α] [DecidableEq α]
    (T : Tournament α) (k : Nat) (v : α) :=
  {f : EmbeddingType T (k + 1) // f.1 0 = v}

noncomputable instance embeddingFiberFintype {α : Type*} [Fintype α] [DecidableEq α]
    (T : Tournament α) (k : Nat) (v : α) : Fintype (EmbeddingFiber T k v) :=
  Fintype.ofFinite _

noncomputable def embeddingFiberEquiv
    {α : Type*} [Fintype α] [DecidableEq α]
    (T : Tournament α) (k : Nat) (v : α) :
    EmbeddingFiber T k v ≃
      EmbeddingType (restrict T (outNeighbors T v)) k where
  toFun z := by
    let g : Fin k → (outNeighbors T v) := fun i =>
      ⟨z.1.1 i.succ, by
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _, ?_⟩
        have he : T.edge (z.1.1 0) (z.1.1 i.succ) :=
          z.1.2.2 (Fin.succ_pos i)
        simpa only [z.2] using he
      ⟩
    refine ⟨g, ?_⟩
    constructor
    · intro i j hij
      apply Fin.succ_injective k
      apply z.1.2.1
      exact congrArg Subtype.val hij
    · intro i j hij
      simpa [restrict] using z.1.2.2 (Fin.succ_lt_succ_iff.mpr hij)
  invFun g := by
    let f : Fin (k + 1) → α := Fin.cons v (fun i => (g.1 i).1)
    refine ⟨⟨f, ?_⟩, ?_⟩
    · refine ⟨?_, ?_⟩
      · rw [Fin.cons_injective_iff]
        constructor
        · rintro ⟨i, hi⟩
          have hi' : (g.1 i).1 = v := by simpa using hi
          have he : T.edge v (g.1 i).1 :=
            (Finset.mem_filter.mp (g.1 i).2).2
          have he' := he
          rw [hi'] at he'
          exact T.antisymm he' he'
        · intro i j hij
          apply g.2.1
          exact Subtype.ext hij
      · intro i j
        refine Fin.cases ?_ (fun i => ?_) i <;>
          refine Fin.cases ?_ (fun j => ?_) j
        · intro hij
          exact (lt_irrefl _ hij).elim
        · intro _
          exact (Finset.mem_filter.mp (g.1 j).2).2
        · intro hij
          exact (Fin.not_lt_zero _ hij).elim
        · intro hij
          simpa [f, restrict] using g.2.2 (Fin.succ_lt_succ_iff.mp hij)
    · simp [f]

  left_inv z := by
    apply Subtype.ext
    apply Subtype.ext
    funext i
    refine Fin.cases ?_ (fun i => ?_) i
    · simpa using z.2.symm
    · rfl
  right_inv g := by
    apply Subtype.ext
    funext i
    apply Subtype.ext
    rfl

lemma embeddingCount_succ {α : Type*} [Fintype α] [DecidableEq α]
    (T : Tournament α) (k : Nat) :
    embeddingCount T (k + 1) =
      ∑ v : α, embeddingCount (restrict T (outNeighbors T v)) k := by
  let head : EmbeddingType T (k + 1) → α := fun f => f.1 0
  calc
    embeddingCount T (k + 1) =
        Fintype.card (Sigma fun v => {f : EmbeddingType T (k + 1) // head f = v}) := by
      exact Fintype.card_congr (Equiv.sigmaFiberEquiv head).symm
    _ = ∑ v : α, Fintype.card {f : EmbeddingType T (k + 1) // head f = v} :=
      Fintype.card_sigma
    _ = ∑ v : α, embeddingCount (restrict T (outNeighbors T v)) k := by
      apply Finset.sum_congr rfl
      intro v hv
      exact Fintype.card_congr (embeddingFiberEquiv T k v)

lemma card_outNeighbors {α : Type*} [Fintype α] [DecidableEq α]
    (T : Tournament α) (v : α) :
    Fintype.card (outNeighbors T v) = outDegree T v := by
  exact Fintype.card_coe (outNeighbors T v)

lemma embeddingCount_lower :
    ∀ {α : Type*} [Fintype α] [DecidableEq α]
      (T : Tournament α) (k : Nat),
      moonFun k (Fintype.card α) ≤ (embeddingCount T k : ℝ) := by
  intro α _ _ T k
  induction k generalizing α with
  | zero =>
      have hcard : Fintype.card (EmbeddingType T 0) = 1 := by
        apply (Fintype.card_eq_one_iff).2
        refine ⟨⟨Fin.elim0, ?_⟩, ?_⟩
        · constructor
          · intro i j
            exact Fin.elim0 i
          · intro i j hij
            exact Fin.elim0 i
        · intro y
          apply Subtype.ext
          funext i
          exact Fin.elim0 i
      simp [moonFun, embeddingCount, hcard]
  | succ k ih =>
      by_cases hzero : Fintype.card α = 0
      · haveI : IsEmpty α := Fintype.card_eq_zero_iff.mp hzero
        rw [embeddingCount_succ]
        simp [hzero]
        cases k with
        | zero =>
            have hp : poly 1 (0 : ℝ) = 0 := by
              simpa [root] using poly_at_root 0
            simp [moonFun, hzero, root, hp]
        | succ k =>
            have hroot : 0 < root (k + 1) := by
              unfold root
              have hpow : (2 : ℝ) ≤ (2 : ℝ) ^ (k + 1) := by
                have hone : (1 : ℝ) ≤ (2 : ℝ) ^ k := by
                  simpa using pow_le_pow_right₀ (a := (2 : ℝ)) (by norm_num)
                    (Nat.zero_le k)
                rw [pow_succ]
                nlinarith
              linarith
            simp [moonFun, hzero, not_le_of_gt hroot]
      · haveI : Nonempty α := Fintype.card_pos_iff.mp (Nat.pos_of_ne_zero hzero)
        have hn : 0 < (Fintype.card α : ℝ) := by
          exact_mod_cast Fintype.card_pos
        have hterm : ∀ v : α,
            moonFun k (outDegree T v) ≤
              (embeddingCount (restrict T (outNeighbors T v)) k : ℝ) := by
          intro v
          have h := ih (T := restrict T (outNeighbors T v))
          simpa [card_outNeighbors] using h
        have hsumbound :
            ∑ v : α, moonFun k (outDegree T v) ≤
              ∑ v : α, (embeddingCount (restrict T (outNeighbors T v)) k : ℝ) := by
          apply Finset.sum_le_sum
          intro v hv
          exact hterm v
        let w : α → ℝ := fun _ => (Fintype.card α : ℝ)⁻¹
        have hw0 : ∀ i ∈ (Finset.univ : Finset α), 0 ≤ w i := by
          intro i hi
          dsimp [w]
          exact (inv_pos.mpr hn).le
        have hw1 : ∑ i ∈ (Finset.univ : Finset α), w i = 1 := by
          simp [w, hn.ne']
        have hj := (convexOn_moonFun k).map_sum_le
          (t := Finset.univ) (w := w)
          (p := fun v : α => (outDegree T v : ℝ)) hw0 hw1 (by simp)
        have havg :
            (∑ v : α, w v * (outDegree T v : ℝ)) =
              ((Fintype.card α : ℝ) - 1) / 2 := by
          dsimp [w]
          have hsumcast :
              (∑ v : α, (outDegree T v : ℝ)) =
                ((∑ v : α, outDegree T v : ℕ) : ℝ) := by
            norm_cast
          rw [← Finset.mul_sum, hsumcast, outdegree_sum T]
          field_simp
          rw [Nat.cast_choose_two]
          ring
        have hj' :
            (Fintype.card α : ℝ) * moonFun k
                (((Fintype.card α : ℝ) - 1) / 2) ≤
              ∑ v : α, moonFun k (outDegree T v) := by
          have hj'' :
              moonFun k (((Fintype.card α : ℝ) - 1) / 2) ≤
                ∑ v : α, w v * moonFun k (outDegree T v) := by
            simpa [smul_eq_mul, havg] using hj
          calc
            (Fintype.card α : ℝ) * moonFun k
                (((Fintype.card α : ℝ) - 1) / 2) ≤
                (Fintype.card α : ℝ) *
                  (∑ v : α, w v * moonFun k (outDegree T v)) :=
              mul_le_mul_of_nonneg_left hj'' hn.le
            _ = ∑ v : α, moonFun k (outDegree T v) := by
              dsimp [w]
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro v hv
              field_simp
        have hshift := moonFun_shift (k := k)
          (n := (Fintype.card α : ℝ)) hn.le
        have hrooted_sum :
            ∑ v : α, (embeddingCount (restrict T (outNeighbors T v)) k : ℝ) =
              (embeddingCount T (k + 1) : ℝ) := by
          rw [embeddingCount_succ, Nat.cast_sum]
        calc
          moonFun (k + 1) (Fintype.card α) ≤
              (Fintype.card α : ℝ) * moonFun k
                (((Fintype.card α : ℝ) - 1) / 2) := hshift
          _ ≤ ∑ v : α, moonFun k (outDegree T v) := hj'
          _ ≤ ∑ v : α,
              (embeddingCount (restrict T (outNeighbors T v)) k : ℝ) := hsumbound
          _ = (embeddingCount T (k + 1) : ℝ) := hrooted_sum

lemma poly_eq_formula (n m : Nat) :
    poly (m + 1) (n : ℝ) =
      ∏ i ∈ Finset.range (m + 1),
        ((n : ℝ) - ((2 : ℝ)^i - 1)) / (2 : ℝ)^i := by
  unfold poly rawPoly denom
  rw [Finset.prod_div_distrib]
  simp [root]

lemma moonFun_nat_eq_moonTau (n k : Nat) :
    moonFun k (n : ℝ) = moonTau n k := by
  cases k with
  | zero => rfl
  | succ m =>
      have hpow : (2 : ℝ)^m = ((2 ^ m : Nat) : ℝ) := by
        norm_num
      by_cases hA : 2 ^ m ≤ n
      · have hcond : root m ≤ (n : ℝ) := by
          unfold root
          have hcast : (2 : ℝ)^m ≤ (n : ℝ) := by
            exact_mod_cast hA
          linarith
        simp [moonFun, moonTau, hA, hcond, poly_eq_formula]
      · have hlt : n < 2 ^ m := Nat.lt_of_not_ge hA
        by_cases heq : n + 1 = 2 ^ m
        · have hrootEq : root m = (n : ℝ) := by
            unfold root
            rw [hpow]
            have hcast : ((2 ^ m : Nat) : ℝ) = (n : ℝ) + 1 := by
              exact_mod_cast heq.symm
            rw [hcast]
            ring
          have hp : poly (m + 1) (n : ℝ) = 0 := by
            rw [← hrootEq]
            exact poly_at_root m
          simp [moonFun, moonTau, hA, hrootEq.le, hp]
        · have hlt2 : n + 1 < 2 ^ m := by omega
          have hcond : ¬ root m ≤ (n : ℝ) := by
            unfold root
            rw [hpow]
            have hcast : (n : ℝ) + 1 < ((2 ^ m : Nat) : ℝ) := by
              exact_mod_cast hlt2
            linarith
          simp [moonFun, moonTau, hA, hcond]

lemma embeddingCount_lower_tau :
    ∀ {α : Type*} [Fintype α] [DecidableEq α]
      (T : Tournament α) (k : Nat),
      moonTau (Fintype.card α) k ≤ (embeddingCount T k : ℝ) := by
  intro α _ _ T k
  rw [← moonFun_nat_eq_moonTau]
  exact embeddingCount_lower T k

lemma transitive_exists_of_card_ge
    {α : Type*} [Fintype α] [DecidableEq α]
    (T : Tournament α) {k : Nat}
    (hk : 2 ^ (k - 1) ≤ Fintype.card α) :
    ∃ f : Fin k → α, TransitiveEmbedding T k f := by
  by_cases hk0 : k = 0
  · subst k
    refine ⟨Fin.elim0, ?_⟩
    constructor
    · intro i j
      exact Fin.elim0 i
    · intro i j hij
      exact Fin.elim0 i
  · have hkpos : 0 < k := Nat.pos_of_ne_zero hk0
    have hbound : 0 < moonTau (Fintype.card α) k := by
      cases k with
      | zero => contradiction
      | succ m =>
          dsimp [moonTau]
          have hpow : 2 ^ m ≤ Fintype.card α := by
            simpa [Nat.succ_sub_one] using hk
          rw [if_pos hpow]
          apply Finset.prod_pos
          intro i hi
          apply div_pos
          · apply sub_pos.mpr
            have hi_le : i ≤ m :=
              Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
            have hpowreal : (2 : ℝ)^m ≤ (Fintype.card α : ℝ) := by
              exact_mod_cast hpow
            have hrootm : root m < (2 : ℝ)^m := by
              unfold root
              linarith
            exact (root_mono hi_le).trans_lt (hrootm.trans_le hpowreal)
          · positivity
    have hcount : 0 < embeddingCount T k := by
      have h := embeddingCount_lower_tau T k
      have hreal : (0 : ℝ) < embeddingCount T k := lt_of_lt_of_le hbound h
      exact_mod_cast hreal
    have hcardpos : 0 < Fintype.card (EmbeddingType T k) := by
      simpa [embeddingCount] using hcount
    letI : Nonempty (EmbeddingType T k) := Fintype.card_pos_iff.mp hcardpos
    obtain ⟨f, hf⟩ := (inferInstance : Nonempty (EmbeddingType T k))
    exact ⟨f, hf⟩

theorem tournament_transitive_subtournament
    (k : Nat) :
    ∀ {α : Type*} [Fintype α] [DecidableEq α]
      (T : Tournament α), Fintype.card α = 2 ^ k →
      ∃ f : Fin (k + 1) → α, TransitiveEmbedding T (k + 1) f := by
  intro α _ _ T hcard
  apply transitive_exists_of_card_ge T
  simpa [Nat.succ_sub_one, hcard]

theorem solution : JSP001021Statement := by
  intro α _ _ T k
  exact embeddingCount_lower_tau T k

end JSP001021
