import Mathlib

/-!
# Černý conjecture: the Pin–Frankl cubic bound and Kari's theorem for Eulerian automata

The Černý conjecture (1964) asserts that every synchronizing complete deterministic finite
automaton with `n` states has a synchronizing (reset) word of length at most `(n - 1)^2`. It is
stated as `cerny_conjecture` in Google DeepMind's formal-conjectures project,
`FormalConjectures/Wikipedia/CernyConjecture.lean`, on top of Mathlib's `DFA α σ` and the predicates
`DFA.IsSynchronizingWord` / `DFA.IsSynchronizing` from
`FormalConjecturesForMathlib/Computability/DFA.lean`. Those two definitions are copied verbatim
below (Apache-2.0).

This file proves two classical partial results.

* `pin_frankl_bound`: every synchronizing DFA with `n` states has a synchronizing word `w` with
  `6 * |w| ≤ n^3 - n`, i.e. `|w| ≤ (n^3 - n) / 6` (`pin_frankl_bound'`).
  J.-E. Pin, *On two combinatorial problems arising from automata theory*, Ann. Discrete Math. 17
  (1983) 535–548, reduced this bound to a combinatorial statement proved by
  P. Frankl, *An extremal problem for two families of sets*, European J. Combin. 3 (1982) 125–127.
* `kari_eulerian_bound`: if every state has exactly `|Σ|` incoming transitions (counted with
  multiplicity), i.e. the underlying digraph is Eulerian in the sense of Kari, then a synchronizing
  word of length at most `(n - 2)(n - 1) + 1 = n^2 - 3n + 3 ≤ (n - 1)^2` exists
  (`cerny_conjecture_eulerian` restates the last inequality in the shape of `cerny_conjecture`).
  J. Kari, *Synchronizing finite automata on Eulerian digraphs*, Theoret. Comput. Sci. 295 (2003)
  223–232, Theorem 2. Some surveys also require strong connectivity in the definition of an
  Eulerian automaton; the theorem here does not assume it, so it covers that reading too.

Frankl's theorem is proved in its general form (`frankl_skew_bollobas`): if `A₁, …, Aₘ` are
`a`-sets and `B₁, …, Bₘ` are `b`-sets with `Aᵢ ∩ Bᵢ = ∅` for all `i` and `Aᵢ ∩ Bⱼ ≠ ∅` for
`i < j`, then `m ≤ (a + b).choose a`.

## Proofs

* Frankl. Give the points distinct rational coordinates `c x` and put
  `gⱼ = ∏_{y ∈ Bⱼ} (X - c y)`, a polynomial of degree `≤ b`. The value
  `Hⱼ(Aᵢ) = ∏_{x ∈ Aᵢ} gⱼ(c x)` vanishes iff `Aᵢ ∩ Bⱼ ≠ ∅`. Expanding the product, `Hⱼ(Aᵢ)` is
  a fixed linear combination of the numbers `rⱼ(s) = ∏_{e ∈ s} coeff_e(gⱼ)`, where `s` runs over
  the multisets of size `a` in `{0, …, b}`. The matrix `(Hⱼ(Aᵢ))` is triangular with nonzero
  diagonal, so the vectors `rⱼ` are linearly independent in a space of dimension
  `|Sym^a {0, …, b}| = (a + b).choose a`.
* Pin. Let `|S| = k ≥ 2` and let `w = a₁ ⋯ a_ℓ` be a shortest word with `|S.w| < k`. Put
  `Sᵢ = S.(a₁ ⋯ a_{i-1})`, so `|Sᵢ| = k`, and pick `xᵢ ≠ yᵢ` in `Sᵢ` merged by `aᵢ ⋯ a_ℓ`.
  For `j < i`, `{xᵢ, yᵢ} ⊆ Sⱼ` would make `a₁ ⋯ a_{j-1} aᵢ ⋯ a_ℓ` a shorter shrinking word. So
  `Aᵢ = {xᵢ, yᵢ}` and `Bᵢ = Q \ Sᵢ` satisfy Frankl's hypotheses with `a = 2`, `b = n - k`, and
  `ℓ ≤ (n - k + 2).choose 2`. Summing over `k = n, …, 2` gives `(n + 1).choose 3 = (n^3 - n) / 6`.
* Kari. Write `P.w⁻¹ = {q | q.w ∈ P}`. The in-degree condition gives
  `∑_{b ∈ Σ} |P.(b w)⁻¹| = |Σ| · |P.w⁻¹|`, so if `|P.w⁻¹| ≠ |P|` then some word of length at most
  `|w|` has `|P.w⁻¹| > |P|`. For `0 < |P| < n` put `x = n·[P] - |P|·𝟙 ∈ ℚ^Q` and let `Vᵢ` be the
  span of the vectors `q ↦ x (q.w)` with `|w| ≤ i`. If `|P.w⁻¹| = |P|` for all `|w| ≤ n - 1`, then
  `V_{n-1}` lies in the hyperplane of coordinate sum zero, of dimension `n - 1`. So the chain `Vᵢ`
  stabilises before `n - 1`, and then all `Vᵢ` lie in that hyperplane. A synchronizing word
  contradicts this. Hence each proper nonempty `P` grows under some word of length `≤ n - 1`.
  Starting from `P = {q | q.a = r}` with `|P| ≥ 2` gives the bound `(n - 2)(n - 1) + 1`.
-/

open Finset Polynomial

/-! ### Definitions copied verbatim from formal-conjectures

Source: `FormalConjecturesForMathlib/Computability/DFA.lean` in
https://github.com/google-deepmind/formal-conjectures (Apache-2.0). -/

namespace DFA

variable {α : Type*} {σ : Type*}

/-- A word `w` is a **synchronizing word** (or reset word) for a DFA `M` if reading `w` from
any state leads to the same single state. -/
def IsSynchronizingWord (M : DFA α σ) (w : List α) : Prop :=
  ∃ p : σ, ∀ q : σ, M.evalFrom q w = p

/-- A DFA `M` is **synchronizing** if it has at least one synchronizing word. -/
def IsSynchronizing (M : DFA α σ) : Prop :=
  ∃ w : List α, M.IsSynchronizingWord w

end DFA

namespace CernyConjecture

/-! ### Frankl's theorem -/

/-- **Frankl (1982)**, skew Bollobás theorem: if `A₁, …, Aₘ` are `a`-element sets and
`B₁, …, Bₘ` are `b`-element sets with `Aᵢ ∩ Bᵢ = ∅` for every `i` and `Aᵢ ∩ Bⱼ ≠ ∅` whenever
`i < j`, then `m ≤ (a + b).choose a`. -/
theorem frankl_skew_bollobas {V : Type*} [DecidableEq V] {m a b : ℕ}
    (A B : Fin m → Finset V) (hA : ∀ i, (A i).card = a) (hB : ∀ i, (B i).card = b)
    (hAB : ∀ i, Disjoint (A i) (B i))
    (hcross : ∀ i j, i < j → ¬ Disjoint (A i) (B j)) :
    m ≤ (a + b).choose a := by
  classical
  set U : Finset V := univ.biUnion (fun i => A i ∪ B i) with hU
  -- distinct rational coordinates on the ground set `U`
  let c : V → ℚ := fun x => if h : x ∈ U then ((U.equivFin ⟨x, h⟩ : ℕ) : ℚ) else 0
  have hc : ∀ x ∈ U, ∀ y ∈ U, c x = c y → x = y := by
    intro x hx y hy hxy
    simp only [c, hx, hy, dite_true, Nat.cast_inj] at hxy
    have := U.equivFin.injective (Fin.ext hxy)
    simpa using this
  have hAU : ∀ i, A i ⊆ U := fun i x hx =>
    mem_biUnion.2 ⟨i, mem_univ _, mem_union_left _ hx⟩
  have hBU : ∀ i, B i ⊆ U := fun i x hx =>
    mem_biUnion.2 ⟨i, mem_univ _, mem_union_right _ hx⟩
  let g : Fin m → ℚ[X] := fun j => ∏ y ∈ B j, (X - C (c y))
  have hdeg : ∀ j, (g j).natDegree < b + 1 := by
    intro j
    have h1 := Polynomial.natDegree_prod_le (B j) (fun y => X - C (c y))
    have h2 : ∑ y ∈ B j, (X - C (c y)).natDegree ≤ ∑ y ∈ B j, 1 :=
      sum_le_sum fun y _ => natDegree_X_sub_C_le _
    simp only [sum_const, smul_eq_mul, mul_one, hB j] at h2
    simp only [g]
    omega
  have hH : ∀ i j, (∏ x ∈ A i, (g j).eval (c x)) = 0 ↔ ¬ Disjoint (A i) (B j) := by
    intro i j
    simp only [g, eval_prod, eval_sub, eval_X, eval_C, prod_eq_zero_iff, sub_eq_zero,
      not_disjoint_iff]
    constructor
    · rintro ⟨x, hx, y, hy, hxy⟩
      exact ⟨x, hx, (hc x (hAU i hx) y (hBU j hy) hxy) ▸ hy⟩
    · rintro ⟨x, hx, hxB⟩
      exact ⟨x, hx, x, hxB, rfl⟩
  let r : Fin m → (Sym (Fin (b + 1)) a → ℚ) := fun j s =>
    (s.1.map fun e : Fin (b + 1) => (g j).coeff (e : ℕ)).prod
  let toSym : (Fin a → Fin (b + 1)) → Sym (Fin (b + 1)) a := fun f =>
    ⟨univ.val.map f, by rw [Multiset.card_map, card_val, card_univ, Fintype.card_fin]⟩
  -- a linear relation among the `r j` gives the same relation among the values `Hⱼ(Aᵢ)`
  have key : ∀ lam : Fin m → ℚ, ∑ j, lam j • r j = 0 →
      ∀ i, ∑ j, lam j * ∏ x ∈ A i, (g j).eval (c x) = 0 := by
    intro lam hlam i
    let E := ((A i).equivFinOfCardEq (hA i)).symm
    have hprod : ∀ j, ∏ x ∈ A i, (g j).eval (c x) =
        ∑ f : Fin a → Fin (b + 1), r j (toSym f) * ∏ k, c (E k) ^ (f k : ℕ) := by
      intro j
      rw [← Finset.prod_coe_sort (A i), ← E.prod_comp]
      simp_rw [eval_eq_sum_range' (hdeg j), Finset.sum_range]
      rw [Fintype.prod_sum]
      refine sum_congr rfl fun f _ => ?_
      rw [prod_mul_distrib]
      congr 1
      simp only [r, toSym, Multiset.map_map, Function.comp_def]
      rfl
    simp_rw [hprod, mul_sum, ← mul_assoc]
    rw [sum_comm]
    refine sum_eq_zero fun f _ => ?_
    rw [← sum_mul]
    have := congrFun hlam (toSym f)
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this
    rw [this, zero_mul]
  have hli : LinearIndependent ℚ r := by
    rw [Fintype.linearIndependent_iff]
    intro lam hlam
    have hk := key lam hlam
    suffices ∀ n (hn : n < m), lam ⟨n, hn⟩ = 0 from fun i => this i.1 i.2
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro hn
      have h := hk ⟨n, hn⟩
      rw [Finset.sum_eq_single ⟨n, hn⟩] at h
      · rcases mul_eq_zero.1 h with h | h
        · exact h
        · exact absurd ((hH _ _).1 h) (not_not.2 (hAB _))
      · intro j _ hj
        rcases lt_or_gt_of_ne hj with hj | hj
        · rw [ih j.1 hj j.2, zero_mul]
        · rw [(hH _ _).2 (hcross _ _ hj), mul_zero]
      · intro h; exact absurd (mem_univ _) h
  have := hli.fintype_card_le_finrank
  rw [Module.finrank_fintype_fun_eq_card, Sym.card_sym_eq_choose, Fintype.card_fin,
    Fintype.card_fin] at this
  have e : b + 1 + a - 1 = a + b := by omega
  rwa [e] at this

/-! ### Pin's reduction and the cubic bound -/

section Pin

variable {α σ : Type*} [Fintype σ] [DecidableEq σ]

omit [Fintype σ] in
theorem image_evalFrom_append (M : DFA α σ) (T : Finset σ) (u v : List α) :
    T.image (fun q => M.evalFrom q (u ++ v)) =
      (T.image fun q => M.evalFrom q u).image fun q => M.evalFrom q v := by
  rw [image_image]
  congr 1
  funext q
  simp [DFA.evalFrom_of_append]

/-- **Pin's lemma**: in a synchronizing DFA with `n` states, every set `S` of `k ≥ 2` states is
shrunk by some word of length at most `(n - k + 2).choose 2`. -/
theorem exists_shrink (M : DFA α σ) (hM : M.IsSynchronizing) (S : Finset σ)
    (hS : 2 ≤ S.card) :
    ∃ w : List α, (S.image fun q => M.evalFrom q w).card < S.card ∧
      w.length ≤ (Fintype.card σ - S.card + 2).choose 2 := by
  classical
  have hex : ∃ ℓ, ∃ w : List α, w.length = ℓ ∧
      (S.image fun q => M.evalFrom q w).card < S.card := by
    obtain ⟨w, p, hp⟩ := hM
    refine ⟨w.length, w, rfl, ?_⟩
    have hsub : S.image (fun q => M.evalFrom q w) ⊆ {p} := by
      intro x hx
      obtain ⟨q, -, rfl⟩ := mem_image.1 hx
      simp [hp q]
    have := card_le_card hsub
    rw [card_singleton] at this
    omega
  -- a shortest shrinking word
  obtain ⟨w, hwl, hw⟩ := Nat.find_spec hex
  set ℓ := Nat.find hex
  have hmin : ∀ v : List α, v.length < ℓ →
      (S.image fun q => M.evalFrom q v).card = S.card := by
    intro v hv
    by_contra h
    have hlt : (S.image fun q => M.evalFrom q v).card < S.card :=
      lt_of_le_of_ne card_image_le h
    have := Nat.find_min' hex ⟨v, rfl, hlt⟩
    omega
  let T : Fin ℓ → Finset σ := fun i => S.image fun q => M.evalFrom q (w.take i)
  have hT : ∀ i : Fin ℓ, (T i).card = S.card := fun i =>
    hmin _ (by simp [hwl, i.isLt])
  have hTd : ∀ i : Fin ℓ,
      ((T i).image fun q => M.evalFrom q (w.drop i)).card < (T i).card := by
    intro i
    rw [hT, ← image_evalFrom_append, List.take_append_drop]
    exact hw
  have hpair : ∀ i : Fin ℓ, ∃ x ∈ T i, ∃ y ∈ T i, x ≠ y ∧
      M.evalFrom x (w.drop i) = M.evalFrom y (w.drop i) := fun i =>
    exists_ne_map_eq_of_card_lt_of_maps_to (hTd i) (fun x hx => mem_image_of_mem _ hx)
  choose x hx y hy hxy hfxy using hpair
  have hcross : ∀ I J : Fin ℓ, J < I → x I ∉ T J ∨ y I ∉ T J := by
    intro I J hJI
    by_contra hcon
    obtain ⟨hxJ, hyJ⟩ := not_or.1 hcon
    rw [not_not] at hxJ hyJ
    have hlen : (w.take J ++ w.drop I).length < ℓ := by
      simp only [List.length_append, List.length_take, List.length_drop, hwl]
      have := I.isLt
      have : (J : ℕ) < I := hJI
      omega
    have h1 := hmin _ hlen
    rw [image_evalFrom_append, ← hT J] at h1
    have hinj := card_image_iff.1 h1
    exact hxy I (hinj hxJ hyJ (hfxy I))
  have key := frankl_skew_bollobas (m := ℓ) (a := 2) (b := Fintype.card σ - S.card)
    (fun i => {x i.rev, y i.rev}) (fun i => univ \ T i.rev)
    (fun i => card_pair (hxy _))
    (fun i => by rw [card_univ_sdiff, hT])
    (fun i => by
      rw [disjoint_left]
      intro z hz
      simp only [mem_insert, mem_singleton] at hz
      rcases hz with rfl | rfl <;> simp [hx, hy])
    (fun i j hij => by
      rw [not_disjoint_iff]
      have hji : j.rev < i.rev := Fin.rev_lt_rev.2 hij
      rcases hcross _ _ hji with h | h
      · exact ⟨x i.rev, by simp, by simp [h]⟩
      · exact ⟨y i.rev, by simp, by simp [h]⟩)
  refine ⟨w, hw, ?_⟩
  rw [hwl]
  calc ℓ ≤ (2 + (Fintype.card σ - S.card)).choose 2 := key
    _ = (Fintype.card σ - S.card + 2).choose 2 := by rw [add_comm]

/-- Iterating Pin's lemma: a nonempty set of `k` states is collapsed to at most one state by a
word of length at most `(n + 1).choose 3 - (n - k + 2).choose 3`. -/
theorem exists_collapse (M : DFA α σ) (hM : M.IsSynchronizing) :
    ∀ S : Finset σ, S.Nonempty → ∃ w : List α, (S.image fun q => M.evalFrom q w).card ≤ 1 ∧
      w.length + (Fintype.card σ - S.card + 2).choose 3 ≤ (Fintype.card σ + 1).choose 3 := by
  intro S
  induction hk : S.card using Nat.strong_induction_on generalizing S with
  | _ k ih =>
    intro hne
    have hkn : k ≤ Fintype.card σ := hk ▸ card_le_univ S
    have hk1 : 1 ≤ k := hk ▸ hne.card_pos
    by_cases h2 : k ≤ 1
    · refine ⟨[], ?_, ?_⟩
      · simp only [DFA.evalFrom_nil, image_id']
        omega
      · simp only [List.length_nil, zero_add]
        exact Nat.choose_le_choose _ (by omega)
    · obtain ⟨w₁, hw₁, hl₁⟩ := exists_shrink M hM S (by omega)
      set S' := S.image fun q => M.evalFrom q w₁
      obtain ⟨w₂, hw₂, hl₂⟩ := ih S'.card (hk ▸ hw₁) S' rfl (hne.image _)
      refine ⟨w₁ ++ w₂, ?_, ?_⟩
      · rwa [image_evalFrom_append]
      · have hk' : S'.card + 1 ≤ k := hk ▸ hw₁
        have hc : (Fintype.card σ - k + 2 + 1).choose 3 =
            (Fintype.card σ - k + 2).choose 2 + (Fintype.card σ - k + 2).choose 3 :=
          Nat.choose_succ_succ' _ _
        have hmono : (Fintype.card σ - k + 2 + 1).choose 3 ≤
            (Fintype.card σ - S'.card + 2).choose 3 :=
          Nat.choose_le_choose _ (by omega)
        rw [List.length_append]
        rw [hk] at hl₁
        omega

end Pin

theorem six_mul_choose_three (n : ℕ) : 6 * (n + 1).choose 3 = n ^ 3 - n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Nat.choose_succ_succ', mul_add, ih, Nat.choose_two_right, Nat.add_sub_cancel]
    have h2 : 2 ∣ (n + 1) * n := by
      rcases Nat.even_or_odd n with ⟨t, rfl⟩ | ⟨t, rfl⟩
      · exact ⟨(t + t + 1) * t, by ring⟩
      · exact ⟨(t + 1) * (2 * t + 1), by ring⟩
    obtain ⟨t, ht⟩ := h2
    rw [ht, Nat.mul_div_cancel_left _ (by norm_num)]
    have hn3 : n ≤ n ^ 3 := by
      rcases n with _ | n
      · simp
      · exact Nat.le_self_pow (by norm_num) _
    have hn3' : n + 1 ≤ (n + 1) ^ 3 := Nat.le_self_pow (by norm_num) _
    zify [hn3, hn3']
    have : ((n + 1 : ℕ) : ℤ) * n = 2 * t := by exact_mod_cast ht
    push_cast at this ⊢
    nlinarith

/-- **Pin–Frankl bound** (Pin 1983, Frankl 1982): every synchronizing DFA with `n` states has a
synchronizing word `w` with `6 |w| ≤ n^3 - n`. -/
theorem pin_frankl_bound {α σ : Type*} [Fintype σ] (M : DFA α σ) (hM : M.IsSynchronizing) :
    ∃ w : List α, M.IsSynchronizingWord w ∧
      6 * w.length ≤ Fintype.card σ ^ 3 - Fintype.card σ := by
  classical
  obtain ⟨w0, p0, hp0⟩ := hM
  have hne : (univ : Finset σ).Nonempty := ⟨p0, mem_univ _⟩
  obtain ⟨w, hw, hl⟩ := exists_collapse M ⟨w0, p0, hp0⟩ univ hne
  refine ⟨w, ⟨M.evalFrom p0 w, fun q => ?_⟩, ?_⟩
  · exact card_le_one.1 hw _ (mem_image_of_mem _ (mem_univ q)) _
      (mem_image_of_mem _ (mem_univ p0))
  · rw [card_univ, Nat.sub_self, zero_add, Nat.choose_eq_zero_of_lt (by norm_num),
      add_zero] at hl
    rw [← six_mul_choose_three]
    omega

/-- **Pin–Frankl bound**, divided form: every synchronizing DFA with `n` states has a
synchronizing word of length at most `(n^3 - n) / 6`. -/
theorem pin_frankl_bound' {α σ : Type*} [Fintype σ] (M : DFA α σ) (hM : M.IsSynchronizing) :
    ∃ w : List α, M.IsSynchronizingWord w ∧
      w.length ≤ (Fintype.card σ ^ 3 - Fintype.card σ) / 6 := by
  obtain ⟨w, hw, hl⟩ := pin_frankl_bound M hM
  exact ⟨w, hw, (Nat.le_div_iff_mul_le (by norm_num)).2 (by rw [mul_comm]; exact hl)⟩

/-! ### Kari's theorem for Eulerian automata -/

section Kari

variable {α σ : Type*} [Fintype σ] [DecidableEq σ]

/-- The preimage `P.w⁻¹ = {q | q.w ∈ P}`. -/
def pre (M : DFA α σ) (P : Finset σ) (w : List α) : Finset σ :=
  univ.filter fun q => M.evalFrom q w ∈ P

theorem pre_nil (M : DFA α σ) (P : Finset σ) : pre M P [] = P := by
  ext q; rw [pre, Finset.mem_filter]; simp

theorem pre_cons (M : DFA α σ) (P : Finset σ) (b : α) (v : List α) :
    pre M P (b :: v) = univ.filter fun q => M.step q b ∈ pre M P v := by
  ext q; rw [pre, Finset.mem_filter, Finset.mem_filter, pre, Finset.mem_filter]; simp

variable [Fintype α]

/-- Kari's equation (1): `∑_{b ∈ Σ} |R.b⁻¹| = |R| · |Σ|` under the in-degree condition. -/
theorem sum_card_filter_step (M : DFA α σ)
    (hE : ∀ q : σ, Fintype.card {pa : σ × α // M.step pa.1 pa.2 = q} = Fintype.card α)
    (R : Finset σ) :
    ∑ b : α, (univ.filter fun q => M.step q b ∈ R).card = R.card * Fintype.card α := by
  have h1 : ∀ r, Fintype.card {pa : σ × α // M.step pa.1 pa.2 = r} =
      ∑ pa : σ × α, if M.step pa.1 pa.2 = r then 1 else 0 := by
    intro r
    rw [Fintype.card_subtype, card_filter]
  calc ∑ b : α, (univ.filter fun q => M.step q b ∈ R).card
      = ∑ b : α, ∑ q : σ, if M.step q b ∈ R then 1 else 0 := by
        simp only [card_filter]
    _ = ∑ pa : σ × α, if M.step pa.1 pa.2 ∈ R then 1 else 0 := by
        rw [Fintype.sum_prod_type, sum_comm]
    _ = ∑ pa : σ × α, ∑ r ∈ R, if M.step pa.1 pa.2 = r then 1 else 0 := by
        refine sum_congr rfl fun pa _ => ?_
        rw [sum_ite_eq]
    _ = ∑ r ∈ R, Fintype.card {pa : σ × α // M.step pa.1 pa.2 = r} := by
        rw [sum_comm]
        exact sum_congr rfl fun r _ => (h1 r).symm
    _ = R.card * Fintype.card α := by
        simp only [hE, sum_const, smul_eq_mul]

/-- If `|P.w⁻¹| ≠ |P|`, then some word `w'` with `|w'| ≤ |w|` has `|P.w'⁻¹| > |P|`. -/
theorem exists_pre_gt (M : DFA α σ)
    (hE : ∀ q : σ, Fintype.card {pa : σ × α // M.step pa.1 pa.2 = q} = Fintype.card α)
    (P : Finset σ) :
    ∀ w : List α, (pre M P w).card ≠ P.card →
      ∃ w' : List α, w'.length ≤ w.length ∧ P.card < (pre M P w').card := by
  intro w
  induction w with
  | nil => intro h; exact absurd (by rw [pre_nil]) h
  | cons a v ih =>
    intro h
    rcases lt_or_gt_of_ne h with hlt | hgt
    · by_cases hv : (pre M P v).card = P.card
      · by_contra hno
        have hle : ∀ b : α, (pre M P (b :: v)).card ≤ P.card := fun b =>
          not_lt.1 fun hb => hno ⟨b :: v, le_rfl, hb⟩
        have hsum := sum_card_filter_step M hE (pre M P v)
        simp only [← pre_cons, hv] at hsum
        have hlt' : ∑ b : α, (pre M P (b :: v)).card < ∑ _b : α, P.card :=
          sum_lt_sum (fun b _ => hle b) ⟨a, mem_univ _, hlt⟩
        rw [hsum, sum_const, card_univ, smul_eq_mul, mul_comm] at hlt'
        exact lt_irrefl _ hlt'
      · obtain ⟨w', hw', hgt'⟩ := ih hv
        exact ⟨w', by simp only [List.length_cons]; omega, hgt'⟩
    · exact ⟨a :: v, le_rfl, hgt⟩

omit [Fintype α] in
/-- Kari's Lemmas 3 and 4 (linear algebra part): in a synchronizing DFA with `n` states, every
set `P` with `0 < |P| < n` has `|P.w⁻¹| ≠ |P|` for some word `w` of length at most `n - 1`. -/
theorem exists_pre_ne (M : DFA α σ) (hM : M.IsSynchronizing) (P : Finset σ)
    (hP0 : 0 < P.card) (hP1 : P.card < Fintype.card σ) :
    ∃ w : List α, w.length ≤ Fintype.card σ - 1 ∧ (pre M P w).card ≠ P.card := by
  classical
  by_contra H
  simp only [not_exists, not_and, not_not] at H
  set n := Fintype.card σ with hn
  -- `T w` is the linear map `g ↦ (q ↦ g (q.w))`
  let T : List α → (σ → ℚ) →ₗ[ℚ] (σ → ℚ) := fun w =>
    LinearMap.funLeft ℚ ℚ (fun q => M.evalFrom q w)
  let x : σ → ℚ := fun q => (if q ∈ P then (n : ℚ) else 0) - P.card
  let wt : (σ → ℚ) →ₗ[ℚ] ℚ := ∑ q, LinearMap.proj q
  have hwt : ∀ g : σ → ℚ, wt g = ∑ q, g q := by
    intro g; simp [wt]
  have hwtT : ∀ w, wt (T w x) = n * (((pre M P w).card : ℚ) - P.card) := by
    intro w
    rw [hwt]
    simp only [T, x, LinearMap.funLeft_apply, sum_sub_distrib, sum_const, card_univ,
      nsmul_eq_mul, ← hn]
    rw [← sum_filter, sum_const, nsmul_eq_mul]
    simp only [pre]
    ring
  let K := LinearMap.ker wt
  have hK : Module.finrank ℚ K < n := by
    have hne : K ≠ ⊤ := by
      intro h
      have : (fun _ : σ => (1 : ℚ)) ∈ K := h ▸ Submodule.mem_top
      rw [LinearMap.mem_ker, hwt] at this
      simp only [sum_const, card_univ, nsmul_eq_mul, mul_one, Nat.cast_eq_zero, ← hn] at this
      omega
    have := Submodule.finrank_lt hne
    rwa [Module.finrank_fintype_fun_eq_card] at this
  -- the Krylov-type chain `V₀ ≤ V₁ ≤ ⋯`
  let Vs : ℕ → Submodule ℚ (σ → ℚ) := fun i =>
    Submodule.span ℚ {g | ∃ w : List α, w.length ≤ i ∧ T w x = g}
  have hmono : ∀ i j, i ≤ j → Vs i ≤ Vs j := by
    intro i j hij
    exact Submodule.span_mono fun g ⟨w, hw, hg⟩ => ⟨w, hw.trans hij, hg⟩
  have hmem : ∀ w : List α, T w x ∈ Vs w.length := fun w =>
    Submodule.subset_span ⟨w, le_rfl, rfl⟩
  have hTcons : ∀ a v g, T (a :: v) g = T [a] (T v g) := fun _ _ _ => rfl
  have hstep : ∀ i a, ∀ g ∈ Vs i, T [a] g ∈ Vs (i + 1) := by
    intro i a g hg
    have : (Vs i).map (T [a]) ≤ Vs (i + 1) := by
      rw [Submodule.map_span_le]
      rintro _ ⟨v, hv, rfl⟩
      rw [← hTcons]
      exact Submodule.subset_span ⟨a :: v, by simp only [List.length_cons]; omega, rfl⟩
    exact this ⟨g, hg, rfl⟩
  have hstable : ∀ i, Vs i = Vs (i + 1) → Vs (i + 1) = Vs (i + 2) := by
    intro i hi
    refine le_antisymm (hmono _ _ (by omega)) (Submodule.span_le.2 ?_)
    rintro _ ⟨w, hw, rfl⟩
    cases w with
    | nil => exact hmono 0 _ (by omega) (hmem [])
    | cons a v =>
      rw [hTcons]
      have hv : T v x ∈ Vs i := by
        rw [hi]
        exact hmono _ _ (by simp only [List.length_cons] at hw; omega) (hmem v)
      exact hstep i a _ hv
  have hstable' : ∀ i, Vs i = Vs (i + 1) → ∀ j, Vs (i + j) = Vs i := by
    intro i hi
    have h1 : ∀ j, Vs (i + j) = Vs (i + j + 1) := by
      intro j
      induction j with
      | zero => exact hi
      | succ j ih => exact hstable _ ih
    intro j
    induction j with
    | zero => rfl
    | succ j ih => rw [← ih, ← add_assoc]; exact (h1 j).symm
  have hVK : Vs (n - 1) ≤ K := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨w, hw, rfl⟩
    show T w x ∈ LinearMap.ker wt
    rw [LinearMap.mem_ker, hwtT, H w hw, sub_self, mul_zero]
  have hx0 : x ≠ 0 := by
    obtain ⟨p, hp⟩ := card_pos.1 hP0
    intro h
    have := congrFun h p
    simp only [x, hp, ite_true, Pi.zero_apply, sub_eq_zero, Nat.cast_inj] at this
    omega
  have hex : ∃ i, i < n - 1 ∧ Vs i = Vs (i + 1) := by
    by_contra hno
    simp only [not_exists, not_and] at hno
    have hrank : ∀ i, i ≤ n - 1 → i + 1 ≤ Module.finrank ℚ (Vs i) := by
      intro i
      induction i with
      | zero =>
        intro _
        rw [zero_add, Nat.one_le_iff_ne_zero]
        intro h0
        rw [Submodule.finrank_eq_zero] at h0
        have : x ∈ Vs 0 := hmem []
        rw [h0, Submodule.mem_bot] at this
        exact hx0 this
      | succ i ih =>
        intro hi
        have hlt : Vs i < Vs (i + 1) :=
          lt_of_le_of_ne (hmono _ _ (by omega)) (hno i (by omega))
        have := Submodule.finrank_lt_finrank_of_lt hlt
        have := ih (by omega)
        omega
    have h1 := hrank (n - 1) le_rfl
    have h2 := Submodule.finrank_mono hVK
    omega
  obtain ⟨i, hi, hVi⟩ := hex
  obtain ⟨w0, p0, hp0⟩ := hM
  have hw0 : T w0 x ∈ K := by
    apply hVK
    by_cases hl : w0.length ≤ n - 1
    · exact hmono _ _ hl (hmem w0)
    · have := hstable' i hVi (w0.length - i)
      rw [Nat.add_sub_cancel' (by omega)] at this
      have hm := hmem w0
      rw [this] at hm
      exact hmono i (n - 1) (by omega) hm
  rw [LinearMap.mem_ker, hwtT, mul_eq_zero, sub_eq_zero, Nat.cast_eq_zero, Nat.cast_inj] at hw0
  have hpre : pre M P w0 = if p0 ∈ P then univ else ∅ := by
    ext q
    split_ifs with h <;> simp [pre, hp0, h]
  rcases hw0 with h | h
  · omega
  · rw [hpre] at h
    split_ifs at h
    · rw [card_univ] at h; omega
    · rw [card_empty] at h; omega

/-- Kari's extension step: every nonempty set `P` of states is the image of all states under some
word of length at most `(n - |P|)(n - 1)`. -/
theorem exists_pre_univ (M : DFA α σ)
    (hE : ∀ q : σ, Fintype.card {pa : σ × α // M.step pa.1 pa.2 = q} = Fintype.card α)
    (hM : M.IsSynchronizing) :
    ∀ P : Finset σ, P.Nonempty → ∃ w : List α, (∀ q, M.evalFrom q w ∈ P) ∧
      w.length ≤ (Fintype.card σ - P.card) * (Fintype.card σ - 1) := by
  intro P
  induction hd : Fintype.card σ - P.card using Nat.strong_induction_on generalizing P with
  | _ d ih =>
    intro hne
    by_cases hfull : P.card = Fintype.card σ
    · refine ⟨[], fun q => ?_, by simp⟩
      rw [DFA.evalFrom_nil, eq_univ_of_card P hfull]
      exact mem_univ q
    · have hlt : P.card < Fintype.card σ := lt_of_le_of_ne (card_le_univ P) hfull
      obtain ⟨v, hvl, hv⟩ := exists_pre_ne M hM P hne.card_pos hlt
      obtain ⟨v', hv'l, hv'⟩ := exists_pre_gt M hE P v hv
      have hne' : (pre M P v').Nonempty := card_pos.1 (lt_of_le_of_lt (Nat.zero_le _) hv')
      have hle' := card_le_univ (pre M P v')
      obtain ⟨u, hu, hul⟩ := ih (Fintype.card σ - (pre M P v').card) (by omega) _ rfl hne'
      refine ⟨u ++ v', fun q => ?_, ?_⟩
      · have := hu q
        rw [pre, Finset.mem_filter] at this
        rw [DFA.evalFrom_of_append]
        exact this.2
      · rw [List.length_append]
        have h1 : Fintype.card σ - (pre M P v').card + 1 ≤ d := by omega
        calc u.length + v'.length
            ≤ (Fintype.card σ - (pre M P v').card) * (Fintype.card σ - 1) +
                (Fintype.card σ - 1) := by omega
          _ = (Fintype.card σ - (pre M P v').card + 1) * (Fintype.card σ - 1) := by ring
          _ ≤ d * (Fintype.card σ - 1) := Nat.mul_le_mul_right _ h1

end Kari

/-- **Kari (2003), Theorem 2**: let `M` be a synchronizing DFA with `n` states over a finite
alphabet `Σ` whose underlying digraph is Eulerian, i.e. every state `q` has exactly `|Σ|` incoming
transitions `(p, a)` with `p.a = q`. Then `M` has a synchronizing word of length at most
`(n - 2)(n - 1) + 1 = n^2 - 3n + 3`, and in particular at most `(n - 1)^2`. -/
theorem kari_eulerian_bound {α σ : Type*} [Fintype α] [Fintype σ] [DecidableEq σ]
    (M : DFA α σ)
    (hE : ∀ q : σ, Fintype.card {pa : σ × α // M.step pa.1 pa.2 = q} = Fintype.card α)
    (hM : M.IsSynchronizing) :
    ∃ w : List α, M.IsSynchronizingWord w ∧
      w.length ≤ (Fintype.card σ - 2) * (Fintype.card σ - 1) + 1 ∧
      w.length ≤ (Fintype.card σ - 1) ^ 2 := by
  obtain ⟨w0, p0, hp0⟩ := hM
  by_cases hn : Fintype.card σ ≤ 1
  · refine ⟨[], ⟨p0, fun q => ?_⟩, by simp, by simp⟩
    exact Fintype.card_le_one_iff.1 hn q p0
  · -- some letter merges two states
    have hna : ∃ a : α, ∃ q₁ q₂ : σ, q₁ ≠ q₂ ∧ M.step q₁ a = M.step q₂ a := by
      by_contra hno
      simp only [not_exists, not_and] at hno
      have hinj : ∀ w : List α, Function.Injective fun q => M.evalFrom q w := by
        intro w
        induction w with
        | nil => exact fun q₁ q₂ h => h
        | cons a v ih =>
          intro q₁ q₂ h
          by_contra hne
          exact hno a q₁ q₂ hne (ih h)
      have : ∀ q₁ q₂ : σ, q₁ = q₂ := fun q₁ q₂ =>
        hinj w0 ((hp0 q₁).trans (hp0 q₂).symm)
      exact hn (Fintype.card_le_one_iff.2 this)
    obtain ⟨a, q₁, q₂, hq, hstep⟩ := hna
    set P : Finset σ := univ.filter fun q => M.step q a = M.step q₁ a with hP
    have hP2 : 2 ≤ P.card := by
      have hsub : ({q₁, q₂} : Finset σ) ⊆ P := by
        intro q hq'
        simp only [mem_insert, mem_singleton] at hq'
        rw [hP, Finset.mem_filter]
        rcases hq' with rfl | rfl
        · exact ⟨mem_univ _, rfl⟩
        · exact ⟨mem_univ _, hstep.symm⟩
      have := card_le_card hsub
      rwa [card_pair hq] at this
    obtain ⟨u, hu, hul⟩ := exists_pre_univ M hE ⟨w0, p0, hp0⟩ P (card_pos.1 (by omega))
    have hul' : u.length ≤ (Fintype.card σ - 2) * (Fintype.card σ - 1) :=
      hul.trans (Nat.mul_le_mul_right _ (by omega))
    refine ⟨u ++ [a], ⟨M.step q₁ a, fun q => ?_⟩, ?_, ?_⟩
    · have := hu q
      rw [hP, Finset.mem_filter] at this
      rw [DFA.evalFrom_append_singleton]
      exact this.2
    · rw [List.length_append, List.length_singleton]
      omega
    · rw [List.length_append, List.length_singleton]
      have : (Fintype.card σ - 1) ^ 2 = (Fintype.card σ - 2) * (Fintype.card σ - 1) +
          (Fintype.card σ - 1) := by
        have e : Fintype.card σ - 1 = (Fintype.card σ - 2) + 1 := by omega
        rw [e]
        ring
      omega

/-- The Černý conjecture holds for Eulerian automata (Kari 2003), in the shape of
`cerny_conjecture` from formal-conjectures. -/
theorem cerny_conjecture_eulerian {α σ : Type*} [Fintype α] [Fintype σ] [DecidableEq σ]
    (M : DFA α σ)
    (hE : ∀ q : σ, Fintype.card {pa : σ × α // M.step pa.1 pa.2 = q} = Fintype.card α)
    (hM : M.IsSynchronizing) :
    ∃ w : List α, M.IsSynchronizingWord w ∧ w.length ≤ (Fintype.card σ - 1) ^ 2 := by
  obtain ⟨w, hw, -, h⟩ := kari_eulerian_bound M hE hM
  exact ⟨w, hw, h⟩

/-! ### Sanity checks: the hypotheses can hold and can fail -/

/-- A two-state automaton over `Bool`: the letter `false` sends every state to `0` and the letter
`true` sends every state to `1`. -/
def exampleDFA : DFA Bool (Fin 2) where
  step _ b := if b then 1 else 0
  start := 0
  accept := ∅

/-- `exampleDFA` is synchronizing (by the word `[false]`). -/
example : exampleDFA.IsSynchronizing := ⟨[false], 0, by decide⟩

/-- `exampleDFA` satisfies Kari's in-degree (Eulerian) condition. -/
example : ∀ q : Fin 2,
    Fintype.card {pa : Fin 2 × Bool // exampleDFA.step pa.1 pa.2 = q} = Fintype.card Bool := by
  decide

/-- The identity automaton on two states is not synchronizing. -/
example : ¬ (DFA.mk (fun q (_ : Unit) => q) (0 : Fin 2) ∅).IsSynchronizing := by
  have h : ∀ (w : List Unit) (q : Fin 2),
      (DFA.mk (fun q (_ : Unit) => q) (0 : Fin 2) ∅).evalFrom q w = q := by
    intro w q
    induction w generalizing q with
    | nil => rfl
    | cons a v ih => exact ih q
  rintro ⟨w, p, hp⟩
  have := (h w 0).symm.trans ((hp 0).trans ((hp 1).symm.trans (h w 1)))
  exact absurd this (by decide)

end CernyConjecture
