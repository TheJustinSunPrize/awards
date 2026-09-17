import Mathlib

/-!
# Erdős Problem 1158: Erdős's 1964 bounds for `ex_t(n, K_t(r))`

Erdős Problem 1158 (https://www.erdosproblems.com/1158) reads:

> Let `K_t(r)` be the complete `t`-partite `t`-uniform hypergraph with `r` vertices in each
> class. Is it true that `ex_t(n, K_t(r)) ≥ n^{t - r^{1-t} - o(1)}` for all `t, r`?

The page records that Erdős [Er64f] proved `n^{t - O(r^{1-t})} ≤ ex_t(n, K_t(r)) ≪ n^{t - r^{1-t}}`.
The question itself is open (the page says it is known only for `t = 2`, `2 ≤ r ≤ 3`). This file
formalizes the two bounds credited to [Er64f]. It does **not** prove the conjectured lower bound.

## Statements proved

* `erdos_1158_upper` (`t ≥ 1`, `r ≥ 1`): there is `C > 0` such that for every `n`, every
  `t`-uniform hypergraph `E` on `Fin n` without a copy of `K_t(r)` has `|E| ≤ C n^{t - r^{1-t}}`.
  `erdos_1158_upper_explicit` gives the constant `C = boxConst r (t - 1)`.
* `erdos_1158_lower_explicit` (`t ≥ 1`, `r ≥ 2`, `n ≥ 2t`): there is a `K_t(r)`-free `t`-uniform
  `E` on `Fin n` with `|E| ≥ n^{t - t(r-1)/(r^t-1)} / (4 r^t (2^t t!)²)`.
* `erdos_1158_lower` (`t ≥ 1`, `r ≥ 2`): there is `c > 0` such that for all `n ≥ 2t` some such `E`
  has `|E| ≥ c n^{t - t r^{1-t}}`. This is the `n^{t - O(r^{1-t})}` bound, with implied constant
  `t`; `deletion_exponent_le` shows `t(r-1)/(r^t-1) ≤ t r^{1-t}`.
* `erdos_1158_lower_eventually`: for every `ε > 0` and all large `n` some such `E` has
  `|E| ≥ n^{t - t(r-1)/(r^t-1) - ε}`.
* `erdos_1158` (`t ≥ 1`, `r ≥ 2`): both bounds for the extremal number `ex t r n`.

## Definitions and faithfulness

* `Uniform` and `ContainsKt` are copied verbatim from the statement-only file
  `Statements/Erdos1158KtrHypergraphLowerBound.lean` of `WoshuaJolk/jig-verifier` (Apache-2.0).
  `ContainsKt E t r` says that there are `t` pairwise disjoint `r`-sets such that every
  transversal `{c 0, …, c (t-1)}` (with `c i` in the `i`-th set) is an edge of `E`, i.e. `E` has a
  (not necessarily induced) copy of `K_t(r)`. That file states the open question, with exponent
  `t - r^{1-t} - ε`. `erdos_1158_lower_eventually` has the same shape with the weaker exponent
  `t - t(r-1)/(r^t-1) - ε` (for `t = r = 2`: `4/3` instead of `3/2`).
* `ex t r n` is the `sup` of `|E|` over the `K_t(r)`-free `E ⊆ powersetCard t univ`.
  `card_le_ex` and `exists_card_eq_ex` show that it is the maximum.
* formal-conjectures has no file for this problem, so there is no statement to reuse.
* Both main bounds are universally quantified over `E`, resp. produce an `E`, with the same
  `Uniform`/`ContainsKt`; neither can hold for a degenerate reason: if `ContainsKt` were never
  true the proved upper bound would fail for the complete `t`-uniform hypergraph, and if it were
  always true the proved lower bound would be impossible.
* Comparison with Theorem 1 of [Er64f] (p. 185). With Erdős's letters (`r` the uniformity, `l`
  the class size, `f = ex + 1`) it reads: for `l > 1`, `n > n₀(r, l)` and a large constant `C`
  independent of `n, r, l`, `n^{r - C/l^{r-1}} < f(n; K^{(r)}(l, …, l)) ≤ n^{r - 1/l^{r-1}}`.
  - Upper bound: Erdős has constant `1` for `n > n₀`. We prove the `≪` form recorded on the
    problem page, with an explicit constant, for every `n`.
  - Lower bound: Erdős does not write out a proof ("uses the same methods combined with the
    methods of [ER60]"). We prove it with `C = t`, via the first-moment deletion method. A
    constant independent of the uniformity `t` is **not** claimed here.

## Proof

*Upper bound* (Erdős's induction on the uniformity, in the "box" form):

1. `orderedEdges E` is the set of injective `t`-tuples whose entries form an edge.
   `|E| ≤ |orderedEdges E|`, and if `E` is `K_t(r)`-free then `orderedEdges E` contains no box
   `A_1 × ⋯ × A_t` with all `|A_i| = r` (`not_hasBox_orderedEdges`: injectivity of the tuples
   forces the `A_i` to be pairwise disjoint).
2. `box_bound`: a box-free `S ⊆ (Fin n)^{t+1}` has `|S|^{r^t} · n ≤ boxConst r t · n^{(t+1) r^t}`.
   With one coordinate, `|S| < r`. In the step (`box_step`) let `d(x)` be the number of `v` with
   `(v, x) ∈ S`. For each `r`-set `B`, the `x` with `B × {x} ⊆ S` form a box-free set, bounded by
   the induction hypothesis. Double counting gives `∑_x C(d(x), r) = ∑_B #{x | B × {x} ⊆ S}`.
   Together with `d^r ≤ r^r r! (C(d, r) + 1)` and the power-mean inequality
   `(∑_x d(x))^r ≤ (n^{t+1})^{r-1} ∑_x d(x)^r`, this gives the bound one dimension up.
3. `erdos_1158_upper_explicit`: taking `r^{t-1}`-th roots gives `|E| ≤ C n^{t - r^{1-t}}`.

*Lower bound* (deletion):

1. Give each set `H` of `t`-subsets of `Fin n` the weight `p^{|H|} (1-p)^{N-|H|}`, where
   `N = C(n, t)`. The weighted mean of `|H| - r^t · #(copies of K_t(r) inside H)` equals
   `pN - r^t p^{r^t} · #copies`, and `#copies ≤ n^{rt}` (`card_copies_le`).
2. Deleting every edge of every copy inside a good `H` leaves a `K_t(r)`-free `t`-uniform
   hypergraph (`exists_free_of_weight`).
3. Take `p = c n^{-β}` with `β = t(r-1)/(r^t-1)` and `c = 1/(2 r^t 2^t t!)`. The exponents match
   (`rt - β r^t = t - β`), and the result has at least `n^{t-β} / (4 r^t (2^t t!)²)` edges.

The weights section repeats the one in our formalization of Erdős Problem 1178. The bounds are
due to Erdős [Er64f]; the case `t = 2` of the upper bound is due to Kővári, Sós and Turán [KST54].
The Lean formalization was written with AI assistance (Claude, Anthropic).

## References

* [Er64f] P. Erdős, _On extremal problems of graphs and generalized graphs_, Israel J. Math. 2
  (1964), 183–190.
* [ER60] P. Erdős and A. Rényi, _On the evolution of random graphs_, Publ. Math. Inst. Hung.
  Acad. Sci. 5 (1960), 17–61.
* [KST54] T. Kővári, V. T. Sós and P. Turán, _On a problem of K. Zarankiewicz_, Colloq. Math. 3
  (1954), 50–57.
* [erdosproblems.com/1158](https://www.erdosproblems.com/1158)
-/

open Finset Filter

namespace Erdos1158

section Problem

/-- `E` is `t`-uniform: every edge has exactly `t` vertices. -/
def Uniform {n : ℕ} (E : Finset (Finset (Fin n))) (t : ℕ) : Prop :=
  ∀ e ∈ E, e.card = t

/-- `E` contains a copy of `K_t(r)`: `t` pairwise disjoint `r`-sets all of whose transversals
are edges of `E`. -/
def ContainsKt {n : ℕ} (E : Finset (Finset (Fin n)))
    (t r : ℕ) : Prop :=
  ∃ parts : Fin t → Finset (Fin n),
    (∀ i, (parts i).card = r) ∧
    (∀ i j, i ≠ j → Disjoint (parts i) (parts j)) ∧
    ∀ choice : Fin t → Fin n,
      (∀ i, choice i ∈ parts i) →
      (Finset.univ.image choice : Finset (Fin n)) ∈ E

open Classical in
/-- `ex t r n = ex_t(n, K_t(r))`: the largest number of edges of a `t`-uniform hypergraph on
`Fin n` that contains no copy of `K_t(r)`. -/
noncomputable def ex (t r n : ℕ) : ℕ :=
  ((powersetCard t (univ : Finset (Fin n))).powerset.filter fun E => ¬ ContainsKt E t r).sup card

theorem card_le_ex {t r n : ℕ} {E : Finset (Finset (Fin n))} (hE : Uniform E t)
    (hK : ¬ ContainsKt E t r) : #E ≤ ex t r n := by
  classical
  unfold ex
  exact le_sup (f := card) (mem_filter.2
    ⟨mem_powerset.2 fun e he => mem_powersetCard.2 ⟨subset_univ _, hE e he⟩, hK⟩)

theorem exists_card_eq_ex (t r n : ℕ) (hr : 1 ≤ r) :
    ∃ E : Finset (Finset (Fin n)), Uniform E t ∧ ¬ ContainsKt E t r ∧ #E = ex t r n := by
  classical
  have hfree : ¬ ContainsKt (∅ : Finset (Finset (Fin n))) t r := by
    rintro ⟨A, hA, -, hsub⟩
    have hne : ∀ i, (A i).Nonempty := fun i => card_pos.1 (by rw [hA i]; omega)
    choose c hc using hne
    exact notMem_empty _ (hsub c hc)
  obtain ⟨E, hE, hEq⟩ := exists_mem_eq_sup
    ((powersetCard t (univ : Finset (Fin n))).powerset.filter fun E => ¬ ContainsKt E t r)
    ⟨∅, mem_filter.2 ⟨empty_mem_powerset _, hfree⟩⟩ card
  obtain ⟨hE1, hE2⟩ := mem_filter.1 hE
  refine ⟨E, fun e he => (mem_powersetCard.1 (mem_powerset.1 hE1 he)).2, hE2, ?_⟩
  unfold ex
  convert hEq.symm

end Problem

section Box

/-- A set `S` of `d`-tuples contains an `r × ⋯ × r` box `A 0 × ⋯ × A (d-1)`. -/
def HasBox {d n : ℕ} (S : Finset (Fin d → Fin n)) (r : ℕ) : Prop :=
  ∃ A : Fin d → Finset (Fin n), (∀ i, #(A i) = r) ∧
    ∀ y : Fin d → Fin n, (∀ i, y i ∈ A i) → y ∈ S

/-- The constant of the box bound `box_bound`. -/
def boxConst (r : ℕ) : ℕ → ℕ
  | 0 => r
  | t + 1 => (r ^ r * r.factorial) ^ (r ^ t) * 2 ^ (r ^ t) * (boxConst r t + 1)

theorem one_le_boxConst {r : ℕ} (hr : 1 ≤ r) : ∀ t, 1 ≤ boxConst r t
  | 0 => hr
  | t + 1 => by
    simp only [boxConst]
    have h1 : 1 ≤ (r ^ r * r.factorial) ^ (r ^ t) :=
      Nat.one_le_pow _ _ (Nat.mul_pos (by positivity) (Nat.factorial_pos r))
    have h2 : 1 ≤ 2 ^ (r ^ t) := Nat.one_le_two_pow
    calc 1 = 1 * 1 * 1 := rfl
      _ ≤ _ := Nat.mul_le_mul (Nat.mul_le_mul h1 h2) (by omega)

/-- `d^r ≤ r^r r! (C(d, r) + 1)`. -/
theorem pow_le_choose_mul {r : ℕ} (hr : 1 ≤ r) (d : ℕ) :
    d ^ r ≤ r ^ r * r.factorial * (d.choose r + 1) := by
  rcases lt_or_ge d r with h | h
  · calc d ^ r ≤ r ^ r := Nat.pow_le_pow_left h.le r
      _ = r ^ r * 1 * 1 := by ring
      _ ≤ r ^ r * r.factorial * (d.choose r + 1) :=
          Nat.mul_le_mul (Nat.mul_le_mul_left _ (Nat.factorial_pos r)) (by omega)
  · have h1 : d ≤ r * (d + 1 - r) := by
      obtain ⟨e, rfl⟩ := Nat.exists_eq_add_of_le h
      rw [show r + e + 1 - r = e + 1 by omega]
      nlinarith
    calc d ^ r ≤ (r * (d + 1 - r)) ^ r := Nat.pow_le_pow_left h1 r
      _ = r ^ r * (d + 1 - r) ^ r := mul_pow _ _ _
      _ ≤ r ^ r * d.descFactorial r := Nat.mul_le_mul_left _ (Nat.pow_sub_le_descFactorial d r)
      _ = r ^ r * r.factorial * d.choose r := by
          rw [Nat.descFactorial_eq_factorial_mul_choose, mul_assoc]
      _ ≤ _ := Nat.mul_le_mul_left _ (Nat.le_succ _)

/-- If `a_B^m n ≤ Q` for all `B ∈ T`, then `(∑_B a_B)^m n ≤ |T|^m Q`. -/
theorem sum_pow_mul_le {α : Type*} (T : Finset α) (a : α → ℕ) {m : ℕ} (hm : m ≠ 0)
    (n Q : ℕ) (h : ∀ B ∈ T, a B ^ m * n ≤ Q) : (∑ B ∈ T, a B) ^ m * n ≤ #T ^ m * Q := by
  rcases T.eq_empty_or_nonempty with rfl | hT
  · simp [zero_pow hm]
  obtain ⟨B₀, hB₀, hmax⟩ := T.exists_max_image a hT
  have hsum : ∑ B ∈ T, a B ≤ #T * a B₀ := by
    simpa using Finset.sum_le_card_nsmul T a (a B₀) hmax
  calc (∑ B ∈ T, a B) ^ m * n ≤ (#T * a B₀) ^ m * n := by gcongr
    _ = #T ^ m * (a B₀ ^ m * n) := by rw [mul_pow, mul_assoc]
    _ ≤ #T ^ m * Q := Nat.mul_le_mul_left _ (h B₀ hB₀)

/-- A box-free set of `1`-tuples has fewer than `r` elements. -/
theorem card_lt_of_not_hasBox {n r : ℕ} (S : Finset (Fin 1 → Fin n)) (hS : ¬ HasBox S r) :
    #S < r := by
  by_contra hlt
  rw [not_lt] at hlt
  obtain ⟨T, hTS, hT⟩ := exists_subset_card_eq hlt
  have hinj : Function.Injective fun y : Fin 1 → Fin n => y 0 := by
    intro y z h
    funext i
    rw [Fin.fin_one_eq_zero i]
    exact h
  apply hS
  refine ⟨fun _ => T.image fun y => y 0, fun i => ?_, fun y hy => ?_⟩
  · rw [card_image_of_injective _ hinj, hT]
  · obtain ⟨z, hz, hzy⟩ := mem_image.1 (hy 0)
    have : z = y := hinj hzy
    exact hTS (this ▸ hz)

/-- The induction step of the box bound. -/
theorem box_step {r : ℕ} (hr : 1 ≤ r) (t : ℕ)
    (ih : ∀ n (S : Finset (Fin (t + 1) → Fin n)), ¬ HasBox S r →
      #S ^ (r ^ t) * n ≤ boxConst r t * n ^ ((t + 1) * r ^ t))
    (n : ℕ) (S : Finset (Fin (t + 2) → Fin n)) (hS : ¬ HasBox S r) :
    #S ^ (r ^ (t + 1)) * n ≤ boxConst r (t + 1) * n ^ ((t + 2) * r ^ (t + 1)) := by
  obtain ⟨k, rfl⟩ : ∃ k, r = k + 1 := ⟨r - 1, by omega⟩
  have hm0 : (k + 1) ^ t ≠ 0 := by positivity
  -- the link of a tuple `x` of the last `t + 1` coordinates
  let N : (Fin (t + 1) → Fin n) → Finset (Fin n) := fun x =>
    univ.filter fun v => (Fin.cons v x : Fin (t + 2) → Fin n) ∈ S
  have h1 : #S = ∑ x, #(N x) := by
    rw [card_eq_sum_card_fiberwise (f := Fin.tail) (t := univ) (fun _ _ => mem_univ _)]
    refine sum_congr rfl fun x _ => ?_
    refine card_bij' (fun y _ => y 0) (fun v _ => Fin.cons v x) ?_ ?_ ?_ ?_
    · intro y hy
      rw [mem_filter] at hy
      simp only [N, mem_filter, mem_univ, true_and]
      rw [← hy.2, Fin.cons_self_tail]
      exact hy.1
    · intro v hv
      simp only [N, mem_filter, mem_univ, true_and] at hv
      rw [mem_filter]
      exact ⟨hv, Fin.tail_cons _ _⟩
    · intro y hy
      rw [mem_filter] at hy
      rw [← hy.2, Fin.cons_self_tail]
    · intro v _
      simp
  set T := powersetCard (k + 1) (univ : Finset (Fin n)) with hT
  let a : Finset (Fin n) → ℕ := fun B => #(univ.filter fun x => B ⊆ N x)
  have h2 : ∑ x, (#(N x)).choose (k + 1) = ∑ B ∈ T, a B := by
    have := sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
      (s := (univ : Finset (Fin (t + 1) → Fin n))) (t := T) (r := fun x B => B ⊆ N x)
    refine (sum_congr rfl fun x _ => ?_).trans (this.trans rfl)
    rw [← card_powersetCard]
    congr 1
    ext B
    simp [bipartiteAbove, hT, mem_powersetCard, and_comm]
  have h3 : ∀ B ∈ T, a B ^ (k + 1) ^ t * n ≤ boxConst (k + 1) t * n ^ ((t + 1) * (k + 1) ^ t) := by
    intro B hB
    apply ih
    rintro ⟨A, hA, hAS⟩
    apply hS
    have hcard : ∀ i, #((Fin.cons B A : Fin (t + 2) → Finset (Fin n)) i) = k + 1 := by
      intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · simpa using (mem_powersetCard.1 hB).2
      · simpa using hA j
    refine ⟨Fin.cons B A, hcard, fun y hy => ?_⟩
    · have hx : Fin.tail y ∈ univ.filter fun x => B ⊆ N x :=
        hAS _ fun i => by simpa [Fin.tail] using hy i.succ
      have h0 : y 0 ∈ B := by simpa using hy 0
      have := (mem_filter.1 hx).2 h0
      simp only [N, mem_filter, mem_univ, true_and, Fin.cons_self_tail] at this
      exact this
  set P := ∑ B ∈ T, a B with hP
  have h4 : P ^ (k + 1) ^ t * n ≤
      n ^ ((k + 1) * (k + 1) ^ t) * (boxConst (k + 1) t * n ^ ((t + 1) * (k + 1) ^ t)) := by
    calc P ^ (k + 1) ^ t * n
        ≤ #T ^ (k + 1) ^ t * (boxConst (k + 1) t * n ^ ((t + 1) * (k + 1) ^ t)) :=
          sum_pow_mul_le T a hm0 n _ h3
      _ ≤ (n ^ (k + 1)) ^ (k + 1) ^ t * (boxConst (k + 1) t * n ^ ((t + 1) * (k + 1) ^ t)) := by
          refine Nat.mul_le_mul_right _ (Nat.pow_le_pow_left ?_ _)
          rw [hT, card_powersetCard, card_univ, Fintype.card_fin]
          exact Nat.choose_le_pow n (k + 1)
      _ = _ := by rw [← pow_mul]
  have h5 : ∑ x, #(N x) ^ (k + 1) ≤ (k + 1) ^ (k + 1) * (k + 1).factorial * (P + n ^ (t + 1)) := by
    calc ∑ x, #(N x) ^ (k + 1)
        ≤ ∑ x, (k + 1) ^ (k + 1) * (k + 1).factorial * ((#(N x)).choose (k + 1) + 1) :=
          sum_le_sum fun x _ => pow_le_choose_mul hr _
      _ = (k + 1) ^ (k + 1) * (k + 1).factorial * (P + n ^ (t + 1)) := by
          rw [← mul_sum, sum_add_distrib, h2]
          simp
  have h6 : #S ^ (k + 1) ≤ (n ^ (t + 1)) ^ k * ∑ x, #(N x) ^ (k + 1) := by
    rw [h1]
    simpa using pow_sum_le_card_mul_sum_pow (s := (univ : Finset (Fin (t + 1) → Fin n)))
      (f := fun x => #(N x)) (fun _ _ => Nat.zero_le _) k
  have h7 : (P ^ (k + 1) ^ t + (n ^ (t + 1)) ^ (k + 1) ^ t) * n ≤
      (boxConst (k + 1) t + 1) * (n ^ ((k + 1) * (k + 1) ^ t) * n ^ ((t + 1) * (k + 1) ^ t)) := by
    have hn : n ≤ n ^ ((k + 1) * (k + 1) ^ t) := by
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · simp
      · exact Nat.le_self_pow (by positivity) n
    have h8 : (n ^ (t + 1)) ^ (k + 1) ^ t * n ≤
        n ^ ((t + 1) * (k + 1) ^ t) * n ^ ((k + 1) * (k + 1) ^ t) := by
      rw [← pow_mul]
      exact Nat.mul_le_mul_left _ hn
    calc (P ^ (k + 1) ^ t + (n ^ (t + 1)) ^ (k + 1) ^ t) * n
        = P ^ (k + 1) ^ t * n + (n ^ (t + 1)) ^ (k + 1) ^ t * n := add_mul _ _ _
      _ ≤ n ^ ((k + 1) * (k + 1) ^ t) * (boxConst (k + 1) t * n ^ ((t + 1) * (k + 1) ^ t)) +
          n ^ ((t + 1) * (k + 1) ^ t) * n ^ ((k + 1) * (k + 1) ^ t) := add_le_add h4 h8
      _ = _ := by ring
  have h9 : (P + n ^ (t + 1)) ^ (k + 1) ^ t ≤
      2 ^ (k + 1) ^ t * (P ^ (k + 1) ^ t + (n ^ (t + 1)) ^ (k + 1) ^ t) :=
    (add_pow_le (Nat.zero_le _) (Nat.zero_le _) _).trans
      (Nat.mul_le_mul_right _ (Nat.pow_le_pow_right two_pos (Nat.sub_le _ 1)))
  calc #S ^ (k + 1) ^ (t + 1) * n
      = (#S ^ (k + 1)) ^ (k + 1) ^ t * n := by rw [pow_succ', pow_mul]
    _ ≤ ((n ^ (t + 1)) ^ k * ((k + 1) ^ (k + 1) * (k + 1).factorial * (P + n ^ (t + 1))))
          ^ (k + 1) ^ t * n := by
        gcongr
        exact h6.trans (Nat.mul_le_mul_left _ h5)
    _ = (n ^ (t + 1)) ^ (k * (k + 1) ^ t) * ((k + 1) ^ (k + 1) * (k + 1).factorial) ^ (k + 1) ^ t *
          ((P + n ^ (t + 1)) ^ (k + 1) ^ t * n) := by
        rw [mul_pow, mul_pow, ← pow_mul]
        ring
    _ ≤ (n ^ (t + 1)) ^ (k * (k + 1) ^ t) * ((k + 1) ^ (k + 1) * (k + 1).factorial) ^ (k + 1) ^ t *
          (2 ^ (k + 1) ^ t * ((P ^ (k + 1) ^ t + (n ^ (t + 1)) ^ (k + 1) ^ t) * n)) := by
        rw [← mul_assoc (2 ^ (k + 1) ^ t)]
        gcongr
    _ ≤ (n ^ (t + 1)) ^ (k * (k + 1) ^ t) * ((k + 1) ^ (k + 1) * (k + 1).factorial) ^ (k + 1) ^ t *
          (2 ^ (k + 1) ^ t * ((boxConst (k + 1) t + 1) *
            (n ^ ((k + 1) * (k + 1) ^ t) * n ^ ((t + 1) * (k + 1) ^ t)))) := by
        gcongr
    _ = boxConst (k + 1) (t + 1) * n ^ ((t + 2) * (k + 1) ^ (t + 1)) := by
        simp only [boxConst]
        rw [show (t + 2) * (k + 1) ^ (t + 1) = (t + 1) * (k * (k + 1) ^ t) +
            ((k + 1) * (k + 1) ^ t + (t + 1) * (k + 1) ^ t) by ring, pow_add, pow_add, pow_mul]
        ring

/-- The box bound: a set `S` of `(t+1)`-tuples over `Fin n` with no `r × ⋯ × r` box has
`|S|^{r^t} · n ≤ boxConst r t · n^{(t+1) r^t}`. -/
theorem box_bound {r : ℕ} (hr : 1 ≤ r) : ∀ (t n : ℕ) (S : Finset (Fin (t + 1) → Fin n)),
    ¬ HasBox S r → #S ^ (r ^ t) * n ≤ boxConst r t * n ^ ((t + 1) * r ^ t)
  | 0, n, S, hS => by
      simp only [pow_zero, pow_one, boxConst, zero_add, one_mul]
      exact Nat.mul_le_mul_right _ (card_lt_of_not_hasBox S hS).le
  | t + 1, n, S, hS => box_step hr t (box_bound hr t) n S hS

end Box

section Upper

/-- The ordered edges of `E`: injective `t`-tuples whose set of entries is an edge. -/
def orderedEdges {n t : ℕ} (E : Finset (Finset (Fin n))) : Finset (Fin t → Fin n) :=
  univ.filter fun y => Function.Injective y ∧ univ.image y ∈ E

/-- A `t`-uniform `E` has at most as many edges as ordered edges. -/
theorem card_le_card_orderedEdges {n t : ℕ} {E : Finset (Finset (Fin n))} (hE : Uniform E t) :
    #E ≤ #(orderedEdges (t := t) E) := by
  refine card_le_card_of_surjOn (fun y => univ.image y) ?_
  intro e he
  have hc : e.card = t := hE e he
  have himg : univ.image (fun i => e.orderEmbOfFin hc i) = e := by
    ext v
    simp only [mem_image, mem_univ, true_and]
    constructor
    · rintro ⟨i, rfl⟩
      exact e.orderEmbOfFin_mem hc i
    · intro hv
      have : v ∈ Set.range (e.orderEmbOfFin hc) := by
        rw [range_orderEmbOfFin]
        exact hv
      obtain ⟨i, hi⟩ := this
      exact ⟨i, hi⟩
  refine ⟨fun i => e.orderEmbOfFin hc i, ?_, himg⟩
  simp only [orderedEdges, coe_filter, mem_univ, true_and]
  refine ⟨(e.orderEmbOfFin hc).injective, ?_⟩
  rw [himg]
  exact he

/-- A box in the ordered edges of `E` is a copy of `K_t(r)` in `E`. -/
theorem not_hasBox_orderedEdges {n t r : ℕ} (hr : 1 ≤ r) {E : Finset (Finset (Fin n))}
    (hK : ¬ ContainsKt E t r) : ¬ HasBox (orderedEdges (t := t) E) r := by
  rintro ⟨A, hA, hAS⟩
  apply hK
  have hne : ∀ i, (A i).Nonempty := fun i => card_pos.1 (by rw [hA i]; omega)
  choose c hc using hne
  refine ⟨A, hA, fun i j hij => ?_, fun y hy => ?_⟩
  · rw [Finset.disjoint_left]
    intro v hvi hvj
    let y := Function.update (Function.update c i v) j v
    have hy : ∀ k, y k ∈ A k := by
      intro k
      by_cases hkj : k = j
      · subst hkj
        simp [y, hvj]
      · by_cases hki : k = i
        · subst hki
          simp [y, hkj, hvi]
        · simp [y, hkj, hki, hc k]
    have hinj := (mem_filter.1 (hAS y hy)).2.1
    have hyij : y i = y j := by simp [y, hij]
    exact hij (hinj hyij)
  · exact (mem_filter.1 (hAS y hy)).2.2

/-- Natural-number form of the upper bound: `|E|^(r^t) · n ≤ boxConst r t · n^((t+1) r^t)` for
a `K_{t+1}(r)`-free `(t+1)`-uniform `E`. -/
theorem card_pow_mul_le {n t r : ℕ} (hr : 1 ≤ r) {E : Finset (Finset (Fin n))}
    (hE : Uniform E (t + 1)) (hK : ¬ ContainsKt E (t + 1) r) :
    #E ^ (r ^ t) * n ≤ boxConst r t * n ^ ((t + 1) * r ^ t) :=
  le_trans (Nat.mul_le_mul_right _ (Nat.pow_le_pow_left (card_le_card_orderedEdges hE) _))
    (box_bound hr t n _ (not_hasBox_orderedEdges hr hK))

/-- `r^{1-(s+1)} = (r^s)⁻¹`. -/
theorem rpow_one_sub_succ (r s : ℕ) :
    (r : ℝ) ^ ((1 : ℝ) - ((s + 1 : ℕ) : ℝ)) = ((r : ℝ) ^ s)⁻¹ := by
  rw [show (1 : ℝ) - ((s + 1 : ℕ) : ℝ) = -(s : ℝ) by push_cast; ring,
    Real.rpow_neg (Nat.cast_nonneg r), Real.rpow_natCast]

/-- **Erdős 1964, upper bound, explicit form**: a `K_t(r)`-free `t`-uniform hypergraph on `Fin n`
has at most `boxConst r (t-1) · n^{t - r^{1-t}}` edges, for every `n`. -/
theorem erdos_1158_upper_explicit (t r : ℕ) (ht : 1 ≤ t) (hr : 1 ≤ r) (n : ℕ)
    (E : Finset (Finset (Fin n))) (hE : Uniform E t) (hK : ¬ ContainsKt E t r) :
    (#E : ℝ) ≤ boxConst r (t - 1) * (n : ℝ) ^ ((t : ℝ) - (r : ℝ) ^ (1 - (t : ℝ))) := by
  obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  have hnat := card_pow_mul_le hr hE hK
  set K : ℝ := (boxConst r s : ℝ) with hKdef
  have hK1 : 1 ≤ K := by rw [hKdef]; exact_mod_cast one_le_boxConst hr s
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have hE0 : E = ∅ := by
      refine eq_empty_of_forall_notMem fun e he => ?_
      have h1 := hE e he
      have h2 : e.card ≤ 0 := by simpa using card_le_univ e
      omega
    simp only [hE0, card_empty, CharP.cast_eq_zero]
    exact mul_nonneg (by linarith) (Real.rpow_nonneg le_rfl _)
  set x : ℝ := (n : ℝ) with hx
  have hx1 : 1 ≤ x := by rw [hx]; exact_mod_cast hn
  have hx0 : 0 < x := by linarith
  set m : ℕ := r ^ s with hm
  have hm0 : m ≠ 0 := by positivity
  have hmR : (0 : ℝ) < m := by exact_mod_cast Nat.pos_of_ne_zero hm0
  set e : ℝ := ((s + 1 : ℕ) : ℝ) - (r : ℝ) ^ (1 - ((s + 1 : ℕ) : ℝ)) with he
  have hem : e * m = (((s + 1) * m : ℕ) : ℝ) - 1 := by
    rw [he, rpow_one_sub_succ, hm]
    push_cast
    have : ((r : ℝ) ^ s) ≠ 0 := by positivity
    field_simp
  have hpow : (x ^ e) ^ m = x ^ ((s + 1) * m) / x := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le, hem, Real.rpow_sub hx0, Real.rpow_one,
      Real.rpow_natCast]
  have hcast : (#E : ℝ) ^ m * x ≤ K * x ^ ((s + 1) * m) := by
    rw [hx, hKdef]; exact_mod_cast hnat
  have h1 : (#E : ℝ) ^ m ≤ K * (x ^ e) ^ m := by
    rw [hpow, ← mul_div_assoc, le_div_iff₀ hx0]
    exact hcast
  have h2 : K * (x ^ e) ^ m ≤ (K * x ^ e) ^ m := by
    rw [mul_pow]
    exact mul_le_mul_of_nonneg_right (le_self_pow₀ hK1 hm0) (by positivity)
  exact (pow_le_pow_iff_left₀ (Nat.cast_nonneg _) (by positivity) hm0).1 (h1.trans h2)

end Upper


section Weights

variable {α : Type*}

/-- The binomial weight `p^|H| (1-p)^(|E|-|H|)` of a subset `H ⊆ E`. -/
def weight (E : Finset α) (p : ℝ) (H : Finset α) : ℝ := p ^ #H * (1 - p) ^ (#E - #H)

theorem sum_weight (E : Finset α) (p : ℝ) : ∑ H ∈ E.powerset, weight E p H = 1 := by
  simp only [weight]
  rw [sum_pow_mul_eq_add_pow]
  simp

theorem weight_nonneg (E : Finset α) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (H : Finset α) :
    0 ≤ weight E p H :=
  mul_nonneg (pow_nonneg hp0 _) (pow_nonneg (by linarith) _)

/-- The total weight of the subsets of `E` containing a fixed `B ⊆ E` is `p^|B|`. -/
theorem sum_weight_superset [DecidableEq α] (E B : Finset α) (hB : B ⊆ E) (p : ℝ) :
    ∑ H ∈ E.powerset with B ⊆ H, weight E p H = p ^ #B := by
  rw [Finset.sum_nbij' (fun H => H \ B) (fun H => H ∪ B)
    (g := fun H => weight (E \ B) p H * p ^ #B) (t := (E \ B).powerset)]
  · rw [← Finset.sum_mul, sum_weight, one_mul]
  · intro H hH
    simp only [mem_filter, mem_powerset] at hH
    simp only [mem_powerset]
    exact sdiff_subset_sdiff hH.1 le_rfl
  · intro H hH
    simp only [mem_powerset] at hH
    simp only [mem_filter, mem_powerset]
    exact ⟨union_subset (hH.trans sdiff_subset) hB, subset_union_right⟩
  · intro H hH
    simp only [mem_filter, mem_powerset] at hH
    exact sdiff_union_of_subset hH.2
  · intro H hH
    simp only [mem_powerset] at hH
    apply union_sdiff_cancel_right
    exact disjoint_of_subset_left hH sdiff_disjoint
  · intro H hH
    simp only [mem_filter, mem_powerset] at hH
    have hBH : #B ≤ #H := card_le_card hH.2
    have hHE : #H ≤ #E := card_le_card hH.1
    simp only [weight, card_sdiff_of_subset hH.2, card_sdiff_of_subset hB]
    rw [mul_right_comm, pow_sub_mul_pow p hBH]
    congr 2
    omega

/-- Linearity of expectation for the number of members of `S` contained in a random subset. -/
theorem sum_weight_mul_card_filter [DecidableEq α] (E : Finset α) (S : Finset (Finset α))
    (hS : ∀ B ∈ S, B ⊆ E) (p : ℝ) :
    ∑ H ∈ E.powerset, weight E p H * (#{B ∈ S | B ⊆ H} : ℝ) = ∑ B ∈ S, p ^ #B := by
  simp_rw [← sum_boole, mul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun B hB => ?_
  rw [← sum_weight_superset E B (hS B hB) p, sum_filter]
  simp

theorem sum_weight_mul_card [DecidableEq α] (E : Finset α) (p : ℝ) :
    ∑ H ∈ E.powerset, weight E p H * (#H : ℝ) = p * #E := by
  have h := sum_weight_mul_card_filter E (E.map ⟨fun x => {x}, singleton_injective⟩)
    (by simp) p
  have hc : ∀ H ∈ E.powerset,
      #{B ∈ E.map ⟨fun x => {x}, singleton_injective⟩ | B ⊆ H} = #H := by
    intro H hH
    rw [mem_powerset] at hH
    rw [filter_map, card_map]
    congr 1
    ext x
    simp only [mem_filter, Function.comp_apply, Function.Embedding.coeFn_mk, singleton_subset_iff]
    exact ⟨fun h => h.2, fun h => ⟨hH h, h⟩⟩
  rw [sum_congr rfl fun H hH => by rw [hc H hH]] at h
  rw [h]
  simp [mul_comm]

end Weights

section Copies

variable {n t r : ℕ}

/-- The edge set `{{c 0, …, c (t-1)} : c i ∈ A i}` of the complete `t`-partite hypergraph with
parts `A 0, …, A (t-1)`. -/
def edgesOf (A : Fin t → Finset (Fin n)) : Finset (Finset (Fin n)) :=
  (Fintype.piFinset A).image fun c => univ.image c

/-- Systems of `t` pairwise disjoint `r`-sets. -/
def partSystems (n t r : ℕ) : Finset (Fin t → Finset (Fin n)) :=
  (Fintype.piFinset fun _ => powersetCard r univ).filter
    fun A => ∀ i j, i ≠ j → Disjoint (A i) (A j)

/-- The edge sets of all copies of `K_t(r)` in the complete `t`-uniform hypergraph on `Fin n`. -/
def copies (n t r : ℕ) : Finset (Finset (Finset (Fin n))) := (partSystems n t r).image edgesOf

/-- A transversal of pairwise disjoint sets is injective. -/
theorem injective_of_mem_piFinset {A : Fin t → Finset (Fin n)}
    (hA : ∀ i j, i ≠ j → Disjoint (A i) (A j)) {c : Fin t → Fin n}
    (hc : c ∈ Fintype.piFinset A) : Function.Injective c := by
  intro i j hij
  by_contra hne
  rw [Fintype.mem_piFinset] at hc
  have h1 := hc i
  have h2 := hc j
  rw [← hij] at h2
  exact Finset.disjoint_left.1 (hA i j hne) h1 h2

/-- Each copy is a set of exactly `r^t` edges of size `t`. -/
theorem copies_spec {B : Finset (Finset (Fin n))} (hB : B ∈ copies n t r) :
    B ⊆ powersetCard t univ ∧ #B = r ^ t := by
  obtain ⟨A, hA, rfl⟩ := mem_image.1 hB
  simp only [partSystems, mem_filter, Fintype.mem_piFinset, mem_powersetCard, subset_univ,
    true_and] at hA
  refine ⟨fun e he => ?_, ?_⟩
  · obtain ⟨c, hc, rfl⟩ := mem_image.1 he
    rw [mem_powersetCard]
    refine ⟨subset_univ _, ?_⟩
    rw [card_image_of_injective _ (injective_of_mem_piFinset hA.2 hc), card_univ,
      Fintype.card_fin]
  · rw [edgesOf, card_image_of_injOn, Fintype.card_piFinset]
    · simp [hA.1]
    · intro c hc c' hc' hcc'
      simp only [mem_coe, Fintype.mem_piFinset] at hc hc'
      funext i
      have hi : c i ∈ univ.image c' := by
        simp only at hcc'
        rw [← hcc']
        exact mem_image_of_mem c (mem_univ i)
      obtain ⟨j, -, hj⟩ := mem_image.1 hi
      by_cases hij : j = i
      · subst hij
        exact hj.symm
      · have h1 := hc' j
        rw [hj] at h1
        exact absurd (hc i) (Finset.disjoint_left.1 (hA.2 j i hij) h1)

/-- There are at most `n^{rt}` copies. -/
theorem card_copies_le : #(copies n t r) ≤ n ^ (r * t) := by
  calc #(copies n t r) ≤ #(partSystems n t r) := card_image_le
    _ ≤ #(Fintype.piFinset fun _ : Fin t => powersetCard r (univ : Finset (Fin n))) :=
        card_filter_le _ _
    _ = (n.choose r) ^ t := by
        rw [Fintype.card_piFinset_const, card_powersetCard, card_univ, Fintype.card_fin]
    _ ≤ (n ^ r) ^ t := Nat.pow_le_pow_left (Nat.choose_le_pow n r) t
    _ = n ^ (r * t) := (pow_mul n r t).symm

/-- A hypergraph containing `K_t(r)` contains the edge set of one of the `copies`. -/
theorem exists_copy_of_containsKt {G : Finset (Finset (Fin n))} (hG : ContainsKt G t r) :
    ∃ B ∈ copies n t r, B ⊆ G := by
  obtain ⟨A, hA, hdisj, hsub⟩ := hG
  refine ⟨edgesOf A, mem_image_of_mem _ ?_, fun e he => ?_⟩
  · simp only [partSystems, mem_filter, Fintype.mem_piFinset, mem_powersetCard, subset_univ,
      true_and]
    exact ⟨hA, hdisj⟩
  · obtain ⟨c, hc, rfl⟩ := mem_image.1 he
    exact hsub c (Fintype.mem_piFinset.1 hc)

end Copies

section Lower

/-- The deletion step: from a subset `H` of all `t`-sets that is at least as good as the average
of the binomial weights, remove every edge of every copy of `K_t(r)` inside `H`. -/
theorem exists_free_of_weight (n t r : ℕ) (hr : 1 ≤ r) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    ∃ G : Finset (Finset (Fin n)), G ⊆ powersetCard t univ ∧ ¬ ContainsKt G t r ∧
      p * (n.choose t) - (r ^ t : ℕ) * p ^ (r ^ t) * #(copies n t r) ≤ #G := by
  set E : Finset (Finset (Fin n)) := powersetCard t univ with hE
  set S := copies n t r with hS
  set q := r ^ t with hq
  have hEcard : #E = n.choose t := by simp [hE]
  let f : Finset (Finset (Fin n)) → ℝ := fun H => (#H : ℝ) - q * (#{B ∈ S | B ⊆ H} : ℝ)
  have hsum : ∑ H ∈ E.powerset, weight E p H * f H = p * (n.choose t) - q * p ^ q * #S := by
    have h1 := sum_weight_mul_card E p
    have h2 := sum_weight_mul_card_filter E S (fun B hB => (copies_spec hB).1) p
    have h3 : ∑ B ∈ S, p ^ #B = #S * p ^ q := by
      rw [sum_congr rfl fun B hB => by rw [(copies_spec hB).2], sum_const, nsmul_eq_mul]
    simp only [f, mul_sub, sum_sub_distrib, h1, hEcard]
    rw [sum_congr rfl fun H _ => mul_left_comm (weight E p H) (q : ℝ) _, ← mul_sum, h2, h3]
    ring
  obtain ⟨H, hH, hmax⟩ := E.powerset.exists_max_image f ⟨∅, empty_mem_powerset E⟩
  have hfH : p * (n.choose t) - q * p ^ q * #S ≤ f H := by
    rw [← hsum]
    calc ∑ H' ∈ E.powerset, weight E p H' * f H'
        ≤ ∑ H' ∈ E.powerset, weight E p H' * f H :=
          sum_le_sum fun H' hH' =>
            mul_le_mul_of_nonneg_left (hmax H' hH') (weight_nonneg E hp0 hp1 H')
      _ = f H := by rw [← sum_mul, sum_weight, one_mul]
  have hHE : H ⊆ E := mem_powerset.1 hH
  set X := {B ∈ S | B ⊆ H} with hX
  refine ⟨H \ X.biUnion id, sdiff_subset.trans hHE, fun hK => ?_, ?_⟩
  · obtain ⟨B, hBS, hBG⟩ := exists_copy_of_containsKt hK
    have hBX : B ∈ X := mem_filter.2 ⟨hBS, hBG.trans sdiff_subset⟩
    obtain ⟨b, hb⟩ : B.Nonempty := card_pos.1 (by rw [(copies_spec hBS).2]; positivity)
    have hbG := hBG hb
    rw [Finset.mem_sdiff] at hbG
    exact hbG.2 (mem_biUnion.2 ⟨B, hBX, hb⟩)
  · have h1 : #H ≤ #(H \ X.biUnion id) + #(X.biUnion id) := card_le_card_sdiff_add_card
    have h2 : #(X.biUnion id) ≤ q * #X := by
      calc #(X.biUnion id) ≤ ∑ B ∈ X, #(id B) := card_biUnion_le
        _ = ∑ B ∈ X, q := sum_congr rfl fun B hB => (copies_spec (mem_filter.1 hB).1).2
        _ = q * #X := by rw [sum_const, smul_eq_mul, mul_comm]
    have h3 : (#H : ℝ) ≤ #(H \ X.biUnion id) + q * #X := by
      exact_mod_cast h1.trans (by omega)
    have h4 : f H = #H - q * #X := rfl
    linarith

/-- The explicit constant `4 r^t (2^t t!)²` of the lower bound. -/
def lowerConst (t r : ℕ) : ℕ := 4 * r ^ t * (2 ^ t * t.factorial) ^ 2

/-- **Erdős 1964, lower bound, explicit form**: for `t ≥ 1`, `r ≥ 2` and `n ≥ 2t` there is a
`K_t(r)`-free `t`-uniform hypergraph on `Fin n` with at least
`n^{t - t(r-1)/(r^t-1)} / (4 r^t (2^t t!)²)` edges. -/
theorem erdos_1158_lower_explicit (t r : ℕ) (ht : 1 ≤ t) (hr : 2 ≤ r) (n : ℕ) (hn : 2 * t ≤ n) :
    ∃ E : Finset (Finset (Fin n)), Uniform E t ∧ ¬ ContainsKt E t r ∧
      (n : ℝ) ^ ((t : ℝ) - t * ((r : ℝ) - 1) / ((r : ℝ) ^ t - 1)) / lowerConst t r ≤ #E := by
  set q : ℕ := r ^ t with hq
  set β : ℝ := t * ((r : ℝ) - 1) / ((r : ℝ) ^ t - 1) with hβ
  set x : ℝ := (n : ℝ) with hx
  set Dc : ℝ := 2 ^ t * t.factorial with hDc
  set c : ℝ := 1 / (2 * q * Dc) with hc
  set p : ℝ := c * x ^ (-β) with hp
  have hx1 : 1 ≤ x := by rw [hx]; exact_mod_cast (show 1 ≤ n by omega)
  have hx0 : 0 < x := by linarith
  have hq2 : 2 ≤ q := by
    rw [hq]
    calc 2 ≤ r := hr
      _ = r ^ 1 := (pow_one r).symm
      _ ≤ r ^ t := Nat.pow_le_pow_right (by omega) ht
  have hqR : (2 : ℝ) ≤ q := by exact_mod_cast hq2
  have hrq : (r : ℝ) ^ t = q := by rw [hq]; push_cast; rfl
  have hq1 : (r : ℝ) ^ t - 1 ≠ 0 := by rw [hrq]; linarith
  have hβ0 : 0 ≤ β := by
    rw [hβ, hrq]
    have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast (show 1 ≤ r by omega)
    apply div_nonneg (mul_nonneg (Nat.cast_nonneg t) (by linarith)) (by linarith)
  have hDc1 : 1 ≤ Dc := by
    rw [hDc]
    exact one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by norm_num))
      (by exact_mod_cast Nat.one_le_iff_ne_zero.2 (Nat.factorial_ne_zero t))
  have hc0 : 0 < c := by rw [hc]; positivity
  have hc1 : c ≤ 1 := by
    rw [hc]
    exact div_le_one_of_le₀ (by nlinarith) (by positivity)
  have hy0 : 0 < x ^ (-β) := Real.rpow_pos_of_pos hx0 _
  have hy1 : x ^ (-β) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hx1 (by linarith)
  have hp0 : 0 ≤ p := by rw [hp]; positivity
  have hp1 : p ≤ 1 := by
    rw [hp]
    calc c * x ^ (-β) ≤ 1 * 1 := mul_le_mul hc1 hy1 hy0.le zero_le_one
      _ = 1 := one_mul 1
  obtain ⟨G, hG1, hG2, hG3⟩ := exists_free_of_weight n t r (by omega) hp0 hp1
  refine ⟨G, fun e he => (mem_powersetCard.1 (hG1 he)).2, hG2, le_trans ?_ hG3⟩
  set z : ℝ := x ^ ((t : ℝ) - β) with hz
  have hz0 : 0 < z := Real.rpow_pos_of_pos hx0 _
  have hN : x ^ t / Dc ≤ (n.choose t : ℝ) := by
    refine le_trans ?_ (Nat.pow_le_choose (α := ℝ) t n)
    have h2 : x ≤ 2 * ((n + 1 - t : ℕ) : ℝ) := by
      rw [hx]; exact_mod_cast (show n ≤ 2 * (n + 1 - t) by omega)
    have h3 : x ^ t ≤ 2 ^ t * ((n + 1 - t : ℕ) : ℝ) ^ t := by
      rw [← mul_pow]; exact pow_le_pow_left₀ (by linarith) h2 t
    rw [hDc, div_le_div_iff₀ (by positivity) (by positivity)]
    calc x ^ t * t.factorial ≤ 2 ^ t * ((n + 1 - t : ℕ) : ℝ) ^ t * t.factorial := by gcongr
      _ = _ := by ring
  have hcop : (#(copies n t r) : ℝ) ≤ x ^ (r * t) := by
    rw [hx]; exact_mod_cast card_copies_le
  have hexp : x ^ (r * t) * (x ^ (-β)) ^ q = z := by
    rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul hx0.le, ← Real.rpow_add hx0, hz]
    congr 1
    rw [hβ, ← hrq]
    push_cast
    field_simp
    ring
  have hxt : x ^ t * x ^ (-β) = z := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hx0, hz, sub_eq_add_neg]
  have key1 : c * z / Dc ≤ p * (n.choose t) := by
    calc c * z / Dc = p * (x ^ t / Dc) := by rw [hp, ← hxt]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hN hp0
  have key2 : (q : ℝ) * p ^ q * #(copies n t r) ≤ c * z / (2 * Dc) := by
    calc (q : ℝ) * p ^ q * #(copies n t r) ≤ q * p ^ q * x ^ (r * t) := by gcongr
      _ = q * c ^ q * z := by rw [← hexp, hp, mul_pow]; ring
      _ ≤ q * c ^ 2 * z :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
            (pow_le_pow_of_le_one hc0.le hc1 hq2) (by positivity)) hz0.le
      _ = c * z / (2 * Dc) := by rw [hc]; field_simp
  have hconst : (lowerConst t r : ℝ) = 4 * q * Dc ^ 2 := by
    simp only [lowerConst, hq, hDc]
    push_cast
    ring
  have hfinal : z / lowerConst t r = c * z / Dc - c * z / (2 * Dc) := by
    rw [hconst, hc]
    field_simp
    ring
  have hG3' : p * (n.choose t) - (q : ℝ) * p ^ q * #(copies n t r) ≤ #G := hG3
  rw [hfinal]
  linarith

end Lower


section Main

/-- **Erdős 1964, upper bound**: `ex_t(n, K_t(r)) ≪ n^{t - r^{1-t}}`. -/
theorem erdos_1158_upper (t r : ℕ) (ht : 1 ≤ t) (hr : 1 ≤ r) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, ∀ E : Finset (Finset (Fin n)), Uniform E t →
      ¬ ContainsKt E t r → (#E : ℝ) ≤ C * (n : ℝ) ^ ((t : ℝ) - (r : ℝ) ^ (1 - (t : ℝ))) :=
  ⟨boxConst r (t - 1), Nat.cast_pos.2 (one_le_boxConst hr (t - 1)),
    fun n E hE hK => erdos_1158_upper_explicit t r ht hr n E hE hK⟩

/-- The deletion exponent is `O(r^{1-t})`: `t(r-1)/(r^t-1) ≤ t r^{1-t}`. -/
theorem deletion_exponent_le (t r : ℕ) (ht : 1 ≤ t) (hr : 2 ≤ r) :
    (t : ℝ) * ((r : ℝ) - 1) / ((r : ℝ) ^ t - 1) ≤ t * (r : ℝ) ^ (1 - (t : ℝ)) := by
  obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
  rw [rpow_one_sub_succ]
  push_cast
  have hr1 : (2 : ℝ) ≤ r := by exact_mod_cast hr
  have hrs : (1 : ℝ) ≤ (r : ℝ) ^ s := one_le_pow₀ (by linarith)
  have hpos : 0 < (r : ℝ) ^ (s + 1) - 1 := by
    rw [pow_succ]
    nlinarith
  rw [div_le_iff₀ hpos]
  have hinv : ((r : ℝ) ^ s)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hrs
  have hrs0 : (r : ℝ) ^ s ≠ 0 := by positivity
  have h : ((s : ℝ) + 1) * ((r : ℝ) ^ s)⁻¹ * ((r : ℝ) ^ (s + 1) - 1) =
      ((s : ℝ) + 1) * (r - ((r : ℝ) ^ s)⁻¹) := by
    rw [pow_succ]
    field_simp
  rw [h]
  have hs : (0 : ℝ) ≤ s + 1 := by positivity
  nlinarith

theorem lowerConst_pos (t r : ℕ) (hr : 1 ≤ r) : (0 : ℝ) < lowerConst t r := by
  have := Nat.factorial_pos t
  have : 0 < lowerConst t r := by unfold lowerConst; positivity
  exact_mod_cast this

/-- **Erdős 1964, lower bound**: `ex_t(n, K_t(r)) ≥ c n^{t - t r^{1-t}}` for `n ≥ 2t`, i.e.
`ex_t(n, K_t(r)) ≥ n^{t - O(r^{1-t})}` (the implied constant is `t`). -/
theorem erdos_1158_lower (t r : ℕ) (ht : 1 ≤ t) (hr : 2 ≤ r) :
    ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, 2 * t ≤ n → ∃ E : Finset (Finset (Fin n)), Uniform E t ∧
      ¬ ContainsKt E t r ∧ c * (n : ℝ) ^ ((t : ℝ) - t * (r : ℝ) ^ (1 - (t : ℝ))) ≤ #E := by
  have hL := lowerConst_pos t r (by omega)
  refine ⟨1 / lowerConst t r, by positivity, fun n hn => ?_⟩
  obtain ⟨E, hE1, hE2, hE3⟩ := erdos_1158_lower_explicit t r ht hr n hn
  refine ⟨E, hE1, hE2, le_trans ?_ hE3⟩
  have hx1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  rw [one_div_mul_eq_div]
  exact div_le_div_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le hx1
    (by linarith [deletion_exponent_le t r ht hr])) hL.le

/-- The lower bound in `ε` form: for every `ε > 0` and all large `n` there is a `K_t(r)`-free
`t`-uniform hypergraph on `Fin n` with at least `n^{t - t(r-1)/(r^t-1) - ε}` edges. -/
theorem erdos_1158_lower_eventually (t r : ℕ) (ht : 1 ≤ t) (hr : 2 ≤ r) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∃ E : Finset (Finset (Fin n)), Uniform E t ∧ ¬ ContainsKt E t r ∧
      (n : ℝ) ^ ((t : ℝ) - t * ((r : ℝ) - 1) / ((r : ℝ) ^ t - 1) - ε) ≤ #E := by
  have hL := lowerConst_pos t r (by omega)
  have h1 : Tendsto (fun n : ℕ => (n : ℝ) ^ ε) atTop atTop :=
    (tendsto_rpow_atTop hε).comp tendsto_natCast_atTop_atTop
  filter_upwards [h1.eventually_ge_atTop (lowerConst t r : ℝ), eventually_ge_atTop (2 * t)]
    with n hn1 hn2
  obtain ⟨E, hE1, hE2, hE3⟩ := erdos_1158_lower_explicit t r ht hr n hn2
  refine ⟨E, hE1, hE2, le_trans ?_ hE3⟩
  have hx0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  rw [Real.rpow_sub hx0]
  exact div_le_div_of_nonneg_left (Real.rpow_nonneg hx0.le _) hL hn1

/-- **Erdős Problem 1158, the bounds of Erdős [Er64f]**: for `t ≥ 1` and `r ≥ 2`,
`n^{t - t r^{1-t}} ≪ ex_t(n, K_t(r)) ≪ n^{t - r^{1-t}}`. -/
theorem erdos_1158 (t r : ℕ) (ht : 1 ≤ t) (hr : 2 ≤ r) :
    (∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, 2 * t ≤ n →
      c * (n : ℝ) ^ ((t : ℝ) - t * (r : ℝ) ^ (1 - (t : ℝ))) ≤ ex t r n) ∧
    (∃ C : ℝ, 0 < C ∧ ∀ n : ℕ,
      (ex t r n : ℝ) ≤ C * (n : ℝ) ^ ((t : ℝ) - (r : ℝ) ^ (1 - (t : ℝ)))) := by
  obtain ⟨c, hc, hlow⟩ := erdos_1158_lower t r ht hr
  obtain ⟨C, hC, hup⟩ := erdos_1158_upper t r ht (by omega)
  refine ⟨⟨c, hc, fun n hn => ?_⟩, ⟨C, hC, fun n => ?_⟩⟩
  · obtain ⟨E, hE1, hE2, hE3⟩ := hlow n hn
    exact hE3.trans (by exact_mod_cast card_le_ex hE1 hE2)
  · obtain ⟨E, hE1, hE2, hE3⟩ := exists_card_eq_ex t r n (by omega)
    rw [← hE3]
    exact hup n E hE1 hE2

end Main

end Erdos1158
