import Mathlib

/-!
# Graphs without `C₃` and `C₄` (Erdős Problem 573): the Kővári–Sós–Turán / Reiman upper bound

Erdős Problem 573 (Erdős–Simonovits) asks whether `ex(n; {C₃, C₄}) ∼ (n / 2) ^ (3 / 2)`.
This file proves the classical upper bound for `C₄`-free graphs (Kővári–Sós–Turán 1954,
Reiman 1958): an `n`-vertex graph containing no `4`-cycle has at most
`(n / 4) * (1 + √(4n - 3))` edges. Consequently
`ex(n; {C₃, C₄}) ≤ ex(n; C₄) ≤ n ^ (3 / 2) / 2 + n / 4`.

"`G` contains no `4`-cycle" is Mathlib's `(cycleGraph 4).Free G`, i.e. there is no injective
graph homomorphism `cycleGraph 4 →g G` (a not necessarily induced copy). The single-graph extremal
number is Mathlib's `SimpleGraph.extremalNumber`, which is also what the formal-conjectures project
uses for `ex(n; C_{2k})` (e.g. `ErdosProblems/572.lean`); formal-conjectures has no file for
Problem 573, so the two-graph extremal number `exC3C4` is defined here in the same style as
`SimpleGraph.extremalNumber`.

## Proof

If `u ≠ w` had two distinct common neighbours `x, y`, then `u - x - w - y - u` would be a `4`-cycle.
Hence `∑ᵥ deg(v)² = ∑_{u,w} codeg(u, w) ≤ ∑ᵤ deg(u) + n(n - 1) = 2e + n(n - 1)`, and by
Cauchy–Schwarz `(2e)² ≤ n ∑ᵥ deg(v)²`. So `4e² - 2ne - n²(n - 1) ≤ 0`, and solving the quadratic
gives `e ≤ (n / 4)(1 + √(4n - 3))`.
-/

namespace C3C4Free

open Finset SimpleGraph

section FourCycle

variable {V : Type*} {G : SimpleGraph V}

/-- `G` contains a copy of `C₄` iff it has four pairwise distinct vertices `a, b, c, d` with
`a ~ b ~ c ~ d ~ a`. This justifies `(cycleGraph 4).Free G` as "`G` has no `4`-cycle". -/
theorem cycleGraph_four_isContained_iff :
    cycleGraph 4 ⊑ G ↔ ∃ a b c d : V, a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a := by
  constructor
  · rintro ⟨f⟩
    have hadj : ∀ i j : Fin 4, (cycleGraph 4).Adj i j → G.Adj (f i) (f j) :=
      fun i j h => f.toHom.map_adj h
    have hinj : ∀ i j : Fin 4, i ≠ j → f i ≠ f j := fun i j h h' => h (f.injective h')
    refine ⟨f 0, f 1, f 2, f 3, hinj _ _ (by decide), hinj _ _ (by decide), hinj _ _ (by decide),
      hinj _ _ (by decide), hinj _ _ (by decide), hinj _ _ (by decide),
      hadj _ _ (by decide), hadj _ _ (by decide), hadj _ _ (by decide), hadj _ _ (by decide)⟩
  · rintro ⟨a, b, c, d, hab, hac, had, hbc, hbd, hcd, h1, h2, h3, h4⟩
    let g : Fin 4 → V := ![a, b, c, d]
    have hg : ∀ i j : Fin 4, (cycleGraph 4).Adj i j → G.Adj (g i) (g j) := by
      intro i j h
      fin_cases i <;> fin_cases j <;>
        first
        | exact absurd h (by decide)
        | simpa [g] using h1 | simpa [g] using h1.symm | simpa [g] using h2
        | simpa [g] using h2.symm | simpa [g] using h3 | simpa [g] using h3.symm
        | simpa [g] using h4 | simpa [g] using h4.symm
    have hginj : Function.Injective g := by
      intro i j h
      fin_cases i <;> fin_cases j <;> simp_all [g, eq_comm]
    exact ⟨⟨⟨g, hg _ _⟩, hginj⟩⟩

/-- `(cycleGraph 3).Free G` is exactly triangle-freeness `G.CliqueFree 3`. -/
theorem free_cycleGraph_three_iff : (cycleGraph 3).Free G ↔ G.CliqueFree 3 := by
  rw [cliqueFree_iff_free_top_fin, cycleGraph_three_eq_top]

end FourCycle

section Counting

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- In a `C₄`-free graph, two distinct vertices have at most one common neighbour. -/
theorem card_commonNeighbors_le_one (hG : (cycleGraph 4).Free G) {u w : V} (huw : u ≠ w) :
    #{v | G.Adj u v ∧ G.Adj w v} ≤ 1 := by
  rw [Finset.card_le_one]
  intro x hx y hy
  by_contra hxy
  simp only [mem_filter, mem_univ, true_and] at hx hy
  exact hG (cycleGraph_four_isContained_iff.2 ⟨u, x, w, y, hx.1.ne, huw, hy.1.ne, hx.2.ne.symm,
    hxy, hy.2.ne, hx.1, hx.2.symm, hy.2, hy.1.symm⟩)

omit [DecidableEq V] in
/-- Double counting cherries: `∑ᵥ deg(v)² = ∑_{u,w} codeg(u, w)`. -/
theorem sum_degree_sq_eq :
    ∑ v, G.degree v ^ 2 = ∑ u, ∑ w, #{v | G.Adj u v ∧ G.Adj w v} := by
  calc ∑ v, G.degree v ^ 2
      = ∑ v, ∑ u, ∑ w, (if G.Adj u v ∧ G.Adj w v then 1 else 0) := by
        refine sum_congr rfl fun v _ => ?_
        rw [← card_neighborFinset_eq_degree, neighborFinset_eq_filter, card_filter, sq,
          sum_mul_sum]
        refine sum_congr rfl fun u _ => sum_congr rfl fun w _ => ?_
        by_cases hu : G.Adj u v <;> by_cases hw : G.Adj w v <;>
          simp [hu, hw, G.adj_comm v]
    _ = ∑ u, ∑ w, ∑ v, (if G.Adj u v ∧ G.Adj w v then 1 else 0) := by
        rw [sum_comm]
        exact sum_congr rfl fun u _ => sum_comm
    _ = _ := by simp only [card_filter]

/-- For a `C₄`-free graph, `∑ᵥ deg(v)² + n ≤ 2e + n²`. -/
theorem sum_degree_sq_add_card_le (hG : (cycleGraph 4).Free G) :
    ∑ v, G.degree v ^ 2 + Fintype.card V ≤ 2 * #G.edgeFinset + Fintype.card V ^ 2 := by
  have h : ∀ u, ∑ w, #{v | G.Adj u v ∧ G.Adj w v} + 1 ≤ G.degree u + Fintype.card V := by
    intro u
    rw [← add_sum_erase _ _ (mem_univ u)]
    have h1 : #{v | G.Adj u v ∧ G.Adj u v} = G.degree u := by
      simp [← card_neighborFinset_eq_degree, neighborFinset_eq_filter]
    have h2 : ∑ w ∈ univ.erase u, #{v | G.Adj u v ∧ G.Adj w v} ≤ #(univ.erase u) := by
      calc ∑ w ∈ univ.erase u, #{v | G.Adj u v ∧ G.Adj w v}
          ≤ ∑ w ∈ univ.erase u, 1 :=
            sum_le_sum fun w hw => card_commonNeighbors_le_one hG (ne_of_mem_erase hw).symm
        _ = #(univ.erase u) := by simp
    have h3 : #(univ.erase u) + 1 = Fintype.card V := by
      rw [card_erase_of_mem (mem_univ u), card_univ]
      have := Fintype.card_pos_iff.2 ⟨u⟩
      omega
    omega
  calc ∑ v, G.degree v ^ 2 + Fintype.card V
      = ∑ u, (∑ w, #{v | G.Adj u v ∧ G.Adj w v} + 1) := by
        rw [sum_degree_sq_eq, sum_add_distrib, sum_const, card_univ, smul_eq_mul, mul_one]
    _ ≤ ∑ u, (G.degree u + Fintype.card V) := sum_le_sum fun u _ => h u
    _ = _ := by
        rw [sum_add_distrib, G.sum_degrees_eq_twice_card_edges, sum_const, card_univ, smul_eq_mul,
          sq]

/-- For a `C₄`-free graph with `n` vertices and `e` edges, `(2e)² + n² ≤ n (2e + n²)`. -/
theorem sq_two_mul_card_edgeFinset_add_sq_le (hG : (cycleGraph 4).Free G) :
    (2 * #G.edgeFinset) ^ 2 + Fintype.card V ^ 2 ≤
      Fintype.card V * (2 * #G.edgeFinset + Fintype.card V ^ 2) := by
  have hcs : (∑ v, G.degree v) ^ 2 ≤ Fintype.card V * ∑ v, G.degree v ^ 2 := by
    simpa using sq_sum_le_card_mul_sum_sq (s := univ) (f := fun v => G.degree v)
  rw [G.sum_degrees_eq_twice_card_edges] at hcs
  have h := Nat.mul_le_mul_left (Fintype.card V) (sum_degree_sq_add_card_le hG)
  rw [mul_add] at h
  nlinarith [hcs, h]

/-- **Kővári–Sós–Turán / Reiman.** A graph on `n` vertices with no `4`-cycle has at most
`(n / 4) * (1 + √(4n - 3))` edges. -/
theorem card_edgeFinset_le_of_free_cycleGraph_four (hG : (cycleGraph 4).Free G) :
    (#G.edgeFinset : ℝ) ≤ Fintype.card V / 4 * (1 + √(4 * Fintype.card V - 3)) := by
  have h := sq_two_mul_card_edgeFinset_add_sq_le hG
  set e := #G.edgeFinset
  set n := Fintype.card V
  have hr : (2 * e : ℝ) ^ 2 + (n : ℝ) ^ 2 ≤ n * (2 * e + (n : ℝ) ^ 2) := by exact_mod_cast h
  rcases Nat.eq_zero_or_pos n with hn | hn
  · have he : (e : ℝ) = 0 := by
      rw [hn] at hr
      push_cast at hr
      nlinarith [sq_nonneg (e : ℝ)]
    simp [he, hn]
  · have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hs0 : 0 ≤ √(4 * (n : ℝ) - 3) := Real.sqrt_nonneg _
    have hs2 : √(4 * (n : ℝ) - 3) ^ 2 = 4 * n - 3 := Real.sq_sqrt (by linarith)
    set s := √(4 * (n : ℝ) - 3)
    by_contra hlt
    rw [not_le] at hlt
    have h1 : 0 < 4 * (e : ℝ) - n * (1 + s) := by linarith
    have h2 : 0 < 4 * (e : ℝ) - n * (1 - s) := by nlinarith
    have h3 : (n : ℝ) ^ 2 * s ^ 2 = n ^ 2 * (4 * n - 3) := by rw [hs2]
    nlinarith [mul_pos h1 h2]

/-- The same bound for graphs with no triangle and no `4`-cycle. -/
theorem card_edgeFinset_le_of_free_cycleGraph_three_four (_hG₃ : (cycleGraph 3).Free G)
    (hG₄ : (cycleGraph 4).Free G) :
    (#G.edgeFinset : ℝ) ≤ Fintype.card V / 4 * (1 + √(4 * Fintype.card V - 3)) :=
  card_edgeFinset_le_of_free_cycleGraph_four hG₄

end Counting

section ExtremalNumber

/-- `ex(n; C₄) ≤ (n / 4) * (1 + √(4n - 3))`, for Mathlib's `SimpleGraph.extremalNumber`. -/
theorem extremalNumber_cycleGraph_four_le (n : ℕ) :
    (extremalNumber n (cycleGraph 4) : ℝ) ≤ n / 4 * (1 + √(4 * n - 3)) := by
  have key := extremalNumber_le_iff_of_nonneg (V := Fin n) (cycleGraph 4)
    (m := (n : ℝ) / 4 * (1 + √(4 * n - 3))) (by positivity)
  rw [Fintype.card_fin] at key
  rw [key]
  intro G _ hG
  simpa using card_edgeFinset_le_of_free_cycleGraph_four hG

open scoped Classical in
/-- The extremal number `ex(n; {C₃, C₄})`: the maximum number of edges of a simple graph on
`n` vertices containing neither a triangle nor a `4`-cycle. Defined exactly like Mathlib's
`SimpleGraph.extremalNumber`, with the single forbidden graph replaced by the pair `C₃, C₄`. -/
noncomputable def exC3C4 (n : ℕ) : ℕ :=
  sup {G : SimpleGraph (Fin n) | (cycleGraph 3).Free G ∧ (cycleGraph 4).Free G} (#·.edgeFinset)

/-- Every `{C₃, C₄}`-free graph on `n` vertices has at most `exC3C4 n` edges. -/
theorem card_edgeFinset_le_exC3C4 {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    (hG₃ : (cycleGraph 3).Free G) (hG₄ : (cycleGraph 4).Free G) :
    #G.edgeFinset ≤ exC3C4 n := by
  classical
  rw [exC3C4]
  convert! @le_sup _ _ _ _ {G : SimpleGraph (Fin n) | (cycleGraph 3).Free G ∧
    (cycleGraph 4).Free G} (#·.edgeFinset) G ((mem_filter_univ _).2 ⟨hG₃, hG₄⟩)

/-- `exC3C4 n` is attained by some `{C₃, C₄}`-free graph on `n` vertices. -/
theorem exists_card_edgeFinset_eq_exC3C4 (n : ℕ) :
    ∃ G : SimpleGraph (Fin n), ∃ _ : DecidableRel G.Adj,
      (cycleGraph 3).Free G ∧ (cycleGraph 4).Free G ∧ #G.edgeFinset = exC3C4 n := by
  classical
  obtain ⟨G, hG, hsup⟩ := exists_mem_eq_sup
    ({G : SimpleGraph (Fin n) | (cycleGraph 3).Free G ∧ (cycleGraph 4).Free G} : Finset _)
    ⟨⊥, (mem_filter_univ _).2 ⟨fun ⟨f⟩ => (bot_adj _ _).1 (f.toHom.map_adj
      (show (cycleGraph 3).Adj 0 1 by decide)), fun ⟨f⟩ => (bot_adj _ _).1 (f.toHom.map_adj
      (show (cycleGraph 4).Adj 0 1 by decide))⟩⟩ (#·.edgeFinset)
  simp only [mem_filter, mem_univ, true_and] at hG
  refine ⟨G, inferInstance, hG.1, hG.2, ?_⟩
  rw [exC3C4]
  convert! hsup.symm

/-- `ex(n; {C₃, C₄}) ≤ ex(n; C₄)`. -/
theorem exC3C4_le_extremalNumber (n : ℕ) : exC3C4 n ≤ extremalNumber n (cycleGraph 4) := by
  rw [exC3C4, extremalNumber]
  apply sup_mono
  intro G hG
  simp only [mem_filter, mem_univ, true_and] at hG ⊢
  exact hG.2

/-- **Main theorem.** `ex(n; {C₃, C₄}) ≤ (n / 4) * (1 + √(4n - 3))`. -/
theorem exC3C4_le (n : ℕ) : (exC3C4 n : ℝ) ≤ n / 4 * (1 + √(4 * n - 3)) :=
  (by exact_mod_cast exC3C4_le_extremalNumber n : (exC3C4 n : ℝ) ≤ extremalNumber n _).trans
    (extremalNumber_cycleGraph_four_le n)

/-- **Main theorem.** `ex(n; {C₃, C₄}) ≤ n ^ (3 / 2) / 2 + n / 4`. -/
theorem exC3C4_le_rpow (n : ℕ) : (exC3C4 n : ℝ) ≤ (n : ℝ) ^ ((3 : ℝ) / 2) / 2 + n / 4 := by
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hsq : √(4 * (n : ℝ) - 3) ≤ 2 * √(n : ℝ) := by
    rw [Real.sqrt_le_left (by positivity), mul_pow, Real.sq_sqrt hn]
    linarith
  have hpow : (n : ℝ) ^ ((3 : ℝ) / 2) = n * √(n : ℝ) := by
    rw [show (3 : ℝ) / 2 = 1 + 1 / 2 by norm_num, Real.rpow_add' hn (by norm_num), Real.rpow_one,
      Real.sqrt_eq_rpow]
  calc (exC3C4 n : ℝ) ≤ n / 4 * (1 + √(4 * n - 3)) := exC3C4_le n
    _ ≤ n / 4 * (1 + 2 * √(n : ℝ)) := by gcongr
    _ = (n : ℝ) ^ ((3 : ℝ) / 2) / 2 + n / 4 := by rw [hpow]; ring

end ExtremalNumber

end C3C4Free
