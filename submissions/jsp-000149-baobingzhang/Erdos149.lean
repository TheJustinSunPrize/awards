import Mathlib

/-!
# Erdős Problem 149: `2K₂`-free graphs of bounded degree

The strong chromatic index `sq(G)` of a graph `G` is the least `k` such that the edges of `G` can
be partitioned into `k` sets of *strongly independent* edges, i.e. sets inducing a union of
vertex-disjoint edges. Erdős Problem 149
([erdosproblems.com/149](https://www.erdosproblems.com/149), [Er88, p. 81]) asks whether
`sq(G) ≤ 5Δ²/4` for every graph of maximum degree `Δ`; this is open.
The problem page adds: "Erdős and Nešetřil also asked the easier problem of whether `G` containing
at least `5Δ²/4` many edges implies `G` containing two strongly independent edges. This was proved
by Chung, Gyárfás, Tuza, and Trotter [CGTT90]." This file formalizes that theorem of [CGTT90].

**Wording.** Read literally ("at least"), the easier question is false: the blow-up of the
five-cycle `C₅(D)` with all parts of size `D/2` (`D` even) has maximum degree `D`, exactly `5D²/4`
edges and no two strongly independent edges (`Erdos149.erdos_149_easier_at_least_false` uses
`C₅ = C₅(2)`). The statement proved in [CGTT90], and formalized here, is the version with "more than
`5Δ²/4` edges", together with the exact extremal number.

## Main results

Let `f(D) = 5D²/4` for even `D` and `f(D) = (5D² - 2D + 1)/4` for odd `D` (`Erdos149.cgttBound`).

* `Erdos149.card_edgeFinset_le`: **[CGTT90, Theorem 4], upper bound.** If every vertex of `G` has
  degree at most `D` and `G` has no two strongly independent edges, then `|E(G)| ≤ f(D)`.
  `Erdos149.card_edgeFinset_le_maxDegree` is the case `D = Δ(G)`. No connectivity assumption is
  needed and `D` is arbitrary (the paper assumes `G` connected and `D ≥ 2`).
* `Erdos149.erdos_149_easier`: if `|E(G)| > 5Δ(G)²/4`, then `G` has two strongly independent edges.
* `Erdos149.blowup_sizes_extremal`: **sharpness.** `C₅(D)`, the blow-up of `C₅` with parts of sizes
  `⌈D/2⌉, ⌈D/2⌉, ⌊D/2⌋, ⌊D/2⌋, ⌊D/2⌋`, has maximum degree `D`, no two strongly independent edges and
  exactly `f(D)` edges.
* Consequences for Problem 149 itself: a graph with no two strongly independent edges has a strong
  edge colouring with `f(Δ) ≤ 5Δ²/4` colours (`Erdos149.exists_isStrongEdgeColoring`,
  `Erdos149.four_mul_cgttBound_le`), and every strong edge colouring of `C₅(D)` uses at least
  `f(D)` colours (`Erdos149.card_le_of_isStrongEdgeColoring_blowup`), so `5/4` cannot be lowered.

formal-conjectures has no file for Problem 149 (checked 2026-09-17), so `StronglyIndependent` and
`IsStrongEdgeColoring` are defined here, following the wording of the problem page.

## Proof

Write `2K₂`-free for "no two strongly independent edges" (`Erdos149.Free2K2`,
`Erdos149.free2K2_iff`). Edges are counted through the handshake lemma, and all double counting is
done with sums over vertices. The case split follows Theorem 5 of [CGTT90] by clique number.

* **`G` contains `K₅`** (`good_of_K5`). Fix a `5`-clique `K` (maximality is not needed). Every edge
  outside `K` sees at least `4` vertices of `K` counted with multiplicity (Claim 0). Counting these
  incidences gives `4|E| ≤ 5D² - 5D - 20`.
* **`ω(G) = 4`** (`good_of_K4`). By Theorem 3 (`exists_dominating`: among the `4`-cliques take one
  leaving the fewest non-isolated vertices undominated) there is a dominating `4`-clique. The same
  count leaves the edges between vertices with `1` and `2` neighbours in `K`. By the argument of
  Theorem 1 all of them meet the neighbourhood of one vertex, so there are at most `(D - 1)(D - 2)`
  of them. This gives `4|E| ≤ 5D² - 3D - 10`.
* **`ω(G) = 3`** (`Ctx.false`). Take a dominating triangle `K` and assume `|E| > f(D)`. Let `Y` be
  the non-isolated vertices outside `K` and `A(x)` the vertices whose only neighbour in `K` is `x`.
  Claims 1-3 of [CGTT90] give `|Y| > (5D-8)/2`, `|A(x)| > D/2` and fewer than `(D-4)/2` vertices
  with two neighbours in `K`. Claims 4-5 give an
  edge between any two sets `A(x)`, `A(y)`. The neighbourhoods into `A(y)` of the vertices of `A(x)`
  are nested (Claim 6, `Ctx.chain`), and Claim 7 (`Ctx.claim7`) yields two linked sets. Linked
  `A(x)`, `A(y)` put all but the doubly attached vertices into two neighbourhoods, a contradiction
  (`Ctx.final`).
* **Triangle-free** (`good_of_triangleFree`). The paper uses a shortest odd cycle. Here we fix an
  edge `xy` instead. If some vertex `r ∉ N(x) ∪ N(y)` has neighbours `u ∈ N(x)` and `v ∈ N(y)`, then
  `x u r v y` is an induced five-cycle. Every non-isolated vertex then lies in one of the sets
  `A_i = N(c_{i-1}) ∩ N(c_{i+1})` (Theorem 2), with neighbours only in `A_{i±1}`, and
  `a_{i-1} + a_{i+1} ≤ D`. The inequality `2|E| ≤ ∑ aᵢ (a_{i-1} + a_{i+1})` is then optimized over
  integers (`arith5`). Otherwise `N(x)` together with the vertices outside `N(x) ∪ N(y)` adjacent
  to `N(y)` is an independent set meeting every edge, and the argument of Theorem 1 gives
  `|E| ≤ D²`.

The uniqueness of the extremal graphs, also proved in [CGTT90], is not formalized.

## References

* [CGTT90] Chung, F. R. K., Gyárfás, A., Tuza, Zs. and Trotter, W. T., _The maximum number of edges
  in `2K₂`-free graphs of bounded degree_. Discrete Math. 81 (1990), 129-135.
* [Er88] Erdős, P., _Problems and results in combinatorial analysis and graph theory_. Discrete
  Math. 72 (1988), 81-92.
* [erdosproblems.com/149](https://www.erdosproblems.com/149)
-/

open Finset

namespace Erdos149

section Definitions

variable {V : Type*}

/-- Two edges `e₁`, `e₂` of `G` are *strongly independent* if the subgraph of `G` induced by their
endpoints consists of the two edges only: they are vertex-disjoint and no edge of `G` joins an
endpoint of `e₁` to an endpoint of `e₂`. -/
def StronglyIndependent (G : SimpleGraph V) (e₁ e₂ : Sym2 V) : Prop :=
  e₁ ∈ G.edgeSet ∧ e₂ ∈ G.edgeSet ∧ ∀ v ∈ e₁, ∀ w ∈ e₂, v ≠ w ∧ ¬G.Adj v w

/-- A *strong edge colouring* of `G`: any two distinct edges of the same colour are strongly
independent. The strong chromatic index `sq(G)` is the least number of colours of such a
colouring. -/
def IsStrongEdgeColoring (G : SimpleGraph V) {α : Type*} (c : G.edgeSet → α) : Prop :=
  ∀ e₁ e₂ : G.edgeSet, e₁ ≠ e₂ → c e₁ = c e₂ → StronglyIndependent G e₁ e₂

/-- `f(D)` from [CGTT90]: `5D²/4` for even `D` and `(5D² - 2D + 1)/4` for odd `D`. -/
def cgttBound (D : ℕ) : ℕ := if Even D then 5 * D ^ 2 / 4 else (5 * D ^ 2 - 2 * D + 1) / 4

end Definitions

/-! ### Basic counting -/

section Proof

variable {V : Type*} [Fintype V]

/-- `G` is `2K₂`-free: for any two edges `ab`, `cd` on four distinct vertices, some edge of `G`
joins them. Equivalent to having no two strongly independent edges (`free2K2_iff`). -/
def Free2K2 (G : SimpleGraph V) : Prop :=
  ∀ a b c d, G.Adj a b → G.Adj c d → a ≠ c → a ≠ d → b ≠ c → b ≠ d →
    G.Adj a c ∨ G.Adj a d ∨ G.Adj b c ∨ G.Adj b d

variable {G : SimpleGraph V} [DecidableRel G.Adj]

lemma degree_eq_sum (v : V) : G.degree v = ∑ u, if G.Adj v u then 1 else 0 := by
  rw [← G.card_neighborFinset_eq_degree, G.neighborFinset_eq_filter, card_filter]

lemma sum_ite_const (p : V → Prop) [DecidablePred p] (c : ℕ) :
    (∑ u, if p u then c else 0) = (∑ u, if p u then 1 else 0) * c := by
  rw [sum_mul]
  apply sum_congr rfl
  intro u _
  split_ifs <;> simp

/-- If every edge has an endpoint satisfying `S`, then `|E| ≤ ∑_{S v} d(v)`. -/
lemma card_edges_le_of_cover (S : V → Prop) [DecidablePred S]
    (hS : ∀ v u, G.Adj v u → S v ∨ S u) :
    #G.edgeFinset ≤ ∑ v, if S v then G.degree v else 0 := by
  have h2 := G.sum_degrees_eq_twice_card_edges
  have key : ∑ v, G.degree v ≤ ∑ v, ∑ u, ((if G.Adj v u ∧ S v then 1 else 0) +
      (if G.Adj u v ∧ S u then 1 else 0)) := by
    apply sum_le_sum
    intro v _
    rw [degree_eq_sum]
    apply sum_le_sum
    intro u _
    by_cases h : G.Adj v u
    · have h' : G.Adj u v := h.symm
      rcases hS v u h with hs | hs <;> simp [h, h', hs]
    · simp [h]
  rw [sum_congr rfl (fun v _ => sum_add_distrib), sum_add_distrib] at key
  rw [sum_comm (f := fun v u => if G.Adj u v ∧ S u then 1 else 0)] at key
  have e1 : ∀ v, (∑ u, if G.Adj v u ∧ S v then 1 else 0) = if S v then G.degree v else 0 := by
    intro v
    by_cases hs : S v
    · simp [hs, degree_eq_sum]
    · simp [hs]
  simp only [e1] at key
  omega

lemma card_edges_eq_zero_of_forall (h : ∀ v u, ¬ G.Adj v u) : #G.edgeFinset = 0 := by
  have := card_edges_le_of_cover (G := G) (fun _ => False) (fun v u huv => (h v u huv).elim)
  simpa using this

/-- Theorem 1 of [CGTT90] in the bipartite setting: `|E| ≤ D²`. -/
lemma card_edges_le_sq_of_bipartite (hfree : Free2K2 G) (D : ℕ) (hD : ∀ v, G.degree v ≤ D)
    (A : V → Prop) [DecidablePred A] (hAind : ∀ v u, A v → A u → ¬ G.Adj v u)
    (hAcov : ∀ v u, G.Adj v u → A v ∨ A u) : #G.edgeFinset ≤ D ^ 2 := by
  by_cases hne : ∃ v u, G.Adj v u
  · obtain ⟨v, u, hvu⟩ := hne
    have hBne : (univ.filter (fun w => ¬ A w)).Nonempty := by
      rcases hAcov v u hvu with h | h
      · exact ⟨u, by simpa using fun hu => hAind v u h hu hvu⟩
      · exact ⟨v, by simpa using fun hv => hAind v u hv h hvu⟩
    obtain ⟨b, hb, hbmax⟩ := exists_max_image _ (fun w => G.degree w) hBne
    simp only [mem_filter, mem_univ, true_and] at hb hbmax
    have hcov : ∀ v u, G.Adj v u → G.Adj b v ∨ G.Adj b u := by
      intro v u hvu
      by_contra hcon
      obtain ⟨hbv, hbu⟩ := not_or.mp hcon
      clear hcon
      -- orient the edge so that `v ∈ A`, `u ∉ A`
      wlog hv : A v generalizing v u
      · have hu : A u := (hAcov v u hvu).resolve_left hv
        exact this u v hvu.symm hbu hbv hu
      have hu : ¬ A u := fun hu => hAind v u hv hu hvu
      have hlt : G.degree b < G.degree u := by
        rw [degree_eq_sum, degree_eq_sum]
        apply sum_lt_sum
        · intro w _
          by_cases hbw : G.Adj b w
          · have hw : A w := (hAcov b w hbw).resolve_left hb
            have hbu' : b ≠ u := fun h => hbv (h ▸ hvu.symm)
            have hbv' : b ≠ v := fun h => hb (h ▸ hv)
            have hwu : w ≠ u := fun h => hu (h ▸ hw)
            have hwv : w ≠ v := fun h => hbv (h ▸ hbw)
            rcases hfree b w u v hbw hvu.symm hbu' hbv' hwu hwv with h | h | h | h
            · exact absurd h hbu
            · exact absurd h hbv
            · simp [hbw, h.symm]
            · exact absurd h (hAind w v hw hv)
          · simp [hbw]
        · exact ⟨v, mem_univ _, by simp [hbv, hvu.symm]⟩
      exact absurd (hbmax u hu) (not_le.mpr hlt)
    calc #G.edgeFinset ≤ ∑ v, if G.Adj b v then G.degree v else 0 :=
          card_edges_le_of_cover _ hcov
      _ ≤ ∑ v, if G.Adj b v then D else 0 := by
          apply sum_le_sum
          intro w _
          split_ifs
          · exact hD w
          · exact le_rfl
      _ = G.degree b * D := by rw [sum_ite_const, ← degree_eq_sum]
      _ ≤ D * D := Nat.mul_le_mul_right D (hD b)
      _ = D ^ 2 := by ring
  · simp [card_edges_eq_zero_of_forall (fun v u h => hne ⟨v, u, h⟩)]

/-! ### The optimization for blow-ups of `C₅` -/

lemma arith5_tight (e m a0 a1 a2 a3 a4 : ℕ) (c0 : a4 + a1 = 2 * m) (c1 : a0 + a2 = 2 * m + 1)
    (c2 : a1 + a3 = 2 * m + 1) (c3 : a2 + a4 = 2 * m + 1) (c4 : a3 + a0 = 2 * m + 1)
    (he : 2 * e ≤ a0 * (a4 + a1) + a1 * (a0 + a2) + a2 * (a1 + a3) + a3 * (a2 + a4) +
      a4 * (a3 + a0)) :
    4 * e + 2 * (2 * m + 1) ≤ 5 * (2 * m + 1) ^ 2 + 1 := by
  rw [c0, c1, c2, c3, c4] at he
  have ha0 : a0 = m := by omega
  have hsum : a0 + a1 + a2 + a3 + a4 = 5 * m + 2 := by omega
  have hm : (a0 + a1 + a2 + a3 + a4) * m = (5 * m + 2) * m := by rw [hsum]
  subst ha0
  nlinarith

/-- If `a_{i-1} + a_{i+1} ≤ D` for all `i` (indices mod `5`) and
`2e ≤ ∑ aᵢ (a_{i-1} + a_{i+1})`, then `4e ≤ 5D²`, and `4e ≤ 5D² - 2D + 1` for odd `D`. -/
lemma arith5 (e D a0 a1 a2 a3 a4 : ℕ) (h0 : a4 + a1 ≤ D) (h1 : a0 + a2 ≤ D) (h2 : a1 + a3 ≤ D)
    (h3 : a2 + a4 ≤ D) (h4 : a3 + a0 ≤ D)
    (he : 2 * e ≤ a0 * (a4 + a1) + a1 * (a0 + a2) + a2 * (a1 + a3) + a3 * (a2 + a4) +
      a4 * (a3 + a0)) :
    4 * e ≤ 5 * D ^ 2 ∧ (Odd D → 4 * e + 2 * D ≤ 5 * D ^ 2 + 1) := by
  have m0 := Nat.mul_le_mul_left a0 h0
  have m1 := Nat.mul_le_mul_left a1 h1
  have m2 := Nat.mul_le_mul_left a2 h2
  have m3 := Nat.mul_le_mul_left a3 h3
  have m4 := Nat.mul_le_mul_left a4 h4
  have hS : 2 * (a0 + a1 + a2 + a3 + a4) ≤ 5 * D := by omega
  have mS := Nat.mul_le_mul_left D hS
  refine ⟨by nlinarith, ?_⟩
  rintro ⟨m, rfl⟩
  by_cases hs : a0 + a1 + a2 + a3 + a4 ≤ 5 * m + 1
  · have := Nat.mul_le_mul_left (2 * m + 1) hs
    nlinarith
  · have hc : a4 + a1 = 2 * m ∨ a0 + a2 = 2 * m ∨ a1 + a3 = 2 * m ∨ a2 + a4 = 2 * m ∨
        a3 + a0 = 2 * m := by omega
    rcases hc with c | c | c | c | c
    · exact arith5_tight e m a0 a1 a2 a3 a4 c (by omega) (by omega) (by omega) (by omega) he
    · exact arith5_tight e m a1 a2 a3 a4 a0 c (by omega) (by omega) (by omega) (by omega)
        (by linarith)
    · exact arith5_tight e m a2 a3 a4 a0 a1 c (by omega) (by omega) (by omega) (by omega)
        (by linarith)
    · exact arith5_tight e m a3 a4 a0 a1 a2 c (by omega) (by omega) (by omega) (by omega)
        (by linarith)
    · exact arith5_tight e m a4 a0 a1 a2 a3 c (by omega) (by omega) (by omega) (by omega)
        (by linarith)

/-! ### Triangle-free graphs containing an induced five-cycle -/

section C5

variable {c0 c1 c2 c3 c4 : V}

/-- The number of common neighbours of `a` and `b`. -/
def pairCount (G : SimpleGraph V) [DecidableRel G.Adj] (a b : V) : ℕ :=
  ∑ u, if G.Adj u a ∧ G.Adj u b then 1 else 0

omit [Fintype V] in
/-- A vertex adjacent to `c0` in an induced five-cycle `c0 c1 c2 c3 c4` is also adjacent to `c2`
or to `c3`. -/
lemma c5_step (hfree : Free2K2 G) (h23 : G.Adj c2 c3) (n02 : ¬G.Adj c0 c2)
    (n30 : ¬G.Adj c3 c0) {v : V} (hv : G.Adj v c0) :
    (G.Adj v c0 ∧ G.Adj v c2) ∨ (G.Adj v c3 ∧ G.Adj v c0) := by
  by_cases h2 : G.Adj v c2
  · exact Or.inl ⟨hv, h2⟩
  by_cases h3 : G.Adj v c3
  · exact Or.inr ⟨h3, hv⟩
  exfalso
  have d1 : v ≠ c2 := fun h => by subst h; exact n02 hv.symm
  have d2 : v ≠ c3 := fun h => by subst h; exact n30 hv
  have d3 : c0 ≠ c2 := fun h => by subst h; exact n30 h23.symm
  have d4 : c0 ≠ c3 := fun h => by subst h; exact n02 h23.symm
  rcases hfree v c0 c2 c3 hv h23 d1 d2 d3 d4 with h | h | h | h
  · exact h2 h
  · exact h3 h
  · exact n02 h
  · exact n30 h.symm

omit [Fintype V] in
/-- Theorem 2 of [CGTT90]: in a triangle-free `2K₂`-free graph with an induced five-cycle, every
non-isolated vertex lies in one of the sets `A_i = N(c_{i-1}) ∩ N(c_{i+1})`. -/
lemma c5_cover (hfree : Free2K2 G) (htri : ∀ a b c, G.Adj a b → G.Adj b c → G.Adj a c → False)
    (h01 : G.Adj c0 c1) (h12 : G.Adj c1 c2) (h23 : G.Adj c2 c3) (h34 : G.Adj c3 c4)
    (h40 : G.Adj c4 c0) (n02 : ¬G.Adj c0 c2) (n13 : ¬G.Adj c1 c3) (n24 : ¬G.Adj c2 c4)
    (n30 : ¬G.Adj c3 c0) (n41 : ¬G.Adj c4 c1) {v w : V} (hvw : G.Adj v w) :
    (G.Adj v c4 ∧ G.Adj v c1) ∨ (G.Adj v c0 ∧ G.Adj v c2) ∨ (G.Adj v c1 ∧ G.Adj v c3) ∨
      (G.Adj v c2 ∧ G.Adj v c4) ∨ (G.Adj v c3 ∧ G.Adj v c0) := by
  have hsome : G.Adj v c0 ∨ G.Adj v c1 ∨ G.Adj v c2 ∨ G.Adj v c3 ∨ G.Adj v c4 := by
    by_contra hcon
    simp only [not_or] at hcon
    obtain ⟨v0, v1, v2, v3, v4⟩ := hcon
    have edge : ∀ a b, G.Adj a b → ¬G.Adj v a → ¬G.Adj v b → G.Adj w a ∨ G.Adj w b := by
      intro a b hab hva hvb
      have d1 : v ≠ a := fun h => by subst h; exact hvb hab
      have d2 : v ≠ b := fun h => by subst h; exact hva hab.symm
      have d3 : w ≠ a := fun h => by subst h; exact hva hvw
      have d4 : w ≠ b := fun h => by subst h; exact hvb hvw
      rcases hfree v w a b hvw hab d1 d2 d3 d4 with h | h | h | h
      · exact absurd h hva
      · exact absurd h hvb
      · exact Or.inl h
      · exact Or.inr h
    have e0 := edge _ _ h01 v0 v1
    have e1 := edge _ _ h12 v1 v2
    have e2 := edge _ _ h23 v2 v3
    have e3 := edge _ _ h34 v3 v4
    have e4 := edge _ _ h40 v4 v0
    have t0 : ¬(G.Adj w c0 ∧ G.Adj w c1) := fun h => htri w c0 c1 h.1 h01 h.2
    have t1 : ¬(G.Adj w c1 ∧ G.Adj w c2) := fun h => htri w c1 c2 h.1 h12 h.2
    have t2 : ¬(G.Adj w c2 ∧ G.Adj w c3) := fun h => htri w c2 c3 h.1 h23 h.2
    have t3 : ¬(G.Adj w c3 ∧ G.Adj w c4) := fun h => htri w c3 c4 h.1 h34 h.2
    have t4 : ¬(G.Adj w c4 ∧ G.Adj w c0) := fun h => htri w c4 c0 h.1 h40 h.2
    rcases e0 with a | a
    · have b2 := e1.resolve_left (fun b => t0 ⟨a, b⟩)
      have b4 := e3.resolve_left (fun b => t2 ⟨b2, b⟩)
      exact t4 ⟨b4, a⟩
    · have b4 := e4.resolve_right (fun b => t0 ⟨b, a⟩)
      have b2 := e2.resolve_right (fun b => t3 ⟨b, b4⟩)
      exact t1 ⟨a, b2⟩
  rcases hsome with h | h | h | h | h
  · rcases c5_step hfree h23 n02 n30 h with h' | h'
    · exact Or.inr (Or.inl h')
    · exact Or.inr (Or.inr (Or.inr (Or.inr h')))
  · rcases c5_step hfree h34 n13 n41 h with h' | h'
    · exact Or.inr (Or.inr (Or.inl h'))
    · exact Or.inl h'
  · rcases c5_step hfree h40 n24 n02 h with h' | h'
    · exact Or.inr (Or.inr (Or.inr (Or.inl h')))
    · exact Or.inr (Or.inl h')
  · rcases c5_step hfree h01 n30 n13 h with h' | h'
    · exact Or.inr (Or.inr (Or.inr (Or.inr h')))
    · exact Or.inr (Or.inr (Or.inl h'))
  · rcases c5_step hfree h12 n41 n24 h with h' | h'
    · exact Or.inl h'
    · exact Or.inr (Or.inr (Or.inr (Or.inl h')))

omit [Fintype V] in
/-- Neighbours of a vertex of `A_0` lie in `A_4 ∪ A_1`. -/
lemma c5_nbr (hfree : Free2K2 G) (htri : ∀ a b c, G.Adj a b → G.Adj b c → G.Adj a c → False)
    (h01 : G.Adj c0 c1) (h12 : G.Adj c1 c2) (h23 : G.Adj c2 c3) (h34 : G.Adj c3 c4)
    (h40 : G.Adj c4 c0) (n02 : ¬G.Adj c0 c2) (n13 : ¬G.Adj c1 c3) (n24 : ¬G.Adj c2 c4)
    (n30 : ¬G.Adj c3 c0) (n41 : ¬G.Adj c4 c1) {v u : V} (hv : G.Adj v c4 ∧ G.Adj v c1)
    (hvu : G.Adj v u) : (G.Adj u c3 ∧ G.Adj u c0) ∨ (G.Adj u c0 ∧ G.Adj u c2) := by
  rcases c5_cover hfree htri h01 h12 h23 h34 h40 n02 n13 n24 n30 n41 hvu.symm with
    h | h | h | h | h
  · exact (htri u v c1 hvu.symm hv.2 h.2).elim
  · exact Or.inr h
  · exact (htri u v c1 hvu.symm hv.2 h.1).elim
  · exact (htri u v c4 hvu.symm hv.1 h.2).elim
  · exact Or.inl h

/-- `a_4 + a_1 ≤ D`, as both sets lie in the neighbourhood of `c0`. -/
lemma c5_size (htri : ∀ a b c, G.Adj a b → G.Adj b c → G.Adj a c → False)
    (h23 : G.Adj c2 c3) (D : ℕ) (hD : ∀ v, G.degree v ≤ D) :
    pairCount G c3 c0 + pairCount G c0 c2 ≤ D := by
  unfold pairCount
  rw [← sum_add_distrib]
  refine le_trans ?_ (hD c0)
  rw [degree_eq_sum]
  apply sum_le_sum
  intro u _
  by_cases h1 : G.Adj u c3 ∧ G.Adj u c0
  · by_cases h2 : G.Adj u c0 ∧ G.Adj u c2
    · exact (htri u c2 c3 h2.2 h23 h1.1).elim
    · rw [ite_eq_left h1, ite_eq_right h2, ite_eq_left h1.2.symm]
  · by_cases h2 : G.Adj u c0 ∧ G.Adj u c2
    · rw [ite_eq_right h1, ite_eq_left h2, ite_eq_left h2.1.symm]
    · rw [ite_eq_right h1, ite_eq_right h2]
      exact Nat.zero_le _

/-- A vertex of `A_0` has degree at most `a_4 + a_1`. -/
lemma c5_degree (hfree : Free2K2 G) (htri : ∀ a b c, G.Adj a b → G.Adj b c → G.Adj a c → False)
    (h01 : G.Adj c0 c1) (h12 : G.Adj c1 c2) (h23 : G.Adj c2 c3) (h34 : G.Adj c3 c4)
    (h40 : G.Adj c4 c0) (n02 : ¬G.Adj c0 c2) (n13 : ¬G.Adj c1 c3) (n24 : ¬G.Adj c2 c4)
    (n30 : ¬G.Adj c3 c0) (n41 : ¬G.Adj c4 c1) {v : V} (hv : G.Adj v c4 ∧ G.Adj v c1) :
    G.degree v ≤ pairCount G c3 c0 + pairCount G c0 c2 := by
  unfold pairCount
  rw [← sum_add_distrib, degree_eq_sum]
  apply sum_le_sum
  intro u _
  by_cases hvu : G.Adj v u
  · rcases c5_nbr hfree htri h01 h12 h23 h34 h40 n02 n13 n24 n30 n41 hv hvu with h | h
    · simp [hvu, h]
    · simp [hvu, h]
  · simp [hvu]

/-- Case (ii) of Theorem 5 in [CGTT90]: a triangle-free `2K₂`-free graph containing an induced
five-cycle is a blow-up of it, and has at most `5D²/4` edges (`(5D² - 2D + 1)/4` for odd `D`). -/
lemma good_of_c5 (hfree : Free2K2 G) (htri : ∀ a b c, G.Adj a b → G.Adj b c → G.Adj a c → False)
    (D : ℕ) (hD : ∀ v, G.degree v ≤ D)
    (h01 : G.Adj c0 c1) (h12 : G.Adj c1 c2) (h23 : G.Adj c2 c3) (h34 : G.Adj c3 c4)
    (h40 : G.Adj c4 c0) (n02 : ¬G.Adj c0 c2) (n13 : ¬G.Adj c1 c3) (n24 : ¬G.Adj c2 c4)
    (n30 : ¬G.Adj c3 c0) (n41 : ¬G.Adj c4 c1) :
    4 * #G.edgeFinset ≤ 5 * D ^ 2 ∧ (Odd D → 4 * #G.edgeFinset + 2 * D ≤ 5 * D ^ 2 + 1) := by
  apply arith5 _ D (pairCount G c4 c1) (pairCount G c0 c2) (pairCount G c1 c3)
    (pairCount G c2 c4) (pairCount G c3 c0)
  · exact c5_size htri h23 D hD
  · exact c5_size htri h34 D hD
  · exact c5_size htri h40 D hD
  · exact c5_size htri h01 D hD
  · exact c5_size htri h12 D hD
  rw [← G.sum_degrees_eq_twice_card_edges]
  have hpt : ∀ v, G.degree v ≤
      (if G.Adj v c4 ∧ G.Adj v c1 then 1 else 0) * (pairCount G c3 c0 + pairCount G c0 c2) +
      (if G.Adj v c0 ∧ G.Adj v c2 then 1 else 0) * (pairCount G c4 c1 + pairCount G c1 c3) +
      (if G.Adj v c1 ∧ G.Adj v c3 then 1 else 0) * (pairCount G c0 c2 + pairCount G c2 c4) +
      (if G.Adj v c2 ∧ G.Adj v c4 then 1 else 0) * (pairCount G c1 c3 + pairCount G c3 c0) +
      (if G.Adj v c3 ∧ G.Adj v c0 then 1 else 0) * (pairCount G c2 c4 + pairCount G c4 c1) := by
    intro v
    by_cases hne : ∃ w, G.Adj v w
    · obtain ⟨w, hw⟩ := hne
      rcases c5_cover hfree htri h01 h12 h23 h34 h40 n02 n13 n24 n30 n41 hw with
        h | h | h | h | h
      · have := c5_degree hfree htri h01 h12 h23 h34 h40 n02 n13 n24 n30 n41 h
        rw [ite_eq_left h]
        omega
      · have := c5_degree hfree htri h12 h23 h34 h40 h01 n13 n24 n30 n41 n02 h
        rw [ite_eq_left h]
        omega
      · have := c5_degree hfree htri h23 h34 h40 h01 h12 n24 n30 n41 n02 n13 h
        rw [ite_eq_left h]
        omega
      · have := c5_degree hfree htri h34 h40 h01 h12 h23 n30 n41 n02 n13 n24 h
        rw [ite_eq_left h]
        omega
      · have := c5_degree hfree htri h40 h01 h12 h23 h34 n41 n02 n13 n24 n30 h
        rw [ite_eq_left h]
        omega
    · have : G.degree v = 0 := by
        rw [degree_eq_sum]
        apply sum_eq_zero
        intro u _
        have : ¬G.Adj v u := fun h => hne ⟨u, h⟩
        simp [this]
      omega
  refine le_trans (sum_le_sum fun v _ => hpt v) ?_
  simp only [sum_add_distrib, ← sum_mul]
  unfold pairCount
  apply le_of_eq
  ring

/-- Cases (i) and (ii) of Theorem 5 in [CGTT90]: the triangle-free case. -/
lemma good_of_triangleFree (hfree : Free2K2 G)
    (htri : ∀ a b c, G.Adj a b → G.Adj b c → G.Adj a c → False)
    (D : ℕ) (hD : ∀ v, G.degree v ≤ D) :
    4 * #G.edgeFinset ≤ 5 * D ^ 2 ∧ (Odd D → 4 * #G.edgeFinset + 2 * D ≤ 5 * D ^ 2 + 1) := by
  have ofSq : #G.edgeFinset ≤ D ^ 2 →
      4 * #G.edgeFinset ≤ 5 * D ^ 2 ∧ (Odd D → 4 * #G.edgeFinset + 2 * D ≤ 5 * D ^ 2 + 1) := by
    intro h
    refine ⟨by nlinarith, fun _ => ?_⟩
    nlinarith [sq_nonneg ((D : ℤ) - 1)]
  by_cases hE : ∃ x y, G.Adj x y
  swap
  · apply ofSq
    simp [card_edges_eq_zero_of_forall (fun v u h => hE ⟨v, u, h⟩)]
  obtain ⟨x, y, hxy⟩ := hE
  by_cases hC : ∃ r u v, ¬G.Adj x r ∧ ¬G.Adj y r ∧ G.Adj x u ∧ G.Adj y v ∧ G.Adj r u ∧ G.Adj r v
  · obtain ⟨r, u, v, hxr, hyr, hxu, hyv, hru, hrv⟩ := hC
    -- the induced five-cycle `x u r v y`
    have n02 : ¬G.Adj x r := hxr
    have n13 : ¬G.Adj u v := fun h => htri u r v hru.symm hrv h
    have n24 : ¬G.Adj r y := fun h => hyr h.symm
    have n30 : ¬G.Adj v x := fun h => htri x y v hxy hyv h.symm
    have n41 : ¬G.Adj y u := fun h => htri y x u hxy.symm hxu h
    exact good_of_c5 hfree htri D hD hxu hru.symm hrv hyv.symm hxy.symm n02 n13 n24 n30 n41
  · apply ofSq
    classical
    refine card_edges_le_sq_of_bipartite hfree D hD
      (fun w => G.Adj x w ∨ (¬G.Adj x w ∧ ¬G.Adj y w ∧ ∃ q, G.Adj y q ∧ G.Adj w q)) ?_ ?_
    · rintro v w (hv | ⟨hxv, hyv, q, hyq, hvq⟩) (hw | ⟨hxw, hyw, q', hyq', hwq'⟩) hvw
      · exact htri x v w hv hvw hw
      · exact hC ⟨w, v, q', hxw, hyw, hv, hyq', hvw.symm, hwq'⟩
      · exact hC ⟨v, w, q, hxv, hyv, hw, hyq, hvw, hvq⟩
      · have d1 : v ≠ x := fun h => by subst h; exact hyv hxy.symm
        have d2 : v ≠ y := fun h => by subst h; exact hxv hxy
        have d3 : w ≠ x := fun h => by subst h; exact hyw hxy.symm
        have d4 : w ≠ y := fun h => by subst h; exact hxw hxy
        rcases hfree v w x y hvw hxy d1 d2 d3 d4 with h | h | h | h
        · exact hxv h.symm
        · exact hyv h.symm
        · exact hxw h.symm
        · exact hyw h.symm
    · intro v w hvw
      by_cases hxv : G.Adj x v
      · exact Or.inl (Or.inl hxv)
      by_cases hxw : G.Adj x w
      · exact Or.inr (Or.inl hxw)
      by_cases hyv : G.Adj y v
      · by_cases hyw : G.Adj y w
        · exact (htri y v w hyv hvw hyw).elim
        · exact Or.inr (Or.inr ⟨hxw, hyw, v, hyv, hvw.symm⟩)
      by_cases hyw : G.Adj y w
      · exact Or.inl (Or.inr ⟨hxv, hyv, w, hyw, hvw⟩)
      have d1 : v ≠ x := fun h => by subst h; exact hyv hxy.symm
      have d2 : v ≠ y := fun h => by subst h; exact hxv hxy
      have d3 : w ≠ x := fun h => by subst h; exact hyw hxy.symm
      have d4 : w ≠ y := fun h => by subst h; exact hxw hxy
      rcases hfree v w x y hvw hxy d1 d2 d3 d4 with h | h | h | h
      · exact (hxv h.symm).elim
      · exact (hyv h.symm).elim
      · exact (hxw h.symm).elim
      · exact (hyw h.symm).elim

end C5

/-! ### Counting around a clique -/

section Clique

variable [DecidableEq V]

/-- The number of neighbours of `v` in `K`. -/
def kdeg (G : SimpleGraph V) [DecidableRel G.Adj] (K : Finset V) (v : V) : ℕ :=
  ∑ x ∈ K, if G.Adj v x then 1 else 0

/-- The number of neighbours of `v` outside `K`. -/
def dout (G : SimpleGraph V) [DecidableRel G.Adj] (K : Finset V) (v : V) : ℕ :=
  ∑ u, if u ∉ K ∧ G.Adj v u then 1 else 0

lemma degree_eq_kdeg_add_dout (K : Finset V) (v : V) :
    G.degree v = kdeg G K v + dout G K v := by
  have h1 : kdeg G K v = ∑ u, if u ∈ K then (if G.Adj v u then 1 else 0) else 0 := by
    rw [kdeg, sum_ite_mem_eq]
  rw [degree_eq_sum, h1, dout, ← sum_add_distrib]
  apply sum_congr rfl
  intro u _
  by_cases hu : u ∈ K <;> by_cases h : G.Adj v u <;> simp [hu, h]

omit [Fintype V] in
lemma kdeg_of_mem {K : Finset V} (hK : G.IsClique (K : Set V)) {v : V} (hv : v ∈ K) :
    kdeg G K v = #K - 1 := by
  have : ∀ x ∈ K, (if G.Adj v x then 1 else 0) = (if x ≠ v then 1 else 0) := by
    intro x hx
    by_cases hxv : x = v
    · subst hxv
      simp
    · simp [hxv, hK hv hx (Ne.symm hxv)]
  rw [kdeg, sum_congr rfl this, ← card_filter, filter_ne', card_erase_of_mem hv]

lemma sum_kdeg_eq_sum_dout (K : Finset V) :
    (∑ v, if v ∉ K then kdeg G K v else 0) = ∑ x ∈ K, dout G K x := by
  simp only [kdeg, dout]
  rw [sum_comm (s := K)]
  apply sum_congr rfl
  intro v _
  by_cases hv : v ∈ K
  · simp [hv]
  · simp [hv, G.adj_comm]

/-- `2|E| = |K|(|K| - 1) + 2 e(K, Y) + 2 e(Y)` for a clique `K` and `Y = V \ K`. -/
lemma two_mul_card_edges_eq {K : Finset V} (hK : G.IsClique (K : Set V)) :
    2 * #G.edgeFinset = #K * (#K - 1) + 2 * (∑ v, if v ∉ K then kdeg G K v else 0) +
      (∑ v, if v ∉ K then dout G K v else 0) := by
  rw [← G.sum_degrees_eq_twice_card_edges]
  have hsplit : ∑ v, G.degree v =
      (∑ v ∈ K, G.degree v) + ∑ v, if v ∉ K then G.degree v else 0 := by
    rw [← sum_ite_mem_eq K, ← sum_add_distrib]
    apply sum_congr rfl
    intro v _
    by_cases hv : v ∈ K <;> simp [hv]
  have hK1 : ∑ v ∈ K, G.degree v = #K * (#K - 1) + ∑ x ∈ K, dout G K x := by
    rw [sum_congr rfl (fun v hv => by rw [degree_eq_kdeg_add_dout K v, kdeg_of_mem hK hv]),
      sum_add_distrib, sum_const, smul_eq_mul]
  have hK2 : (∑ v, if v ∉ K then G.degree v else 0) =
      (∑ v, if v ∉ K then kdeg G K v else 0) + ∑ v, if v ∉ K then dout G K v else 0 := by
    rw [← sum_add_distrib]
    apply sum_congr rfl
    intro v _
    by_cases hv : v ∈ K <;> simp [hv, degree_eq_kdeg_add_dout K v]
  rw [hsplit, hK1, hK2, ← sum_kdeg_eq_sum_dout]
  ring

lemma sum_dout_eq_sum_pairs (K : Finset V) :
    (∑ v, if v ∉ K then dout G K v else 0) =
      ∑ v, ∑ u, if v ∉ K ∧ u ∉ K ∧ G.Adj v u then 1 else 0 := by
  apply sum_congr rfl
  intro v _
  by_cases hv : v ∈ K
  · simp [hv]
  · simp [hv, dout]

/-- Summing a weight over ordered adjacent pairs outside `K`. -/
lemma sum_pairs_eq (K : Finset V) (g : V → ℕ) :
    (∑ v, ∑ u, if v ∉ K ∧ u ∉ K ∧ G.Adj v u then g v + g u else 0) =
      2 * ∑ v, if v ∉ K then g v * dout G K v else 0 := by
  have h1 : ∀ v, (∑ u, if v ∉ K ∧ u ∉ K ∧ G.Adj v u then g v + g u else 0) =
      (∑ u, if v ∉ K ∧ u ∉ K ∧ G.Adj v u then g v else 0) +
        ∑ u, if v ∉ K ∧ u ∉ K ∧ G.Adj v u then g u else 0 := by
    intro v
    rw [← sum_add_distrib]
    apply sum_congr rfl
    intro u _
    split_ifs <;> simp
  simp only [h1, sum_add_distrib]
  have h2 : (∑ v, ∑ u, if v ∉ K ∧ u ∉ K ∧ G.Adj v u then g u else 0) =
      ∑ v, ∑ u, if v ∉ K ∧ u ∉ K ∧ G.Adj v u then g v else 0 := by
    rw [sum_comm]
    apply sum_congr rfl
    intro v _
    apply sum_congr rfl
    intro u _
    by_cases hv : v ∈ K <;> by_cases hu : u ∈ K <;> by_cases h : G.Adj v u <;>
      simp [hv, hu, h, G.adj_comm]
  rw [h2]
  have h3 : ∀ v, (∑ u, if v ∉ K ∧ u ∉ K ∧ G.Adj v u then g v else 0) =
      if v ∉ K then g v * dout G K v else 0 := by
    intro v
    by_cases hv : v ∈ K
    · simp [hv]
    · simp only [hv, not_false_eq_true, true_and, ite_true, dout, mul_sum]
      apply sum_congr rfl
      intro u _
      split_ifs <;> simp
  simp only [h3]
  ring

omit [Fintype V] in
/-- Claim 0 of [CGTT90]: an edge outside a clique `K` sees at least `|K| - 1` vertices of `K`. -/
lemma claim0 (hfree : Free2K2 G) {K : Finset V} (hK : G.IsClique (K : Set V)) {v u : V}
    (hv : v ∉ K) (hu : u ∉ K) (hvu : G.Adj v u) : #K ≤ kdeg G K v + kdeg G K u + 1 := by
  have hM : #(K.filter (fun x => ¬G.Adj v x ∧ ¬G.Adj u x)) ≤ 1 := by
    rw [card_le_one]
    intro x hx y hy
    simp only [mem_filter] at hx hy
    by_contra hxy
    have d1 : x ≠ v := fun h => hv (h ▸ hx.1)
    have d2 : x ≠ u := fun h => hu (h ▸ hx.1)
    have d3 : y ≠ v := fun h => hv (h ▸ hy.1)
    have d4 : y ≠ u := fun h => hu (h ▸ hy.1)
    rcases hfree x y v u (hK hx.1 hy.1 hxy) hvu d1 d2 d3 d4 with h | h | h | h
    · exact hx.2.1 h.symm
    · exact hx.2.2 h.symm
    · exact hy.2.1 h.symm
    · exact hy.2.2 h.symm
  have : #K ≤ kdeg G K v + kdeg G K u + #(K.filter (fun x => ¬G.Adj v x ∧ ¬G.Adj u x)) := by
    rw [card_eq_sum_ones, kdeg, kdeg, card_filter, ← sum_add_distrib, ← sum_add_distrib]
    apply sum_le_sum
    intro x _
    by_cases a : G.Adj v x <;> by_cases b : G.Adj u x <;> simp [a, b]
  omega

/-- Theorem 3 of [CGTT90]: if `ω(G) = p ≥ 3`, then some `p`-clique dominates every
non-isolated vertex. -/
lemma exists_dominating (hfree : Free2K2 G) {p : ℕ} (hp : 3 ≤ p) (hcf : G.CliqueFree (p + 1))
    {K0 : Finset V} (hK0 : G.IsNClique p K0) :
    ∃ K, G.IsNClique p K ∧ ∀ v w, G.Adj v w → v ∈ K ∨ ∃ x ∈ K, G.Adj v x := by
  obtain ⟨K, hKmem, hKmin⟩ := exists_min_image (G.cliqueFinset p)
    (fun K => ∑ v, if v ∉ K ∧ (∃ w, G.Adj v w) ∧ ∀ x ∈ K, ¬G.Adj v x then 1 else 0)
    ⟨K0, SimpleGraph.mem_cliqueFinset_iff.2 hK0⟩
  rw [SimpleGraph.mem_cliqueFinset_iff] at hKmem
  refine ⟨K, hKmem, ?_⟩
  intro z0 y0 hzy
  by_contra hcon
  simp only [not_or, not_exists, not_and] at hcon
  obtain ⟨hz0K, hz0x⟩ := hcon
  have hy0K : y0 ∉ K := fun h => hz0x y0 h hzy
  have hmiss : ∀ x ∈ K, ∀ x' ∈ K, ¬G.Adj y0 x → ¬G.Adj y0 x' → x = x' := by
    intro x hx x' hx' h1 h2
    by_contra hne
    have d1 : z0 ≠ x := fun h => hz0K (h ▸ hx)
    have d2 : z0 ≠ x' := fun h => hz0K (h ▸ hx')
    have d3 : y0 ≠ x := fun h => hy0K (h ▸ hx)
    have d4 : y0 ≠ x' := fun h => hy0K (h ▸ hx')
    rcases hfree z0 y0 x x' hzy (hKmem.isClique hx hx' hne) d1 d2 d3 d4 with h | h | h | h
    · exact hz0x x hx h
    · exact hz0x x' hx' h
    · exact h1 h
    · exact h2 h
  obtain ⟨xi, hxi, hy0xi⟩ : ∃ xi ∈ K, ¬G.Adj y0 xi := by
    by_contra hall
    simp only [not_exists, not_and, not_not] at hall
    exact hcf _ (hKmem.insert hall)
  have hK'clique : G.IsNClique p (insert y0 (K.erase xi)) := by
    refine hKmem.insert_erase (fun w hw => ?_) hxi
    simp only [mem_sdiff, mem_singleton] at hw
    by_contra hyw
    exact hw.2 (hmiss w hw.1 xi hxi hyw hy0xi)
  have hmin := hKmin _ (SimpleGraph.mem_cliqueFinset_iff.2 hK'clique)
  have hcard : 1 < #(K.erase xi) := by
    rw [card_erase_of_mem hxi, hKmem.card_eq]
    omega
  by_cases hv : ∃ v, (v ∉ insert y0 (K.erase xi) ∧ (∃ w, G.Adj v w) ∧
      ∀ x ∈ insert y0 (K.erase xi), ¬G.Adj v x) ∧
      ¬(v ∉ K ∧ (∃ w, G.Adj v w) ∧ ∀ x ∈ K, ¬G.Adj v x)
  · obtain ⟨v, ⟨hvK', ⟨w, hvw⟩, hvx⟩, hvK⟩ := hv
    simp only [not_and, not_forall, not_not] at hvK
    by_cases hvinK : v ∈ K
    · have hvxi : v = xi := by
        by_contra h
        exact hvK' (mem_insert_of_mem (mem_erase.2 ⟨h, hvinK⟩))
      obtain ⟨a, ha, b, hb, hab⟩ := one_lt_card.1 hcard
      have ha' := mem_erase.1 ha
      exact hvx a (mem_insert_of_mem ha) (hKmem.isClique hvinK ha'.2 (hvxi ▸ ha'.1.symm))
    · obtain ⟨x, hxK, hvx'⟩ := hvK hvinK ⟨w, hvw⟩
      have hxxi : x = xi := by
        by_contra h
        exact hvx x (mem_insert_of_mem (mem_erase.2 ⟨h, hxK⟩)) hvx'
      subst hxxi
      have d1 : z0 ≠ x := fun h => hz0K (h ▸ hxK)
      have d2 : z0 ≠ v := fun h => hz0x x hxK (h ▸ hvx')
      have d3 : y0 ≠ x := fun h => hy0K (h ▸ hxK)
      have d4 : y0 ≠ v := fun h => hvK' (h ▸ mem_insert_self _ _)
      rcases hfree z0 y0 x v hzy hvx'.symm d1 d2 d3 d4 with h | h | h | h
      · exact hz0x x hxK h
      · obtain ⟨a, ha, b, hb, hab⟩ := one_lt_card.1 hcard
        have ha' := mem_erase.1 ha
        have hb' := mem_erase.1 hb
        have e1 : z0 ≠ a := fun h => hz0K (h ▸ ha'.2)
        have e2 : z0 ≠ b := fun h => hz0K (h ▸ hb'.2)
        have e3 : v ≠ a := fun h => hvK' (h ▸ mem_insert_of_mem ha)
        have e4 : v ≠ b := fun h => hvK' (h ▸ mem_insert_of_mem hb)
        rcases hfree z0 v a b h (hKmem.isClique ha'.2 hb'.2 hab) e1 e2 e3 e4 with h' | h' | h' | h'
        · exact hz0x a ha'.2 h'
        · exact hz0x b hb'.2 h'
        · exact hvx a (mem_insert_of_mem ha) h'
        · exact hvx b (mem_insert_of_mem hb) h'
      · exact hy0xi h
      · exact hvx y0 (mem_insert_self _ _) h.symm
  · have hv' : ∀ v, (v ∉ insert y0 (K.erase xi) ∧ (∃ w, G.Adj v w) ∧
        ∀ x ∈ insert y0 (K.erase xi), ¬G.Adj v x) →
        (v ∉ K ∧ (∃ w, G.Adj v w) ∧ ∀ x ∈ K, ¬G.Adj v x) :=
      fun v h => by_contra fun hb => hv ⟨v, h, hb⟩
    have hlt : (∑ v, if v ∉ insert y0 (K.erase xi) ∧ (∃ w, G.Adj v w) ∧
        ∀ x ∈ insert y0 (K.erase xi), ¬G.Adj v x then 1 else 0) <
        ∑ v, if v ∉ K ∧ (∃ w, G.Adj v w) ∧ ∀ x ∈ K, ¬G.Adj v x then 1 else 0 := by
      apply sum_lt_sum
      · intro v _
        by_cases h1 : v ∉ insert y0 (K.erase xi) ∧ (∃ w, G.Adj v w) ∧
            ∀ x ∈ insert y0 (K.erase xi), ¬G.Adj v x
        · rw [ite_eq_left h1, ite_eq_left (hv' v h1)]
        · rw [ite_eq_right h1]
          exact Nat.zero_le _
      · refine ⟨z0, mem_univ _, ?_⟩
        have h1 : ¬(z0 ∉ insert y0 (K.erase xi) ∧ (∃ w, G.Adj z0 w) ∧
            ∀ x ∈ insert y0 (K.erase xi), ¬G.Adj z0 x) :=
          fun h => h.2.2 y0 (mem_insert_self _ _) hzy
        have h2 : z0 ∉ K ∧ (∃ w, G.Adj z0 w) ∧ ∀ x ∈ K, ¬G.Adj z0 x :=
          ⟨hz0K, ⟨y0, hzy⟩, hz0x⟩
        rw [ite_eq_right h1, ite_eq_left h2]
        exact Nat.zero_lt_one
    exact absurd hmin (not_le.2 hlt)

lemma sum_kdeg_add_le {p : ℕ} {K : Finset V} (hK : G.IsNClique p K) (D : ℕ)
    (hD : ∀ v, G.degree v ≤ D) :
    (∑ v, if v ∉ K then kdeg G K v else 0) + p * (p - 1) ≤ p * D := by
  rw [sum_kdeg_eq_sum_dout]
  have : ∑ x ∈ K, (dout G K x + (p - 1)) ≤ ∑ x ∈ K, D := by
    apply sum_le_sum
    intro x hx
    have := hD x
    rw [degree_eq_kdeg_add_dout K x, kdeg_of_mem hK.isClique hx, hK.card_eq] at this
    omega
  rw [sum_add_distrib, sum_const, sum_const, smul_eq_mul, smul_eq_mul, hK.card_eq] at this
  exact this

lemma sum_kdeg_mul_dout_le (D : ℕ) (hD : ∀ v, G.degree v ≤ D) (K : Finset V) :
    (∑ v, if v ∉ K then kdeg G K v * dout G K v else 0) ≤
      (D - 1) * ∑ v, if v ∉ K then kdeg G K v else 0 := by
  rw [mul_sum]
  apply sum_le_sum
  intro v _
  by_cases hv : v ∉ K
  · rw [ite_eq_left hv, ite_eq_left hv]
    have := hD v
    rw [degree_eq_kdeg_add_dout K v] at this
    rcases Nat.eq_zero_or_pos (kdeg G K v) with h | h
    · simp [h]
    · rw [mul_comm]
      exact Nat.mul_le_mul_right _ (by omega)
  · rw [ite_eq_right hv, ite_eq_right hv]
    simp

omit [Fintype V] in
lemma kdeg_lt {p : ℕ} (hcf : G.CliqueFree (p + 1)) {K : Finset V} (hK : G.IsNClique p K)
    (v : V) : kdeg G K v < p := by
  by_contra hge
  apply hcf (insert v K)
  apply hK.insert
  intro x hx
  by_contra hvx
  have : kdeg G K v < ∑ x ∈ K, 1 := by
    apply sum_lt_sum
    · intro y _
      split_ifs <;> simp
    · exact ⟨x, hx, by simp [hvx]⟩
  rw [← card_eq_sum_ones, hK.card_eq] at this
  omega

omit [Fintype V] [DecidableEq V] in
lemma one_le_kdeg {K : Finset V} (hdom : ∀ v w, G.Adj v w → v ∈ K ∨ ∃ x ∈ K, G.Adj v x)
    {v w : V} (hv : v ∉ K) (hvw : G.Adj v w) : 1 ≤ kdeg G K v := by
  obtain ⟨x, hx, hvx⟩ := (hdom v w hvw).resolve_left hv
  unfold kdeg
  calc 1 = (fun x => if G.Adj v x then 1 else 0) x := by simp [hvx]
    _ ≤ _ := single_le_sum (f := fun x => if G.Adj v x then 1 else 0)
        (fun _ _ => Nat.zero_le _) hx

lemma degree_pos_of_mem {p : ℕ} {K : Finset V} (hK : G.IsNClique p K) (D : ℕ)
    (hD : ∀ v, G.degree v ≤ D) (hp : 1 ≤ p) : p - 1 ≤ D := by
  obtain ⟨x, hx⟩ : K.Nonempty := by
    rw [← card_pos, hK.card_eq]
    omega
  have := hD x
  rw [degree_eq_kdeg_add_dout K x, kdeg_of_mem hK.isClique hx, hK.card_eq] at this
  omega

/-- Case (iii) of Theorem 5 in [CGTT90], for a `5`-clique. -/
lemma good_of_K5 (hfree : Free2K2 G) (D : ℕ) (hD : ∀ v, G.degree v ≤ D) {K : Finset V}
    (hK : G.IsNClique 5 K) : 4 * #G.edgeFinset + 5 * D + 20 ≤ 5 * D ^ 2 := by
  have hid := two_mul_card_edges_eq hK.isClique
  rw [hK.card_eq] at hid
  have hP := sum_kdeg_add_le hK D hD
  have h1 : 4 * (∑ v, if v ∉ K then dout G K v else 0) ≤
      ∑ v, ∑ u, if v ∉ K ∧ u ∉ K ∧ G.Adj v u then kdeg G K v + kdeg G K u else 0 := by
    rw [sum_dout_eq_sum_pairs, mul_sum]
    apply sum_le_sum
    intro v _
    rw [mul_sum]
    apply sum_le_sum
    intro u _
    by_cases h : v ∉ K ∧ u ∉ K ∧ G.Adj v u
    · rw [ite_eq_left h, ite_eq_left h]
      have := claim0 hfree hK.isClique h.1 h.2.1 h.2.2
      rw [hK.card_eq] at this
      omega
    · rw [ite_eq_right h, ite_eq_right h]
      simp
  rw [sum_pairs_eq] at h1
  have h2 := sum_kdeg_mul_dout_le D hD K
  have hD4 := degree_pos_of_mem hK D hD (by norm_num)
  obtain ⟨d, rfl⟩ : ∃ d, D = d + 4 := ⟨D - 4, by omega⟩
  have e1 : d + 4 - 1 = d + 3 := by omega
  rw [e1] at h2
  have h3 : (d + 3) * (∑ v, if v ∉ K then kdeg G K v else 0) ≤ (d + 3) * (5 * d) :=
    Nat.mul_le_mul_left _ (by omega)
  simp only [show (5 : ℕ) * (5 - 1) = 20 from rfl] at hid hP
  nlinarith

/-- The ordered pairs `(v, u)` outside `K` with `k(v) = 1`, `k(u) = 2`. -/
lemma sum_M_le (hfree : Free2K2 G) (D : ℕ) (hD : ∀ v, G.degree v ≤ D) {K : Finset V}
    (hK : G.IsNClique 4 K) (hdom : ∀ v w, G.Adj v w → v ∈ K ∨ ∃ x ∈ K, G.Adj v x) :
    (∑ v, ∑ u, if v ∉ K ∧ u ∉ K ∧ G.Adj v u ∧ kdeg G K v = 1 ∧ kdeg G K u = 2 then 1 else 0)
      ≤ (D - 1) * (D - 2) := by
  have hstab : ∀ v v', v ∉ K → v' ∉ K → kdeg G K v = 1 → kdeg G K v' = 1 → ¬G.Adj v v' := by
    intro v v' hv hv' h1 h2 hvv'
    have := claim0 hfree hK.isClique hv hv' hvv'
    rw [hK.card_eq] at this
    omega
  by_cases hne : (univ.filter (fun b => b ∉ K ∧ kdeg G K b = 2)).Nonempty
  swap
  · have hzero : ∀ u, ¬(u ∉ K ∧ kdeg G K u = 2) := by
      intro u hu
      exact hne ⟨u, by simpa using hu⟩
    have : (∑ v, ∑ u, if v ∉ K ∧ u ∉ K ∧ G.Adj v u ∧ kdeg G K v = 1 ∧ kdeg G K u = 2
        then 1 else 0) = 0 := by
      apply sum_eq_zero
      intro v _
      apply sum_eq_zero
      intro u _
      have : ¬(v ∉ K ∧ u ∉ K ∧ G.Adj v u ∧ kdeg G K v = 1 ∧ kdeg G K u = 2) :=
        fun h => hzero u ⟨h.2.1, h.2.2.2.2⟩
      rw [ite_eq_right this]
    rw [this]
    exact Nat.zero_le _
  obtain ⟨b, hb, hbmax⟩ := exists_max_image _
    (fun b => ∑ v, if v ∉ K ∧ kdeg G K v = 1 ∧ G.Adj v b then 1 else 0) hne
  simp only [mem_filter, mem_univ, true_and] at hb hbmax
  have hcov : ∀ v u, v ∉ K → u ∉ K → G.Adj v u → kdeg G K v = 1 → kdeg G K u = 2 →
      G.Adj v b ∨ G.Adj u b := by
    intro v u hv hu hvu hkv hku
    by_contra hcon
    obtain ⟨hvb, hub⟩ := not_or.mp hcon
    clear hcon
    have hlt : (∑ w, if w ∉ K ∧ kdeg G K w = 1 ∧ G.Adj w b then 1 else 0) <
        ∑ w, if w ∉ K ∧ kdeg G K w = 1 ∧ G.Adj w u then 1 else 0 := by
      apply sum_lt_sum
      · intro w _
        by_cases hw : w ∉ K ∧ kdeg G K w = 1 ∧ G.Adj w b
        · have d1 : b ≠ u := fun h => hvb (h ▸ hvu)
          have d2 : b ≠ v := fun h => by rw [h] at hb; omega
          have d3 : w ≠ u := fun h => by rw [h] at hw; omega
          have d4 : w ≠ v := fun h => hvb (h ▸ hw.2.2)
          rcases hfree b w u v hw.2.2.symm hvu.symm d1 d2 d3 d4 with h | h | h | h
          · exact absurd h.symm hub
          · exact absurd h.symm hvb
          · rw [ite_eq_left hw, ite_eq_left ⟨hw.1, hw.2.1, h⟩]
          · exact absurd h (hstab w v hw.1 hv hw.2.1 hkv)
        · rw [ite_eq_right hw]
          exact Nat.zero_le _
      · refine ⟨v, mem_univ _, ?_⟩
        rw [ite_eq_right (fun h => hvb h.2.2), ite_eq_left ⟨hv, hkv, hvu⟩]
        exact Nat.zero_lt_one
    exact absurd (hbmax u ⟨hu, hku⟩) (not_le.2 hlt)
  -- regroup the pairs according to the endpoint adjacent to `b`
  have step1 : (∑ v, ∑ u, if v ∉ K ∧ u ∉ K ∧ G.Adj v u ∧ kdeg G K v = 1 ∧ kdeg G K u = 2
      then 1 else 0) ≤
      (∑ v, ∑ u, if v ∉ K ∧ u ∉ K ∧ G.Adj v u ∧ kdeg G K v = 1 ∧ kdeg G K u = 2 ∧ G.Adj v b
        then 1 else 0) +
      (∑ v, ∑ u, if v ∉ K ∧ u ∉ K ∧ G.Adj v u ∧ kdeg G K v = 1 ∧ kdeg G K u = 2 ∧ G.Adj u b
        then 1 else 0) := by
    rw [← sum_add_distrib]
    apply sum_le_sum
    intro v _
    rw [← sum_add_distrib]
    apply sum_le_sum
    intro u _
    by_cases h : v ∉ K ∧ u ∉ K ∧ G.Adj v u ∧ kdeg G K v = 1 ∧ kdeg G K u = 2
    · rcases hcov v u h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2 with h' | h'
      · rw [ite_eq_left h, ite_eq_left ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2, h'⟩]
        exact Nat.le_add_right _ _
      · have h'' : v ∉ K ∧ u ∉ K ∧ G.Adj v u ∧ kdeg G K v = 1 ∧ kdeg G K u = 2 ∧ G.Adj u b :=
          ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2, h'⟩
        rw [ite_eq_left h, ite_eq_left h'']
        exact Nat.le_add_left _ _
    · rw [ite_eq_right h]
      exact Nat.zero_le _
  have step2 : (∑ v, ∑ u, if v ∉ K ∧ u ∉ K ∧ G.Adj v u ∧ kdeg G K v = 1 ∧ kdeg G K u = 2 ∧
      G.Adj v b then 1 else 0) ≤
      ∑ w, if w ∉ K ∧ kdeg G K w = 1 ∧ G.Adj w b then dout G K w else 0 := by
    apply sum_le_sum
    intro v _
    by_cases hv : v ∉ K ∧ kdeg G K v = 1 ∧ G.Adj v b
    · rw [ite_eq_left hv, dout]
      apply sum_le_sum
      intro u _
      by_cases h : v ∉ K ∧ u ∉ K ∧ G.Adj v u ∧ kdeg G K v = 1 ∧ kdeg G K u = 2 ∧ G.Adj v b
      · rw [ite_eq_left h, ite_eq_left ⟨h.2.1, h.2.2.1⟩]
      · rw [ite_eq_right h]
        exact Nat.zero_le _
    · rw [ite_eq_right hv]
      apply le_of_eq
      apply sum_eq_zero
      intro u _
      exact ite_eq_right fun h => hv ⟨h.1, h.2.2.2.1, h.2.2.2.2.2⟩
  have step3 : (∑ v, ∑ u, if v ∉ K ∧ u ∉ K ∧ G.Adj v u ∧ kdeg G K v = 1 ∧ kdeg G K u = 2 ∧
      G.Adj u b then 1 else 0) ≤
      ∑ w, if w ∉ K ∧ kdeg G K w = 2 ∧ G.Adj w b then dout G K w else 0 := by
    rw [sum_comm]
    apply sum_le_sum
    intro u _
    by_cases hu : u ∉ K ∧ kdeg G K u = 2 ∧ G.Adj u b
    · rw [ite_eq_left hu, dout]
      apply sum_le_sum
      intro v _
      by_cases h : v ∉ K ∧ u ∉ K ∧ G.Adj v u ∧ kdeg G K v = 1 ∧ kdeg G K u = 2 ∧ G.Adj u b
      · rw [ite_eq_left h, ite_eq_left ⟨h.1, h.2.2.1.symm⟩]
      · rw [ite_eq_right h]
        exact Nat.zero_le _
    · rw [ite_eq_right hu]
      apply le_of_eq
      apply sum_eq_zero
      intro v _
      exact ite_eq_right fun h => hu ⟨h.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩
  have step4 : (∑ w, if w ∉ K ∧ kdeg G K w = 1 ∧ G.Adj w b then dout G K w else 0) +
      (∑ w, if w ∉ K ∧ kdeg G K w = 2 ∧ G.Adj w b then dout G K w else 0) ≤
      (D - 1) * dout G K b := by
    rw [← sum_add_distrib, dout, mul_sum]
    apply sum_le_sum
    intro w _
    by_cases hw : w ∉ K ∧ G.Adj b w
    · have hk := one_le_kdeg hdom hw.1 hw.2.symm
      have hdw := hD w
      rw [degree_eq_kdeg_add_dout K w] at hdw
      rw [ite_eq_left hw]
      split_ifs <;> omega
    · rw [ite_eq_right hw]
      have h1 : ¬(w ∉ K ∧ kdeg G K w = 1 ∧ G.Adj w b) := fun h => hw ⟨h.1, h.2.2.symm⟩
      have h2 : ¬(w ∉ K ∧ kdeg G K w = 2 ∧ G.Adj w b) := fun h => hw ⟨h.1, h.2.2.symm⟩
      rw [ite_eq_right h1, ite_eq_right h2]
      simp
  have hb2 : dout G K b ≤ D - 2 := by
    have := hD b
    rw [degree_eq_kdeg_add_dout K b, hb.2] at this
    omega
  calc _ ≤ _ := step1
    _ ≤ _ := add_le_add step2 step3
    _ ≤ _ := step4
    _ ≤ (D - 1) * (D - 2) := Nat.mul_le_mul_left _ hb2

/-- Case (iv) of Theorem 5 in [CGTT90], for a dominating `4`-clique when `ω(G) = 4`. -/
lemma good_of_K4 (hfree : Free2K2 G) (D : ℕ) (hD : ∀ v, G.degree v ≤ D) {K : Finset V}
    (hK : G.IsNClique 4 K)
    (hdom : ∀ v w, G.Adj v w → v ∈ K ∨ ∃ x ∈ K, G.Adj v x) :
    4 * #G.edgeFinset + 3 * D + 10 ≤ 5 * D ^ 2 := by
  have hid := two_mul_card_edges_eq hK.isClique
  rw [hK.card_eq] at hid
  have hP := sum_kdeg_add_le hK D hD
  have h1 : 4 * (∑ v, if v ∉ K then dout G K v else 0) ≤
      (∑ v, ∑ u, if v ∉ K ∧ u ∉ K ∧ G.Adj v u then kdeg G K v + kdeg G K u else 0) +
      ((∑ v, ∑ u, if v ∉ K ∧ u ∉ K ∧ G.Adj v u ∧ kdeg G K v = 1 ∧ kdeg G K u = 2
        then 1 else 0) +
      (∑ v, ∑ u, if v ∉ K ∧ u ∉ K ∧ G.Adj v u ∧ kdeg G K v = 2 ∧ kdeg G K u = 1
        then 1 else 0)) := by
    rw [sum_dout_eq_sum_pairs, mul_sum, ← sum_add_distrib, ← sum_add_distrib]
    apply sum_le_sum
    intro v _
    rw [mul_sum, ← sum_add_distrib, ← sum_add_distrib]
    apply sum_le_sum
    intro u _
    by_cases h : v ∉ K ∧ u ∉ K ∧ G.Adj v u
    · rw [ite_eq_left h, ite_eq_left h]
      have h0 := claim0 hfree hK.isClique h.1 h.2.1 h.2.2
      rw [hK.card_eq] at h0
      have hv1 := one_le_kdeg hdom h.1 h.2.2
      have hu1 := one_le_kdeg hdom h.2.1 h.2.2.symm
      have hc : 4 ≤ kdeg G K v + kdeg G K u ∨ (kdeg G K v = 1 ∧ kdeg G K u = 2) ∨
          (kdeg G K v = 2 ∧ kdeg G K u = 1) := by omega
      rcases hc with hc | hc | hc
      · omega
      · rw [ite_eq_left (show v ∉ K ∧ u ∉ K ∧ G.Adj v u ∧ kdeg G K v = 1 ∧ kdeg G K u = 2 from
          ⟨h.1, h.2.1, h.2.2, hc.1, hc.2⟩)]
        omega
      · rw [ite_eq_left (show v ∉ K ∧ u ∉ K ∧ G.Adj v u ∧ kdeg G K v = 2 ∧ kdeg G K u = 1 from
          ⟨h.1, h.2.1, h.2.2, hc.1, hc.2⟩)]
        omega
    · rw [ite_eq_right h, ite_eq_right h]
      have h1 : ¬(v ∉ K ∧ u ∉ K ∧ G.Adj v u ∧ kdeg G K v = 1 ∧ kdeg G K u = 2) :=
        fun h' => h ⟨h'.1, h'.2.1, h'.2.2.1⟩
      have h2 : ¬(v ∉ K ∧ u ∉ K ∧ G.Adj v u ∧ kdeg G K v = 2 ∧ kdeg G K u = 1) :=
        fun h' => h ⟨h'.1, h'.2.1, h'.2.2.1⟩
      rw [ite_eq_right h1, ite_eq_right h2]
      simp
  have hswap : (∑ v, ∑ u, if v ∉ K ∧ u ∉ K ∧ G.Adj v u ∧ kdeg G K v = 2 ∧ kdeg G K u = 1
      then 1 else 0) =
      ∑ v, ∑ u, if v ∉ K ∧ u ∉ K ∧ G.Adj v u ∧ kdeg G K v = 1 ∧ kdeg G K u = 2 then 1 else 0 := by
    rw [sum_comm]
    apply sum_congr rfl
    intro v _
    apply sum_congr rfl
    intro u _
    apply if_congr _ rfl rfl
    constructor
    · rintro ⟨a, b, c, d, e⟩
      exact ⟨b, a, c.symm, e, d⟩
    · rintro ⟨a, b, c, d, e⟩
      exact ⟨b, a, c.symm, e, d⟩
  rw [hswap, sum_pairs_eq] at h1
  have h2 := sum_kdeg_mul_dout_le D hD K
  have hM := sum_M_le hfree D hD hK hdom
  have hD3 := degree_pos_of_mem hK D hD (by norm_num)
  obtain ⟨d, rfl⟩ : ∃ d, D = d + 3 := ⟨D - 3, by omega⟩
  have e1 : d + 3 - 1 = d + 2 := by omega
  have e2 : d + 3 - 2 = d + 1 := by omega
  rw [e1] at h2 hM
  rw [e2] at hM
  have h3 : (d + 2) * (∑ v, if v ∉ K then kdeg G K v else 0) ≤ (d + 2) * (4 * d) :=
    Nat.mul_le_mul_left _ (by omega)
  simp only [show (4 : ℕ) * (4 - 1) = 12 from rfl] at hid hP
  nlinarith

/-! ### Case `ω(G) = 3` -/

omit [Fintype V] in
lemma eq_triple {K : Finset V} (hK3 : #K = 3) {x y z : V} (hx : x ∈ K) (hy : y ∈ K)
    (hz : z ∈ K) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) : K = {x, y, z} := by
  symm
  apply eq_of_subset_of_card_le
  · intro t ht
    simp only [mem_insert, mem_singleton] at ht
    rcases ht with rfl | rfl | rfl <;> assumption
  · rw [hK3, card_insert_of_notMem (by simp [hxy, hxz]), card_pair hyz]

omit [Fintype V] in
lemma kdeg_triple {K : Finset V} (hK3 : #K = 3) {x y z : V} (hx : x ∈ K) (hy : y ∈ K)
    (hz : z ∈ K) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) (v : V) :
    kdeg G K v = (if G.Adj v x then 1 else 0) + (if G.Adj v y then 1 else 0) +
      (if G.Adj v z then 1 else 0) := by
  rw [kdeg, eq_triple hK3 hx hy hz hxy hxz hyz, sum_insert (by simp [hxy, hxz]), sum_pair hyz,
    add_assoc]

omit [Fintype V] in
lemma two_others {K : Finset V} (hK3 : #K = 3) {x : V} (hx : x ∈ K) :
    ∃ y ∈ K, ∃ z ∈ K, y ≠ x ∧ z ≠ x ∧ y ≠ z := by
  have : #(K.erase x) = 2 := by rw [card_erase_of_mem hx, hK3]
  obtain ⟨y, z, hyz, he⟩ := card_eq_two.1 this
  have hy : y ∈ K.erase x := by rw [he]; simp
  have hz : z ∈ K.erase x := by rw [he]; simp
  rw [mem_erase] at hy hz
  exact ⟨y, hy.2, z, hz.2, hy.1, hz.1, hyz⟩

omit [Fintype V] [DecidableEq V] in
lemma exists_adj_of_one_le_kdeg {K : Finset V} {v : V} (h : 1 ≤ kdeg G K v) :
    ∃ p ∈ K, G.Adj v p := by
  by_contra hc
  have : kdeg G K v = 0 := by
    apply sum_eq_zero
    intro p hp
    exact ite_eq_right fun hvp => hc ⟨p, hp, hvp⟩
  omega

/-- `v` is a vertex outside `K` whose only neighbour in `K` is `x`. -/
def sgl (G : SimpleGraph V) [DecidableRel G.Adj] (K : Finset V) (x v : V) : Prop :=
  v ∉ K ∧ kdeg G K v = 1 ∧ G.Adj v x

instance {K : Finset V} {x : V} : DecidablePred (sgl G K x) :=
  fun v => by unfold sgl; infer_instance

/-- The hypotheses of the case `ω(G) = 3` of [CGTT90], assuming more edges than the bound. -/
structure Ctx (G : SimpleGraph V) [DecidableRel G.Adj] (D : ℕ) (K : Finset V) : Prop where
  free : Free2K2 G
  deg : ∀ v, G.degree v ≤ D
  clique : G.IsNClique 3 K
  cf : G.CliqueFree 4
  dom : ∀ v w, G.Adj v w → v ∈ K ∨ ∃ x ∈ K, G.Adj v x
  big : (Even D ∧ 5 * D ^ 2 < 4 * #G.edgeFinset) ∨
    (Odd D ∧ 5 * D ^ 2 + 1 < 4 * #G.edgeFinset + 2 * D)

namespace Ctx

variable {D : ℕ} {K : Finset V}

omit [Fintype V] in
lemma sgl_not_adj {x y v : V} (hx : x ∈ K) (hy : y ∈ K) (hxy : x ≠ y)
    (hv : sgl G K x v) : ¬G.Adj v y := by
  intro hvy
  have hsub : ({x, y} : Finset V) ⊆ K := by
    intro t ht
    simp only [mem_insert, mem_singleton] at ht
    rcases ht with rfl | rfl <;> assumption
  have h1 := sum_le_sum_of_subset (f := fun t => if G.Adj v t then 1 else 0) hsub
  rw [sum_pair hxy] at h1
  have h2 := hv.2.1
  unfold kdeg at h2
  simp only [hv.2.2, hvy, ite_true] at h1
  omega

omit [Fintype V] in
lemma sgl_ne {x y v u : V} (hx : x ∈ K) (hy : y ∈ K) (hxy : x ≠ y) (hv : sgl G K x v)
    (hu : sgl G K y u) : v ≠ u := fun e => sgl_not_adj hx hy hxy hv (e ▸ hu.2.2)

lemma stable (h : Ctx G D K) {x v v' : V} (hx : x ∈ K) (hv : sgl G K x v)
    (hv' : sgl G K x v') : ¬G.Adj v v' := by
  intro hvv'
  obtain ⟨y, hy, z, hz, hyx, hzx, hyz⟩ := two_others h.clique.card_eq hx
  have d1 : v ≠ y := fun e => hv.1 (e ▸ hy)
  have d2 : v ≠ z := fun e => hv.1 (e ▸ hz)
  have d3 : v' ≠ y := fun e => hv'.1 (e ▸ hy)
  have d4 : v' ≠ z := fun e => hv'.1 (e ▸ hz)
  rcases h.free v v' y z hvv' (h.clique.isClique hy hz hyz) d1 d2 d3 d4 with e | e | e | e
  · exact sgl_not_adj hx hy hyx.symm hv e
  · exact sgl_not_adj hx hz hzx.symm hv e
  · exact sgl_not_adj hx hy hyx.symm hv' e
  · exact sgl_not_adj hx hz hzx.symm hv' e

lemma two_le (h : Ctx G D K) : 2 ≤ D :=
  degree_pos_of_mem h.clique D h.deg (by norm_num)

/-- Claim 1 of [CGTT90]: `|Y| > (5D - 8)/2`. -/
lemma F1 (h : Ctx G D K) :
    5 * D < 2 * (∑ v, if v ∉ K ∧ 1 ≤ kdeg G K v then 1 else 0) + 8 := by
  have hP := sum_kdeg_add_le h.clique D h.deg
  simp only [show (3 : ℕ) * (3 - 1) = 6 from rfl] at hP
  have hdeg : ∀ v, G.degree v ≤ (if v ∈ K then D else 0) + (if v ∉ K then kdeg G K v else 0) +
      (if v ∉ K ∧ 1 ≤ kdeg G K v then 1 else 0) * (D - 1) := by
    intro v
    have hv := h.deg v
    by_cases hvK : v ∈ K
    · rw [ite_eq_left hvK]
      omega
    · rw [ite_eq_right hvK, ite_eq_left hvK]
      by_cases hk : 1 ≤ kdeg G K v
      · rw [ite_eq_left ⟨hvK, hk⟩]
        omega
      · have hz : G.degree v = 0 := by
          rw [degree_eq_sum]
          apply sum_eq_zero
          intro u _
          exact ite_eq_right fun hvu => hk (one_le_kdeg h.dom hvK hvu)
        omega
  have hsum := sum_le_sum (fun v (_ : v ∈ univ) => hdeg v)
  rw [sum_add_distrib, sum_add_distrib, ← sum_mul, sum_ite_mem_eq, sum_const, smul_eq_mul,
    h.clique.card_eq, G.sum_degrees_eq_twice_card_edges] at hsum
  have h2 := h.two_le
  by_contra hc
  rcases h.big with ⟨⟨m, rfl⟩, hb⟩ | ⟨⟨m, rfl⟩, hb⟩
  · obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    have e1 : k + 1 + (k + 1) - 1 = 2 * k + 1 := by omega
    rw [e1] at hsum
    have := Nat.mul_le_mul_right (2 * k + 1)
      (show (∑ v, if v ∉ K ∧ 1 ≤ kdeg G K v then 1 else 0) ≤ 5 * k + 1 by omega)
    nlinarith
  · obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    have e1 : 2 * (k + 1) + 1 - 1 = 2 * k + 2 := by omega
    rw [e1] at hsum
    have := Nat.mul_le_mul_right (2 * k + 2)
      (show (∑ v, if v ∉ K ∧ 1 ≤ kdeg G K v then 1 else 0) ≤ 5 * k + 3 by omega)
    nlinarith

/-- Claim 3 of [CGTT90]: `λ₂ < (D - 4)/2`. -/
lemma F2 (h : Ctx G D K) :
    2 * (∑ v, if v ∉ K ∧ kdeg G K v = 2 then 1 else 0) + 4 < D := by
  have hP := sum_kdeg_add_le h.clique D h.deg
  simp only [show (3 : ℕ) * (3 - 1) = 6 from rfl] at hP
  have hF1 := h.F1
  have hpt : ∀ v, (if v ∉ K ∧ 1 ≤ kdeg G K v then 1 else 0) +
      (if v ∉ K ∧ kdeg G K v = 2 then 1 else 0) ≤ if v ∉ K then kdeg G K v else 0 := by
    intro v
    by_cases hv : v ∉ K
    · rw [ite_eq_left hv]
      by_cases a : 1 ≤ kdeg G K v
      · rw [ite_eq_left ⟨hv, a⟩]
        by_cases b : kdeg G K v = 2
        · rw [ite_eq_left ⟨hv, b⟩]
          omega
        · rw [ite_eq_right fun c => b c.2]
          omega
      · rw [ite_eq_right fun c => a c.2]
        by_cases b : kdeg G K v = 2
        · omega
        · rw [ite_eq_right fun c => b c.2]
          omega
    · rw [ite_eq_right hv, ite_eq_right fun c => hv c.1, ite_eq_right fun c => hv c.1]
  have := sum_le_sum (fun v (_ : v ∈ univ) => hpt v)
  rw [sum_add_distrib] at this
  omega

/-- Claim 2 of [CGTT90]: `|A(i)| > D/2`. -/
lemma F3 (h : Ctx G D K) {x : V} (hx : x ∈ K) :
    D < 2 * ∑ v, if sgl G K x v then 1 else 0 := by
  obtain ⟨y, hy, z, hz, hyx, hzx, hyz⟩ := two_others h.clique.card_eq hx
  have hpt : ∀ v, (if v ∉ K ∧ 1 ≤ kdeg G K v then 1 else 0) ≤
      (if v ∉ K ∧ G.Adj y v then 1 else 0) + (if v ∉ K ∧ G.Adj z v then 1 else 0) +
        (if sgl G K x v then 1 else 0) := by
    intro v
    simp only [sgl, kdeg_triple h.clique.card_eq hx hy hz hyx.symm hzx.symm hyz]
    by_cases a : G.Adj v x <;> by_cases b : G.Adj v y <;> by_cases c : G.Adj v z <;>
      by_cases hvK : v ∈ K <;> simp [a, b, c, hvK, G.adj_comm y v, G.adj_comm z v]
  have hsum := sum_le_sum (fun v (_ : v ∈ univ) => hpt v)
  rw [sum_add_distrib, sum_add_distrib] at hsum
  have hdy := h.deg y
  have hdz := h.deg z
  rw [degree_eq_kdeg_add_dout K y, kdeg_of_mem h.clique.isClique hy, h.clique.card_eq] at hdy
  rw [degree_eq_kdeg_add_dout K z, kdeg_of_mem h.clique.isClique hz, h.clique.card_eq] at hdz
  unfold dout at hdy hdz
  have hF1 := h.F1
  omega

lemma nonempty_sgl (h : Ctx G D K) {x : V} (hx : x ∈ K) : ∃ v, sgl G K x v := by
  by_contra hc
  have := h.F3 hx
  have : (∑ v, if sgl G K x v then 1 else 0) = 0 :=
    sum_eq_zero fun v _ => ite_eq_right fun hv => hc ⟨v, hv⟩
  omega

/-- Claim 4 of [CGTT90]: some edge joins two vertices with a single neighbour in `K`. -/
lemma F4 (h : Ctx G D K) :
    ∃ v u, v ∉ K ∧ u ∉ K ∧ G.Adj v u ∧ kdeg G K v = 1 ∧ kdeg G K u = 1 := by
  by_contra hcon
  have hid := two_mul_card_edges_eq h.clique.isClique
  rw [h.clique.card_eq] at hid
  have hP := sum_kdeg_add_le h.clique D h.deg
  simp only [show (3 : ℕ) * (3 - 1) = 6 from rfl] at hP
  have hF2 := h.F2
  have h1 : (∑ v, if v ∉ K then dout G K v else 0) ≤
      ∑ v, ∑ u, if v ∉ K ∧ u ∉ K ∧ G.Adj v u then
        (if kdeg G K v = 2 then 1 else 0) + (if kdeg G K u = 2 then 1 else 0) else 0 := by
    rw [sum_dout_eq_sum_pairs]
    apply sum_le_sum
    intro v _
    apply sum_le_sum
    intro u _
    by_cases hp : v ∉ K ∧ u ∉ K ∧ G.Adj v u
    · rw [ite_eq_left hp, ite_eq_left hp]
      have hv1 := one_le_kdeg h.dom hp.1 hp.2.2
      have hu1 := one_le_kdeg h.dom hp.2.1 hp.2.2.symm
      have hv3 := kdeg_lt h.cf h.clique v
      have hu3 := kdeg_lt h.cf h.clique u
      have hn : ¬(kdeg G K v = 1 ∧ kdeg G K u = 1) :=
        fun hh => hcon ⟨v, u, hp.1, hp.2.1, hp.2.2, hh.1, hh.2⟩
      split_ifs <;> omega
    · rw [ite_eq_right hp, ite_eq_right hp]
  rw [sum_pairs_eq] at h1
  have h2 : (∑ v, if v ∉ K then (if kdeg G K v = 2 then 1 else 0) * dout G K v else 0) ≤
      (∑ v, if v ∉ K ∧ kdeg G K v = 2 then 1 else 0) * (D - 2) := by
    rw [sum_mul]
    apply sum_le_sum
    intro v _
    by_cases hv : v ∉ K ∧ kdeg G K v = 2
    · rw [ite_eq_left hv.1, ite_eq_left hv.2, ite_eq_left hv]
      have := h.deg v
      rw [degree_eq_kdeg_add_dout K v] at this
      omega
    · by_cases hvK : v ∉ K
      · rw [ite_eq_left hvK, ite_eq_right (fun h2 => hv ⟨hvK, h2⟩), ite_eq_right hv]
        simp
      · rw [ite_eq_right hvK, ite_eq_right hv]
        simp
  obtain ⟨d, rfl⟩ : ∃ d, D = d + 5 := ⟨D - 5, by omega⟩
  have e1 : d + 5 - 2 = d + 3 := by omega
  rw [e1] at h2
  have h3 := Nat.mul_le_mul_right (d + 3)
    (show 2 * (∑ v, if v ∉ K ∧ kdeg G K v = 2 then 1 else 0) ≤ d by omega)
  simp only [show (3 : ℕ) * (3 - 1) = 6 from rfl] at hid
  rcases h.big with ⟨_, hb⟩ | ⟨_, hb⟩ <;> nlinarith

lemma not_full (h : Ctx G D K) {x y z w : V} (hx : x ∈ K) (hy : y ∈ K) (hz : z ∈ K)
    (hxy : x ≠ y) (hwx : ∀ v, sgl G K x v → G.Adj w v) (hwy : ∀ v, sgl G K y v → G.Adj w v)
    (hwz : G.Adj w z) : False := by
  have h3x := h.F3 hx
  have h3y := h.F3 hy
  have hle : (∑ v, if sgl G K x v then 1 else 0) + (∑ v, if sgl G K y v then 1 else 0) +
      (∑ v, if v = z then 1 else 0) ≤ G.degree w := by
    rw [degree_eq_sum, ← sum_add_distrib, ← sum_add_distrib]
    apply sum_le_sum
    intro v _
    by_cases a : sgl G K x v
    · have b : ¬sgl G K y v := fun b => sgl_not_adj hx hy hxy a b.2.2
      have c : v ≠ z := fun e => a.1 (e ▸ hz)
      rw [ite_eq_left a, ite_eq_right b, ite_eq_right c, ite_eq_left (hwx v a)]
    · by_cases b : sgl G K y v
      · have c : v ≠ z := fun e => b.1 (e ▸ hz)
        rw [ite_eq_right a, ite_eq_left b, ite_eq_right c, ite_eq_left (hwy v b)]
      · by_cases c : v = z
        · rw [ite_eq_right a, ite_eq_right b, ite_eq_left c, ite_eq_left (c ▸ hwz)]
        · rw [ite_eq_right a, ite_eq_right b, ite_eq_right c]
          exact Nat.zero_le _
  have hz1 : (∑ v, if v = z then 1 else 0) = 1 := by simp
  have := h.deg w
  omega

lemma chain (h : Ctx G D K) {x y : V} (hx : x ∈ K) (hy : y ∈ K) (hxy : x ≠ y)
    (hcov : ∀ u, sgl G K y u → ∃ v, sgl G K x v ∧ G.Adj v u) :
    ∃ a0, sgl G K x a0 ∧ ∀ u, sgl G K y u → G.Adj a0 u := by
  have hne : (univ.filter (sgl G K x)).Nonempty := by
    obtain ⟨v, hv⟩ := h.nonempty_sgl hx
    exact ⟨v, by simpa using hv⟩
  obtain ⟨a0, ha0, hmax⟩ := exists_max_image _
    (fun a => ∑ u, if sgl G K y u ∧ G.Adj a u then 1 else 0) hne
  simp only [mem_filter, mem_univ, true_and] at ha0 hmax
  refine ⟨a0, ha0, fun u hu => ?_⟩
  by_contra hnot
  obtain ⟨a1, ha1, ha1u⟩ := hcov u hu
  have hlt : (∑ w, if sgl G K y w ∧ G.Adj a0 w then 1 else 0) <
      ∑ w, if sgl G K y w ∧ G.Adj a1 w then 1 else 0 := by
    apply sum_lt_sum
    · intro w _
      by_cases hw : sgl G K y w ∧ G.Adj a0 w
      · rw [ite_eq_left hw]
        have d1 : a0 ≠ a1 := fun e => hnot (e ▸ ha1u)
        have d2 : a0 ≠ u := sgl_ne hx hy hxy ha0 hu
        have d3 : w ≠ a1 := sgl_ne hy hx (Ne.symm hxy) hw.1 ha1
        have d4 : w ≠ u := fun e => hnot (e ▸ hw.2)
        rcases h.free a0 w a1 u hw.2 ha1u d1 d2 d3 d4 with e | e | e | e
        · exact absurd e (h.stable hx ha0 ha1)
        · exact absurd e hnot
        · rw [ite_eq_left ⟨hw.1, e.symm⟩]
        · exact absurd e (h.stable hy hw.1 hu)
      · rw [ite_eq_right hw]
        exact Nat.zero_le _
    · refine ⟨u, mem_univ _, ?_⟩
      rw [ite_eq_right (fun e => hnot e.2), ite_eq_left ⟨hu, ha1u⟩]
      exact Nat.zero_lt_one
  exact absurd (hmax a1 ha1) (not_le.2 hlt)

lemma claim5_core (h : Ctx G D K) {x y z : V} (hx : x ∈ K) (hy : y ∈ K) (hz : z ∈ K)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hno : ∀ v u, sgl G K x v → sgl G K y u → ¬G.Adj v u) {t w : V} (ht : sgl G K x t)
    (hw : sgl G K z w) (htw : G.Adj t w) : False := by
  obtain ⟨y', hy'⟩ := h.nonempty_sgl hy
  have hwy : ∀ v, sgl G K y v → G.Adj w v := by
    intro v hv
    have d1 : t ≠ y := fun e => ht.1 (e ▸ hy)
    have d2 : t ≠ v := sgl_ne hx hy hxy ht hv
    have d3 : w ≠ y := fun e => hw.1 (e ▸ hy)
    have d4 : w ≠ v := sgl_ne hz hy (Ne.symm hyz) hw hv
    rcases h.free t w y v htw hv.2.2.symm d1 d2 d3 d4 with e | e | e | e
    · exact absurd e (sgl_not_adj hx hy hxy ht)
    · exact absurd e (hno t v ht hv)
    · exact absurd e (sgl_not_adj hz hy (Ne.symm hyz) hw)
    · exact e
  have hwx : ∀ v, sgl G K x v → G.Adj w v := by
    intro v hv
    have d1 : v ≠ w := sgl_ne hx hz hxz hv hw
    have d2 : v ≠ y' := sgl_ne hx hy hxy hv hy'
    have d3 : x ≠ w := fun e => hw.1 (e ▸ hx)
    have d4 : x ≠ y' := fun e => hy'.1 (e ▸ hx)
    rcases h.free v x w y' hv.2.2 (hwy y' hy') d1 d2 d3 d4 with e | e | e | e
    · exact e.symm
    · exact absurd e (hno v y' hv hy')
    · exact absurd e.symm (sgl_not_adj hz hx (Ne.symm hxz) hw)
    · exact absurd e.symm (sgl_not_adj hy hx (Ne.symm hxy) hy')
  exact h.not_full hx hy hz hxy hwx hwy hw.2.2

omit [Fintype V] in
lemma third {K : Finset V} (hK3 : #K = 3) {x y : V} (hx : x ∈ K) :
    ∃ z ∈ K, z ≠ x ∧ z ≠ y := by
  obtain ⟨a, ha, b, hb, hax, hbx, hab⟩ := two_others hK3 hx
  by_cases hay : a = y
  · exact ⟨b, hb, hbx, fun e => hab (hay.trans e.symm)⟩
  · exact ⟨a, ha, hax, hay⟩

/-- Claim 5 of [CGTT90]: any two of the sets `A(i)` are joined by an edge. -/
lemma claim5 (h : Ctx G D K) {x y : V} (hx : x ∈ K) (hy : y ∈ K) (hxy : x ≠ y) :
    ∃ v u, sgl G K x v ∧ sgl G K y u ∧ G.Adj v u := by
  by_contra hcon
  have hno : ∀ v u, sgl G K x v → sgl G K y u → ¬G.Adj v u :=
    fun v u hv hu hvu => hcon ⟨v, u, hv, hu, hvu⟩
  have hno' : ∀ v u, sgl G K y v → sgl G K x u → ¬G.Adj v u :=
    fun v u hv hu hvu => hno u v hu hv hvu.symm
  obtain ⟨z, hz, hzx, hzy⟩ := third h.clique.card_eq hx (y := y)
  have hK := eq_triple h.clique.card_eq hx hy hz hxy (Ne.symm hzx) (Ne.symm hzy)
  obtain ⟨v, u, hv, hu, hvu, hkv, hku⟩ := h.F4
  obtain ⟨p, hp, hvp⟩ := exists_adj_of_one_le_kdeg (G := G) (K := K) (v := v) (by omega)
  obtain ⟨q, hq, huq⟩ := exists_adj_of_one_le_kdeg (G := G) (K := K) (v := u) (by omega)
  have hsv : sgl G K p v := ⟨hv, hkv, hvp⟩
  have hsu : sgl G K q u := ⟨hu, hku, huq⟩
  have hp' : p = x ∨ p = y ∨ p = z := by
    rw [hK] at hp
    simpa using hp
  have hq' : q = x ∨ q = y ∨ q = z := by
    rw [hK] at hq
    simpa using hq
  rcases hp' with e1 | e1 | e1 <;> rw [e1] at hsv <;> rcases hq' with e2 | e2 | e2 <;>
    rw [e2] at hsu
  · exact h.stable hx hsv hsu hvu
  · exact hno v u hsv hsu hvu
  · exact h.claim5_core hx hy hz hxy (Ne.symm hzx) (Ne.symm hzy) hno hsv hsu hvu
  · exact hno u v hsu hsv hvu.symm
  · exact h.stable hy hsv hsu hvu
  · exact h.claim5_core hy hx hz (Ne.symm hxy) (Ne.symm hzy) (Ne.symm hzx) hno' hsv hsu hvu
  · exact h.claim5_core hx hy hz hxy (Ne.symm hzx) (Ne.symm hzy) hno hsu hsv hvu.symm
  · exact h.claim5_core hy hx hz (Ne.symm hxy) (Ne.symm hzy) (Ne.symm hzx) hno' hsu hsv hvu.symm
  · exact h.stable hz hsv hsu hvu

/-- Claim 7 of [CGTT90] (core step): if some vertex of `A(y)` has no neighbour in `A(x)`, then
`A(x)` and `A(z)` are linked. -/
lemma claim7 (h : Ctx G D K) {x y z : V} (hx : x ∈ K) (hy : y ∈ K) (hz : z ∈ K)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) {y0 : V} (hy0 : sgl G K y y0)
    (hy0no : ∀ v, sgl G K x v → ¬G.Adj v y0) :
    (∃ a0, sgl G K x a0 ∧ ∀ w, sgl G K z w → G.Adj a0 w) ∧
      (∃ c0, sgl G K z c0 ∧ ∀ v, sgl G K x v → G.Adj c0 v) := by
  obtain ⟨x0, z0, hx0, hz0, hx0z0⟩ := h.claim5 hx hz hxz
  have h1 : G.Adj z0 y0 := by
    have d1 : x0 ≠ y := fun e => hx0.1 (e ▸ hy)
    have d2 : x0 ≠ y0 := sgl_ne hx hy hxy hx0 hy0
    have d3 : z0 ≠ y := fun e => hz0.1 (e ▸ hy)
    have d4 : z0 ≠ y0 := sgl_ne hz hy (Ne.symm hyz) hz0 hy0
    rcases h.free x0 z0 y y0 hx0z0 hy0.2.2.symm d1 d2 d3 d4 with e | e | e | e
    · exact absurd e (sgl_not_adj hx hy hxy hx0)
    · exact absurd e (hy0no x0 hx0)
    · exact absurd e (sgl_not_adj hz hy (Ne.symm hyz) hz0)
    · exact e
  have h2 : ∀ v, sgl G K x v → G.Adj z0 v := by
    intro v hv
    have d1 : z0 ≠ x := fun e => hz0.1 (e ▸ hx)
    have d2 : z0 ≠ v := sgl_ne hz hx (Ne.symm hxz) hz0 hv
    have d3 : y0 ≠ x := fun e => hy0.1 (e ▸ hx)
    have d4 : y0 ≠ v := sgl_ne hy hx (Ne.symm hxy) hy0 hv
    rcases h.free z0 y0 x v h1 hv.2.2.symm d1 d2 d3 d4 with e | e | e | e
    · exact absurd e (sgl_not_adj hz hx (Ne.symm hxz) hz0)
    · exact e
    · exact absurd e (sgl_not_adj hy hx (Ne.symm hxy) hy0)
    · exact absurd e.symm (hy0no v hv)
  obtain ⟨y1, hy1, hz0y1⟩ : ∃ y1, sgl G K y y1 ∧ ¬G.Adj z0 y1 := by
    by_contra hc
    have hall : ∀ v, sgl G K y v → G.Adj z0 v :=
      fun v hv => by_contra fun hn => hc ⟨v, hv, hn⟩
    exact h.not_full hx hy hz hxy h2 hall hz0.2.2
  have h4 : ∀ v, sgl G K x v → G.Adj v y1 := by
    intro v hv
    have d1 : z0 ≠ y1 := sgl_ne hz hy (Ne.symm hyz) hz0 hy1
    have d2 : z0 ≠ y := fun e => hz0.1 (e ▸ hy)
    have d3 : v ≠ y1 := sgl_ne hx hy hxy hv hy1
    have d4 : v ≠ y := fun e => hv.1 (e ▸ hy)
    rcases h.free z0 v y1 y (h2 v hv) hy1.2.2 d1 d2 d3 d4 with e | e | e | e
    · exact absurd e hz0y1
    · exact absurd e (sgl_not_adj hz hy (Ne.symm hyz) hz0)
    · exact e
    · exact absurd e (sgl_not_adj hx hy hxy hv)
  have h5 : ∀ w, sgl G K z w → ∃ v, sgl G K x v ∧ G.Adj v w := by
    intro z1 hz1
    by_contra hc
    have hz1no : ∀ v, sgl G K x v → ¬G.Adj v z1 := fun v hv hvz => hc ⟨v, hv, hvz⟩
    have e1 : G.Adj y1 z1 := by
      have d1 : x0 ≠ z := fun e => hx0.1 (e ▸ hz)
      have d2 : x0 ≠ z1 := sgl_ne hx hz hxz hx0 hz1
      have d3 : y1 ≠ z := fun e => hy1.1 (e ▸ hz)
      have d4 : y1 ≠ z1 := sgl_ne hy hz hyz hy1 hz1
      rcases h.free x0 y1 z z1 (h4 x0 hx0) hz1.2.2.symm d1 d2 d3 d4 with e | e | e | e
      · exact absurd e (sgl_not_adj hx hz hxz hx0)
      · exact absurd e (hz1no x0 hx0)
      · exact absurd e (sgl_not_adj hy hz hyz hy1)
      · exact e
    have e2 : G.Adj y0 z1 := by
      have d1 : y0 ≠ y1 := fun e => hz0y1 (e ▸ h1)
      have d2 : y0 ≠ z1 := sgl_ne hy hz hyz hy0 hz1
      have d3 : z0 ≠ y1 := sgl_ne hz hy (Ne.symm hyz) hz0 hy1
      have d4 : z0 ≠ z1 := fun e => hz1no x0 hx0 (e ▸ hx0z0)
      rcases h.free y0 z0 y1 z1 h1.symm e1 d1 d2 d3 d4 with e | e | e | e
      · exact absurd e (h.stable hy hy0 hy1)
      · exact e
      · exact absurd e hz0y1
      · exact absurd e (h.stable hz hz0 hz1)
    have d1 : y0 ≠ x := fun e => hy0.1 (e ▸ hx)
    have d2 : y0 ≠ x0 := sgl_ne hy hx (Ne.symm hxy) hy0 hx0
    have d3 : z1 ≠ x := fun e => hz1.1 (e ▸ hx)
    have d4 : z1 ≠ x0 := sgl_ne hz hx (Ne.symm hxz) hz1 hx0
    rcases h.free y0 z1 x x0 e2 hx0.2.2.symm d1 d2 d3 d4 with e | e | e | e
    · exact sgl_not_adj hy hx (Ne.symm hxy) hy0 e
    · exact hy0no x0 hx0 e.symm
    · exact sgl_not_adj hz hx (Ne.symm hxz) hz1 e
    · exact hz1no x0 hx0 e.symm
  exact ⟨h.chain hx hz hxz h5, z0, hz0, h2⟩

/-- The final step of case (v) in [CGTT90]: two linked sets `A(x)`, `A(y)` force
`|Y| ≤ 2(D - 1) + λ₂`, contradicting Claims 1 and 3. -/
lemma final (h : Ctx G D K) {x y : V} (hx : x ∈ K) (hy : y ∈ K) (hxy : x ≠ y)
    {a0 b0 : V} (ha0 : sgl G K x a0) (ha0y : ∀ u, sgl G K y u → G.Adj a0 u)
    (hb0 : sgl G K y b0) (hb0x : ∀ v, sgl G K x v → G.Adj b0 v) : False := by
  obtain ⟨z, hz, hzx, hzy⟩ := third h.clique.card_eq hx (y := y)
  have hK := eq_triple h.clique.card_eq hx hy hz hxy (Ne.symm hzx) (Ne.symm hzy)
  have hab := ha0y b0 hb0
  have hpt : ∀ v, (if v ∉ K ∧ 1 ≤ kdeg G K v then 1 else 0) ≤
      (if v ∉ K ∧ kdeg G K v = 2 then 1 else 0) + (if v ∉ K ∧ G.Adj a0 v then 1 else 0) +
        (if v ∉ K ∧ G.Adj b0 v then 1 else 0) := by
    intro v
    by_cases hv : v ∉ K ∧ 1 ≤ kdeg G K v
    · rw [ite_eq_left hv]
      have h3 := kdeg_lt h.cf h.clique v
      by_cases h2 : kdeg G K v = 2
      · rw [ite_eq_left ⟨hv.1, h2⟩]
        omega
      · have h1 : kdeg G K v = 1 := by omega
        obtain ⟨p, hp, hvp⟩ := exists_adj_of_one_le_kdeg hv.2
        have hsp : sgl G K p v := ⟨hv.1, h1, hvp⟩
        have hp' : p = x ∨ p = y ∨ p = z := by
          rw [hK] at hp
          simpa using hp
        have key : G.Adj a0 v ∨ G.Adj b0 v := by
          rcases hp' with e | e | e
          · rw [e] at hsp
            exact Or.inr (hb0x v hsp)
          · rw [e] at hsp
            exact Or.inl (ha0y v hsp)
          · rw [e] at hsp
            have d1 : a0 ≠ z := fun e => ha0.1 (e ▸ hz)
            have d2 : a0 ≠ v := sgl_ne hx hz (Ne.symm hzx) ha0 hsp
            have d3 : b0 ≠ z := fun e => hb0.1 (e ▸ hz)
            have d4 : b0 ≠ v := sgl_ne hy hz (Ne.symm hzy) hb0 hsp
            rcases h.free a0 b0 z v hab hsp.2.2.symm d1 d2 d3 d4 with e | e | e | e
            · exact absurd e (sgl_not_adj hx hz (Ne.symm hzx) ha0)
            · exact Or.inl e
            · exact absurd e (sgl_not_adj hy hz (Ne.symm hzy) hb0)
            · exact Or.inr e
        have hn2 : ¬(v ∉ K ∧ kdeg G K v = 2) := fun c => h2 c.2
        rw [ite_eq_right hn2]
        rcases key with k | k
        · rw [ite_eq_left (show v ∉ K ∧ G.Adj a0 v from ⟨hv.1, k⟩)]
          omega
        · rw [ite_eq_left (show v ∉ K ∧ G.Adj b0 v from ⟨hv.1, k⟩)]
          omega
    · rw [ite_eq_right hv]
      exact Nat.zero_le _
  have hsum := sum_le_sum (fun v (_ : v ∈ univ) => hpt v)
  rw [sum_add_distrib, sum_add_distrib] at hsum
  have hda := h.deg a0
  have hdb := h.deg b0
  rw [degree_eq_kdeg_add_dout K a0, ha0.2.1] at hda
  rw [degree_eq_kdeg_add_dout K b0, hb0.2.1] at hdb
  unfold dout at hda hdb
  have hF1 := h.F1
  have hF2 := h.F2
  omega

/-- Case (v) of Theorem 5 in [CGTT90]: the assumptions of `Ctx` are contradictory. -/
lemma false (h : Ctx G D K) : False := by
  obtain ⟨x, y, z, hxy, hxz, hyz, hK⟩ := card_eq_three.1 h.clique.card_eq
  have hx : x ∈ K := by rw [hK]; simp
  have hy : y ∈ K := by rw [hK]; simp
  have hz : z ∈ K := by rw [hK]; simp
  by_cases h1 : ∃ y0, sgl G K y y0 ∧ ∀ v, sgl G K x v → ¬G.Adj v y0
  · obtain ⟨y0, hy0, hno⟩ := h1
    obtain ⟨⟨a0, ha0, ha0z⟩, ⟨c0, hc0, hc0x⟩⟩ := h.claim7 hx hy hz hxy hxz hyz hy0 hno
    exact h.final hx hz hxz ha0 ha0z hc0 hc0x
  by_cases h2 : ∃ x0, sgl G K x x0 ∧ ∀ u, sgl G K y u → ¬G.Adj u x0
  · obtain ⟨x0, hx0, hno⟩ := h2
    obtain ⟨⟨a0, ha0, ha0z⟩, ⟨c0, hc0, hc0y⟩⟩ :=
      h.claim7 hy hx hz (Ne.symm hxy) hyz hxz hx0 hno
    exact h.final hy hz hyz ha0 ha0z hc0 hc0y
  have hcov1 : ∀ u, sgl G K y u → ∃ v, sgl G K x v ∧ G.Adj v u := fun u hu =>
    by_contra fun hc => h1 ⟨u, hu, fun v hv hvu => hc ⟨v, hv, hvu⟩⟩
  have hcov2 : ∀ v, sgl G K x v → ∃ u, sgl G K y u ∧ G.Adj u v := fun v hv =>
    by_contra fun hc => h2 ⟨v, hv, fun u hu huv => hc ⟨u, hu, huv⟩⟩
  obtain ⟨a0, ha0, ha0y⟩ := h.chain hx hy hxy hcov1
  obtain ⟨b0, hb0, hb0x⟩ := h.chain hy hx (Ne.symm hxy) hcov2
  exact h.final hx hy hxy ha0 ha0y hb0 hb0x

end Ctx

lemma good_of_K3 (hfree : Free2K2 G) (D : ℕ) (hD : ∀ v, G.degree v ≤ D) {K : Finset V}
    (hK : G.IsNClique 3 K) (hcf : G.CliqueFree 4)
    (hdom : ∀ v w, G.Adj v w → v ∈ K ∨ ∃ x ∈ K, G.Adj v x) :
    4 * #G.edgeFinset ≤ 5 * D ^ 2 ∧ (Odd D → 4 * #G.edgeFinset + 2 * D ≤ 5 * D ^ 2 + 1) := by
  have h2 : 2 ≤ D := degree_pos_of_mem hK D hD (by norm_num)
  by_contra hc
  apply Ctx.false (G := G) (D := D) (K := K)
  refine ⟨hfree, hD, hK, hcf, hdom, ?_⟩
  rcases Nat.even_or_odd D with he | ho
  · refine Or.inl ⟨he, ?_⟩
    by_contra h'
    exact hc ⟨by omega, fun ho => ((Nat.not_even_iff_odd.2 ho) he).elim⟩
  · refine Or.inr ⟨ho, ?_⟩
    by_contra h'
    exact hc ⟨by omega, fun _ => by omega⟩

/-- Theorem 4 of [CGTT90], in the form `4|E| ≤ 5D²`, and `4|E| ≤ 5D² - 2D + 1` for odd `D`. -/
theorem four_mul_card_edges_le (hfree : Free2K2 G) (D : ℕ) (hD : ∀ v, G.degree v ≤ D) :
    4 * #G.edgeFinset ≤ 5 * D ^ 2 ∧ (Odd D → 4 * #G.edgeFinset + 2 * D ≤ 5 * D ^ 2 + 1) := by
  by_cases h5 : G.CliqueFree 5
  · by_cases h4 : G.CliqueFree 4
    · by_cases h3 : G.CliqueFree 3
      · apply good_of_triangleFree hfree _ D hD
        intro a b c hab hbc hac
        exact h3 {a, b, c} (SimpleGraph.is3Clique_triple_iff.2 ⟨hab, hac, hbc⟩)
      · simp only [SimpleGraph.CliqueFree, not_forall, not_not] at h3
        obtain ⟨K0, hK0⟩ := h3
        obtain ⟨K, hK, hdom⟩ := exists_dominating hfree le_rfl h4 hK0
        exact good_of_K3 hfree D hD hK h4 hdom
    · simp only [SimpleGraph.CliqueFree, not_forall, not_not] at h4
      obtain ⟨K0, hK0⟩ := h4
      obtain ⟨K, hK, hdom⟩ := exists_dominating hfree (by norm_num) h5 hK0
      have := good_of_K4 hfree D hD hK hdom
      exact ⟨by linarith, fun _ => by linarith⟩
  · simp only [SimpleGraph.CliqueFree, not_forall, not_not] at h5
    obtain ⟨K0, hK0⟩ := h5
    have := good_of_K5 hfree D hD hK0
    exact ⟨by linarith, fun _ => by linarith⟩

end Clique

end Proof

/-! ### The blow-ups of the five-cycle -/

/-- Adjacency in the five-cycle on `Fin 5`. -/
def c5adj (i j : Fin 5) : Prop := i - j = 1 ∨ j - i = 1

instance : DecidableRel c5adj := fun _ _ => inferInstanceAs (Decidable (_ ∨ _))

lemma c5adj_irrefl : ∀ i : Fin 5, ¬c5adj i i := by decide

lemma c5adj_free : ∀ i j k l : Fin 5, c5adj i j → c5adj k l →
    c5adj i k ∨ c5adj i l ∨ c5adj j k ∨ c5adj j l := by decide

/-- The blow-up of `C₅` in which vertex `i` is replaced by an independent set of size `a i`. -/
def blowup (a : Fin 5 → ℕ) : SimpleGraph (Σ i : Fin 5, Fin (a i)) where
  Adj p q := c5adj p.1 q.1
  symm := ⟨fun p q h => by
    unfold c5adj at *
    tauto⟩
  loopless := ⟨fun p h => c5adj_irrefl p.1 h⟩

instance (a : Fin 5 → ℕ) : DecidableRel (blowup a).Adj :=
  fun p q => inferInstanceAs (Decidable (c5adj p.1 q.1))

lemma c5sum (a : Fin 5 → ℕ) (i : Fin 5) :
    (∑ j : Fin 5, if c5adj i j then a j else 0) = a (i + 4) + a (i + 1) := by
  fin_cases i <;> simp (config := { decide := true }) [Fin.sum_univ_five, c5adj] <;> ring

lemma blowup_degree (a : Fin 5 → ℕ) (p : Σ i : Fin 5, Fin (a i)) :
    (blowup a).degree p = a (p.1 + 4) + a (p.1 + 1) := by
  rw [← (blowup a).card_neighborFinset_eq_degree, (blowup a).neighborFinset_eq_filter,
    card_filter, Fintype.sum_sigma, ← c5sum]
  apply sum_congr rfl
  intro j _
  by_cases h : c5adj p.1 j
  · simp [blowup, h]
  · simp [blowup, h]

lemma two_mul_card_edges_blowup (a : Fin 5 → ℕ) :
    2 * #(blowup a).edgeFinset = ∑ i : Fin 5, a i * (a (i + 4) + a (i + 1)) := by
  rw [← (blowup a).sum_degrees_eq_twice_card_edges, Fintype.sum_sigma]
  apply sum_congr rfl
  intro i _
  simp [blowup_degree]

/-- The part sizes of `C₅(D)`: two consecutive parts of size `⌈D/2⌉`, three of size `⌊D/2⌋`. -/
def sizes (D : ℕ) : Fin 5 → ℕ := ![(D + 1) / 2, (D + 1) / 2, D / 2, D / 2, D / 2]

lemma sizes_deg_le (D : ℕ) (i : Fin 5) : sizes D (i + 4) + sizes D (i + 1) ≤ D := by
  fin_cases i <;> simp [sizes] <;> omega

lemma card_edges_blowup_sizes (D : ℕ) : #(blowup (sizes D)).edgeFinset = cgttBound D := by
  have h2 := two_mul_card_edges_blowup (sizes D)
  generalize #(blowup (sizes D)).edgeFinset = e at h2 ⊢
  simp [Fin.sum_univ_five, sizes] at h2
  rcases Nat.even_or_odd' D with ⟨m, rfl | rfl⟩
  · have e1 : (2 * m + 1) / 2 = m := by omega
    have e2 : 2 * m / 2 = m := by omega
    rw [e1, e2] at h2
    have hc : cgttBound (2 * m) = 5 * m ^ 2 := by
      rw [cgttBound, ite_eq_left (even_two_mul m)]
      rw [show 5 * (2 * m) ^ 2 = 4 * (5 * m ^ 2) by ring, Nat.mul_div_cancel_left _ (by norm_num)]
    rw [hc]
    nlinarith
  · have e1 : (2 * m + 1 + 1) / 2 = m + 1 := by omega
    have e2 : (2 * m + 1) / 2 = m := by omega
    rw [e1, e2] at h2
    have hc : cgttBound (2 * m + 1) = 5 * m ^ 2 + 4 * m + 1 := by
      rw [cgttBound, ite_eq_right (Nat.not_even_iff_odd.2 (odd_two_mul_add_one m))]
      rw [show 5 * (2 * m + 1) ^ 2 - 2 * (2 * m + 1) + 1 = 4 * (5 * m ^ 2 + 4 * m + 1) by
        ring_nf; omega, Nat.mul_div_cancel_left _ (by norm_num)]
    rw [hc]
    nlinarith

lemma maxDegree_blowup_sizes (D : ℕ) : (blowup (sizes D)).maxDegree = D := by
  apply le_antisymm
  · apply SimpleGraph.maxDegree_le_of_forall_degree_le
    intro p
    rw [blowup_degree]
    exact sizes_deg_le D p.1
  · rcases Nat.eq_zero_or_pos D with hD | hD
    · simp [hD]
    · have hpos : 0 < sizes D 0 := by simp [sizes]; omega
      have := (blowup (sizes D)).degree_le_maxDegree ⟨0, ⟨0, hpos⟩⟩
      rw [blowup_degree] at this
      generalize (blowup (sizes D)).maxDegree = M at this ⊢
      simp [sizes] at this
      omega

lemma blowup_free (a : Fin 5 → ℕ) : Free2K2 (blowup a) :=
  fun p q r s hpq hrs _ _ _ _ => c5adj_free p.1 q.1 r.1 s.1 hpq hrs

/-! ### Main results -/

section Main

variable {V : Type*} [Fintype V] [DecidableEq V]

omit [Fintype V] [DecidableEq V] in
lemma free2K2_iff (G : SimpleGraph V) : Free2K2 G ↔ ∀ e₁ e₂, ¬StronglyIndependent G e₁ e₂ := by
  constructor
  · intro hfree e₁ e₂ hs
    induction e₁ using Sym2.ind with
    | h a b =>
    induction e₂ using Sym2.ind with
    | h c d =>
    obtain ⟨hab, hcd, h⟩ := hs
    rw [SimpleGraph.mem_edgeSet] at hab hcd
    have hac := h a (Sym2.mem_mk_left a b) c (Sym2.mem_mk_left c d)
    have had := h a (Sym2.mem_mk_left a b) d (Sym2.mem_mk_right c d)
    have hbc := h b (Sym2.mem_mk_right a b) c (Sym2.mem_mk_left c d)
    have hbd := h b (Sym2.mem_mk_right a b) d (Sym2.mem_mk_right c d)
    rcases hfree a b c d hab hcd hac.1 had.1 hbc.1 hbd.1 with e | e | e | e
    · exact hac.2 e
    · exact had.2 e
    · exact hbc.2 e
    · exact hbd.2 e
  · intro h a b c d hab hcd hac had hbc hbd
    by_contra hcon
    simp only [not_or] at hcon
    obtain ⟨nac, nad, nbc, nbd⟩ := hcon
    apply h s(a, b) s(c, d)
    refine ⟨hab, hcd, ?_⟩
    intro v hv w hw
    rw [Sym2.mem_iff] at hv hw
    rcases hv with rfl | rfl <;> rcases hw with rfl | rfl
    · exact ⟨hac, nac⟩
    · exact ⟨had, nad⟩
    · exact ⟨hbc, nbc⟩
    · exact ⟨hbd, nbd⟩

/-- **Chung–Gyárfás–Tuza–Trotter [CGTT90, Theorem 4], upper bound.** A graph with maximum degree at
most `D` and no two strongly independent edges has at most `f(D)` edges, where `f(D) = 5D²/4` for
even `D` and `f(D) = (5D² - 2D + 1)/4` for odd `D`. -/
theorem card_edgeFinset_le (G : SimpleGraph V) [DecidableRel G.Adj] (D : ℕ)
    (hD : ∀ v, G.degree v ≤ D) (h : ∀ e₁ e₂, ¬StronglyIndependent G e₁ e₂) :
    #G.edgeFinset ≤ cgttBound D := by
  obtain ⟨h1, h2⟩ := four_mul_card_edges_le ((free2K2_iff G).2 h) D hD
  unfold cgttBound
  split_ifs with he
  · exact (Nat.le_div_iff_mul_le (by norm_num)).2 (by linarith)
  · have h3 := h2 (Nat.not_even_iff_odd.1 he)
    have h4 : 2 * D ≤ 5 * D ^ 2 := by nlinarith
    exact (Nat.le_div_iff_mul_le (by norm_num)).2 (by omega)

/-- [CGTT90, Theorem 4] with `D = Δ(G)`. -/
theorem card_edgeFinset_le_maxDegree (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : ∀ e₁ e₂, ¬StronglyIndependent G e₁ e₂) : #G.edgeFinset ≤ cgttBound G.maxDegree :=
  card_edgeFinset_le G _ G.degree_le_maxDegree h

/-- **Erdős Problem 149, the question of Erdős and Nešetřil answered by [CGTT90].** A graph with
maximum degree `Δ` and more than `5Δ²/4` edges contains two strongly independent edges. -/
theorem erdos_149_easier (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : (5 / 4 : ℝ) * (G.maxDegree : ℝ) ^ 2 < (#G.edgeFinset : ℝ)) :
    ∃ e₁ e₂, StronglyIndependent G e₁ e₂ := by
  by_contra hc
  have hc' : ∀ e₁ e₂, ¬StronglyIndependent G e₁ e₂ := fun e₁ e₂ he => hc ⟨e₁, e₂, he⟩
  have h4 := (four_mul_card_edges_le ((free2K2_iff G).2 hc') _ G.degree_le_maxDegree).1
  have h5 : (4 : ℝ) * (#G.edgeFinset : ℝ) ≤ 5 * (G.maxDegree : ℝ) ^ 2 := by exact_mod_cast h4
  linarith

omit [Fintype V] [DecidableEq V] in
/-- `f(D) ≤ 5D²/4`. -/
lemma four_mul_cgttBound_le (D : ℕ) : 4 * cgttBound D ≤ 5 * D ^ 2 := by
  unfold cgttBound
  have h1 := Nat.div_mul_le_self (5 * D ^ 2) 4
  have h2 := Nat.div_mul_le_self (5 * D ^ 2 - 2 * D + 1) 4
  split_ifs with he
  · omega
  · have ho := Nat.not_even_iff_odd.1 he
    have hD : 1 ≤ D := ho.pos
    have h3 : 1 * D ≤ D * D := Nat.mul_le_mul_right D hD
    have h4 : D ^ 2 = D * D := sq D
    omega

/-- For graphs with no two strongly independent edges, the conjectured bound
`sq(G) ≤ 5Δ²/4` of Erdős Problem 149 holds: there is a strong edge colouring with `f(Δ)` colours. -/
theorem exists_isStrongEdgeColoring (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : ∀ e₁ e₂, ¬StronglyIndependent G e₁ e₂) :
    ∃ c : G.edgeSet → Fin (cgttBound G.maxDegree), IsStrongEdgeColoring G c := by
  have hle := card_edgeFinset_le_maxDegree G h
  rw [SimpleGraph.edgeFinset_card] at hle
  refine ⟨fun e => Fin.castLE hle (Fintype.equivFin G.edgeSet e), ?_⟩
  intro e₁ e₂ hne heq
  exact absurd ((Fintype.equivFin G.edgeSet).injective (Fin.castLE_injective hle heq)) hne

end Main

/-! ### Sharpness: the graphs `C₅(D)` -/

/-- **[CGTT90], extremal graphs.** `C₅(D)`, the blow-up of the five-cycle with parts of sizes
`⌈D/2⌉, ⌈D/2⌉, ⌊D/2⌋, ⌊D/2⌋, ⌊D/2⌋`, has maximum degree `D`, no two strongly independent edges,
and exactly `f(D)` edges. -/
theorem blowup_sizes_extremal (D : ℕ) :
    (blowup (sizes D)).maxDegree = D ∧
      (∀ e₁ e₂, ¬StronglyIndependent (blowup (sizes D)) e₁ e₂) ∧
      #(blowup (sizes D)).edgeFinset = cgttBound D :=
  ⟨maxDegree_blowup_sizes D, (free2K2_iff _).1 (blowup_free _), card_edges_blowup_sizes D⟩

/-- Every strong edge colouring of `C₅(D)` uses at least `f(D)` colours (`5D²/4` for even `D`),
so the constant `5/4` in Erdős Problem 149 cannot be lowered. -/
theorem card_le_of_isStrongEdgeColoring_blowup (D k : ℕ)
    (c : (blowup (sizes D)).edgeSet → Fin k) (hc : IsStrongEdgeColoring _ c) :
    cgttBound D ≤ k := by
  have hinj : Function.Injective c := by
    intro e₁ e₂ heq
    by_contra hne
    exact (blowup_sizes_extremal D).2.1 _ _ (hc e₁ e₂ hne heq)
  have h := Fintype.card_le_of_injective c hinj
  rwa [Fintype.card_fin, ← SimpleGraph.edgeFinset_card, (blowup_sizes_extremal D).2.2] at h

/-- The wording "at least `5Δ²/4` edges" of the Erdős–Nešetřil question is false as literally
stated: `C₅ = C₅(2)` has `Δ = 2`, exactly `5 = 5·2²/4` edges and no two strongly independent
edges. The correct threshold is "more than `5Δ²/4`" (`erdos_149_easier`). -/
theorem erdos_149_easier_at_least_false :
    ¬∀ (W : Type) [Fintype W] [DecidableEq W] (H : SimpleGraph W) [DecidableRel H.Adj],
      (5 / 4 : ℝ) * (H.maxDegree : ℝ) ^ 2 ≤ (#H.edgeFinset : ℝ) →
        ∃ e₁ e₂, StronglyIndependent H e₁ e₂ := by
  intro h
  obtain ⟨hmax, hfree, hcard⟩ := blowup_sizes_extremal 2
  have h2 : cgttBound 2 = 5 := by decide
  obtain ⟨e₁, e₂, he⟩ := h _ (blowup (sizes 2)) (by rw [hmax, hcard, h2]; norm_num)
  exact hfree e₁ e₂ he

end Erdos149
