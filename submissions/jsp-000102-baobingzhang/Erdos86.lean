import Mathlib

/-!
# Erdős Problem 86: the Brass–Harborth–Nienborg lower bound

Let `f(n)` be the maximum number of edges of a `C₄`-free subgraph of the hypercube `Qₙ`
(which has `n 2^(n-1)` edges). Erdős asked whether `f(n) ≤ (1/2 + o(1)) n 2^(n-1)`; this is open.
[erdosproblems.com/86](https://www.erdosproblems.com/86) records the lower bounds
`f(n) ≥ (1/2 + c/n) n 2^(n-1)` (Erdős) and `f(n) ≥ (1/2 + c/√n) n 2^(n-1)`
(Brass–Harborth–Nienborg), and the upper bounds `0.6068 n 2^(n-1)` (Balogh–Hu–Lidický–Liu) and
`0.60318 n 2^(n-1)` (Baber).

This file proves the Brass–Harborth–Nienborg lower bound:

* `Erdos86.bhn_four_pow`: if `n = 4 ^ r`, then `Qₙ` has a `C₄`-free subgraph with exactly
  `½ (n + √n) 2^(n-1)` edges [BHN95, Theorem].
* `Erdos86.exists_c4Free_subgraph`: for every `n ≥ 1`, `Qₙ` has a `C₄`-free subgraph `H` with
  `4 |E(H)| = 2^n (n + 2^r)`, where `r = ⌊log₄ n⌋` (so `2^r > √n / 2`).
* `Erdos86.erdos_86_lower_bound`: there is `c > 0` (namely `c = 1/4`) such that for every `n ≥ 1`,
  `Qₙ` has a `C₄`-free subgraph with at least `(1/2 + c/√n) n 2^(n-1)` edges; this is the
  Brass–Harborth–Nienborg bound in the form recorded on erdosproblems.com, and it subsumes Erdős's
  `(1/2 + c/n)` bound.

The statements use the formal-conjectures conventions of `FormalConjectures/ErdosProblems/86.lean`:
subgraphs `H ≤ hypercube n` of `hypercube n : SimpleGraph (Fin n → Bool)`, `C₄`-freeness
`¬ cycleGraph 4 ⊑ H`, and edge count `H.edgeSet.ncard`. The definition `SimpleGraph.hypercube`
(with its simp lemma) is copied verbatim from Google DeepMind's formal-conjectures project,
`FormalConjecturesForMathlib/Combinatorics/SimpleGraph/Hypercube.lean`
(Copyright 2026 The Formal Conjectures Authors, Apache License 2.0).

## Construction

We work with *good colourings*: `2`-colourings of the edges of `Q_ι = {0,1}^ι` with no
monochromatic square; the `true` edges then form a `C₄`-free subgraph
(`GoodColoring.not_cycleGraph_four_isContained`). Following the substitution method of
Brass, Harborth and Nienborg (as described in B. Stanton, *A generalization of the methods of
Brass, Harborth, and Nienborg*, arXiv:1405.5957), fix an `a/e/o`-colouring of the edges of `Q₄`
in which `e` and `o` are disjoint perfect matchings and every square contains an `e`-edge and an
`o`-edge (`eDir`, `oDir`; found by computer search, checked here by `decide`). Given a good
colouring of `Q_ι`, colour `Q_{ι × Fin 4}` as follows (`GoodColoring.step`): in block `w`, an
`e`-edge gets the parity of the coordinates outside block `w`, an `o`-edge the opposite parity,
and an `a`-edge the colour of the `w`-edge of `Q_ι` at the vector of block parities. This is again
good, and if every vertex of `Q_ι` has `d` true edges then every vertex of `Q_{ι × Fin 4}` has
`|ι| + 2d` true edges. Starting from `Q₁` with its edge coloured `true`, `Q_{4^r}` gets a good
colouring that is `(4^r + 2^r)/2`-regular in colour `true`, giving `½ (n + √n) 2^(n-1)` edges
(this is the equality case of Bialostocki's bound). For general `n`, further coordinates are added
one at a time, the new direction being coloured by the parity of the old coordinates
(`GoodColoring.extend`).

## References

* [BHN95] P. Brass, H. Harborth and H. Nienborg, *On the maximum number of edges in a
  `C₄`-free subgraph of `Qₙ`*, J. Graph Theory 19 (1995), 17–23.
* [Er91] P. Erdős, *Problems and results in combinatorial analysis and combinatorial number
  theory*, Graph theory, combinatorics, and applications, Vol. 1 (Kalamazoo, MI, 1988) (1991),
  397–406.
-/

namespace SimpleGraph

open scoped Finset

/-- `hypercube n` is the `n`-dimensional hypercube graph `Qₙ`: the vertices are the `n`-bit
vectors, and two vertices are adjacent when they differ in exactly one coordinate. -/
def hypercube (n : ℕ) : SimpleGraph (Fin n → Bool) where
  Adj u v := #{i | u i ≠ v i} = 1
  symm.symm _ _ := by simp [eq_comm]
  loopless.irrefl _ := by simp

@[simp]
theorem hypercube_adj {n : ℕ} {u v : Fin n → Bool} :
    (hypercube n).Adj u v ↔ #{i | u i ≠ v i} = 1 := Iff.rfl

end SimpleGraph

namespace Erdos86

open Finset SimpleGraph

section Flip

variable {ι : Type*} [DecidableEq ι]

/-- Flip the `i`-th coordinate of a bit vector. -/
def flipAt (x : ι → Bool) (i : ι) : ι → Bool := fun t => if t = i then !x t else x t

@[simp] theorem flipAt_self (x : ι → Bool) (i : ι) : flipAt x i i = !x i := by simp [flipAt]

theorem flipAt_of_ne (x : ι → Bool) {i t : ι} (h : t ≠ i) : flipAt x i t = x t := by
  simp [flipAt, h]

@[simp] theorem flipAt_flipAt (x : ι → Bool) (i : ι) : flipAt (flipAt x i) i = x := by
  funext t; by_cases h : t = i <;> simp [flipAt, h]

theorem flipAt_comm (x : ι → Bool) (i j : ι) :
    flipAt (flipAt x i) j = flipAt (flipAt x j) i := by
  funext t; simp only [flipAt]; split_ifs <;> simp_all

theorem flipAt_ne_self (x : ι → Bool) (i : ι) : flipAt x i ≠ x := fun h => by
  have := congrFun h i; simp at this

theorem flipAt_injective (x : ι → Bool) : Function.Injective (flipAt x) := by
  intro i j h
  by_contra hij
  have := congrFun h i
  simp [flipAt, hij] at this

end Flip

section Q4

/-- A perfect matching `e` of `Q₄`, given as the direction of the matching edge at each vertex
(vertex `v` is encoded by its four bits `v 0, v 1, v 2, v 3`). -/
def eDir : Bool → Bool → Bool → Bool → Fin 4
  | false, false, false, false => 0
  | true, false, false, false => 0
  | false, true, false, false => 2
  | true, true, false, false => 3
  | false, false, true, false => 3
  | true, false, true, false => 1
  | false, true, true, false => 2
  | true, true, true, false => 1
  | false, false, false, true => 1
  | true, false, false, true => 2
  | false, true, false, true => 1
  | true, true, false, true => 3
  | false, false, true, true => 3
  | true, false, true, true => 2
  | false, true, true, true => 0
  | true, true, true, true => 0

/-- A second perfect matching `o` of `Q₄`, disjoint from `e`. Every square of `Q₄` contains an
edge of `e` and an edge of `o` (this is what `qcol_good` checks). -/
def oDir : Bool → Bool → Bool → Bool → Fin 4
  | false, false, false, false => 1
  | true, false, false, false => 3
  | false, true, false, false => 1
  | true, true, false, false => 2
  | false, false, true, false => 0
  | true, false, true, false => 0
  | false, true, true, false => 3
  | true, true, true, false => 2
  | false, false, false, true => 2
  | true, false, false, true => 3
  | false, true, false, true => 0
  | true, true, false, true => 0
  | false, false, true, true => 2
  | true, false, true, true => 1
  | false, true, true, true => 3
  | true, true, true, true => 1

/-- The colour of the `Q₄`-edge from `v` in direction `j`: edges of `e` get colour `π`, edges
of `o` get colour `!π`, and all remaining edges (the `a`-edges) get colour `c`. -/
def qcol (v : Fin 4 → Bool) (j : Fin 4) (c π : Bool) : Bool :=
  if eDir (v 0) (v 1) (v 2) (v 3) = j then π
  else if oDir (v 0) (v 1) (v 2) (v 3) = j then !π else c

theorem forall_fin4_bool {P : (Fin 4 → Bool) → Prop} (h : ∀ a b c d, P ![a, b, c, d]) :
    ∀ v, P v := by
  intro v
  have hv : v = ![v 0, v 1, v 2, v 3] := by
    funext j; fin_cases j <;> rfl
  rw [hv]; exact h _ _ _ _

theorem qcol_flipAt (v : Fin 4 → Bool) (j : Fin 4) (c π : Bool) :
    qcol (flipAt v j) j c π = qcol v j c π := by
  revert v
  refine forall_fin4_bool ?_
  revert j c π
  decide

theorem card_qcol (v : Fin 4 → Bool) (c π : Bool) :
    #{j | qcol v j c π = true} = 2 * c.toNat + 1 := by
  revert v
  refine forall_fin4_bool ?_
  revert c π
  decide

theorem qcol_good (v : Fin 4 → Bool) (j k : Fin 4) (c π : Bool) (hjk : j ≠ k) :
    ¬ (qcol v j c π = qcol (flipAt v k) j c π ∧ qcol (flipAt v k) j c π = qcol v k c π ∧
      qcol v k c π = qcol (flipAt v j) k c π) := by
  revert v
  refine forall_fin4_bool ?_
  revert j k c π
  decide

end Q4

section Parity

variable {ι : Type*} [DecidableEq ι]

/-- Whether `x` has an odd number of `true` coordinates inside `S`. -/
def oddOn (S : Finset ι) (x : ι → Bool) : Bool := decide (Odd (∑ t ∈ S, (x t).toNat))

theorem oddOn_flipAt_of_mem {S : Finset ι} (x : ι → Bool) {i : ι} (hi : i ∈ S) :
    oddOn S (flipAt x i) = !oddOn S x := by
  have h1 := Finset.add_sum_erase S (fun t => (flipAt x i t).toNat) hi
  have h2 := Finset.add_sum_erase S (fun t => (x t).toNat) hi
  have h3 : ∑ t ∈ S.erase i, (flipAt x i t).toNat = ∑ t ∈ S.erase i, (x t).toNat :=
    Finset.sum_congr rfl fun t ht => by rw [flipAt_of_ne x (Finset.ne_of_mem_erase ht)]
  rw [oddOn, oddOn, ← h1, ← h2, h3, flipAt_self]
  generalize ∑ t ∈ S.erase i, (x t).toNat = N
  rcases Nat.even_or_odd N with h | h <;>
    cases x i <;> simp [add_comm 1 N, h, Nat.not_odd_iff_even.mpr]

theorem oddOn_flipAt_of_notMem {S : Finset ι} (x : ι → Bool) {i : ι} (hi : i ∉ S) :
    oddOn S (flipAt x i) = oddOn S x := by
  rw [oddOn, oddOn]
  congr 2
  exact Finset.sum_congr rfl fun t ht => by rw [flipAt_of_ne x (by rintro rfl; exact hi ht)]

/-- Exactly half of all bit vectors have odd weight. -/
theorem two_mul_card_oddOn [Fintype ι] [Nonempty ι] :
    2 * #{x : ι → Bool | oddOn univ x = true} = 2 ^ Fintype.card ι := by
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  have hswap :
      #{x : ι → Bool | oddOn univ x = true} = #{x : ι → Bool | ¬ oddOn univ x = true} := by
    refine Finset.card_nbij' (flipAt · i₀) (flipAt · i₀) ?_ ?_ ?_ ?_
    · intro x hx; simp_all [oddOn_flipAt_of_mem x (Finset.mem_univ i₀)]
    · intro x hx; simp_all [oddOn_flipAt_of_mem x (Finset.mem_univ i₀)]
    · intro x _; simp
    · intro x _; simp
  have htot := Finset.card_filter_add_card_filter_not
    (s := (univ : Finset (ι → Bool))) (fun x => oddOn univ x = true)
  rw [Finset.card_univ, Fintype.card_fun, Fintype.card_bool] at htot
  omega

end Parity

section Coloring

/-- A `2`-colouring of the edges of the cube `{0,1}^ι` with no monochromatic square:
`col x i` is the colour of the edge joining `x` and `flipAt x i`. -/
structure GoodColoring (ι : Type*) [DecidableEq ι] where
  /-- The colour of the edge from `x` in direction `i`. -/
  col : (ι → Bool) → ι → Bool
  col_flipAt : ∀ x i, col (flipAt x i) i = col x i
  good : ∀ x i j, i ≠ j →
    ¬ (col x i = col (flipAt x j) i ∧ col (flipAt x j) i = col x j ∧
      col x j = col (flipAt x i) j)

namespace GoodColoring

variable {ι : Type*} [DecidableEq ι] (C : GoodColoring ι)

/-- The subgraph of the cube formed by the `true`-coloured edges. -/
def graph : SimpleGraph (ι → Bool) where
  Adj x y := ∃ i, y = flipAt x i ∧ C.col x i = true
  symm.symm := by
    rintro x y ⟨i, rfl, h⟩
    exact ⟨i, (flipAt_flipAt x i).symm, by rw [C.col_flipAt]; exact h⟩
  loopless.irrefl := by
    rintro x ⟨i, h, -⟩
    exact flipAt_ne_self x i h.symm

theorem graph_adj {x y : ι → Bool} :
    C.graph.Adj x y ↔ ∃ i, y = flipAt x i ∧ C.col x i = true :=
  Iff.rfl

end GoodColoring

end Coloring

section FourCycle

variable {V : Type*} {G : SimpleGraph V}

/-- `G` contains a copy of `C₄` iff it has four pairwise distinct vertices `a, b, c, d` with
`a ~ b ~ c ~ d ~ a`. (Copied from `Jsp/C3C4Free.lean` of this project.) -/
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

end FourCycle

namespace GoodColoring

variable {ι : Type*} [DecidableEq ι] (C : GoodColoring ι)

/-- The `true`-coloured edges of a good colouring contain no `4`-cycle. -/
theorem not_cycleGraph_four_isContained : ¬ cycleGraph 4 ⊑ C.graph := by
  rw [cycleGraph_four_isContained_iff]
  rintro ⟨a, b, c, d, -, hac, -, -, hbd, -, ⟨i, hb, h1⟩, ⟨j, hc, h2⟩, ⟨k, hd, h3⟩, ⟨l, ha, h4⟩⟩
  have hij : i ≠ j := by
    rintro rfl; exact hac (by rw [hc, hb, flipAt_flipAt])
  have hjk : j ≠ k := by
    rintro rfl; exact hbd (by rw [hd, hc, flipAt_flipAt])
  have hkl : k ≠ l := by
    rintro rfl; exact hac (by rw [ha, hd, flipAt_flipAt])
  have hki : k = i := by
    by_contra hki
    have := congrFun ha k
    rw [hd, hc, hb] at this
    simp [flipAt, hkl, hjk.symm, hki] at this
  subst hki
  have hlj : l = j := by
    by_contra hlj
    have := congrFun ha j
    rw [hd, hc, hb] at this
    simp [flipAt, Ne.symm hlj, hjk] at this
  subst hlj
  have hd' : d = flipAt a l := by rw [hd, hc, hb, flipAt_comm, flipAt_flipAt]
  subst hb hc
  apply C.good a k l hij
  have e1 : C.col a k = true := h1
  have e2 : C.col (flipAt a l) k = true := by
    rw [← hd', ← h3, hd, C.col_flipAt]
  have e3 : C.col a l = true := by
    rw [← h4]; conv_lhs => rw [ha]
    exact C.col_flipAt d l
  have e4 : C.col (flipAt a k) l = true := h2
  rw [e1, e2, e3, e4]
  exact ⟨rfl, rfl, rfl⟩

/-- Flipping one coordinate gives an edge of the hypercube. -/
theorem hypercube_adj_flipAt {n : ℕ} (x : Fin n → Bool) (i : Fin n) :
    (hypercube n).Adj x (flipAt x i) := by
  rw [hypercube_adj, Finset.card_eq_one]
  refine ⟨i, ?_⟩
  ext t
  by_cases h : t = i <;> simp [flipAt, h]

theorem graph_le_hypercube {n : ℕ} (C : GoodColoring (Fin n)) : C.graph ≤ hypercube n := by
  rintro x y ⟨i, rfl, -⟩
  exact hypercube_adj_flipAt x i

/-- The degree of `x` in `C.graph` is the number of `true`-coloured directions at `x`. -/
theorem degree_graph [Fintype ι] [DecidableRel C.graph.Adj] (x : ι → Bool) :
    C.graph.degree x = #{i | C.col x i = true} := by
  rw [← card_neighborFinset_eq_degree]
  have : C.graph.neighborFinset x =
      (univ.filter fun i => C.col x i = true).image (flipAt x) := by
    ext y
    simp only [mem_neighborFinset, graph_adj, mem_image, mem_filter, mem_univ, true_and]
    constructor
    · rintro ⟨i, rfl, h⟩; exact ⟨i, h, rfl⟩
    · rintro ⟨i, h, rfl⟩; exact ⟨i, rfl, h⟩
  rw [this, card_image_of_injective _ (flipAt_injective x)]

/-- Handshake lemma for `C.graph`. -/
theorem two_mul_ncard_edgeSet [Fintype ι] :
    2 * C.graph.edgeSet.ncard = ∑ x, #{i | C.col x i = true} := by
  classical
  rw [← coe_edgeFinset, Set.ncard_coe_finset, ← sum_degrees_eq_twice_card_edges]
  exact Finset.sum_congr rfl fun x _ => C.degree_graph x

end GoodColoring

section Step

variable {ι : Type*} [DecidableEq ι] [Fintype ι]

/-- The block of `X` at `w`, a vertex of `Q₄`. -/
def blk (X : ι × Fin 4 → Bool) (w : ι) : Fin 4 → Bool := fun j => X (w, j)

/-- The block parities of `X`, a vertex of `Q_ι`. -/
def proj (X : ι × Fin 4 → Bool) : ι → Bool := fun w => oddOn univ (blk X w)

/-- The parity of `X` outside the block `w`. -/
def restPar (X : ι × Fin 4 → Bool) (w : ι) : Bool :=
  oddOn (univ.filter fun p : ι × Fin 4 => p.1 ≠ w) X

omit [Fintype ι] in
theorem blk_flipAt_self (X : ι × Fin 4 → Bool) (w : ι) (j : Fin 4) :
    blk (flipAt X (w, j)) w = flipAt (blk X w) j := by
  funext k; by_cases h : k = j <;> simp [blk, flipAt, h]

omit [Fintype ι] in
theorem blk_flipAt_of_ne (X : ι × Fin 4 → Bool) {w w' : ι} (h : w' ≠ w) (j : Fin 4) :
    blk (flipAt X (w', j)) w = blk X w := by
  funext k; simp [blk, flipAt, Ne.symm h]

omit [Fintype ι] in
theorem proj_flipAt (X : ι × Fin 4 → Bool) (w : ι) (j : Fin 4) :
    proj (flipAt X (w, j)) = flipAt (proj X) w := by
  funext w'
  by_cases h : w' = w
  · subst h
    rw [flipAt_self, proj, proj, blk_flipAt_self, oddOn_flipAt_of_mem _ (mem_univ _)]
  · rw [flipAt_of_ne _ h, proj, proj, blk_flipAt_of_ne X (Ne.symm h)]

theorem restPar_flipAt_self (X : ι × Fin 4 → Bool) (w : ι) (j : Fin 4) :
    restPar (flipAt X (w, j)) w = restPar X w :=
  oddOn_flipAt_of_notMem X (by simp)

theorem restPar_flipAt_of_ne (X : ι × Fin 4 → Bool) {w w' : ι} (h : w' ≠ w) (j : Fin 4) :
    restPar (flipAt X (w', j)) w = !restPar X w :=
  oddOn_flipAt_of_mem X (by simpa using h)

theorem qcol_ne_of_matched {v : Fin 4 → Bool} {j : Fin 4}
    (h : eDir (v 0) (v 1) (v 2) (v 3) = j ∨ oDir (v 0) (v 1) (v 2) (v 3) = j) (c c' π : Bool) :
    qcol v j c π ≠ qcol v j c' (!π) := by
  rcases h with h | h
  · simp [qcol, h]
  · by_cases he : eDir (v 0) (v 1) (v 2) (v 3) = j
    · simp [qcol, he]
    · simp [qcol, he, h]

theorem qcol_of_unmatched {v : Fin 4 → Bool} {j : Fin 4}
    (h : ¬ (eDir (v 0) (v 1) (v 2) (v 3) = j ∨ oDir (v 0) (v 1) (v 2) (v 3) = j)) (c π : Bool) :
    qcol v j c π = c := by
  rw [not_or] at h
  simp [qcol, h.1, h.2]

namespace GoodColoring

/-- The Brass–Harborth–Nienborg substitution step: from a good colouring of `Q_ι` build a good
colouring of `Q_{ι × Fin 4}`. Inside the block `w`, the `e`-edges of `Q₄` get the parity of `X`
outside the block, the `o`-edges the opposite parity, and the `a`-edges copy the colour of the
`w`-edge of `Q_ι` at the vector of block parities. -/
def step (C : GoodColoring ι) : GoodColoring (ι × Fin 4) where
  col X p := qcol (blk X p.1) p.2 (C.col (proj X) p.1) (restPar X p.1)
  col_flipAt X p := by
    obtain ⟨w, j⟩ := p
    simp only
    rw [blk_flipAt_self, proj_flipAt, C.col_flipAt, restPar_flipAt_self, qcol_flipAt]
  good X p q hpq := by
    obtain ⟨w, j⟩ := p
    obtain ⟨w', k⟩ := q
    simp only
    by_cases hw : w = w'
    · subst hw
      have hjk : j ≠ k := fun h => hpq (by rw [h])
      rw [blk_flipAt_self, blk_flipAt_self, proj_flipAt, proj_flipAt, C.col_flipAt,
        restPar_flipAt_self, restPar_flipAt_self]
      exact qcol_good _ j k _ _ hjk
    · rw [blk_flipAt_of_ne X (Ne.symm hw), blk_flipAt_of_ne X hw, proj_flipAt, proj_flipAt,
        restPar_flipAt_of_ne X (Ne.symm hw), restPar_flipAt_of_ne X hw]
      rintro ⟨h1, h2, h3⟩
      by_cases hA : eDir (blk X w 0) (blk X w 1) (blk X w 2) (blk X w 3) = j ∨
          oDir (blk X w 0) (blk X w 1) (blk X w 2) (blk X w 3) = j
      · exact qcol_ne_of_matched hA _ _ _ h1
      by_cases hB : eDir (blk X w' 0) (blk X w' 1) (blk X w' 2) (blk X w' 3) = k ∨
          oDir (blk X w' 0) (blk X w' 1) (blk X w' 2) (blk X w' 3) = k
      · exact qcol_ne_of_matched hB _ _ _ h3
      simp only [qcol_of_unmatched hA, qcol_of_unmatched hB] at h1 h2 h3
      exact C.good (proj X) w w' hw ⟨h1, h2, h3⟩

omit [DecidableEq ι] in
theorem card_filter_prod (P : ι × Fin 4 → Prop) [DecidablePred P] :
    #{p | P p} = ∑ w, #{j | P (w, j)} := by
  simp only [card_filter]
  exact Fintype.sum_prod_type _

theorem card_filter_eq_sum_toNat {κ : Type*} [Fintype κ] (b : κ → Bool) :
    #{w | b w = true} = ∑ w, (b w).toNat := by
  rw [card_filter]
  exact Finset.sum_congr rfl fun w _ => by cases b w <;> rfl

/-- Number of `true`-coloured directions of the substituted colouring. -/
theorem card_step (C : GoodColoring ι) (X : ι × Fin 4 → Bool) :
    #{p | C.step.col X p = true} = 2 * #{w | C.col (proj X) w = true} + Fintype.card ι := by
  have hc : Fintype.card ι = ∑ _w : ι, 1 := by simp
  rw [card_filter_prod, card_filter_eq_sum_toNat, Finset.mul_sum, hc, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun w _ => card_qcol _ _ _

end GoodColoring

end Step

section Transfer

namespace GoodColoring

variable {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]

theorem flipAt_comp_equiv (e : ι ≃ κ) (x : κ → Bool) (k : κ) :
    flipAt x k ∘ e = flipAt (x ∘ e) (e.symm k) := by
  funext i
  simp only [Function.comp, flipAt, ← Equiv.eq_symm_apply]

/-- Transport a good colouring along a bijection of coordinates. -/
def congr (e : ι ≃ κ) (C : GoodColoring ι) : GoodColoring κ where
  col x k := C.col (x ∘ e) (e.symm k)
  col_flipAt x k := by
    rw [flipAt_comp_equiv, C.col_flipAt]
  good x k l hkl := by
    rw [flipAt_comp_equiv, flipAt_comp_equiv]
    exact C.good (x ∘ e) (e.symm k) (e.symm l) (fun h => hkl (e.symm.injective h))

theorem card_congr [Fintype ι] [Fintype κ] (e : ι ≃ κ) (C : GoodColoring ι) (x : κ → Bool) :
    #{k | (C.congr e).col x k = true} = #{i | C.col (x ∘ e) i = true} := by
  refine (Finset.card_equiv e.symm fun k => ?_)
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rfl

theorem sum_card_congr [Fintype ι] [Fintype κ] (e : ι ≃ κ) (C : GoodColoring ι) :
    ∑ x, #{k | (C.congr e).col x k = true} = ∑ y, #{i | C.col y i = true} := by
  simp only [card_congr]
  exact Fintype.sum_equiv (e.symm.arrowCongr (Equiv.refl Bool)) _ _ fun x => rfl

/-- Add one coordinate: the new direction is coloured by the parity of the old coordinates. -/
def extend [Fintype ι] (C : GoodColoring ι) : GoodColoring (Option ι) where
  col x o := match o with
    | none => oddOn univ (fun t => x (some t))
    | some i => C.col (fun t => x (some t)) i
  col_flipAt x o := by
    cases o with
    | none => simp only [flipAt_of_ne x (Option.some_ne_none _)]
    | some i =>
      simp only
      have : (fun t => flipAt x (some i) (some t)) = flipAt (fun t => x (some t)) i := by
        funext t; simp [flipAt]
      rw [this, C.col_flipAt]
  good x o₁ o₂ h := by
    have hsome :
        ∀ i, (fun t => flipAt x (some i) (some t)) = flipAt (fun t => x (some t)) i := by
      intro i; funext t; simp [flipAt]
    cases o₁ with
    | none =>
      cases o₂ with
      | none => exact absurd rfl h
      | some j =>
        rintro ⟨h1, -, -⟩
        simp only [hsome, oddOn_flipAt_of_mem _ (mem_univ j)] at h1
        exact Bool.eq_not_self _ |>.mp h1
    | some i =>
      cases o₂ with
      | none =>
        rintro ⟨-, -, h3⟩
        simp only [hsome, oddOn_flipAt_of_mem _ (mem_univ i)] at h3
        exact Bool.eq_not_self _ |>.mp h3
      | some j =>
        simp only [hsome]
        exact C.good _ i j (fun hij => h (by rw [hij]))

theorem card_extend [Fintype ι] (C : GoodColoring ι) (x : Option ι → Bool) :
    #{o | C.extend.col x o = true} =
      (oddOn univ (fun t => x (some t))).toNat + #{i | C.col (fun t => x (some t)) i = true} := by
  rw [card_filter, Fintype.sum_option, card_filter]
  congr 1
  show (if oddOn univ (fun t => x (some t)) = true then 1 else 0) = _
  cases oddOn univ (fun t => x (some t)) <;> rfl

theorem sum_card_extend [Fintype ι] [Nonempty ι] (C : GoodColoring ι) :
    ∑ x, #{o | C.extend.col x o = true} =
      2 * ∑ y, #{i | C.col y i = true} + 2 ^ Fintype.card ι := by
  simp only [card_extend]
  have h := Fintype.sum_equiv (Equiv.piOptionEquivProd (β := fun _ => Bool))
    (fun x : Option ι → Bool =>
      (oddOn univ (fun t => x (some t))).toNat + #{i | C.col (fun t => x (some t)) i = true})
    (fun p : Bool × (ι → Bool) => (oddOn univ p.2).toNat + #{i | C.col p.2 i = true})
    fun x => rfl
  rw [h, Fintype.sum_prod_type]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_bool, smul_eq_mul,
    Finset.sum_add_distrib]
  rw [← card_filter_eq_sum_toNat, ← two_mul_card_oddOn]
  ring

end GoodColoring

end Transfer

section Main

open GoodColoring

/-- The iterated Brass–Harborth–Nienborg colouring of `Q_{4^r}`: every vertex has exactly
`(4^r + 2^r)/2` edges of colour `true`. -/
theorem exists_goodColoring_four_pow (r : ℕ) :
    ∃ C : GoodColoring (Fin (4 ^ r)), ∀ x, 2 * #{i | C.col x i = true} = 4 ^ r + 2 ^ r := by
  induction r with
  | zero =>
    refine ⟨⟨fun _ _ => true, fun _ _ => rfl, fun x i j hij => ?_⟩, fun x => ?_⟩
    · exact absurd (Fin.ext (by have := i.isLt; have := j.isLt; simp only [pow_zero] at *; omega))
        hij
    · simp
  | succ r ih =>
    obtain ⟨C, hC⟩ := ih
    let e : Fin (4 ^ r) × Fin 4 ≃ Fin (4 ^ (r + 1)) :=
      finProdFinEquiv.trans (finCongr (pow_succ 4 r).symm)
    refine ⟨C.step.congr e, fun x => ?_⟩
    rw [card_congr, card_step, Fintype.card_fin]
    have := hC (proj (x ∘ e))
    have h4 : 4 ^ (r + 1) = 4 ^ r * 4 := pow_succ 4 r
    have h2 : 2 ^ (r + 1) = 2 ^ r * 2 := pow_succ 2 r
    omega

/-- Adding `t` further coordinates to the Brass–Harborth–Nienborg colouring of `Q_{4^r}`. -/
theorem exists_goodColoring_add (r t : ℕ) :
    ∃ C : GoodColoring (Fin (4 ^ r + t)),
      2 * ∑ x, #{i | C.col x i = true} = 2 ^ (4 ^ r + t) * (4 ^ r + t + 2 ^ r) := by
  induction t with
  | zero =>
    obtain ⟨C, hC⟩ := exists_goodColoring_four_pow r
    refine ⟨C, ?_⟩
    show 2 * ∑ x : Fin (4 ^ r) → Bool, #{i | C.col x i = true} = 2 ^ (4 ^ r) * (4 ^ r + 2 ^ r)
    rw [Finset.mul_sum]
    simp only [hC, Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_bool,
      Fintype.card_fin, smul_eq_mul]
  | succ t ih =>
    obtain ⟨C, hC⟩ := ih
    have : Nonempty (Fin (4 ^ r + t)) := ⟨⟨0, by positivity⟩⟩
    refine ⟨C.extend.congr (finSuccEquiv (4 ^ r + t)).symm, ?_⟩
    rw [sum_card_congr, sum_card_extend, Fintype.card_fin]
    calc 2 * (2 * ∑ y, #{i | C.col y i = true} + 2 ^ (4 ^ r + t))
        = 2 * (2 * ∑ y, #{i | C.col y i = true}) + 2 * 2 ^ (4 ^ r + t) := by ring
      _ = 2 ^ (4 ^ r + (t + 1)) * (4 ^ r + (t + 1) + 2 ^ r) := by rw [hC]; ring

end Main

section Theorems

open GoodColoring

/-- **Brass–Harborth–Nienborg (1995).** If `n = 4 ^ r`, then `Qₙ` has a `C₄`-free subgraph
with exactly `½ (n + √n) 2 ^ (n - 1)` edges. -/
theorem bhn_four_pow (n r : ℕ) (hn : n = 4 ^ r) :
    ∃ H : SimpleGraph (Fin n → Bool), H ≤ hypercube n ∧ ¬ cycleGraph 4 ⊑ H ∧
      (H.edgeSet.ncard : ℝ) = 1 / 2 * (n + √n) * 2 ^ (n - 1 : ℕ) := by
  subst hn
  obtain ⟨C, hC⟩ := exists_goodColoring_four_pow r
  refine ⟨C.graph, C.graph_le_hypercube, C.not_cycleGraph_four_isContained, ?_⟩
  have h2 := C.two_mul_ncard_edgeSet
  have hsum : 2 * ∑ x, #{i | C.col x i = true} = 2 ^ (4 ^ r) * (4 ^ r + 2 ^ r) := by
    rw [Finset.mul_sum]
    simp only [hC, sum_const, card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin,
      smul_eq_mul]
  have h4 : 4 * C.graph.edgeSet.ncard = 2 ^ (4 ^ r) * (4 ^ r + 2 ^ r) := by omega
  have hsqrt : √((4 ^ r : ℕ) : ℝ) = 2 ^ r := by
    have e : ((4 ^ r : ℕ) : ℝ) = (2 ^ r) ^ 2 := by
      push_cast; rw [← pow_mul, mul_comm, pow_mul]; norm_num
    rw [e]
    exact Real.sqrt_sq (by positivity)
  have hpow : (2 : ℝ) ^ (4 ^ r) = 2 ^ (4 ^ r - 1) * 2 := by
    rw [← pow_succ, Nat.sub_add_cancel (Nat.one_le_pow _ _ (by norm_num))]
  have h4R : (4 : ℝ) * C.graph.edgeSet.ncard = 2 ^ (4 ^ r) * ((4 ^ r : ℕ) + 2 ^ r) := by
    exact_mod_cast h4
  rw [hsqrt]
  rw [hpow] at h4R
  push_cast at h4R ⊢
  linarith

/-- For every `n ≥ 1`, `Qₙ` has a `C₄`-free subgraph with `2 ^ n (n + 2 ^ r) / 4` edges, where
`4 ^ r ≤ n < 4 ^ (r + 1)`. -/
theorem exists_c4Free_subgraph (n : ℕ) (hn : 0 < n) :
    ∃ H : SimpleGraph (Fin n → Bool), H ≤ hypercube n ∧ ¬ cycleGraph 4 ⊑ H ∧
      4 * H.edgeSet.ncard = 2 ^ n * (n + 2 ^ Nat.log 4 n) := by
  set L := Nat.log 4 n
  have hle : 4 ^ L ≤ n := Nat.pow_log_le_self 4 hn.ne'
  obtain ⟨t, ht⟩ : ∃ t, n = 4 ^ L + t := ⟨n - 4 ^ L, by omega⟩
  obtain ⟨C, hC⟩ := exists_goodColoring_add L t
  refine ⟨(C.congr (finCongr ht.symm)).graph, (C.congr (finCongr ht.symm)).graph_le_hypercube,
    (C.congr (finCongr ht.symm)).not_cycleGraph_four_isContained, ?_⟩
  have h2 := (C.congr (finCongr ht.symm)).two_mul_ncard_edgeSet
  rw [sum_card_congr] at h2
  have key : 2 ^ n * (n + 2 ^ L) = 2 ^ (4 ^ L + t) * (4 ^ L + t + 2 ^ L) := by rw [← ht]
  omega

/-- **Erdős Problem 86, lower bound (Brass–Harborth–Nienborg 1995).** There is `c > 0` such
that for every `n ≥ 1` the hypercube `Qₙ` has a `C₄`-free subgraph with at least
`(1/2 + c/√n) n 2 ^ (n - 1)` edges. Here `c = 1/4`. -/
theorem erdos_86_lower_bound : ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, 0 < n →
    ∃ H : SimpleGraph (Fin n → Bool), H ≤ hypercube n ∧ ¬ cycleGraph 4 ⊑ H ∧
      (1 / 2 + c / √n) * n * 2 ^ (n - 1 : ℕ) ≤ (H.edgeSet.ncard : ℝ) := by
  refine ⟨1 / 4, by norm_num, fun n hn => ?_⟩
  obtain ⟨H, hle, hfree, hcard⟩ := exists_c4Free_subgraph n hn
  refine ⟨H, hle, hfree, ?_⟩
  set L := Nat.log 4 n
  have hlt : n < 4 ^ (L + 1) := Nat.lt_pow_succ_log_self (by norm_num) n
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hs0 : 0 < √(n : ℝ) := Real.sqrt_pos.mpr hnR
  have hss : √(n : ℝ) ^ 2 = n := Real.sq_sqrt hnR.le
  have hsL : √(n : ℝ) ≤ 2 * 2 ^ L := by
    have h1 : (n : ℝ) ≤ (2 * 2 ^ L) ^ 2 := by
      have h3 : (n : ℝ) < (4 : ℝ) ^ (L + 1) := by exact_mod_cast hlt
      have e : (2 * (2 : ℝ) ^ L) ^ 2 = 4 ^ (L + 1) := by
        rw [pow_succ, show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul, mul_pow, ← pow_mul]; ring
      linarith
    calc √(n : ℝ) ≤ √((2 * 2 ^ L) ^ 2) := Real.sqrt_le_sqrt h1
      _ = 2 * 2 ^ L := Real.sqrt_sq (by positivity)
  have hpow : (2 : ℝ) ^ n = 2 ^ (n - 1) * 2 := by
    rw [← pow_succ, Nat.sub_add_cancel hn]
  have hcardR : (4 : ℝ) * H.edgeSet.ncard = 2 ^ n * (n + 2 ^ L) := by exact_mod_cast hcard
  rw [hpow] at hcardR
  have hP : 0 < (2 : ℝ) ^ (n - 1) := by positivity
  have e : (1 / 2 + 1 / 4 / √(n : ℝ)) * n = n / 2 + √(n : ℝ) / 4 := by
    field_simp
    linear_combination -2 * hss
  rw [e]
  have := mul_le_mul_of_nonneg_left hsL hP.le
  nlinarith

end Theorems

end Erdos86
