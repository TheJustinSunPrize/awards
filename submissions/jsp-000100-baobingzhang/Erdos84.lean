import Mathlib

/-!
# Erdős Problem 84: the number of cycle sets

The *cycle set* of a graph `G` on `n` vertices is the set `A ⊆ {3, …, n}` of the lengths of the
cycles of `G`. Let `f(n)` be the number of distinct cycle sets as `G` ranges over all graphs on `n`
vertices. Erdős and Faudree [Er97] (who showed `2^(n/2) < f(n) ≤ 2^(n-2)`) asked to prove that
`f(n) = o(2^n)`, and whether `f(n) / 2^(n/2) → ∞`. The first question was answered by
Verstraëte [Ve04], who proved `f(n) ≪ 2^(n - n^(1/10))`; Nenadov [Ne25] improved this to
`f(n) ≤ 2^(n - Ω(√n / log^(3/2) n))`.

## Statements proved

* `erdos_84`: `(fun n => (numCycleSets n : ℝ)) =o[atTop] (fun n => (2 : ℝ) ^ n)`, that is,
  `f(n) = o(2^n)`. This is the complete answer to the first question of the problem.
* `erdos_84_tendsto`, `erdos_84_eps`: the equivalent forms `f(n) / 2^n → 0` and
  `∀ ε > 0, ∃ N, ∀ n ≥ N, f(n) ≤ ε · 2^n`.
* `eventually_numCycleSets_le`: for every `K`, eventually `f(n) ≤ 3 · 2^(n - K)`.

Definitions. `cycleSet G` is the set of lengths `p.length` of closed walks `p` with `p.IsCycle`
(Mathlib's notion of a cycle), and `numCycleSets n` is the `Set.ncard` of the set of cycle sets of
graphs `G : SimpleGraph (Fin n)`. Cycle sets do not depend on the labelling of the vertices
(`cycleSet_comap_equiv`), so this counts cycle sets of all `n`-vertex graphs. Sanity checks: the
family of cycle sets is finite (`cycleSets_finite`), so `Set.ncard` is its true size; every cycle
length lies in `[3, n]` (`cycleSet_subset_Icc`); the empty graph has no cycles (`cycleSet_bot`),
`K₃` has a triangle (`three_mem_cycleSet_top`), and `f(3) ≥ 2` (`two_le_numCycleSets_three`).

## What is not proved

The second question (`f(n) / 2^(n/2) → ∞`) is open and is not addressed. The quantitative bounds
of Verstraëte and Nenadov are not formalized; this file proves their qualitative consequence
`f(n) = o(2^n)`.

## Proof

The argument follows the overall strategy of Verstraëte [Ve04] as presented by Nenadov
[Ne25, §5]: split off graphs without a long cycle and graphs with a long cycle and few further
edges (both are few), and for the remaining graphs find a small "fingerprint" set which must be
contained in the cycle set. The fingerprint arguments below are simpler than Nenadov's container
lemmas and give a weaker quantitative bound, which is enough for `o(2^n)`.

Fix `K`, let `ℓ = ⌊log₂ n⌋ + 1`, `m = 4(ℓ + K + 2)`, `κ = m² + m` and `r = ⌊n / 4ℓ⌋`.

1. *No long cycle.* If every cycle has length `< n - K`, the cycle set is a subset of
   `{0, …, n-K-1}`: at most `2^(n-K)` possibilities.
2. *Normalisation* (`exists_stdCycle`). Otherwise relabel the vertices so that `0, 1, …, L-1` is
   a cycle, with `L ≥ n - K`.
3. *Few further edges* (`card_stdCycle_sparse_le`). If at most `r` edges are not on this cycle,
   the graph is determined by `L` and these edges: at most `(n+1)(r+1)(n²+1)^r ≤ 2^(n-K)` graphs.
4. *Fingerprints* (`exists_large_diffs`, `fpFamily`, `card_upset_le`). If `X` is a set of at least
   `κ` natural numbers, a greedy double-counting argument gives `B ⊆ X` with `#B = 2m` and at least
   `m²/2` distinct positive differences. The sets `{d + 2 : d ∈ diffs B}` and
   `{L - d : d ∈ diffs B}` (`B ⊆ [0, 2n]`, `L ≤ n`) of size `≥ m²/2` form a family with at most
   `2(n+1)(2n+1)^(2m)` members, so at most `2(n+1)(2n+1)^(2m) · 2^(n+1-m²/2) ≤ 2^(n-K)` subsets of
   `{0, …, n}` contain one of them.
5. *Many further edges* (`fingerprint_exists`). One of the following gives a set `X` of size `κ`
   such that `y - x + 2` (resp. `L - (y - x)`) is a cycle length for all `x < y` in `X`:
   * a vertex `w ≥ L` with `κ` neighbours on the cycle: for neighbours `p < q` the cycle
     `w, p, p+1, …, q` has length `q - p + 2` (`star_mem`);
   * otherwise there are at least `κ³` chords `(a, b)` of the cycle. Applying Mirsky's theorem
     (`chain_or_antichain`) to nesting and then to "lying to the left of", there are `κ` pairwise
     nested chords (a chord nested in another closes a cycle of length
     `span' - span + 2`, `nested_mem`), or `κ` pairwise non-overlapping chords (the cycle can be
     short-cut along any subfamily, `shortcut_mem`, so `L` minus any difference of prefix sums of
     `span - 1` is a cycle length), or `κ` pairwise crossing chords (for `a < a' < b < b'` the
     cycle `a, …, a', b', b'-1, …, b` has length `(a' + b') - (a + b) + 2`, `crossing_mem`).
6. *Conclusion.* Once `200000 (⌊log₂ n⌋ + K + 3)^7 ≤ n`, `f(n) ≤ 3 · 2^(n-K)`.

Cycles are built from explicit vertex sequences (`mem_cycleSet_of_fn`, `mem_cycleSet_finset`).

## References

* [Er97] Erdős, P., _Some recent problems and results in graph theory_, Discrete Math. 164 (1997),
  81–85.
* [Ve04] Verstraëte, J., _On the number of sets of cycle lengths_, Combinatorica 24 (2004),
  719–730.
* [Ne25] Nenadov, R., _Improved bound on the number of cycle sets_, arXiv:2501.09904 (2025).
* [erdosproblems.com/84](https://www.erdosproblems.com/84)
-/

open Finset

namespace Erdos84

/-- The cycle set of a graph: the set of lengths of its cycles. -/
def cycleSet {V : Type*} (G : SimpleGraph V) : Set ℕ :=
  {k | ∃ (v : V) (p : G.Walk v v), p.IsCycle ∧ p.length = k}

/-- `f(n)`: the number of distinct cycle sets of graphs on `n` vertices. -/
noncomputable def numCycleSets (n : ℕ) : ℕ :=
  Set.ncard {A : Set ℕ | ∃ G : SimpleGraph (Fin n), cycleSet G = A}

section Builder

variable {V : Type*} {G : SimpleGraph V}

/-- The walk `g 0, g 1, …, g m` along a sequence of vertices. -/
def walkFn (g : ℕ → V) (k : ℕ) (hadj : ∀ i, i + 1 < k → G.Adj (g i) (g (i + 1))) :
    (m : ℕ) → m < k → G.Walk (g 0) (g m)
  | 0, _ => SimpleGraph.Walk.nil
  | m + 1, h => (walkFn g k hadj m (by omega)).concat (hadj m h)

lemma walkFn_support (g : ℕ → V) (k : ℕ) (hadj : ∀ i, i + 1 < k → G.Adj (g i) (g (i + 1)))
    (m : ℕ) (hm : m < k) : (walkFn g k hadj m hm).support = (List.range (m + 1)).map g := by
  induction m with
  | zero => simp [walkFn]
  | succ m ih =>
    simp only [walkFn, SimpleGraph.Walk.support_concat, ih (by omega)]
    simp [List.range_succ]

lemma walkFn_length (g : ℕ → V) (k : ℕ) (hadj : ∀ i, i + 1 < k → G.Adj (g i) (g (i + 1)))
    (m : ℕ) (hm : m < k) : (walkFn g k hadj m hm).length = m := by
  induction m with
  | zero => simp [walkFn]
  | succ m ih => simp [walkFn, ih (by omega)]

lemma walkFn_edges (g : ℕ → V) (k : ℕ) (hadj : ∀ i, i + 1 < k → G.Adj (g i) (g (i + 1)))
    (m : ℕ) (hm : m < k) :
    (walkFn g k hadj m hm).edges = (List.range m).map (fun i => s(g i, g (i + 1))) := by
  induction m with
  | zero => simp [walkFn]
  | succ m ih =>
    simp only [walkFn, SimpleGraph.Walk.edges_concat, ih (by omega)]
    simp [List.range_succ, List.concat_eq_append]

/-- **Cycle builder.** A sequence `g 0, …, g (k-1)` of `k ≥ 3` distinct vertices in which
consecutive vertices are adjacent and `g (k-1)` is adjacent to `g 0` gives a cycle of length
`k`. -/
theorem mem_cycleSet_of_fn (k : ℕ) (hk : 3 ≤ k) (g : ℕ → V)
    (hinj : ∀ i j, i < k → j < k → g i = g j → i = j)
    (hadj : ∀ i, i + 1 < k → G.Adj (g i) (g (i + 1))) (hclose : G.Adj (g (k - 1)) (g 0)) :
    k ∈ cycleSet G := by
  set p := walkFn g k hadj (k - 1) (by omega) with hp
  refine ⟨g (k - 1), SimpleGraph.Walk.cons hclose p, ?_, ?_⟩
  · rw [SimpleGraph.Walk.cons_isCycle_iff]
    constructor
    · rw [SimpleGraph.Walk.isPath_def, hp, walkFn_support]
      rw [List.nodup_map_iff_inj_on List.nodup_range]
      intro i hi j hj hij
      simp only [List.mem_range] at hi hj
      exact hinj i j (by omega) (by omega) hij
    · rw [hp, walkFn_edges]
      simp only [List.mem_map, List.mem_range, not_exists, not_and]
      intro i hi he
      rw [Sym2.eq_iff] at he
      rcases he with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · have := hinj i (k - 1) (by omega) (by omega) h1
        omega
      · have := hinj i 0 (by omega) (by omega) h1
        have := hinj (i + 1) (k - 1) (by omega) (by omega) h2
        omega
  · simp [hp, walkFn_length]; omega

end Builder

/-- Adjacency in a graph on `Fin n`, read on natural-number labels. -/
def AdjN {n : ℕ} (H : SimpleGraph (Fin n)) (a b : ℕ) : Prop :=
  ∃ (ha : a < n) (hb : b < n), H.Adj ⟨a, ha⟩ ⟨b, hb⟩

lemma AdjN.symm {n : ℕ} {H : SimpleGraph (Fin n)} {a b : ℕ} (h : AdjN H a b) : AdjN H b a := by
  obtain ⟨ha, hb, h⟩ := h
  exact ⟨hb, ha, h.symm⟩

lemma AdjN.ne {n : ℕ} {H : SimpleGraph (Fin n)} {a b : ℕ} (h : AdjN H a b) : a ≠ b := by
  obtain ⟨ha, hb, h⟩ := h
  intro hab
  subst hab
  exact H.loopless.irrefl _ h

/-- Cycle builder on natural-number labels. -/
theorem mem_cycleSet_nat {n : ℕ} {H : SimpleGraph (Fin n)} (k : ℕ) (hk : 3 ≤ k) (g : ℕ → ℕ)
    (hinj : ∀ i j, i < k → j < k → g i = g j → i = j)
    (hadj : ∀ i, i + 1 < k → AdjN H (g i) (g (i + 1))) (hclose : AdjN H (g (k - 1)) (g 0)) :
    k ∈ cycleSet H := by
  have hn : 0 < n := by obtain ⟨h, -⟩ := hclose; omega
  let g' : ℕ → Fin n := fun i => ⟨min (g i) (n - 1), by omega⟩
  have hg' : ∀ i (hi : g i < n), g' i = ⟨g i, hi⟩ := by
    intro i hi; simp only [g', Fin.mk.injEq]; omega
  refine mem_cycleSet_of_fn k hk g' ?_ ?_ ?_
  · intro i j hi hj hij
    have hgi : g i < n := by
      rcases Nat.lt_or_ge (i + 1) k with h | h
      · exact (hadj i h).1
      · have : i = k - 1 := by omega
        subst this; exact hclose.1
    have hgj : g j < n := by
      rcases Nat.lt_or_ge (j + 1) k with h | h
      · exact (hadj j h).1
      · have : j = k - 1 := by omega
        subst this; exact hclose.1
    rw [hg' i hgi, hg' j hgj] at hij
    exact hinj i j hi hj (Fin.mk.inj hij)
  · intro i hi
    obtain ⟨h1, h2, h⟩ := hadj i hi
    rwa [hg' i h1, hg' (i + 1) h2]
  · obtain ⟨h1, h2, h⟩ := hclose
    rwa [hg' _ h1, hg' 0 h2]

/-- Cycle builder for a finite set of labels, traversed in increasing order. -/
theorem mem_cycleSet_finset {n : ℕ} {H : SimpleGraph (Fin n)} (Z : Finset ℕ) (h3 : 3 ≤ #Z)
    (hcons : ∀ u ∈ Z, ∀ v ∈ Z, u < v → (∀ w ∈ Z, ¬ (u < w ∧ w < v)) → AdjN H u v)
    (lo hi : ℕ) (hlo : lo ∈ Z) (hhi : hi ∈ Z) (hlo' : ∀ z ∈ Z, lo ≤ z) (hhi' : ∀ z ∈ Z, z ≤ hi)
    (hclose : AdjN H hi lo) : #Z ∈ cycleSet H := by
  set k := #Z with hk
  let e := Z.orderEmbOfFin hk.symm
  let g : ℕ → ℕ := fun i => if h : i < k then e ⟨i, h⟩ else 0
  have hg : ∀ i (h : i < k), g i = e ⟨i, h⟩ := fun i h => by simp [g, h]
  have hmem : ∀ i (h : i < k), g i ∈ Z := fun i h => by
    rw [hg i h]; exact Z.orderEmbOfFin_mem hk.symm _
  refine mem_cycleSet_nat k h3 g ?_ ?_ ?_
  · intro i j hi hj hij
    rw [hg i hi, hg j hj] at hij
    exact Fin.mk.inj (e.injective hij)
  · intro i hi
    have hlt : g i < g (i + 1) := by
      rw [hg i (by omega), hg (i + 1) hi]
      exact e.strictMono (Fin.mk_lt_mk.mpr (by omega))
    refine hcons _ (hmem i (by omega)) _ (hmem (i + 1) hi) hlt ?_
    intro w hw ⟨h1, h2⟩
    have hw' : w ∈ Set.range e := by
      rw [Finset.range_orderEmbOfFin]; exact hw
    obtain ⟨⟨j, hj⟩, rfl⟩ := hw'
    rw [hg i (by omega)] at h1
    rw [hg (i + 1) hi] at h2
    have a1 := e.lt_iff_lt.mp h1
    have a2 := e.lt_iff_lt.mp h2
    simp only [Fin.mk_lt_mk] at a1 a2
    omega
  · have hk0 : 0 < k := by omega
    have e0 : g 0 = lo := by
      rw [hg 0 hk0]
      have := Finset.orderEmbOfFin_zero hk.symm hk0
      rw [this]
      exact le_antisymm (Z.min'_le _ hlo) (hlo' _ (Z.min'_mem _))
    have e1 : g (k - 1) = hi := by
      rw [hg (k - 1) (by omega)]
      have := Finset.orderEmbOfFin_last hk.symm hk0
      rw [this]
      exact le_antisymm (hhi' _ (Z.max'_mem _)) (Z.le_max' _ hhi)
    rw [e0, e1]; exact hclose

/-- Cycle sets are invariant under relabelling the vertices. -/
theorem cycleSet_comap_equiv {V W : Type*} (σ : V ≃ W) (G : SimpleGraph W) :
    cycleSet (G.comap σ) = cycleSet G := by
  ext k
  constructor
  · rintro ⟨v, p, hp, rfl⟩
    let φ := SimpleGraph.Iso.comap σ G
    refine ⟨φ v, p.map φ.toHom, ?_, by simp⟩
    exact hp.map φ.injective
  · rintro ⟨v, p, hp, rfl⟩
    let φ := (SimpleGraph.Iso.comap σ G).symm
    refine ⟨φ v, p.map φ.toHom, ?_, by simp⟩
    exact hp.map φ.injective

/-- Every cycle length of a graph on `Fin n` lies in `[3, n]`. -/
theorem cycleSet_subset_Icc {n : ℕ} (G : SimpleGraph (Fin n)) : cycleSet G ⊆ Set.Icc 3 n := by
  rintro k ⟨v, p, hp, rfl⟩
  refine ⟨hp.three_le_length, ?_⟩
  have hinj := hp.getVert_injOn'
  have : #((range p.length).image (fun i => p.getVert i)) = p.length := by
    rw [Finset.card_image_of_injOn, Finset.card_range]
    intro i hi j hj hij
    simp only [coe_range, Set.mem_Iio] at hi hj
    exact hinj (by simp; omega) (by simp; omega) hij
  have h2 := Finset.card_le_univ ((range p.length).image (fun i => p.getVert i))
  simp only [Fintype.card_fin] at h2
  omega

/-- A graph on `Fin n` whose vertices `0, 1, …, L-1` form a cycle in this order. -/
def StdCycle {n : ℕ} (H : SimpleGraph (Fin n)) (L : ℕ) : Prop :=
  3 ≤ L ∧ L ≤ n ∧ (∀ i, i + 1 < L → AdjN H i (i + 1)) ∧ AdjN H (L - 1) 0

/-- Normalisation: a graph with a cycle of length `L` is isomorphic to one in which the cycle
is `0, 1, …, L-1`. -/
theorem exists_stdCycle {n : ℕ} (G : SimpleGraph (Fin n)) {L : ℕ} (hL : L ∈ cycleSet G) :
    ∃ H : SimpleGraph (Fin n), cycleSet H = cycleSet G ∧ StdCycle H L := by
  have hIcc := cycleSet_subset_Icc G hL
  obtain ⟨v, p, hp, rfl⟩ := hL
  set L := p.length with hLdef
  have h3 : 3 ≤ L := hIcc.1
  have hLn : L ≤ n := hIcc.2
  have hinj := hp.getVert_injOn'
  let fn : Fin n → Fin n := fun i => p.getVert i.val
  let s : Finset (Fin n) := univ.filter (fun i => i.val < L)
  have hfs : Set.InjOn fn s := by
    intro i hi j hj hij
    simp only [s, coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hi hj
    exact Fin.ext (hinj (by simp; omega) (by simp; omega) hij)
  obtain ⟨σ', hσ'⟩ := Finset.exists_equiv_extend_of_card_eq (t := (univ : Finset (Fin n)))
    (by simp) (subset_univ _) hfs
  let σ : Fin n ≃ Fin n := σ'.trans (Equiv.subtypeUnivEquiv (fun _ => mem_univ _))
  have hσ : ∀ i : Fin n, i.val < L → σ i = p.getVert i.val := by
    intro i hi
    have := hσ' i (by simp [s, hi])
    simpa [σ] using this
  refine ⟨G.comap σ, cycleSet_comap_equiv σ G, hIcc.1, hIcc.2, ?_, ?_⟩
  · intro i hi
    refine ⟨by omega, by omega, ?_⟩
    simp only [SimpleGraph.comap_adj]
    rw [hσ ⟨i, _⟩ (by simp; omega), hσ ⟨i + 1, _⟩ (by simp; omega)]
    exact p.adj_getVert_succ (i := i) (by omega)
  · refine ⟨by omega, by omega, ?_⟩
    simp only [SimpleGraph.comap_adj]
    rw [hσ ⟨L - 1, _⟩ (by simp; omega), hσ ⟨0, _⟩ (by simp; omega)]
    have h := p.adj_getVert_succ (i := L - 1) (by omega)
    have e : L - 1 + 1 = L := by omega
    rw [e, hLdef, SimpleGraph.Walk.getVert_length] at h
    simpa [SimpleGraph.Walk.getVert_zero] using h

/-! ### Chains and antichains (Mirsky) -/

/-- Mirsky's theorem, in the form used here: for a strict order `r` on a finite set `s` (strict
monotonicity of a natural-number measure `μ` gives well-foundedness), either `s` contains a chain
of size `c + 1`, or `s` contains an antichain of size at least `#s / c`. -/
theorem chain_or_antichain {α : Type*} [DecidableEq α] (r : α → α → Prop) (μ : α → ℕ)
    (c : ℕ) : ∀ (s : Finset α), (∀ x ∈ s, ∀ y ∈ s, r x y → μ x < μ y) →
    (∀ x ∈ s, ∀ y ∈ s, ∀ z ∈ s, r x y → r y z → r x z) →
    (∃ t ⊆ s, c + 1 ≤ #t ∧ ∀ x ∈ t, ∀ y ∈ t, x ≠ y → r x y ∨ r y x) ∨
    (∃ t ⊆ s, #s ≤ c * #t ∧ ∀ x ∈ t, ∀ y ∈ t, ¬ r x y) := by
  classical
  induction c with
  | zero =>
    intro s hμ _
    rcases s.eq_empty_or_nonempty with h | ⟨x, hx⟩
    · right; exact ⟨∅, by simp, by simp [h], by simp⟩
    · left
      refine ⟨{x}, by simpa using hx, by simp, ?_⟩
      intro a ha b hb hab
      simp only [mem_singleton] at ha hb
      exact absurd (ha.trans hb.symm) hab
  | succ c ih =>
    intro s hμ htr
    set M := s.filter (fun x => ∀ y ∈ s, ¬ r y x) with hM
    set s' := s.filter (fun x => ¬ ∀ y ∈ s, ¬ r y x) with hs'
    have hMs : M ⊆ s := filter_subset _ _
    have hs's : s' ⊆ s := filter_subset _ _
    have hcard : #s = #M + #s' := by
      rw [hM, hs', Finset.card_filter_add_card_filter_not]
    have hManti : ∀ x ∈ M, ∀ y ∈ M, ¬ r x y := by
      intro x hx y hy hxy
      simp only [hM, mem_filter] at hx hy
      exact hy.2 x hx.1 hxy
    rcases ih s' (fun x hx y hy => hμ x (hs's hx) y (hs's hy))
        (fun x hx y hy z hz => htr x (hs's hx) y (hs's hy) z (hs's hz)) with
      ⟨t, hts, hct, hchain⟩ | ⟨t, hts, hct, hanti⟩
    · left
      have htne : t.Nonempty := by
        rw [← Finset.card_pos]; omega
      obtain ⟨x0, hx0, hx0min⟩ := t.exists_min_image μ htne
      have hx0s' := hts hx0
      simp only [hs', mem_filter, not_forall, not_not] at hx0s'
      obtain ⟨hx0s, y, hy, hyx⟩ := hx0s'
      set Y := s.filter (fun y => r y x0) with hY
      have hYne : Y.Nonempty := ⟨y, by simp [hY, hy, hyx]⟩
      obtain ⟨z, hz, hzmin⟩ := Y.exists_min_image μ hYne
      simp only [hY, mem_filter] at hz
      have hzM : z ∈ M := by
        simp only [hM, mem_filter]
        refine ⟨hz.1, fun w hw hwz => ?_⟩
        have hwY : w ∈ Y := by
          simp only [hY, mem_filter]; exact ⟨hw, htr w hw z hz.1 x0 hx0s hwz hz.2⟩
        have := hzmin w hwY
        have := hμ w hw z hz.1 hwz
        omega
      have hzt : z ∉ t := by
        intro hzt
        have := hts hzt
        simp only [hs', mem_filter] at this
        simp only [hM, mem_filter] at hzM
        exact this.2 hzM.2
      refine ⟨insert z t, ?_, ?_, ?_⟩
      · intro w hw
        rcases mem_insert.mp hw with rfl | hw
        · exact hz.1
        · exact hs's (hts hw)
      · rw [card_insert_of_notMem hzt]; omega
      · have key : ∀ w ∈ t, r z w := by
          intro w hw
          by_cases hwx : w = x0
          · subst hwx; exact hz.2
          · rcases hchain x0 hx0 w hw (Ne.symm hwx) with h | h
            · exact htr z hz.1 x0 hx0s w (hs's (hts hw)) hz.2 h
            · have := hμ w (hs's (hts hw)) x0 hx0s h
              have := hx0min w hw
              omega
        intro a ha b hb hab
        rcases mem_insert.mp ha with ha' | ha'
        · rcases mem_insert.mp hb with hb' | hb'
          · exact absurd (ha'.trans hb'.symm) hab
          · subst ha'; exact Or.inl (key b hb')
        · rcases mem_insert.mp hb with hb' | hb'
          · subst hb'; exact Or.inr (key a ha')
          · exact hchain a ha' b hb' hab
    · right
      by_cases hle : #t ≤ #M
      · refine ⟨M, hMs, ?_, hManti⟩
        have : c * #t ≤ c * #M := Nat.mul_le_mul_left c hle
        rw [hcard]; nlinarith
      · refine ⟨t, hts.trans hs's, ?_, hanti⟩
        rw [hcard]; push Not at hle; nlinarith

/-! ### Difference sets -/

/-- The set of positive differences of a finite set of natural numbers. -/
def diffs (B : Finset ℕ) : Finset ℕ :=
  ((B ×ˢ B).filter (fun p => p.1 < p.2)).image (fun p => p.2 - p.1)

lemma mem_diffs {B : Finset ℕ} {d : ℕ} :
    d ∈ diffs B ↔ ∃ x ∈ B, ∃ y ∈ B, x < y ∧ y - x = d := by
  simp only [diffs, mem_image, mem_filter, mem_product, Prod.exists]
  constructor
  · rintro ⟨x, y, ⟨⟨hx, hy⟩, hxy⟩, rfl⟩; exact ⟨x, hx, y, hy, hxy, rfl⟩
  · rintro ⟨x, hx, y, hy, hxy, rfl⟩; exact ⟨x, y, ⟨⟨hx, hy⟩, hxy⟩, rfl⟩

lemma diffs_mono {B B' : Finset ℕ} (h : B ⊆ B') : diffs B ⊆ diffs B' := by
  intro d hd
  obtain ⟨x, hx, y, hy, hxy, rfl⟩ := mem_diffs.mp hd
  exact mem_diffs.mpr ⟨x, h hx, y, h hy, hxy, rfl⟩

lemma exists_card_filter_lt_eq (X : Finset ℕ) (m : ℕ) (hm : m ≤ #X) :
    ∃ c, #(X.filter (· < c)) = m := by
  induction m with
  | zero => exact ⟨0, by simp⟩
  | succ m ih =>
    obtain ⟨c, hc⟩ := ih (by omega)
    have hne : (X.filter (fun x => c ≤ x)).Nonempty := by
      rw [← Finset.card_pos]
      have := Finset.card_filter_add_card_filter_not (s := X) (fun x => x < c)
      simp only [not_lt] at this
      omega
    obtain ⟨c', hc'X, hc'min⟩ := (X.filter (fun x => c ≤ x)).exists_min_image id hne
    simp only [mem_filter, id] at hc'X hc'min
    refine ⟨c' + 1, ?_⟩
    have : X.filter (· < c' + 1) = insert c' (X.filter (· < c)) := by
      ext x
      simp only [mem_filter, mem_insert]
      constructor
      · rintro ⟨hx, hxc⟩
        by_cases h : x < c
        · exact Or.inr ⟨hx, h⟩
        · left; have := hc'min x ⟨hx, by omega⟩; omega
      · rintro (rfl | ⟨hx, hxc⟩)
        · exact ⟨hc'X.1, by omega⟩
        · exact ⟨hx, by omega⟩
    rw [this, card_insert_of_notMem (by simp; omega), hc]

/-- **Greedy difference lemma.** A set `X` of at least `m² + m` natural numbers contains a subset
`B` of size `2m` with at least `m² / 2` distinct positive differences. -/
theorem exists_large_diffs (X : Finset ℕ) (m : ℕ) (hX : m * m + m ≤ #X) :
    ∃ B ⊆ X, #B = 2 * m ∧ m * m ≤ 2 * #(diffs B) := by
  classical
  obtain ⟨c, hc⟩ := exists_card_filter_lt_eq X m (by nlinarith)
  set B0 := X.filter (· < c) with hB0
  set X' := X.filter (fun x => ¬ x < c) with hX'
  have hcardX' : #X' = #X - m := by
    have hsplit : #B0 + #X' = #X := Finset.card_filter_add_card_filter_not _
    omega
  let DA : Finset ℕ → Finset ℕ := fun A => (A ×ˢ B0).image (fun p => p.1 - p.2)
  have hB0lt : ∀ b ∈ B0, b < c := fun b hb => (mem_filter.mp hb).2
  have hX'ge : ∀ a ∈ X', c ≤ a := fun a ha => by
    have := (mem_filter.mp ha).2; omega
  have claim : ∀ s, s ≤ m → ∃ A ⊆ X', #A ≤ s ∧ min (s * m) #X' ≤ 2 * #(DA A) := by
    intro s
    induction s with
    | zero => intro _; exact ⟨∅, by simp, by simp, by simp⟩
    | succ s ih =>
      intro hs
      obtain ⟨A, hAX, hAs, hAD⟩ := ih (by omega)
      by_cases hbig : #X' ≤ 2 * #(DA A)
      · exact ⟨A, hAX, by omega, le_trans (min_le_right _ _) hbig⟩
      push Not at hbig
      set D := DA A with hD
      have hsm : s * m ≤ 2 * #D := by
        rcases le_total (s * m) #X' with h | h
        · rw [min_eq_left h] at hAD; exact hAD
        · rw [min_eq_right h] at hAD; omega
      -- double counting
      have hsum : ∑ a ∈ X', #(B0.filter (fun b => a - b ∉ D)) =
          ∑ b ∈ B0, #(X'.filter (fun a => a - b ∉ D)) := by
        simp only [card_filter]
        exact Finset.sum_comm
      have hlow : ∀ b ∈ B0, #X' - #D ≤ #(X'.filter (fun a => a - b ∉ D)) := by
        intro b hb
        have h1 : #(X'.filter (fun a => a - b ∈ D)) ≤ #D := by
          apply Finset.card_le_card_of_injOn (fun a => a - b)
          · intro a ha
            simp only [coe_filter, Set.mem_ofPred_eq] at ha
            exact ha.2
          · intro a1 ha1 a2 ha2 h
            simp only [coe_filter, Set.mem_ofPred_eq] at ha1 ha2
            have := hX'ge a1 ha1.1
            have := hX'ge a2 ha2.1
            have := hB0lt b hb
            simp only at h
            omega
        have := Finset.card_filter_add_card_filter_not (s := X') (fun a => a - b ∈ D)
        omega
      have hmpos : 0 < m := by omega
      obtain ⟨a, haX, ha⟩ : ∃ a ∈ X', m < 2 * #(B0.filter (fun b => a - b ∉ D)) := by
        by_contra hcon
        push Not at hcon
        have h1 : 2 * ∑ a ∈ X', #(B0.filter (fun b => a - b ∉ D)) ≤ #X' * m := by
          rw [Finset.mul_sum]
          calc ∑ a ∈ X', 2 * #(B0.filter (fun b => a - b ∉ D)) ≤ ∑ a ∈ X', m :=
                Finset.sum_le_sum hcon
            _ = #X' * m := by simp
        have h2 : #B0 * (#X' - #D) ≤ ∑ b ∈ B0, #(X'.filter (fun a => a - b ∉ D)) := by
          calc #B0 * (#X' - #D) = ∑ b ∈ B0, (#X' - #D) := by simp
            _ ≤ _ := Finset.sum_le_sum hlow
        rw [hsum] at h1
        have hB0c : #B0 = m := hc
        rw [hB0c] at h2
        have h3 : m * (#X' - #D) * 2 ≤ #X' * m := by nlinarith
        have h4 : #X' - #D + (#X' - #D) > #X' := by omega
        nlinarith
      refine ⟨insert a A, ?_, ?_, ?_⟩
      · intro x hx
        rcases mem_insert.mp hx with rfl | hx
        · exact haX
        · exact hAX hx
      · exact le_trans (card_insert_le _ _) (by omega)
      · have hsub : D ∪ (B0.filter (fun b => a - b ∉ D)).image (fun b => a - b) ⊆
            DA (insert a A) := by
          intro d hd
          rcases mem_union.mp hd with hd | hd
          · simp only [hD, DA, mem_image, mem_product, Prod.exists] at hd ⊢
            obtain ⟨x, y, ⟨hx, hy⟩, rfl⟩ := hd
            exact ⟨x, y, ⟨mem_insert_of_mem hx, hy⟩, rfl⟩
          · simp only [mem_image, mem_filter] at hd
            obtain ⟨b, ⟨hb, -⟩, rfl⟩ := hd
            simp only [DA, mem_image, mem_product, Prod.exists]
            exact ⟨a, b, ⟨mem_insert_self _ _, hb⟩, rfl⟩
        have hdisj : Disjoint D ((B0.filter (fun b => a - b ∉ D)).image (fun b => a - b)) := by
          rw [Finset.disjoint_left]
          intro d hd hd'
          simp only [mem_image, mem_filter] at hd'
          obtain ⟨b, ⟨-, hb⟩, rfl⟩ := hd'
          exact hb hd
        have hcimg : #((B0.filter (fun b => a - b ∉ D)).image (fun b => a - b)) =
            #(B0.filter (fun b => a - b ∉ D)) := by
          apply Finset.card_image_of_injOn
          intro b1 hb1 b2 hb2 h
          simp only [coe_filter, Set.mem_ofPred_eq] at hb1 hb2
          have := hB0lt b1 hb1.1
          have := hB0lt b2 hb2.1
          have := hX'ge a haX
          simp only at h
          omega
        have := Finset.card_le_card hsub
        rw [card_union_of_disjoint hdisj, hcimg] at this
        have : (s + 1) * m ≤ 2 * #(DA (insert a A)) := by nlinarith
        exact le_trans (min_le_left _ _) this
  obtain ⟨A, hAX, hAm, hAD⟩ := claim m le_rfl
  have hmin : min (m * m) #X' = m * m := min_eq_left (by omega)
  rw [hmin] at hAD
  have hB'X : B0 ∪ A ⊆ X := union_subset (filter_subset _ _) (hAX.trans (filter_subset _ _))
  have hB'card : #(B0 ∪ A) ≤ 2 * m := by
    have := card_union_le B0 A
    have hB0c : #B0 = m := hc
    omega
  obtain ⟨B, hB'B, hBX, hBcard⟩ := Finset.exists_subsuperset_card_eq hB'X hB'card
    (by nlinarith)
  refine ⟨B, hBX, hBcard, ?_⟩
  have hsub : DA A ⊆ diffs B := by
    intro d hd
    simp only [DA, mem_image, mem_product, Prod.exists] at hd
    obtain ⟨x, y, ⟨hx, hy⟩, rfl⟩ := hd
    exact mem_diffs.mpr ⟨y, hB'B (mem_union_left _ hy), x, hB'B (mem_union_right _ hx),
      by have := hB0lt y hy; have := hX'ge x (hAX hx); omega, rfl⟩
  have := Finset.card_le_card hsub
  omega

/-! ### Up-sets of a family -/

lemma card_supersets_le (U T : Finset ℕ) :
    #(U.powerset.filter (fun S => T ⊆ S)) ≤ 2 ^ (#U - #T) := by
  by_cases hTU : T ⊆ U
  · have hsub : U.powerset.filter (fun S => T ⊆ S) ⊆ (U \ T).powerset.image (· ∪ T) := by
      intro S hS
      simp only [mem_filter, mem_powerset] at hS
      simp only [mem_image, mem_powerset]
      refine ⟨S \ T, sdiff_subset_sdiff hS.1 le_rfl, ?_⟩
      exact sdiff_union_of_subset hS.2
    calc #(U.powerset.filter (fun S => T ⊆ S)) ≤ #((U \ T).powerset.image (· ∪ T)) :=
          card_le_card hsub
      _ ≤ #((U \ T).powerset) := card_image_le
      _ = 2 ^ (#U - #T) := by rw [card_powerset, card_sdiff_of_subset hTU]
  · have : U.powerset.filter (fun S => T ⊆ S) = ∅ := by
      ext S
      simp only [mem_filter, mem_powerset, notMem_empty, iff_false, not_and]
      intro hS hTS
      exact hTU (hTS.trans hS)
    rw [this]; simp

/-- Union bound: the number of subsets of `U` containing a member of `𝓕`, where each member of
`𝓕` has at least `M` elements, is at most `#𝓕 · 2^(#U - M)`. -/
theorem card_upset_le (U : Finset ℕ) (𝓕 : Finset (Finset ℕ)) (M : ℕ)
    (hM : ∀ T ∈ 𝓕, M ≤ #T) :
    #(U.powerset.filter (fun S => ∃ T ∈ 𝓕, T ⊆ S)) ≤ #𝓕 * 2 ^ (#U - M) := by
  have hsub : U.powerset.filter (fun S => ∃ T ∈ 𝓕, T ⊆ S) ⊆
      𝓕.biUnion (fun T => U.powerset.filter (fun S => T ⊆ S)) := by
    intro S hS
    simp only [mem_filter, mem_powerset] at hS
    obtain ⟨hSU, T, hT, hTS⟩ := hS
    simp only [mem_biUnion, mem_filter, mem_powerset]
    exact ⟨T, hT, hSU, hTS⟩
  calc #(U.powerset.filter (fun S => ∃ T ∈ 𝓕, T ⊆ S))
      ≤ #(𝓕.biUnion (fun T => U.powerset.filter (fun S => T ⊆ S))) := card_le_card hsub
    _ ≤ ∑ T ∈ 𝓕, #(U.powerset.filter (fun S => T ⊆ S)) := card_biUnion_le
    _ ≤ ∑ T ∈ 𝓕, 2 ^ (#U - M) := by
        apply Finset.sum_le_sum
        intro T hT
        exact (card_supersets_le U T).trans
          (Nat.pow_le_pow_right (by norm_num) (by have := hM T hT; omega))
    _ = #𝓕 * 2 ^ (#U - M) := by simp

/-! ### Cycles in a graph containing the standard cycle `0, 1, …, L-1` -/

section Cycles

variable {n : ℕ} {H : SimpleGraph (Fin n)} {L : ℕ}

lemma StdCycle.adj_succ (hs : StdCycle H L) {i : ℕ} (hi : i + 1 < L) : AdjN H i (i + 1) :=
  hs.2.2.1 i hi

lemma StdCycle.adj_close (hs : StdCycle H L) : AdjN H (L - 1) 0 := hs.2.2.2

/-- A vertex `w` outside the cycle with neighbours `p < q` on it closes a cycle of length
`q - p + 2`. -/
theorem star_mem (hs : StdCycle H L) {w p q : ℕ} (hw : L ≤ w) (hpq : p < q) (hq : q < L)
    (hp : AdjN H p w) (hqw : AdjN H q w) : q - p + 2 ∈ cycleSet H := by
  classical
  set Z := Icc p q ∪ {w} with hZ
  have hcard : #Z = q - p + 2 := by
    rw [hZ, card_union_of_disjoint (by simp; omega), Nat.card_Icc, card_singleton]; omega
  rw [← hcard]
  refine mem_cycleSet_finset Z (by omega) ?_ p w (by simp [hZ]; omega) (by simp [hZ])
    ?_ ?_ hp.symm
  · intro u hu v hv huv hbtw
    simp only [hZ, mem_union, mem_Icc, mem_singleton] at hu hv
    rcases hv with hv | rfl
    · have hu' : p ≤ u ∧ u ≤ q := by omega
      by_cases h : u + 1 = v
      · subst h; exact hs.adj_succ (by omega)
      · exact absurd ⟨by omega, by omega⟩ (hbtw (u + 1) (by simp [hZ]; omega))
    · have hu' : p ≤ u ∧ u ≤ q := by omega
      by_cases h : u = q
      · subst h; exact hqw
      · exact absurd ⟨by omega, by omega⟩ (hbtw q (by simp [hZ]; omega))
  · intro z hz; simp only [hZ, mem_union, mem_Icc, mem_singleton] at hz; omega
  · intro z hz; simp only [hZ, mem_union, mem_Icc, mem_singleton] at hz; omega

/-- Two nested chords `(a₁, b₁)` inside `(a₂, b₂)` give a cycle of length
`(b₂ - a₂) - (b₁ - a₁) + 2`. -/
theorem nested_mem (hs : StdCycle H L) {a₁ b₁ a₂ b₂ : ℕ} (h21 : a₂ ≤ a₁) (h12 : a₁ < b₁)
    (h22 : b₁ ≤ b₂) (hb : b₂ < L) (hne : ¬ (a₁ = a₂ ∧ b₁ = b₂))
    (he : AdjN H a₁ b₁) (hf : AdjN H a₂ b₂) : (b₂ - a₂) - (b₁ - a₁) + 2 ∈ cycleSet H := by
  classical
  set Z := Icc a₂ a₁ ∪ Icc b₁ b₂ with hZ
  have hcard : #Z = (b₂ - a₂) - (b₁ - a₁) + 2 := by
    rw [hZ, card_union_of_disjoint, Nat.card_Icc, Nat.card_Icc]
    · omega
    · rw [Finset.disjoint_left]; intro x hx hx'; simp only [mem_Icc] at hx hx'; omega
  rw [← hcard]
  refine mem_cycleSet_finset Z (by omega) ?_ a₂ b₂ (by simp [hZ]; omega) (by simp [hZ]; omega)
    ?_ ?_ hf.symm
  · intro u hu v hv huv hbtw
    simp only [hZ, mem_union, mem_Icc] at hu hv
    by_cases h : u + 1 = v
    · subst h; exact hs.adj_succ (by omega)
    · have hu1 : u = a₁ ∧ v = b₁ := by
        by_contra hcon
        rcases hu with hu | hu
        · by_cases hua : u = a₁
          · have hvb : v ≠ b₁ := fun h' => hcon ⟨hua, h'⟩
            exact hbtw b₁ (by simp [hZ]; omega) ⟨by omega, by omega⟩
          · exact hbtw (u + 1) (by simp [hZ]; omega) ⟨by omega, by omega⟩
        · exact hbtw (u + 1) (by simp [hZ]; omega) ⟨by omega, by omega⟩
      rw [hu1.1, hu1.2]; exact he
  · intro z hz; simp only [hZ, mem_union, mem_Icc] at hz; omega
  · intro z hz; simp only [hZ, mem_union, mem_Icc] at hz; omega

/-- Two crossing chords `a₁ < a₂ < b₁ < b₂` give a cycle of length
`(a₂ + b₂) - (a₁ + b₁) + 2`. -/
theorem crossing_mem (hs : StdCycle H L) {a₁ b₁ a₂ b₂ : ℕ} (h1 : a₁ < a₂) (h2 : a₂ < b₁)
    (h3 : b₁ < b₂) (hb : b₂ < L) (he : AdjN H a₁ b₁) (hf : AdjN H a₂ b₂) :
    (a₂ + b₂) - (a₁ + b₁) + 2 ∈ cycleSet H := by
  set s := a₂ - a₁ with hsdef
  set k := (a₂ + b₂) - (a₁ + b₁) + 2 with hk
  let g : ℕ → ℕ := fun i => if i ≤ s then a₁ + i else b₂ - (i - (s + 1))
  have g1 : ∀ i, i ≤ s → g i = a₁ + i := fun i hi => by simp [g, hi]
  have g2 : ∀ i, s < i → g i = b₂ - (i - (s + 1)) := fun i hi => by
    simp [g, show ¬ i ≤ s by omega]
  refine mem_cycleSet_nat k (by omega) g ?_ ?_ ?_
  · intro i j hi hj hij
    rcases Nat.lt_or_ge s i with hi' | hi' <;> rcases Nat.lt_or_ge s j with hj' | hj'
    · rw [g2 i hi', g2 j hj'] at hij; omega
    · rw [g2 i hi', g1 j hj'] at hij; omega
    · rw [g1 i hi', g2 j hj'] at hij; omega
    · rw [g1 i hi', g1 j hj'] at hij; omega
  · intro i hi
    rcases Nat.lt_or_ge i s with hi' | hi'
    · rw [g1 i hi'.le, g1 (i + 1) hi', ← add_assoc]; exact hs.adj_succ (by omega)
    · rcases Nat.eq_or_lt_of_le hi' with rfl | hi''
      · rw [g1 _ le_rfl, g2 _ (by omega)]
        have e1 : a₁ + (a₂ - a₁) = a₂ := by omega
        have e2 : b₂ - (a₂ - a₁ + 1 - (a₂ - a₁ + 1)) = b₂ := by omega
        rw [e1, e2]; exact hf
      · rw [g2 i hi'', g2 (i + 1) (by omega)]
        have e : b₂ - (i - (s + 1)) = b₂ - (i + 1 - (s + 1)) + 1 := by omega
        rw [e]; exact (hs.adj_succ (by omega)).symm
  · rw [g2 (k - 1) (by omega), g1 0 (by omega)]
    have e1 : b₂ - (k - 1 - (s + 1)) = b₁ := by omega
    rw [e1, add_zero]; exact he.symm

/-- **Short-cutting.** A nonempty family `J` of pairwise non-overlapping chords (none of them
the edge `(0, L-1)`) can all be used to shortcut the standard cycle simultaneously. -/
theorem shortcut_mem (hs : StdCycle H L) (J : Finset (ℕ × ℕ)) (hJ : J.Nonempty)
    (hch : ∀ e ∈ J, e.1 + 2 ≤ e.2 ∧ e.2 < L ∧ AdjN H e.1 e.2 ∧ ¬ (e.1 = 0 ∧ e.2 = L - 1))
    (hdisj : ∀ e ∈ J, ∀ f ∈ J, e ≠ f → e.2 ≤ f.1 ∨ f.2 ≤ e.1) :
    (∑ e ∈ J, (e.2 - e.1 - 1)) + 3 ≤ L ∧ L - ∑ e ∈ J, (e.2 - e.1 - 1) ∈ cycleSet H := by
  classical
  set U := J.biUnion (fun e => Ioo e.1 e.2) with hU
  set Z := range L \ U with hZ
  have hUsub : U ⊆ range L := by
    intro x hx
    simp only [hU, mem_biUnion, mem_Ioo] at hx
    obtain ⟨e, he, h1, h2⟩ := hx
    have := (hch e he).2.1
    simp; omega
  have hUcard : #U = ∑ e ∈ J, (e.2 - e.1 - 1) := by
    rw [hU, card_biUnion]
    · simp [Nat.card_Ioo]
    · intro e he f hf hef
      simp only [Function.onFun]
      rw [Finset.disjoint_left]
      intro x hx hx'
      simp only [mem_Ioo] at hx hx'
      rcases hdisj e he f hf hef with h | h <;> omega
  have hZcard : #Z = L - #U := by rw [hZ, card_sdiff_of_subset hUsub, card_range]
  -- membership in `Z`
  have memZ : ∀ x, x ∈ Z ↔ x < L ∧ ∀ e ∈ J, ¬ (e.1 < x ∧ x < e.2) := by
    intro x
    simp only [hZ, hU, mem_sdiff, mem_range, mem_biUnion, mem_Ioo, not_exists, not_and]
  have endpt : ∀ e ∈ J, e.1 ∈ Z ∧ e.2 ∈ Z := by
    intro e he
    have hc := hch e he
    refine ⟨(memZ _).mpr ⟨by omega, fun f hf => ?_⟩, (memZ _).mpr ⟨hc.2.1, fun f hf => ?_⟩⟩
    · by_cases hef : e = f
      · subst hef; omega
      · rcases hdisj e he f hf hef with h | h
        · have := (hch f hf).1; omega
        · omega
    · by_cases hef : e = f
      · subst hef; omega
      · rcases hdisj e he f hf hef with h | h
        · omega
        · have := (hch f hf).1; omega
  have hL3 : 3 ≤ L := hs.1
  have h0 : 0 ∈ Z := (memZ 0).mpr ⟨by omega, fun e _ h => by omega⟩
  have hL1 : L - 1 ∈ Z := (memZ _).mpr ⟨by omega, fun e he h => by
    have := (hch e he).2.1; omega⟩
  have hZ3 : 3 ≤ #Z := by
    obtain ⟨e, he⟩ := hJ
    have hc := hch e he
    have he' := endpt e he
    by_cases h : e.1 = 0
    · have hsub : ({e.1, e.2, L - 1} : Finset ℕ) ⊆ Z := by
        intro x hx; simp only [mem_insert, mem_singleton] at hx
        rcases hx with rfl | rfl | rfl
        · exact he'.1
        · exact he'.2
        · exact hL1
      have := card_le_card hsub
      rw [card_insert_of_notMem (by simp; omega), card_insert_of_notMem (by simp; omega),
        card_singleton] at this
      omega
    · have hsub : ({0, e.1, e.2} : Finset ℕ) ⊆ Z := by
        intro x hx; simp only [mem_insert, mem_singleton] at hx
        rcases hx with rfl | rfl | rfl
        · exact h0
        · exact he'.1
        · exact he'.2
      have := card_le_card hsub
      rw [card_insert_of_notMem (by simp; omega), card_insert_of_notMem (by simp; omega),
        card_singleton] at this
      omega
  refine ⟨by omega, ?_⟩
  rw [← hUcard, ← hZcard]
  refine mem_cycleSet_finset Z hZ3 ?_ 0 (L - 1) h0 hL1 (fun z _ => Nat.zero_le _)
    (fun z hz => by have := ((memZ z).mp hz).1; omega) hs.adj_close
  intro u hu v hv huv hbtw
  by_cases h : u + 1 = v
  · subst h; exact hs.adj_succ ((memZ _).mp hv).1
  · have hu1 : u + 1 ∉ Z := fun hz => hbtw (u + 1) hz ⟨by omega, by omega⟩
    have hvL := ((memZ _).mp hv).1
    rw [memZ] at hu1
    push Not at hu1
    obtain ⟨e, he, h1, h2⟩ := hu1 (by omega)
    have hue : u = e.1 := by
      have := ((memZ u).mp hu).2 e he
      by_contra hne; exact this ⟨by omega, by omega⟩
    have hve : v = e.2 := by
      rcases Nat.lt_trichotomy v e.2 with hlt | heq | hgt
      · exact absurd ⟨by omega, hlt⟩ (((memZ v).mp hv).2 e he)
      · exact heq
      · exact absurd ⟨by omega, hgt⟩ (hbtw e.2 (endpt e he).2)
    rw [hue, hve]; exact (hch e he).2.2.1

end Cycles

/-! ### Fingerprints -/

open Classical in
/-- The cycle set of `H`, as a finset (all cycle lengths are at most `n`). -/
noncomputable def cyc {n : ℕ} (H : SimpleGraph (Fin n)) : Finset ℕ :=
  (range (n + 1)).filter (· ∈ cycleSet H)

lemma mem_cyc {n : ℕ} {H : SimpleGraph (Fin n)} {k : ℕ} : k ∈ cyc H ↔ k ∈ cycleSet H := by
  classical
  simp only [cyc, mem_filter, mem_range, and_iff_right_iff_imp]
  intro hk; have := (cycleSet_subset_Icc H hk).2; omega

/-- The fingerprint family: sets of the form `{d + 2 : d ∈ diffs B}` or `{L - d : d ∈ diffs B}`
with `#B = 2m`, `B ⊆ [0, 2n]`, `L ≤ n`, having at least `m² / 2` elements. -/
def fpFamily (n m : ℕ) : Finset (Finset ℕ) :=
  ((range (n + 1) ×ˢ powersetCard (2 * m) (range (2 * n + 1))).biUnion
    (fun p => {(diffs p.2).image (· + 2), (diffs p.2).image (p.1 - ·)})).filter
    (fun T => m * m ≤ 2 * #T)

lemma card_fpFamily_le (n m : ℕ) : #(fpFamily n m) ≤ 2 * (n + 1) * (2 * n + 1) ^ (2 * m) := by
  unfold fpFamily
  refine (card_filter_le _ _).trans ?_
  refine card_biUnion_le.trans ?_
  calc ∑ p ∈ range (n + 1) ×ˢ powersetCard (2 * m) (range (2 * n + 1)),
        #({(diffs p.2).image (· + 2), (diffs p.2).image (p.1 - ·)} : Finset (Finset ℕ))
      ≤ ∑ p ∈ range (n + 1) ×ˢ powersetCard (2 * m) (range (2 * n + 1)), 2 := by
        apply sum_le_sum; intro p _; exact card_le_two
    _ = 2 * ((n + 1) * (2 * n + 1).choose (2 * m)) := by
        simp [card_product, card_powersetCard, mul_comm]
    _ ≤ 2 * ((n + 1) * (2 * n + 1) ^ (2 * m)) := by
        gcongr; exact Nat.choose_le_pow _ _
    _ = 2 * (n + 1) * (2 * n + 1) ^ (2 * m) := by ring

section FP

variable {n : ℕ} {H : SimpleGraph (Fin n)}

/-- Fingerprint from a set `X` whose pairwise differences (plus two) are cycle lengths. -/
theorem fp_plus (m : ℕ) (X : Finset ℕ) (hXr : X ⊆ range (2 * n + 1)) (hX : m * m + m ≤ #X)
    (hcyc : ∀ x ∈ X, ∀ y ∈ X, x < y → y - x + 2 ∈ cycleSet H) :
    ∃ T ∈ fpFamily n m, T ⊆ cyc H := by
  obtain ⟨B, hBX, hBc, hBd⟩ := exists_large_diffs X m hX
  refine ⟨(diffs B).image (· + 2), ?_, ?_⟩
  · simp only [fpFamily, mem_filter, mem_biUnion, mem_product, mem_range, mem_powersetCard,
      Prod.exists, mem_insert, mem_singleton]
    refine ⟨⟨0, B, ⟨by omega, hBX.trans hXr, hBc⟩, Or.inl rfl⟩, ?_⟩
    rwa [card_image_of_injective _ (add_left_injective 2)]
  · intro k hk
    simp only [mem_image] at hk
    obtain ⟨d, hd, rfl⟩ := hk
    obtain ⟨x, hx, y, hy, hxy, rfl⟩ := mem_diffs.mp hd
    exact mem_cyc.mpr (hcyc x (hBX hx) y (hBX hy) hxy)

/-- Fingerprint from a set `X` such that `L` minus pairwise differences are cycle lengths. -/
theorem fp_minus (m L : ℕ) (hLn : L ≤ n) (X : Finset ℕ) (hXr : X ⊆ range (2 * n + 1))
    (hX : m * m + m ≤ #X)
    (hcyc : ∀ x ∈ X, ∀ y ∈ X, x < y → y - x ≤ L ∧ L - (y - x) ∈ cycleSet H) :
    ∃ T ∈ fpFamily n m, T ⊆ cyc H := by
  obtain ⟨B, hBX, hBc, hBd⟩ := exists_large_diffs X m hX
  refine ⟨(diffs B).image (L - ·), ?_, ?_⟩
  · simp only [fpFamily, mem_filter, mem_biUnion, mem_product, mem_range, mem_powersetCard,
      Prod.exists, mem_insert, mem_singleton]
    refine ⟨⟨L, B, ⟨by omega, hBX.trans hXr, hBc⟩, Or.inr rfl⟩, ?_⟩
    rwa [card_image_of_injOn]
    intro d1 hd1 d2 hd2 h
    obtain ⟨x1, hx1, y1, hy1, hxy1, rfl⟩ := mem_diffs.mp hd1
    obtain ⟨x2, hx2, y2, hy2, hxy2, rfl⟩ := mem_diffs.mp hd2
    have h1 := (hcyc x1 (hBX hx1) y1 (hBX hy1) hxy1).1
    have h2 := (hcyc x2 (hBX hx2) y2 (hBX hy2) hxy2).1
    simp only at h
    omega
  · intro k hk
    simp only [mem_image] at hk
    obtain ⟨d, hd, rfl⟩ := hk
    obtain ⟨x, hx, y, hy, hxy, rfl⟩ := mem_diffs.mp hd
    exact mem_cyc.mpr (hcyc x (hBX hx) y (hBX hy) hxy).2

end FP

/-! ### Graphs with a long cycle and many extra edges -/

/-- The pairs `(a, b)` (with `a < b`) that are edges of the standard cycle `0, 1, …, L-1`. -/
def StdPair (L : ℕ) (e : ℕ × ℕ) : Prop := (e.2 = e.1 + 1 ∧ e.2 < L) ∨ (e.1 = 0 ∧ e.2 = L - 1)

open Classical in
/-- The edges of `H` that are not edges of the standard cycle, as pairs `a < b`. -/
noncomputable def extraEdges {n : ℕ} (H : SimpleGraph (Fin n)) (L : ℕ) : Finset (ℕ × ℕ) :=
  (range n ×ˢ range n).filter (fun e => e.1 < e.2 ∧ AdjN H e.1 e.2 ∧ ¬ StdPair L e)

/-- Nesting of chords: `e` lies inside `f`. -/
def Nest (e f : ℕ × ℕ) : Prop := f.1 ≤ e.1 ∧ e.2 ≤ f.2 ∧ e ≠ f

/-- Chords that do not overlap: `e` lies to the left of `f`. -/
def LeftOf (e f : ℕ × ℕ) : Prop := e.2 ≤ f.1

/-- Two distinct chords that are neither nested nor non-overlapping cross. -/
lemma cross_of_not_nest_not_leftOf {e f : ℕ × ℕ} (hne : e ≠ f)
    (h1 : ¬ Nest e f) (h2 : ¬ Nest f e) (h3 : ¬ LeftOf e f)
    (hle : e.1 + e.2 ≤ f.1 + f.2) : e.1 < f.1 ∧ f.1 < e.2 ∧ e.2 < f.2 := by
  have h1' : ¬ (f.1 ≤ e.1 ∧ e.2 ≤ f.2) := fun h => h1 ⟨h.1, h.2, hne⟩
  have h2' : ¬ (e.1 ≤ f.1 ∧ f.2 ≤ e.2) := fun h => h2 ⟨h.1, h.2, Ne.symm hne⟩
  have hne' : ¬ (e.1 = f.1 ∧ e.2 = f.2) := fun h => hne (Prod.ext h.1 h.2)
  simp only [LeftOf, not_le] at h3
  omega

section Main

variable {n : ℕ} {H : SimpleGraph (Fin n)} {L : ℕ}

/-- **Container step.** If `H` contains the standard cycle `0, …, L-1` with `L ≥ n - K` and has
more than `r` further edges, where `r ≥ (m² + m)³ + K(m² + m + K)`, then the cycle set of `H`
contains a member of `fpFamily n m`. -/
theorem fingerprint_exists (hs : StdCycle H L) {K m r : ℕ} (hm : 1 ≤ m) (hL : n ≤ L + K)
    (hr : r < #(extraEdges H L))
    (hpar : (m * m + m) ^ 3 + K * (m * m + m + K) ≤ r) :
    ∃ T ∈ fpFamily n m, T ⊆ cyc H := by
  classical
  set κ := m * m + m with hκ
  have hκpos : 2 ≤ κ := by nlinarith
  have hLn : L ≤ n := hs.2.1
  by_cases hstar : ∃ w, L ≤ w ∧ w < n ∧ κ ≤ #((range L).filter (fun a => AdjN H a w))
  · obtain ⟨w, hw, hwn, hcard⟩ := hstar
    refine fp_plus m _ ?_ hcard ?_
    · intro x hx; simp only [mem_filter, mem_range] at hx ⊢; omega
    · intro p hp q hq hpq
      simp only [mem_filter, mem_range] at hp hq
      exact star_mem hs hw hpq hq.1 hp.2 hq.2
  push Not at hstar
  -- the chords of the standard cycle
  set R := (range L ×ˢ range L).filter (fun e => e.1 < e.2 ∧ AdjN H e.1 e.2 ∧ ¬ StdPair L e)
    with hR
  have hRprop : ∀ e ∈ R, e.1 + 2 ≤ e.2 ∧ e.2 < L ∧ AdjN H e.1 e.2 ∧ ¬ (e.1 = 0 ∧ e.2 = L - 1) := by
    intro e he
    simp only [hR, mem_filter, mem_product, mem_range, StdPair, not_or, not_and] at he
    obtain ⟨⟨h1, h2⟩, h3, h4, h5, h6⟩ := he
    refine ⟨?_, h2, h4, fun h => h6 h.1 h.2⟩
    by_contra hc
    exact h5 (by omega) h2
  -- many chords
  have hextra : #(extraEdges H L) ≤ #R + K * (κ + K) := by
    have hsub : extraEdges H L ⊆ R ∪ (Ico L n).biUnion
        (fun w => ((range w).filter (fun a => AdjN H a w)).image (fun a => (a, w))) := by
      intro e he
      simp only [extraEdges, mem_filter, mem_product, mem_range] at he
      obtain ⟨⟨h1, h2⟩, h3, h4, h5⟩ := he
      by_cases hL' : e.2 < L
      · apply mem_union_left
        simp only [hR, mem_filter, mem_product, mem_range]
        exact ⟨⟨by omega, hL'⟩, h3, h4, h5⟩
      · apply mem_union_right
        simp only [mem_biUnion, mem_Ico, mem_image, mem_filter, mem_range]
        exact ⟨e.2, ⟨by omega, h2⟩, e.1, ⟨h3, h4⟩, rfl⟩
    refine (card_le_card hsub).trans ((card_union_le _ _).trans ?_)
    gcongr
    refine card_biUnion_le.trans ?_
    calc ∑ w ∈ Ico L n, #(((range w).filter (fun a => AdjN H a w)).image (fun a => (a, w)))
        ≤ ∑ w ∈ Ico L n, (κ + K) := by
          apply sum_le_sum
          intro w hw
          simp only [mem_Ico] at hw
          refine card_image_le.trans ?_
          have hsub2 : (range w).filter (fun a => AdjN H a w) ⊆
              (range L).filter (fun a => AdjN H a w) ∪ Ico L w := by
            intro a ha
            simp only [mem_filter, mem_range] at ha
            simp only [mem_union, mem_filter, mem_range, mem_Ico]
            by_cases haL : a < L
            · exact Or.inl ⟨haL, ha.2⟩
            · exact Or.inr ⟨by omega, ha.1⟩
          refine (card_le_card hsub2).trans ((card_union_le _ _).trans ?_)
          have := hstar w hw.1 hw.2
          rw [Nat.card_Ico]
          omega
      _ = (n - L) * (κ + K) := by simp
      _ ≤ K * (κ + K) := by gcongr; omega
  have hRbig : κ ^ 3 ≤ #R := by omega
  have hRsub : ∀ e ∈ R, e.1 < e.2 := fun e he => by have := (hRprop e he).1; omega
  -- first dichotomy: nested chain, or an antichain for nesting
  rcases chain_or_antichain Nest (fun e => e.2 - e.1) κ R
      (fun e he f hf h => by
        have := hRsub e he; have := hRsub f hf
        simp only [Nest] at h
        obtain ⟨h1, h2, h3⟩ := h
        have hne' : ¬ (e.1 = f.1 ∧ e.2 = f.2) := fun h => h3 (Prod.ext h.1 h.2)
        omega)
      (fun e he f hf g hg hef hfg => by
        have := hRsub e he; have := hRsub f hf; have := hRsub g hg
        simp only [Nest] at hef hfg ⊢
        obtain ⟨h1, h2, h3⟩ := hef
        obtain ⟨h4, h5, h6⟩ := hfg
        refine ⟨by omega, by omega, fun hEG => ?_⟩
        subst hEG
        have hne' : ¬ (e.1 = f.1 ∧ e.2 = f.2) := fun h => h3 (Prod.ext h.1 h.2)
        omega) with
    ⟨t, htR, htc, hchain⟩ | ⟨A, hAR, hAc, hanti⟩
  · -- nested chain: differences of spans
    have hinj : Set.InjOn (fun e : ℕ × ℕ => e.2 - e.1) t := by
      intro e he f hf h
      by_contra hef
      have := hRsub e (htR he); have := hRsub f (htR hf)
      simp only at h
      rcases hchain e he f hf hef with h' | h' <;>
      · simp only [Nest] at h'
        obtain ⟨h1, h2, h3⟩ := h'
        have hne' : ¬ (e.1 = f.1 ∧ e.2 = f.2) := fun h => hef (Prod.ext h.1 h.2)
        omega
    refine fp_plus m (t.image (fun e => e.2 - e.1)) ?_ ?_ ?_
    · intro x hx
      simp only [mem_image] at hx
      obtain ⟨e, he, rfl⟩ := hx
      have := (hRprop e (htR he)).2.1
      simp only [mem_range]; omega
    · rw [card_image_of_injOn hinj]; omega
    · intro x hx y hy hxy
      simp only [mem_image] at hx hy
      obtain ⟨e, he, rfl⟩ := hx
      obtain ⟨f, hf, rfl⟩ := hy
      have hef : e ≠ f := by rintro rfl; omega
      have hpe := hRprop e (htR he)
      have hpf := hRprop f (htR hf)
      rcases hchain e he f hf hef with h' | h'
      · simp only [Nest] at h'
        obtain ⟨h1, h2, h3⟩ := h'
        exact nested_mem hs h1 (by omega) h2 hpf.2.1
          (fun h => h3 (Prod.ext h.1 h.2)) hpe.2.2.1 hpf.2.2.1
      · simp only [Nest] at h'
        obtain ⟨h1, h2, h3⟩ := h'
        have hne' : ¬ (f.1 = e.1 ∧ f.2 = e.2) := fun h => h3 (Prod.ext h.1 h.2)
        omega
  · -- antichain for nesting
    have hAbig : κ * κ ≤ #A := by
      have h1 : κ * (κ * κ) ≤ κ * #A := by
        calc κ * (κ * κ) = κ ^ 3 := by ring
          _ ≤ #R := hRbig
          _ ≤ κ * #A := hAc
      exact Nat.le_of_mul_le_mul_left h1 (by omega)
    rcases chain_or_antichain LeftOf (fun e => e.1) κ A
        (fun e he f hf h => by
          have := hRsub e (hAR he); simp only [LeftOf] at h; omega)
        (fun e he f hf g hg hef hfg => by
          have := hRsub f (hAR hf); simp only [LeftOf] at hef hfg ⊢; omega) with
      ⟨C, hCA, hCc, hCchain⟩ | ⟨A', hA'A, hA'c, hA'anti⟩
    · -- a chain of non-overlapping chords: prefix sums
      set u : ℕ × ℕ → ℕ := fun g => g.2 - g.1 - 1 with hu
      set P : ℕ × ℕ → ℕ := fun e => ∑ g ∈ C.filter (fun g => g.1 ≤ e.1), u g with hP
      have hCR : ∀ e ∈ C, e ∈ R := fun e he => hAR (hCA he)
      have hsubchain : ∀ J ⊆ C, J.Nonempty →
          (∑ g ∈ J, u g) + 3 ≤ L ∧ L - ∑ g ∈ J, u g ∈ cycleSet H := by
        intro J hJC hJ
        refine shortcut_mem hs J hJ (fun e he => hRprop e (hCR e (hJC he))) ?_
        intro e he f hf hef
        rcases hCchain e (hJC he) f (hJC hf) hef with h | h
        · exact Or.inl h
        · exact Or.inr h
      have hsplit : ∀ e ∈ C, ∀ f ∈ C, LeftOf e f →
          P f = P e + ∑ g ∈ C.filter (fun g => e.1 < g.1 ∧ g.1 ≤ f.1), u g := by
        intro e he f hf hef
        have he1 := hRsub e (hCR e he)
        simp only [LeftOf] at hef
        simp only [hP]
        rw [← Finset.sum_filter_add_sum_filter_not (C.filter (fun g => g.1 ≤ f.1))
          (fun g => g.1 ≤ e.1)]
        congr 1
        · congr 1; ext g; simp only [mem_filter]; constructor
          · rintro ⟨⟨h1, _⟩, h3⟩; exact ⟨h1, h3⟩
          · rintro ⟨h1, h3⟩; exact ⟨⟨h1, by omega⟩, h3⟩
        · congr 1; ext g; simp only [mem_filter, not_le]; constructor
          · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨h1, h3, h2⟩
          · rintro ⟨h1, h3, h2⟩; exact ⟨⟨h1, h2⟩, h3⟩
      have hupos : ∀ g ∈ C, 1 ≤ u g := fun g hg => by
        have := (hRprop g (hCR g hg)).1; simp only [hu]; omega
      have hPlt : ∀ e ∈ C, ∀ f ∈ C, LeftOf e f → P e < P f := by
        intro e he f hf hef
        rw [hsplit e he f hf hef]
        have hfJ : f ∈ C.filter (fun g => e.1 < g.1 ∧ g.1 ≤ f.1) := by
          simp only [mem_filter]
          have := hRsub e (hCR e he); simp only [LeftOf] at hef
          exact ⟨hf, by omega, le_rfl⟩
        have := Finset.single_le_sum (f := u) (fun g _ => Nat.zero_le _) hfJ
        have := hupos f hf
        omega
      have hPle : ∀ e ∈ C, P e + 3 ≤ L := by
        intro e he
        have hJ : (C.filter (fun g => g.1 ≤ e.1)).Nonempty := ⟨e, by simp [he]⟩
        exact (hsubchain _ (filter_subset _ _) hJ).1
      have hinj : Set.InjOn P C := by
        intro e he f hf h
        by_contra hef
        rcases hCchain e he f hf hef with h' | h'
        · have := hPlt e he f hf h'; omega
        · have := hPlt f hf e he h'; omega
      refine fp_minus m L hLn (C.image P) ?_ ?_ ?_
      · intro x hx
        simp only [mem_image] at hx
        obtain ⟨e, he, rfl⟩ := hx
        have := hPle e he
        simp only [mem_range]; omega
      · rw [card_image_of_injOn hinj]; omega
      · intro x hx y hy hxy
        simp only [mem_image] at hx hy
        obtain ⟨e, he, rfl⟩ := hx
        obtain ⟨f, hf, rfl⟩ := hy
        have hef : e ≠ f := by rintro rfl; omega
        rcases hCchain e he f hf hef with h' | h'
        · rw [hsplit e he f hf h']
          have hJ : (C.filter (fun g => e.1 < g.1 ∧ g.1 ≤ f.1)).Nonempty := by
            refine ⟨f, ?_⟩
            simp only [mem_filter]
            have := hRsub e (hCR e he); simp only [LeftOf] at h'
            exact ⟨hf, by omega, le_rfl⟩
          have hc := hsubchain _ (filter_subset _ _) hJ
          refine ⟨by omega, ?_⟩
          have e1 : P e + ∑ g ∈ C.filter (fun g => e.1 < g.1 ∧ g.1 ≤ f.1), u g - P e =
              ∑ g ∈ C.filter (fun g => e.1 < g.1 ∧ g.1 ≤ f.1), u g := by omega
          rw [e1]; exact hc.2
        · have := hPlt f hf e he h'; omega
    · -- pairwise crossing chords
      have hA'big : κ ≤ #A' := by
        have h1 : κ * κ ≤ κ * #A' := hAbig.trans hA'c
        exact Nat.le_of_mul_le_mul_left h1 (by omega)
      have hcross : ∀ e ∈ A', ∀ f ∈ A', e ≠ f → e.1 + e.2 ≤ f.1 + f.2 →
          e.1 < f.1 ∧ f.1 < e.2 ∧ e.2 < f.2 := by
        intro e he f hf hef hle
        exact cross_of_not_nest_not_leftOf hef
          (hanti e (hA'A he) f (hA'A hf)) (hanti f (hA'A hf) e (hA'A he))
          (hA'anti e he f hf) hle
      have hinj : Set.InjOn (fun e : ℕ × ℕ => e.1 + e.2) A' := by
        intro e he f hf h
        by_contra hef
        simp only at h
        have := hcross e he f hf hef (by omega)
        omega
      refine fp_plus m (A'.image (fun e => e.1 + e.2)) ?_ ?_ ?_
      · intro x hx
        simp only [mem_image] at hx
        obtain ⟨e, he, rfl⟩ := hx
        have := hRprop e (hAR (hA'A he))
        simp only [mem_range]; omega
      · rw [card_image_of_injOn hinj]; exact hA'big
      · intro x hx y hy hxy
        simp only [mem_image] at hx hy
        obtain ⟨e, he, rfl⟩ := hx
        obtain ⟨f, hf, rfl⟩ := hy
        have hef : e ≠ f := by rintro rfl; omega
        obtain ⟨h1, h2, h3⟩ := hcross e he f hf hef hxy.le
        have hpe := hRprop e (hAR (hA'A he))
        have hpf := hRprop f (hAR (hA'A hf))
        exact crossing_mem hs h1 h2 h3 hpf.2.1 hpe.2.2.1 hpf.2.2.1

end Main

/-! ### Counting -/

section Counting

variable {n : ℕ}

lemma cyc_congr {H G : SimpleGraph (Fin n)} (h : cycleSet H = cycleSet G) : cyc H = cyc G := by
  ext k; rw [mem_cyc, mem_cyc, h]

lemma adjN_iff_of_stdCycle {H : SimpleGraph (Fin n)} {L : ℕ} (hs : StdCycle H L) {a b : ℕ}
    (hab : a < b) (hb : b < n) :
    AdjN H a b ↔ StdPair L (a, b) ∨ (a, b) ∈ extraEdges H L := by
  classical
  constructor
  · intro h
    by_cases hp : StdPair L (a, b)
    · exact Or.inl hp
    · right
      simp only [extraEdges, mem_filter, mem_product, mem_range]
      exact ⟨⟨by omega, hb⟩, hab, h, hp⟩
  · rintro (h | h)
    · rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · simp only at h1 h2; subst h1; exact hs.adj_succ h2
      · simp only at h1 h2; subst h1 h2; exact hs.adj_close.symm
    · simp only [extraEdges, mem_filter] at h; exact h.2.2.1

lemma eq_of_extraEdges_eq {H₁ H₂ : SimpleGraph (Fin n)} {L : ℕ} (h₁ : StdCycle H₁ L)
    (h₂ : StdCycle H₂ L) (he : extraEdges H₁ L = extraEdges H₂ L) : H₁ = H₂ := by
  have key : ∀ a b : ℕ, a < b → b < n → (AdjN H₁ a b ↔ AdjN H₂ a b) := by
    intro a b hab hb
    rw [adjN_iff_of_stdCycle h₁ hab hb, adjN_iff_of_stdCycle h₂ hab hb, he]
  ext ⟨i, hi⟩ ⟨j, hj⟩
  rcases Nat.lt_trichotomy i j with hij | rfl | hij
  · have := key i j hij hj
    exact ⟨fun h => (this.mp ⟨hi, hj, h⟩).2.2, fun h => (this.mpr ⟨hi, hj, h⟩).2.2⟩
  · exact ⟨fun h => absurd h (H₁.loopless.irrefl _), fun h => absurd h (H₂.loopless.irrefl _)⟩
  · have := key j i hij hi
    exact ⟨fun h => (this.mp ⟨hj, hi, h.symm⟩).2.2.symm,
      fun h => (this.mpr ⟨hj, hi, h.symm⟩).2.2.symm⟩

lemma card_small_subsets_le (P : Finset (ℕ × ℕ)) (r : ℕ) :
    #(P.powerset.filter (fun E => #E ≤ r)) ≤ (r + 1) * (#P + 1) ^ r := by
  have hsub : P.powerset.filter (fun E => #E ≤ r) ⊆
      (range (r + 1)).biUnion (fun j => P.powersetCard j) := by
    intro E hE
    simp only [mem_filter, mem_powerset] at hE
    simp only [mem_biUnion, mem_range, mem_powersetCard]
    exact ⟨#E, by omega, hE.1, rfl⟩
  refine (card_le_card hsub).trans (card_biUnion_le.trans ?_)
  calc ∑ j ∈ range (r + 1), #(P.powersetCard j) ≤ ∑ j ∈ range (r + 1), (#P + 1) ^ r := by
        apply sum_le_sum
        intro j hj
        simp only [mem_range] at hj
        rw [card_powersetCard]
        calc (#P).choose j ≤ #P ^ j := Nat.choose_le_pow _ _
          _ ≤ (#P + 1) ^ j := Nat.pow_le_pow_left (by omega) _
          _ ≤ (#P + 1) ^ r := Nat.pow_le_pow_right (by omega) (by omega)
    _ = (r + 1) * (#P + 1) ^ r := by simp

open Classical in
/-- Graphs containing the standard `L`-cycle plus at most `r` further edges are few. -/
lemma card_stdCycle_sparse_le (L r : ℕ) :
    #((univ : Finset (SimpleGraph (Fin n))).filter
      (fun H => StdCycle H L ∧ #(extraEdges H L) ≤ r)) ≤ (r + 1) * (n * n + 1) ^ r := by
  classical
  have h := card_small_subsets_le (range n ×ˢ range n) r
  rw [card_product, card_range] at h
  refine le_trans (card_le_card_of_injOn (fun H => extraEdges H L) ?_ ?_) h
  · intro H hH
    simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hH
    simp only [coe_filter, mem_powerset, Set.mem_ofPred_eq]
    refine ⟨filter_subset _ _, hH.2⟩
  · intro H₁ hH₁ H₂ hH₂ he
    simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hH₁ hH₂
    exact eq_of_extraEdges_eq hH₁.1 hH₂.1 he

/-- The explicit bound on the number of cycle sets. -/
theorem card_cyc_le (K m r : ℕ) (hm : 1 ≤ m)
    (hpar : (m * m + m) ^ 3 + K * (m * m + m + K) ≤ r) :
    #((univ : Finset (SimpleGraph (Fin n))).image cyc) ≤
      2 ^ (n - K) + (n + 1) * ((r + 1) * (n * n + 1) ^ r) +
        2 * (n + 1) * (2 * n + 1) ^ (2 * m) * 2 ^ (n + 1 - m * m / 2) := by
  classical
  set 𝒜₁ : Finset (Finset ℕ) := (range (n - K)).powerset
  set 𝒜₂ : Finset (Finset ℕ) := (range (n + 1)).biUnion (fun L =>
    ((univ : Finset (SimpleGraph (Fin n))).filter
      (fun H => StdCycle H L ∧ #(extraEdges H L) ≤ r)).image cyc)
  set 𝒜₃ : Finset (Finset ℕ) :=
    (range (n + 1)).powerset.filter (fun S => ∃ T ∈ fpFamily n m, T ⊆ S)
  have hsub : (univ : Finset (SimpleGraph (Fin n))).image cyc ⊆ 𝒜₁ ∪ 𝒜₂ ∪ 𝒜₃ := by
    intro S hS
    simp only [mem_image, mem_univ, true_and] at hS
    obtain ⟨G, rfl⟩ := hS
    by_cases hlong : ∃ k ∈ cycleSet G, n ≤ k + K
    · obtain ⟨k, hk, hkK⟩ := hlong
      obtain ⟨H, hHG, hHs⟩ := exists_stdCycle G hk
      rw [← cyc_congr hHG]
      by_cases hsp : #(extraEdges H k) ≤ r
      · apply mem_union_left; apply mem_union_right
        simp only [𝒜₂, mem_biUnion, mem_range, mem_image, mem_filter, mem_univ, true_and]
        exact ⟨k, by have := hHs.2.1; omega, H, ⟨hHs, hsp⟩, rfl⟩
      · apply mem_union_right
        push Not at hsp
        obtain ⟨T, hT, hTS⟩ := fingerprint_exists hHs hm hkK hsp hpar
        simp only [𝒜₃, mem_filter, mem_powerset]
        refine ⟨?_, T, hT, hTS⟩
        intro x hx
        simp only [cyc, mem_filter] at hx
        exact hx.1
    · apply mem_union_left; apply mem_union_left
      simp only [𝒜₁, mem_powerset]
      intro x hx
      push Not at hlong
      have := hlong x (mem_cyc.mp hx)
      simp only [mem_range]; omega
  refine (card_le_card hsub).trans ?_
  refine (card_union_le _ _).trans (add_le_add ((card_union_le _ _).trans (add_le_add ?_ ?_)) ?_)
  · simp [𝒜₁]
  · refine card_biUnion_le.trans ?_
    calc ∑ L ∈ range (n + 1), #(((univ : Finset (SimpleGraph (Fin n))).filter
          (fun H => StdCycle H L ∧ #(extraEdges H L) ≤ r)).image cyc)
        ≤ ∑ L ∈ range (n + 1), (r + 1) * (n * n + 1) ^ r := by
          apply sum_le_sum; intro L _
          exact card_image_le.trans (card_stdCycle_sparse_le L r)
      _ = (n + 1) * ((r + 1) * (n * n + 1) ^ r) := by simp
  · have h := card_upset_le (range (n + 1)) (fpFamily n m) (m * m / 2) (by
      intro T hT
      simp only [fpFamily, mem_filter] at hT
      omega)
    rw [card_range] at h
    exact h.trans (Nat.mul_le_mul_right _ (card_fpFamily_le n m))

/-- `numCycleSets n` is at most the number of distinct finsets `cyc G`. -/
theorem numCycleSets_le_card (n : ℕ) :
    numCycleSets n ≤ #((univ : Finset (SimpleGraph (Fin n))).image cyc) := by
  classical
  rw [← Set.ncard_coe_finset]
  refine Set.ncard_le_ncard_of_injOn (fun A => (range (n + 1)).filter (· ∈ A)) ?_ ?_
  · rintro A ⟨G, rfl⟩
    simp only [coe_image, coe_univ, Set.image_univ, Set.mem_range]
    exact ⟨G, by ext k; simp [cyc]⟩
  · rintro A ⟨G₁, rfl⟩ B ⟨G₂, rfl⟩ h
    ext k
    have h1 := cycleSet_subset_Icc G₁ (a := k)
    have h2 := cycleSet_subset_Icc G₂ (a := k)
    have := congrArg (k ∈ ·) h
    simp only [mem_filter, mem_range, Set.mem_Icc] at this h1 h2
    constructor
    · intro hk; exact (this.mp ⟨by have := (h1 hk).2; omega, hk⟩).2
    · intro hk; exact (this.mpr ⟨by have := (h2 hk).2; omega, hk⟩).2

end Counting

/-! ### Asymptotics -/

lemma eventually_poly_le_two_pow (C c : ℕ) : ∃ j₀, ∀ j, j₀ ≤ j → C * (j + c) ^ 7 ≤ 2 ^ j := by
  obtain ⟨D, hD⟩ : ∃ D, D = C * 9 ^ 7 := ⟨_, rfl⟩
  refine ⟨8 * (D + c + 8), fun j hj => ?_⟩
  obtain ⟨q, hq⟩ : ∃ q, q = j / 8 := ⟨_, rfl⟩
  have hq1 : D + c + 8 ≤ q := by omega
  have h1 : j + c ≤ 9 * q := by omega
  have h2 : 8 * q ≤ j := by omega
  calc C * (j + c) ^ 7 ≤ C * (9 * q) ^ 7 := by gcongr
    _ = D * q ^ 7 := by rw [hD]; ring
    _ ≤ q * q ^ 7 := Nat.mul_le_mul_right _ (by omega)
    _ = q ^ 8 := by ring
    _ ≤ (2 ^ q) ^ 8 := Nat.pow_le_pow_left Nat.lt_two_pow_self.le _
    _ = 2 ^ (8 * q) := by ring
    _ ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) h2

/-- For every `K`, eventually `f(n) ≤ 3 · 2^(n - K)`. -/
theorem eventually_numCycleSets_le (K : ℕ) :
    ∃ N₀, ∀ n, N₀ ≤ n → K ≤ n ∧ numCycleSets n ≤ 3 * 2 ^ (n - K) := by
  obtain ⟨j₀, hj₀⟩ := eventually_poly_le_two_pow 200000 (K + 3)
  refine ⟨2 ^ (j₀ + 1), fun n hn => ?_⟩
  have hn0 : n ≠ 0 := by have := Nat.one_le_two_pow (n := j₀ + 1); omega
  obtain ⟨j, hj⟩ : ∃ j, j = Nat.log 2 n := ⟨_, rfl⟩
  have hjle : 2 ^ j ≤ n := hj ▸ Nat.pow_log_le_self 2 hn0
  have hnlt : n < 2 ^ (j + 1) := hj ▸ Nat.lt_pow_succ_log_self (by norm_num) n
  have hj₀j : j₀ ≤ j := by
    have := Nat.le_log_of_pow_le (b := 2) (by norm_num) hn
    omega
  obtain ⟨Q, hQ⟩ : ∃ Q, Q = j + K + 3 := ⟨_, rfl⟩
  have hA : 200000 * Q ^ 7 ≤ n := by rw [hQ]; exact (hj₀ j hj₀j).trans hjle
  have hQ1 : 3 ≤ Q := by omega
  have hQ7 : Q ≤ Q ^ 7 := Nat.le_self_pow (by norm_num) Q
  have hQ2 : Q * Q ≤ Q ^ 7 := by
    calc Q * Q = Q ^ 2 := by ring
      _ ≤ Q ^ 7 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have hKn : K ≤ n := by omega
  refine ⟨hKn, ?_⟩
  obtain ⟨ℓ, hℓ⟩ : ∃ ℓ, ℓ = j + 1 := ⟨_, rfl⟩
  rw [← hℓ] at hnlt
  obtain ⟨m, hm⟩ : ∃ m, m = 4 * Q := ⟨_, rfl⟩
  obtain ⟨r, hr⟩ : ∃ r, r = n / (4 * ℓ) := ⟨_, rfl⟩
  have hr4 : r * (4 * ℓ) ≤ n := hr ▸ Nat.div_mul_le_self n (4 * ℓ)
  have hrn : r ≤ n := hr ▸ Nat.div_le_self _ _
  -- the parameter condition
  have hpar : (m * m + m) ^ 3 + K * (m * m + m + K) ≤ r := by
    rw [hr, Nat.le_div_iff_mul_le (by omega)]
    have hmm : m * m + m ≤ 32 * (Q * Q) := by rw [hm]; nlinarith
    have hK : K ≤ Q := by omega
    have e3 : ℓ ≤ Q := by omega
    have h6 : Q ^ 3 ≤ Q ^ 6 := Nat.pow_le_pow_right (by omega) (by norm_num)
    have h6' : Q ^ 2 ≤ Q ^ 6 := Nat.pow_le_pow_right (by omega) (by norm_num)
    have e5 : Q * (32 * (Q * Q) + Q) ≤ 33 * Q ^ 6 := by nlinarith
    calc ((m * m + m) ^ 3 + K * (m * m + m + K)) * (4 * ℓ)
        ≤ ((32 * (Q * Q)) ^ 3 + Q * (32 * (Q * Q) + Q)) * (4 * Q) := by
          gcongr
      _ ≤ ((32 * (Q * Q)) ^ 3 + 33 * Q ^ 6) * (4 * Q) := by gcongr
      _ = 131204 * Q ^ 7 := by ring
      _ ≤ 200000 * Q ^ 7 := by gcongr; norm_num
      _ ≤ n := hA
  -- second term
  have hT2 : (n + 1) * ((r + 1) * (n * n + 1) ^ r) ≤ 2 ^ (n - K) := by
    have a1 : n + 1 ≤ 2 ^ ℓ := hnlt
    have a2 : r + 1 ≤ 2 ^ ℓ := by omega
    have a3 : n * n + 1 ≤ 2 ^ (2 * ℓ) := by
      have : n * n < 2 ^ ℓ * 2 ^ ℓ := Nat.mul_lt_mul'' hnlt hnlt
      rw [two_mul, pow_add]; omega
    have a4 : (n * n + 1) ^ r ≤ 2 ^ (2 * ℓ * r) := by
      rw [pow_mul]; exact Nat.pow_le_pow_left a3 r
    have a5 : 2 * ℓ + 2 * ℓ * r ≤ n - K := by
      have : 4 * Q ≤ n := by nlinarith
      have : 2 * (2 * ℓ * r) ≤ n := by nlinarith
      omega
    calc (n + 1) * ((r + 1) * (n * n + 1) ^ r) ≤ 2 ^ ℓ * (2 ^ ℓ * 2 ^ (2 * ℓ * r)) := by
          gcongr
      _ = 2 ^ (2 * ℓ + 2 * ℓ * r) := by rw [← pow_add, ← pow_add]; ring_nf
      _ ≤ 2 ^ (n - K) := Nat.pow_le_pow_right (by norm_num) a5
  -- third term
  have hT3 : 2 * (n + 1) * (2 * n + 1) ^ (2 * m) * 2 ^ (n + 1 - m * m / 2) ≤ 2 ^ (n - K) := by
    have hmm2 : m * m / 2 = 8 * (Q * Q) := by
      rw [hm]; have : 4 * Q * (4 * Q) = 2 * (8 * (Q * Q)) := by ring
      rw [this]; omega
    have b1 : n + 1 ≤ 2 ^ ℓ := hnlt
    have b2 : 2 * n + 1 ≤ 2 ^ (ℓ + 1) := by rw [pow_succ]; omega
    have b3 : 8 * (Q * Q) ≤ n + 1 := by nlinarith
    have b4 : 1 + ℓ + (ℓ + 1) * (2 * m) + (n + 1 - 8 * (Q * Q)) ≤ n - K := by
      have : 1 + ℓ + (ℓ + 1) * (2 * m) + K + 1 ≤ 8 * (Q * Q) := by
        rw [hm]
        have : ℓ + 1 ≤ Q - K - 1 := by omega
        have hQK : K + 1 + (ℓ + 1) = Q := by omega
        nlinarith
      omega
    calc 2 * (n + 1) * (2 * n + 1) ^ (2 * m) * 2 ^ (n + 1 - m * m / 2)
        ≤ 2 * 2 ^ ℓ * (2 ^ (ℓ + 1)) ^ (2 * m) * 2 ^ (n + 1 - 8 * (Q * Q)) := by
          rw [hmm2]; gcongr
      _ = 2 ^ (1 + ℓ + (ℓ + 1) * (2 * m) + (n + 1 - 8 * (Q * Q))) := by
          rw [← pow_mul, pow_add, pow_add, pow_add, pow_one]
      _ ≤ 2 ^ (n - K) := Nat.pow_le_pow_right (by norm_num) b4
  have hmain := (numCycleSets_le_card n).trans (card_cyc_le K m r (by omega) hpar)
  omega

/-- **Erdős Problem 84 (first question).** The number `f(n)` of distinct cycle sets of graphs on
`n` vertices satisfies `f(n) = o(2^n)`. -/
theorem erdos_84 :
    (fun n => (numCycleSets n : ℝ)) =o[Filter.atTop] (fun n => (2 : ℝ) ^ n) := by
  rw [Asymptotics.isLittleO_iff]
  intro c hc
  obtain ⟨K, hK⟩ := pow_unbounded_of_one_lt (3 / c) (by norm_num : (1 : ℝ) < 2)
  obtain ⟨N₀, hN₀⟩ := eventually_numCycleSets_le K
  rw [Filter.eventually_atTop]
  refine ⟨N₀, fun n hn => ?_⟩
  obtain ⟨hKn, hle⟩ := hN₀ n hn
  simp only [Real.norm_natCast, norm_pow, Real.norm_ofNat]
  have h3 : (3 : ℝ) < c * 2 ^ K := by
    rw [div_lt_iff₀ hc] at hK; linarith
  have hle' : (numCycleSets n : ℝ) ≤ 3 * 2 ^ (n - K) := by exact_mod_cast hle
  have hpow : (2 : ℝ) ^ n = 2 ^ (n - K) * 2 ^ K := by
    rw [← pow_add, Nat.sub_add_cancel hKn]
  rw [hpow]
  have hpos : (0 : ℝ) < 2 ^ (n - K) := by positivity
  nlinarith

/-- The same statement in ratio form: `f(n) / 2^n → 0`. -/
theorem erdos_84_tendsto :
    Filter.Tendsto (fun n => (numCycleSets n : ℝ) / 2 ^ n) Filter.atTop (nhds 0) :=
  erdos_84.tendsto_div_nhds_zero

/-- The same statement with explicit quantifiers: for every `ε > 0`, eventually
`f(n) ≤ ε · 2^n`. -/
theorem erdos_84_eps :
    ∀ ε : ℝ, ε > 0 → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → (numCycleSets n : ℝ) ≤ ε * (2 : ℝ) ^ n := by
  intro ε hε
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (Asymptotics.isLittleO_iff.mp erdos_84 hε)
  refine ⟨N, fun n hn => ?_⟩
  have := hN n hn
  simpa [Real.norm_natCast, norm_pow, Real.norm_ofNat] using this

/-! ### Sanity checks on the definitions -/

/-- The family of cycle sets of graphs on `Fin n` is finite, so `numCycleSets n` is its actual
number of elements. -/
theorem cycleSets_finite (n : ℕ) :
    {A : Set ℕ | ∃ G : SimpleGraph (Fin n), cycleSet G = A}.Finite :=
  Set.finite_range (cycleSet (V := Fin n))

/-- The empty graph has no cycles. -/
theorem cycleSet_bot {V : Type*} : cycleSet (⊥ : SimpleGraph V) = ∅ := by
  ext k
  simp only [Set.mem_empty_iff_false, iff_false]
  rintro ⟨v, p, hp, -⟩
  cases p with
  | nil => exact SimpleGraph.Walk.not_isCycle_nil hp
  | cons h _ => exact h

/-- The triangle `K₃` has a cycle of length `3`. -/
theorem three_mem_cycleSet_top : 3 ∈ cycleSet (⊤ : SimpleGraph (Fin 3)) := by
  refine mem_cycleSet_nat 3 le_rfl id (fun i j _ _ h => h) ?_ ?_
  · intro i hi
    exact ⟨by simp; omega, by simp; omega, by simp [Fin.ext_iff]⟩
  · exact ⟨by simp, by simp, by simp [Fin.ext_iff]⟩

/-- In particular the count is not degenerate: `f(3) ≥ 2`. -/
theorem two_le_numCycleSets_three : 2 ≤ numCycleSets 3 := by
  have hne : (∅ : Set ℕ) ≠ cycleSet (⊤ : SimpleGraph (Fin 3)) := by
    intro h; have := three_mem_cycleSet_top; rw [← h] at this; exact this
  have hsub : ({∅, cycleSet (⊤ : SimpleGraph (Fin 3))} : Set (Set ℕ)) ⊆
      {A : Set ℕ | ∃ G : SimpleGraph (Fin 3), cycleSet G = A} := by
    intro A hA
    rcases hA with rfl | rfl
    · exact ⟨⊥, cycleSet_bot⟩
    · exact ⟨⊤, rfl⟩
  have := Set.ncard_le_ncard hsub (cycleSets_finite 3)
  rwa [Set.ncard_pair hne] at this

end Erdos84
