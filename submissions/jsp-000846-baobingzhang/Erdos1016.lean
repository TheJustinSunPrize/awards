import Mathlib

/-!
# Erdős Problem #1016: Bondy's lower bound for pancyclic graphs

A graph on `n` vertices is *pancyclic* if it contains a cycle of every length `3 ≤ k ≤ n`.
Let `h(n)` be minimal such that some graph on `n` vertices with `n + h(n)` edges is pancyclic.
Bondy (1971) stated `log₂(n - 1) - 1 ≤ h(n)`; a proof was given by Griffin (2013).

We prove:
* `Erdos1016.card_sub_one_le_two_pow`: every pancyclic graph on `n ≥ 3` vertices with `m`
  edges satisfies `n - 1 ≤ 2 ^ (m + 1 - n)`;
* `Erdos1016.add_logb_le_card_edgeFinset`: the same in real form, `n + log₂(n - 1) - 1 ≤ m`;
* `Erdos1016.logb_sub_one_le_h`: `log₂(n - 1) - 1 ≤ h(n)` for `n ≥ 3`, where `h` is defined
  literally as in the problem (`Erdos1016.h_spec` checks that it is the minimum).

Proof: remove one edge from a Hamiltonian cycle to get a path `P` with `n - 1` edges and let
`R = E(G) \ E(P)`. Send each cycle length `k` to `E(C_k) ∩ R`. Every vertex has even degree in a
cycle, and a nonempty edge set inside a path has a vertex of degree one; hence the sets
`E(C_k) ∩ R` are nonempty and pairwise distinct, so `n - 2 ≤ 2 ^ |R| - 1`.
-/

open Finset

namespace Erdos1016

variable {V : Type*}

/-- `G` contains a cycle of length `k` (a cycle of length `k` has exactly `k` vertices). -/
def HasCycleOfLength (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∃ v, ∃ w : G.Walk v v, w.IsCycle ∧ w.length = k

/-- A graph on a finite vertex set of size `n` is pancyclic if it contains a cycle of every
length `k` with `3 ≤ k ≤ n`. -/
def IsPancyclic [Fintype V] (G : SimpleGraph V) : Prop :=
  ∀ k, 3 ≤ k → k ≤ Fintype.card V → HasCycleOfLength G k

/-- Having a cycle of length `k ≥ 3` is the same as containing a copy of the cycle graph `C_k`. -/
theorem hasCycleOfLength_iff_cycleGraph_isContained (G : SimpleGraph V) {k : ℕ} (hk : 3 ≤ k) :
    HasCycleOfLength G k ↔ (SimpleGraph.cycleGraph k).IsContained G :=
  (SimpleGraph.cycleGraph_isContained_iff hk).symm

/-- The minimum number of edges of a pancyclic graph on `n` vertices. -/
noncomputable def minPancyclicEdges (n : ℕ) : ℕ :=
  sInf {m | ∃ G : SimpleGraph (Fin n), IsPancyclic G ∧ G.edgeSet.ncard = m}

/-- Erdős #1016: `h n` is minimal such that there is a graph on `n` vertices with `n + h n`
edges which contains a cycle of every length `3 ≤ k ≤ n`. -/
noncomputable def h (n : ℕ) : ℤ := (minPancyclicEdges n : ℤ) - n

section Parity

variable [DecidableEq V]

/-- Every vertex lies in an even number of edges of `S`. -/
def EvenDeg (S : Finset (Sym2 V)) : Prop := ∀ x : V, Even #{e ∈ S | x ∈ e}

lemma evenDeg_symmDiff {S T : Finset (Sym2 V)} (hS : EvenDeg S) (hT : EvenDeg T) :
    EvenDeg (symmDiff S T) := by
  intro x
  obtain ⟨a, ha⟩ := hS x
  obtain ⟨b, hb⟩ := hT x
  have h1 : {e ∈ symmDiff S T | x ∈ e} = symmDiff {e ∈ S | x ∈ e} {e ∈ T | x ∈ e} := by
    ext e
    simp only [mem_filter, mem_symmDiff]
    tauto
  have h2 := card_sdiff_add_card_inter {e ∈ S | x ∈ e} {e ∈ T | x ∈ e}
  have h3 := card_sdiff_add_card_inter {e ∈ T | x ∈ e} {e ∈ S | x ∈ e}
  have h4 : #(symmDiff {e ∈ S | x ∈ e} {e ∈ T | x ∈ e}) =
      #({e ∈ S | x ∈ e} \ {e ∈ T | x ∈ e}) + #({e ∈ T | x ∈ e} \ {e ∈ S | x ∈ e}) := by
    rw [Finset.symmDiff_def, card_union_of_disjoint disjoint_sdiff_sdiff]
  rw [inter_comm] at h3
  rw [h1]
  exact ⟨a + b - #({e ∈ S | x ∈ e} ∩ {e ∈ T | x ∈ e}), by omega⟩

/-- A nonempty set of edges of a path has a vertex lying in exactly one of them. -/
lemma exists_card_eq_one_of_subset_path {G : SimpleGraph V} {u v : V} (p : G.Walk u v)
    (hp : p.IsPath) (D : Finset (Sym2 V)) (hD : D ⊆ p.edges.toFinset) (hne : D.Nonempty) :
    ∃ x, #{e ∈ D | x ∈ e} = 1 := by
  induction p generalizing D with
  | nil =>
    obtain ⟨e, he⟩ := hne
    simpa using hD he
  | @cons a w b hadj q ih =>
    rw [SimpleGraph.Walk.cons_isPath_iff] at hp
    by_cases hmem : s(a, w) ∈ D
    · refine ⟨a, card_eq_one.2 ⟨s(a, w), ?_⟩⟩
      ext e
      simp only [mem_filter, mem_singleton]
      constructor
      · rintro ⟨heD, hae⟩
        have he := hD heD
        simp only [SimpleGraph.Walk.edges_cons, List.toFinset_cons, mem_insert,
          List.mem_toFinset] at he
        rcases he with rfl | he
        · rfl
        · exfalso
          obtain ⟨y, rfl⟩ := Sym2.mem_iff_exists.1 hae
          exact hp.2 (q.fst_mem_support_of_mem_edges he)
      · rintro rfl
        exact ⟨hmem, Sym2.mem_mk_left _ _⟩
    · refine ih hp.1 D (fun e he => ?_) hne
      have he' := hD he
      simp only [SimpleGraph.Walk.edges_cons, List.toFinset_cons, mem_insert] at he'
      rcases he' with rfl | he'
      · exact absurd he hmem
      · exact he'

/-- An edge set with all degrees even contained in the edges of a path is empty. -/
lemma eq_empty_of_evenDeg_subset_path {G : SimpleGraph V} {u v : V} (p : G.Walk u v)
    (hp : p.IsPath) {D : Finset (Sym2 V)} (hD : D ⊆ p.edges.toFinset) (he : EvenDeg D) :
    D = ∅ := by
  by_contra hne
  obtain ⟨x, hx⟩ :=
    exists_card_eq_one_of_subset_path p hp D hD (nonempty_iff_ne_empty.2 hne)
  have := he x
  rw [hx] at this
  exact Nat.not_even_one this

/-- The edge set of a cycle has all degrees even. -/
lemma evenDeg_edges_of_isCycle {G : SimpleGraph V} {v : V} {c : G.Walk v v} (hc : c.IsCycle) :
    EvenDeg c.edges.toFinset := by
  intro x
  have h := (hc.isTrail.even_countP_edges_iff x).2 (fun hvv => (hvv rfl).elim)
  rw [List.countP_eq_length_filter, ← List.toFinset_card_of_nodup (hc.edges_nodup.filter _),
    List.toFinset_filter] at h
  simpa using h

end Parity

/-- A cycle of length `k` gives at least `k` edges. -/
lemma le_card_edgeFinset_of_hasCycleOfLength (G : SimpleGraph V) [Fintype G.edgeSet]
    [DecidableEq V] {k : ℕ} (hk : HasCycleOfLength G k) : k ≤ #G.edgeFinset := by
  obtain ⟨v, c, hc, rfl⟩ := hk
  rw [← c.length_edges, ← List.toFinset_card_of_nodup hc.edges_nodup]
  refine card_le_card fun e he => ?_
  rw [List.mem_toFinset] at he
  exact SimpleGraph.mem_edgeFinset.2 (c.edges_subset_edgeSet he)

/-- **Bondy's bound, integer form.** A pancyclic graph on `n ≥ 3` vertices with `m` edges
satisfies `n - 1 ≤ 2 ^ (m + 1 - n)`. -/
theorem card_sub_one_le_two_pow [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hn : 3 ≤ Fintype.card V) (hG : IsPancyclic G) :
    Fintype.card V - 1 ≤ 2 ^ (#G.edgeFinset + 1 - Fintype.card V) := by
  set n := Fintype.card V with hn_def
  -- a Hamiltonian cycle, minus one edge, is a path `p` with `n - 1` edges
  obtain ⟨v, c, hc, hlen⟩ := hG n hn le_rfl
  cases c with
  | nil => simp at hlen; omega
  | cons hadj p =>
  rw [SimpleGraph.Walk.cons_isCycle_iff] at hc
  have hp := hc.1
  simp only [SimpleGraph.Walk.length_cons] at hlen
  set F := p.edges.toFinset with hF_def
  have hFcard : #F = n - 1 := by
    rw [hF_def, List.toFinset_card_of_nodup hp.isTrail.edges_nodup, p.length_edges]
    omega
  have hFsub : F ⊆ G.edgeFinset := fun e he => by
    rw [hF_def, List.mem_toFinset] at he
    exact SimpleGraph.mem_edgeFinset.2 (p.edges_subset_edgeSet he)
  -- choose, for every length `k`, the edge set of a cycle of length `k`
  have key : ∀ k ∈ Icc 3 n, ∃ S : Finset (Sym2 V), S ⊆ G.edgeFinset ∧ #S = k ∧ EvenDeg S := by
    intro k hk
    rw [mem_Icc] at hk
    obtain ⟨x, c, hc, hl⟩ := hG k hk.1 hk.2
    refine ⟨c.edges.toFinset, fun e he => ?_, ?_, evenDeg_edges_of_isCycle hc⟩
    · rw [List.mem_toFinset] at he
      exact SimpleGraph.mem_edgeFinset.2 (c.edges_subset_edgeSet he)
    · rw [List.toFinset_card_of_nodup hc.edges_nodup, c.length_edges, hl]
  choose! S hSsub hScard hSeven using key
  have hle := card_le_card_of_injOn (s := Icc 3 n) (t := (G.edgeFinset \ F).powerset.erase ∅)
    (fun k => S k \ F) ?maps ?inj
  · rw [Nat.card_Icc, card_erase_of_mem (empty_mem_powerset _), card_powerset,
      card_sdiff_of_subset hFsub, hFcard] at hle
    have hexp : #G.edgeFinset - (n - 1) = #G.edgeFinset + 1 - n := by omega
    rw [hexp] at hle
    have := Nat.one_le_two_pow (n := #G.edgeFinset + 1 - n)
    omega
  case maps =>
    intro k hk
    have hk' := mem_Icc.1 hk
    rw [mem_coe, mem_erase, mem_powerset]
    refine ⟨fun h0 => ?_, sdiff_subset_sdiff (hSsub k hk) subset_rfl⟩
    rw [sdiff_eq_empty_iff_subset] at h0
    have := eq_empty_of_evenDeg_subset_path p hp h0 (hSeven k hk)
    have := hScard k hk
    simp_all
    omega
  case inj =>
    intro k hk k' hk' hkk
    simp only at hkk
    have hsub : symmDiff (S k) (S k') ⊆ F := by
      intro e he
      by_contra heF
      rw [mem_symmDiff] at he
      rcases he with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · have : e ∈ S k \ F := mem_sdiff.2 ⟨h1, heF⟩
        rw [hkk] at this
        exact h2 (mem_sdiff.1 this).1
      · have : e ∈ S k' \ F := mem_sdiff.2 ⟨h1, heF⟩
        rw [← hkk] at this
        exact h2 (mem_sdiff.1 this).1
    have hD := eq_empty_of_evenDeg_subset_path p hp hsub
      (evenDeg_symmDiff (hSeven k hk) (hSeven k' hk'))
    rw [symmDiff_eq_empty] at hD
    rw [← hScard k hk, ← hScard k' hk', hD]

/-- **Bondy's bound, real form.** A pancyclic graph on `n ≥ 3` vertices has at least
`n + log₂(n - 1) - 1` edges. -/
theorem add_logb_le_card_edgeFinset [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hn : 3 ≤ Fintype.card V) (hG : IsPancyclic G) :
    (Fintype.card V : ℝ) + Real.logb 2 (Fintype.card V - 1) - 1 ≤ #G.edgeFinset := by
  set n := Fintype.card V with hn_def
  have hm : n ≤ #G.edgeFinset :=
    le_card_edgeFinset_of_hasCycleOfLength G (hG n hn le_rfl)
  have hmain := card_sub_one_le_two_pow G hn hG
  rw [← hn_def] at hmain
  have hcast : (n : ℝ) - 1 ≤ (2 : ℝ) ^ (#G.edgeFinset + 1 - n) := by
    have : ((n - 1 : ℕ) : ℝ) ≤ ((2 ^ (#G.edgeFinset + 1 - n) : ℕ) : ℝ) := by
      exact_mod_cast hmain
    simpa [Nat.cast_sub (by omega : 1 ≤ n)] using this
  have hpos : (0 : ℝ) < n - 1 := by
    have : (3 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hlog := Real.logb_le_logb_of_le (b := 2) (by norm_num) hpos hcast
  rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num), mul_one,
    Nat.cast_sub (by omega), Nat.cast_add, Nat.cast_one] at hlog
  linarith

/-- **Bondy's bound for graphs on `Fin n`**, integer and real forms. -/
theorem pancyclic_edge_lower_bound (n : ℕ) (hn : 3 ≤ n) (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (hG : IsPancyclic G) :
    n - 1 ≤ 2 ^ (#G.edgeFinset + 1 - n) ∧
      (n : ℝ) + Real.logb 2 (n - 1) - 1 ≤ #G.edgeFinset := by
  have hn' : 3 ≤ Fintype.card (Fin n) := by simpa using hn
  have h1 := card_sub_one_le_two_pow G hn' hG
  have h2 := add_logb_le_card_edgeFinset G hn' hG
  simp only [Fintype.card_fin] at h1 h2
  exact ⟨h1, h2⟩

/-- The complete graph on `n` vertices is pancyclic (vacuously so for `n < 3`). -/
theorem isPancyclic_top (n : ℕ) : IsPancyclic (⊤ : SimpleGraph (Fin n)) := by
  intro k hk hkn
  rw [hasCycleOfLength_iff_cycleGraph_isContained _ hk]
  exact SimpleGraph.isContained_top_iff.2 ⟨Fin.castLEEmb (by simpa using hkn)⟩

/-- Pancyclicity is a real constraint: the empty graph on `3` vertices is not pancyclic. -/
theorem not_isPancyclic_bot : ¬ IsPancyclic (⊥ : SimpleGraph (Fin 3)) := fun hG => by
  have := le_card_edgeFinset_of_hasCycleOfLength _ (hG 3 le_rfl (by simp))
  simp at this

lemma edgeSet_ncard_eq (G : SimpleGraph V) [Fintype G.edgeSet] :
    G.edgeSet.ncard = #G.edgeFinset := by
  rw [← SimpleGraph.coe_edgeFinset, Set.ncard_coe_finset]

/-- `h n` is exactly the minimum from the problem: some pancyclic graph on `n` vertices has
`n + h n` edges, and every pancyclic graph on `n` vertices has at least `n + h n` edges. -/
theorem h_spec (n : ℕ) :
    (∃ G : SimpleGraph (Fin n), IsPancyclic G ∧ (G.edgeSet.ncard : ℤ) = n + h n) ∧
      ∀ G : SimpleGraph (Fin n), IsPancyclic G → (n : ℤ) + h n ≤ G.edgeSet.ncard := by
  have hne : {m | ∃ G : SimpleGraph (Fin n), IsPancyclic G ∧ G.edgeSet.ncard = m}.Nonempty :=
    ⟨_, ⊤, isPancyclic_top n, rfl⟩
  refine ⟨?_, fun G hG => ?_⟩
  · obtain ⟨G, hG, hGm⟩ := Nat.sInf_mem hne
    exact ⟨G, hG, by rw [hGm, h, minPancyclicEdges]; ring⟩
  · have : minPancyclicEdges n ≤ G.edgeSet.ncard := Nat.sInf_le ⟨G, hG, rfl⟩
    rw [h]
    omega

/-- **Erdős #1016, Bondy's lower bound.** For `n ≥ 3`, `log₂(n - 1) - 1 ≤ h(n)`. -/
theorem logb_sub_one_le_h (n : ℕ) (hn : 3 ≤ n) : Real.logb 2 (n - 1) - 1 ≤ (h n : ℝ) := by
  classical
  obtain ⟨⟨G, hG, hGm⟩, -⟩ := h_spec n
  have hb := add_logb_le_card_edgeFinset G (by simpa using hn) hG
  rw [Fintype.card_fin, ← edgeSet_ncard_eq] at hb
  have : ((G.edgeSet.ncard : ℤ) : ℝ) = ((n : ℤ) : ℝ) + (h n : ℝ) := by
    rw [hGm]; push_cast; ring
  push_cast at this
  linarith

/-- Integer form of the bound on `h`: `n - 1 ≤ 2 ^ (h n + 1)` for `n ≥ 3`. -/
theorem sub_one_le_two_pow_h (n : ℕ) (hn : 3 ≤ n) :
    0 ≤ h n ∧ n - 1 ≤ 2 ^ (h n + 1).toNat := by
  classical
  obtain ⟨⟨G, hG, hGm⟩, -⟩ := h_spec n
  have hb := card_sub_one_le_two_pow G (by simpa using hn) hG
  have hm := le_card_edgeFinset_of_hasCycleOfLength G (hG n hn (by simp))
  rw [Fintype.card_fin, ← edgeSet_ncard_eq] at hb
  rw [← edgeSet_ncard_eq] at hm
  have hexp : (h n + 1).toNat = G.edgeSet.ncard + 1 - n := by omega
  refine ⟨by omega, ?_⟩
  rw [hexp]
  exact hb

end Erdos1016
