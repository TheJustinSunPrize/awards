import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Mathlib.Combinatorics.SimpleGraph.CycleGraph
import Mathlib.Tactic
import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.Ramsey

/-!
JSP-000443 / Erdős 552: Boza's Theorem 6 and Corollary 8.
Mathematical source: https://arxiv.org/html/2409.12770v2
This file formalizes known mathematics, not a solution of the full open problem.
-/

open Finset SimpleGraph

namespace JSP443

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
lemma four_cycle_of_common {v w x y : V} (hvw : v ≠ w) (hxy : x ≠ y)
    (hvx : G.Adj v x) (hwx : G.Adj w x)
    (hvy : G.Adj v y) (hwy : G.Adj w y) : cycleGraph 4 ⊑ G := by
  let f : Fin 4 → V := ![v, x, w, y]
  have hvx' := hvx.ne
  have hwx' := hwx.ne
  have hvy' := hvy.ne
  have hwy' := hwy.ne
  have hf : Function.Injective f := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [f]
  refine ⟨⟨⟨f, ?_⟩, hf⟩⟩
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    simp_all [f, cycleGraph_adj, G.adj_comm] <;>
    exact False.elim ((by decide : (-2 : Fin 4) ≠ 1) hij)

lemma common_card_le_one (hfree : ¬cycleGraph 4 ⊑ G) {v w : V} (hvw : v ≠ w) :
    (G.neighborFinset v ∩ G.neighborFinset w).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro x hx y hy
  by_contra hxy
  simp only [mem_inter, mem_neighborFinset] at hx hy
  exact hfree (four_cycle_of_common G hvw hxy hx.1 hx.2 hy.1 hy.2)

omit [DecidableEq V] in
lemma star_iff (n : ℕ) :
    completeBipartiteGraph (Fin 1) (Fin n) ⊑ G ↔ ∃ v, n ≤ G.degree v := by
  rw [completeBipartiteGraph_isContained_iff]
  constructor
  · rintro ⟨l, r, hl, hr, h⟩
    simp only [Fintype.card_fin] at hl hr
    obtain ⟨v, rfl⟩ := Finset.card_eq_one.mp hl
    refine ⟨v, ?_⟩
    rw [← card_neighborFinset_eq_degree, ← hr]
    apply Finset.card_le_card
    intro x hx
    simpa using h (by simp) hx
  · rintro ⟨v, hv⟩
    obtain ⟨r, hr, hcard⟩ := Finset.exists_subset_card_eq hv
    refine ⟨{v}, r, by simp, by simpa using hcard, ?_⟩
    intro x hx y hy
    have : x = v := by simpa using hx
    subst x
    simpa using hr hy

/-- Delete exactly b+1 vertices while lowering the degree guarantee by only one. -/
theorem deletion_lemma (hfree : ¬cycleGraph 4 ⊑ G) (a b : ℕ)
    (ha : 1 ≤ a) (hb : 1 ≤ b) (hcard : Fintype.card V = a + 2*b)
    (hdeg : ∀ v, b ≤ G.degree v) :
    ∃ W : Finset V, W.card = a+b-1 ∧
      ∀ w ∈ W, b-1 ≤ (G.neighborFinset w ∩ W).card := by
  classical
  by_cases hex : ∃ v, G.degree v = b
  · obtain ⟨v, hv⟩ := hex
    let U := insert v (G.neighborFinset v)
    let W := (Finset.univ : Finset V) \ U
    have hU : U.card = b+1 := by simp [U, hv]
    have hW : W.card = a+b-1 := by
      simp only [W, card_sdiff_of_subset (subset_univ U), card_univ, hcard, hU]
      omega
    refine ⟨W, hW, ?_⟩
    intro w hw
    have hwU : w ∉ U := (mem_sdiff.mp hw).2
    have hwv : w ≠ v := by intro h; subst w; exact hwU (mem_insert_self _ _)
    have hnv : ¬G.Adj w v := by
      intro h
      exact hwU (mem_insert_of_mem (by simpa using h.symm))
    have hi : G.neighborFinset w ∩ U = G.neighborFinset w ∩ G.neighborFinset v := by
      ext x
      simp only [U, mem_inter, mem_insert]
      constructor
      · rintro ⟨hx, rfl | hxv⟩
        · exact (hnv (by simpa using hx)).elim
        · exact ⟨hx, hxv⟩
      · rintro ⟨hx, hxv⟩; exact ⟨hx, Or.inr hxv⟩
    have hle : (G.neighborFinset w ∩ U).card ≤ 1 := by
      rw [hi]; exact common_card_le_one G hfree hwv
    have hpart := Finset.card_sdiff_add_card_inter (G.neighborFinset w) U
    have heq : G.neighborFinset w ∩ W = G.neighborFinset w \ U := by
      ext; simp [W]
    rw [heq]
    have hd := hdeg w
    change b ≤ (G.neighborFinset w).card at hd
    omega
  · have hstrict : ∀ v, b+1 ≤ G.degree v := by
      intro v
      have h := hdeg v
      have hn : G.degree v ≠ b := fun hv => hex ⟨v, hv⟩
      omega
    have hpos : 0 < Fintype.card V := by omega
    obtain ⟨v⟩ := Fintype.card_pos_iff.mp hpos
    obtain ⟨S, hS, hScard⟩ := Finset.exists_subset_card_eq (hdeg v)
    let U := insert v S
    let W := (Finset.univ : Finset V) \ U
    have hvS : v ∉ S := fun h => G.notMem_neighborFinset_self v (hS h)
    have hU : U.card = b+1 := by simp [U, hvS, hScard]
    have hW : W.card = a+b-1 := by
      simp only [W, card_sdiff_of_subset (subset_univ U), card_univ, hcard, hU]
      omega
    refine ⟨W, hW, ?_⟩
    intro w hw
    have hwv : w ≠ v := by
      intro h; subst w
      exact (mem_sdiff.mp hw).2 (mem_insert_self _ _)
    have hSle : (G.neighborFinset w ∩ S).card ≤ 1 :=
      (Finset.card_le_card (Finset.inter_subset_inter_left hS)).trans
        (common_card_le_one G hfree hwv)
    have hsub : G.neighborFinset w ∩ U ⊆ insert v (G.neighborFinset w ∩ S) := by
      intro x hx
      simp only [U, mem_inter, mem_insert] at hx ⊢
      rcases hx with ⟨hx, rfl | hxS⟩
      · exact Or.inl rfl
      · exact Or.inr ⟨hx, hxS⟩
    have hle : (G.neighborFinset w ∩ U).card ≤ 2 := by
      have h1 := Finset.card_le_card hsub
      have h2 := Finset.card_insert_le v (G.neighborFinset w ∩ S)
      omega
    have hpart := Finset.card_sdiff_add_card_inter (G.neighborFinset w) U
    have heq : G.neighborFinset w ∩ W = G.neighborFinset w \ U := by
      ext; simp [W]
    rw [heq]
    have hd := hstrict w
    change b+1 ≤ (G.neighborFinset w).card at hd
    omega

/-- The exact Ramsey function used in the original Formal Conjectures statement. -/
noncomputable def f (n : ℕ) : ℕ :=
  SimpleGraph.graphRamsey (cycleGraph 4) (completeBipartiteGraph (Fin 1) (Fin n))

def RamseyAt (n N : ℕ) : Prop :=
  ∀ C : SimpleGraph (Fin N), cycleGraph 4 ⊑ C ∨
    completeBipartiteGraph (Fin 1) (Fin n) ⊑ Cᶜ

/-- A coarse finite bound, sufficient to justify the minimum in graphRamsey. -/
lemma ramseyAt_bound (n : ℕ) : RamseyAt n (2*n+2) := by
  classical
  intro C
  by_cases hc : cycleGraph 4 ⊑ C
  · exact Or.inl hc
  right
  by_contra hs
  have hd : ∀ v, n+2 ≤ C.degree v := by
    intro v
    have hh : Cᶜ.degree v < n := by
      apply Nat.lt_of_not_ge
      intro hn
      exact hs ((star_iff Cᶜ n).mpr ⟨v, hn⟩)
    rw [C.degree_compl v, Fintype.card_fin] at hh
    omega
  let v : Fin (2*n+2) := ⟨0, by omega⟩
  let w : Fin (2*n+2) := ⟨1, by omega⟩
  have hvw : v ≠ w := by simp [v, w]
  have hi := common_card_le_one C hc hvw
  have hu : (C.neighborFinset v ∪ C.neighborFinset w).card ≤ 2*n+2 :=
    (Finset.card_le_univ _).trans_eq (Fintype.card_fin _)
  have he := Finset.card_union_add_card_inter (C.neighborFinset v) (C.neighborFinset w)
  have hv := hd v
  have hw := hd w
  change n+2 ≤ (C.neighborFinset v).card at hv
  change n+2 ≤ (C.neighborFinset w).card at hw
  omega

omit [DecidableEq V] [DecidableRel G.Adj] in
lemma ramseyAt_lift {n N : ℕ} (h : RamseyAt n N) (hcard : N ≤ Fintype.card V) :
    cycleGraph 4 ⊑ G ∨ completeBipartiteGraph (Fin 1) (Fin n) ⊑ Gᶜ := by
  classical
  obtain ⟨e⟩ : Nonempty (Fin N ↪ V) :=
    Function.Embedding.nonempty_of_card_le (by simpa using hcard)
  have heq : (G.comap e)ᶜ = Gᶜ.comap e := by
    ext x y
    simp [SimpleGraph.comap_adj, SimpleGraph.compl_adj, e.injective.eq_iff]
  rcases h (G.comap e) with hc | hs
  · exact Or.inl (hc.trans ⟨(SimpleGraph.Embedding.comap e G).toCopy⟩)
  · rw [heq] at hs
    exact Or.inr (hs.trans ⟨(SimpleGraph.Embedding.comap e Gᶜ).toCopy⟩)

lemma ramseyAt_f (n : ℕ) : RamseyAt n (f n) := by
  exact Nat.sInf_mem (s := {N | RamseyAt n N}) ⟨2*n+2, ramseyAt_bound n⟩

lemma f_le_of_ramseyAt {n N : ℕ} (h : RamseyAt n N) : f n ≤ N :=
  Nat.sInf_le h

lemma lt_f_of_bad (n : ℕ) (hc : ¬cycleGraph 4 ⊑ G)
    (hs : ¬completeBipartiteGraph (Fin 1) (Fin n) ⊑ Gᶜ) : Fintype.card V < f n := by
  by_contra h
  have hh := ramseyAt_lift G (ramseyAt_f n) (Nat.le_of_not_gt h)
  exact hh.elim hc hs

lemma f_lower (n : ℕ) : n+1 ≤ f n := by
  classical
  have hc : ¬cycleGraph 4 ⊑ (⊥ : SimpleGraph (Fin n)) := by
    rintro ⟨c⟩
    have h := c.toHom.map_adj (show (cycleGraph 4).Adj 0 1 by decide)
    exact h
  have hs : ¬completeBipartiteGraph (Fin 1) (Fin n) ⊑ (⊥ : SimpleGraph (Fin n))ᶜ := by
    intro h
    obtain ⟨v, hv⟩ := (star_iff _ n).mp h
    have hh := (⊥ : SimpleGraph (Fin n))ᶜ.degree_lt_card_verts v
    simp only [Fintype.card_fin] at hh
    omega
  have hh := lt_f_of_bad (⊥ : SimpleGraph (Fin n)) n hc hs
  simpa using hh

/-- Boza, Theorem 6: a uniform disjunction for all positive a and b. -/
theorem boza_theorem6 (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) :
    a+b ≤ f a ∨ f (a+b) ≤ a+2*b := by
  classical
  by_cases hf : f (a+b) ≤ a+2*b
  · exact Or.inr hf
  left
  have hnot : ¬RamseyAt (a+b) (a+2*b) := fun h => hf (f_le_of_ramseyAt h)
  obtain ⟨C, hc, hs⟩ : ∃ C : SimpleGraph (Fin (a+2*b)),
      ¬cycleGraph 4 ⊑ C ∧ ¬completeBipartiteGraph (Fin 1) (Fin (a+b)) ⊑ Cᶜ := by
    simpa only [RamseyAt, not_forall, not_or] using hnot
  have hd : ∀ v, b ≤ C.degree v := by
    intro v
    have hh : Cᶜ.degree v < a+b := by
      apply Nat.lt_of_not_ge
      intro hn
      exact hs ((star_iff Cᶜ (a+b)).mpr ⟨v, hn⟩)
    rw [C.degree_compl v, Fintype.card_fin] at hh
    omega
  obtain ⟨W, hW, hdW⟩ := deletion_lemma C hc a b ha hb (Fintype.card_fin _) hd
  let S : Set (Fin (a+2*b)) := ↑W
  let D := C.induce S
  have hDcard : Fintype.card S = a+b-1 := by simpa [S] using hW
  have hDc : ¬cycleGraph 4 ⊑ D := fun h => hc (h.trans ⟨Copy.induce C S⟩)
  have hDd : ∀ v, b-1 ≤ D.degree v := by
    intro v
    have hh := hdW v v.prop
    have he : (C.neighborFinset v ∩ W).card = D.degree v := by
      rw [← D.card_neighborSet_eq_degree v, ← Fintype.card_coe]
      apply Fintype.card_congr
      refine {
        toFun := fun x => ⟨⟨x, (mem_inter.mp x.prop).2⟩, ?_⟩
        invFun := fun x => ⟨x.val, ?_⟩
        left_inv := by intro x; rfl
        right_inv := by intro x; rfl }
      · exact (mem_neighborFinset C _ _).mp (mem_inter.mp x.prop).1
      · exact mem_inter.mpr ⟨(mem_neighborFinset C _ _).mpr x.prop, x.val.prop⟩
    exact hh.trans_eq he
  have hDs : ¬completeBipartiteGraph (Fin 1) (Fin a) ⊑ Dᶜ := by
    intro h
    obtain ⟨v, hv⟩ := (star_iff Dᶜ a).mp h
    rw [D.degree_compl v, hDcard] at hv
    have hh := hDd v
    omega
  have hh := lt_f_of_bad D a hDc hDs
  rw [hDcard] at hh
  omega

/-- Boza, Corollary 8, with the same Ramsey definition as Erdős 552. -/
theorem boza_corollary8 (n : ℕ) (hn : 1 ≤ n) :
    f (f n + 1) ≤ 2 * f n - n + 2 := by
  have hl := f_lower n
  have hb : 1 ≤ f n - n + 1 := by omega
  have h := boza_theorem6 n (f n - n + 1) hn hb
  have he : n + (f n - n + 1) = f n + 1 := by omega
  rw [he] at h
  rcases h with h | h
  · omega
  · omega

#print axioms boza_theorem6
#print axioms boza_corollary8
#check @boza_theorem6
#check @boza_corollary8

end JSP443
