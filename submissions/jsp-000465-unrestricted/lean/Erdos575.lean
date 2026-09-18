/-
Copyright (c) 2026 The Justin Sun Prize contributors.
Released under the MIT license; see LICENSE.
AI assistance: Codex. Mathematical source: Lefkowitz--Wigderson.
-/
import Mathlib.Combinatorics.SimpleGraph.Extremal.Basic
import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Tauto

/-!
The Lefkowitz--Wigderson counterexample to the unrestricted compactness question.
This file does not address the variant requiring connected forbidden graphs,
or the variant excluding forests.
-/

open SimpleGraph Finset

namespace Erdos575

/-- The two-edge star, with its centre labelled 0. -/
def twoStar : SimpleGraph (Fin 3) where
  Adj a b := (a = 0 ∧ b ≠ 0) ∨ (b = 0 ∧ a ≠ 0)
  symm := ⟨by intro a b; tauto⟩
  loopless := ⟨by intro a; simp⟩

/-- Two vertex-disjoint edges, on the pairs {0,1} and {2,3}. -/
def twoMatching : SimpleGraph (Fin 4) where
  Adj a b := a.val / 2 = b.val / 2 ∧ a ≠ b
  symm := ⟨by intro a b h; exact ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨by intro a; simp⟩

theorem twoStar_bipartite : twoStar.IsBipartite := by
  refine ⟨Coloring.mk (fun x => if x = 0 then 0 else 1) ?_⟩
  intro a b h
  rcases h with h | h <;> simp [h.1, h.2]

theorem twoMatching_bipartite : twoMatching.IsBipartite := by
  refine ⟨Coloring.mk (fun x => ⟨x.val % 2, Nat.mod_lt _ (by decide)⟩) ?_⟩
  intro a b h
  fin_cases a <;> fin_cases b <;> simp_all [twoMatching]

lemma contains_twoStar {V : Type*} (G : SimpleGraph V) {a b c : V}
    (hab : G.Adj a b) (hac : G.Adj a c) (hbc : b ≠ c) : twoStar ⊑ G := by
  have hneab := hab.ne
  have hneac := hac.ne
  refine ⟨⟨⟨(fun i => if i = 0 then a else if i = 1 then b else c), ?_⟩, ?_⟩⟩
  · intro i j h
    fin_cases i <;> fin_cases j <;>
      simp_all [twoStar, SimpleGraph.adj_comm]
  · intro i j h
    fin_cases i <;> fin_cases j <;> simp_all

lemma contains_twoMatching {V : Type*} (G : SimpleGraph V) {a b c d : V}
    (hab : G.Adj a b) (hcd : G.Adj c d)
    (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) :
    twoMatching ⊑ G := by
  have hneab := hab.ne
  have hnecd := hcd.ne
  refine ⟨⟨⟨(fun i => if i = 0 then a else if i = 1 then b else if i = 2 then c else d), ?_⟩, ?_⟩⟩
  · intro i j h
    fin_cases i <;> fin_cases j <;>
      simp_all [twoMatching, SimpleGraph.adj_comm]
  · intro i j h
    fin_cases i <;> fin_cases j <;> simp_all

/-- Avoiding both patterns forces any two unordered edges to be equal. -/
lemma edges_equal_of_free {V : Type*} {G : SimpleGraph V}
    (hs : twoStar.Free G) (hm : twoMatching.Free G)
    {a b c d : V} (hab : G.Adj a b) (hcd : G.Adj c d) :
    s(a,b) = s(c,d) := by
  have uniq {x y z : V} (hxy : G.Adj x y) (hxz : G.Adj x z) : y = z := by
    by_contra h
    exact hs (contains_twoStar G hxy hxz h)
  by_cases hac : a = c
  · subst c
    rw [uniq hab hcd]
  by_cases had : a = d
  · subst d
    rw [uniq hab hcd.symm, Sym2.eq_swap]
  by_cases hbc : b = c
  · subst c
    rw [uniq hab.symm hcd, Sym2.eq_swap]
  by_cases hbd : b = d
  · subst d
    rw [uniq hab.symm hcd.symm]
  exact (hm (contains_twoMatching G hab hcd hac had hbc hbd)).elim

theorem card_edges_le_one {V : Type*} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hs : twoStar.Free G) (hm : twoMatching.Free G) :
    G.edgeFinset.card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro e he f hf
  induction e using Sym2.inductionOn with | _ a b =>
    induction f using Sym2.inductionOn with | _ c d =>
      exact edges_equal_of_free hs hm (G.mem_edgeFinset.mp he) (G.mem_edgeFinset.mp hf)

/-- A matching, possibly with one isolated vertex. -/
def matching (n : ℕ) : SimpleGraph (Fin n) where
  Adj a b := a.val / 2 = b.val / 2 ∧ a ≠ b
  symm := ⟨by intro a b h; exact ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨by intro a; simp⟩

/-- A star; the definition also covers the empty vertex type. -/
def star (n : ℕ) : SimpleGraph (Fin n) where
  Adj a b := (a.val = 0 ∧ b.val ≠ 0) ∨ (b.val = 0 ∧ a.val ≠ 0)
  symm := ⟨by intro a b; tauto⟩
  loopless := ⟨by intro a; simp⟩

lemma matching_neighbor_unique {n : ℕ} {a b c : Fin n}
    (hab : (matching n).Adj a b) (hac : (matching n).Adj a c) : b = c := by
  obtain ⟨hab, hab'⟩ := hab
  obtain ⟨hac, hac'⟩ := hac
  have hb : a.val ≠ b.val := fun h => hab' (Fin.ext h)
  have hc : a.val ≠ c.val := fun h => hac' (Fin.ext h)
  apply Fin.ext
  omega

theorem matching_free_twoStar (n : ℕ) : twoStar.Free (matching n) := by
  intro ⟨f⟩
  have h01 := f.toHom.map_rel (show twoStar.Adj 0 1 from by simp [twoStar])
  have h02 := f.toHom.map_rel (show twoStar.Adj 0 2 from by simp [twoStar])
  have h := f.injective (matching_neighbor_unique h01 h02)
  norm_num at h

theorem star_free_twoMatching (n : ℕ) : twoMatching.Free (star n) := by
  intro ⟨f⟩
  have h01 := f.toHom.map_rel (show twoMatching.Adj 0 1 from by simp [twoMatching])
  have h23 := f.toHom.map_rel (show twoMatching.Adj 2 3 from by simp [twoMatching])
  rcases h01 with h01 | h01 <;> rcases h23 with h23 | h23
  all_goals
    have h := f.injective (Fin.ext (h01.1.trans h23.1.symm))
    norm_num at h

open scoped Classical in
lemma matching_many_edges (m : ℕ) : m ≤ (matching (2*m)).edgeFinset.card := by
  let edge (i : Fin m) : Sym2 (Fin (2*m)) :=
    s(⟨2*i.val, by omega⟩, ⟨2*i.val+1, by omega⟩)
  have mem (i : Fin m) : edge i ∈ (matching (2*m)).edgeFinset := by
    apply (matching (2*m)).mem_edgeFinset.mpr
    change (2*i.val)/2 = (2*i.val+1)/2 ∧ _
    constructor
    · omega
    · intro h
      have heq : 2*i.val = 2*i.val+1 := congrArg Fin.val h
      omega
  have inj : Function.Injective edge := by
    intro i j h
    simp only [edge, Sym2.eq_iff, Fin.mk.injEq] at h
    apply Fin.ext
    omega
  simpa using Finset.card_le_card_of_injOn (s := Finset.univ) (t := (matching (2*m)).edgeFinset) edge (fun i _ => mem i) (by
    intro i hi j hj h
    exact inj h)

open scoped Classical in
lemma star_many_edges {m : ℕ} (hm : 1 ≤ m) : m ≤ (star (2*m)).edgeFinset.card := by
  let edge (i : Fin m) : Sym2 (Fin (2*m)) :=
    s(⟨0, by omega⟩, ⟨i.val+1, by omega⟩)
  have mem (i : Fin m) : edge i ∈ (star (2*m)).edgeFinset := by
    apply (star (2*m)).mem_edgeFinset.mpr
    change (0 = 0 ∧ i.val+1 ≠ 0) ∨ _
    exact Or.inl ⟨rfl, by omega⟩
  have inj : Function.Injective edge := by
    intro i j h
    simp only [edge, Sym2.eq_iff, Fin.mk.injEq] at h
    apply Fin.ext
    omega
  simpa using Finset.card_le_card_of_injOn (s := Finset.univ) (t := (star (2*m)).edgeFinset) edge (fun i _ => mem i) (by
    intro i hi j hj h
    exact inj h)

open scoped Classical in
/-- Extremal number of a finite family, with ordinary (not induced) subgraphs. -/
noncomputable def familyExtremal {ι : Type*} [Fintype ι] {k : ι → ℕ}
    (F : (i : ι) → SimpleGraph (Fin (k i))) (n : ℕ) : ℕ :=
  Finset.sup {G : SimpleGraph (Fin n) | ∀ i, (F i).Free G}
    (fun G => G.edgeFinset.card)

def orders : Bool → ℕ | false => 3 | true => 4

def forbidden : (i : Bool) → SimpleGraph (Fin (orders i))
  | false => twoStar
  | true => twoMatching

theorem forbidden_bipartite (i : Bool) : (forbidden i).IsBipartite := by
  cases i
  · exact twoStar_bipartite
  · exact twoMatching_bipartite

theorem familyExtremal_le_one (n : ℕ) : familyExtremal forbidden n ≤ 1 := by
  classical
  rw [familyExtremal, Finset.sup_le_iff]
  intro G hG
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hG
  exact card_edges_le_one G (hG false) (hG true)

theorem member_extremal_lower (i : Bool) {m : ℕ} (hm : 1 ≤ m) :
    m ≤ extremalNumber (2*m) (forbidden i) := by
  classical
  cases i
  · have h := card_edgeFinset_le_extremalNumber (matching_free_twoStar (2*m))
    simp only [Fintype.card_fin] at h
    exact (matching_many_edges m).trans h
  · have h := card_edgeFinset_le_extremalNumber (star_free_twoMatching (2*m))
    simp only [Fintype.card_fin] at h
    exact (star_many_edges hm).trans h

/-- Every member fails every eventual constant-factor bound. -/
theorem no_member_bound (i : Bool) (C : ℝ) (hC : 0 ≤ C) (N : ℕ) :
    ∃ n : ℕ, N ≤ n ∧
      C * (familyExtremal forbidden n : ℝ) < (extremalNumber n (forbidden i) : ℝ) := by
  obtain ⟨r, hr⟩ := exists_nat_gt C
  let m := r + N + 1
  have hm : 1 ≤ m := by omega
  refine ⟨2*m, by omega, ?_⟩
  have hfamily : (familyExtremal forbidden (2*m) : ℝ) ≤ 1 := by
    exact_mod_cast familyExtremal_le_one (2*m)
  have hmember : (m : ℝ) ≤ (extremalNumber (2*m) (forbidden i) : ℝ) := by
    exact_mod_cast member_extremal_lower i hm
  have hmr : (r : ℝ) < (m : ℝ) := by
    exact_mod_cast (show r < m by omega)
  calc
    C * (familyExtremal forbidden (2*m) : ℝ) ≤ C := mul_le_of_le_one_right hC hfamily
    _ < (r : ℝ) := hr
    _ < (m : ℝ) := hmr
    _ ≤ _ := hmember

/-- The unrestricted finite-family compactness assertion, including eventual bounds. -/
def UnrestrictedCompactness : Prop :=
  ∀ (ι : Type) [Fintype ι] [Nonempty ι] (k : ι → ℕ)
    (F : (i : ι) → SimpleGraph (Fin (k i))),
    (∃ i, (F i).IsBipartite) →
    ∃ i, (F i).IsBipartite ∧ ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ,
      ∀ n : ℕ, N ≤ n → (extremalNumber n (F i) : ℝ) ≤ C * (familyExtremal F n : ℝ)

/-- The original unrestricted Erdős--Simonovits compactness statement is false. -/
theorem not_unrestrictedCompactness : ¬ UnrestrictedCompactness := by
  intro h
  obtain ⟨i, _, C, hC, N, hbound⟩ :=
    h Bool orders forbidden ⟨false, forbidden_bipartite false⟩
  obtain ⟨n, hn, hlt⟩ := no_member_bound i C hC N
  exact (not_lt_of_ge (hbound n hn)) hlt

#print axioms not_unrestrictedCompactness

end Erdos575
