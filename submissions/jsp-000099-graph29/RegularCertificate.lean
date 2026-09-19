import Mathlib.Data.Finset.Card

/- A generic certificate checker. Mathematical graph data is supplied separately.
   No external program output is trusted by the soundness theorem. -/
namespace RegularCertificate

variable {V : Type} [DecidableEq V]

def degree (N : V → Finset V) (S : Finset V) (v : V) : Nat := (N v ∩ S).card

def RegularOn (N : V → Finset V) (S : Finset V) (d : Nat) : Prop :=
  ∀ v ∈ S, degree N S v = d

inductive Cert (V : Type) where
  | small : Cert V
  | bad (v : V) : Cert V
  | drop (v : V) (next : Cert V) : Cert V
  | fill (v : V) (next : Cert V) : Cert V
  | empty (v : V) (next : Cert V) : Cert V
  | split (v : V) (yes no : Cert V) : Cert V

def incompatible (N : V → Finset V) (d : Nat) (S U : Finset V) (v : V) : Bool :=
  decide (d < degree N S v ∨ degree N U v < d)

def check (N : V → Finset V) (k d : Nat) (S U : Finset V) : Cert V → Bool
  | .small => decide (U.card < k)
  | .bad v => decide (v ∈ S) && incompatible N d S U v
  | .drop v next => incompatible N d S U v && check N k d S (U.erase v) next
  | .fill v next => decide (v ∈ S ∧ degree N U v = d) &&
      check N k d (S ∪ (N v ∩ U)) U next
  | .empty v next => decide (v ∈ S ∧ degree N S v = d) &&
      check N k d S (U \ (N v \ S)) next
  | .split v yes no => check N k d (insert v S) U yes && check N k d S (U.erase v) no

theorem degree_mono (N : V → Finset V) {S T : Finset V} (h : S ⊆ T) (v : V) :
    degree N S v ≤ degree N T v := by
  apply Finset.card_le_card
  intro x hx
  simp only [Finset.mem_inter] at hx ⊢
  exact ⟨hx.1, h hx.2⟩

theorem incompatible_not_mem (N : V → Finset V) (d : Nat) (S U T : Finset V)
    (hST : S ⊆ T) (hTU : T ⊆ U) (hreg : RegularOn N T d) (v : V)
    (h : incompatible N d S U v = true) : v ∉ T := by
  intro hv
  have hlo := degree_mono N hST v
  have hhi := degree_mono N hTU v
  have heq := hreg v hv
  simp only [incompatible, decide_eq_true_eq] at h
  omega

theorem check_sound (N : V → Finset V) (k d : Nat) (c : Cert V) :
    ∀ S U, check N k d S U c = true →
    ∀ T, S ⊆ T → T ⊆ U → k ≤ T.card → ¬ RegularOn N T d := by
  induction c with
  | small =>
    intro S U hc T hST hTU hk hreg
    simp only [check, decide_eq_true_eq] at hc
    have := Finset.card_le_card hTU
    omega
  | bad v =>
    intro S U hc T hST hTU hk hreg
    simp only [check, Bool.and_eq_true, decide_eq_true_eq] at hc
    exact incompatible_not_mem N d S U T hST hTU hreg v hc.2 (hST hc.1)
  | drop v next ih =>
    intro S U hc T hST hTU hk hreg
    simp only [check, Bool.and_eq_true] at hc
    apply ih S (U.erase v) hc.2 T hST ?_ hk hreg
    intro x hx
    apply Finset.mem_erase.mpr
    refine ⟨?_, hTU hx⟩
    intro heq
    subst x
    exact incompatible_not_mem N d S U T hST hTU hreg v hc.1 hx
  | fill v next ih =>
    intro S U hc T hST hTU hk hreg
    simp only [check, Bool.and_eq_true, decide_eq_true_eq] at hc
    have hvT := hST hc.1.1
    have hsub : N v ∩ T ⊆ N v ∩ U := by
      intro x hx
      exact Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hx).1, hTU (Finset.mem_inter.mp hx).2⟩
    have heq : N v ∩ T = N v ∩ U := by
      apply Finset.eq_of_subset_of_card_le hsub
      change degree N U v ≤ degree N T v
      rw [hc.1.2, hreg v hvT]
    apply ih (S ∪ (N v ∩ U)) U hc.2 T ?_ hTU hk hreg
    intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · exact hST hx
    · rw [← heq] at hx
      exact (Finset.mem_inter.mp hx).2
  | empty v next ih =>
    intro S U hc T hST hTU hk hreg
    simp only [check, Bool.and_eq_true, decide_eq_true_eq] at hc
    have hvT := hST hc.1.1
    have hsub : N v ∩ S ⊆ N v ∩ T := by
      intro x hx
      exact Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hx).1, hST (Finset.mem_inter.mp hx).2⟩
    have heq : N v ∩ S = N v ∩ T := by
      apply Finset.eq_of_subset_of_card_le hsub
      change degree N T v ≤ degree N S v
      rw [hc.1.2, hreg v hvT]
    apply ih S (U \ (N v \ S)) hc.2 T hST ?_ hk hreg
    intro x hx
    apply Finset.mem_sdiff.mpr
    refine ⟨hTU hx, ?_⟩
    intro hbad
    have hnx := (Finset.mem_sdiff.mp hbad).1
    have hin : x ∈ N v ∩ T := Finset.mem_inter.mpr ⟨hnx, hx⟩
    rw [← heq] at hin
    exact (Finset.mem_sdiff.mp hbad).2 (Finset.mem_inter.mp hin).2
  | split v yes no ihy ihn =>
    intro S U hc T hST hTU hk hreg
    simp only [check, Bool.and_eq_true] at hc
    by_cases hv : v ∈ T
    · apply ihy (insert v S) U hc.1 T ?_ hTU hk hreg
      exact Finset.insert_subset_iff.mpr ⟨hv, hST⟩
    · apply ihn S (U.erase v) hc.2 T hST ?_ hk hreg
      intro x hx
      exact Finset.mem_erase.mpr ⟨by intro heq; subst x; exact hv hx, hTU hx⟩

#print axioms check_sound
end RegularCertificate
