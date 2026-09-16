import MaskCertificate
namespace Erdos82Finite
open RegularCertificate

/- Checkpoints store concrete masks to avoid repeated evaluation of long state expressions.
   Every checkpoint is checked for exact equality; its labels are not trusted. -/
inductive FastCert where
  | small : FastCert
  | bad (v : Fin 29) : FastCert
  | drop (v : Fin 29) (next : FastCert) : FastCert
  | fill (v : Fin 29) (next : FastCert) : FastCert
  | empty (v : Fin 29) (next : FastCert) : FastCert
  | split (v : Fin 29) (yes no : FastCert) : FastCert
  | checkpoint (selected possible : Nat) (next : FastCert) : FastCert

def FastCert.erase : FastCert → Cert (Fin 29)
  | .small => .small
  | .bad v => .bad v
  | .drop v next => .drop v next.erase
  | .fill v next => .fill v next.erase
  | .empty v next => .empty v next.erase
  | .split v yes no => .split v yes.erase no.erase
  | .checkpoint _ _ next => next.erase

def fcheck (k d S U : Nat) : FastCert → Bool
  | .small => decide (bitcount 29 0 U < k)
  | .bad v => S.testBit v.val && mincompatible d S U v
  | .drop v next => mincompatible d S U v && fcheck k d S (U &&& (full ^^^ (2^v.val))) next
  | .fill v next => (S.testBit v.val && decide (mdegree U v = d)) &&
      fcheck k d (S ||| (adjBits v &&& U)) U next
  | .empty v next => (S.testBit v.val && decide (mdegree S v = d)) &&
      fcheck k d S (U &&& (full ^^^ (adjBits v &&& (full ^^^ S)))) next
  | .split v yes no => fcheck k d (S ||| 2^v.val) U yes &&
      fcheck k d S (U &&& (full ^^^ (2^v.val))) no
  | .checkpoint selected possible next => (S == selected && U == possible) &&
      fcheck k d selected possible next

theorem fcheck_refines (k d : Nat) (c : FastCert) : ∀ S U,
    fcheck k d S U c = true → mcheck k d S U c.erase = true := by
  induction c with
  | small => intro S U h; exact h
  | bad v => intro S U h; exact h
  | drop v next ih =>
    intro S U h
    simp only [fcheck, Bool.and_eq_true] at h
    simp only [FastCert.erase, mcheck, Bool.and_eq_true]
    exact ⟨h.1, ih _ _ h.2⟩
  | fill v next ih =>
    intro S U h
    simp only [fcheck, Bool.and_eq_true] at h
    simp only [FastCert.erase, mcheck, Bool.and_eq_true]
    exact ⟨h.1, ih _ _ h.2⟩
  | empty v next ih =>
    intro S U h
    simp only [fcheck, Bool.and_eq_true] at h
    simp only [FastCert.erase, mcheck, Bool.and_eq_true]
    exact ⟨h.1, ih _ _ h.2⟩
  | split v yes no ihy ihn =>
    intro S U h
    simp only [fcheck, Bool.and_eq_true] at h
    simp only [FastCert.erase, mcheck, Bool.and_eq_true]
    exact ⟨ihy _ _ h.1, ihn _ _ h.2⟩
  | checkpoint selected possible next ih =>
    intro S U h
    simp only [fcheck, Bool.and_eq_true, beq_iff_eq] at h
    rcases h with ⟨⟨rfl, rfl⟩, h⟩
    exact ih _ _ h

theorem fcheck_sound (d : Nat) (c : FastCert) (h : fcheck 7 d 0 full c = true)
    (T : Finset (Fin 29)) (hT : 7 ≤ T.card) : ¬ RegularOn neighbors T d :=
  mcheck_sound d c.erase (fcheck_refines 7 d c 0 full h) T hT

#print axioms fcheck_sound
end Erdos82Finite
