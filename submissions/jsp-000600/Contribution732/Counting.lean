/-
Copyright (c) 2026. Released under the Apache License, Version 2.0.

New formalization of the unrestricted profile count in Noga Alon's
"Blocking partial designs and block-compatible sequences", Theorem 2.3.
The underlying projective-plane truncation construction extends the attributed
plby/lean-proofs Erdos732 formalization; no new mathematical discovery is claimed.
-/
import Contribution732.Profiles

open scoped BigOperators
open Finset Fintype

namespace Contribution732

/-- All multisets of `q^2+q+1` allowable primary sizes, with multiplicities
unrestricted. Unlike the original bounded frequency code, this includes every
profile with entries between `3` and `q+1`. -/
abbrev ProfileCode (q : ℕ) := Sym (Fin (q - 1)) (q ^ 2 + q + 1)

def profileSizes (q : ℕ) (c : ProfileCode q) : Multiset ℕ :=
  (c : Multiset (Fin (q - 1))).map (fun i ↦ i.val + 3)

lemma profileSizes_card (q : ℕ) (c : ProfileCode q) :
    (profileSizes q c).card = q ^ 2 + q + 1 := by
  simp [profileSizes]

lemma profileSizes_bounds (q : ℕ) (hq : 2 ≤ q) (c : ProfileCode q)
    {a : ℕ} (ha : a ∈ profileSizes q c) : 3 ≤ a ∧ a ≤ q + 1 := by
  obtain ⟨i, _, rfl⟩ := Multiset.mem_map.mp ha
  have := i.isLt
  omega

lemma profileSizes_injective (q : ℕ) : Function.Injective (profileSizes q) := by
  intro c d h
  apply Sym.coe_injective
  apply Multiset.map_injective (f := fun i : Fin (q - 1) ↦ i.val + 3) ?_ h
  intro i j hij
  change i.val + 3 = j.val + 3 at hij
  exact Fin.ext (Nat.add_right_cancel hij)

/-- Stars and bars counts all profiles, without an artificial bound on the
number of occurrences of an individual size. -/
theorem card_profileCode (q : ℕ) (hq : 2 ≤ q) :
    Fintype.card (ProfileCode q) =
      Nat.choose (q ^ 2 + q + 1 + q - 2) (q - 2) := by
  change Fintype.card (Sym (Fin (q - 1)) (q ^ 2 + q + 1)) = _
  rw [Sym.card_sym_eq_choose, Fintype.card_fin]
  have htop : q - 1 + (q ^ 2 + q + 1) - 1 = q ^ 2 + q + 1 + q - 2 := by
    omega
  rw [htop]
  apply Nat.choose_symm_of_eq_add
  omega

/-- Alon's exact finite family, now using every allowed profile over any
finite field. The ground set may be enlarged beyond the projective plane. -/
theorem complete_profile_family (K : Type*) [Field K] [Fintype K]
    (n : ℕ) (hn : (Fintype.card K) ^ 2 + Fintype.card K + 1 ≤ n) :
    ∃ S : Finset (Multiset ℕ),
      S.card = Nat.choose
        ((Fintype.card K) ^ 2 + Fintype.card K + 1 + Fintype.card K - 2)
        (Fintype.card K - 2) ∧
      ∀ sizes ∈ S, Erdos732.BlockCompatible n sizes := by
  classical
  let q := Fintype.card K
  have hq : 2 ≤ q := Fintype.one_lt_card
  have hex (c : ProfileCode q) := exists_compatible_of_profile K n hn
    (profileSizes q c) (profileSizes_card q c)
    (fun a ha ↦ profileSizes_bounds q hq c ha)
  let sizes : ProfileCode q → Multiset ℕ := fun c ↦ Classical.choose (hex c)
  have hcompatible (c : ProfileCode q) : Erdos732.BlockCompatible n (sizes c) :=
    (Classical.choose_spec (hex c)).1
  have hfilter (c : ProfileCode q) :
      (sizes c).filter (fun a ↦ 3 ≤ a) = profileSizes q c :=
    (Classical.choose_spec (hex c)).2
  have hinj : Function.Injective sizes := by
    intro c d hcd
    apply profileSizes_injective q
    rw [← hfilter c, ← hfilter d, hcd]
  let e : ProfileCode q ↪ Multiset ℕ := ⟨sizes, hinj⟩
  refine ⟨Finset.univ.map e, ?_, ?_⟩
  · rw [Finset.card_map, Finset.card_univ, card_profileCode q hq]
  · intro s hs
    obtain ⟨c, _, rfl⟩ := Finset.mem_map.mp hs
    exact hcompatible c

end Contribution732
