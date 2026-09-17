import Contribution732.FinitePlane

/-!
# Arbitrary truncation profiles over any finite field

This formalization covers the full truncation-profile
construction in Noga Alon's Theorem 2.3, "Blocking partial designs and
block-compatible sequences", https://web.math.princeton.edu/~nalon/PDFS/remark191.pdf.

The geometric proof below explicitly generalizes and reuses the construction in
`Erdos732.exists_compatible_of_code`, upstream plby/lean-proofs commit
8822f7ddef30fadbd92e1c6ab4ed897af356af5e, src/latest/ErdosProblems/Erdos732.lean.
That source credits Noga Alon for the mathematics and Codex / GPT-5.6 Sol for
the formalization, with the Formal Conjectures Authors' Apache 2.0 notice.
Its completion-by-pairs lemmas are imported unchanged.

The strengthened interface accepts every multiset of the required cardinality
with all entries between 3 and q+1, and works over an arbitrary finite field.
It does not restrict multiplicities through a code `Fin (q - 2) → Fin q` or
assume that the field cardinality is prime. All lines are reindexed by a `Fin`
type before completion, allowing the finite field itself to live in any universe.
-/

open scoped BigOperators LinearAlgebra.Projectivization
open Finset Fintype

namespace Contribution732

open Erdos732

universe u

/-- Every length-`q²+q+1` truncation profile in `[3,q+1]` is realized over an
arbitrary finite field of cardinality `q`, with optional extra ground points.
Completing uncovered pairs adds only size-two blocks, so filtering recovers
the entire given profile, with all multiplicities unchanged. -/
theorem exists_compatible_of_profile (K : Type u) [Field K] [Fintype K]
    (n : ℕ) (hn : (Fintype.card K) ^ 2 + Fintype.card K + 1 ≤ n)
    (m : Multiset ℕ)
    (hmcard : m.card = (Fintype.card K) ^ 2 + Fintype.card K + 1)
    (hmbounds : ∀ a ∈ m, 3 ≤ a ∧ a ≤ Fintype.card K + 1) :
    ∃ sizes : Multiset ℕ, Erdos732.BlockCompatible n sizes ∧
      sizes.filter (fun a ↦ 3 ≤ a) = m := by
  classical
  let I := Fin ((Fintype.card K) ^ 2 + Fintype.card K + 1)
  have hlineCard : Fintype.card I = Fintype.card (PG K) := by
    simp [I, card_PG]
  let lines : I ≃ PG K := Fintype.equivOfCardEq hlineCard
  have hprofileCard : Fintype.card I = Fintype.card m := by
    rw [Multiset.card_coe, hmcard]
    simp [I]
  let e : I ≃ m := Fintype.equivOfCardEq hprofileCard
  let desired : I → ℕ := fun i ↦ (e i : ℕ)
  have hdesiredMem (i : I) : desired i ∈ m := by
    exact Multiset.coe_mem
  have hdesiredBounds (i : I) :
      3 ≤ desired i ∧ desired i ≤ Fintype.card K + 1 :=
    hmbounds (desired i) (hdesiredMem i)
  have hdesiredSizes : Finset.univ.val.map desired = m := by
    have he := congrArg (Multiset.map fun z : m ↦ (z : ℕ))
      (Multiset.map_univ_val_equiv e)
    rw [Multiset.map_map, Multiset.map_univ_coe] at he
    exact he
  have hchoose (i : I) :
      ∃ s : Finset (PG K), s ⊆ linePoints K (lines i) ∧ s.card = desired i := by
    obtain ⟨s, hs, hscard⟩ :=
      Finset.exists_subset_card_eq (s := linePoints K (lines i))
        (by simpa using (hdesiredBounds i).2)
    exact ⟨s, hs, hscard⟩
  let X : I → Finset (PG K) := fun i ↦ Classical.choose (hchoose i)
  have hXsub (i : I) : X i ⊆ linePoints K (lines i) :=
    (Classical.choose_spec (hchoose i)).1
  have hXcard (i : I) : (X i).card = desired i :=
    (Classical.choose_spec (hchoose i)).2
  let ι : PG K ↪ Fin n := Classical.choice
    (Function.Embedding.nonempty_of_card_le (by simpa [card_PG] using hn))
  let A : I → Finset (Fin n) := fun i ↦ (X i).map ι
  have hAcard (i : I) : (A i).card = desired i := by
    simp [A, hXcard]
  have hApartial : Erdos732.IsPartialDesign A := by
    intro x y hxy i j hxi hyi hxj hyj
    obtain ⟨px, hpxi, hpx⟩ := Finset.mem_map.mp hxi
    obtain ⟨py, hpyi, hpy⟩ := Finset.mem_map.mp hyi
    obtain ⟨px', hpxj, hpx'⟩ := Finset.mem_map.mp hxj
    obtain ⟨py', hpyj, hpy'⟩ := Finset.mem_map.mp hyj
    have hpxeq : px = px' := ι.injective (hpx.trans hpx'.symm)
    have hpyeq : py = py' := ι.injective (hpy.trans hpy'.symm)
    subst px'
    subst py'
    have hpxy : px ≠ py := by
      intro heq
      apply hxy
      rw [← hpx, ← hpy, heq]
    have hpxiLine : px ∈ lines i := (Finset.mem_filter.mp (hXsub i hpxi)).2
    have hpyiLine : py ∈ lines i := (Finset.mem_filter.mp (hXsub i hpyi)).2
    have hpxjLine : px ∈ lines j := (Finset.mem_filter.mp (hXsub j hpxj)).2
    have hpyjLine : py ∈ lines j := (Finset.mem_filter.mp (hXsub j hpyj)).2
    apply lines.injective
    exact (Configuration.Nondegenerate.eq_or_eq
      hpxiLine hpyiLine hpxjLine hpyjLine).resolve_left hpxy
  have hAsizes : Erdos732.familySizes A = m := by
    rw [Erdos732.familySizes]
    calc
      (Finset.univ.val.map fun i ↦ (A i).card) = Finset.univ.val.map desired := by
        apply Multiset.map_congr
        · rfl
        intro i hi
        exact hAcard i
      _ = m := hdesiredSizes
  have hAthree (i : I) : 3 ≤ (A i).card := by
    rw [hAcard]
    exact (hdesiredBounds i).1
  let D := Erdos732.completePartialDesign A hApartial
    (fun i ↦ (hAthree i).trans' (by omega))
  refine ⟨D.blockSizes, ⟨D, rfl⟩, ?_⟩
  rw [show D.blockSizes.filter (fun a ↦ 3 ≤ a) = Erdos732.familySizes A by
    exact Erdos732.filter_blockSizes_completePartialDesign A hApartial hAthree,
    hAsizes]

/-- Complete a primary profile by the exact deficit in its covered point pairs. -/
def completeProfile (n : ℕ) (m : Multiset ℕ) : Multiset ℕ :=
  m + Multiset.replicate
    (Nat.choose n 2 - (m.map fun k ↦ Nat.choose k 2).sum) 2

/-- In a compatible design all entries below three are two. Its primary profile
therefore determines the entire size multiset: pair counting fixes exactly how
many size-two blocks remain. The subtraction is justified by the pair-count
equality, rather than by an additional hypothesis on a proposed profile. -/
theorem determined_by_primary_profile {n : ℕ} {sizes m : Multiset ℕ}
    (hcompatible : Erdos732.BlockCompatible n sizes)
    (hprimary : sizes.filter (fun a ↦ 3 ≤ a) = m) :
    sizes = completeProfile n m := by
  classical
  let rest := sizes.filter (fun a ↦ ¬3 ≤ a)
  have hrest : rest = Multiset.replicate rest.card 2 := by
    apply Multiset.eq_replicate_card.mpr
    intro a ha
    have hmem : a ∈ sizes ∧ ¬3 ≤ a := Multiset.mem_filter.mp ha
    have hbounds := Erdos732.BlockCompatible.size_bounds hcompatible hmem.1
    omega
  have hsplit : m + rest = sizes := by
    simpa only [hprimary] using
      (Multiset.filter_add_not (p := fun a : ℕ ↦ 3 ≤ a) sizes)
  have hsplit' : sizes = m + Multiset.replicate rest.card 2 :=
    hsplit.symm.trans (congrArg (fun t : Multiset ℕ ↦ m + t) hrest)
  have hpairs : (m.map fun k ↦ Nat.choose k 2).sum + rest.card = Nat.choose n 2 := by
    have h := Erdos732.BlockCompatible.pair_count hcompatible
    rw [hsplit'] at h
    simpa using h
  have hcount : rest.card = Nat.choose n 2 - (m.map fun k ↦ Nat.choose k 2).sum := by
    omega
  calc
    sizes = m + Multiset.replicate rest.card 2 := hsplit'
    _ = completeProfile n m := by rw [hcount]; rfl

/-- Alon's full explicit completed profile is compatible for every finite field.
The only assumptions are the original ground-set size and primary-profile bounds. -/
theorem completeProfile_compatible (K : Type u) [Field K] [Fintype K]
    (n : ℕ) (hn : (Fintype.card K) ^ 2 + Fintype.card K + 1 ≤ n)
    (m : Multiset ℕ)
    (hmcard : m.card = (Fintype.card K) ^ 2 + Fintype.card K + 1)
    (hmbounds : ∀ a ∈ m, 3 ≤ a ∧ a ≤ Fintype.card K + 1) :
    Erdos732.BlockCompatible n (completeProfile n m) := by
  obtain ⟨sizes, hcompatible, hprimary⟩ :=
    exists_compatible_of_profile K n hn m hmcard hmbounds
  rw [← determined_by_primary_profile hcompatible hprimary]
  exact hcompatible

end Contribution732
