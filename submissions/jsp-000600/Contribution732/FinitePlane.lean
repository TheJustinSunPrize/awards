/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license.

Adapted from ErdosProblems/Erdos732.lean, lines 384–429, in
https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos732.lean
Informal author of the design construction: Noga Alon.
Upstream formal authors: Codex, GPT-5.6 Sol.
This adaptation replaces the prime field ZMod q with an arbitrary finite field.
-/

import ErdosProblems.Erdos732

/-!
# Finite-field projective planes for the full truncation-profile construction

The original source supplies the projective plane only over `ZMod q` with
`q.Prime`.  The same geometric lemmas hold over every finite field.  Keeping
the field as a parameter permits finite extensions and arbitrary prime-power
orders without imposing primality on the order itself.

-/

open scoped LinearAlgebra.Projectivization

namespace Contribution732

universe u

noncomputable section

/-- Points, and dually lines, in the projective plane over `K`. -/
abbrev PG (K : Type u) [Field K] := ℙ K (Fin 3 → K)

noncomputable instance pgFintype (K : Type u) [Field K] [Fintype K] :
    Fintype (PG K) := Fintype.ofFinite (PG K)

/-- Mathlib's field-plane instance requests decidable equality on the field.
Supply it classically so the public geometric statements need no extra
decidability or plane-existence hypothesis. -/
noncomputable instance pgProjectivePlane (K : Type u) [Field K] :
    Configuration.ProjectivePlane (PG K) (PG K) := by
  classical
  infer_instance

lemma card_PG (K : Type u) [Field K] [Fintype K] :
    Fintype.card (PG K) = Fintype.card K ^ 2 + Fintype.card K + 1 := by
  rw [← Nat.card_eq_fintype_card]
  rw [Projectivization.card_of_finrank (n := 3) K (Fin 3 → K) (by simp)]
  simp only [Nat.card_eq_fintype_card]
  norm_num [Finset.sum_range_succ, pow_two]
  ring

lemma projectivePlane_order_eq (K : Type u) [Field K] [Fintype K] :
    Configuration.ProjectivePlane.order (PG K) (PG K) = Fintype.card K := by
  let d := Configuration.ProjectivePlane.order (PG K) (PG K)
  have hcard := Configuration.ProjectivePlane.card_points (PG K) (PG K)
  rw [card_PG K] at hcard
  change Fintype.card K ^ 2 + Fintype.card K + 1 = d ^ 2 + d + 1 at hcard
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · nlinarith
  · nlinarith

/-- The points incident to a projective line, as a finset. -/
noncomputable def linePoints (K : Type u) [Field K] [Fintype K]
    (l : PG K) : Finset (PG K) := by
  classical
  exact Finset.univ.filter fun p ↦ p ∈ l

@[simp]
lemma mem_linePoints (K : Type u) [Field K] [Fintype K] (p l : PG K) :
    p ∈ linePoints K l ↔ p ∈ l := by
  classical
  simp [linePoints]

@[simp]
lemma card_linePoints (K : Type u) [Field K] [Fintype K] (l : PG K) :
    (linePoints K l).card = Fintype.card K + 1 := by
  classical
  calc
    (linePoints K l).card = Fintype.card {p : PG K // p ∈ l} := by
      rw [linePoints]
      symm
      apply Fintype.card_subtype
    _ = Configuration.pointCount (PG K) l := by
      rw [Configuration.pointCount, Nat.card_eq_fintype_card]
    _ = Configuration.ProjectivePlane.order (PG K) (PG K) + 1 :=
      Configuration.ProjectivePlane.pointCount_eq (PG K) l
    _ = Fintype.card K + 1 := by rw [projectivePlane_order_eq K]

end

end Contribution732
