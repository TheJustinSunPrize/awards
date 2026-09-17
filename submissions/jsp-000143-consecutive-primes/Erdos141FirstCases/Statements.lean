/-
Copyright 2025 The Formal Conjectures Authors.
Licensed under the Apache License, Version 2.0.
Definitions copied from Formal Conjectures revision
40e7c98697de6f66b8cbdbf641749ab39ed9c152, Erdős 141 and Combinatorics/AP/Basic.
-/
import Mathlib.Algebra.Module.NatInt
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Set.Card
import Mathlib.Data.Nat.Prime.Nth

variable {α : Type*} [AddCommMonoid α]

def Set.IsAPOfLengthWith (s : Set α) (l : ℕ∞) (a d : α) : Prop :=
  ENat.card s = l ∧ s = {a + n • d | (n : ℕ) (_ : n < l)}

def Set.IsAPOfLength (s : Set α) (l : ℕ∞) : Prop :=
  ∃ a d : α, s.IsAPOfLengthWith l a d

namespace Erdos141

def Set.IsPrimeProgressionOfLength (s : Set ℕ) (l : ℕ∞) : Prop :=
  ∃ a, ENat.card s = l ∧ s = {(a + n).nth Nat.Prime | (n : ℕ) (_ : n < l)}

open Nat Erdos141

def Set.IsAPAndPrimeProgressionOfLength (s : Set ℕ) (l : ℕ) :=
  s.IsAPOfLength l ∧ s.IsPrimeProgressionOfLength l

end Erdos141
