/-
Erdős 1063 / JSP-000883: original target definitions, with companion proof-source modules.
The revised project has NOT been compiled in the packaging environment.

The minimum and Big-O/Little-o target follow the Formal Conjectures Authors'
ErdosProblems/1063.lean (2026), Git blob bda13fc03989bb240293a164c7d70c75dfcc86f9.
The natural-number lcm is cast to Real only AFTER it is computed.
Released under Apache-2.0; see ../LICENSE and ../docs/SOURCES.md.
Prepared with ChatGPT assistance. No priority claim.
-/
import Mathlib

open Filter Asymptotics

namespace JSP000883

/-- A genuine block with exactly one nondivisor of the actual binomial coefficient. -/
def Admissible (k n : ℕ) : Prop :=
  2 * k ≤ n ∧ ∃ i0 < k, ¬ (n - i0) ∣ n.choose k ∧
    ∀ i < k, i ≠ i0 → (n - i) ∣ n.choose k

/-- Natural infimum, following the original target. Nonemptiness must be proved. -/
noncomputable def leastN (k : ℕ) : ℕ :=
  sInf {n : ℕ | Admissible k n}

/-- This least common multiple is computed in ℕ, never in ℝ. -/
def lcmInitial (k : ℕ) : ℕ :=
  (Finset.Icc 1 (k - 1)).lcm id

def center (k p : ℕ) : ℕ := k * (lcmInitial k / p)

def chooseLeft (k p : ℕ) : Prop := center k p % p ≤ k - p - 1

def candidateN (k p : ℕ) : ℕ :=
  if center k p % p ≤ k - p - 1 then center k p else center k p + k - 1

def candidateOffset (k p : ℕ) : ℕ :=
  if center k p % p ≤ k - p - 1 then 0 else k - 1

/-- Original target: the fully quantified finite construction, not sampled instances. -/
def FiniteConstructionClaim : Prop :=
  ∀ k p : ℕ, 9 ≤ k → p.Prime → k < 2 * p → 3 * p + 2 ≤ 2 * k →
    let n := candidateN k p
    let i0 := candidateOffset k p
    2 * k ≤ n ∧ i0 < k ∧ n - i0 = center k p ∧
      ¬ (center k p) ∣ n.choose k ∧
      (∀ i < k, i ≠ i0 → (n - i) ∣ n.choose k) ∧
      n ≤ 3 * lcmInitial k

/-- Original target: prime-distribution input needed for the eventual theorem. -/
def EventualPrimeIntervalClaim : Prop :=
  ∃ K : ℕ, 9 ≤ K ∧ ∀ k : ℕ, K ≤ k →
    ∃ p : ℕ, p.Prime ∧ k < 2 * p ∧ 3 * p + 2 ≤ 2 * k

/-- Original target: explicit nonemptiness rules out the empty-infimum shortcut. -/
def EventualUpperClaim : Prop :=
  ∃ K : ℕ, ∀ k : ℕ, K ≤ k →
    (∃ n : ℕ, Admissible k n) ∧ leastN k ≤ 3 * lcmInitial k

/-- UNPROVED endpoint corresponding to `erdos_1063.better_upper`, with U=L. -/
def BetterUpperClaim : Prop :=
  ((fun k : ℕ => (leastN k : ℝ)) =O[atTop] fun k : ℕ => (lcmInitial k : ℝ)) ∧
    ((fun k : ℕ => (lcmInitial k : ℝ)) =o[atTop]
      fun k : ℕ => (k : ℝ) * (lcmInitial k : ℝ))

-- Companion theorem bodies are in FiniteConstruction, PrimeInterval, and Asymptotics.
-- Their existence in source is not a claim of successful compiler verification.

end JSP000883
