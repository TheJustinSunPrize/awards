/- leanprover/lean4:v4.35.0-rc2  mathlib v4.35.0-rc2 -/
/-
JSP-000283 — Observation record: the greedy sequence obtained by repeatedly
adjoining the smallest positive integer that is not expressible as a sum of
two (not necessarily distinct) existing terms, started from the single
existing term 1, is exactly the sequence of odd positive integers
1, 3, 5, 7, ….

Catalog question (TheJustinSunPrize/awards, problems/catalog-0201-0300.md,
#JSP-000283):
  "Does the sequence obtained by repeatedly adjoining the smallest integer
   not expressible as a sum of two existing terms eventually become
   periodic?"

Reading fixed here
------------------
* the initial set of existing terms is `{1}`;
* "a sum of two existing terms" allows the same term to be used twice
  (so `2 = 1 + 1` is expressible);
* the candidates among which the smallest one is chosen are the positive
  integers (over all of ℤ there is no smallest non-expressible integer, so
  this is the only reading under which the greedy procedure is well defined).

Under this reading the catalogue question has a definitive structural
answer: the greedy sequence is `g n = 2*n + 1` for every `n`, i.e. the
differences `g (n+1) - g n` are constantly `2` from the very first step.
(If one insists on literal periodicity of the terms, `a (n+p) = a n`, then
no strictly increasing sequence is ever periodic; the exact closed form
proved below is the precise content recorded here.)

Scope of this file
------------------
This file records a complete, machine-checked Lean proof of the
characterization above.  It does NOT address other readings of the question
(e.g. requiring the two summands to be distinct, or a different starting
set), does not change the catalogue entry of JSP-000283 (which remains
Open), and makes no award claim.

Method
------
The sequence is defined by structural recursion: `known n` is the finite set
`{g 0, …, g n}` of terms already adjoined (built in tandem with `g`), and
`g (n+1) = cand (known n)` where `cand S` is the least positive integer
that is neither in `S` nor a sum of two (not necessarily distinct) elements
of `S`, obtained from `Nat.find` (a classical decidability instance is used;
this introduces only the standard `Classical.choice` axiom).  The key lemma
is `cand {1, 3, …, 2n+1} = 2n+3`: every `m ≤ 2n+2` is excluded (odd `m` is
already in the set; an even `m = 2j` is `1 + (2j-1)`, both summands being in
the set — this uses `2 = 1 + 1` for `j = 1`), while `2n+3` is odd and a sum
of two odd numbers is even, so `2n+3` is free.  No `sorry`, `admit`,
`native_decide`, or added unproved assumptions are used.

Mathematical area: Number theory.
Problem posed: no later than 1980 (bibliographic evidence).

Formalization author: Yaohua-Leo (AI-assisted via ZCode (GLM)).
-/

import Mathlib

/-- `m` is *free* for a finite set `S` of existing terms when `m` is a
positive integer, is not itself in `S`, and is not the sum of two (not
necessarily distinct) elements of `S`. -/
def IsFree (S : Finset ℕ) (m : ℕ) : Prop :=
  0 < m ∧ m ∉ S ∧ ∀ a ∈ S, ∀ b ∈ S, a + b ≠ m

/-- Classical decidability of `IsFree` (allowed; introduces only the standard
`Classical.choice` axiom). -/
noncomputable instance instDecidableIsFree (S : Finset ℕ) (m : ℕ) :
    Decidable (IsFree S m) :=
  Classical.propDecidable _

/-- Membership in the set of the first `n+1` odd positive integers
`{2*k+1 : k < n+1}`, phrased in an `omega`-friendly way. -/
theorem mem_oddSet {n m : ℕ} :
    m ∈ (Finset.range (n + 1)).image (fun k => 2 * k + 1) ↔ m % 2 = 1 ∧ m ≤ 2 * n + 1 := by
  constructor
  · intro h
    obtain ⟨k, hk, hkm⟩ := Finset.mem_image.mp h
    simp only [Finset.mem_range] at hk
    subst hkm
    omega
  · intro h
    exact Finset.mem_image.mpr ⟨(m - 1) / 2, Finset.mem_range.mpr (by omega), by omega⟩

/-- Every finite set of existing terms admits a free integer: take a number
strictly larger than every element and hence than every possible sum. -/
theorem exists_isFree (S : Finset ℕ) : ∃ m, IsFree S m := by
  refine ⟨2 * S.sup id + 3, ⟨by omega, ?_, ?_⟩⟩
  · intro hmem
    have hle : 2 * S.sup id + 3 ≤ S.sup id := Finset.le_sup (f := id) hmem
    omega
  · intro a ha b hb habs
    have hal : a ≤ S.sup id := Finset.le_sup (f := id) ha
    have hbl : b ≤ S.sup id := Finset.le_sup (f := id) hb
    omega

/-- The greedy step: the smallest free integer for `S`, existing because
`S` is finite (`exists_isFree`). -/
noncomputable def cand (S : Finset ℕ) : ℕ :=
  Nat.find (exists_isFree S)

/-- `known n` is the set `{g 0, …, g n}` of the first `n+1` greedy terms,
built in tandem with `g` below. -/
noncomputable def known : ℕ → Finset ℕ
  | 0 => {1}
  | n + 1 => insert (cand (known n)) (known n)

theorem known_zero : known 0 = {1} := rfl

theorem known_succ (n : ℕ) :
    known (n + 1) = insert (cand (known n)) (known n) := rfl

/-- The greedy sequence: `g 0 = 1`; `g (n+1)` is the smallest positive
integer that is neither among `g 0, …, g n` nor a sum of two (not
necessarily distinct) of them. -/
noncomputable def g : ℕ → ℕ
  | 0 => 1
  | n + 1 => cand (known n)

theorem g_zero : g 0 = 1 := rfl

theorem g_succ (n : ℕ) : g (n + 1) = cand (known n) := rfl

/-- Auxiliary form of the (renamed) `Finset.range_succ` fact. -/
theorem range_succ' (n : ℕ) :
    Finset.range (n + 2) = insert (n + 1) (Finset.range (n + 1)) := by
  ext m
  simp only [Finset.mem_range, Finset.mem_insert]
  omega

/-- **Key lemma**: for the set of the first `n+1` odd numbers, the greedy
choice is the next odd number `2n+3`. -/
theorem cand_odd_image (n : ℕ) :
    cand ((Finset.range (n + 1)).image (fun k => 2 * k + 1)) = 2 * n + 3 := by
  rw [cand, Nat.find_eq_iff]
  constructor
  · -- `2n+3` is free: it is positive, odd and larger than every element of
    -- the set, and a sum of two odd numbers is even.
    refine ⟨by omega, ?_, ?_⟩
    · intro hmem
      have hle := (mem_oddSet.mp hmem).2
      omega
    · intro a ha b hb habs
      have ha' := (mem_oddSet.mp ha).1
      have hb' := (mem_oddSet.mp hb).1
      omega
  · -- every smaller positive integer is excluded
    intro k hk hfree
    by_cases hk1 : k % 2 = 1
    · -- odd `k`: already an element of the set
      exact hfree.2.1 (mem_oddSet.mpr ⟨hk1, by omega⟩)
    · -- even `k = 2j ≥ 2`: `k = 1 + (2j - 1)`, both summands in the set
      -- (this uses that the two summands may coincide, for `k = 2 = 1 + 1`)
      have h2 : k % 2 < 2 := Nat.mod_lt _ (by omega)
      have hk0 : k % 2 = 0 := by omega
      have hpos : 0 < k := hfree.1
      exact hfree.2.2 1 (mem_oddSet.mpr ⟨by omega, by omega⟩)
        (2 * ((k - 1) / 2) + 1) (mem_oddSet.mpr ⟨by omega, by omega⟩) (by omega)

/-- The set of the first `n+1` greedy terms is exactly the set of the first
`n+1` odd positive integers. -/
theorem known_eq (n : ℕ) :
    known n = (Finset.range (n + 1)).image (fun k => 2 * k + 1) := by
  induction n with
  | zero => simp [known_zero, Finset.range_one, Finset.image_singleton]
  | succ n ih =>
    rw [known_succ, ih, cand_odd_image, range_succ', Finset.image_insert,
      show 2 * (n + 1) + 1 = 2 * n + 3 from by omega]

/-- **JSP-000283 (main result, stated reading):** the greedy sequence is
exactly the odd numbers: `g n = 2*n + 1` for every `n`. -/
theorem jsp000283 (n : ℕ) : g n = 2 * n + 1 := by
  cases n with
  | zero => exact g_zero
  | succ n =>
    rw [g_succ, known_eq, cand_odd_image]
    omega

/-- The gap sequence is constantly `2` from the very first step: the
structural answer to the catalogue question under the stated reading. -/
theorem jsp000283_gaps (n : ℕ) : g (n + 1) = g n + 2 := by
  rw [g_succ, known_eq, cand_odd_image, jsp000283 n]

/-- The sequence is strictly increasing (so, under the literal reading
"eventually periodic = some tail satisfies `a (n+p) = a n`", it is not
literally periodic; the exact closed form `jsp000283` is the content
recorded). -/
theorem jsp000283_strict_mono : StrictMono g := by
  intro a b hab
  rw [jsp000283 a, jsp000283 b]
  omega

#print axioms exists_isFree
#print axioms cand_odd_image
#print axioms known_eq
#print axioms jsp000283
#print axioms jsp000283_gaps
#print axioms jsp000283_strict_mono
