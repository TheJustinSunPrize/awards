/- leanprover/lean4:v4.35.0-rc2  mathlib v4.35.0-rc2 -/

import Mathlib

/-!
# JSP-000370 observation: the least `n` with `k ∣ φ(n)` jumps from `k + 1` to `4k + 1`

The Justin Sun Prize problem
[JSP-000370](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0301-0400.md#JSP-000370)
asks: *How large can the smallest integer whose totient is divisible by a
prescribed positive integer be?*  That is, for a fixed positive integer `k`, let
`f(k)` denote the least positive integer `n` such that `k ∣ φ(n)`; how large can
`f(k)` be relative to `k`?

This file records a complete, machine-checked Lean proof of two explicit
instances witnessing that the ratio `f(k) / k` is not a constant close to `1`:

* `k = 6`:  `f(6) = 7 = 6 + 1`.  Concretely, `6 ∣ φ(7)`, and no `1 ≤ m ≤ 6`
  satisfies `6 ∣ φ(m)` (the totients `φ(1), …, φ(6) = 1, 1, 2, 2, 4, 2` are
  never divisible by `6`).
* `k = 13`: `f(13) = 53 = 4 · 13 + 1`.  Concretely, `13 ∣ φ(53)`, and no
  `1 ≤ m ≤ 52` satisfies `13 ∣ φ(m)`.

So the minimum is exactly `k + 1` for `k = 6` but exactly `4k + 1` for `k = 13`.

**Scope.**  Only the two explicit instances `k = 6` and `k = 13` are verified
(in each case: the witness `n` works and every smaller positive `m` fails).
How large `f(k)` can be for a general prescribed `k` — the actual catalog
question — is *not* addressed, the catalogued problem is not resolved, and no
award claim is made.
-/

/-- No positive `m ≤ 6` has totient divisible by `6`
(the values `φ(1), …, φ(6)` are `1, 1, 2, 2, 4, 2`). -/
theorem no_totient_div_six_upto_six :
    ∀ m ∈ Finset.Icc 1 6, ¬ 6 ∣ Nat.totient m := by
  decide

/-- No positive `m ≤ 52` has totient divisible by `13`. -/
theorem no_totient_div_thirteen_upto_fifty_two :
    ∀ m ∈ Finset.Icc 1 52, ¬ 13 ∣ Nat.totient m := by
  decide

/-- The witness totient for `k = 6`: `φ(7) = 6`. -/
theorem totient_seven_eq_six : Nat.totient 7 = 6 := by
  decide

/-- The witness totient for `k = 13`: `φ(53) = 52 = 4 · 13`. -/
theorem totient_fifty_three_eq_fifty_two : Nat.totient 53 = 52 := by
  decide

/-- The least positive integer whose totient is divisible by `6` is exactly
`7 = 6 + 1`: nothing in `[1, 6]` works, and `7` does. -/
theorem least_with_totient_div_by_six :
    (∀ m, 0 < m → m ≤ 6 → ¬ 6 ∣ Nat.totient m) ∧ 6 ∣ Nat.totient 7 :=
  ⟨fun m hm₀ hm₆ =>
    no_totient_div_six_upto_six m (Finset.mem_Icc.mpr ⟨hm₀, hm₆⟩),
    by decide⟩

/-- The least positive integer whose totient is divisible by `13` is exactly
`53 = 4 · 13 + 1`: nothing in `[1, 52]` works, and `53` does. -/
theorem least_with_totient_div_by_thirteen :
    (∀ m, 0 < m → m ≤ 52 → ¬ 13 ∣ Nat.totient m) ∧ 13 ∣ Nat.totient 53 :=
  ⟨fun m hm₀ hm₅₂ =>
    no_totient_div_thirteen_upto_fifty_two m (Finset.mem_Icc.mpr ⟨hm₀, hm₅₂⟩),
    by decide⟩

/-- **JSP-000370 observation, small instance.**  For `k = 6` the least positive
integer whose totient is divisible by `k` is `k + 1 = 7`: `6 ∣ φ(7)` while no
positive `m ≤ 6` satisfies `6 ∣ φ(m)`. -/
theorem jsp000370_small :
    ∃ k : ℕ, 0 < k ∧ k ∣ Nat.totient (k + 1) ∧
      ∀ m, 0 < m → m ≤ k → ¬ k ∣ Nat.totient m := by
  refine ⟨6, by decide, ?_, ?_⟩
  · decide
  · intro m hm₀ hm₆
    exact no_totient_div_six_upto_six m (Finset.mem_Icc.mpr ⟨hm₀, hm₆⟩)

/-- **JSP-000370 observation, large instance.**  For `k = 13` the least positive
integer whose totient is divisible by `k` is `4k + 1 = 53`: `13 ∣ φ(53)` while
no positive `m ≤ 4 · 13 = 52` satisfies `13 ∣ φ(m)`.  Together with
`jsp000370_small` this shows the ratio `f(k) / k` of the least such integer to
`k` is not a fixed constant: it equals `7 / 6` for `k = 6` but `53 / 13 > 4`
for `k = 13`. -/
theorem jsp000370_large :
    ∃ k : ℕ, 0 < k ∧ k ∣ Nat.totient (4 * k + 1) ∧
      ∀ m, 0 < m → m ≤ 4 * k → ¬ k ∣ Nat.totient m := by
  refine ⟨13, by decide, ?_, ?_⟩
  · decide
  · intro m hm₀ hm₅₂
    exact no_totient_div_thirteen_upto_fifty_two m
      (Finset.mem_Icc.mpr ⟨hm₀, hm₅₂⟩)

-- Axiom audit: the two `no_totient_div_*` and the totient-value theorems are
-- proved by `decide` (axiom-free); the main theorems are assembled purely from
-- those and order/dvd lemmas.
#print axioms no_totient_div_six_upto_six
#print axioms no_totient_div_thirteen_upto_fifty_two
#print axioms totient_seven_eq_six
#print axioms totient_fifty_three_eq_fifty_two
#print axioms least_with_totient_div_by_six
#print axioms least_with_totient_div_by_thirteen
#print axioms jsp000370_small
#print axioms jsp000370_large
