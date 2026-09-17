/-
Copyright 2026 James-16. Released under the Apache License, Version 2.0.
Developed with substantial OpenAI Codex assistance.
This formalizes known mathematics: the ten consecutive primes in arithmetic progression
published by H. Dubner, T. Forbes, N. Lygeros, M. Mizony, H. Nelson, and P. Zimmermann,
Mathematics of Computation 71 (2002), 1323–1328. Manfred Toplic found the progression in 1998.
No resolution of the unbounded Erdős 141 problem or the eleven-term case is claimed.
-/
import Erdos141FirstCases.Primes
import Erdos141FirstCases.Blocks
import Erdos141FirstCases.Bridge

namespace Erdos141FirstCases

theorem prime_term (i : ℕ) (hi : i < 10) : Nat.Prime (start + i * 210) := by
  have hc : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first | exact prime_100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229719 | exact prime_100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229929 | exact prime_100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230139 | exact prime_100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230349 | exact prime_100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230559 | exact prime_100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230769 | exact prime_100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230979 | exact prime_100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231189 | exact prime_100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231399 | exact prime_100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231609

end Erdos141FirstCases

namespace Erdos141

open Erdos141FirstCases Erdos141

/-- The exact Formal Conjectures target for all known lengths from three through ten. -/
theorem erdos_141.variants.first_cases :
    (∀ k ≥ 3, k ≤ 10 → ∃ (s : Set ℕ), s.IsAPAndPrimeProgressionOfLength k) := by
  intro k hk hten
  apply progression_from_certificates start 210 k (by decide) (by omega)
  · intro i hi
    exact prime_term i (by omega)
  · intro i hi x hlo hhi
    have hx : start ≤ x := by omega
    have hr : x - start < 1891 := by omega
    have hmod : (x - start) % 210 ≠ 0 := by omega
    have hc := composite_between (x - start) hr hmod
    simpa only [Nat.add_sub_of_le hx] using hc

end Erdos141
