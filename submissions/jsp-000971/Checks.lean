import Counting

open JSP000971

-- The start time is included, even at n = 0.
example : historical (fun _ : ℕ => (0 : ℕ)) 0 = {0} := by decide

-- Repeated visits to one site never create another historical favorite.
example : (historical (fun _ : ℕ => (0 : ℕ)) 8).card = 1 := by decide

-- Every new site ties for first when there are no repeated visits.
example : (historical (fun k : ℕ => k) 5).card = 6 := by decide
example : maximum (fun k : ℕ => k) 5 = 1 := by decide

-- Ties must include both sites; a single-winner definition would fail.
example : favorites (fun k : ℕ => k % 2) 3 = {0, 1} := by decide

-- All parameters remain universally quantified; the planar case is an instance.
example (s : ℕ → ℤ × ℤ) (N n K : ℕ)
    (hK : ∀ k, N ≤ k → k ≤ n → (favorites s k).card ≤ K) :
    (historical s n).card ≤ N + K * maximum s n :=
  historical_card_le s N n K hK

-- Eventually at most three simultaneous favorites gives the desired pathwise bound.
theorem eventually_three_counting (s : ℕ → ℤ × ℤ)
    (h : ∃ N, ∀ k, N ≤ k → (favorites s k).card ≤ 3) :
    ∃ N, ∀ n, N ≤ n → (historical s n).card ≤ N + 3 * maximum s n := by
  obtain ⟨N, hN⟩ := h
  exact ⟨N, fun n _ => historical_card_le s N n 3 (fun k hk _ => hN k hk)⟩

#print axioms JSP000971.mem_favorites_iff
#print axioms eventually_three_counting
