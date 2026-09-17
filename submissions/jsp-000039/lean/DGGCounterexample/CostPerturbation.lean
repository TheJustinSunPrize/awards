import DGGCounterexample.Submission

namespace DGG

def minUnsplitCost (a b c : ℚ) : ℚ :=
  min (15 * a + 10 * b) (min (15 * a + 15 * c) (10 * b + 15 * c))

theorem minUnsplitCost_lower_bound {a b c : ℚ}
    (_ha : 0 ≤ a) (_hb : 0 ≤ b) (hc : 0 ≤ c)
    {r : Route} (hr : Feasible r) :
    minUnsplitCost a b c ≤ routeCost a b c r := by
  rw [feasible_routes] at hr
  rcases hr with hr | hr | hr | hr
  · rw [hr, routeEEZ_data.right]
    exact min_le_left _ _
  · rw [hr, routeEZE_data.right]
    exact le_trans (min_le_right _ _) (min_le_left _ _)
  · rw [hr, routeZEE_data.right]
    exact le_trans (min_le_right _ _) (min_le_right _ _)
  · rw [hr, routeEEE_data.right]
    have hfirst : 15 * a + 10 * b ≤ 15 * a + 10 * b + 15 * c := by linarith
    exact le_trans (min_le_left _ _) hfirst

theorem minUnsplitCost_attained (a b c : ℚ) :
    (∃ r : Route, Feasible r ∧ routeCost a b c r = minUnsplitCost a b c) := by
  unfold minUnsplitCost
  by_cases h1 : 15 * a + 10 * b ≤ min (15 * a + 15 * c) (10 * b + 15 * c)
  · refine ⟨routeEEZ, (routeEEZ_data (a := a) (b := b) (c := c)).left, ?_⟩
    rw [routeEEZ_data.right, min_eq_left h1]
  · have hlt1 : min (15 * a + 15 * c) (10 * b + 15 * c) < 15 * a + 10 * b := lt_of_not_ge h1
    by_cases h2 : 15 * a + 15 * c ≤ 10 * b + 15 * c
    · refine ⟨routeEZE, (routeEZE_data (a := a) (b := b) (c := c)).left, ?_⟩
      rw [routeEZE_data.right, min_eq_right (le_of_lt hlt1), min_eq_left h2]
    · refine ⟨routeZEE, (routeZEE_data (a := a) (b := b) (c := c)).left, ?_⟩
      have h2le : 10 * b + 15 * c ≤ 15 * a + 15 * c := le_of_lt (lt_of_not_ge h2)
      rw [routeZEE_data.right, min_eq_right (le_of_lt hlt1), min_eq_right h2le]

theorem feasible_prices_iff {a b c q : ℚ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    (∃ r : Route, Feasible r ∧ routeCost a b c r ≤ q) ↔
      minUnsplitCost a b c ≤ q := by
  constructor
  · rintro ⟨r, hr, hcost⟩
    exact le_trans (minUnsplitCost_lower_bound ha hb hc hr) hcost
  · intro hq
    rcases minUnsplitCost_attained a b c with ⟨r, hr, hcost⟩
    exact ⟨r, hr, by linarith⟩

theorem counterexample_iff (a b c : ℚ)
    (_ha : 0 ≤ a) (_hb : 0 ≤ b) (_hc : 0 ≤ c) :
    fractionalCost a b c < minUnsplitCost a b c ↔
      10 * c < 5 * a + 4 * b ∧
      6 * b < 5 * a + 5 * c ∧
      10 * a < 4 * b + 5 * c := by
  unfold fractionalCost minUnsplitCost
  constructor
  · intro h
    have hA : 10 * a + 6 * b + 10 * c < 15 * a + 10 * b :=
      lt_of_lt_of_le h (min_le_left _ _)
    have hB : 10 * a + 6 * b + 10 * c < 15 * a + 15 * c :=
      lt_of_lt_of_le (lt_of_lt_of_le h (min_le_right _ _)) (min_le_left _ _)
    have hC : 10 * a + 6 * b + 10 * c < 10 * b + 15 * c :=
      lt_of_lt_of_le (lt_of_lt_of_le h (min_le_right _ _)) (min_le_right _ _)
    constructor
    · linarith
    · constructor <;> linarith
  · rintro ⟨hA, hB, hC⟩
    apply lt_min
    · linarith
    · apply lt_min <;> linarith

theorem middle_price_iff (b : ℚ) (hb : 0 ≤ b) :
    fractionalCost 2 b 2 < minUnsplitCost 2 b 2 ↔
      (5 / 2 : ℚ) < b ∧ b < (10 / 3 : ℚ) := by
  constructor
  · intro h
    have h' := (counterexample_iff 2 b 2 (by norm_num) hb (by norm_num)).mp h
    constructor <;> linarith
  · intro h
    apply (counterexample_iff 2 b 2 (by norm_num) hb (by norm_num)).mpr
    constructor
    · linarith
    · constructor <;> linarith

theorem perturbed_fractional_cost :
    fractionalCost 2 (13 / 4) 2 = (119 / 2 : ℚ) := by
  norm_num [fractionalCost]

theorem perturbed_minimum :
    minUnsplitCost 2 (13 / 4) 2 = (60 : ℚ) := by
  norm_num [minUnsplitCost]

theorem perturbed_gap :
    minUnsplitCost 2 (13 / 4) 2 - fractionalCost 2 (13 / 4) 2 = (1 / 2 : ℚ) := by
  norm_num [minUnsplitCost, fractionalCost]

theorem perturbed_example :
    fractionalCost 2 (13 / 4) 2 < minUnsplitCost 2 (13 / 4) 2 := by
  have hb : (0 : ℚ) ≤ 13 / 4 := by norm_num
  rw [middle_price_iff (13 / 4) hb]
  norm_num

#print axioms perturbed_example
#print axioms counterexample_iff
#print axioms feasible_prices_iff

end DGG
