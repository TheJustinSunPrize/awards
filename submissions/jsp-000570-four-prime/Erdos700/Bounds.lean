import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

/-! Universal polynomial inequalities for the four-prime criterion.
Generated using nonnegative substitutions; each identity and sign is checked
by Lean. These statements concern all parameters in the stated range. -/

namespace Erdos700.FourPrime.Bounds
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

theorem c_at_least_10 (a b c : ℤ)
    (ha : 1 ≤ a) (hb : 3*a ≤ b) (hc : b*(b-a)+b+1 ≤ c) :
    0 < c - 9 := by
  let x := a-1
  let y := b-3*a
  let z := c-(b*(b-a)+b+1)
  have hx : 0 ≤ x := by dsimp [x]; linarith
  have hy : 0 ≤ y := by dsimp [y]; linarith
  have hz : 0 ≤ z := by dsimp [z]; linarith
  have hid : c - 9 = 6 * x ^ 2 + 5 * x * y + 15 * x + y ^ 2 + 6 * y + z + 1 := by
    dsimp [x, y, z]
    ring
  rw [hid]
  positivity

theorem T1_positive (a b c : ℤ)
    (ha : 1 ≤ a) (hb : 3*a ≤ b) (hc : b*(b-a)+b+1 ≤ c) :
    0 < 3 * a ^ 2 - 2 * a * (b + c) + b * c := by
  let x := a-1
  let y := b-3*a
  let z := c-(b*(b-a)+b+1)
  have hx : 0 ≤ x := by dsimp [x]; linarith
  have hy : 0 ≤ y := by dsimp [y]; linarith
  have hz : 0 ≤ z := by dsimp [z]; linarith
  have hid : 3 * a ^ 2 - 2 * a * (b + c) + b * c = 6 * x ^ 3 + 11 * x ^ 2 * y + 18 * x ^ 2 + 6 * x * y ^ 2 + 24 * x * y + x * z + 19 * x + y ^ 3 + 7 * y ^ 2 + y * z + 14 * y + z + 7 := by
    dsimp [x, y, z]
    ring
  rw [hid]
  positivity

theorem T1_less_than_bc (a b c : ℤ)
    (ha : 1 ≤ a) (hb : 3*a ≤ b) (hc : b*(b-a)+b+1 ≤ c) :
    0 < -3 * a ^ 2 + 2 * a * (b + c) := by
  let x := a-1
  let y := b-3*a
  let z := c-(b*(b-a)+b+1)
  have hx : 0 ≤ x := by dsimp [x]; linarith
  have hy : 0 ≤ y := by dsimp [y]; linarith
  have hz : 0 ≤ z := by dsimp [z]; linarith
  have hid : -3 * a ^ 2 + 2 * a * (b + c) = 12 * x ^ 3 + 10 * x ^ 2 * y + 45 * x ^ 2 + 2 * x * y ^ 2 + 24 * x * y + 2 * x * z + 56 * x + 2 * y ^ 2 + 14 * y + 2 * z + 23 := by
    dsimp [x, y, z]
    ring
  rw [hid]
  positivity

theorem S1_positive (a b c : ℤ)
    (ha : 1 ≤ a) (hb : 3*a ≤ b) (hc : b*(b-a)+b+1 ≤ c) :
    0 < -3 * a + b + c := by
  let x := a-1
  let y := b-3*a
  let z := c-(b*(b-a)+b+1)
  have hx : 0 ≤ x := by dsimp [x]; linarith
  have hy : 0 ≤ y := by dsimp [y]; linarith
  have hz : 0 ≤ z := by dsimp [z]; linarith
  have hid : -3 * a + b + c = 6 * x ^ 2 + 5 * x * y + 15 * x + y ^ 2 + 7 * y + z + 10 := by
    dsimp [x, y, z]
    ring
  rw [hid]
  positivity

theorem R_greater_than_one (a b c : ℤ)
    (ha : 1 ≤ a) (hb : 3*a ≤ b) (hc : b*(b-a)+b+1 ≤ c) :
    0 < a - 3 * b + c - 1 := by
  let x := a-1
  let y := b-3*a
  let z := c-(b*(b-a)+b+1)
  have hx : 0 ≤ x := by dsimp [x]; linarith
  have hy : 0 ≤ y := by dsimp [y]; linarith
  have hz : 0 ≤ z := by dsimp [z]; linarith
  have hid : a - 3 * b + c - 1 = 6 * x ^ 2 + 5 * x * y + 7 * x + y ^ 2 + 3 * y + z + 1 := by
    dsimp [x, y, z]
    ring
  rw [hid]
  positivity

theorem R_less_than_c (a b c : ℤ)
    (ha : 1 ≤ a) (hb : 3*a ≤ b) (hc : b*(b-a)+b+1 ≤ c) :
    0 < -a + 3 * b := by
  let x := a-1
  let y := b-3*a
  let z := c-(b*(b-a)+b+1)
  have hx : 0 ≤ x := by dsimp [x]; linarith
  have hy : 0 ≤ y := by dsimp [y]; linarith
  have hz : 0 ≤ z := by dsimp [z]; linarith
  have hid : -a + 3 * b = 8 * x + 3 * y + 8 := by
    dsimp [x, y, z]
    ring
  rw [hid]
  positivity

theorem B_positive (a b c : ℤ)
    (ha : 1 ≤ a) (hb : 3*a ≤ b) (hc : b*(b-a)+b+1 ≤ c) :
    0 < 2 * a * b - 3 * b ^ 2 + c * (-a + 2 * b) := by
  let x := a-1
  let y := b-3*a
  let z := c-(b*(b-a)+b+1)
  have hx : 0 ≤ x := by dsimp [x]; linarith
  have hy : 0 ≤ y := by dsimp [y]; linarith
  have hz : 0 ≤ z := by dsimp [z]; linarith
  have hid : 2 * a * b - 3 * b ^ 2 + c * (-a + 2 * b) = 30 * x ^ 3 + 37 * x ^ 2 * y + 84 * x ^ 2 + 15 * x * y ^ 2 + 69 * x * y + 5 * x * z + 83 * x + 2 * y ^ 3 + 14 * y ^ 2 + 2 * y * z + 34 * y + 5 * z + 29 := by
    dsimp [x, y, z]
    ring
  rw [hid]
  positivity

theorem B_less_than_2bc (a b c : ℤ)
    (ha : 1 ≤ a) (hb : 3*a ≤ b) (hc : b*(b-a)+b+1 ≤ c) :
    0 < -2 * a * b + 3 * b ^ 2 + 2 * b * c - c * (-a + 2 * b) := by
  let x := a-1
  let y := b-3*a
  let z := c-(b*(b-a)+b+1)
  have hx : 0 ≤ x := by dsimp [x]; linarith
  have hy : 0 ≤ y := by dsimp [y]; linarith
  have hz : 0 ≤ z := by dsimp [z]; linarith
  have hid : -2 * a * b + 3 * b ^ 2 + 2 * b * c - c * (-a + 2 * b) = 6 * x ^ 3 + 5 * x ^ 2 * y + 42 * x ^ 2 + x * y ^ 2 + 27 * x * y + x * z + 67 * x + 4 * y ^ 2 + 22 * y + z + 31 := by
    dsimp [x, y, z]
    ring
  rw [hid]
  positivity

theorem U_positive (a b c : ℤ)
    (ha : 1 ≤ a) (hb : 3*a ≤ b) (hc : b*(b-a)+b+1 ≤ c) :
    0 < a * b + 3 * c ^ 2 - 2 * c * (a + b) := by
  let x := a-1
  let y := b-3*a
  let z := c-(b*(b-a)+b+1)
  have hx : 0 ≤ x := by dsimp [x]; linarith
  have hy : 0 ≤ y := by dsimp [y]; linarith
  have hz : 0 ≤ z := by dsimp [z]; linarith
  have hid : a * b + 3 * c ^ 2 - 2 * c * (a + b) = 108 * x ^ 4 + 180 * x ^ 3 * y + 492 * x ^ 3 + 111 * x ^ 2 * y ^ 2 + 614 * x ^ 2 * y + 36 * x ^ 2 * z + 870 * x ^ 2 + 30 * x * y ^ 3 + 252 * x * y ^ 2 + 30 * x * y * z + 723 * x * y + 82 * x * z + 706 * x + 3 * y ^ 4 + 34 * y ^ 3 + 6 * y ^ 2 * z + 148 * y ^ 2 + 34 * y * z + 293 * y + 3 * z ^ 2 + 52 * z + 223 := by
    dsimp [x, y, z]
    ring
  rw [hid]
  positivity

theorem U_less_than_3c_squared (a b c : ℤ)
    (ha : 1 ≤ a) (hb : 3*a ≤ b) (hc : b*(b-a)+b+1 ≤ c) :
    0 < -a * b + 2 * c * (a + b) := by
  let x := a-1
  let y := b-3*a
  let z := c-(b*(b-a)+b+1)
  have hx : 0 ≤ x := by dsimp [x]; linarith
  have hy : 0 ≤ y := by dsimp [y]; linarith
  have hz : 0 ≤ z := by dsimp [z]; linarith
  have hid : -a * b + 2 * c * (a + b) = 48 * x ^ 3 + 52 * x ^ 2 * y + 165 * x ^ 2 + 18 * x * y ^ 2 + 117 * x * y + 8 * x * z + 194 * x + 2 * y ^ 3 + 20 * y ^ 2 + 2 * y * z + 67 * y + 8 * z + 77 := by
    dsimp [x, y, z]
    ring
  rw [hid]
  positivity

theorem c_greater_than_a_plus_b (a b c : ℤ)
    (ha : 1 ≤ a) (hb : 3*a ≤ b) (hc : b*(b-a)+b+1 ≤ c) :
    0 < -a - b + c := by
  let x := a-1
  let y := b-3*a
  let z := c-(b*(b-a)+b+1)
  have hx : 0 ≤ x := by dsimp [x]; linarith
  have hy : 0 ≤ y := by dsimp [y]; linarith
  have hz : 0 ≤ z := by dsimp [z]; linarith
  have hid : -a - b + c = 6 * x ^ 2 + 5 * x * y + 11 * x + y ^ 2 + 5 * y + z + 6 := by
    dsimp [x, y, z]
    ring
  rw [hid]
  positivity

theorem largest_gap_exceeds_L (a b c : ℤ)
    (ha : 1 ≤ a) (hb : 3*a ≤ b) (hc : b*(b-a)+b+1 ≤ c) :
    0 < -b * (-a + b) - b + c := by
  let x := a-1
  let y := b-3*a
  let z := c-(b*(b-a)+b+1)
  have hx : 0 ≤ x := by dsimp [x]; linarith
  have hy : 0 ≤ y := by dsimp [y]; linarith
  have hz : 0 ≤ z := by dsimp [z]; linarith
  have hid : -b * (-a + b) - b + c = z + 1 := by
    dsimp [x, y, z]
    ring
  rw [hid]
  positivity

theorem p1_to_p2_h0_gap (a b c : ℤ)
    (ha : 1 ≤ a) (hb : 3*a ≤ b) (hc : b*(b-a)+b+1 ≤ c) :
    0 < 2 * a * b - 3 * b ^ 2 + c * (-a + 2 * b) - (-2 * a + 2 * b) * (a - 3 * b + c) := by
  let x := a-1
  let y := b-3*a
  let z := c-(b*(b-a)+b+1)
  have hx : 0 ≤ x := by dsimp [x]; linarith
  have hy : 0 ≤ y := by dsimp [y]; linarith
  have hz : 0 ≤ z := by dsimp [z]; linarith
  have hid : 2 * a * b - 3 * b ^ 2 + c * (-a + 2 * b) - (-2 * a + 2 * b) * (a - 3 * b + c) = 6 * x ^ 3 + 5 * x ^ 2 * y + 32 * x ^ 2 + x * y ^ 2 + 23 * x * y + x * z + 47 * x + 4 * y ^ 2 + 18 * y + z + 21 := by
    dsimp [x, y, z]
    ring
  rw [hid]
  positivity

theorem p1_to_p3_low_gap (a b c : ℤ)
    (ha : 1 ≤ a) (hb : 3*a ≤ b) (hc : b*(b-a)+b+1 ≤ c) :
    0 < (-a + c) * (3 * a - 2 * b + c) := by
  let x := a-1
  let y := b-3*a
  let z := c-(b*(b-a)+b+1)
  have hx : 0 ≤ x := by dsimp [x]; linarith
  have hy : 0 ≤ y := by dsimp [y]; linarith
  have hz : 0 ≤ z := by dsimp [z]; linarith
  have hid : (-a + c) * (3 * a - 2 * b + c) = 36 * x ^ 4 + 60 * x ^ 3 * y + 156 * x ^ 3 + 37 * x ^ 2 * y ^ 2 + 190 * x ^ 2 * y + 12 * x ^ 2 * z + 264 * x ^ 2 + 10 * x * y ^ 3 + 76 * x * y ^ 2 + 10 * x * y * z + 208 * x * y + 26 * x * z + 206 * x + y ^ 4 + 10 * y ^ 3 + 2 * y ^ 2 * z + 40 * y ^ 2 + 10 * y * z + 78 * y + z ^ 2 + 16 * z + 63 := by
    dsimp [x, y, z]
    ring
  rw [hid]
  positivity

theorem p0_to_p3_low_gap (a b c : ℤ)
    (ha : 1 ≤ a) (hb : 3*a ≤ b) (hc : b*(b-a)+b+1 ≤ c) :
    0 < -a * b * c + c * (-a + c) * (-b + c) := by
  let x := a-1
  let y := b-3*a
  let z := c-(b*(b-a)+b+1)
  have hx : 0 ≤ x := by dsimp [x]; linarith
  have hy : 0 ≤ y := by dsimp [y]; linarith
  have hz : 0 ≤ z := by dsimp [z]; linarith
  have hid : -a * b * c + c * (-a + c) * (-b + c) = 216 * x ^ 6 + 540 * x ^ 5 * y + 1476 * x ^ 5 + 558 * x ^ 4 * y ^ 2 + 3072 * x ^ 4 * y + 108 * x ^ 4 * z + 4266 * x ^ 4 + 305 * x ^ 3 * y ^ 3 + 2537 * x ^ 3 * y ^ 2 + 180 * x ^ 3 * y * z + 7107 * x ^ 3 * y + 492 * x ^ 3 * z + 6675 * x ^ 3 + 93 * x ^ 2 * y ^ 4 + 1039 * x ^ 2 * y ^ 3 + 111 * x ^ 2 * y ^ 2 * z + 4403 * x ^ 2 * y ^ 2 + 614 * x ^ 2 * y * z + 8357 * x ^ 2 * y + 18 * x ^ 2 * z ^ 2 + 867 * x ^ 2 * z + 5970 * x ^ 2 + 15 * x * y ^ 5 + 211 * x * y ^ 4 + 30 * x * y ^ 3 * z + 1202 * x * y ^ 3 + 252 * x * y ^ 2 * z + 3456 * x * y ^ 2 + 15 * x * y * z ^ 2 + 722 * x * y * z + 5000 * x * y + 41 * x * z ^ 2 + 700 * x * z + 2900 * x + y ^ 6 + 17 * y ^ 5 + 3 * y ^ 4 * z + 122 * y ^ 4 + 34 * y ^ 3 * z + 472 * y ^ 3 + 3 * y ^ 2 * z ^ 2 + 148 * y ^ 2 * z + 1036 * y ^ 2 + 17 * y * z ^ 2 + 292 * y * z + 1220 * y + z ^ 3 + 26 * z ^ 2 + 220 * z + 600 := by
    dsimp [x, y, z]
    ring
  rw [hid]
  positivity

theorem p2_to_p3_low_gap (a b c : ℤ)
    (ha : 1 ≤ a) (hb : 3*a ≤ b) (hc : b*(b-a)+b+1 ≤ c) :
    0 < -b * (-a + b) + c * (-a + c) := by
  let x := a-1
  let y := b-3*a
  let z := c-(b*(b-a)+b+1)
  have hx : 0 ≤ x := by dsimp [x]; linarith
  have hy : 0 ≤ y := by dsimp [y]; linarith
  have hz : 0 ≤ z := by dsimp [z]; linarith
  have hid : -b * (-a + b) + c * (-a + c) = 36 * x ^ 4 + 60 * x ^ 3 * y + 174 * x ^ 3 + 37 * x ^ 2 * y ^ 2 + 217 * x ^ 2 * y + 12 * x ^ 2 * z + 318 * x ^ 2 + 10 * x * y ^ 3 + 89 * x * y ^ 2 + 10 * x * y * z + 264 * x * y + 29 * x * z + 263 * x + y ^ 4 + 12 * y ^ 3 + 2 * y ^ 2 * z + 54 * y ^ 2 + 12 * y * z + 109 * y + z ^ 2 + 19 * z + 84 := by
    dsimp [x, y, z]
    ring
  rw [hid]
  positivity

theorem a_less_b (a b c : ℤ)
    (ha : 1 ≤ a) (hb : 3*a ≤ b) (hc : b*(b-a)+b+1 ≤ c) :
    0 < -a + b := by
  let x := a-1
  let y := b-3*a
  let z := c-(b*(b-a)+b+1)
  have hx : 0 ≤ x := by dsimp [x]; linarith
  have hy : 0 ≤ y := by dsimp [y]; linarith
  have hz : 0 ≤ z := by dsimp [z]; linarith
  have hid : -a + b = 2 * x + y + 2 := by
    dsimp [x, y, z]
    ring
  rw [hid]
  positivity

theorem b_less_c (a b c : ℤ)
    (ha : 1 ≤ a) (hb : 3*a ≤ b) (hc : b*(b-a)+b+1 ≤ c) :
    0 < -b + c := by
  let x := a-1
  let y := b-3*a
  let z := c-(b*(b-a)+b+1)
  have hx : 0 ≤ x := by dsimp [x]; linarith
  have hy : 0 ≤ y := by dsimp [y]; linarith
  have hz : 0 ≤ z := by dsimp [z]; linarith
  have hid : -b + c = 6 * x ^ 2 + 5 * x * y + 12 * x + y ^ 2 + 5 * y + z + 7 := by
    dsimp [x, y, z]
    ring
  rw [hid]
  positivity

theorem S_positive (a b c : ℤ)
    (ha : 1 ≤ a) (hb : 3*a ≤ b) (hc : b*(b-a)+b+1 ≤ c) :
    0 < a + b + c := by
  let x := a-1
  let y := b-3*a
  let z := c-(b*(b-a)+b+1)
  have hx : 0 ≤ x := by dsimp [x]; linarith
  have hy : 0 ≤ y := by dsimp [y]; linarith
  have hz : 0 ≤ z := by dsimp [z]; linarith
  have hid : a + b + c = 6 * x ^ 2 + 5 * x * y + 19 * x + y ^ 2 + 7 * y + z + 14 := by
    dsimp [x, y, z]
    ring
  rw [hid]
  positivity

theorem S_less_3c (a b c : ℤ)
    (ha : 1 ≤ a) (hb : 3*a ≤ b) (hc : b*(b-a)+b+1 ≤ c) :
    0 < -a - b + 2 * c := by
  let x := a-1
  let y := b-3*a
  let z := c-(b*(b-a)+b+1)
  have hx : 0 ≤ x := by dsimp [x]; linarith
  have hy : 0 ≤ y := by dsimp [y]; linarith
  have hz : 0 ≤ z := by dsimp [z]; linarith
  have hid : -a - b + 2 * c = 12 * x ^ 2 + 10 * x * y + 26 * x + 2 * y ^ 2 + 11 * y + 2 * z + 16 := by
    dsimp [x, y, z]
    ring
  rw [hid]
  positivity

theorem T_positive (a b c : ℤ)
    (ha : 1 ≤ a) (hb : 3*a ≤ b) (hc : b*(b-a)+b+1 ≤ c) :
    0 < a * b + a * c + b * c := by
  let x := a-1
  let y := b-3*a
  let z := c-(b*(b-a)+b+1)
  have hx : 0 ≤ x := by dsimp [x]; linarith
  have hy : 0 ≤ y := by dsimp [y]; linarith
  have hz : 0 ≤ z := by dsimp [z]; linarith
  have hid : a * b + a * c + b * c = 24 * x ^ 3 + 26 * x ^ 2 * y + 87 * x ^ 2 + 9 * x * y ^ 2 + 60 * x * y + 4 * x * z + 106 * x + y ^ 3 + 10 * y ^ 2 + y * z + 35 * y + 4 * z + 43 := by
    dsimp [x, y, z]
    ring
  rw [hid]
  positivity

theorem T_less_3c_squared (a b c : ℤ)
    (ha : 1 ≤ a) (hb : 3*a ≤ b) (hc : b*(b-a)+b+1 ≤ c) :
    0 < -a * b - a * c - b * c + 3 * c ^ 2 := by
  let x := a-1
  let y := b-3*a
  let z := c-(b*(b-a)+b+1)
  have hx : 0 ≤ x := by dsimp [x]; linarith
  have hy : 0 ≤ y := by dsimp [y]; linarith
  have hz : 0 ≤ z := by dsimp [z]; linarith
  have hid : -a * b - a * c - b * c + 3 * c ^ 2 = 108 * x ^ 4 + 180 * x ^ 3 * y + 516 * x ^ 3 + 111 * x ^ 2 * y ^ 2 + 640 * x ^ 2 * y + 36 * x ^ 2 * z + 948 * x ^ 2 + 30 * x * y ^ 3 + 261 * x * y ^ 2 + 30 * x * y * z + 780 * x * y + 86 * x * z + 794 * x + 3 * y ^ 4 + 35 * y ^ 3 + 6 * y ^ 2 * z + 158 * y ^ 2 + 35 * y * z + 325 * y + 3 * z ^ 2 + 56 * z + 257 := by
    dsimp [x, y, z]
    ring
  rw [hid]
  positivity

theorem Z_positive (a b c : ℤ)
    (ha : 1 ≤ a) (hb : 3*a ≤ b) (hc : b*(b-a)+b+1 ≤ c) :
    0 < a * b * c := by
  let x := a-1
  let y := b-3*a
  let z := c-(b*(b-a)+b+1)
  have hx : 0 ≤ x := by dsimp [x]; linarith
  have hy : 0 ≤ y := by dsimp [y]; linarith
  have hz : 0 ≤ z := by dsimp [z]; linarith
  have hid : a * b * c = 18 * x ^ 4 + 21 * x ^ 3 * y + 81 * x ^ 3 + 8 * x ^ 2 * y ^ 2 + 69 * x ^ 2 * y + 3 * x ^ 2 * z + 138 * x ^ 2 + x * y ^ 3 + 17 * x * y ^ 2 + x * y * z + 76 * x * y + 6 * x * z + 105 * x + y ^ 3 + 9 * y ^ 2 + y * z + 28 * y + 3 * z + 30 := by
    dsimp [x, y, z]
    ring
  rw [hid]
  positivity

theorem Z_less_c_cubed (a b c : ℤ)
    (ha : 1 ≤ a) (hb : 3*a ≤ b) (hc : b*(b-a)+b+1 ≤ c) :
    0 < -a * b * c + c ^ 3 := by
  let x := a-1
  let y := b-3*a
  let z := c-(b*(b-a)+b+1)
  have hx : 0 ≤ x := by dsimp [x]; linarith
  have hy : 0 ≤ y := by dsimp [y]; linarith
  have hz : 0 ≤ z := by dsimp [z]; linarith
  have hid : -a * b * c + c ^ 3 = 216 * x ^ 6 + 540 * x ^ 5 * y + 1620 * x ^ 5 + 558 * x ^ 4 * y ^ 2 + 3348 * x ^ 4 * y + 108 * x ^ 4 * z + 5112 * x ^ 4 + 305 * x ^ 3 * y ^ 3 + 2745 * x ^ 3 * y ^ 2 + 180 * x ^ 3 * y * z + 8394 * x ^ 3 * y + 540 * x ^ 3 * z + 8694 * x ^ 3 + 93 * x ^ 2 * y ^ 4 + 1116 * x ^ 2 * y ^ 3 + 111 * x ^ 2 * y ^ 2 * z + 5125 * x ^ 2 * y ^ 2 + 666 * x ^ 2 * y * z + 10641 * x ^ 2 * y + 18 * x ^ 2 * z ^ 2 + 1032 * x ^ 2 * z + 8412 * x ^ 2 + 15 * x * y ^ 5 + 225 * x * y ^ 4 + 30 * x * y ^ 3 * z + 1379 * x * y ^ 3 + 270 * x * y ^ 2 * z + 4303 * x * y ^ 2 + 15 * x * y * z ^ 2 + 839 * x * y * z + 6824 * x * y + 45 * x * z ^ 2 + 894 * x * z + 4395 * x + y ^ 6 + 18 * y ^ 5 + 3 * y ^ 4 * z + 138 * y ^ 4 + 36 * y ^ 3 * z + 575 * y ^ 3 + 3 * y ^ 2 * z ^ 2 + 168 * y ^ 2 * z + 1371 * y ^ 2 + 18 * y * z ^ 2 + 359 * y * z + 1772 * y + z ^ 3 + 30 * z ^ 2 + 297 * z + 970 := by
    dsimp [x, y, z]
    ring
  rw [hid]
  positivity

theorem S1_less_2c (a b c : ℤ)
    (ha : 1 ≤ a) (hb : 3*a ≤ b) (hc : b*(b-a)+b+1 ≤ c) :
    0 < 3 * a - b + c := by
  let x := a-1
  let y := b-3*a
  let z := c-(b*(b-a)+b+1)
  have hx : 0 ≤ x := by dsimp [x]; linarith
  have hy : 0 ≤ y := by dsimp [y]; linarith
  have hz : 0 ≤ z := by dsimp [z]; linarith
  have hid : 3 * a - b + c = 6 * x ^ 2 + 5 * x * y + 15 * x + y ^ 2 + 5 * y + z + 10 := by
    dsimp [x, y, z]
    ring
  rw [hid]
  positivity

theorem D_positive (a b c : ℤ)
    (ha : 1 ≤ a) (hb : 3*a ≤ b) (hc : b*(b-a)+b+1 ≤ c) :
    0 < -a - b + 3 * c := by
  let x := a-1
  let y := b-3*a
  let z := c-(b*(b-a)+b+1)
  have hx : 0 ≤ x := by dsimp [x]; linarith
  have hy : 0 ≤ y := by dsimp [y]; linarith
  have hz : 0 ≤ z := by dsimp [z]; linarith
  have hid : -a - b + 3 * c = 18 * x ^ 2 + 15 * x * y + 41 * x + 3 * y ^ 2 + 17 * y + 3 * z + 26 := by
    dsimp [x, y, z]
    ring
  rw [hid]
  positivity

theorem D_less_3c (a b c : ℤ)
    (ha : 1 ≤ a) (hb : 3*a ≤ b) (hc : b*(b-a)+b+1 ≤ c) :
    0 < a + b := by
  let x := a-1
  let y := b-3*a
  let z := c-(b*(b-a)+b+1)
  have hx : 0 ≤ x := by dsimp [x]; linarith
  have hy : 0 ≤ y := by dsimp [y]; linarith
  have hz : 0 ≤ z := by dsimp [z]; linarith
  have hid : a + b = 4 * x + y + 4 := by
    dsimp [x, y, z]
    ring
  rw [hid]
  positivity

theorem A_positive (a b c : ℤ)
    (ha : 1 ≤ a) (hb : 3*a ≤ b) (hc : b*(b-a)+b+1 ≤ c) :
    0 < a * (-a + b) * (-a + c) := by
  let x := a-1
  let y := b-3*a
  let z := c-(b*(b-a)+b+1)
  have hx : 0 ≤ x := by dsimp [x]; linarith
  have hy : 0 ≤ y := by dsimp [y]; linarith
  have hz : 0 ≤ z := by dsimp [z]; linarith
  have hid : a * (-a + b) * (-a + c) = 12 * x ^ 4 + 16 * x ^ 3 * y + 52 * x ^ 3 + 7 * x ^ 2 * y ^ 2 + 52 * x ^ 2 * y + 2 * x ^ 2 * z + 86 * x ^ 2 + x * y ^ 3 + 15 * x * y ^ 2 + x * y * z + 57 * x * y + 4 * x * z + 64 * x + y ^ 3 + 8 * y ^ 2 + y * z + 21 * y + 2 * z + 18 := by
    dsimp [x, y, z]
    ring
  rw [hid]
  positivity

theorem A_less_c_cubed (a b c : ℤ)
    (ha : 1 ≤ a) (hb : 3*a ≤ b) (hc : b*(b-a)+b+1 ≤ c) :
    0 < -a * (-a + b) * (-a + c) + c ^ 3 := by
  let x := a-1
  let y := b-3*a
  let z := c-(b*(b-a)+b+1)
  have hx : 0 ≤ x := by dsimp [x]; linarith
  have hy : 0 ≤ y := by dsimp [y]; linarith
  have hz : 0 ≤ z := by dsimp [z]; linarith
  have hid : -a * (-a + b) * (-a + c) + c ^ 3 = 216 * x ^ 6 + 540 * x ^ 5 * y + 1620 * x ^ 5 + 558 * x ^ 4 * y ^ 2 + 3348 * x ^ 4 * y + 108 * x ^ 4 * z + 5118 * x ^ 4 + 305 * x ^ 3 * y ^ 3 + 2745 * x ^ 3 * y ^ 2 + 180 * x ^ 3 * y * z + 8399 * x ^ 3 * y + 540 * x ^ 3 * z + 8723 * x ^ 3 + 93 * x ^ 2 * y ^ 4 + 1116 * x ^ 2 * y ^ 3 + 111 * x ^ 2 * y ^ 2 * z + 5126 * x ^ 2 * y ^ 2 + 666 * x ^ 2 * y * z + 10658 * x ^ 2 * y + 18 * x ^ 2 * z ^ 2 + 1033 * x ^ 2 * z + 8464 * x ^ 2 + 15 * x * y ^ 5 + 225 * x * y ^ 4 + 30 * x * y ^ 3 * z + 1379 * x * y ^ 3 + 270 * x * y ^ 2 * z + 4305 * x * y ^ 2 + 15 * x * y * z ^ 2 + 839 * x * y * z + 6843 * x * y + 45 * x * z ^ 2 + 896 * x * z + 4436 * x + y ^ 6 + 18 * y ^ 5 + 3 * y ^ 4 * z + 138 * y ^ 4 + 36 * y ^ 3 * z + 575 * y ^ 3 + 3 * y ^ 2 * z ^ 2 + 168 * y ^ 2 * z + 1372 * y ^ 2 + 18 * y * z ^ 2 + 359 * y * z + 1779 * y + z ^ 3 + 30 * z ^ 2 + 298 * z + 982 := by
    dsimp [x, y, z]
    ring
  rw [hid]
  positivity

theorem C_positive (a b c : ℤ)
    (ha : 1 ≤ a) (hb : 3*a ≤ b) (hc : b*(b-a)+b+1 ≤ c) :
    0 < b * (-a + b) * (-b + c) := by
  let x := a-1
  let y := b-3*a
  let z := c-(b*(b-a)+b+1)
  have hx : 0 ≤ x := by dsimp [x]; linarith
  have hy : 0 ≤ y := by dsimp [y]; linarith
  have hz : 0 ≤ z := by dsimp [z]; linarith
  have hid : b * (-a + b) * (-b + c) = 36 * x ^ 4 + 60 * x ^ 3 * y + 144 * x ^ 3 + 37 * x ^ 2 * y ^ 2 + 180 * x ^ 2 * y + 6 * x ^ 2 * z + 222 * x ^ 2 + 10 * x * y ^ 3 + 74 * x * y ^ 2 + 5 * x * y * z + 185 * x * y + 12 * x * z + 156 * x + y ^ 4 + 10 * y ^ 3 + y ^ 2 * z + 38 * y ^ 2 + 5 * y * z + 65 * y + 6 * z + 42 := by
    dsimp [x, y, z]
    ring
  rw [hid]
  positivity

theorem C_less_c_cubed (a b c : ℤ)
    (ha : 1 ≤ a) (hb : 3*a ≤ b) (hc : b*(b-a)+b+1 ≤ c) :
    0 < -b * (-a + b) * (-b + c) + c ^ 3 := by
  let x := a-1
  let y := b-3*a
  let z := c-(b*(b-a)+b+1)
  have hx : 0 ≤ x := by dsimp [x]; linarith
  have hy : 0 ≤ y := by dsimp [y]; linarith
  have hz : 0 ≤ z := by dsimp [z]; linarith
  have hid : -b * (-a + b) * (-b + c) + c ^ 3 = 216 * x ^ 6 + 540 * x ^ 5 * y + 1620 * x ^ 5 + 558 * x ^ 4 * y ^ 2 + 3348 * x ^ 4 * y + 108 * x ^ 4 * z + 5094 * x ^ 4 + 305 * x ^ 3 * y ^ 3 + 2745 * x ^ 3 * y ^ 2 + 180 * x ^ 3 * y * z + 8355 * x ^ 3 * y + 540 * x ^ 3 * z + 8631 * x ^ 3 + 93 * x ^ 2 * y ^ 4 + 1116 * x ^ 2 * y ^ 3 + 111 * x ^ 2 * y ^ 2 * z + 5096 * x ^ 2 * y ^ 2 + 666 * x ^ 2 * y * z + 10530 * x ^ 2 * y + 18 * x ^ 2 * z ^ 2 + 1029 * x ^ 2 * z + 8328 * x ^ 2 + 15 * x * y ^ 5 + 225 * x * y ^ 4 + 30 * x * y ^ 3 * z + 1370 * x * y ^ 3 + 270 * x * y ^ 2 * z + 4246 * x * y ^ 2 + 15 * x * y * z ^ 2 + 835 * x * y * z + 6715 * x * y + 45 * x * z ^ 2 + 888 * x * z + 4344 * x + y ^ 6 + 18 * y ^ 5 + 3 * y ^ 4 * z + 137 * y ^ 4 + 36 * y ^ 3 * z + 566 * y ^ 3 + 3 * y ^ 2 * z ^ 2 + 167 * y ^ 2 * z + 1342 * y ^ 2 + 18 * y * z ^ 2 + 355 * y * z + 1735 * y + z ^ 3 + 30 * z ^ 2 + 294 * z + 958 := by
    dsimp [x, y, z]
    ring
  rw [hid]
  positivity

theorem F_positive (a b c : ℤ)
    (ha : 1 ≤ a) (hb : 3*a ≤ b) (hc : b*(b-a)+b+1 ≤ c) :
    0 < c * (-a + c) * (-b + c) := by
  let x := a-1
  let y := b-3*a
  let z := c-(b*(b-a)+b+1)
  have hx : 0 ≤ x := by dsimp [x]; linarith
  have hy : 0 ≤ y := by dsimp [y]; linarith
  have hz : 0 ≤ z := by dsimp [z]; linarith
  have hid : c * (-a + c) * (-b + c) = 216 * x ^ 6 + 540 * x ^ 5 * y + 1476 * x ^ 5 + 558 * x ^ 4 * y ^ 2 + 3072 * x ^ 4 * y + 108 * x ^ 4 * z + 4284 * x ^ 4 + 305 * x ^ 3 * y ^ 3 + 2537 * x ^ 3 * y ^ 2 + 180 * x ^ 3 * y * z + 7128 * x ^ 3 * y + 492 * x ^ 3 * z + 6756 * x ^ 3 + 93 * x ^ 2 * y ^ 4 + 1039 * x ^ 2 * y ^ 3 + 111 * x ^ 2 * y ^ 2 * z + 4411 * x ^ 2 * y ^ 2 + 614 * x ^ 2 * y * z + 8426 * x ^ 2 * y + 18 * x ^ 2 * z ^ 2 + 870 * x ^ 2 * z + 6108 * x ^ 2 + 15 * x * y ^ 5 + 211 * x * y ^ 4 + 30 * x * y ^ 3 * z + 1203 * x * y ^ 3 + 252 * x * y ^ 2 * z + 3473 * x * y ^ 2 + 15 * x * y * z ^ 2 + 723 * x * y * z + 5076 * x * y + 41 * x * z ^ 2 + 706 * x * z + 3005 * x + y ^ 6 + 17 * y ^ 5 + 3 * y ^ 4 * z + 122 * y ^ 4 + 34 * y ^ 3 * z + 473 * y ^ 3 + 3 * y ^ 2 * z ^ 2 + 148 * y ^ 2 * z + 1045 * y ^ 2 + 17 * y * z ^ 2 + 293 * y * z + 1248 * y + z ^ 3 + 26 * z ^ 2 + 223 * z + 630 := by
    dsimp [x, y, z]
    ring
  rw [hid]
  positivity

theorem F_less_c_cubed (a b c : ℤ)
    (ha : 1 ≤ a) (hb : 3*a ≤ b) (hc : b*(b-a)+b+1 ≤ c) :
    0 < c ^ 3 - c * (-a + c) * (-b + c) := by
  let x := a-1
  let y := b-3*a
  let z := c-(b*(b-a)+b+1)
  have hx : 0 ≤ x := by dsimp [x]; linarith
  have hy : 0 ≤ y := by dsimp [y]; linarith
  have hz : 0 ≤ z := by dsimp [z]; linarith
  have hid : c ^ 3 - c * (-a + c) * (-b + c) = 144 * x ^ 5 + 276 * x ^ 4 * y + 846 * x ^ 4 + 208 * x ^ 3 * y ^ 2 + 1287 * x ^ 3 * y + 48 * x ^ 3 * z + 2019 * x ^ 3 + 77 * x ^ 2 * y ^ 3 + 722 * x ^ 2 * y ^ 2 + 52 * x ^ 2 * y * z + 2284 * x ^ 2 * y + 165 * x ^ 2 * z + 2442 * x ^ 2 + 14 * x * y ^ 4 + 177 * x * y ^ 3 + 18 * x * y ^ 2 * z + 847 * x * y ^ 2 + 117 * x * y * z + 1824 * x * y + 4 * x * z ^ 2 + 194 * x * z + 1495 * x + y ^ 5 + 16 * y ^ 4 + 2 * y ^ 3 * z + 103 * y ^ 3 + 20 * y ^ 2 * z + 335 * y ^ 2 + y * z ^ 2 + 67 * y * z + 552 * y + 4 * z ^ 2 + 77 * z + 370 := by
    dsimp [x, y, z]
    ring
  rw [hid]
  positivity

theorem large_base_thresholds (c p : ℤ) (hc : 1 ≤ c) (hp : 100*c^5 ≤ p) :
    11*c^3 < p ∧ 13*c^2 < p ∧ 7*c^3 < p := by
  have h3 : c^3 ≤ c^5 := pow_le_pow_right₀ hc (by decide : 3 ≤ 5)
  have h2 : c^2 ≤ c^5 := pow_le_pow_right₀ hc (by decide : 2 ≤ 5)
  have hpos : 0 < c^5 := pow_pos (by linarith : 0 < c) 5
  constructor
  · nlinarith only [h3, hpos, hp]
  constructor <;> nlinarith only [h2, h3, hpos, hp]

end Erdos700.FourPrime.Bounds
