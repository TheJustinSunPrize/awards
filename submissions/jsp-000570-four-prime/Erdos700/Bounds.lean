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
    (ha : 1 ≤ a) (hb : 3*a ≤ b) (hc : 3*b+1 ≤ c) :
    0 < c - 9 := by
  let x := a-1
  let y := b-3*a
  let z := c-(3*b+1)
  have hx : 0 ≤ x := by dsimp [x]; linarith
  have hy : 0 ≤ y := by dsimp [y]; linarith
  have hz : 0 ≤ z := by dsimp [z]; linarith
  have hid : c - 9 = 9 * x + 3 * y + z + 1 := by
    dsimp [x, y, z]
    ring
  rw [hid]
  positivity

theorem T1_positive (a b c : ℤ)
    (ha : 1 ≤ a) (hb : 3*a ≤ b) (hc : 3*b+1 ≤ c) :
    0 < 3 * a ^ 2 - 2 * a * (b + c) + b * c := by
  let x := a-1
  let y := b-3*a
  let z := c-(3*b+1)
  have hx : 0 ≤ x := by dsimp [x]; linarith
  have hy : 0 ≤ y := by dsimp [y]; linarith
  have hz : 0 ≤ z := by dsimp [z]; linarith
  have hid : 3 * a ^ 2 - 2 * a * (b + c) + b * c = 6 * x ^ 2 + 10 * x * y + x * z + 13 * x + 3 * y ^ 2 + y * z + 11 * y + z + 7 := by
    dsimp [x, y, z]
    ring
  rw [hid]
  positivity

theorem T1_less_than_bc (a b c : ℤ)
    (ha : 1 ≤ a) (hb : 3*a ≤ b) (hc : 3*b+1 ≤ c) :
    0 < -3 * a ^ 2 + 2 * a * (b + c) := by
  let x := a-1
  let y := b-3*a
  let z := c-(3*b+1)
  have hx : 0 ≤ x := by dsimp [x]; linarith
  have hy : 0 ≤ y := by dsimp [y]; linarith
  have hz : 0 ≤ z := by dsimp [z]; linarith
  have hid : -3 * a ^ 2 + 2 * a * (b + c) = 21 * x ^ 2 + 8 * x * y + 2 * x * z + 44 * x + 8 * y + 2 * z + 23 := by
    dsimp [x, y, z]
    ring
  rw [hid]
  positivity

theorem S1_positive (a b c : ℤ)
    (ha : 1 ≤ a) (hb : 3*a ≤ b) (hc : 3*b+1 ≤ c) :
    0 < -3 * a + b + c := by
  let x := a-1
  let y := b-3*a
  let z := c-(3*b+1)
  have hx : 0 ≤ x := by dsimp [x]; linarith
  have hy : 0 ≤ y := by dsimp [y]; linarith
  have hz : 0 ≤ z := by dsimp [z]; linarith
  have hid : -3 * a + b + c = 9 * x + 4 * y + z + 10 := by
    dsimp [x, y, z]
    ring
  rw [hid]
  positivity

theorem R_greater_than_one (a b c : ℤ)
    (ha : 1 ≤ a) (hb : 3*a ≤ b) (hc : 3*b+1 ≤ c) :
    0 < a - 3 * b + c - 1 := by
  let x := a-1
  let y := b-3*a
  let z := c-(3*b+1)
  have hx : 0 ≤ x := by dsimp [x]; linarith
  have hy : 0 ≤ y := by dsimp [y]; linarith
  have hz : 0 ≤ z := by dsimp [z]; linarith
  have hid : a - 3 * b + c - 1 = x + z + 1 := by
    dsimp [x, y, z]
    ring
  rw [hid]
  positivity

theorem R_less_than_c (a b c : ℤ)
    (ha : 1 ≤ a) (hb : 3*a ≤ b) (hc : 3*b+1 ≤ c) :
    0 < -a + 3 * b := by
  let x := a-1
  let y := b-3*a
  let z := c-(3*b+1)
  have hx : 0 ≤ x := by dsimp [x]; linarith
  have hy : 0 ≤ y := by dsimp [y]; linarith
  have hz : 0 ≤ z := by dsimp [z]; linarith
  have hid : -a + 3 * b = 8 * x + 3 * y + 8 := by
    dsimp [x, y, z]
    ring
  rw [hid]
  positivity

theorem B_positive (a b c : ℤ)
    (ha : 1 ≤ a) (hb : 3*a ≤ b) (hc : 3*b+1 ≤ c) :
    0 < 2 * a * b - 3 * b ^ 2 + c * (-a + 2 * b) := by
  let x := a-1
  let y := b-3*a
  let z := c-(3*b+1)
  have hx : 0 ≤ x := by dsimp [x]; linarith
  have hy : 0 ≤ y := by dsimp [y]; linarith
  have hz : 0 ≤ z := by dsimp [z]; linarith
  have hid : 2 * a * b - 3 * b ^ 2 + c * (-a + 2 * b) = 24 * x ^ 2 + 17 * x * y + 5 * x * z + 53 * x + 3 * y ^ 2 + 2 * y * z + 19 * y + 5 * z + 29 := by
    dsimp [x, y, z]
    ring
  rw [hid]
  positivity

theorem B_less_than_2bc (a b c : ℤ)
    (ha : 1 ≤ a) (hb : 3*a ≤ b) (hc : 3*b+1 ≤ c) :
    0 < -2 * a * b + 3 * b ^ 2 + 2 * b * c - c * (-a + 2 * b) := by
  let x := a-1
  let y := b-3*a
  let z := c-(3*b+1)
  have hx : 0 ≤ x := by dsimp [x]; linarith
  have hy : 0 ≤ y := by dsimp [y]; linarith
  have hz : 0 ≤ z := by dsimp [z]; linarith
  have hid : -2 * a * b + 3 * b ^ 2 + 2 * b * c - c * (-a + 2 * b) = 30 * x ^ 2 + 19 * x * y + x * z + 61 * x + 3 * y ^ 2 + 19 * y + z + 31 := by
    dsimp [x, y, z]
    ring
  rw [hid]
  positivity

theorem U_positive (a b c : ℤ)
    (ha : 1 ≤ a) (hb : 3*a ≤ b) (hc : 3*b+1 ≤ c) :
    0 < a * b + 3 * c ^ 2 - 2 * c * (a + b) := by
  let x := a-1
  let y := b-3*a
  let z := c-(3*b+1)
  have hx : 0 ≤ x := by dsimp [x]; linarith
  have hy : 0 ≤ y := by dsimp [y]; linarith
  have hz : 0 ≤ z := by dsimp [z]; linarith
  have hid : a * b + 3 * c ^ 2 - 2 * c * (a + b) = 174 * x ^ 2 + 121 * x * y + 46 * x * z + 394 * x + 21 * y ^ 2 + 16 * y * z + 137 * y + 3 * z ^ 2 + 52 * z + 223 := by
    dsimp [x, y, z]
    ring
  rw [hid]
  positivity

theorem U_less_than_3c_squared (a b c : ℤ)
    (ha : 1 ≤ a) (hb : 3*a ≤ b) (hc : 3*b+1 ≤ c) :
    0 < -a * b + 2 * c * (a + b) := by
  let x := a-1
  let y := b-3*a
  let z := c-(3*b+1)
  have hx : 0 ≤ x := by dsimp [x]; linarith
  have hy : 0 ≤ y := by dsimp [y]; linarith
  have hz : 0 ≤ z := by dsimp [z]; linarith
  have hid : -a * b + 2 * c * (a + b) = 69 * x ^ 2 + 41 * x * y + 8 * x * z + 146 * x + 6 * y ^ 2 + 2 * y * z + 43 * y + 8 * z + 77 := by
    dsimp [x, y, z]
    ring
  rw [hid]
  positivity

theorem c_greater_than_a_plus_b (a b c : ℤ)
    (ha : 1 ≤ a) (hb : 3*a ≤ b) (hc : 3*b+1 ≤ c) :
    0 < -a - b + c := by
  let x := a-1
  let y := b-3*a
  let z := c-(3*b+1)
  have hx : 0 ≤ x := by dsimp [x]; linarith
  have hy : 0 ≤ y := by dsimp [y]; linarith
  have hz : 0 ≤ z := by dsimp [z]; linarith
  have hid : -a - b + c = 5 * x + 2 * y + z + 6 := by
    dsimp [x, y, z]
    ring
  rw [hid]
  positivity

theorem L_less_c_squared (a b c : ℤ)
    (ha : 1 ≤ a) (hb : 3*a ≤ b) (hc : 3*b+1 ≤ c) :
    0 < c ^ 2 - b * (b - a) := by
  let x := a-1
  let y := b-3*a
  let z := c-(3*b+1)
  have hx : 0 ≤ x := by dsimp [x]; linarith
  have hy : 0 ≤ y := by dsimp [y]; linarith
  have hz : 0 ≤ z := by dsimp [z]; linarith
  have hid : c ^ 2 - b * (b - a) = 75 * x ^ 2 + 49 * x * y + 18 * x * z + 168 * x + 8 * y ^ 2 + 6 * y * z + 55 * y + z ^ 2 + 20 * z + 94 := by
    dsimp [x, y, z]
    ring
  rw [hid]
  positivity

theorem p1_to_p2_h0_gap (a b c : ℤ)
    (ha : 1 ≤ a) (hb : 3*a ≤ b) (hc : 3*b+1 ≤ c) :
    0 < 2 * a * b - 3 * b ^ 2 + c * (-a + 2 * b) - (-2 * a + 2 * b) * (a - 3 * b + c) := by
  let x := a-1
  let y := b-3*a
  let z := c-(3*b+1)
  have hx : 0 ≤ x := by dsimp [x]; linarith
  have hy : 0 ≤ y := by dsimp [y]; linarith
  have hz : 0 ≤ z := by dsimp [z]; linarith
  have hid : 2 * a * b - 3 * b ^ 2 + c * (-a + 2 * b) - (-2 * a + 2 * b) * (a - 3 * b + c) = 20 * x ^ 2 + 15 * x * y + x * z + 41 * x + 3 * y ^ 2 + 15 * y + z + 21 := by
    dsimp [x, y, z]
    ring
  rw [hid]
  positivity

theorem p1_to_p3_low_gap (a b c : ℤ)
    (ha : 1 ≤ a) (hb : 3*a ≤ b) (hc : 3*b+1 ≤ c) :
    0 < (-a + c) * (3 * a - 2 * b + c) := by
  let x := a-1
  let y := b-3*a
  let z := c-(3*b+1)
  have hx : 0 ≤ x := by dsimp [x]; linarith
  have hy : 0 ≤ y := by dsimp [y]; linarith
  have hz : 0 ≤ z := by dsimp [z]; linarith
  have hid : (-a + c) * (3 * a - 2 * b + c) = 48 * x ^ 2 + 26 * x * y + 14 * x * z + 110 * x + 3 * y ^ 2 + 4 * y * z + 30 * y + z ^ 2 + 16 * z + 63 := by
    dsimp [x, y, z]
    ring
  rw [hid]
  positivity

theorem p0_to_p3_low_gap (a b c : ℤ)
    (ha : 1 ≤ a) (hb : 3*a ≤ b) (hc : 3*b+1 ≤ c) :
    0 < -a * b * c + c * (-a + c) * (-b + c) := by
  let x := a-1
  let y := b-3*a
  let z := c-(3*b+1)
  have hx : 0 ≤ x := by dsimp [x]; linarith
  have hy : 0 ≤ y := by dsimp [y]; linarith
  have hz : 0 ≤ z := by dsimp [z]; linarith
  have hid : -a * b * c + c * (-a + c) * (-b + c) = 405 * x ^ 3 + 432 * x ^ 2 * y + 171 * x ^ 2 * z + 1386 * x ^ 2 + 153 * x * y ^ 2 + 120 * x * y * z + 984 * x * y + 23 * x * z ^ 2 + 388 * x * z + 1580 * x + 18 * y ^ 3 + 21 * y ^ 2 * z + 174 * y ^ 2 + 8 * y * z ^ 2 + 136 * y * z + 560 * y + z ^ 3 + 26 * z ^ 2 + 220 * z + 600 := by
    dsimp [x, y, z]
    ring
  rw [hid]
  positivity

theorem p2_to_p3_low_gap (a b c : ℤ)
    (ha : 1 ≤ a) (hb : 3*a ≤ b) (hc : 3*b+1 ≤ c) :
    0 < -b * (-a + b) + c * (-a + c) := by
  let x := a-1
  let y := b-3*a
  let z := c-(3*b+1)
  have hx : 0 ≤ x := by dsimp [x]; linarith
  have hy : 0 ≤ y := by dsimp [y]; linarith
  have hz : 0 ≤ z := by dsimp [z]; linarith
  have hid : -b * (-a + b) + c * (-a + c) = 66 * x ^ 2 + 46 * x * y + 17 * x * z + 149 * x + 8 * y ^ 2 + 6 * y * z + 52 * y + z ^ 2 + 19 * z + 84 := by
    dsimp [x, y, z]
    ring
  rw [hid]
  positivity

theorem a_less_b (a b c : ℤ)
    (ha : 1 ≤ a) (hb : 3*a ≤ b) (hc : 3*b+1 ≤ c) :
    0 < -a + b := by
  let x := a-1
  let y := b-3*a
  let z := c-(3*b+1)
  have hx : 0 ≤ x := by dsimp [x]; linarith
  have hy : 0 ≤ y := by dsimp [y]; linarith
  have hz : 0 ≤ z := by dsimp [z]; linarith
  have hid : -a + b = 2 * x + y + 2 := by
    dsimp [x, y, z]
    ring
  rw [hid]
  positivity

theorem b_less_c (a b c : ℤ)
    (ha : 1 ≤ a) (hb : 3*a ≤ b) (hc : 3*b+1 ≤ c) :
    0 < -b + c := by
  let x := a-1
  let y := b-3*a
  let z := c-(3*b+1)
  have hx : 0 ≤ x := by dsimp [x]; linarith
  have hy : 0 ≤ y := by dsimp [y]; linarith
  have hz : 0 ≤ z := by dsimp [z]; linarith
  have hid : -b + c = 6 * x + 2 * y + z + 7 := by
    dsimp [x, y, z]
    ring
  rw [hid]
  positivity

theorem S_positive (a b c : ℤ)
    (ha : 1 ≤ a) (hb : 3*a ≤ b) (hc : 3*b+1 ≤ c) :
    0 < a + b + c := by
  let x := a-1
  let y := b-3*a
  let z := c-(3*b+1)
  have hx : 0 ≤ x := by dsimp [x]; linarith
  have hy : 0 ≤ y := by dsimp [y]; linarith
  have hz : 0 ≤ z := by dsimp [z]; linarith
  have hid : a + b + c = 13 * x + 4 * y + z + 14 := by
    dsimp [x, y, z]
    ring
  rw [hid]
  positivity

theorem S_less_3c (a b c : ℤ)
    (ha : 1 ≤ a) (hb : 3*a ≤ b) (hc : 3*b+1 ≤ c) :
    0 < -a - b + 2 * c := by
  let x := a-1
  let y := b-3*a
  let z := c-(3*b+1)
  have hx : 0 ≤ x := by dsimp [x]; linarith
  have hy : 0 ≤ y := by dsimp [y]; linarith
  have hz : 0 ≤ z := by dsimp [z]; linarith
  have hid : -a - b + 2 * c = 14 * x + 5 * y + 2 * z + 16 := by
    dsimp [x, y, z]
    ring
  rw [hid]
  positivity

theorem T_positive (a b c : ℤ)
    (ha : 1 ≤ a) (hb : 3*a ≤ b) (hc : 3*b+1 ≤ c) :
    0 < a * b + a * c + b * c := by
  let x := a-1
  let y := b-3*a
  let z := c-(3*b+1)
  have hx : 0 ≤ x := by dsimp [x]; linarith
  have hy : 0 ≤ y := by dsimp [y]; linarith
  have hz : 0 ≤ z := by dsimp [z]; linarith
  have hid : a * b + a * c + b * c = 39 * x ^ 2 + 22 * x * y + 4 * x * z + 82 * x + 3 * y ^ 2 + y * z + 23 * y + 4 * z + 43 := by
    dsimp [x, y, z]
    ring
  rw [hid]
  positivity

theorem T_less_3c_squared (a b c : ℤ)
    (ha : 1 ≤ a) (hb : 3*a ≤ b) (hc : 3*b+1 ≤ c) :
    0 < -a * b - a * c - b * c + 3 * c ^ 2 := by
  let x := a-1
  let y := b-3*a
  let z := c-(3*b+1)
  have hx : 0 ≤ x := by dsimp [x]; linarith
  have hy : 0 ≤ y := by dsimp [y]; linarith
  have hz : 0 ≤ z := by dsimp [z]; linarith
  have hid : -a * b - a * c - b * c + 3 * c ^ 2 = 204 * x ^ 2 + 140 * x * y + 50 * x * z + 458 * x + 24 * y ^ 2 + 17 * y * z + 157 * y + 3 * z ^ 2 + 56 * z + 257 := by
    dsimp [x, y, z]
    ring
  rw [hid]
  positivity

theorem Z_positive (a b c : ℤ)
    (ha : 1 ≤ a) (hb : 3*a ≤ b) (hc : 3*b+1 ≤ c) :
    0 < a * b * c := by
  let x := a-1
  let y := b-3*a
  let z := c-(3*b+1)
  have hx : 0 ≤ x := by dsimp [x]; linarith
  have hy : 0 ≤ y := by dsimp [y]; linarith
  have hz : 0 ≤ z := by dsimp [z]; linarith
  have hid : a * b * c = 27 * x ^ 3 + 18 * x ^ 2 * y + 3 * x ^ 2 * z + 84 * x ^ 2 + 3 * x * y ^ 2 + x * y * z + 37 * x * y + 6 * x * z + 87 * x + 3 * y ^ 2 + y * z + 19 * y + 3 * z + 30 := by
    dsimp [x, y, z]
    ring
  rw [hid]
  positivity

theorem Z_less_c_cubed (a b c : ℤ)
    (ha : 1 ≤ a) (hb : 3*a ≤ b) (hc : 3*b+1 ≤ c) :
    0 < -a * b * c + c ^ 3 := by
  let x := a-1
  let y := b-3*a
  let z := c-(3*b+1)
  have hx : 0 ≤ x := by dsimp [x]; linarith
  have hy : 0 ≤ y := by dsimp [y]; linarith
  have hz : 0 ≤ z := by dsimp [z]; linarith
  have hid : -a * b * c + c ^ 3 = 702 * x ^ 3 + 711 * x ^ 2 * y + 240 * x ^ 2 * z + 2346 * x ^ 2 + 240 * x * y ^ 2 + 161 * x * y * z + 1583 * x * y + 27 * x * z ^ 2 + 534 * x * z + 2613 * x + 27 * y ^ 3 + 27 * y ^ 2 * z + 267 * y ^ 2 + 9 * y * z ^ 2 + 179 * y * z + 881 * y + z ^ 3 + 30 * z ^ 2 + 297 * z + 970 := by
    dsimp [x, y, z]
    ring
  rw [hid]
  positivity

theorem S1_less_2c (a b c : ℤ)
    (ha : 1 ≤ a) (hb : 3*a ≤ b) (hc : 3*b+1 ≤ c) :
    0 < 3 * a - b + c := by
  let x := a-1
  let y := b-3*a
  let z := c-(3*b+1)
  have hx : 0 ≤ x := by dsimp [x]; linarith
  have hy : 0 ≤ y := by dsimp [y]; linarith
  have hz : 0 ≤ z := by dsimp [z]; linarith
  have hid : 3 * a - b + c = 9 * x + 2 * y + z + 10 := by
    dsimp [x, y, z]
    ring
  rw [hid]
  positivity

theorem D_positive (a b c : ℤ)
    (ha : 1 ≤ a) (hb : 3*a ≤ b) (hc : 3*b+1 ≤ c) :
    0 < -a - b + 3 * c := by
  let x := a-1
  let y := b-3*a
  let z := c-(3*b+1)
  have hx : 0 ≤ x := by dsimp [x]; linarith
  have hy : 0 ≤ y := by dsimp [y]; linarith
  have hz : 0 ≤ z := by dsimp [z]; linarith
  have hid : -a - b + 3 * c = 23 * x + 8 * y + 3 * z + 26 := by
    dsimp [x, y, z]
    ring
  rw [hid]
  positivity

theorem D_less_3c (a b c : ℤ)
    (ha : 1 ≤ a) (hb : 3*a ≤ b) (hc : 3*b+1 ≤ c) :
    0 < a + b := by
  let x := a-1
  let y := b-3*a
  let z := c-(3*b+1)
  have hx : 0 ≤ x := by dsimp [x]; linarith
  have hy : 0 ≤ y := by dsimp [y]; linarith
  have hz : 0 ≤ z := by dsimp [z]; linarith
  have hid : a + b = 4 * x + y + 4 := by
    dsimp [x, y, z]
    ring
  rw [hid]
  positivity

theorem A_positive (a b c : ℤ)
    (ha : 1 ≤ a) (hb : 3*a ≤ b) (hc : 3*b+1 ≤ c) :
    0 < a * (-a + b) * (-a + c) := by
  let x := a-1
  let y := b-3*a
  let z := c-(3*b+1)
  have hx : 0 ≤ x := by dsimp [x]; linarith
  have hy : 0 ≤ y := by dsimp [y]; linarith
  have hz : 0 ≤ z := by dsimp [z]; linarith
  have hid : a * (-a + b) * (-a + c) = 16 * x ^ 3 + 14 * x ^ 2 * y + 2 * x ^ 2 * z + 50 * x ^ 2 + 3 * x * y ^ 2 + x * y * z + 29 * x * y + 4 * x * z + 52 * x + 3 * y ^ 2 + y * z + 15 * y + 2 * z + 18 := by
    dsimp [x, y, z]
    ring
  rw [hid]
  positivity

theorem A_less_c_cubed (a b c : ℤ)
    (ha : 1 ≤ a) (hb : 3*a ≤ b) (hc : 3*b+1 ≤ c) :
    0 < -a * (-a + b) * (-a + c) + c ^ 3 := by
  let x := a-1
  let y := b-3*a
  let z := c-(3*b+1)
  have hx : 0 ≤ x := by dsimp [x]; linarith
  have hy : 0 ≤ y := by dsimp [y]; linarith
  have hz : 0 ≤ z := by dsimp [z]; linarith
  have hid : -a * (-a + b) * (-a + c) + c ^ 3 = 713 * x ^ 3 + 715 * x ^ 2 * y + 241 * x ^ 2 * z + 2380 * x ^ 2 + 240 * x * y ^ 2 + 161 * x * y * z + 1591 * x * y + 27 * x * z ^ 2 + 536 * x * z + 2648 * x + 27 * y ^ 3 + 27 * y ^ 2 * z + 267 * y ^ 2 + 9 * y * z ^ 2 + 179 * y * z + 885 * y + z ^ 3 + 30 * z ^ 2 + 298 * z + 982 := by
    dsimp [x, y, z]
    ring
  rw [hid]
  positivity

theorem C_positive (a b c : ℤ)
    (ha : 1 ≤ a) (hb : 3*a ≤ b) (hc : 3*b+1 ≤ c) :
    0 < b * (-a + b) * (-b + c) := by
  let x := a-1
  let y := b-3*a
  let z := c-(3*b+1)
  have hx : 0 ≤ x := by dsimp [x]; linarith
  have hy : 0 ≤ y := by dsimp [y]; linarith
  have hz : 0 ≤ z := by dsimp [z]; linarith
  have hid : b * (-a + b) * (-b + c) = 36 * x ^ 3 + 42 * x ^ 2 * y + 6 * x ^ 2 * z + 114 * x ^ 2 + 16 * x * y ^ 2 + 5 * x * y * z + 89 * x * y + 12 * x * z + 120 * x + 2 * y ^ 3 + y ^ 2 * z + 17 * y ^ 2 + 5 * y * z + 47 * y + 6 * z + 42 := by
    dsimp [x, y, z]
    ring
  rw [hid]
  positivity

theorem C_less_c_cubed (a b c : ℤ)
    (ha : 1 ≤ a) (hb : 3*a ≤ b) (hc : 3*b+1 ≤ c) :
    0 < -b * (-a + b) * (-b + c) + c ^ 3 := by
  let x := a-1
  let y := b-3*a
  let z := c-(3*b+1)
  have hx : 0 ≤ x := by dsimp [x]; linarith
  have hy : 0 ≤ y := by dsimp [y]; linarith
  have hz : 0 ≤ z := by dsimp [z]; linarith
  have hid : -b * (-a + b) * (-b + c) + c ^ 3 = 693 * x ^ 3 + 687 * x ^ 2 * y + 237 * x ^ 2 * z + 2316 * x ^ 2 + 227 * x * y ^ 2 + 157 * x * y * z + 1531 * x * y + 27 * x * z ^ 2 + 528 * x * z + 2580 * x + 25 * y ^ 3 + 26 * y ^ 2 * z + 253 * y ^ 2 + 9 * y * z ^ 2 + 175 * y * z + 853 * y + z ^ 3 + 30 * z ^ 2 + 294 * z + 958 := by
    dsimp [x, y, z]
    ring
  rw [hid]
  positivity

theorem F_positive (a b c : ℤ)
    (ha : 1 ≤ a) (hb : 3*a ≤ b) (hc : 3*b+1 ≤ c) :
    0 < c * (-a + c) * (-b + c) := by
  let x := a-1
  let y := b-3*a
  let z := c-(3*b+1)
  have hx : 0 ≤ x := by dsimp [x]; linarith
  have hy : 0 ≤ y := by dsimp [y]; linarith
  have hz : 0 ≤ z := by dsimp [z]; linarith
  have hid : c * (-a + c) * (-b + c) = 432 * x ^ 3 + 450 * x ^ 2 * y + 174 * x ^ 2 * z + 1470 * x ^ 2 + 156 * x * y ^ 2 + 121 * x * y * z + 1021 * x * y + 23 * x * z ^ 2 + 394 * x * z + 1667 * x + 18 * y ^ 3 + 21 * y ^ 2 * z + 177 * y ^ 2 + 8 * y * z ^ 2 + 137 * y * z + 579 * y + z ^ 3 + 26 * z ^ 2 + 223 * z + 630 := by
    dsimp [x, y, z]
    ring
  rw [hid]
  positivity

theorem F_less_c_cubed (a b c : ℤ)
    (ha : 1 ≤ a) (hb : 3*a ≤ b) (hc : 3*b+1 ≤ c) :
    0 < c ^ 3 - c * (-a + c) * (-b + c) := by
  let x := a-1
  let y := b-3*a
  let z := c-(3*b+1)
  have hx : 0 ≤ x := by dsimp [x]; linarith
  have hy : 0 ≤ y := by dsimp [y]; linarith
  have hz : 0 ≤ z := by dsimp [z]; linarith
  have hid : c ^ 3 - c * (-a + c) * (-b + c) = 297 * x ^ 3 + 279 * x ^ 2 * y + 69 * x ^ 2 * z + 960 * x ^ 2 + 87 * x * y ^ 2 + 41 * x * y * z + 599 * x * y + 4 * x * z ^ 2 + 146 * x * z + 1033 * x + 9 * y ^ 3 + 6 * y ^ 2 * z + 93 * y ^ 2 + y * z ^ 2 + 43 * y * z + 321 * y + 4 * z ^ 2 + 77 * z + 370 := by
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
