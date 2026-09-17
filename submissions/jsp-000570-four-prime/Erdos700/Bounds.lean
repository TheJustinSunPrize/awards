import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

/-! Universal polynomial inequalities for the four-prime criterion.
Generated using nonnegative substitutions; each identity and sign is checked
by Lean. These statements concern all parameters in the stated range. -/

namespace Erdos700.FourPrime.Bounds
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

theorem c_at_least_90 (a b c : ℤ)
    (ha : 1 ≤ a) (hb : 3*a ≤ b) (hc : 10*b^2 ≤ c) :
    0 < c - 89 := by
  let x := a-1
  let y := b-3*a
  let z := c-10*b^2
  have hx : 0 ≤ x := by dsimp [x]; linarith
  have hy : 0 ≤ y := by dsimp [y]; linarith
  have hz : 0 ≤ z := by dsimp [z]; linarith
  have hid : c - 89 = 90 * x ^ 2 + 60 * x * y + 180 * x + 10 * y ^ 2 + 60 * y + z + 1 := by
    dsimp [x, y, z]
    ring
  rw [hid]
  positivity

theorem T1_positive (a b c : ℤ)
    (ha : 1 ≤ a) (hb : 3*a ≤ b) (hc : 10*b^2 ≤ c) :
    0 < 3 * a ^ 2 - 2 * a * (b + c) + b * c := by
  let x := a-1
  let y := b-3*a
  let z := c-10*b^2
  have hx : 0 ≤ x := by dsimp [x]; linarith
  have hy : 0 ≤ y := by dsimp [y]; linarith
  have hz : 0 ≤ z := by dsimp [z]; linarith
  have hid : 3 * a ^ 2 - 2 * a * (b + c) + b * c = 90 * x ^ 3 + 150 * x ^ 2 * y + 267 * x ^ 2 + 70 * x * y ^ 2 + 298 * x * y + x * z + 264 * x + 10 * y ^ 3 + 70 * y ^ 2 + y * z + 148 * y + z + 87 := by
    dsimp [x, y, z]
    ring
  rw [hid]
  positivity

theorem T1_less_than_bc (a b c : ℤ)
    (ha : 1 ≤ a) (hb : 3*a ≤ b) (hc : 10*b^2 ≤ c) :
    0 < -3 * a ^ 2 + 2 * a * (b + c) := by
  let x := a-1
  let y := b-3*a
  let z := c-10*b^2
  have hx : 0 ≤ x := by dsimp [x]; linarith
  have hy : 0 ≤ y := by dsimp [y]; linarith
  have hz : 0 ≤ z := by dsimp [z]; linarith
  have hid : -3 * a ^ 2 + 2 * a * (b + c) = 180 * x ^ 3 + 120 * x ^ 2 * y + 543 * x ^ 2 + 20 * x * y ^ 2 + 242 * x * y + 2 * x * z + 546 * x + 20 * y ^ 2 + 122 * y + 2 * z + 183 := by
    dsimp [x, y, z]
    ring
  rw [hid]
  positivity

theorem S1_positive (a b c : ℤ)
    (ha : 1 ≤ a) (hb : 3*a ≤ b) (hc : 10*b^2 ≤ c) :
    0 < -3 * a + b + c := by
  let x := a-1
  let y := b-3*a
  let z := c-10*b^2
  have hx : 0 ≤ x := by dsimp [x]; linarith
  have hy : 0 ≤ y := by dsimp [y]; linarith
  have hz : 0 ≤ z := by dsimp [z]; linarith
  have hid : -3 * a + b + c = 90 * x ^ 2 + 60 * x * y + 180 * x + 10 * y ^ 2 + 61 * y + z + 90 := by
    dsimp [x, y, z]
    ring
  rw [hid]
  positivity

theorem R_greater_than_one (a b c : ℤ)
    (ha : 1 ≤ a) (hb : 3*a ≤ b) (hc : 10*b^2 ≤ c) :
    0 < a - 3 * b + c - 1 := by
  let x := a-1
  let y := b-3*a
  let z := c-10*b^2
  have hx : 0 ≤ x := by dsimp [x]; linarith
  have hy : 0 ≤ y := by dsimp [y]; linarith
  have hz : 0 ≤ z := by dsimp [z]; linarith
  have hid : a - 3 * b + c - 1 = 90 * x ^ 2 + 60 * x * y + 172 * x + 10 * y ^ 2 + 57 * y + z + 81 := by
    dsimp [x, y, z]
    ring
  rw [hid]
  positivity

theorem R_less_than_c (a b c : ℤ)
    (ha : 1 ≤ a) (hb : 3*a ≤ b) (hc : 10*b^2 ≤ c) :
    0 < -a + 3 * b := by
  let x := a-1
  let y := b-3*a
  let z := c-10*b^2
  have hx : 0 ≤ x := by dsimp [x]; linarith
  have hy : 0 ≤ y := by dsimp [y]; linarith
  have hz : 0 ≤ z := by dsimp [z]; linarith
  have hid : -a + 3 * b = 8 * x + 3 * y + 8 := by
    dsimp [x, y, z]
    ring
  rw [hid]
  positivity

theorem B_positive (a b c : ℤ)
    (ha : 1 ≤ a) (hb : 3*a ≤ b) (hc : 10*b^2 ≤ c) :
    0 < 2 * a * b - 3 * b ^ 2 + c * (-a + 2 * b) := by
  let x := a-1
  let y := b-3*a
  let z := c-10*b^2
  have hx : 0 ≤ x := by dsimp [x]; linarith
  have hy : 0 ≤ y := by dsimp [y]; linarith
  have hz : 0 ≤ z := by dsimp [z]; linarith
  have hid : 2 * a * b - 3 * b ^ 2 + c * (-a + 2 * b) = 450 * x ^ 3 + 480 * x ^ 2 * y + 1329 * x ^ 2 + 170 * x * y ^ 2 + 944 * x * y + 5 * x * z + 1308 * x + 20 * y ^ 3 + 167 * y ^ 2 + 2 * y * z + 464 * y + 5 * z + 429 := by
    dsimp [x, y, z]
    ring
  rw [hid]
  positivity

theorem B_less_than_2bc (a b c : ℤ)
    (ha : 1 ≤ a) (hb : 3*a ≤ b) (hc : 10*b^2 ≤ c) :
    0 < -2 * a * b + 3 * b ^ 2 + 2 * b * c - c * (-a + 2 * b) := by
  let x := a-1
  let y := b-3*a
  let z := c-10*b^2
  have hx : 0 ≤ x := by dsimp [x]; linarith
  have hy : 0 ≤ y := by dsimp [y]; linarith
  have hz : 0 ≤ z := by dsimp [z]; linarith
  have hid : -2 * a * b + 3 * b ^ 2 + 2 * b * c - c * (-a + 2 * b) = 90 * x ^ 3 + 60 * x ^ 2 * y + 291 * x ^ 2 + 10 * x * y ^ 2 + 136 * x * y + x * z + 312 * x + 13 * y ^ 2 + 76 * y + z + 111 := by
    dsimp [x, y, z]
    ring
  rw [hid]
  positivity

theorem U_positive (a b c : ℤ)
    (ha : 1 ≤ a) (hb : 3*a ≤ b) (hc : 10*b^2 ≤ c) :
    0 < a * b + 3 * c ^ 2 - 2 * c * (a + b) := by
  let x := a-1
  let y := b-3*a
  let z := c-10*b^2
  have hx : 0 ≤ x := by dsimp [x]; linarith
  have hy : 0 ≤ y := by dsimp [y]; linarith
  have hz : 0 ≤ z := by dsimp [z]; linarith
  have hid : a * b + 3 * c ^ 2 - 2 * c * (a + b) = 24300 * x ^ 4 + 32400 * x ^ 3 * y + 96480 * x ^ 3 + 16200 * x ^ 2 * y ^ 2 + 96540 * x ^ 2 * y + 540 * x ^ 2 * z + 143643 * x ^ 2 + 3600 * x * y ^ 3 + 32200 * x * y ^ 2 + 360 * x * y * z + 95881 * x * y + 1072 * x * z + 95046 * x + 300 * y ^ 4 + 3580 * y ^ 3 + 60 * y ^ 2 * z + 16000 * y ^ 2 + 358 * y * z + 31741 * y + 3 * z ^ 2 + 532 * z + 23583 := by
    dsimp [x, y, z]
    ring
  rw [hid]
  positivity

theorem U_less_than_3c_squared (a b c : ℤ)
    (ha : 1 ≤ a) (hb : 3*a ≤ b) (hc : 10*b^2 ≤ c) :
    0 < -a * b + 2 * c * (a + b) := by
  let x := a-1
  let y := b-3*a
  let z := c-10*b^2
  have hx : 0 ≤ x := by dsimp [x]; linarith
  have hy : 0 ≤ y := by dsimp [y]; linarith
  have hz : 0 ≤ z := by dsimp [z]; linarith
  have hid : -a * b + 2 * c * (a + b) = 720 * x ^ 3 + 660 * x ^ 2 * y + 2157 * x ^ 2 + 200 * x * y ^ 2 + 1319 * x * y + 8 * x * z + 2154 * x + 20 * y ^ 3 + 200 * y ^ 2 + 2 * y * z + 659 * y + 8 * z + 717 := by
    dsimp [x, y, z]
    ring
  rw [hid]
  positivity

theorem c_greater_than_a_plus_b (a b c : ℤ)
    (ha : 1 ≤ a) (hb : 3*a ≤ b) (hc : 10*b^2 ≤ c) :
    0 < -a - b + c := by
  let x := a-1
  let y := b-3*a
  let z := c-10*b^2
  have hx : 0 ≤ x := by dsimp [x]; linarith
  have hy : 0 ≤ y := by dsimp [y]; linarith
  have hz : 0 ≤ z := by dsimp [z]; linarith
  have hid : -a - b + c = 90 * x ^ 2 + 60 * x * y + 176 * x + 10 * y ^ 2 + 59 * y + z + 86 := by
    dsimp [x, y, z]
    ring
  rw [hid]
  positivity

theorem largest_gap_exceeds_L (a b c : ℤ)
    (ha : 1 ≤ a) (hb : 3*a ≤ b) (hc : 10*b^2 ≤ c) :
    0 < -b * (-a + b) - b + c := by
  let x := a-1
  let y := b-3*a
  let z := c-10*b^2
  have hx : 0 ≤ x := by dsimp [x]; linarith
  have hy : 0 ≤ y := by dsimp [y]; linarith
  have hz : 0 ≤ z := by dsimp [z]; linarith
  have hid : -b * (-a + b) - b + c = 84 * x ^ 2 + 55 * x * y + 165 * x + 9 * y ^ 2 + 54 * y + z + 81 := by
    dsimp [x, y, z]
    ring
  rw [hid]
  positivity

theorem p1_to_p2_h0_gap (a b c : ℤ)
    (ha : 1 ≤ a) (hb : 3*a ≤ b) (hc : 10*b^2 ≤ c) :
    0 < 2 * a * b - 3 * b ^ 2 + c * (-a + 2 * b) - (-2 * a + 2 * b) * (a - 3 * b + c) := by
  let x := a-1
  let y := b-3*a
  let z := c-10*b^2
  have hx : 0 ≤ x := by dsimp [x]; linarith
  have hy : 0 ≤ y := by dsimp [y]; linarith
  have hz : 0 ≤ z := by dsimp [z]; linarith
  have hid : 2 * a * b - 3 * b ^ 2 + c * (-a + 2 * b) - (-2 * a + 2 * b) * (a - 3 * b + c) = 90 * x ^ 3 + 60 * x ^ 2 * y + 281 * x ^ 2 + 10 * x * y ^ 2 + 132 * x * y + x * z + 292 * x + 13 * y ^ 2 + 72 * y + z + 101 := by
    dsimp [x, y, z]
    ring
  rw [hid]
  positivity

theorem p1_to_p3_low_gap (a b c : ℤ)
    (ha : 1 ≤ a) (hb : 3*a ≤ b) (hc : 10*b^2 ≤ c) :
    0 < (-a + c) * (3 * a - 2 * b + c) := by
  let x := a-1
  let y := b-3*a
  let z := c-10*b^2
  have hx : 0 ≤ x := by dsimp [x]; linarith
  have hy : 0 ≤ y := by dsimp [y]; linarith
  have hz : 0 ≤ z := by dsimp [z]; linarith
  have hid : (-a + c) * (3 * a - 2 * b + c) = 8100 * x ^ 4 + 10800 * x ^ 3 * y + 32040 * x ^ 3 + 5400 * x ^ 2 * y ^ 2 + 31980 * x ^ 2 * y + 180 * x ^ 2 * z + 47523 * x ^ 2 + 1200 * x * y ^ 3 + 10640 * x * y ^ 2 + 120 * x * y * z + 31562 * x * y + 356 * x * z + 31326 * x + 100 * y ^ 4 + 1180 * y ^ 3 + 20 * y ^ 2 * z + 5240 * y ^ 2 + 118 * y * z + 10382 * y + z ^ 2 + 176 * z + 7743 := by
    dsimp [x, y, z]
    ring
  rw [hid]
  positivity

theorem p0_to_p3_low_gap (a b c : ℤ)
    (ha : 1 ≤ a) (hb : 3*a ≤ b) (hc : 10*b^2 ≤ c) :
    0 < -a * b * c + c * (-a + c) * (-b + c) := by
  let x := a-1
  let y := b-3*a
  let z := c-10*b^2
  have hx : 0 ≤ x := by dsimp [x]; linarith
  have hy : 0 ≤ y := by dsimp [y]; linarith
  have hz : 0 ≤ z := by dsimp [z]; linarith
  have hid : -a * b * c + c * (-a + c) * (-b + c) = 729000 * x ^ 6 + 1458000 * x ^ 5 * y + 4341600 * x ^ 5 + 1215000 * x ^ 4 * y ^ 2 + 7238700 * x ^ 4 * y + 24300 * x ^ 4 * z + 10773000 * x ^ 4 + 540000 * x ^ 3 * y ^ 3 + 4827600 * x ^ 3 * y ^ 2 + 32400 * x ^ 3 * y * z + 14374800 * x ^ 3 * y + 96480 * x ^ 3 * z + 14256000 * x ^ 3 + 135000 * x ^ 2 * y ^ 4 + 1609800 * x ^ 2 * y ^ 3 + 16200 * x ^ 2 * y ^ 2 * z + 7192800 * x ^ 2 * y ^ 2 + 96540 * x ^ 2 * y * z + 14272200 * x ^ 2 * y + 270 * x ^ 2 * z ^ 2 + 143640 * x ^ 2 * z + 10611000 * x ^ 2 + 18000 * x * y ^ 5 + 268400 * x * y ^ 4 + 3600 * x * y ^ 3 * z + 1599600 * x * y ^ 3 + 32200 * x * y ^ 2 * z + 4762800 * x * y ^ 2 + 180 * x * y * z ^ 2 + 95880 * x * y * z + 7084800 * x * y + 536 * x * z ^ 2 + 95040 * x * z + 4212000 * x + 1000 * y ^ 6 + 17900 * y ^ 5 + 300 * y ^ 4 * z + 133400 * y ^ 4 + 3580 * y ^ 3 * z + 529800 * y ^ 3 + 30 * y ^ 2 * z ^ 2 + 16000 * y ^ 2 * z + 1182600 * y ^ 2 + 179 * y * z ^ 2 + 31740 * y * z + 1406700 * y + z ^ 3 + 266 * z ^ 2 + 23580 * z + 696600 := by
    dsimp [x, y, z]
    ring
  rw [hid]
  positivity

theorem p2_to_p3_low_gap (a b c : ℤ)
    (ha : 1 ≤ a) (hb : 3*a ≤ b) (hc : 10*b^2 ≤ c) :
    0 < -b * (-a + b) + c * (-a + c) := by
  let x := a-1
  let y := b-3*a
  let z := c-10*b^2
  have hx : 0 ≤ x := by dsimp [x]; linarith
  have hy : 0 ≤ y := by dsimp [y]; linarith
  have hz : 0 ≤ z := by dsimp [z]; linarith
  have hid : -b * (-a + b) + c * (-a + c) = 8100 * x ^ 4 + 10800 * x ^ 3 * y + 32310 * x ^ 3 + 5400 * x ^ 2 * y ^ 2 + 32340 * x ^ 2 * y + 180 * x ^ 2 * z + 48324 * x ^ 2 + 1200 * x * y ^ 3 + 10790 * x * y ^ 2 + 120 * x * y * z + 32275 * x * y + 359 * x * z + 32118 * x + 100 * y ^ 4 + 1200 * y ^ 3 + 20 * y ^ 2 * z + 5389 * y ^ 2 + 120 * y * z + 10735 * y + z ^ 2 + 179 * z + 8004 := by
    dsimp [x, y, z]
    ring
  rw [hid]
  positivity

theorem a_less_b (a b c : ℤ)
    (ha : 1 ≤ a) (hb : 3*a ≤ b) (hc : 10*b^2 ≤ c) :
    0 < -a + b := by
  let x := a-1
  let y := b-3*a
  let z := c-10*b^2
  have hx : 0 ≤ x := by dsimp [x]; linarith
  have hy : 0 ≤ y := by dsimp [y]; linarith
  have hz : 0 ≤ z := by dsimp [z]; linarith
  have hid : -a + b = 2 * x + y + 2 := by
    dsimp [x, y, z]
    ring
  rw [hid]
  positivity

theorem b_less_c (a b c : ℤ)
    (ha : 1 ≤ a) (hb : 3*a ≤ b) (hc : 10*b^2 ≤ c) :
    0 < -b + c := by
  let x := a-1
  let y := b-3*a
  let z := c-10*b^2
  have hx : 0 ≤ x := by dsimp [x]; linarith
  have hy : 0 ≤ y := by dsimp [y]; linarith
  have hz : 0 ≤ z := by dsimp [z]; linarith
  have hid : -b + c = 90 * x ^ 2 + 60 * x * y + 177 * x + 10 * y ^ 2 + 59 * y + z + 87 := by
    dsimp [x, y, z]
    ring
  rw [hid]
  positivity

theorem S_positive (a b c : ℤ)
    (ha : 1 ≤ a) (hb : 3*a ≤ b) (hc : 10*b^2 ≤ c) :
    0 < a + b + c := by
  let x := a-1
  let y := b-3*a
  let z := c-10*b^2
  have hx : 0 ≤ x := by dsimp [x]; linarith
  have hy : 0 ≤ y := by dsimp [y]; linarith
  have hz : 0 ≤ z := by dsimp [z]; linarith
  have hid : a + b + c = 90 * x ^ 2 + 60 * x * y + 184 * x + 10 * y ^ 2 + 61 * y + z + 94 := by
    dsimp [x, y, z]
    ring
  rw [hid]
  positivity

theorem S_less_3c (a b c : ℤ)
    (ha : 1 ≤ a) (hb : 3*a ≤ b) (hc : 10*b^2 ≤ c) :
    0 < -a - b + 2 * c := by
  let x := a-1
  let y := b-3*a
  let z := c-10*b^2
  have hx : 0 ≤ x := by dsimp [x]; linarith
  have hy : 0 ≤ y := by dsimp [y]; linarith
  have hz : 0 ≤ z := by dsimp [z]; linarith
  have hid : -a - b + 2 * c = 180 * x ^ 2 + 120 * x * y + 356 * x + 20 * y ^ 2 + 119 * y + 2 * z + 176 := by
    dsimp [x, y, z]
    ring
  rw [hid]
  positivity

theorem T_positive (a b c : ℤ)
    (ha : 1 ≤ a) (hb : 3*a ≤ b) (hc : 10*b^2 ≤ c) :
    0 < a * b + a * c + b * c := by
  let x := a-1
  let y := b-3*a
  let z := c-10*b^2
  have hx : 0 ≤ x := by dsimp [x]; linarith
  have hy : 0 ≤ y := by dsimp [y]; linarith
  have hz : 0 ≤ z := by dsimp [z]; linarith
  have hid : a * b + a * c + b * c = 360 * x ^ 3 + 330 * x ^ 2 * y + 1083 * x ^ 2 + 100 * x * y ^ 2 + 661 * x * y + 4 * x * z + 1086 * x + 10 * y ^ 3 + 100 * y ^ 2 + y * z + 331 * y + 4 * z + 363 := by
    dsimp [x, y, z]
    ring
  rw [hid]
  positivity

theorem T_less_3c_squared (a b c : ℤ)
    (ha : 1 ≤ a) (hb : 3*a ≤ b) (hc : 10*b^2 ≤ c) :
    0 < -a * b - a * c - b * c + 3 * c ^ 2 := by
  let x := a-1
  let y := b-3*a
  let z := c-10*b^2
  have hx : 0 ≤ x := by dsimp [x]; linarith
  have hy : 0 ≤ y := by dsimp [y]; linarith
  have hz : 0 ≤ z := by dsimp [z]; linarith
  have hid : -a * b - a * c - b * c + 3 * c ^ 2 = 24300 * x ^ 4 + 32400 * x ^ 3 * y + 96840 * x ^ 3 + 16200 * x ^ 2 * y ^ 2 + 96870 * x ^ 2 * y + 540 * x ^ 2 * z + 144717 * x ^ 2 + 3600 * x * y ^ 3 + 32300 * x * y ^ 2 + 360 * x * y * z + 96539 * x * y + 1076 * x * z + 96114 * x + 300 * y ^ 4 + 3590 * y ^ 3 + 60 * y ^ 2 * z + 16100 * y ^ 2 + 359 * y * z + 32069 * y + 3 * z ^ 2 + 536 * z + 23937 := by
    dsimp [x, y, z]
    ring
  rw [hid]
  positivity

theorem Z_positive (a b c : ℤ)
    (ha : 1 ≤ a) (hb : 3*a ≤ b) (hc : 10*b^2 ≤ c) :
    0 < a * b * c := by
  let x := a-1
  let y := b-3*a
  let z := c-10*b^2
  have hx : 0 ≤ x := by dsimp [x]; linarith
  have hy : 0 ≤ y := by dsimp [y]; linarith
  have hz : 0 ≤ z := by dsimp [z]; linarith
  have hid : a * b * c = 270 * x ^ 4 + 270 * x ^ 3 * y + 1080 * x ^ 3 + 90 * x ^ 2 * y ^ 2 + 810 * x ^ 2 * y + 3 * x ^ 2 * z + 1620 * x ^ 2 + 10 * x * y ^ 3 + 180 * x * y ^ 2 + x * y * z + 810 * x * y + 6 * x * z + 1080 * x + 10 * y ^ 3 + 90 * y ^ 2 + y * z + 270 * y + 3 * z + 270 := by
    dsimp [x, y, z]
    ring
  rw [hid]
  positivity

theorem Z_less_c_cubed (a b c : ℤ)
    (ha : 1 ≤ a) (hb : 3*a ≤ b) (hc : 10*b^2 ≤ c) :
    0 < -a * b * c + c ^ 3 := by
  let x := a-1
  let y := b-3*a
  let z := c-10*b^2
  have hx : 0 ≤ x := by dsimp [x]; linarith
  have hy : 0 ≤ y := by dsimp [y]; linarith
  have hz : 0 ≤ z := by dsimp [z]; linarith
  have hid : -a * b * c + c ^ 3 = 729000 * x ^ 6 + 1458000 * x ^ 5 * y + 4374000 * x ^ 5 + 1215000 * x ^ 4 * y ^ 2 + 7290000 * x ^ 4 * y + 24300 * x ^ 4 * z + 10934730 * x ^ 4 + 540000 * x ^ 3 * y ^ 3 + 4860000 * x ^ 3 * y ^ 2 + 32400 * x ^ 3 * y * z + 14579730 * x ^ 3 * y + 97200 * x ^ 3 * z + 14578920 * x ^ 3 + 135000 * x ^ 2 * y ^ 4 + 1620000 * x ^ 2 * y ^ 3 + 16200 * x ^ 2 * y ^ 2 * z + 7289910 * x ^ 2 * y ^ 2 + 97200 * x ^ 2 * y * z + 14579190 * x ^ 2 * y + 270 * x ^ 2 * z ^ 2 + 145797 * x ^ 2 * z + 10933380 * x ^ 2 + 18000 * x * y ^ 5 + 270000 * x * y ^ 4 + 3600 * x * y ^ 3 * z + 1619990 * x * y ^ 3 + 32400 * x * y ^ 2 * z + 4859820 * x * y ^ 2 + 180 * x * y * z ^ 2 + 97199 * x * y * z + 7289190 * x * y + 540 * x * z ^ 2 + 97194 * x * z + 4372920 * x + 1000 * y ^ 6 + 18000 * y ^ 5 + 300 * y ^ 4 * z + 135000 * y ^ 4 + 3600 * y ^ 3 * z + 539990 * y ^ 3 + 30 * y ^ 2 * z ^ 2 + 16200 * y ^ 2 * z + 1214910 * y ^ 2 + 180 * y * z ^ 2 + 32399 * y * z + 1457730 * y + z ^ 3 + 270 * z ^ 2 + 24297 * z + 728730 := by
    dsimp [x, y, z]
    ring
  rw [hid]
  positivity

theorem S1_less_2c (a b c : ℤ)
    (ha : 1 ≤ a) (hb : 3*a ≤ b) (hc : 10*b^2 ≤ c) :
    0 < 3 * a - b + c := by
  let x := a-1
  let y := b-3*a
  let z := c-10*b^2
  have hx : 0 ≤ x := by dsimp [x]; linarith
  have hy : 0 ≤ y := by dsimp [y]; linarith
  have hz : 0 ≤ z := by dsimp [z]; linarith
  have hid : 3 * a - b + c = 90 * x ^ 2 + 60 * x * y + 180 * x + 10 * y ^ 2 + 59 * y + z + 90 := by
    dsimp [x, y, z]
    ring
  rw [hid]
  positivity

theorem D_positive (a b c : ℤ)
    (ha : 1 ≤ a) (hb : 3*a ≤ b) (hc : 10*b^2 ≤ c) :
    0 < -a - b + 3 * c := by
  let x := a-1
  let y := b-3*a
  let z := c-10*b^2
  have hx : 0 ≤ x := by dsimp [x]; linarith
  have hy : 0 ≤ y := by dsimp [y]; linarith
  have hz : 0 ≤ z := by dsimp [z]; linarith
  have hid : -a - b + 3 * c = 270 * x ^ 2 + 180 * x * y + 536 * x + 30 * y ^ 2 + 179 * y + 3 * z + 266 := by
    dsimp [x, y, z]
    ring
  rw [hid]
  positivity

theorem D_less_3c (a b c : ℤ)
    (ha : 1 ≤ a) (hb : 3*a ≤ b) (hc : 10*b^2 ≤ c) :
    0 < a + b := by
  let x := a-1
  let y := b-3*a
  let z := c-10*b^2
  have hx : 0 ≤ x := by dsimp [x]; linarith
  have hy : 0 ≤ y := by dsimp [y]; linarith
  have hz : 0 ≤ z := by dsimp [z]; linarith
  have hid : a + b = 4 * x + y + 4 := by
    dsimp [x, y, z]
    ring
  rw [hid]
  positivity

theorem A_positive (a b c : ℤ)
    (ha : 1 ≤ a) (hb : 3*a ≤ b) (hc : 10*b^2 ≤ c) :
    0 < a * (-a + b) * (-a + c) := by
  let x := a-1
  let y := b-3*a
  let z := c-10*b^2
  have hx : 0 ≤ x := by dsimp [x]; linarith
  have hy : 0 ≤ y := by dsimp [y]; linarith
  have hz : 0 ≤ z := by dsimp [z]; linarith
  have hid : a * (-a + b) * (-a + c) = 180 * x ^ 4 + 210 * x ^ 3 * y + 718 * x ^ 3 + 80 * x ^ 2 * y ^ 2 + 629 * x ^ 2 * y + 2 * x ^ 2 * z + 1074 * x ^ 2 + 10 * x * y ^ 3 + 160 * x * y ^ 2 + x * y * z + 628 * x * y + 4 * x * z + 714 * x + 10 * y ^ 3 + 80 * y ^ 2 + y * z + 209 * y + 2 * z + 178 := by
    dsimp [x, y, z]
    ring
  rw [hid]
  positivity

theorem A_less_c_cubed (a b c : ℤ)
    (ha : 1 ≤ a) (hb : 3*a ≤ b) (hc : 10*b^2 ≤ c) :
    0 < -a * (-a + b) * (-a + c) + c ^ 3 := by
  let x := a-1
  let y := b-3*a
  let z := c-10*b^2
  have hx : 0 ≤ x := by dsimp [x]; linarith
  have hy : 0 ≤ y := by dsimp [y]; linarith
  have hz : 0 ≤ z := by dsimp [z]; linarith
  have hid : -a * (-a + b) * (-a + c) + c ^ 3 = 729000 * x ^ 6 + 1458000 * x ^ 5 * y + 4374000 * x ^ 5 + 1215000 * x ^ 4 * y ^ 2 + 7290000 * x ^ 4 * y + 24300 * x ^ 4 * z + 10934820 * x ^ 4 + 540000 * x ^ 3 * y ^ 3 + 4860000 * x ^ 3 * y ^ 2 + 32400 * x ^ 3 * y * z + 14579790 * x ^ 3 * y + 97200 * x ^ 3 * z + 14579282 * x ^ 3 + 135000 * x ^ 2 * y ^ 4 + 1620000 * x ^ 2 * y ^ 3 + 16200 * x ^ 2 * y ^ 2 * z + 7289920 * x ^ 2 * y ^ 2 + 97200 * x ^ 2 * y * z + 14579371 * x ^ 2 * y + 270 * x ^ 2 * z ^ 2 + 145798 * x ^ 2 * z + 10933926 * x ^ 2 + 18000 * x * y ^ 5 + 270000 * x * y ^ 4 + 3600 * x * y ^ 3 * z + 1619990 * x * y ^ 3 + 32400 * x * y ^ 2 * z + 4859840 * x * y ^ 2 + 180 * x * y * z ^ 2 + 97199 * x * y * z + 7289372 * x * y + 540 * x * z ^ 2 + 97196 * x * z + 4373286 * x + 1000 * y ^ 6 + 18000 * y ^ 5 + 300 * y ^ 4 * z + 135000 * y ^ 4 + 3600 * y ^ 3 * z + 539990 * y ^ 3 + 30 * y ^ 2 * z ^ 2 + 16200 * y ^ 2 * z + 1214920 * y ^ 2 + 180 * y * z ^ 2 + 32399 * y * z + 1457791 * y + z ^ 3 + 270 * z ^ 2 + 24298 * z + 728822 := by
    dsimp [x, y, z]
    ring
  rw [hid]
  positivity

theorem C_positive (a b c : ℤ)
    (ha : 1 ≤ a) (hb : 3*a ≤ b) (hc : 10*b^2 ≤ c) :
    0 < b * (-a + b) * (-b + c) := by
  let x := a-1
  let y := b-3*a
  let z := c-10*b^2
  have hx : 0 ≤ x := by dsimp [x]; linarith
  have hy : 0 ≤ y := by dsimp [y]; linarith
  have hz : 0 ≤ z := by dsimp [z]; linarith
  have hid : b * (-a + b) * (-b + c) = 540 * x ^ 4 + 810 * x ^ 3 * y + 2142 * x ^ 3 + 450 * x ^ 2 * y ^ 2 + 2409 * x ^ 2 * y + 6 * x ^ 2 * z + 3186 * x ^ 2 + 110 * x * y ^ 3 + 892 * x * y ^ 2 + 5 * x * y * z + 2388 * x * y + 12 * x * z + 2106 * x + 10 * y ^ 4 + 109 * y ^ 3 + y ^ 2 * z + 442 * y ^ 2 + 5 * y * z + 789 * y + 6 * z + 522 := by
    dsimp [x, y, z]
    ring
  rw [hid]
  positivity

theorem C_less_c_cubed (a b c : ℤ)
    (ha : 1 ≤ a) (hb : 3*a ≤ b) (hc : 10*b^2 ≤ c) :
    0 < -b * (-a + b) * (-b + c) + c ^ 3 := by
  let x := a-1
  let y := b-3*a
  let z := c-10*b^2
  have hx : 0 ≤ x := by dsimp [x]; linarith
  have hy : 0 ≤ y := by dsimp [y]; linarith
  have hz : 0 ≤ z := by dsimp [z]; linarith
  have hid : -b * (-a + b) * (-b + c) + c ^ 3 = 729000 * x ^ 6 + 1458000 * x ^ 5 * y + 4374000 * x ^ 5 + 1215000 * x ^ 4 * y ^ 2 + 7290000 * x ^ 4 * y + 24300 * x ^ 4 * z + 10934460 * x ^ 4 + 540000 * x ^ 3 * y ^ 3 + 4860000 * x ^ 3 * y ^ 2 + 32400 * x ^ 3 * y * z + 14579190 * x ^ 3 * y + 97200 * x ^ 3 * z + 14577858 * x ^ 3 + 135000 * x ^ 2 * y ^ 4 + 1620000 * x ^ 2 * y ^ 3 + 16200 * x ^ 2 * y ^ 2 * z + 7289550 * x ^ 2 * y ^ 2 + 97200 * x ^ 2 * y * z + 14577591 * x ^ 2 * y + 270 * x ^ 2 * z ^ 2 + 145794 * x ^ 2 * z + 10931814 * x ^ 2 + 18000 * x * y ^ 5 + 270000 * x * y ^ 4 + 3600 * x * y ^ 3 * z + 1619890 * x * y ^ 3 + 32400 * x * y ^ 2 * z + 4859108 * x * y ^ 2 + 180 * x * y * z ^ 2 + 97195 * x * y * z + 7287612 * x * y + 540 * x * z ^ 2 + 97188 * x * z + 4371894 * x + 1000 * y ^ 6 + 18000 * y ^ 5 + 300 * y ^ 4 * z + 134990 * y ^ 4 + 3600 * y ^ 3 * z + 539891 * y ^ 3 + 30 * y ^ 2 * z ^ 2 + 16199 * y ^ 2 * z + 1214558 * y ^ 2 + 180 * y * z ^ 2 + 32395 * y * z + 1457211 * y + z ^ 3 + 270 * z ^ 2 + 24294 * z + 728478 := by
    dsimp [x, y, z]
    ring
  rw [hid]
  positivity

theorem F_positive (a b c : ℤ)
    (ha : 1 ≤ a) (hb : 3*a ≤ b) (hc : 10*b^2 ≤ c) :
    0 < c * (-a + c) * (-b + c) := by
  let x := a-1
  let y := b-3*a
  let z := c-10*b^2
  have hx : 0 ≤ x := by dsimp [x]; linarith
  have hy : 0 ≤ y := by dsimp [y]; linarith
  have hz : 0 ≤ z := by dsimp [z]; linarith
  have hid : c * (-a + c) * (-b + c) = 729000 * x ^ 6 + 1458000 * x ^ 5 * y + 4341600 * x ^ 5 + 1215000 * x ^ 4 * y ^ 2 + 7238700 * x ^ 4 * y + 24300 * x ^ 4 * z + 10773270 * x ^ 4 + 540000 * x ^ 3 * y ^ 3 + 4827600 * x ^ 3 * y ^ 2 + 32400 * x ^ 3 * y * z + 14375070 * x ^ 3 * y + 96480 * x ^ 3 * z + 14257080 * x ^ 3 + 135000 * x ^ 2 * y ^ 4 + 1609800 * x ^ 2 * y ^ 3 + 16200 * x ^ 2 * y ^ 2 * z + 7192890 * x ^ 2 * y ^ 2 + 96540 * x ^ 2 * y * z + 14273010 * x ^ 2 * y + 270 * x ^ 2 * z ^ 2 + 143643 * x ^ 2 * z + 10612620 * x ^ 2 + 18000 * x * y ^ 5 + 268400 * x * y ^ 4 + 3600 * x * y ^ 3 * z + 1599610 * x * y ^ 3 + 32200 * x * y ^ 2 * z + 4762980 * x * y ^ 2 + 180 * x * y * z ^ 2 + 95881 * x * y * z + 7085610 * x * y + 536 * x * z ^ 2 + 95046 * x * z + 4213080 * x + 1000 * y ^ 6 + 17900 * y ^ 5 + 300 * y ^ 4 * z + 133400 * y ^ 4 + 3580 * y ^ 3 * z + 529810 * y ^ 3 + 30 * y ^ 2 * z ^ 2 + 16000 * y ^ 2 * z + 1182690 * y ^ 2 + 179 * y * z ^ 2 + 31741 * y * z + 1406970 * y + z ^ 3 + 266 * z ^ 2 + 23583 * z + 696870 := by
    dsimp [x, y, z]
    ring
  rw [hid]
  positivity

theorem F_less_c_cubed (a b c : ℤ)
    (ha : 1 ≤ a) (hb : 3*a ≤ b) (hc : 10*b^2 ≤ c) :
    0 < c ^ 3 - c * (-a + c) * (-b + c) := by
  let x := a-1
  let y := b-3*a
  let z := c-10*b^2
  have hx : 0 ≤ x := by dsimp [x]; linarith
  have hy : 0 ≤ y := by dsimp [y]; linarith
  have hz : 0 ≤ z := by dsimp [z]; linarith
  have hid : c ^ 3 - c * (-a + c) * (-b + c) = 32400 * x ^ 5 + 51300 * x ^ 4 * y + 161730 * x ^ 4 + 32400 * x ^ 3 * y ^ 2 + 204930 * x ^ 3 * y + 720 * x ^ 3 * z + 322920 * x ^ 3 + 10200 * x ^ 2 * y ^ 3 + 97110 * x ^ 2 * y ^ 2 + 660 * x ^ 2 * y * z + 306990 * x ^ 2 * y + 2157 * x ^ 2 * z + 322380 * x ^ 2 + 1600 * x * y ^ 4 + 20390 * x * y ^ 3 + 200 * x * y ^ 2 * z + 97020 * x * y ^ 2 + 1319 * x * y * z + 204390 * x * y + 4 * x * z ^ 2 + 2154 * x * z + 160920 * x + 100 * y ^ 5 + 1600 * y ^ 4 + 20 * y ^ 3 * z + 10190 * y ^ 3 + 200 * y ^ 2 * z + 32310 * y ^ 2 + y * z ^ 2 + 659 * y * z + 51030 * y + 4 * z ^ 2 + 717 * z + 32130 := by
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
