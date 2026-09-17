import SecondOrder
open SecondOrder
example : (1000000 : ℕ).sqrt = 1000 := by decide +kernel
example : (1000000 : ℕ).sqrt.sqrt = 31 := by decide +kernel
example : (100 : ℕ)^3 ≤ 1000000 := by decide +kernel
example : 1000000 < (100+1 : ℕ)^3 := by decide +kernel
#eval IO.println (Lean.Json.compress (Lean.toJson ((List.range 1001).map cubeRoot)))
