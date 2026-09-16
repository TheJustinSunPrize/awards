import Init.Classical

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace JSP000746.RUP

theorem c5292 (p : Nat → Prop)
    (d200 : (p 88) → (p 93) → (p 103) → False)
    (d154 : (¬ p 65) → (¬ p 70) → (¬ p 103) → False)
    : (¬ p 70) → (¬ p 65) → (p 93) → (p 88) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 103 := (fun u => d200 a3 a2 u)
  exact d154 a1 a0 v0

theorem c5293 (p : Nat → Prop)
    (d5027 : (¬ p 93) → (¬ p 76) → (p 103) → (p 77) → False)
    (d154 : (¬ p 65) → (¬ p 70) → (¬ p 103) → False)
    : (¬ p 70) → (¬ p 65) → (¬ p 93) → (¬ p 76) → (p 77) → False := by
  intro a0 a1 a2 a3 a4
  have v0 : ¬ p 103 := (fun u => d5027 a2 a3 u a4)
  exact d154 a1 a0 v0

theorem c5294 (p : Nat → Prop)
    (d5073 : (¬ p 40) → (¬ p 43) → (p 103) → (p 100) → False)
    (d154 : (¬ p 65) → (¬ p 70) → (¬ p 103) → False)
    : (¬ p 70) → (¬ p 65) → (¬ p 40) → (¬ p 43) → (p 100) → False := by
  intro a0 a1 a2 a3 a4
  have v0 : ¬ p 103 := (fun u => d5073 a2 a3 u a4)
  exact d154 a1 a0 v0

theorem c5295 (p : Nat → Prop)
    (d5116 : (¬ p 57) → (¬ p 53) → (p 103) → (p 99) → False)
    (d154 : (¬ p 65) → (¬ p 70) → (¬ p 103) → False)
    : (¬ p 70) → (¬ p 65) → (¬ p 57) → (¬ p 53) → (p 99) → False := by
  intro a0 a1 a2 a3 a4
  have v0 : ¬ p 103 := (fun u => d5116 a2 a3 u a4)
  exact d154 a1 a0 v0

theorem c5296 (p : Nat → Prop)
    (d5196 : (¬ p 30) → (¬ p 28) → (p 105) → (p 103) → False)
    (d154 : (¬ p 65) → (¬ p 70) → (¬ p 103) → False)
    : (¬ p 70) → (¬ p 65) → (¬ p 30) → (¬ p 28) → (p 105) → False := by
  intro a0 a1 a2 a3 a4
  have v0 : ¬ p 103 := (fun u => d5196 a2 a3 a4 u)
  exact d154 a1 a0 v0

theorem c5297 (p : Nat → Prop)
    (d5285 : (¬ p 41) → (¬ p 38) → (¬ p 26) → (¬ p 28) → (p 103) → False)
    (d154 : (¬ p 65) → (¬ p 70) → (¬ p 103) → False)
    : (¬ p 70) → (¬ p 65) → (¬ p 41) → (¬ p 38) → (¬ p 26) → (¬ p 28) → False := by
  intro a0 a1 a2 a3 a4 a5
  have v0 : ¬ p 103 := (fun u => d5285 a2 a3 a4 a5 u)
  exact d154 a1 a0 v0

theorem c5298 (p : Nat → Prop)
    (d7 : (p 99) → (p 100) → (p 109) → False)
    (d394 : (¬ p 8) → (¬ p 9) → (¬ p 109) → False)
    : (¬ p 8) → (¬ p 9) → (p 100) → (p 99) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 109 := (fun u => d7 a3 a2 u)
  exact d394 a0 a1 v0

theorem c5299 (p : Nat → Prop)
    (d140 : (p 24) → (p 25) → (p 109) → False)
    (d394 : (¬ p 8) → (¬ p 9) → (¬ p 109) → False)
    : (¬ p 8) → (¬ p 9) → (p 25) → (p 24) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 109 := (fun u => d140 a3 a2 u)
  exact d394 a0 a1 v0

theorem c5300 (p : Nat → Prop)
    (d252 : (p 53) → (p 54) → (p 109) → False)
    (d394 : (¬ p 8) → (¬ p 9) → (¬ p 109) → False)
    : (¬ p 8) → (¬ p 9) → (p 53) → (p 54) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 109 := (fun u => d252 a2 a3 u)
  exact d394 a0 a1 v0

theorem c5301 (p : Nat → Prop)
    (d539 : (p 39) → (p 40) → (p 109) → False)
    (d394 : (¬ p 8) → (¬ p 9) → (¬ p 109) → False)
    : (¬ p 8) → (¬ p 9) → (p 39) → (p 40) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 109 := (fun u => d539 a2 a3 u)
  exact d394 a0 a1 v0

theorem c5302 (p : Nat → Prop)
    (d327 : (p 89) → (p 90) → (p 109) → False)
    (d394 : (¬ p 8) → (¬ p 9) → (¬ p 109) → False)
    : (¬ p 8) → (¬ p 9) → (p 89) → (p 90) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 109 := (fun u => d327 a2 a3 u)
  exact d394 a0 a1 v0

theorem c5303 (p : Nat → Prop)
    (d328 : (p 66) → (p 67) → (p 109) → False)
    (d394 : (¬ p 8) → (¬ p 9) → (¬ p 109) → False)
    : (¬ p 8) → (¬ p 9) → (p 67) → (p 66) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 109 := (fun u => d328 a3 a2 u)
  exact d394 a0 a1 v0

theorem c5304 (p : Nat → Prop)
    (d334 : (p 78) → (p 79) → (p 109) → False)
    (d394 : (¬ p 8) → (¬ p 9) → (¬ p 109) → False)
    : (¬ p 8) → (¬ p 9) → (p 79) → (p 78) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 109 := (fun u => d334 a3 a2 u)
  exact d394 a0 a1 v0

theorem c5305 (p : Nat → Prop)
    (d4974 : (¬ p 39) → (¬ p 42) → (p 109) → (p 119) → False)
    (d394 : (¬ p 8) → (¬ p 9) → (¬ p 109) → False)
    : (¬ p 8) → (¬ p 9) → (¬ p 39) → (¬ p 42) → (p 119) → False := by
  intro a0 a1 a2 a3 a4
  have v0 : ¬ p 109 := (fun u => d4974 a2 a3 u a4)
  exact d394 a0 a1 v0

theorem c5306 (p : Nat → Prop)
    (d4979 : (¬ p 96) → (¬ p 89) → (p 123) → (p 109) → False)
    (d394 : (¬ p 8) → (¬ p 9) → (¬ p 109) → False)
    : (¬ p 8) → (¬ p 9) → (¬ p 96) → (¬ p 89) → (p 123) → False := by
  intro a0 a1 a2 a3 a4
  have v0 : ¬ p 109 := (fun u => d4979 a2 a3 a4 u)
  exact d394 a0 a1 v0

theorem c5307 (p : Nat → Prop)
    (d5109 : (¬ p 24) → (¬ p 26) → (p 109) → (p 118) → False)
    (d394 : (¬ p 8) → (¬ p 9) → (¬ p 109) → False)
    : (¬ p 8) → (¬ p 9) → (¬ p 24) → (¬ p 26) → (p 118) → False := by
  intro a0 a1 a2 a3 a4
  have v0 : ¬ p 109 := (fun u => d5109 a2 a3 u a4)
  exact d394 a0 a1 v0

theorem c5308 (p : Nat → Prop)
    (d5131 : (¬ p 72) → (¬ p 67) → (p 114) → (p 109) → False)
    (d394 : (¬ p 8) → (¬ p 9) → (¬ p 109) → False)
    : (¬ p 8) → (¬ p 9) → (¬ p 72) → (¬ p 67) → (p 114) → False := by
  intro a0 a1 a2 a3 a4
  have v0 : ¬ p 109 := (fun u => d5131 a2 a3 a4 u)
  exact d394 a0 a1 v0

theorem c5309 (p : Nat → Prop)
    (d143 : (p 9) → (p 11) → (p 119) → False)
    (d49 : (¬ p 25) → (¬ p 27) → (¬ p 119) → False)
    : (¬ p 25) → (¬ p 27) → (p 9) → (p 11) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 119 := (fun u => d143 a2 a3 u)
  exact d49 a0 a1 v0

theorem c5310 (p : Nat → Prop)
    (d578 : (p 67) → (p 69) → (p 119) → False)
    (d49 : (¬ p 25) → (¬ p 27) → (¬ p 119) → False)
    : (¬ p 25) → (¬ p 27) → (p 67) → (p 69) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 119 := (fun u => d578 a2 a3 u)
  exact d49 a0 a1 v0

theorem c5311 (p : Nat → Prop)
    (d310 : (p 79) → (p 81) → (p 119) → False)
    (d49 : (¬ p 25) → (¬ p 27) → (¬ p 119) → False)
    : (¬ p 25) → (¬ p 27) → (p 81) → (p 79) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 119 := (fun u => d310 a3 a2 u)
  exact d49 a0 a1 v0

theorem c5312 (p : Nat → Prop)
    (d289 : (p 118) → (p 119) → (p 126) → False)
    (d49 : (¬ p 25) → (¬ p 27) → (¬ p 119) → False)
    : (¬ p 25) → (¬ p 27) → (p 126) → (p 118) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 119 := (fun u => d289 a3 u a2)
  exact d49 a0 a1 v0

theorem c5313 (p : Nat → Prop)
    (d227 : (p 40) → (p 42) → (p 119) → False)
    (d49 : (¬ p 25) → (¬ p 27) → (¬ p 119) → False)
    : (¬ p 25) → (¬ p 27) → (p 40) → (p 42) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 119 := (fun u => d227 a2 a3 u)
  exact d49 a0 a1 v0

theorem c5314 (p : Nat → Prop)
    (d5045 : (¬ p 64) → (¬ p 69) → (p 119) → (p 90) → False)
    (d49 : (¬ p 25) → (¬ p 27) → (¬ p 119) → False)
    : (¬ p 25) → (¬ p 27) → (¬ p 64) → (¬ p 69) → (p 90) → False := by
  intro a0 a1 a2 a3 a4
  have v0 : ¬ p 119 := (fun u => d5045 a2 a3 u a4)
  exact d49 a0 a1 v0

theorem c5315 (p : Nat → Prop)
    (d5075 : (¬ p 97) → (¬ p 90) → (p 137) → (p 119) → False)
    (d49 : (¬ p 25) → (¬ p 27) → (¬ p 119) → False)
    : (¬ p 25) → (¬ p 27) → (¬ p 97) → (¬ p 90) → (p 137) → False := by
  intro a0 a1 a2 a3 a4
  have v0 : ¬ p 119 := (fun u => d5075 a2 a3 a4 u)
  exact d49 a0 a1 v0

theorem c5316 (p : Nat → Prop)
    (d5137 : (¬ p 72) → (¬ p 67) → (p 119) → (p 135) → False)
    (d49 : (¬ p 25) → (¬ p 27) → (¬ p 119) → False)
    : (¬ p 25) → (¬ p 27) → (¬ p 72) → (¬ p 67) → (p 135) → False := by
  intro a0 a1 a2 a3 a4
  have v0 : ¬ p 119 := (fun u => d5137 a2 a3 u a4)
  exact d49 a0 a1 v0

theorem c5317 (p : Nat → Prop)
    (d5145 : (¬ p 100) → (¬ p 108) → (p 119) → (p 138) → False)
    (d49 : (¬ p 25) → (¬ p 27) → (¬ p 119) → False)
    : (¬ p 25) → (¬ p 27) → (¬ p 100) → (¬ p 108) → (p 138) → False := by
  intro a0 a1 a2 a3 a4
  have v0 : ¬ p 119 := (fun u => d5145 a2 a3 u a4)
  exact d49 a0 a1 v0

theorem c5318 (p : Nat → Prop)
    (d5176 : (¬ p 27) → (¬ p 29) → (¬ p 54) → (¬ p 58) → (p 119) → False)
    (d49 : (¬ p 25) → (¬ p 27) → (¬ p 119) → False)
    : (¬ p 25) → (¬ p 27) → (¬ p 29) → (¬ p 54) → (¬ p 58) → False := by
  intro a0 a1 a2 a3 a4
  have v0 : ¬ p 119 := (fun u => d5176 a1 a2 a3 a4 u)
  exact d49 a0 a1 v0

theorem c5319 (p : Nat → Prop)
    (d5305 : (¬ p 8) → (¬ p 9) → (¬ p 39) → (¬ p 42) → (p 119) → False)
    (d49 : (¬ p 25) → (¬ p 27) → (¬ p 119) → False)
    : (¬ p 25) → (¬ p 27) → (¬ p 8) → (¬ p 9) → (¬ p 39) → (¬ p 42) → False := by
  intro a0 a1 a2 a3 a4 a5
  have v0 : ¬ p 119 := (fun u => d5305 a2 a3 a4 a5 u)
  exact d49 a0 a1 v0

theorem c5320 (p : Nat → Prop)
    (d533 : (p 56) → (p 57) → (p 133) → False)
    (d166 : (¬ p 11) → (¬ p 12) → (¬ p 133) → False)
    : (¬ p 11) → (¬ p 12) → (p 57) → (p 56) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 133 := (fun u => d533 a3 a2 u)
  exact d166 a0 a1 v0

theorem c5321 (p : Nat → Prop)
    (d306 : (p 69) → (p 70) → (p 133) → False)
    (d166 : (¬ p 11) → (¬ p 12) → (¬ p 133) → False)
    : (¬ p 11) → (¬ p 12) → (p 69) → (p 70) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 133 := (fun u => d306 a2 a3 u)
  exact d166 a0 a1 v0

theorem c5322 (p : Nat → Prop)
    (d285 : (p 42) → (p 43) → (p 133) → False)
    (d166 : (¬ p 11) → (¬ p 12) → (¬ p 133) → False)
    : (¬ p 11) → (¬ p 12) → (p 43) → (p 42) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 133 := (fun u => d285 a3 a2 u)
  exact d166 a0 a1 v0

theorem c5323 (p : Nat → Prop)
    (d482 : (p 133) → (p 136) → (p 141) → False)
    (d166 : (¬ p 11) → (¬ p 12) → (¬ p 133) → False)
    : (¬ p 11) → (¬ p 12) → (p 141) → (p 136) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 133 := (fun u => d482 u a3 a2)
  exact d166 a0 a1 v0

theorem c5324 (p : Nat → Prop)
    (d124 : (p 27) → (p 28) → (p 133) → False)
    (d166 : (¬ p 11) → (¬ p 12) → (¬ p 133) → False)
    : (¬ p 11) → (¬ p 12) → (p 27) → (p 28) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 133 := (fun u => d124 a2 a3 u)
  exact d166 a0 a1 v0

theorem c5325 (p : Nat → Prop)
    (d39 : (p 133) → (p 138) → (p 143) → False)
    (d166 : (¬ p 11) → (¬ p 12) → (¬ p 133) → False)
    : (¬ p 11) → (¬ p 12) → (p 143) → (p 138) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 133 := (fun u => d39 u a3 a2)
  exact d166 a0 a1 v0

theorem c5326 (p : Nat → Prop)
    (d5020 : (¬ p 93) → (¬ p 76) → (p 81) → (p 133) → False)
    (d166 : (¬ p 11) → (¬ p 12) → (¬ p 133) → False)
    : (¬ p 11) → (¬ p 12) → (¬ p 93) → (¬ p 76) → (p 81) → False := by
  intro a0 a1 a2 a3 a4
  have v0 : ¬ p 133 := (fun u => d5020 a2 a3 a4 u)
  exact d166 a0 a1 v0

theorem c5327 (p : Nat → Prop)
    (d5151 : (¬ p 26) → (¬ p 28) → (p 133) → (p 126) → False)
    (d166 : (¬ p 11) → (¬ p 12) → (¬ p 133) → False)
    : (¬ p 11) → (¬ p 12) → (¬ p 26) → (¬ p 28) → (p 126) → False := by
  intro a0 a1 a2 a3 a4
  have v0 : ¬ p 133 := (fun u => d5151 a2 a3 u a4)
  exact d166 a0 a1 v0

theorem c5328 (p : Nat → Prop)
    (d5287 : (¬ p 70) → (¬ p 65) → (p 102) → (p 133) → False)
    (d166 : (¬ p 11) → (¬ p 12) → (¬ p 133) → False)
    : (¬ p 11) → (¬ p 12) → (¬ p 70) → (¬ p 65) → (p 102) → False := by
  intro a0 a1 a2 a3 a4
  have v0 : ¬ p 133 := (fun u => d5287 a2 a3 a4 u)
  exact d166 a0 a1 v0

theorem c5329 (p : Nat → Prop)
    (d5117 : (¬ p 57) → (¬ p 53) → (¬ p 39) → (¬ p 42) → (p 133) → False)
    (d166 : (¬ p 11) → (¬ p 12) → (¬ p 133) → False)
    : (¬ p 11) → (¬ p 12) → (¬ p 57) → (¬ p 53) → (¬ p 39) → (¬ p 42) → False := by
  intro a0 a1 a2 a3 a4 a5
  have v0 : ¬ p 133 := (fun u => d5117 a2 a3 a4 a5 u)
  exact d166 a0 a1 v0

theorem c5330 (p : Nat → Prop)
    (d5188 : (¬ p 13) → (¬ p 12) → (¬ p 27) → (¬ p 29) → (p 133) → False)
    (d166 : (¬ p 11) → (¬ p 12) → (¬ p 133) → False)
    : (¬ p 11) → (¬ p 12) → (¬ p 13) → (¬ p 27) → (¬ p 29) → False := by
  intro a0 a1 a2 a3 a4
  have v0 : ¬ p 133 := (fun u => d5188 a2 a1 a3 a4 u)
  exact d166 a0 a1 v0

theorem c5331 (p : Nat → Prop)
    (d193 : (p 11) → (p 14) → (p 135) → False)
    (d417 : (¬ p 42) → (¬ p 45) → (¬ p 135) → False)
    : (¬ p 42) → (¬ p 45) → (p 14) → (p 11) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 135 := (fun u => d193 a3 a2 u)
  exact d417 a0 a1 v0

theorem c5332 (p : Nat → Prop)
    (d345 : (p 126) → (p 129) → (p 135) → False)
    (d417 : (¬ p 42) → (¬ p 45) → (¬ p 135) → False)
    : (¬ p 42) → (¬ p 45) → (p 129) → (p 126) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 135 := (fun u => d345 a3 a2 u)
  exact d417 a0 a1 v0

theorem c5333 (p : Nat → Prop)
    (d176 : (p 69) → (p 72) → (p 135) → False)
    (d417 : (¬ p 42) → (¬ p 45) → (¬ p 135) → False)
    : (¬ p 42) → (¬ p 45) → (p 72) → (p 69) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 135 := (fun u => d176 a3 a2 u)
  exact d417 a0 a1 v0

theorem c5334 (p : Nat → Prop)
    (d579 : (p 102) → (p 105) → (p 135) → False)
    (d417 : (¬ p 42) → (¬ p 45) → (¬ p 135) → False)
    : (¬ p 42) → (¬ p 45) → (p 102) → (p 105) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 135 := (fun u => d579 a2 a3 u)
  exact d417 a0 a1 v0

theorem c5335 (p : Nat → Prop)
    (d183 : (p 135) → (p 138) → (p 150) → False)
    (d417 : (¬ p 42) → (¬ p 45) → (¬ p 135) → False)
    : (¬ p 42) → (¬ p 45) → (p 138) → (p 150) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 135 := (fun u => d183 u a2 a3)
  exact d417 a0 a1 v0

theorem c5336 (p : Nat → Prop)
    (d337 : (p 135) → (p 137) → (p 149) → False)
    (d417 : (¬ p 42) → (¬ p 45) → (¬ p 135) → False)
    : (¬ p 42) → (¬ p 45) → (p 149) → (p 137) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 135 := (fun u => d337 u a3 a2)
  exact d417 a0 a1 v0

theorem c5337 (p : Nat → Prop)
    (d4955 : (¬ p 129) → (¬ p 55) → (p 56) → (p 135) → False)
    (d417 : (¬ p 42) → (¬ p 45) → (¬ p 135) → False)
    : (¬ p 42) → (¬ p 45) → (¬ p 129) → (¬ p 55) → (p 56) → False := by
  intro a0 a1 a2 a3 a4
  have v0 : ¬ p 135 := (fun u => d4955 a2 a3 a4 u)
  exact d417 a0 a1 v0

theorem c5338 (p : Nat → Prop)
    (d5212 : (¬ p 14) → (¬ p 15) → (p 136) → (p 135) → False)
    (d417 : (¬ p 42) → (¬ p 45) → (¬ p 135) → False)
    : (¬ p 42) → (¬ p 45) → (¬ p 14) → (¬ p 15) → (p 136) → False := by
  intro a0 a1 a2 a3 a4
  have v0 : ¬ p 135 := (fun u => d5212 a2 a3 a4 u)
  exact d417 a0 a1 v0

theorem c5339 (p : Nat → Prop)
    (d5260 : (¬ p 114) → (¬ p 78) → (p 81) → (p 135) → False)
    (d417 : (¬ p 42) → (¬ p 45) → (¬ p 135) → False)
    : (¬ p 42) → (¬ p 45) → (¬ p 114) → (¬ p 78) → (p 81) → False := by
  intro a0 a1 a2 a3 a4
  have v0 : ¬ p 135 := (fun u => d5260 a2 a3 a4 u)
  exact d417 a0 a1 v0

theorem c5340 (p : Nat → Prop)
    (d5178 : (¬ p 27) → (¬ p 29) → (¬ p 14) → (¬ p 13) → (p 135) → False)
    (d417 : (¬ p 42) → (¬ p 45) → (¬ p 135) → False)
    : (¬ p 42) → (¬ p 45) → (¬ p 27) → (¬ p 29) → (¬ p 14) → (¬ p 13) → False := by
  intro a0 a1 a2 a3 a4 a5
  have v0 : ¬ p 135 := (fun u => d5178 a2 a3 a4 a5 u)
  exact d417 a0 a1 v0

theorem c5341 (p : Nat → Prop)
    (d5316 : (¬ p 25) → (¬ p 27) → (¬ p 72) → (¬ p 67) → (p 135) → False)
    (d417 : (¬ p 42) → (¬ p 45) → (¬ p 135) → False)
    : (¬ p 42) → (¬ p 45) → (¬ p 25) → (¬ p 27) → (¬ p 72) → (¬ p 67) → False := by
  intro a0 a1 a2 a3 a4 a5
  have v0 : ¬ p 135 := (fun u => d5316 a2 a3 a4 a5 u)
  exact d417 a0 a1 v0

theorem c5342 (p : Nat → Prop)
    (d474 : (p 130) → (p 132) → (p 152) → False)
    (d107 : (¬ p 31) → (¬ p 33) → (¬ p 152) → False)
    : (¬ p 31) → (¬ p 33) → (p 130) → (p 132) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 152 := (fun u => d474 a2 a3 u)
  exact d107 a0 a1 v0

theorem c5343 (p : Nat → Prop)
    (d63 : (p 136) → (p 138) → (p 152) → False)
    (d107 : (¬ p 31) → (¬ p 33) → (¬ p 152) → False)
    : (¬ p 31) → (¬ p 33) → (p 136) → (p 138) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 152 := (fun u => d63 a2 a3 u)
  exact d107 a0 a1 v0

theorem c5344 (p : Nat → Prop)
    (d447 : (p 15) → (p 17) → (p 152) → False)
    (d107 : (¬ p 31) → (¬ p 33) → (¬ p 152) → False)
    : (¬ p 31) → (¬ p 33) → (p 17) → (p 15) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 152 := (fun u => d447 a3 a2 u)
  exact d107 a0 a1 v0

theorem c5346 (p : Nat → Prop)
    (d5035 : (¬ p 123) → (¬ p 79) → (p 152) → (p 87) → False)
    (d107 : (¬ p 31) → (¬ p 33) → (¬ p 152) → False)
    : (¬ p 31) → (¬ p 33) → (¬ p 123) → (¬ p 79) → (p 87) → False := by
  intro a0 a1 a2 a3 a4
  have v0 : ¬ p 152 := (fun u => d5035 a2 a3 u a4)
  exact d107 a0 a1 v0

theorem c5347 (p : Nat → Prop)
    (d5099 : (¬ p 16) → (¬ p 15) → (¬ p 17) → (p 152) → False)
    (d107 : (¬ p 31) → (¬ p 33) → (¬ p 152) → False)
    : (¬ p 31) → (¬ p 33) → (¬ p 16) → (¬ p 15) → (¬ p 17) → False := by
  intro a0 a1 a2 a3 a4
  have v0 : ¬ p 152 := (fun u => d5099 a2 a3 a4 u)
  exact d107 a0 a1 v0

theorem c5348 (p : Nat → Prop)
    (d5211 : (¬ p 14) → (¬ p 15) → (p 152) → (p 150) → False)
    (d107 : (¬ p 31) → (¬ p 33) → (¬ p 152) → False)
    : (¬ p 31) → (¬ p 33) → (¬ p 14) → (¬ p 15) → (p 150) → False := by
  intro a0 a1 a2 a3 a4
  have v0 : ¬ p 152 := (fun u => d5211 a2 a3 u a4)
  exact d107 a0 a1 v0

theorem c5349 (p : Nat → Prop)
    (d5269 : (¬ p 132) → (¬ p 91) → (p 152) → (p 96) → False)
    (d107 : (¬ p 31) → (¬ p 33) → (¬ p 152) → False)
    : (¬ p 31) → (¬ p 33) → (¬ p 132) → (¬ p 91) → (p 96) → False := by
  intro a0 a1 a2 a3 a4
  have v0 : ¬ p 152 := (fun u => d5269 a2 a3 u a4)
  exact d107 a0 a1 v0

theorem c5350 (p : Nat → Prop)
    (d4968 : (¬ p 136) → (¬ p 56) → (¬ p 147) → (¬ p 58) → (p 152) → False)
    (d107 : (¬ p 31) → (¬ p 33) → (¬ p 152) → False)
    : (¬ p 31) → (¬ p 33) → (¬ p 136) → (¬ p 56) → (¬ p 147) → (¬ p 58) → False := by
  intro a0 a1 a2 a3 a4 a5
  have v0 : ¬ p 152 := (fun u => d4968 a2 a3 a4 a5 u)
  exact d107 a0 a1 v0

theorem c5351 (p : Nat → Prop)
    (d5010 : (¬ p 150) → (¬ p 45) → (¬ p 43) → (¬ p 141) → (p 152) → False)
    (d107 : (¬ p 31) → (¬ p 33) → (¬ p 152) → False)
    : (¬ p 31) → (¬ p 33) → (¬ p 150) → (¬ p 45) → (¬ p 43) → (¬ p 141) → False := by
  intro a0 a1 a2 a3 a4 a5
  have v0 : ¬ p 152 := (fun u => d5010 a2 a3 a4 a5 u)
  exact d107 a0 a1 v0

theorem c5352 (p : Nat → Prop)
    (d5250 : (¬ p 130) → (¬ p 68) → (¬ p 143) → (¬ p 70) → (p 152) → False)
    (d107 : (¬ p 31) → (¬ p 33) → (¬ p 152) → False)
    : (¬ p 31) → (¬ p 33) → (¬ p 130) → (¬ p 68) → (¬ p 143) → (¬ p 70) → False := by
  intro a0 a1 a2 a3 a4 a5
  have v0 : ¬ p 152 := (fun u => d5250 a2 a3 a4 a5 u)
  exact d107 a0 a1 v0

theorem c5353 (p : Nat → Prop)
    (d395 : (p 1) → (p 4) → (p 20) → False)
    (d170 : (¬ p 1) → (¬ p 2) → (¬ p 18) → False)
    : (¬ p 2) → (¬ p 18) → (p 4) → (p 20) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 1 := (fun u => d395 u a2 a3)
  exact d170 v0 a0 a1

theorem c5354 (p : Nat → Prop)
    (d258 : (p 1) → (p 9) → (p 25) → False)
    (d170 : (¬ p 1) → (¬ p 2) → (¬ p 18) → False)
    : (¬ p 2) → (¬ p 18) → (p 25) → (p 9) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 1 := (fun u => d258 u a3 a2)
  exact d170 v0 a0 a1

theorem c5355 (p : Nat → Prop)
    (d398 : (p 1) → (p 11) → (p 27) → False)
    (d170 : (¬ p 1) → (¬ p 2) → (¬ p 18) → False)
    : (¬ p 2) → (¬ p 18) → (p 27) → (p 11) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 1 := (fun u => d398 u a3 a2)
  exact d170 v0 a0 a1

theorem c5356 (p : Nat → Prop)
    (d82 : (p 1) → (p 14) → (p 30) → False)
    (d170 : (¬ p 1) → (¬ p 2) → (¬ p 18) → False)
    : (¬ p 2) → (¬ p 18) → (p 14) → (p 30) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 1 := (fun u => d82 u a2 a3)
  exact d170 v0 a0 a1

theorem c5357 (p : Nat → Prop)
    (d191 : (p 1) → (p 12) → (p 28) → False)
    (d170 : (¬ p 1) → (¬ p 2) → (¬ p 18) → False)
    : (¬ p 2) → (¬ p 18) → (p 12) → (p 28) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 1 := (fun u => d191 u a2 a3)
  exact d170 v0 a0 a1

theorem c5358 (p : Nat → Prop)
    (d336 : (p 1) → (p 7) → (p 23) → False)
    (d170 : (¬ p 1) → (¬ p 2) → (¬ p 18) → False)
    : (¬ p 2) → (¬ p 18) → (p 7) → (p 23) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 1 := (fun u => d336 u a2 a3)
  exact d170 v0 a0 a1

theorem c5359 (p : Nat → Prop)
    (d477 : (p 1) → (p 6) → (p 22) → False)
    (d170 : (¬ p 1) → (¬ p 2) → (¬ p 18) → False)
    : (¬ p 2) → (¬ p 18) → (p 6) → (p 22) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 1 := (fun u => d477 u a2 a3)
  exact d170 v0 a0 a1

theorem c5360 (p : Nat → Prop)
    (d365 : (p 1) → (p 10) → (p 26) → False)
    (d170 : (¬ p 1) → (¬ p 2) → (¬ p 18) → False)
    : (¬ p 2) → (¬ p 18) → (p 26) → (p 10) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 1 := (fun u => d365 u a3 a2)
  exact d170 v0 a0 a1

theorem c5361 (p : Nat → Prop)
    (d451 : (p 1) → (p 15) → (p 31) → False)
    (d170 : (¬ p 1) → (¬ p 2) → (¬ p 18) → False)
    : (¬ p 2) → (¬ p 18) → (p 15) → (p 31) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 1 := (fun u => d451 u a2 a3)
  exact d170 v0 a0 a1

theorem c5362 (p : Nat → Prop)
    (d413 : (p 1) → (p 17) → (p 33) → False)
    (d170 : (¬ p 1) → (¬ p 2) → (¬ p 18) → False)
    : (¬ p 2) → (¬ p 18) → (p 17) → (p 33) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 1 := (fun u => d413 u a2 a3)
  exact d170 v0 a0 a1

theorem c5363 (p : Nat → Prop)
    (d4941 : (¬ p 21) → (¬ p 50) → (p 1) → (p 3) → False)
    (d170 : (¬ p 1) → (¬ p 2) → (¬ p 18) → False)
    : (¬ p 2) → (¬ p 18) → (¬ p 21) → (¬ p 50) → (p 3) → False := by
  intro a0 a1 a2 a3 a4
  have v0 : ¬ p 1 := (fun u => d4941 a2 a3 u a4)
  exact d170 v0 a0 a1

theorem c5364 (p : Nat → Prop)
    (d5222 : (¬ p 30) → (¬ p 149) → (p 1) → (p 16) → False)
    (d170 : (¬ p 1) → (¬ p 2) → (¬ p 18) → False)
    : (¬ p 2) → (¬ p 18) → (¬ p 30) → (¬ p 149) → (p 16) → False := by
  intro a0 a1 a2 a3 a4
  have v0 : ¬ p 1 := (fun u => d5222 a2 a3 u a4)
  exact d170 v0 a0 a1

theorem c5365 (p : Nat → Prop)
    (d543 : (p 118) → (p 123) → (p 130) → False)
    (d564 : (¬ p 9) → (¬ p 10) → (¬ p 118) → False)
    : (¬ p 9) → (¬ p 10) → (p 123) → (p 130) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 118 := (fun u => d543 u a2 a3)
  exact d564 a0 a1 v0

theorem c5366 (p : Nat → Prop)
    (d79 : (p 54) → (p 55) → (p 118) → False)
    (d564 : (¬ p 9) → (¬ p 10) → (¬ p 118) → False)
    : (¬ p 9) → (¬ p 10) → (p 54) → (p 55) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 118 := (fun u => d79 a2 a3 u)
  exact d564 a0 a1 v0

theorem c5367 (p : Nat → Prop)
    (d519 : (p 79) → (p 80) → (p 118) → False)
    (d564 : (¬ p 9) → (¬ p 10) → (¬ p 118) → False)
    : (¬ p 9) → (¬ p 10) → (p 79) → (p 80) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 118 := (fun u => d519 a2 a3 u)
  exact d564 a0 a1 v0

theorem c5368 (p : Nat → Prop)
    (d277 : (p 90) → (p 91) → (p 118) → False)
    (d564 : (¬ p 9) → (¬ p 10) → (¬ p 118) → False)
    : (¬ p 9) → (¬ p 10) → (p 91) → (p 90) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 118 := (fun u => d277 a3 a2 u)
  exact d564 a0 a1 v0

theorem c5369 (p : Nat → Prop)
    (d495 : (p 40) → (p 41) → (p 118) → False)
    (d564 : (¬ p 9) → (¬ p 10) → (¬ p 118) → False)
    : (¬ p 9) → (¬ p 10) → (p 41) → (p 40) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 118 := (fun u => d495 a3 a2 u)
  exact d564 a0 a1 v0

theorem c5370 (p : Nat → Prop)
    (d182 : (p 67) → (p 68) → (p 118) → False)
    (d564 : (¬ p 9) → (¬ p 10) → (¬ p 118) → False)
    : (¬ p 9) → (¬ p 10) → (p 67) → (p 68) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 118 := (fun u => d182 a2 a3 u)
  exact d564 a0 a1 v0

theorem c5371 (p : Nat → Prop)
    (d5146 : (¬ p 100) → (¬ p 108) → (p 132) → (p 118) → False)
    (d564 : (¬ p 9) → (¬ p 10) → (¬ p 118) → False)
    : (¬ p 9) → (¬ p 10) → (¬ p 100) → (¬ p 108) → (p 132) → False := by
  intro a0 a1 a2 a3 a4
  have v0 : ¬ p 118 := (fun u => d5146 a2 a3 a4 u)
  exact d564 a0 a1 v0

theorem c5372 (p : Nat → Prop)
    (d5281 : (¬ p 41) → (¬ p 38) → (p 100) → (p 118) → False)
    (d564 : (¬ p 9) → (¬ p 10) → (¬ p 118) → False)
    : (¬ p 9) → (¬ p 10) → (¬ p 41) → (¬ p 38) → (p 100) → False := by
  intro a0 a1 a2 a3 a4
  have v0 : ¬ p 118 := (fun u => d5281 a2 a3 a4 u)
  exact d564 a0 a1 v0

theorem c5373 (p : Nat → Prop)
    (d5312 : (¬ p 25) → (¬ p 27) → (p 126) → (p 118) → False)
    (d564 : (¬ p 9) → (¬ p 10) → (¬ p 118) → False)
    : (¬ p 9) → (¬ p 10) → (¬ p 25) → (¬ p 27) → (p 126) → False := by
  intro a0 a1 a2 a3 a4
  have v0 : ¬ p 118 := (fun u => d5312 a2 a3 a4 u)
  exact d564 a0 a1 v0

theorem c5374 (p : Nat → Prop)
    (d5089 : (¬ p 41) → (¬ p 44) → (¬ p 54) → (¬ p 58) → (p 118) → False)
    (d564 : (¬ p 9) → (¬ p 10) → (¬ p 118) → False)
    : (¬ p 9) → (¬ p 10) → (¬ p 41) → (¬ p 44) → (¬ p 54) → (¬ p 58) → False := by
  intro a0 a1 a2 a3 a4 a5
  have v0 : ¬ p 118 := (fun u => d5089 a2 a3 a4 a5 u)
  exact d564 a0 a1 v0

theorem c5375 (p : Nat → Prop)
    (d5168 : (¬ p 86) → (¬ p 80) → (¬ p 97) → (¬ p 90) → (p 118) → False)
    (d564 : (¬ p 9) → (¬ p 10) → (¬ p 118) → False)
    : (¬ p 9) → (¬ p 10) → (¬ p 86) → (¬ p 80) → (¬ p 97) → (¬ p 90) → False := by
  intro a0 a1 a2 a3 a4 a5
  have v0 : ¬ p 118 := (fun u => d5168 a2 a3 a4 a5 u)
  exact d564 a0 a1 v0

theorem c5376 (p : Nat → Prop)
    (d5307 : (¬ p 8) → (¬ p 9) → (¬ p 24) → (¬ p 26) → (p 118) → False)
    (d564 : (¬ p 9) → (¬ p 10) → (¬ p 118) → False)
    : (¬ p 9) → (¬ p 10) → (¬ p 8) → (¬ p 24) → (¬ p 26) → False := by
  intro a0 a1 a2 a3 a4
  have v0 : ¬ p 118 := (fun u => d5307 a2 a0 a3 a4 u)
  exact d564 a0 a1 v0

theorem c5377 (p : Nat → Prop)
    (d60 : (p 81) → (p 86) → (p 137) → False)
    (d589 : (¬ p 69) → (¬ p 74) → (¬ p 137) → False)
    : (¬ p 74) → (¬ p 69) → (p 81) → (p 86) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 137 := (fun u => d60 a2 a3 u)
  exact d589 a1 a0 v0

theorem c5378 (p : Nat → Prop)
    (d592 : (p 102) → (p 107) → (p 137) → False)
    (d589 : (¬ p 69) → (¬ p 74) → (¬ p 137) → False)
    : (¬ p 74) → (¬ p 69) → (p 107) → (p 102) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 137 := (fun u => d592 a3 a2 u)
  exact d589 a1 a0 v0

theorem c5379 (p : Nat → Prop)
    (d194 : (p 42) → (p 47) → (p 137) → False)
    (d589 : (¬ p 69) → (¬ p 74) → (¬ p 137) → False)
    : (¬ p 74) → (¬ p 69) → (p 47) → (p 42) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 137 := (fun u => d194 a3 a2 u)
  exact d589 a1 a0 v0

theorem c5380 (p : Nat → Prop)
    (d4898 : (¬ p 142) → (¬ p 57) → (p 137) → (p 56) → False)
    (d589 : (¬ p 69) → (¬ p 74) → (¬ p 137) → False)
    : (¬ p 74) → (¬ p 69) → (¬ p 142) → (¬ p 57) → (p 56) → False := by
  intro a0 a1 a2 a3 a4
  have v0 : ¬ p 137 := (fun u => d4898 a2 a3 u a4)
  exact d589 a1 a0 v0

theorem c5381 (p : Nat → Prop)
    (d4932 : (¬ p 17) → (¬ p 16) → (p 137) → (p 138) → False)
    (d589 : (¬ p 69) → (¬ p 74) → (¬ p 137) → False)
    : (¬ p 74) → (¬ p 69) → (¬ p 17) → (¬ p 16) → (p 138) → False := by
  intro a0 a1 a2 a3 a4
  have v0 : ¬ p 137 := (fun u => d4932 a2 a3 u a4)
  exact d589 a1 a0 v0

theorem c5382 (p : Nat → Prop)
    (d5092 : (¬ p 16) → (¬ p 15) → (p 137) → (p 136) → False)
    (d589 : (¬ p 69) → (¬ p 74) → (¬ p 137) → False)
    : (¬ p 74) → (¬ p 69) → (¬ p 16) → (¬ p 15) → (p 136) → False := by
  intro a0 a1 a2 a3 a4
  have v0 : ¬ p 137 := (fun u => d5092 a2 a3 u a4)
  exact d589 a1 a0 v0

theorem c5383 (p : Nat → Prop)
    (d5162 : (¬ p 86) → (¬ p 80) → (p 137) → (p 126) → False)
    (d589 : (¬ p 69) → (¬ p 74) → (¬ p 137) → False)
    : (¬ p 74) → (¬ p 69) → (¬ p 86) → (¬ p 80) → (p 126) → False := by
  intro a0 a1 a2 a3 a4
  have v0 : ¬ p 137 := (fun u => d5162 a2 a3 u a4)
  exact d589 a1 a0 v0

theorem c5384 (p : Nat → Prop)
    (d5221 : (¬ p 30) → (¬ p 149) → (p 137) → (p 27) → False)
    (d589 : (¬ p 69) → (¬ p 74) → (¬ p 137) → False)
    : (¬ p 74) → (¬ p 69) → (¬ p 30) → (¬ p 149) → (p 27) → False := by
  intro a0 a1 a2 a3 a4
  have v0 : ¬ p 137 := (fun u => d5221 a2 a3 u a4)
  exact d589 a1 a0 v0

theorem c5385 (p : Nat → Prop)
    (d5336 : (¬ p 42) → (¬ p 45) → (p 149) → (p 137) → False)
    (d589 : (¬ p 69) → (¬ p 74) → (¬ p 137) → False)
    : (¬ p 74) → (¬ p 69) → (¬ p 42) → (¬ p 45) → (p 149) → False := by
  intro a0 a1 a2 a3 a4
  have v0 : ¬ p 137 := (fun u => d5336 a2 a3 a4 u)
  exact d589 a1 a0 v0

theorem c5386 (p : Nat → Prop)
    (d5127 : (¬ p 107) → (¬ p 99) → (¬ p 39) → (¬ p 42) → (p 137) → False)
    (d589 : (¬ p 69) → (¬ p 74) → (¬ p 137) → False)
    : (¬ p 74) → (¬ p 69) → (¬ p 107) → (¬ p 99) → (¬ p 39) → (¬ p 42) → False := by
  intro a0 a1 a2 a3 a4 a5
  have v0 : ¬ p 137 := (fun u => d5127 a2 a3 a4 a5 u)
  exact d589 a1 a0 v0

theorem c5387 (p : Nat → Prop)
    (d5207 : (¬ p 44) → (¬ p 47) → (¬ p 27) → (¬ p 29) → (p 137) → False)
    (d589 : (¬ p 69) → (¬ p 74) → (¬ p 137) → False)
    : (¬ p 74) → (¬ p 69) → (¬ p 44) → (¬ p 47) → (¬ p 27) → (¬ p 29) → False := by
  intro a0 a1 a2 a3 a4 a5
  have v0 : ¬ p 137 := (fun u => d5207 a2 a3 a4 a5 u)
  exact d589 a1 a0 v0

theorem c5388 (p : Nat → Prop)
    (d5315 : (¬ p 25) → (¬ p 27) → (¬ p 97) → (¬ p 90) → (p 137) → False)
    (d589 : (¬ p 69) → (¬ p 74) → (¬ p 137) → False)
    : (¬ p 74) → (¬ p 69) → (¬ p 25) → (¬ p 27) → (¬ p 97) → (¬ p 90) → False := by
  intro a0 a1 a2 a3 a4 a5
  have v0 : ¬ p 137 := (fun u => d5315 a2 a3 a4 a5 u)
  exact d589 a1 a0 v0

theorem c5389 (p : Nat → Prop)
    (d348 : (p 5) → (p 11) → (p 81) → False)
    (d561 : (¬ p 81) → (¬ p 87) → (¬ p 138) → False)
    : (¬ p 138) → (¬ p 87) → (p 5) → (p 11) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 81 := (fun u => d348 a2 a3 u)
  exact d561 v0 a1 a0

theorem c5390 (p : Nat → Prop)
    (d151 : (p 21) → (p 27) → (p 81) → False)
    (d561 : (¬ p 81) → (¬ p 87) → (¬ p 138) → False)
    : (¬ p 138) → (¬ p 87) → (p 27) → (p 21) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 81 := (fun u => d151 a3 a2 u)
  exact d561 v0 a1 a0

theorem c5391 (p : Nat → Prop)
    (d346 : (p 63) → (p 69) → (p 81) → False)
    (d561 : (¬ p 81) → (¬ p 87) → (¬ p 138) → False)
    : (¬ p 138) → (¬ p 87) → (p 69) → (p 63) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 81 := (fun u => d346 a3 a2 u)
  exact d561 v0 a1 a0

theorem c5392 (p : Nat → Prop)
    (d96 : (p 80) → (p 81) → (p 126) → False)
    (d561 : (¬ p 81) → (¬ p 87) → (¬ p 138) → False)
    : (¬ p 138) → (¬ p 87) → (p 80) → (p 126) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 81 := (fun u => d96 a2 u a3)
  exact d561 v0 a1 a0

theorem c5393 (p : Nat → Prop)
    (d545 : (p 50) → (p 56) → (p 81) → False)
    (d561 : (¬ p 81) → (¬ p 87) → (¬ p 138) → False)
    : (¬ p 138) → (¬ p 87) → (p 50) → (p 56) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 81 := (fun u => d545 a2 a3 u)
  exact d561 v0 a1 a0

theorem c5394 (p : Nat → Prop)
    (d253 : (p 77) → (p 81) → (p 102) → False)
    (d561 : (¬ p 81) → (¬ p 87) → (¬ p 138) → False)
    : (¬ p 138) → (¬ p 87) → (p 77) → (p 102) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 81 := (fun u => d253 a2 u a3)
  exact d561 v0 a1 a0

theorem c5395 (p : Nat → Prop)
    (d5030 : (¬ p 123) → (¬ p 79) → (p 81) → (p 136) → False)
    (d561 : (¬ p 81) → (¬ p 87) → (¬ p 138) → False)
    : (¬ p 138) → (¬ p 87) → (¬ p 123) → (¬ p 79) → (p 136) → False := by
  intro a0 a1 a2 a3 a4
  have v0 : ¬ p 81 := (fun u => d5030 a2 a3 u a4)
  exact d561 v0 a1 a0

theorem c5396 (p : Nat → Prop)
    (d5038 : (¬ p 64) → (¬ p 69) → (p 81) → (p 76) → False)
    (d561 : (¬ p 81) → (¬ p 87) → (¬ p 138) → False)
    : (¬ p 138) → (¬ p 87) → (¬ p 64) → (¬ p 69) → (p 76) → False := by
  intro a0 a1 a2 a3 a4
  have v0 : ¬ p 81 := (fun u => d5038 a2 a3 u a4)
  exact d561 v0 a1 a0

theorem c5397 (p : Nat → Prop)
    (d5238 : (¬ p 78) → (¬ p 39) → (p 81) → (p 42) → False)
    (d561 : (¬ p 81) → (¬ p 87) → (¬ p 138) → False)
    : (¬ p 138) → (¬ p 87) → (¬ p 78) → (¬ p 39) → (p 42) → False := by
  intro a0 a1 a2 a3 a4
  have v0 : ¬ p 81 := (fun u => d5238 a2 a3 u a4)
  exact d561 v0 a1 a0

theorem c5398 (p : Nat → Prop)
    (d5311 : (¬ p 25) → (¬ p 27) → (p 81) → (p 79) → False)
    (d561 : (¬ p 81) → (¬ p 87) → (¬ p 138) → False)
    : (¬ p 138) → (¬ p 87) → (¬ p 25) → (¬ p 27) → (p 79) → False := by
  intro a0 a1 a2 a3 a4
  have v0 : ¬ p 81 := (fun u => d5311 a2 a3 u a4)
  exact d561 v0 a1 a0

theorem c5399 (p : Nat → Prop)
    (d5377 : (¬ p 74) → (¬ p 69) → (p 81) → (p 86) → False)
    (d561 : (¬ p 81) → (¬ p 87) → (¬ p 138) → False)
    : (¬ p 138) → (¬ p 87) → (¬ p 74) → (¬ p 69) → (p 86) → False := by
  intro a0 a1 a2 a3 a4
  have v0 : ¬ p 81 := (fun u => d5377 a2 a3 u a4)
  exact d561 v0 a1 a0

theorem c5400 (p : Nat → Prop)
    (d5326 : (¬ p 11) → (¬ p 12) → (¬ p 93) → (¬ p 76) → (p 81) → False)
    (d561 : (¬ p 81) → (¬ p 87) → (¬ p 138) → False)
    : (¬ p 138) → (¬ p 87) → (¬ p 11) → (¬ p 12) → (¬ p 93) → (¬ p 76) → False := by
  intro a0 a1 a2 a3 a4 a5
  have v0 : ¬ p 81 := (fun u => d5326 a2 a3 a4 a5 u)
  exact d561 v0 a1 a0

theorem c5401 (p : Nat → Prop)
    (d5339 : (¬ p 42) → (¬ p 45) → (¬ p 114) → (¬ p 78) → (p 81) → False)
    (d561 : (¬ p 81) → (¬ p 87) → (¬ p 138) → False)
    : (¬ p 138) → (¬ p 87) → (¬ p 42) → (¬ p 45) → (¬ p 114) → (¬ p 78) → False := by
  intro a0 a1 a2 a3 a4 a5
  have v0 : ¬ p 81 := (fun u => d5339 a2 a3 a4 a5 u)
  exact d561 v0 a1 a0

theorem c5402 (p : Nat → Prop)
    (d66 : (p 68) → (p 69) → (p 126) → False)
    (d53 : (¬ p 10) → (¬ p 11) → (¬ p 126) → False)
    : (¬ p 11) → (¬ p 10) → (p 69) → (p 68) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 126 := (fun u => d66 a3 a2 u)
  exact d53 a1 a0 v0

theorem c5403 (p : Nat → Prop)
    (d588 : (p 26) → (p 27) → (p 126) → False)
    (d53 : (¬ p 10) → (¬ p 11) → (¬ p 126) → False)
    : (¬ p 11) → (¬ p 10) → (p 26) → (p 27) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 126 := (fun u => d588 a2 a3 u)
  exact d53 a1 a0 v0

theorem c5404 (p : Nat → Prop)
    (d382 : (p 126) → (p 130) → (p 136) → False)
    (d53 : (¬ p 10) → (¬ p 11) → (¬ p 126) → False)
    : (¬ p 11) → (¬ p 10) → (p 136) → (p 130) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 126 := (fun u => d382 u a3 a2)
  exact d53 a1 a0 v0

theorem c5405 (p : Nat → Prop)
    (d321 : (p 55) → (p 56) → (p 126) → False)
    (d53 : (¬ p 10) → (¬ p 11) → (¬ p 126) → False)
    : (¬ p 11) → (¬ p 10) → (p 55) → (p 56) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 126 := (fun u => d321 a2 a3 u)
  exact d53 a1 a0 v0

theorem c5406 (p : Nat → Prop)
    (d481 : (p 126) → (p 132) → (p 138) → False)
    (d53 : (¬ p 10) → (¬ p 11) → (¬ p 126) → False)
    : (¬ p 11) → (¬ p 10) → (p 132) → (p 138) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 126 := (fun u => d481 u a2 a3)
  exact d53 a1 a0 v0

theorem c5407 (p : Nat → Prop)
    (d5041 : (¬ p 64) → (¬ p 69) → (p 91) → (p 126) → False)
    (d53 : (¬ p 10) → (¬ p 11) → (¬ p 126) → False)
    : (¬ p 11) → (¬ p 10) → (¬ p 64) → (¬ p 69) → (p 91) → False := by
  intro a0 a1 a2 a3 a4
  have v0 : ¬ p 126 := (fun u => d5041 a2 a3 a4 u)
  exact d53 a1 a0 v0

theorem c5408 (p : Nat → Prop)
    (d5279 : (¬ p 41) → (¬ p 38) → (p 102) → (p 126) → False)
    (d53 : (¬ p 10) → (¬ p 11) → (¬ p 126) → False)
    : (¬ p 11) → (¬ p 10) → (¬ p 41) → (¬ p 38) → (p 102) → False := by
  intro a0 a1 a2 a3 a4
  have v0 : ¬ p 126 := (fun u => d5279 a2 a3 a4 u)
  exact d53 a1 a0 v0

theorem c5409 (p : Nat → Prop)
    (d5332 : (¬ p 42) → (¬ p 45) → (p 129) → (p 126) → False)
    (d53 : (¬ p 10) → (¬ p 11) → (¬ p 126) → False)
    : (¬ p 11) → (¬ p 10) → (¬ p 42) → (¬ p 45) → (p 129) → False := by
  intro a0 a1 a2 a3 a4
  have v0 : ¬ p 126 := (fun u => d5332 a2 a3 a4 u)
  exact d53 a1 a0 v0

theorem c5410 (p : Nat → Prop)
    (d5392 : (¬ p 138) → (¬ p 87) → (p 80) → (p 126) → False)
    (d53 : (¬ p 10) → (¬ p 11) → (¬ p 126) → False)
    : (¬ p 11) → (¬ p 10) → (¬ p 138) → (¬ p 87) → (p 80) → False := by
  intro a0 a1 a2 a3 a4
  have v0 : ¬ p 126 := (fun u => d5392 a2 a3 a4 u)
  exact d53 a1 a0 v0

theorem c5411 (p : Nat → Prop)
    (d5179 : (¬ p 27) → (¬ p 29) → (¬ p 41) → (¬ p 44) → (p 126) → False)
    (d53 : (¬ p 10) → (¬ p 11) → (¬ p 126) → False)
    : (¬ p 11) → (¬ p 10) → (¬ p 27) → (¬ p 29) → (¬ p 41) → (¬ p 44) → False := by
  intro a0 a1 a2 a3 a4 a5
  have v0 : ¬ p 126 := (fun u => d5179 a2 a3 a4 a5 u)
  exact d53 a1 a0 v0

theorem c5412 (p : Nat → Prop)
    (d5327 : (¬ p 11) → (¬ p 12) → (¬ p 26) → (¬ p 28) → (p 126) → False)
    (d53 : (¬ p 10) → (¬ p 11) → (¬ p 126) → False)
    : (¬ p 11) → (¬ p 10) → (¬ p 12) → (¬ p 26) → (¬ p 28) → False := by
  intro a0 a1 a2 a3 a4
  have v0 : ¬ p 126 := (fun u => d5327 a0 a2 a3 a4 u)
  exact d53 a1 a0 v0

theorem c5413 (p : Nat → Prop)
    (d5373 : (¬ p 9) → (¬ p 10) → (¬ p 25) → (¬ p 27) → (p 126) → False)
    (d53 : (¬ p 10) → (¬ p 11) → (¬ p 126) → False)
    : (¬ p 11) → (¬ p 10) → (¬ p 9) → (¬ p 25) → (¬ p 27) → False := by
  intro a0 a1 a2 a3 a4
  have v0 : ¬ p 126 := (fun u => d5373 a2 a1 a3 a4 u)
  exact d53 a1 a0 v0

theorem c5414 (p : Nat → Prop)
    (d5383 : (¬ p 74) → (¬ p 69) → (¬ p 86) → (¬ p 80) → (p 126) → False)
    (d53 : (¬ p 10) → (¬ p 11) → (¬ p 126) → False)
    : (¬ p 11) → (¬ p 10) → (¬ p 74) → (¬ p 69) → (¬ p 86) → (¬ p 80) → False := by
  intro a0 a1 a2 a3 a4 a5
  have v0 : ¬ p 126 := (fun u => d5383 a2 a3 a4 a5 u)
  exact d53 a1 a0 v0

theorem c5415 (p : Nat → Prop)
    (d4648 : (p 100) → (p 40) → (¬ p 10) → (¬ p 38) → (p 7) → False)
    (d541 : (p 38) → (p 40) → (p 100) → False)
    : (p 7) → (p 100) → (p 40) → (¬ p 10) → False := by
  intro a0 a1 a2 a3
  have v0 : p 38 := Classical.byContradiction (fun u => d4648 a1 a2 a3 u a0)
  exact d541 v0 a2 a1

theorem c5416 (p : Nat → Prop)
    (d4681 : (p 99) → (p 78) → (p 65) → (¬ p 80) → (¬ p 38) → (p 35) → False)
    (d414 : (p 35) → (p 38) → (p 65) → False)
    : (p 99) → (p 65) → (p 35) → (p 78) → (¬ p 80) → False := by
  intro a0 a1 a2 a3 a4
  have v0 : p 38 := Classical.byContradiction (fun u => d4681 a0 a3 a1 a4 u a2)
  exact d414 a2 v0 a1

theorem c5417 (p : Nat → Prop)
    (d4688 : (p 99) → (¬ p 89) → (p 4) → (p 3) → (p 5) → (p 88) → False)
    (d95 : (p 88) → (p 89) → (p 99) → False)
    : (p 5) → (p 3) → (p 4) → (p 99) → (p 88) → False := by
  intro a0 a1 a2 a3 a4
  have v0 : p 89 := Classical.byContradiction (fun u => d4688 a3 u a2 a1 a0 a4)
  exact d95 a4 v0 a3

theorem c5418 (p : Nat → Prop)
    (d4721 : (p 78) → (p 5) → (¬ p 18) → (¬ p 79) → (p 49) → (p 89) → (p 34) → (¬ p 38) → False)
    (d874 : (p 79) → (p 5) → (p 78) → False)
    : (p 34) → (p 49) → (p 5) → (p 78) → (p 89) → (¬ p 18) → (¬ p 38) → False := by
  intro a0 a1 a2 a3 a4 a5 a6
  have v0 : p 79 := Classical.byContradiction (fun u => d4721 a3 a2 a5 u a1 a4 a0 a6)
  exact d874 v0 a2 a3

theorem c5422 (p : Nat → Prop)
    (d147 : (p 5) → (p 10) → (p 80) → False)
    (d5191 : (¬ p 30) → (¬ p 28) → (p 143) → (p 150) → False)
    (d5006 : (¬ p 150) → (¬ p 45) → (p 138) → (p 42) → False)
    (d5410 : (¬ p 11) → (¬ p 10) → (¬ p 138) → (¬ p 87) → (p 80) → False)
    (d4131 : (p 87) → (p 76) → (p 80) → False)
    (d5021 : (¬ p 93) → (¬ p 76) → (p 143) → (p 87) → False)
    (d5241 : (¬ p 78) → (¬ p 39) → (¬ p 150) → (¬ p 45) → (p 87) → False)
    (d4557 : (p 77) → (p 78) → (p 5) → False)
    (d75 : (¬ p 21) → (¬ p 23) → (¬ p 77) → False)
    (d222 : (p 20) → (p 23) → (p 65) → False)
    (d5296 : (¬ p 70) → (¬ p 65) → (¬ p 30) → (¬ p 28) → (p 105) → False)
    (d5292 : (¬ p 70) → (¬ p 65) → (p 93) → (p 88) → False)
    (d5198 : (¬ p 30) → (¬ p 28) → (¬ p 105) → (¬ p 88) → (p 93) → False)
    : (p 143) → (¬ p 70) → (¬ p 21) → (¬ p 45) → (¬ p 28) → (¬ p 30) → (p 5) → (¬ p 11) → (p 80) → (p 42) → (¬ p 39) → (p 20) → False := by
  intro a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11
  have v0 : ¬ p 10 := (fun u => d147 a6 u a8)
  have v1 : ¬ p 150 := (fun u => d5191 a5 a4 a0 u)
  have v2 : ¬ p 138 := (fun u => d5006 v1 a3 u a9)
  have v3 : p 87 := Classical.byContradiction (fun u => d5410 a7 v0 v2 u a8)
  have v4 : ¬ p 76 := (fun u => d4131 v3 u a8)
  have v5 : p 93 := Classical.byContradiction (fun u => d5021 u v4 a0 v3)
  have v6 : p 78 := Classical.byContradiction (fun u => d5241 u a10 v1 a3 v3)
  have v7 : ¬ p 77 := (fun u => d4557 u v6 a6)
  have v8 : p 23 := Classical.byContradiction (fun u => d75 a2 u v7)
  have v9 : ¬ p 65 := (fun u => d222 a11 v8 u)
  have v10 : ¬ p 105 := (fun u => d5296 a1 v9 a5 a4 u)
  have v11 : ¬ p 88 := (fun u => d5292 a1 v9 v5 u)
  exact d5198 a5 a4 v10 v11 v5

theorem c5423 (p : Nat → Prop)
    (d5247 : (¬ p 130) → (¬ p 68) → (p 20) → (p 31) → False)
    (d5422 : (p 143) → (¬ p 70) → (¬ p 21) → (¬ p 45) → (¬ p 28) → (¬ p 30) → (p 5) → (¬ p 11) → (p 80) → (p 42) → (¬ p 39) → (p 20) → False)
    (d5352 : (¬ p 31) → (¬ p 33) → (¬ p 130) → (¬ p 68) → (¬ p 143) → (¬ p 70) → False)
    (d5017 : (¬ p 143) → (¬ p 70) → (p 20) → (p 33) → False)
    : (¬ p 70) → (¬ p 21) → (¬ p 45) → (¬ p 28) → (¬ p 30) → (¬ p 130) → (p 5) → (¬ p 11) → (p 80) → (¬ p 68) → (p 42) → (¬ p 39) → (p 20) → False := by
  intro a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12
  have v0 : ¬ p 31 := (fun u => d5247 a5 a9 a12 u)
  have v1 : ¬ p 143 := (fun u => d5422 u a0 a1 a2 a3 a4 a6 a7 a8 a10 a11 a12)
  have v2 : p 33 := Classical.byContradiction (fun u => d5352 v0 u a5 a9 v1 a0)
  exact d5017 v1 a0 a12 v2

theorem c5424 (p : Nat → Prop)
    (d245 : (p 3) → (p 5) → (p 50) → False)
    (d329 : (p 3) → (p 12) → (p 57) → False)
    (d1154 : (p 3) → (p 8) → (p 12) → False)
    (d235 : (¬ p 50) → (¬ p 54) → (¬ p 79) → False)
    (d5299 : (¬ p 8) → (¬ p 9) → (p 25) → (p 24) → False)
    (d797 : (p 54) → (p 53) → (p 3) → False)
    (d400 : (¬ p 22) → (¬ p 24) → (¬ p 89) → False)
    (d5113 : (¬ p 57) → (¬ p 53) → (p 93) → (p 89) → False)
    : (p 3) → (p 93) → (p 12) → (p 25) → (¬ p 79) → (p 5) → (¬ p 9) → (¬ p 22) → False := by
  intro a0 a1 a2 a3 a4 a5 a6 a7
  have v0 : ¬ p 50 := (fun u => d245 a0 a5 u)
  have v1 : ¬ p 57 := (fun u => d329 a0 a2 u)
  have v2 : ¬ p 8 := (fun u => d1154 a0 u a2)
  have v3 : p 54 := Classical.byContradiction (fun u => d235 v0 u a4)
  have v4 : ¬ p 24 := (fun u => d5299 v2 a6 a3 u)
  have v5 : ¬ p 53 := (fun u => d797 v3 u a0)
  have v6 : p 89 := Classical.byContradiction (fun u => d400 a7 v4 u)
  exact d5113 v1 v5 a1 v6

theorem c5425 (p : Nat → Prop)
    (d5243 : (¬ p 130) → (¬ p 68) → (p 136) → (p 69) → False)
    (d266 : (p 49) → (p 56) → (p 69) → False)
    (d5249 : (¬ p 130) → (¬ p 68) → (¬ p 136) → (¬ p 56) → (p 49) → False)
    : (p 49) → (¬ p 130) → (¬ p 68) → (p 69) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 136 := (fun u => d5243 a1 a2 u a3)
  have v1 : ¬ p 56 := (fun u => d266 a0 u a3)
  exact d5249 a1 a2 v0 v1 a0

theorem c5426 (p : Nat → Prop)
    (d4146 : (p 43) → (p 2) → (p 42) → False)
    (d5322 : (¬ p 11) → (¬ p 12) → (p 43) → (p 42) → False)
    (d4003 : (p 20) → (p 37) → (¬ p 68) → (p 21) → (¬ p 2) → False)
    (d5423 : (¬ p 70) → (¬ p 21) → (¬ p 45) → (¬ p 28) → (¬ p 30) → (¬ p 130) → (p 5) → (¬ p 11) → (p 80) → (¬ p 68) → (p 42) → (¬ p 39) → (p 20) → False)
    (d329 : (p 3) → (p 12) → (p 57) → False)
    (d5115 : (¬ p 57) → (¬ p 53) → (p 66) → (p 70) → False)
    : (p 43) → (¬ p 45) → (p 66) → (¬ p 53) → (p 3) → (¬ p 28) → (¬ p 30) → (¬ p 130) → (p 5) → (¬ p 11) → (p 80) → (¬ p 68) → (p 42) → (¬ p 39) → (p 37) → (p 20) → False := by
  intro a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15
  have v0 : ¬ p 2 := (fun u => d4146 a0 u a12)
  have v1 : p 12 := Classical.byContradiction (fun u => d5322 a9 u a0 a12)
  have v2 : ¬ p 21 := (fun u => d4003 a15 a14 a11 u v0)
  have v3 : p 70 := Classical.byContradiction (fun u => d5423 u v2 a1 a5 a6 a7 a8 a9 a10 a11 a12 a13 a15)
  have v4 : ¬ p 57 := (fun u => d329 a4 v1 u)
  exact d5115 v4 a3 a2 v3

theorem c5427 (p : Nat → Prop)
    (d2347 : (p 37) → (p 89) → (p 76) → False)
    (d797 : (p 54) → (p 53) → (p 3) → False)
    (d844 : (p 40) → (p 18) → (p 42) → False)
    (d668 : (p 18) → (p 39) → (p 37) → False)
    (d5426 : (p 43) → (¬ p 45) → (p 66) → (¬ p 53) → (p 3) → (¬ p 28) → (¬ p 30) → (¬ p 130) → (p 5) → (¬ p 11) → (p 80) → (¬ p 68) → (p 42) → (¬ p 39) → (p 37) → (p 20) → False)
    (d5072 : (¬ p 40) → (¬ p 43) → (p 57) → (p 54) → False)
    (d5115 : (¬ p 57) → (¬ p 53) → (p 66) → (p 70) → False)
    (d5113 : (¬ p 57) → (¬ p 53) → (p 93) → (p 89) → False)
    (d5423 : (¬ p 70) → (¬ p 21) → (¬ p 45) → (¬ p 28) → (¬ p 30) → (¬ p 130) → (p 5) → (¬ p 11) → (p 80) → (¬ p 68) → (p 42) → (¬ p 39) → (p 20) → False)
    (d5119 : (¬ p 57) → (¬ p 53) → (¬ p 93) → (¬ p 76) → (p 78) → False)
    (d5234 : (¬ p 78) → (¬ p 39) → (p 21) → (p 18) → False)
    : (¬ p 45) → (p 89) → (p 66) → (p 3) → (p 54) → (¬ p 28) → (¬ p 30) → (¬ p 130) → (p 5) → (¬ p 11) → (p 80) → (¬ p 68) → (p 42) → (p 37) → (p 20) → (p 18) → False := by
  intro a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15
  have v0 : ¬ p 76 := (fun u => d2347 a13 a1 u)
  have v1 : ¬ p 53 := (fun u => d797 a4 u a3)
  have v2 : ¬ p 40 := (fun u => d844 u a15 a12)
  have v3 : ¬ p 39 := (fun u => d668 a15 u a13)
  have v4 : ¬ p 43 := (fun u => d5426 u a0 a2 v1 a3 a5 a6 a7 a8 a9 a10 a11 a12 v3 a13 a14)
  have v5 : ¬ p 57 := (fun u => d5072 v2 v4 u a4)
  have v6 : ¬ p 70 := (fun u => d5115 v5 v1 a2 u)
  have v7 : ¬ p 93 := (fun u => d5113 v5 v1 u a1)
  have v8 : p 21 := Classical.byContradiction (fun u => d5423 v6 u a0 a5 a6 a7 a8 a9 a10 a11 a12 v3 a14)
  have v9 : ¬ p 78 := (fun u => d5119 v5 v1 v7 v0 u)
  exact d5234 v9 v3 v8 a15

theorem c5428 (p : Nat → Prop)
    (d5042 : (¬ p 64) → (¬ p 69) → (p 37) → (p 42) → False)
    (d5425 : (p 49) → (¬ p 130) → (¬ p 68) → (p 69) → False)
    (d74 : (¬ p 63) → (¬ p 68) → (¬ p 80) → False)
    (d4609 : (p 67) → (p 69) → (p 20) → False)
    (d844 : (p 40) → (p 18) → (p 42) → False)
    (d668 : (p 18) → (p 39) → (p 37) → False)
    (d55 : (p 18) → (p 22) → (p 37) → False)
    (d2776 : (¬ p 4) → (¬ p 49) → (p 80) → (¬ p 63) → (¬ p 54) → False)
    (d549 : (¬ p 3) → (¬ p 4) → (¬ p 49) → False)
    (d797 : (p 54) → (p 53) → (p 3) → False)
    (d3147 : (¬ p 49) → (¬ p 66) → (¬ p 4) → (p 54) → False)
    (d1572 : (¬ p 22) → (p 66) → (¬ p 64) → (¬ p 89) → False)
    (d2347 : (p 37) → (p 89) → (p 76) → False)
    (d5427 : (¬ p 45) → (p 89) → (p 66) → (p 3) → (p 54) → (¬ p 28) → (¬ p 30) → (¬ p 130) → (p 5) → (¬ p 11) → (p 80) → (¬ p 68) → (p 42) → (p 37) → (p 20) → (p 18) → False)
    (d3721 : (p 43) → (p 18) → (p 45) → False)
    (d5200 : (¬ p 30) → (¬ p 28) → (¬ p 72) → (¬ p 67) → (¬ p 40) → (¬ p 43) → False)
    (d5072 : (¬ p 40) → (¬ p 43) → (p 57) → (p 54) → False)
    (d247 : (p 66) → (p 72) → (p 114) → False)
    (d5113 : (¬ p 57) → (¬ p 53) → (p 93) → (p 89) → False)
    (d5263 : (¬ p 114) → (¬ p 78) → (¬ p 39) → (p 45) → False)
    (d5119 : (¬ p 57) → (¬ p 53) → (¬ p 93) → (¬ p 76) → (p 78) → False)
    : (¬ p 4) → (¬ p 28) → (¬ p 30) → (¬ p 130) → (p 5) → (¬ p 11) → (¬ p 63) → (¬ p 68) → (¬ p 64) → (p 42) → (p 37) → (p 20) → (p 18) → False := by
  intro a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12
  have v0 : p 69 := Classical.byContradiction (fun u => d5042 a8 u a10 a9)
  have v1 : ¬ p 49 := (fun u => d5425 u a3 a7 v0)
  have v2 : p 80 := Classical.byContradiction (fun u => d74 a6 a7 u)
  have v3 : ¬ p 67 := (fun u => d4609 u v0 a11)
  have v4 : ¬ p 40 := (fun u => d844 u a12 a9)
  have v5 : ¬ p 39 := (fun u => d668 a12 u a10)
  have v6 : ¬ p 22 := (fun u => d55 a12 u a10)
  have v7 : p 54 := Classical.byContradiction (fun u => d2776 a0 v1 v2 a6 u)
  have v8 : p 3 := Classical.byContradiction (fun u => d549 u a0 v1)
  have v9 : ¬ p 53 := (fun u => d797 v7 u v8)
  have v10 : p 66 := Classical.byContradiction (fun u => d3147 v1 u a0 v7)
  have v11 : p 89 := Classical.byContradiction (fun u => d1572 v6 v10 a8 u)
  have v12 : ¬ p 76 := (fun u => d2347 a10 v11 u)
  have v13 : p 45 := Classical.byContradiction (fun u => d5427 u v11 v10 v8 v7 a1 a2 a3 a4 a5 v2 a7 a9 a10 a11 a12)
  have v14 : ¬ p 43 := (fun u => d3721 u a12 v13)
  have v15 : p 72 := Classical.byContradiction (fun u => d5200 a2 a1 u v3 v4 v14)
  have v16 : ¬ p 57 := (fun u => d5072 v4 v14 u v7)
  have v17 : ¬ p 114 := (fun u => d247 v10 v15 u)
  have v18 : ¬ p 93 := (fun u => d5113 v16 v9 u v11)
  have v19 : p 78 := Classical.byContradiction (fun u => d5263 v17 u v5 v13)
  exact d5119 v16 v9 v18 v12 v19

theorem c5429 (p : Nat → Prop)
    (d59 : (p 4) → (p 14) → (p 72) → False)
    (d5253 : (¬ p 130) → (¬ p 68) → (¬ p 14) → (¬ p 15) → (p 72) → False)
    : (p 72) → (¬ p 15) → (p 4) → (¬ p 130) → (¬ p 68) → False := by
  intro a0 a1 a2 a3 a4
  have v0 : ¬ p 14 := (fun u => d59 a2 u a0)
  exact d5253 a3 a4 v0 a1 a0

theorem c5430 (p : Nat → Prop)
    (d74 : (¬ p 63) → (¬ p 68) → (¬ p 80) → False)
    (d5042 : (¬ p 64) → (¬ p 69) → (p 37) → (p 42) → False)
    (d4609 : (p 67) → (p 69) → (p 20) → False)
    (d582 : (p 18) → (p 27) → (p 42) → False)
    (d844 : (p 40) → (p 18) → (p 42) → False)
    (d668 : (p 18) → (p 39) → (p 37) → False)
    (d147 : (p 5) → (p 10) → (p 80) → False)
    (d755 : (p 80) → (p 130) → (¬ p 9) → (p 5) → False)
    (d5413 : (¬ p 11) → (¬ p 10) → (¬ p 9) → (¬ p 25) → (¬ p 27) → False)
    (d638 : (p 25) → (p 20) → (p 30) → False)
    (d3714 : (p 28) → (p 25) → (p 18) → False)
    (d5428 : (¬ p 4) → (¬ p 28) → (¬ p 30) → (¬ p 130) → (p 5) → (¬ p 11) → (¬ p 63) → (¬ p 68) → (¬ p 64) → (p 42) → (p 37) → (p 20) → (p 18) → False)
    (d4611 : (p 70) → (p 4) → (p 69) → False)
    (d4212 : (p 15) → (¬ p 9) → (p 4) → (p 80) → (¬ p 68) → False)
    (d5429 : (p 72) → (¬ p 15) → (p 4) → (¬ p 130) → (¬ p 68) → False)
    (d5200 : (¬ p 30) → (¬ p 28) → (¬ p 72) → (¬ p 67) → (¬ p 40) → (¬ p 43) → False)
    (d3721 : (p 43) → (p 18) → (p 45) → False)
    (d4146 : (p 43) → (p 2) → (p 42) → False)
    (d5423 : (¬ p 70) → (¬ p 21) → (¬ p 45) → (¬ p 28) → (¬ p 30) → (¬ p 130) → (p 5) → (¬ p 11) → (p 80) → (¬ p 68) → (p 42) → (¬ p 39) → (p 20) → False)
    (d4003 : (p 20) → (p 37) → (¬ p 68) → (p 21) → (¬ p 2) → False)
    : (p 5) → (¬ p 9) → (¬ p 11) → (¬ p 63) → (¬ p 68) → (¬ p 64) → (p 42) → (p 37) → (p 20) → (p 18) → False := by
  intro a0 a1 a2 a3 a4 a5 a6 a7 a8 a9
  have v0 : p 80 := Classical.byContradiction (fun u => d74 a3 a4 u)
  have v1 : p 69 := Classical.byContradiction (fun u => d5042 a5 u a7 a6)
  have v2 : ¬ p 67 := (fun u => d4609 u v1 a8)
  have v3 : ¬ p 27 := (fun u => d582 a9 u a6)
  have v4 : ¬ p 40 := (fun u => d844 u a9 a6)
  have v5 : ¬ p 39 := (fun u => d668 a9 u a7)
  have v6 : ¬ p 10 := (fun u => d147 a0 u v0)
  have v7 : ¬ p 130 := (fun u => d755 v0 u a1 a0)
  have v8 : p 25 := Classical.byContradiction (fun u => d5413 a2 v6 a1 u v3)
  have v9 : ¬ p 30 := (fun u => d638 v8 a8 u)
  have v10 : ¬ p 28 := (fun u => d3714 u v8 a9)
  have v11 : p 4 := Classical.byContradiction (fun u => d5428 u v10 v9 v7 a0 a2 a3 a4 a5 a6 a7 a8 a9)
  have v12 : ¬ p 70 := (fun u => d4611 u v11 v1)
  have v13 : ¬ p 15 := (fun u => d4212 u a1 v11 v0 a4)
  have v14 : ¬ p 72 := (fun u => d5429 u v13 v11 v7 a4)
  have v15 : p 43 := Classical.byContradiction (fun u => d5200 v9 v10 v14 v2 v4 u)
  have v16 : ¬ p 45 := (fun u => d3721 v15 a9 u)
  have v17 : ¬ p 2 := (fun u => d4146 v15 u a6)
  have v18 : p 21 := Classical.byContradiction (fun u => d5423 v12 u v16 v10 v9 v7 a0 a2 v0 a4 a6 v5 a8)
  exact d4003 a8 a7 a4 v18 v17

theorem c5431 (p : Nat → Prop)
    (d5219 : (¬ p 14) → (¬ p 15) → (¬ p 72) → (¬ p 67) → (p 123) → False)
    (d4556 : (p 12) → (p 4) → (p 7) → False)
    (d4354 : (p 8) → (¬ p 49) → (p 3) → (p 4) → False)
    (d329 : (p 3) → (p 12) → (p 57) → False)
    (d5308 : (¬ p 8) → (¬ p 9) → (¬ p 72) → (¬ p 67) → (p 114) → False)
    (d111 : (¬ p 7) → (¬ p 8) → (¬ p 99) → False)
    (d5264 : (¬ p 114) → (¬ p 78) → (¬ p 14) → (¬ p 15) → (¬ p 123) → (¬ p 79) → False)
    (d3671 : (¬ p 53) → (p 99) → (¬ p 57) → (¬ p 49) → False)
    (d5300 : (¬ p 8) → (¬ p 9) → (p 53) → (p 54) → False)
    (d250 : (p 50) → (p 53) → (p 78) → False)
    (d235 : (¬ p 50) → (¬ p 54) → (¬ p 79) → False)
    : (p 3) → (¬ p 79) → (¬ p 14) → (p 12) → (¬ p 72) → (¬ p 49) → (¬ p 15) → (p 4) → (¬ p 9) → (¬ p 67) → False := by
  intro a0 a1 a2 a3 a4 a5 a6 a7 a8 a9
  have v0 : ¬ p 123 := (fun u => d5219 a2 a6 a4 a9 u)
  have v1 : ¬ p 7 := (fun u => d4556 a3 a7 u)
  have v2 : ¬ p 8 := (fun u => d4354 u a5 a0 a7)
  have v3 : ¬ p 57 := (fun u => d329 a0 a3 u)
  have v4 : ¬ p 114 := (fun u => d5308 v2 a8 a4 a9 u)
  have v5 : p 99 := Classical.byContradiction (fun u => d111 v1 v2 u)
  have v6 : p 78 := Classical.byContradiction (fun u => d5264 v4 u a2 a6 v0 a1)
  have v7 : p 53 := Classical.byContradiction (fun u => d3671 u v5 v3 a5)
  have v8 : ¬ p 54 := (fun u => d5300 v2 a8 v7 u)
  have v9 : ¬ p 50 := (fun u => d250 u v7 v6)
  exact d235 v9 v8 a1

theorem c5432 (p : Nat → Prop)
    (d5219 : (¬ p 14) → (¬ p 15) → (¬ p 72) → (¬ p 67) → (p 123) → False)
    (d5431 : (p 3) → (¬ p 79) → (¬ p 14) → (p 12) → (¬ p 72) → (¬ p 49) → (¬ p 15) → (p 4) → (¬ p 9) → (¬ p 67) → False)
    (d505 : (¬ p 2) → (¬ p 3) → (¬ p 34) → False)
    (d502 : (p 34) → (p 42) → (p 56) → False)
    (d4940 : (¬ p 21) → (¬ p 50) → (p 34) → (p 18) → False)
    (d5036 : (¬ p 123) → (¬ p 79) → (¬ p 136) → (¬ p 56) → (p 50) → False)
    : (¬ p 79) → (¬ p 14) → (¬ p 21) → (p 12) → (¬ p 2) → (¬ p 72) → (¬ p 49) → (¬ p 136) → (¬ p 15) → (p 4) → (¬ p 9) → (¬ p 67) → (p 42) → (p 18) → False := by
  intro a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13
  have v0 : ¬ p 123 := (fun u => d5219 a1 a8 a5 a11 u)
  have v1 : ¬ p 3 := (fun u => d5431 u a0 a1 a3 a5 a6 a8 a9 a10 a11)
  have v2 : p 34 := Classical.byContradiction (fun u => d505 a4 v1 u)
  have v3 : ¬ p 56 := (fun u => d502 v2 a12 u)
  have v4 : p 50 := Classical.byContradiction (fun u => d4940 a2 u v2 a13)
  exact d5036 v0 a0 a7 v3 v4

theorem c5433 (p : Nat → Prop)
    (d505 : (¬ p 2) → (¬ p 3) → (¬ p 34) → False)
    (d4940 : (¬ p 21) → (¬ p 50) → (p 34) → (p 18) → False)
    (d2710 : (p 53) → (p 50) → (p 34) → False)
    (d5236 : (¬ p 78) → (¬ p 39) → (p 50) → (p 34) → False)
    (d3743 : (¬ p 49) → (¬ p 3) → (¬ p 53) → (p 8) → False)
    (d5304 : (¬ p 8) → (¬ p 9) → (p 79) → (p 78) → False)
    : (¬ p 3) → (p 79) → (¬ p 21) → (¬ p 2) → (¬ p 49) → (¬ p 9) → (¬ p 39) → (p 18) → False := by
  intro a0 a1 a2 a3 a4 a5 a6 a7
  have v0 : p 34 := Classical.byContradiction (fun u => d505 a3 a0 u)
  have v1 : p 50 := Classical.byContradiction (fun u => d4940 a2 u v0 a7)
  have v2 : ¬ p 53 := (fun u => d2710 u v1 v0)
  have v3 : p 78 := Classical.byContradiction (fun u => d5236 u a6 v1 v0)
  have v4 : ¬ p 8 := (fun u => d3743 a4 a0 v2 u)
  exact d5304 v4 a5 a1 v3

theorem c5434 (p : Nat → Prop)
    (d5367 : (¬ p 9) → (¬ p 10) → (p 79) → (p 80) → False)
    (d5433 : (¬ p 3) → (p 79) → (¬ p 21) → (¬ p 2) → (¬ p 49) → (¬ p 9) → (¬ p 39) → (p 18) → False)
    (d798 : (p 6) → (p 10) → (p 3) → False)
    (d4354 : (p 8) → (¬ p 49) → (p 3) → (p 4) → False)
    (d4016 : (¬ p 6) → (p 99) → (¬ p 7) → (¬ p 5) → (p 3) → False)
    (d111 : (¬ p 7) → (¬ p 8) → (¬ p 99) → False)
    : (p 79) → (¬ p 7) → (¬ p 21) → (¬ p 2) → (¬ p 49) → (p 4) → (¬ p 5) → (¬ p 9) → (p 80) → (¬ p 39) → (p 18) → False := by
  intro a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10
  have v0 : p 10 := Classical.byContradiction (fun u => d5367 a7 u a0 a8)
  have v1 : p 3 := Classical.byContradiction (fun u => d5433 u a0 a2 a3 a4 a7 a9 a10)
  have v2 : ¬ p 6 := (fun u => d798 u v0 v1)
  have v3 : ¬ p 8 := (fun u => d4354 u a4 v1 a5)
  have v4 : ¬ p 99 := (fun u => d4016 v2 u a1 a6 v1)
  exact d111 a1 v3 v4

theorem c5435 (p : Nat → Prop)
    (d51 : (p 3) → (p 10) → (p 55) → False)
    (d4886 : (¬ p 51) → (¬ p 63) → (p 10) → (p 4) → (p 3) → False)
    (d4960 : (¬ p 129) → (¬ p 55) → (¬ p 21) → (¬ p 50) → (p 30) → False)
    (d822 : (p 50) → (p 51) → (p 3) → False)
    : (p 3) → (¬ p 129) → (p 10) → (p 30) → (¬ p 21) → (p 4) → (¬ p 63) → False := by
  intro a0 a1 a2 a3 a4 a5 a6
  have v0 : ¬ p 55 := (fun u => d51 a0 a2 u)
  have v1 : p 51 := Classical.byContradiction (fun u => d4886 u a6 a2 a5 a0)
  have v2 : p 50 := Classical.byContradiction (fun u => d4960 a1 v0 a4 u a3)
  exact d822 v2 v1 a0

theorem c5436 (p : Nat → Prop)
    (d74 : (¬ p 63) → (¬ p 68) → (¬ p 80) → False)
    (d20 : (¬ p 4) → (¬ p 5) → (¬ p 63) → False)
    (d4212 : (p 15) → (¬ p 9) → (p 4) → (p 80) → (¬ p 68) → False)
    (d582 : (p 18) → (p 27) → (p 42) → False)
    (d668 : (p 18) → (p 39) → (p 37) → False)
    (d4146 : (p 43) → (p 2) → (p 42) → False)
    (d5322 : (¬ p 11) → (¬ p 12) → (p 43) → (p 42) → False)
    (d242 : (p 18) → (p 28) → (p 43) → False)
    (d4003 : (p 20) → (p 37) → (¬ p 68) → (p 21) → (¬ p 2) → False)
    (d4556 : (p 12) → (p 4) → (p 7) → False)
    (d5434 : (p 79) → (¬ p 7) → (¬ p 21) → (¬ p 2) → (¬ p 49) → (p 4) → (¬ p 5) → (¬ p 9) → (p 80) → (¬ p 39) → (p 18) → False)
    (d5432 : (¬ p 79) → (¬ p 14) → (¬ p 21) → (p 12) → (¬ p 2) → (¬ p 72) → (¬ p 49) → (¬ p 136) → (¬ p 15) → (p 4) → (¬ p 9) → (¬ p 67) → (p 42) → (p 18) → False)
    (d5194 : (¬ p 30) → (¬ p 28) → (p 12) → (p 14) → False)
    (d5135 : (¬ p 72) → (¬ p 67) → (p 30) → (p 25) → False)
    (d5413 : (¬ p 11) → (¬ p 10) → (¬ p 9) → (¬ p 25) → (¬ p 27) → False)
    (d115 : (p 10) → (p 14) → (p 129) → False)
    (d5435 : (p 3) → (¬ p 129) → (p 10) → (p 30) → (¬ p 21) → (p 4) → (¬ p 63) → False)
    (d505 : (¬ p 2) → (¬ p 3) → (¬ p 34) → False)
    (d52 : (p 34) → (p 43) → (p 57) → False)
    (d4940 : (¬ p 21) → (¬ p 50) → (p 34) → (p 18) → False)
    (d2710 : (p 53) → (p 50) → (p 34) → False)
    (d3743 : (¬ p 49) → (¬ p 3) → (¬ p 53) → (p 8) → False)
    (d3671 : (¬ p 53) → (p 99) → (¬ p 57) → (¬ p 49) → False)
    (d111 : (¬ p 7) → (¬ p 8) → (¬ p 99) → False)
    : (p 43) → (¬ p 72) → (¬ p 49) → (¬ p 136) → (¬ p 5) → (¬ p 9) → (¬ p 11) → (¬ p 63) → (¬ p 68) → (¬ p 67) → (p 42) → (p 37) → (p 20) → (p 18) → False := by
  intro a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13
  have v0 : p 80 := Classical.byContradiction (fun u => d74 a7 a8 u)
  have v1 : p 4 := Classical.byContradiction (fun u => d20 u a4 a7)
  have v2 : ¬ p 15 := (fun u => d4212 u a5 v1 v0 a8)
  have v3 : ¬ p 27 := (fun u => d582 a13 u a10)
  have v4 : ¬ p 39 := (fun u => d668 a13 u a11)
  have v5 : ¬ p 2 := (fun u => d4146 a0 u a10)
  have v6 : p 12 := Classical.byContradiction (fun u => d5322 a6 u a0 a10)
  have v7 : ¬ p 28 := (fun u => d242 a13 u a0)
  have v8 : ¬ p 21 := (fun u => d4003 a12 a11 a8 u v5)
  have v9 : ¬ p 7 := (fun u => d4556 v6 v1 u)
  have v10 : ¬ p 79 := (fun u => d5434 u v9 v8 v5 a2 v1 a4 a5 v0 v4 a13)
  have v11 : p 14 := Classical.byContradiction (fun u => d5432 v10 u v8 v6 v5 a1 a2 a3 v2 v1 a5 a9 a10 a13)
  have v12 : p 30 := Classical.byContradiction (fun u => d5194 u v7 v6 v11)
  have v13 : ¬ p 25 := (fun u => d5135 a1 a9 v12 u)
  have v14 : p 10 := Classical.byContradiction (fun u => d5413 a6 u a5 v13 v3)
  have v15 : ¬ p 129 := (fun u => d115 v14 v11 u)
  have v16 : ¬ p 3 := (fun u => d5435 u v15 v14 v12 v8 v1 a7)
  have v17 : p 34 := Classical.byContradiction (fun u => d505 v5 v16 u)
  have v18 : ¬ p 57 := (fun u => d52 v17 a0 u)
  have v19 : p 50 := Classical.byContradiction (fun u => d4940 v8 u v17 a13)
  have v20 : ¬ p 53 := (fun u => d2710 u v19 v17)
  have v21 : ¬ p 8 := (fun u => d3743 a2 v16 v20 u)
  have v22 : ¬ p 99 := (fun u => d3671 v20 u v18 a2)
  exact d111 v9 v21 v22

theorem c5437 (p : Nat → Prop)
    (d4940 : (¬ p 21) → (¬ p 50) → (p 34) → (p 18) → False)
    (d1134 : (p 34) → (p 38) → (p 42) → False)
    (d2710 : (p 53) → (p 50) → (p 34) → False)
    (d259 : (¬ p 35) → (¬ p 38) → (¬ p 65) → False)
    (d3743 : (¬ p 49) → (¬ p 3) → (¬ p 53) → (p 8) → False)
    (d273 : (¬ p 49) → (¬ p 53) → (¬ p 66) → False)
    (d111 : (¬ p 7) → (¬ p 8) → (¬ p 99) → False)
    (d435 : (p 65) → (p 66) → (p 99) → False)
    : (p 34) → (¬ p 21) → (¬ p 7) → (¬ p 3) → (¬ p 49) → (¬ p 35) → (p 42) → (p 18) → False := by
  intro a0 a1 a2 a3 a4 a5 a6 a7
  have v0 : p 50 := Classical.byContradiction (fun u => d4940 a1 u a0 a7)
  have v1 : ¬ p 38 := (fun u => d1134 a0 u a6)
  have v2 : ¬ p 53 := (fun u => d2710 u v0 a0)
  have v3 : p 65 := Classical.byContradiction (fun u => d259 a5 v1 u)
  have v4 : ¬ p 8 := (fun u => d3743 a4 a3 v2 u)
  have v5 : p 66 := Classical.byContradiction (fun u => d273 a4 v2 u)
  have v6 : p 99 := Classical.byContradiction (fun u => d111 a2 v4 u)
  exact d435 v3 v5 v6

theorem c5438 (p : Nat → Prop)
    (d2715 : (p 37) → (p 42) → (p 35) → False)
    (d668 : (p 18) → (p 39) → (p 37) → False)
    (d55 : (p 18) → (p 22) → (p 37) → False)
    (d5437 : (p 34) → (¬ p 21) → (¬ p 7) → (¬ p 3) → (¬ p 49) → (¬ p 35) → (p 42) → (p 18) → False)
    (d505 : (¬ p 2) → (¬ p 3) → (¬ p 34) → False)
    (d452 : (p 2) → (p 6) → (p 37) → False)
    (d3838 : (p 37) → (¬ p 5) → (¬ p 39) → (¬ p 21) → (¬ p 24) → (¬ p 7) → (p 2) → False)
    (d213 : (¬ p 5) → (¬ p 6) → (¬ p 76) → False)
    (d1418 : (p 66) → (¬ p 22) → (p 20) → (¬ p 7) → (p 4) → (¬ p 6) → False)
    (d4135 : (¬ p 8) → (p 24) → (¬ p 9) → (¬ p 7) → False)
    (d5232 : (¬ p 78) → (¬ p 39) → (p 37) → (p 76) → False)
    (d273 : (¬ p 49) → (¬ p 53) → (¬ p 66) → False)
    (d2960 : (p 78) → (p 53) → (¬ p 7) → (¬ p 6) → (p 8) → False)
    : (¬ p 21) → (¬ p 7) → (¬ p 3) → (¬ p 49) → (p 4) → (¬ p 5) → (¬ p 9) → (p 42) → (p 37) → (p 20) → (p 18) → False := by
  intro a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10
  have v0 : ¬ p 35 := (fun u => d2715 a8 a7 u)
  have v1 : ¬ p 39 := (fun u => d668 a10 u a8)
  have v2 : ¬ p 22 := (fun u => d55 a10 u a8)
  have v3 : ¬ p 34 := (fun u => d5437 u a0 a1 a2 a3 v0 a7 a10)
  have v4 : p 2 := Classical.byContradiction (fun u => d505 u a2 v3)
  have v5 : ¬ p 6 := (fun u => d452 v4 u a8)
  have v6 : p 24 := Classical.byContradiction (fun u => d3838 a8 a5 v1 a0 u a1 v4)
  have v7 : p 76 := Classical.byContradiction (fun u => d213 a5 v5 u)
  have v8 : ¬ p 66 := (fun u => d1418 u v2 a9 a1 a4 v5)
  have v9 : p 8 := Classical.byContradiction (fun u => d4135 u v6 a6 a1)
  have v10 : p 78 := Classical.byContradiction (fun u => d5232 u v1 a8 v7)
  have v11 : p 53 := Classical.byContradiction (fun u => d273 a3 u v8)
  exact d2960 v10 v11 a1 v5 v9

theorem c5439 (p : Nat → Prop)
    (d4536 : (p 78) → (p 80) → (p 21) → False)
    (d5234 : (¬ p 78) → (¬ p 39) → (p 21) → (p 18) → False)
    : (p 21) → (p 80) → (¬ p 39) → (p 18) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 78 := (fun u => d4536 u a1 a0)
  exact d5234 v0 a2 a0 a3

theorem c5440 (p : Nat → Prop)
    (d1215 : (p 4) → (p 2) → (p 7) → False)
    (d418 : (p 4) → (p 7) → (p 65) → False)
    (d505 : (¬ p 2) → (¬ p 3) → (¬ p 34) → False)
    (d259 : (¬ p 35) → (¬ p 38) → (¬ p 65) → False)
    (d1134 : (p 34) → (p 38) → (p 42) → False)
    : (p 7) → (¬ p 3) → (p 4) → (¬ p 35) → (p 42) → False := by
  intro a0 a1 a2 a3 a4
  have v0 : ¬ p 2 := (fun u => d1215 a2 u a0)
  have v1 : ¬ p 65 := (fun u => d418 a2 a0 u)
  have v2 : p 34 := Classical.byContradiction (fun u => d505 v0 a1 u)
  have v3 : p 38 := Classical.byContradiction (fun u => d259 a3 u v1)
  exact d1134 v2 v3 a4

theorem c5441 (p : Nat → Prop)
    (d5016 : (¬ p 143) → (¬ p 70) → (p 138) → (p 69) → False)
    (d5325 : (¬ p 11) → (¬ p 12) → (p 143) → (p 138) → False)
    : (p 138) → (¬ p 12) → (¬ p 70) → (¬ p 11) → (p 69) → False := by
  intro a0 a1 a2 a3 a4
  have v0 : p 143 := Classical.byContradiction (fun u => d5016 u a2 a0 a4)
  exact d5325 a3 a1 v0 a0

theorem c5442 (p : Nat → Prop)
    (d582 : (p 18) → (p 27) → (p 42) → False)
    (d844 : (p 40) → (p 18) → (p 42) → False)
    (d5322 : (¬ p 11) → (¬ p 12) → (p 43) → (p 42) → False)
    (d5330 : (¬ p 11) → (¬ p 12) → (¬ p 13) → (¬ p 27) → (¬ p 29) → False)
    (d5441 : (p 138) → (¬ p 12) → (¬ p 70) → (¬ p 11) → (p 69) → False)
    (d5394 : (¬ p 138) → (¬ p 87) → (p 77) → (p 102) → False)
    (d4571 : (p 77) → (p 87) → (p 79) → False)
    (d5029 : (¬ p 123) → (¬ p 79) → (p 80) → (p 130) → False)
    (d5066 : (¬ p 40) → (¬ p 43) → (p 141) → (p 123) → False)
    (d5365 : (¬ p 9) → (¬ p 10) → (p 123) → (p 130) → False)
    (d4995 : (¬ p 43) → (¬ p 141) → (p 41) → (p 130) → False)
    (d4996 : (¬ p 43) → (¬ p 141) → (p 18) → (p 31) → False)
    (d4617 : (p 91) → (p 10) → (p 80) → False)
    (d5085 : (¬ p 41) → (¬ p 44) → (p 13) → (p 10) → False)
    (d4643 : (p 87) → (¬ p 91) → (p 143) → (p 80) → False)
    (d209 : (p 34) → (p 44) → (p 58) → False)
    (d5017 : (¬ p 143) → (¬ p 70) → (p 20) → (p 33) → False)
    (d3753 : (¬ p 31) → (¬ p 58) → (¬ p 56) → (¬ p 27) → (¬ p 29) → (¬ p 33) → False)
    : (¬ p 12) → (¬ p 29) → (p 77) → (p 102) → (p 34) → (p 130) → (¬ p 56) → (¬ p 70) → (¬ p 9) → (¬ p 11) → (p 80) → (p 69) → (p 42) → (p 20) → (p 18) → False := by
  intro a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14
  have v0 : ¬ p 27 := (fun u => d582 a14 u a12)
  have v1 : ¬ p 40 := (fun u => d844 u a14 a12)
  have v2 : ¬ p 43 := (fun u => d5322 a9 a0 u a12)
  have v3 : p 13 := Classical.byContradiction (fun u => d5330 a9 a0 u v0 a1)
  have v4 : ¬ p 138 := (fun u => d5441 u a0 a7 a9 a11)
  have v5 : p 87 := Classical.byContradiction (fun u => d5394 v4 u a2 a3)
  have v6 : ¬ p 79 := (fun u => d4571 a2 v5 u)
  have v7 : p 123 := Classical.byContradiction (fun u => d5029 u v6 a10 a5)
  have v8 : ¬ p 141 := (fun u => d5066 v1 v2 u v7)
  have v9 : p 10 := Classical.byContradiction (fun u => d5365 a8 u v7 a5)
  have v10 : ¬ p 41 := (fun u => d4995 v2 v8 u a5)
  have v11 : ¬ p 31 := (fun u => d4996 v2 v8 a14 u)
  have v12 : ¬ p 91 := (fun u => d4617 u v9 a10)
  have v13 : p 44 := Classical.byContradiction (fun u => d5085 v10 u v3 v9)
  have v14 : ¬ p 143 := (fun u => d4643 v5 v12 u a10)
  have v15 : ¬ p 58 := (fun u => d209 a4 v13 u)
  have v16 : ¬ p 33 := (fun u => d5017 v14 a7 a13 u)
  exact d3753 v11 v15 a6 v0 a1 v16

theorem c5443 (p : Nat → Prop)
    (d5066 : (¬ p 40) → (¬ p 43) → (p 141) → (p 123) → False)
    (d5365 : (¬ p 9) → (¬ p 10) → (p 123) → (p 130) → False)
    (d4993 : (¬ p 43) → (¬ p 141) → (p 136) → (p 42) → False)
    (d4617 : (p 91) → (p 10) → (p 80) → False)
    (d4961 : (¬ p 136) → (¬ p 56) → (p 55) → (p 130) → False)
    (d444 : (¬ p 51) → (¬ p 55) → (¬ p 91) → False)
    : (p 123) → (¬ p 43) → (¬ p 51) → (p 130) → (¬ p 56) → (¬ p 9) → (p 80) → (¬ p 40) → (p 42) → False := by
  intro a0 a1 a2 a3 a4 a5 a6 a7 a8
  have v0 : ¬ p 141 := (fun u => d5066 a7 a1 u a0)
  have v1 : p 10 := Classical.byContradiction (fun u => d5365 a5 u a0 a3)
  have v2 : ¬ p 136 := (fun u => d4993 a1 v0 u a8)
  have v3 : ¬ p 91 := (fun u => d4617 u v1 a6)
  have v4 : ¬ p 55 := (fun u => d4961 v2 a4 u a3)
  exact d444 a2 v4 v3

theorem c5444 (p : Nat → Prop)
    (d266 : (p 49) → (p 56) → (p 69) → False)
    (d668 : (p 18) → (p 39) → (p 37) → False)
    (d5439 : (p 21) → (p 80) → (¬ p 39) → (p 18) → False)
    (d844 : (p 40) → (p 18) → (p 42) → False)
    (d55 : (p 18) → (p 22) → (p 37) → False)
    (d2047 : (p 34) → (p 42) → (¬ p 65) → (p 49) → False)
    (d4940 : (¬ p 21) → (¬ p 50) → (p 34) → (p 18) → False)
    (d222 : (p 20) → (p 23) → (p 65) → False)
    (d4949 : (¬ p 102) → (¬ p 56) → (p 65) → (p 49) → False)
    (d2710 : (p 53) → (p 50) → (p 34) → False)
    (d5236 : (¬ p 78) → (¬ p 39) → (p 50) → (p 34) → False)
    (d75 : (¬ p 21) → (¬ p 23) → (¬ p 77) → False)
    (d572 : (p 77) → (p 78) → (p 99) → False)
    (d3692 : (p 77) → (p 108) → (p 102) → False)
    (d111 : (¬ p 7) → (¬ p 8) → (¬ p 99) → False)
    (d4096 : (¬ p 7) → (p 89) → (p 78) → (¬ p 99) → False)
    (d400 : (¬ p 22) → (¬ p 24) → (¬ p 89) → False)
    (d4169 : (p 24) → (p 20) → (p 29) → False)
    (d5442 : (¬ p 12) → (¬ p 29) → (p 77) → (p 102) → (p 34) → (p 130) → (¬ p 56) → (¬ p 70) → (¬ p 9) → (¬ p 11) → (p 80) → (p 69) → (p 42) → (p 20) → (p 18) → False)
    (d5112 : (¬ p 57) → (¬ p 53) → (p 12) → (p 8) → False)
    (d3347 : (p 57) → (p 51) → (p 50) → False)
    (d52 : (p 34) → (p 43) → (p 57) → False)
    (d5443 : (p 123) → (¬ p 43) → (¬ p 51) → (p 130) → (¬ p 56) → (¬ p 9) → (p 80) → (¬ p 40) → (p 42) → False)
    (d5029 : (¬ p 123) → (¬ p 79) → (p 80) → (p 130) → False)
    (d4571 : (p 77) → (p 87) → (p 79) → False)
    (d264 : (p 77) → (p 79) → (p 100) → False)
    (d5394 : (¬ p 138) → (¬ p 87) → (p 77) → (p 102) → False)
    (d5149 : (¬ p 100) → (¬ p 108) → (¬ p 40) → (¬ p 43) → (p 143) → False)
    (d5016 : (¬ p 143) → (¬ p 70) → (p 138) → (p 69) → False)
    : (p 34) → (p 130) → (p 49) → (¬ p 7) → (¬ p 70) → (¬ p 9) → (¬ p 11) → (p 80) → (p 69) → (p 42) → (p 37) → (p 20) → (p 18) → False := by
  intro a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12
  have v0 : ¬ p 56 := (fun u => d266 a2 u a8)
  have v1 : ¬ p 39 := (fun u => d668 a12 u a10)
  have v2 : ¬ p 21 := (fun u => d5439 u a7 v1 a12)
  have v3 : ¬ p 40 := (fun u => d844 u a12 a9)
  have v4 : ¬ p 22 := (fun u => d55 a12 u a10)
  have v5 : p 65 := Classical.byContradiction (fun u => d2047 a0 a9 u a2)
  have v6 : p 50 := Classical.byContradiction (fun u => d4940 v2 u a0 a12)
  have v7 : ¬ p 23 := (fun u => d222 a11 u v5)
  have v8 : p 102 := Classical.byContradiction (fun u => d4949 u v0 v5 a2)
  have v9 : ¬ p 53 := (fun u => d2710 u v6 a0)
  have v10 : p 78 := Classical.byContradiction (fun u => d5236 u v1 v6 a0)
  have v11 : p 77 := Classical.byContradiction (fun u => d75 v2 v7 u)
  have v12 : ¬ p 99 := (fun u => d572 v11 v10 u)
  have v13 : ¬ p 108 := (fun u => d3692 v11 u v8)
  have v14 : p 8 := Classical.byContradiction (fun u => d111 a3 u v12)
  have v15 : ¬ p 89 := (fun u => d4096 a3 u v10 v12)
  have v16 : p 24 := Classical.byContradiction (fun u => d400 v4 u v15)
  have v17 : ¬ p 29 := (fun u => d4169 v16 a11 u)
  have v18 : p 12 := Classical.byContradiction (fun u => d5442 u v17 v11 v8 a0 a1 v0 a4 a5 a6 a7 a8 a9 a11 a12)
  have v19 : p 57 := Classical.byContradiction (fun u => d5112 u v9 v18 v14)
  have v20 : ¬ p 51 := (fun u => d3347 v19 u v6)
  have v21 : ¬ p 43 := (fun u => d52 a0 u v19)
  have v22 : ¬ p 123 := (fun u => d5443 u v21 v20 a1 v0 a5 a7 v3 a9)
  have v23 : p 79 := Classical.byContradiction (fun u => d5029 v22 u a7 a1)
  have v24 : ¬ p 87 := (fun u => d4571 v11 u v23)
  have v25 : ¬ p 100 := (fun u => d264 v11 v23 u)
  have v26 : p 138 := Classical.byContradiction (fun u => d5394 u v24 v11 v8)
  have v27 : ¬ p 143 := (fun u => d5149 v25 v13 v3 v21 u)
  exact d5016 v27 a4 v26 a8

theorem c5445 (p : Nat → Prop)
    (d4611 : (p 70) → (p 4) → (p 69) → False)
    (d668 : (p 18) → (p 39) → (p 37) → False)
    (d5439 : (p 21) → (p 80) → (¬ p 39) → (p 18) → False)
    (d582 : (p 18) → (p 27) → (p 42) → False)
    (d2715 : (p 37) → (p 42) → (p 35) → False)
    (d5440 : (p 7) → (¬ p 3) → (p 4) → (¬ p 35) → (p 42) → False)
    (d5438 : (¬ p 21) → (¬ p 7) → (¬ p 3) → (¬ p 49) → (p 4) → (¬ p 5) → (¬ p 9) → (p 42) → (p 37) → (p 20) → (p 18) → False)
    (d266 : (p 49) → (p 56) → (p 69) → False)
    (d5425 : (p 49) → (¬ p 130) → (¬ p 68) → (p 69) → False)
    (d5444 : (p 34) → (p 130) → (p 49) → (¬ p 7) → (¬ p 70) → (¬ p 9) → (¬ p 11) → (p 80) → (p 69) → (p 42) → (p 37) → (p 20) → (p 18) → False)
    (d505 : (¬ p 2) → (¬ p 3) → (¬ p 34) → False)
    (d452 : (p 2) → (p 6) → (p 37) → False)
    (d4146 : (p 43) → (p 2) → (p 42) → False)
    (d3838 : (p 37) → (¬ p 5) → (¬ p 39) → (¬ p 21) → (¬ p 24) → (¬ p 7) → (p 2) → False)
    (d213 : (¬ p 5) → (¬ p 6) → (¬ p 76) → False)
    (d207 : (¬ p 6) → (¬ p 7) → (¬ p 88) → False)
    (d4169 : (p 24) → (p 20) → (p 29) → False)
    (d275 : (p 76) → (p 80) → (p 91) → False)
    (d5232 : (¬ p 78) → (¬ p 39) → (p 37) → (p 76) → False)
    (d3595 : (p 20) → (p 65) → (p 78) → (¬ p 6) → (¬ p 5) → (p 2) → (p 24) → False)
    (d3501 : (p 42) → (p 102) → (p 37) → (¬ p 65) → False)
    (d4946 : (¬ p 102) → (¬ p 56) → (p 51) → (p 88) → False)
    (d444 : (¬ p 51) → (¬ p 55) → (¬ p 91) → False)
    (d4961 : (¬ p 136) → (¬ p 56) → (p 55) → (p 130) → False)
    (d1049 : (¬ p 29) → (¬ p 27) → (p 136) → (¬ p 31) → False)
    (d4993 : (¬ p 43) → (¬ p 141) → (p 136) → (p 42) → False)
    (d631 : (p 130) → (p 31) → (p 141) → False)
    : (¬ p 3) → (p 4) → (¬ p 5) → (¬ p 9) → (¬ p 11) → (p 80) → (¬ p 68) → (p 69) → (p 42) → (p 37) → (p 20) → (p 18) → False := by
  intro a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11
  have v0 : ¬ p 70 := (fun u => d4611 u a1 a7)
  have v1 : ¬ p 39 := (fun u => d668 a11 u a9)
  have v2 : ¬ p 21 := (fun u => d5439 u a5 v1 a11)
  have v3 : ¬ p 27 := (fun u => d582 a11 u a8)
  have v4 : ¬ p 35 := (fun u => d2715 a9 a8 u)
  have v5 : ¬ p 7 := (fun u => d5440 u a0 a1 v4 a8)
  have v6 : p 49 := Classical.byContradiction (fun u => d5438 v2 v5 a0 u a1 a2 a3 a8 a9 a10 a11)
  have v7 : ¬ p 56 := (fun u => d266 v6 u a7)
  have v8 : p 130 := Classical.byContradiction (fun u => d5425 v6 u a6 a7)
  have v9 : ¬ p 34 := (fun u => d5444 u v8 v6 v5 v0 a3 a4 a5 a7 a8 a9 a10 a11)
  have v10 : p 2 := Classical.byContradiction (fun u => d505 u a0 v9)
  have v11 : ¬ p 6 := (fun u => d452 v10 u a9)
  have v12 : ¬ p 43 := (fun u => d4146 u v10 a8)
  have v13 : p 24 := Classical.byContradiction (fun u => d3838 a9 a2 v1 v2 u v5 v10)
  have v14 : p 76 := Classical.byContradiction (fun u => d213 a2 v11 u)
  have v15 : p 88 := Classical.byContradiction (fun u => d207 v11 v5 u)
  have v16 : ¬ p 29 := (fun u => d4169 v13 a10 u)
  have v17 : ¬ p 91 := (fun u => d275 v14 a5 u)
  have v18 : p 78 := Classical.byContradiction (fun u => d5232 u v1 a9 v14)
  have v19 : ¬ p 65 := (fun u => d3595 a10 u v18 v11 a2 v10 v13)
  have v20 : ¬ p 102 := (fun u => d3501 a8 u a9 v19)
  have v21 : ¬ p 51 := (fun u => d4946 v20 v7 u v15)
  have v22 : p 55 := Classical.byContradiction (fun u => d444 v21 u v17)
  have v23 : p 136 := Classical.byContradiction (fun u => d4961 u v7 v22 v8)
  have v24 : p 31 := Classical.byContradiction (fun u => d1049 v16 v3 v23 u)
  have v25 : p 141 := Classical.byContradiction (fun u => d4993 v12 u v23 a8)
  exact d631 v8 v24 v25

theorem c5446 (p : Nat → Prop)
    (d4886 : (¬ p 51) → (¬ p 63) → (p 10) → (p 4) → (p 3) → False)
    (d5443 : (p 123) → (¬ p 43) → (¬ p 51) → (p 130) → (¬ p 56) → (¬ p 9) → (p 80) → (¬ p 40) → (p 42) → False)
    (d5367 : (¬ p 9) → (¬ p 10) → (p 79) → (p 80) → False)
    (d5029 : (¬ p 123) → (¬ p 79) → (p 80) → (p 130) → False)
    : (¬ p 51) → (¬ p 43) → (p 130) → (¬ p 56) → (p 3) → (p 4) → (¬ p 9) → (p 80) → (¬ p 63) → (¬ p 40) → (p 42) → False := by
  intro a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10
  have v0 : ¬ p 10 := (fun u => d4886 a0 a8 u a5 a4)
  have v1 : ¬ p 123 := (fun u => d5443 u a1 a0 a2 a3 a6 a7 a9 a10)
  have v2 : ¬ p 79 := (fun u => d5367 a6 v0 u a7)
  exact d5029 v1 v2 a7 a2

theorem c5447 (p : Nat → Prop)
    (d55 : (p 18) → (p 22) → (p 37) → False)
    (d400 : (¬ p 22) → (¬ p 24) → (¬ p 89) → False)
    (d4169 : (p 24) → (p 20) → (p 29) → False)
    (d582 : (p 18) → (p 27) → (p 42) → False)
    (d844 : (p 40) → (p 18) → (p 42) → False)
    (d5029 : (¬ p 123) → (¬ p 79) → (p 80) → (p 130) → False)
    (d235 : (¬ p 50) → (¬ p 54) → (¬ p 79) → False)
    (d5066 : (¬ p 40) → (¬ p 43) → (p 141) → (p 123) → False)
    (d5072 : (¬ p 40) → (¬ p 43) → (p 57) → (p 54) → False)
    (d4996 : (¬ p 43) → (¬ p 141) → (p 18) → (p 31) → False)
    (d5000 : (¬ p 43) → (¬ p 141) → (p 96) → (p 37) → False)
    (d5111 : (¬ p 57) → (¬ p 53) → (p 28) → (p 24) → False)
    (d5306 : (¬ p 8) → (¬ p 9) → (¬ p 96) → (¬ p 89) → (p 123) → False)
    (d1154 : (p 3) → (p 8) → (p 12) → False)
    (d1518 : (p 58) → (p 49) → (¬ p 66) → (¬ p 12) → (p 3) → False)
    (d3753 : (¬ p 31) → (¬ p 58) → (¬ p 56) → (¬ p 27) → (¬ p 29) → (¬ p 33) → False)
    (d4204 : (p 33) → (¬ p 70) → (p 150) → (p 20) → False)
    (d5005 : (¬ p 150) → (¬ p 45) → (p 18) → (p 33) → False)
    (d552 : (p 18) → (p 30) → (p 45) → False)
    (d5216 : (¬ p 14) → (¬ p 15) → (¬ p 43) → (¬ p 141) → (p 45) → False)
    (d5200 : (¬ p 30) → (¬ p 28) → (¬ p 72) → (¬ p 67) → (¬ p 40) → (¬ p 43) → False)
    (d59 : (p 4) → (p 14) → (p 72) → False)
    : (¬ p 79) → (¬ p 53) → (¬ p 66) → (¬ p 89) → (¬ p 50) → (¬ p 43) → (p 130) → (¬ p 56) → (p 49) → (p 3) → (¬ p 15) → (¬ p 70) → (p 4) → (¬ p 9) → (p 80) → (¬ p 67) → (p 42) → (p 37) → (p 20) → (p 18) → False := by
  intro a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19
  have v0 : ¬ p 22 := (fun u => d55 a19 u a17)
  have v1 : p 24 := Classical.byContradiction (fun u => d400 v0 u a3)
  have v2 : ¬ p 29 := (fun u => d4169 v1 a18 u)
  have v3 : ¬ p 27 := (fun u => d582 a19 u a16)
  have v4 : ¬ p 40 := (fun u => d844 u a19 a16)
  have v5 : p 123 := Classical.byContradiction (fun u => d5029 u a0 a14 a6)
  have v6 : p 54 := Classical.byContradiction (fun u => d235 a4 u a0)
  have v7 : ¬ p 141 := (fun u => d5066 v4 a5 u v5)
  have v8 : ¬ p 57 := (fun u => d5072 v4 a5 u v6)
  have v9 : ¬ p 31 := (fun u => d4996 a5 v7 a19 u)
  have v10 : ¬ p 96 := (fun u => d5000 a5 v7 u a17)
  have v11 : ¬ p 28 := (fun u => d5111 v8 a1 u v1)
  have v12 : p 8 := Classical.byContradiction (fun u => d5306 u a13 v10 a3 v5)
  have v13 : ¬ p 12 := (fun u => d1154 a9 v12 u)
  have v14 : ¬ p 58 := (fun u => d1518 u a8 a2 v13 a9)
  have v15 : p 33 := Classical.byContradiction (fun u => d3753 v9 v14 a7 v3 v2 u)
  have v16 : ¬ p 150 := (fun u => d4204 v15 a11 u a18)
  have v17 : p 45 := Classical.byContradiction (fun u => d5005 v16 u a19 v15)
  have v18 : ¬ p 30 := (fun u => d552 a19 u v17)
  have v19 : p 14 := Classical.byContradiction (fun u => d5216 u a10 a5 v7 v17)
  have v20 : p 72 := Classical.byContradiction (fun u => d5200 v18 v11 u a15 v4 a5)
  exact d59 a12 v19 v20

theorem c5448 (p : Nat → Prop)
    (d5042 : (¬ p 64) → (¬ p 69) → (p 37) → (p 42) → False)
    (d266 : (p 49) → (p 56) → (p 69) → False)
    (d20 : (¬ p 4) → (¬ p 5) → (¬ p 63) → False)
    (d4611 : (p 70) → (p 4) → (p 69) → False)
    (d4609 : (p 67) → (p 69) → (p 20) → False)
    (d582 : (p 18) → (p 27) → (p 42) → False)
    (d844 : (p 40) → (p 18) → (p 42) → False)
    (d668 : (p 18) → (p 39) → (p 37) → False)
    (d55 : (p 18) → (p 22) → (p 37) → False)
    (d5446 : (¬ p 51) → (¬ p 43) → (p 130) → (¬ p 56) → (p 3) → (p 4) → (¬ p 9) → (p 80) → (¬ p 63) → (¬ p 40) → (p 42) → False)
    (d822 : (p 50) → (p 51) → (p 3) → False)
    (d38 : (p 3) → (p 6) → (p 51) → False)
    (d213 : (¬ p 5) → (¬ p 6) → (¬ p 76) → False)
    (d2347 : (p 37) → (p 89) → (p 76) → False)
    (d4131 : (p 87) → (p 76) → (p 80) → False)
    (d5232 : (¬ p 78) → (¬ p 39) → (p 37) → (p 76) → False)
    (d1572 : (¬ p 22) → (p 66) → (¬ p 64) → (¬ p 89) → False)
    (d400 : (¬ p 22) → (¬ p 24) → (¬ p 89) → False)
    (d1263 : (p 24) → (p 53) → (p 78) → False)
    (d4169 : (p 24) → (p 20) → (p 29) → False)
    (d5447 : (¬ p 79) → (¬ p 53) → (¬ p 66) → (¬ p 89) → (¬ p 50) → (¬ p 43) → (p 130) → (¬ p 56) → (p 49) → (p 3) → (¬ p 15) → (¬ p 70) → (p 4) → (¬ p 9) → (p 80) → (¬ p 67) → (p 42) → (p 37) → (p 20) → (p 18) → False)
    (d5304 : (¬ p 8) → (¬ p 9) → (p 79) → (p 78) → False)
    (d1154 : (p 3) → (p 8) → (p 12) → False)
    (d5441 : (p 138) → (¬ p 12) → (¬ p 70) → (¬ p 11) → (p 69) → False)
    (d1518 : (p 58) → (p 49) → (¬ p 66) → (¬ p 12) → (p 3) → False)
    (d5398 : (¬ p 138) → (¬ p 87) → (¬ p 25) → (¬ p 27) → (p 79) → False)
    (d638 : (p 25) → (p 20) → (p 30) → False)
    (d3714 : (p 28) → (p 25) → (p 18) → False)
    (d5200 : (¬ p 30) → (¬ p 28) → (¬ p 72) → (¬ p 67) → (¬ p 40) → (¬ p 43) → False)
    (d59 : (p 4) → (p 14) → (p 72) → False)
    (d5220 : (¬ p 14) → (¬ p 15) → (¬ p 30) → (¬ p 28) → (p 141) → False)
    (d5216 : (¬ p 14) → (¬ p 15) → (¬ p 43) → (¬ p 141) → (p 45) → False)
    (d4996 : (¬ p 43) → (¬ p 141) → (p 18) → (p 31) → False)
    (d3753 : (¬ p 31) → (¬ p 58) → (¬ p 56) → (¬ p 27) → (¬ p 29) → (¬ p 33) → False)
    (d4204 : (p 33) → (¬ p 70) → (p 150) → (p 20) → False)
    (d5005 : (¬ p 150) → (¬ p 45) → (p 18) → (p 33) → False)
    : (¬ p 43) → (p 130) → (p 49) → (p 3) → (¬ p 15) → (¬ p 5) → (¬ p 9) → (¬ p 11) → (p 80) → (¬ p 63) → (¬ p 64) → (p 42) → (p 37) → (p 20) → (p 18) → False := by
  intro a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14
  have v0 : p 69 := Classical.byContradiction (fun u => d5042 a10 u a12 a11)
  have v1 : ¬ p 56 := (fun u => d266 a2 u v0)
  have v2 : p 4 := Classical.byContradiction (fun u => d20 u a5 a9)
  have v3 : ¬ p 70 := (fun u => d4611 u v2 v0)
  have v4 : ¬ p 67 := (fun u => d4609 u v0 a13)
  have v5 : ¬ p 27 := (fun u => d582 a14 u a11)
  have v6 : ¬ p 40 := (fun u => d844 u a14 a11)
  have v7 : ¬ p 39 := (fun u => d668 a14 u a12)
  have v8 : ¬ p 22 := (fun u => d55 a14 u a12)
  have v9 : p 51 := Classical.byContradiction (fun u => d5446 u a0 a1 v1 a3 v2 a6 a8 a9 v6 a11)
  have v10 : ¬ p 50 := (fun u => d822 u v9 a3)
  have v11 : ¬ p 6 := (fun u => d38 a3 u v9)
  have v12 : p 76 := Classical.byContradiction (fun u => d213 a5 v11 u)
  have v13 : ¬ p 89 := (fun u => d2347 a12 u v12)
  have v14 : ¬ p 87 := (fun u => d4131 u v12 a8)
  have v15 : p 78 := Classical.byContradiction (fun u => d5232 u v7 a12 v12)
  have v16 : ¬ p 66 := (fun u => d1572 v8 u a10 v13)
  have v17 : p 24 := Classical.byContradiction (fun u => d400 v8 u v13)
  have v18 : ¬ p 53 := (fun u => d1263 v17 u v15)
  have v19 : ¬ p 29 := (fun u => d4169 v17 a13 u)
  have v20 : p 79 := Classical.byContradiction (fun u => d5447 u v18 v16 v13 v10 a0 a1 v1 a2 a3 a4 v3 v2 a6 a8 v4 a11 a12 a13 a14)
  have v21 : p 8 := Classical.byContradiction (fun u => d5304 u a6 v20 v15)
  have v22 : ¬ p 12 := (fun u => d1154 a3 v21 u)
  have v23 : ¬ p 138 := (fun u => d5441 u v22 v3 a7 v0)
  have v24 : ¬ p 58 := (fun u => d1518 u a2 v16 v22 a3)
  have v25 : p 25 := Classical.byContradiction (fun u => d5398 v23 v14 u v5 v20)
  have v26 : ¬ p 30 := (fun u => d638 v25 a13 u)
  have v27 : ¬ p 28 := (fun u => d3714 u v25 a14)
  have v28 : p 72 := Classical.byContradiction (fun u => d5200 v26 v27 u v4 v6 a0)
  have v29 : ¬ p 14 := (fun u => d59 v2 u v28)
  have v30 : ¬ p 141 := (fun u => d5220 v29 a4 v26 v27 u)
  have v31 : ¬ p 45 := (fun u => d5216 v29 a4 a0 v30 u)
  have v32 : ¬ p 31 := (fun u => d4996 a0 v30 a14 u)
  have v33 : p 33 := Classical.byContradiction (fun u => d3753 v32 v24 v1 v5 v19 u)
  have v34 : ¬ p 150 := (fun u => d4204 v33 v3 u a13)
  exact d5005 v34 v31 a14 v33

theorem c5449 (p : Nat → Prop)
    (d5042 : (¬ p 64) → (¬ p 69) → (p 37) → (p 42) → False)
    (d74 : (¬ p 63) → (¬ p 68) → (¬ p 80) → False)
    (d5430 : (p 5) → (¬ p 9) → (¬ p 11) → (¬ p 63) → (¬ p 68) → (¬ p 64) → (p 42) → (p 37) → (p 20) → (p 18) → False)
    (d20 : (¬ p 4) → (¬ p 5) → (¬ p 63) → False)
    (d5445 : (¬ p 3) → (p 4) → (¬ p 5) → (¬ p 9) → (¬ p 11) → (p 80) → (¬ p 68) → (p 69) → (p 42) → (p 37) → (p 20) → (p 18) → False)
    (d4212 : (p 15) → (¬ p 9) → (p 4) → (p 80) → (¬ p 68) → False)
    (d5425 : (p 49) → (¬ p 130) → (¬ p 68) → (p 69) → False)
    (d5448 : (¬ p 43) → (p 130) → (p 49) → (p 3) → (¬ p 15) → (¬ p 5) → (¬ p 9) → (¬ p 11) → (p 80) → (¬ p 63) → (¬ p 64) → (p 42) → (p 37) → (p 20) → (p 18) → False)
    (d5322 : (¬ p 11) → (¬ p 12) → (p 43) → (p 42) → False)
    (d4556 : (p 12) → (p 4) → (p 7) → False)
    (d1154 : (p 3) → (p 8) → (p 12) → False)
    (d111 : (¬ p 7) → (¬ p 8) → (¬ p 99) → False)
    (d4016 : (¬ p 6) → (p 99) → (¬ p 7) → (¬ p 5) → (p 3) → False)
    (d798 : (p 6) → (p 10) → (p 3) → False)
    (d5367 : (¬ p 9) → (¬ p 10) → (p 79) → (p 80) → False)
    (d5365 : (¬ p 9) → (¬ p 10) → (p 123) → (p 130) → False)
    (d5029 : (¬ p 123) → (¬ p 79) → (p 80) → (p 130) → False)
    : (p 49) → (¬ p 9) → (¬ p 11) → (¬ p 63) → (¬ p 68) → (¬ p 64) → (p 42) → (p 37) → (p 20) → (p 18) → False := by
  intro a0 a1 a2 a3 a4 a5 a6 a7 a8 a9
  have v0 : p 69 := Classical.byContradiction (fun u => d5042 a5 u a7 a6)
  have v1 : p 80 := Classical.byContradiction (fun u => d74 a3 a4 u)
  have v2 : ¬ p 5 := (fun u => d5430 u a1 a2 a3 a4 a5 a6 a7 a8 a9)
  have v3 : p 4 := Classical.byContradiction (fun u => d20 u v2 a3)
  have v4 : p 3 := Classical.byContradiction (fun u => d5445 u v3 v2 a1 a2 v1 a4 v0 a6 a7 a8 a9)
  have v5 : ¬ p 15 := (fun u => d4212 u a1 v3 v1 a4)
  have v6 : p 130 := Classical.byContradiction (fun u => d5425 a0 u a4 v0)
  have v7 : p 43 := Classical.byContradiction (fun u => d5448 u v6 a0 v4 v5 v2 a1 a2 v1 a3 a5 a6 a7 a8 a9)
  have v8 : p 12 := Classical.byContradiction (fun u => d5322 a2 u v7 a6)
  have v9 : ¬ p 7 := (fun u => d4556 v8 v3 u)
  have v10 : ¬ p 8 := (fun u => d1154 v4 u v8)
  have v11 : p 99 := Classical.byContradiction (fun u => d111 v9 v10 u)
  have v12 : p 6 := Classical.byContradiction (fun u => d4016 u v11 v9 v2 v4)
  have v13 : ¬ p 10 := (fun u => d798 v12 u v4)
  have v14 : ¬ p 79 := (fun u => d5367 a1 v13 u v1)
  have v15 : ¬ p 123 := (fun u => d5365 a1 v13 u v6)
  exact d5029 v15 v14 v1 v6

theorem c5450 (p : Nat → Prop)
    (d4354 : (p 8) → (¬ p 49) → (p 3) → (p 4) → False)
    (d798 : (p 6) → (p 10) → (p 3) → False)
    (d111 : (¬ p 7) → (¬ p 8) → (¬ p 99) → False)
    (d4016 : (¬ p 6) → (p 99) → (¬ p 7) → (¬ p 5) → (p 3) → False)
    : (p 3) → (p 10) → (¬ p 7) → (p 4) → (¬ p 5) → (¬ p 49) → False := by
  intro a0 a1 a2 a3 a4 a5
  have v0 : ¬ p 8 := (fun u => d4354 u a5 a0 a3)
  have v1 : ¬ p 6 := (fun u => d798 u a1 a0)
  have v2 : p 99 := Classical.byContradiction (fun u => d111 a2 v0 u)
  exact d4016 v1 v2 a2 a4 a0

theorem c5451 (p : Nat → Prop)
    (d755 : (p 80) → (p 130) → (¬ p 9) → (p 5) → False)
    (d5439 : (p 21) → (p 80) → (¬ p 39) → (p 18) → False)
    (d5434 : (p 79) → (¬ p 7) → (¬ p 21) → (¬ p 2) → (¬ p 49) → (p 4) → (¬ p 5) → (¬ p 9) → (p 80) → (¬ p 39) → (p 18) → False)
    (d5029 : (¬ p 123) → (¬ p 79) → (p 80) → (p 130) → False)
    (d5365 : (¬ p 9) → (¬ p 10) → (p 123) → (p 130) → False)
    (d5450 : (p 3) → (p 10) → (¬ p 7) → (p 4) → (¬ p 5) → (¬ p 49) → False)
    (d505 : (¬ p 2) → (¬ p 3) → (¬ p 34) → False)
    (d5437 : (p 34) → (¬ p 21) → (¬ p 7) → (¬ p 3) → (¬ p 49) → (¬ p 35) → (p 42) → (p 18) → False)
    : (¬ p 39) → (¬ p 7) → (¬ p 2) → (p 4) → (p 130) → (p 80) → (¬ p 9) → (¬ p 49) → (¬ p 35) → (p 42) → (p 18) → False := by
  intro a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10
  have v0 : ¬ p 5 := (fun u => d755 a5 a4 a6 u)
  have v1 : ¬ p 21 := (fun u => d5439 u a5 a0 a10)
  have v2 : ¬ p 79 := (fun u => d5434 u a1 v1 a2 a7 a3 v0 a6 a5 a0 a10)
  have v3 : p 123 := Classical.byContradiction (fun u => d5029 u v2 a5 a4)
  have v4 : p 10 := Classical.byContradiction (fun u => d5365 a6 u v3 a4)
  have v5 : ¬ p 3 := (fun u => d5450 u v4 a1 a3 v0 a7)
  have v6 : p 34 := Classical.byContradiction (fun u => d505 a2 v5 u)
  exact d5437 v6 v1 a1 v5 a7 a8 a9 a10

theorem c5452 (p : Nat → Prop)
    (d755 : (p 80) → (p 130) → (¬ p 9) → (p 5) → False)
    (d844 : (p 40) → (p 18) → (p 42) → False)
    (d4146 : (p 43) → (p 2) → (p 42) → False)
    (d5322 : (¬ p 11) → (¬ p 12) → (p 43) → (p 42) → False)
    (d4556 : (p 12) → (p 4) → (p 7) → False)
    (d5451 : (¬ p 39) → (¬ p 7) → (¬ p 2) → (p 4) → (p 130) → (p 80) → (¬ p 9) → (¬ p 49) → (¬ p 35) → (p 42) → (p 18) → False)
    (d1171 : (p 39) → (p 34) → (p 43) → False)
    (d668 : (p 18) → (p 39) → (p 37) → False)
    (d505 : (¬ p 2) → (¬ p 3) → (¬ p 34) → False)
    (d4259 : (¬ p 37) → (¬ p 79) → (p 3) → (¬ p 40) → (¬ p 34) → False)
    (d5450 : (p 3) → (p 10) → (¬ p 7) → (p 4) → (¬ p 5) → (¬ p 49) → False)
    (d5367 : (¬ p 9) → (¬ p 10) → (p 79) → (p 80) → False)
    : (p 43) → (¬ p 11) → (p 4) → (p 130) → (p 80) → (¬ p 9) → (¬ p 49) → (¬ p 35) → (p 42) → (p 18) → False := by
  intro a0 a1 a2 a3 a4 a5 a6 a7 a8 a9
  have v0 : ¬ p 5 := (fun u => d755 a4 a3 a5 u)
  have v1 : ¬ p 40 := (fun u => d844 u a9 a8)
  have v2 : ¬ p 2 := (fun u => d4146 a0 u a8)
  have v3 : p 12 := Classical.byContradiction (fun u => d5322 a1 u a0 a8)
  have v4 : ¬ p 7 := (fun u => d4556 v3 a2 u)
  have v5 : p 39 := Classical.byContradiction (fun u => d5451 u v4 v2 a2 a3 a4 a5 a6 a7 a8 a9)
  have v6 : ¬ p 34 := (fun u => d1171 v5 u a0)
  have v7 : ¬ p 37 := (fun u => d668 a9 v5 u)
  have v8 : p 3 := Classical.byContradiction (fun u => d505 v2 u v6)
  have v9 : p 79 := Classical.byContradiction (fun u => d4259 v7 u v8 v1 v6)
  have v10 : ¬ p 10 := (fun u => d5450 v8 u v4 a2 v0 a6)
  exact d5367 a5 v10 v9 a4

theorem c5453 (p : Nat → Prop)
    (d5367 : (¬ p 9) → (¬ p 10) → (p 79) → (p 80) → False)
    (d5365 : (¬ p 9) → (¬ p 10) → (p 123) → (p 130) → False)
    (d5029 : (¬ p 123) → (¬ p 79) → (p 80) → (p 130) → False)
    : (¬ p 10) → (p 130) → (p 80) → (¬ p 9) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 79 := (fun u => d5367 a3 a0 u a2)
  have v1 : ¬ p 123 := (fun u => d5365 a3 a0 u a1)
  exact d5029 v1 v0 a2 a1

theorem c5455 (p : Nat → Prop)
    (d755 : (p 80) → (p 130) → (¬ p 9) → (p 5) → False)
    (d5453 : (¬ p 10) → (p 130) → (p 80) → (¬ p 9) → False)
    (d798 : (p 6) → (p 10) → (p 3) → False)
    (d213 : (¬ p 5) → (¬ p 6) → (¬ p 76) → False)
    (d5450 : (p 3) → (p 10) → (¬ p 7) → (p 4) → (¬ p 5) → (¬ p 49) → False)
    (d418 : (p 4) → (p 7) → (p 65) → False)
    (d4354 : (p 8) → (¬ p 49) → (p 3) → (p 4) → False)
    (d844 : (p 40) → (p 18) → (p 42) → False)
    (d10 : (¬ p 37) → (¬ p 40) → (¬ p 90) → False)
    (d2715 : (p 37) → (p 42) → (p 35) → False)
    (d3501 : (p 42) → (p 102) → (p 37) → (¬ p 65) → False)
    (d2347 : (p 37) → (p 89) → (p 76) → False)
    (d4948 : (¬ p 102) → (¬ p 56) → (p 7) → (p 3) → False)
    (d5306 : (¬ p 8) → (¬ p 9) → (¬ p 96) → (¬ p 89) → (p 123) → False)
    (d120 : (p 3) → (p 11) → (p 56) → False)
    (d5452 : (p 43) → (¬ p 11) → (p 4) → (p 130) → (p 80) → (¬ p 9) → (¬ p 49) → (¬ p 35) → (p 42) → (p 18) → False)
    (d5066 : (¬ p 40) → (¬ p 43) → (p 141) → (p 123) → False)
    (d5000 : (¬ p 43) → (¬ p 141) → (p 96) → (p 37) → False)
    : (p 18) → (p 42) → (¬ p 90) → (p 123) → (p 3) → (p 4) → (p 130) → (p 80) → (¬ p 9) → (¬ p 49) → False := by
  intro a0 a1 a2 a3 a4 a5 a6 a7 a8 a9
  have v0 : ¬ p 5 := (fun u => d755 a7 a6 a8 u)
  have v1 : p 10 := Classical.byContradiction (fun u => d5453 u a6 a7 a8)
  have v2 : ¬ p 6 := (fun u => d798 u v1 a4)
  have v3 : p 76 := Classical.byContradiction (fun u => d213 v0 v2 u)
  have v4 : p 7 := Classical.byContradiction (fun u => d5450 a4 v1 u a5 v0 a9)
  have v5 : ¬ p 65 := (fun u => d418 a5 v4 u)
  have v6 : ¬ p 8 := (fun u => d4354 u a9 a4 a5)
  have v7 : ¬ p 40 := (fun u => d844 u a0 a1)
  have v8 : p 37 := Classical.byContradiction (fun u => d10 u v7 a2)
  have v9 : ¬ p 35 := (fun u => d2715 v8 a1 u)
  have v10 : ¬ p 102 := (fun u => d3501 a1 u v8 v5)
  have v11 : ¬ p 89 := (fun u => d2347 v8 u v3)
  have v12 : p 56 := Classical.byContradiction (fun u => d4948 v10 u v4 a4)
  have v13 : p 96 := Classical.byContradiction (fun u => d5306 v6 a8 u v11 a3)
  have v14 : ¬ p 11 := (fun u => d120 a4 u v12)
  have v15 : ¬ p 43 := (fun u => d5452 u v14 a5 a6 a7 a8 a9 v9 a1 a0)
  have v16 : ¬ p 141 := (fun u => d5066 v7 v15 u a3)
  exact d5000 v15 v16 v13 v8

theorem c5456 (p : Nat → Prop)
    (d755 : (p 80) → (p 130) → (¬ p 9) → (p 5) → False)
    (d5453 : (¬ p 10) → (p 130) → (p 80) → (¬ p 9) → False)
    (d5450 : (p 3) → (p 10) → (¬ p 7) → (p 4) → (¬ p 5) → (¬ p 49) → False)
    (d1215 : (p 4) → (p 2) → (p 7) → False)
    (d4354 : (p 8) → (¬ p 49) → (p 3) → (p 4) → False)
    (d5455 : (p 18) → (p 42) → (¬ p 90) → (p 123) → (p 3) → (p 4) → (p 130) → (p 80) → (¬ p 9) → (¬ p 49) → False)
    (d5353 : (¬ p 2) → (¬ p 18) → (p 4) → (p 20) → False)
    (d5363 : (¬ p 2) → (¬ p 18) → (¬ p 21) → (¬ p 50) → (p 3) → False)
    (d1261 : (¬ p 20) → (¬ p 22) → (p 37) → (¬ p 18) → False)
    (d2797 : (¬ p 22) → (p 66) → (¬ p 24) → (¬ p 20) → False)
    (d4536 : (p 78) → (p 80) → (p 21) → False)
    (d10 : (¬ p 37) → (¬ p 40) → (¬ p 90) → False)
    (d5299 : (¬ p 8) → (¬ p 9) → (p 25) → (p 24) → False)
    (d5301 : (¬ p 8) → (¬ p 9) → (p 39) → (p 40) → False)
    (d785 : (p 40) → (p 38) → (p 7) → (¬ p 25) → (p 42) → False)
    (d5235 : (¬ p 78) → (¬ p 39) → (p 80) → (p 41) → False)
    (d5278 : (¬ p 41) → (¬ p 38) → (p 7) → (p 10) → False)
    : (p 42) → (p 66) → (¬ p 90) → (p 123) → (¬ p 22) → (¬ p 50) → (p 3) → (p 4) → (p 130) → (p 80) → (¬ p 9) → (¬ p 49) → False := by
  intro a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11
  have v0 : ¬ p 5 := (fun u => d755 a9 a8 a10 u)
  have v1 : p 10 := Classical.byContradiction (fun u => d5453 u a8 a9 a10)
  have v2 : p 7 := Classical.byContradiction (fun u => d5450 a6 v1 u a7 v0 a11)
  have v3 : ¬ p 2 := (fun u => d1215 a7 u v2)
  have v4 : ¬ p 8 := (fun u => d4354 u a11 a6 a7)
  have v5 : ¬ p 18 := (fun u => d5455 u a0 a2 a3 a6 a7 a8 a9 a10 a11)
  have v6 : ¬ p 20 := (fun u => d5353 v3 v5 a7 u)
  have v7 : p 21 := Classical.byContradiction (fun u => d5363 v3 v5 u a5 a6)
  have v8 : ¬ p 37 := (fun u => d1261 v6 a4 u v5)
  have v9 : p 24 := Classical.byContradiction (fun u => d2797 a4 a1 u v6)
  have v10 : ¬ p 78 := (fun u => d4536 u a9 v7)
  have v11 : p 40 := Classical.byContradiction (fun u => d10 v8 u a2)
  have v12 : ¬ p 25 := (fun u => d5299 v4 a10 u v9)
  have v13 : ¬ p 39 := (fun u => d5301 v4 a10 u v11)
  have v14 : ¬ p 38 := (fun u => d785 v11 u v2 v12 a0)
  have v15 : ¬ p 41 := (fun u => d5235 v10 v13 a9 u)
  exact d5278 v15 v14 v2 v1

theorem c5457 (p : Nat → Prop)
    (d5353 : (¬ p 2) → (¬ p 18) → (p 4) → (p 20) → False)
    (d1261 : (¬ p 20) → (¬ p 22) → (p 37) → (¬ p 18) → False)
    (d2797 : (¬ p 22) → (p 66) → (¬ p 24) → (¬ p 20) → False)
    (d10 : (¬ p 37) → (¬ p 40) → (¬ p 90) → False)
    (d5299 : (¬ p 8) → (¬ p 9) → (p 25) → (p 24) → False)
    (d5301 : (¬ p 8) → (¬ p 9) → (p 39) → (p 40) → False)
    (d5319 : (¬ p 25) → (¬ p 27) → (¬ p 8) → (¬ p 9) → (¬ p 39) → (¬ p 42) → False)
    (d4970 : (¬ p 39) → (¬ p 42) → (p 27) → (p 24) → False)
    : (¬ p 18) → (¬ p 42) → (p 66) → (¬ p 90) → (¬ p 22) → (¬ p 2) → (¬ p 8) → (p 4) → (¬ p 9) → False := by
  intro a0 a1 a2 a3 a4 a5 a6 a7 a8
  have v0 : ¬ p 20 := (fun u => d5353 a5 a0 a7 u)
  have v1 : ¬ p 37 := (fun u => d1261 v0 a4 u a0)
  have v2 : p 24 := Classical.byContradiction (fun u => d2797 a4 a2 u v0)
  have v3 : p 40 := Classical.byContradiction (fun u => d10 v1 u a3)
  have v4 : ¬ p 25 := (fun u => d5299 a6 a8 u v2)
  have v5 : ¬ p 39 := (fun u => d5301 a6 a8 u v3)
  have v6 : p 27 := Classical.byContradiction (fun u => d5319 v4 u a6 a8 v5 a1)
  exact d4970 v5 a1 v6 v2

theorem c5458 (p : Nat → Prop)
    (d3227 : (p 51) → (p 76) → (p 22) → False)
    (d225 : (p 18) → (p 25) → (p 40) → False)
    (d5301 : (¬ p 8) → (¬ p 9) → (p 39) → (p 40) → False)
    (d5319 : (¬ p 25) → (¬ p 27) → (¬ p 8) → (¬ p 9) → (¬ p 39) → (¬ p 42) → False)
    (d4972 : (¬ p 39) → (¬ p 42) → (p 66) → (p 69) → False)
    (d4970 : (¬ p 39) → (¬ p 42) → (p 27) → (p 24) → False)
    (d400 : (¬ p 22) → (¬ p 24) → (¬ p 89) → False)
    (d471 : (p 64) → (p 66) → (p 89) → False)
    (d25 : (p 76) → (p 78) → (p 89) → False)
    (d5044 : (¬ p 64) → (¬ p 69) → (p 56) → (p 51) → False)
    (d5235 : (¬ p 78) → (¬ p 39) → (p 80) → (p 41) → False)
    (d4948 : (¬ p 102) → (¬ p 56) → (p 7) → (p 3) → False)
    (d5278 : (¬ p 41) → (¬ p 38) → (p 7) → (p 10) → False)
    (d557 : (p 23) → (p 27) → (p 102) → False)
    (d1539 : (p 40) → (p 18) → (p 38) → (¬ p 23) → False)
    : (p 40) → (p 18) → (¬ p 42) → (p 66) → (p 76) → (p 51) → (p 7) → (¬ p 8) → (p 3) → (p 10) → (p 80) → (¬ p 9) → False := by
  intro a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11
  have v0 : ¬ p 22 := (fun u => d3227 a5 a4 u)
  have v1 : ¬ p 25 := (fun u => d225 a1 u a0)
  have v2 : ¬ p 39 := (fun u => d5301 a7 a11 u a0)
  have v3 : p 27 := Classical.byContradiction (fun u => d5319 v1 u a7 a11 v2 a2)
  have v4 : ¬ p 69 := (fun u => d4972 v2 a2 a3 u)
  have v5 : ¬ p 24 := (fun u => d4970 v2 a2 v3 u)
  have v6 : p 89 := Classical.byContradiction (fun u => d400 v0 v5 u)
  have v7 : ¬ p 64 := (fun u => d471 u a3 v6)
  have v8 : ¬ p 78 := (fun u => d25 a4 u v6)
  have v9 : ¬ p 56 := (fun u => d5044 v7 v4 u a5)
  have v10 : ¬ p 41 := (fun u => d5235 v8 v2 a10 u)
  have v11 : p 102 := Classical.byContradiction (fun u => d4948 u v9 a6 a8)
  have v12 : p 38 := Classical.byContradiction (fun u => d5278 v10 u a6 a9)
  have v13 : ¬ p 23 := (fun u => d557 u v3 v11)
  exact d1539 a0 a1 v12 v13

theorem c5459 (p : Nat → Prop)
    (d755 : (p 80) → (p 130) → (¬ p 9) → (p 5) → False)
    (d5453 : (¬ p 10) → (p 130) → (p 80) → (¬ p 9) → False)
    (d798 : (p 6) → (p 10) → (p 3) → False)
    (d213 : (¬ p 5) → (¬ p 6) → (¬ p 76) → False)
    (d3227 : (p 51) → (p 76) → (p 22) → False)
    (d822 : (p 50) → (p 51) → (p 3) → False)
    (d5450 : (p 3) → (p 10) → (¬ p 7) → (p 4) → (¬ p 5) → (¬ p 49) → False)
    (d1215 : (p 4) → (p 2) → (p 7) → False)
    (d4354 : (p 8) → (¬ p 49) → (p 3) → (p 4) → False)
    (d5029 : (¬ p 123) → (¬ p 79) → (p 80) → (p 130) → False)
    (d235 : (¬ p 50) → (¬ p 54) → (¬ p 79) → False)
    (d797 : (p 54) → (p 53) → (p 3) → False)
    (d17 : (p 51) → (p 54) → (p 90) → False)
    (d273 : (¬ p 49) → (¬ p 53) → (¬ p 66) → False)
    (d5456 : (p 42) → (p 66) → (¬ p 90) → (p 123) → (¬ p 22) → (¬ p 50) → (p 3) → (p 4) → (p 130) → (p 80) → (¬ p 9) → (¬ p 49) → False)
    (d5457 : (¬ p 18) → (¬ p 42) → (p 66) → (¬ p 90) → (¬ p 22) → (¬ p 2) → (¬ p 8) → (p 4) → (¬ p 9) → False)
    (d5458 : (p 40) → (p 18) → (¬ p 42) → (p 66) → (p 76) → (p 51) → (p 7) → (¬ p 8) → (p 3) → (p 10) → (p 80) → (¬ p 9) → False)
    (d10 : (¬ p 37) → (¬ p 40) → (¬ p 90) → False)
    (d668 : (p 18) → (p 39) → (p 37) → False)
    (d2347 : (p 37) → (p 89) → (p 76) → False)
    (d400 : (¬ p 22) → (¬ p 24) → (¬ p 89) → False)
    (d4600 : (p 27) → (p 24) → (p 18) → False)
    (d5299 : (¬ p 8) → (¬ p 9) → (p 25) → (p 24) → False)
    (d5319 : (¬ p 25) → (¬ p 27) → (¬ p 8) → (¬ p 9) → (¬ p 39) → (¬ p 42) → False)
    : (¬ p 79) → (p 51) → (p 3) → (p 4) → (p 130) → (p 80) → (¬ p 9) → (¬ p 49) → False := by
  intro a0 a1 a2 a3 a4 a5 a6 a7
  have v0 : ¬ p 5 := (fun u => d755 a5 a4 a6 u)
  have v1 : p 10 := Classical.byContradiction (fun u => d5453 u a4 a5 a6)
  have v2 : ¬ p 6 := (fun u => d798 u v1 a2)
  have v3 : p 76 := Classical.byContradiction (fun u => d213 v0 v2 u)
  have v4 : ¬ p 22 := (fun u => d3227 a1 v3 u)
  have v5 : ¬ p 50 := (fun u => d822 u a1 a2)
  have v6 : p 7 := Classical.byContradiction (fun u => d5450 a2 v1 u a3 v0 a7)
  have v7 : ¬ p 2 := (fun u => d1215 a3 u v6)
  have v8 : ¬ p 8 := (fun u => d4354 u a7 a2 a3)
  have v9 : p 123 := Classical.byContradiction (fun u => d5029 u a0 a5 a4)
  have v10 : p 54 := Classical.byContradiction (fun u => d235 v5 u a0)
  have v11 : ¬ p 53 := (fun u => d797 v10 u a2)
  have v12 : ¬ p 90 := (fun u => d17 a1 v10 u)
  have v13 : p 66 := Classical.byContradiction (fun u => d273 a7 v11 u)
  have v14 : ¬ p 42 := (fun u => d5456 u v13 v12 v9 v4 v5 a2 a3 a4 a5 a6 a7)
  have v15 : p 18 := Classical.byContradiction (fun u => d5457 u v14 v13 v12 v4 v7 v8 a3 a6)
  have v16 : ¬ p 40 := (fun u => d5458 u v15 v14 v13 v3 a1 v6 v8 a2 v1 a5 a6)
  have v17 : p 37 := Classical.byContradiction (fun u => d10 u v16 v12)
  have v18 : ¬ p 39 := (fun u => d668 v15 u v17)
  have v19 : ¬ p 89 := (fun u => d2347 v17 u v3)
  have v20 : p 24 := Classical.byContradiction (fun u => d400 v4 u v19)
  have v21 : ¬ p 27 := (fun u => d4600 u v20 v15)
  have v22 : ¬ p 25 := (fun u => d5299 v8 a6 u v20)
  exact d5319 v22 v21 v8 a6 v18 v14

theorem c5460 (p : Nat → Prop)
    (d668 : (p 18) → (p 39) → (p 37) → False)
    (d5232 : (¬ p 78) → (¬ p 39) → (p 37) → (p 76) → False)
    : (p 37) → (p 18) → (¬ p 78) → (p 76) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 39 := (fun u => d668 a1 u a0)
  exact d5232 a2 v0 a0 a3

theorem c5461 (p : Nat → Prop)
    (d5302 : (¬ p 8) → (¬ p 9) → (p 89) → (p 90) → False)
    (d211 : (p 90) → (p 96) → (p 123) → False)
    (d5306 : (¬ p 8) → (¬ p 9) → (¬ p 96) → (¬ p 89) → (p 123) → False)
    : (p 90) → (p 123) → (¬ p 8) → (¬ p 9) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 89 := (fun u => d5302 a2 a3 u a0)
  have v1 : ¬ p 96 := (fun u => d211 a0 u a1)
  exact d5306 a2 a3 v1 v0 a1

theorem c5462 (p : Nat → Prop)
    (d5460 : (p 37) → (p 18) → (¬ p 78) → (p 76) → False)
    (d10 : (¬ p 37) → (¬ p 40) → (¬ p 90) → False)
    (d225 : (p 18) → (p 25) → (p 40) → False)
    (d5301 : (¬ p 8) → (¬ p 9) → (p 39) → (p 40) → False)
    (d5458 : (p 40) → (p 18) → (¬ p 42) → (p 66) → (p 76) → (p 51) → (p 7) → (¬ p 8) → (p 3) → (p 10) → (p 80) → (¬ p 9) → False)
    (d5319 : (¬ p 25) → (¬ p 27) → (¬ p 8) → (¬ p 9) → (¬ p 39) → (¬ p 42) → False)
    (d273 : (¬ p 49) → (¬ p 53) → (¬ p 66) → False)
    (d4970 : (¬ p 39) → (¬ p 42) → (p 27) → (p 24) → False)
    (d4635 : (p 53) → (p 76) → (¬ p 24) → (p 51) → False)
    : (p 18) → (¬ p 42) → (¬ p 90) → (¬ p 78) → (p 76) → (p 51) → (p 7) → (¬ p 8) → (p 3) → (p 10) → (p 80) → (¬ p 9) → (¬ p 49) → False := by
  intro a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12
  have v0 : ¬ p 37 := (fun u => d5460 u a0 a3 a4)
  have v1 : p 40 := Classical.byContradiction (fun u => d10 v0 u a2)
  have v2 : ¬ p 25 := (fun u => d225 a0 u v1)
  have v3 : ¬ p 39 := (fun u => d5301 a7 a11 u v1)
  have v4 : ¬ p 66 := (fun u => d5458 v1 a0 a1 u a4 a5 a6 a7 a8 a9 a10 a11)
  have v5 : p 27 := Classical.byContradiction (fun u => d5319 v2 u a7 a11 v3 a1)
  have v6 : p 53 := Classical.byContradiction (fun u => d273 a12 u v4)
  have v7 : ¬ p 24 := (fun u => d4970 v3 a1 v5 u)
  exact d4635 v6 a4 v7 a5

theorem c5463 (p : Nat → Prop)
    (d4354 : (p 8) → (¬ p 49) → (p 3) → (p 4) → False)
    (d5304 : (¬ p 8) → (¬ p 9) → (p 79) → (p 78) → False)
    (d3227 : (p 51) → (p 76) → (p 22) → False)
    (d822 : (p 50) → (p 51) → (p 3) → False)
    (d1215 : (p 4) → (p 2) → (p 7) → False)
    (d51 : (p 3) → (p 10) → (p 55) → False)
    (d5462 : (p 18) → (¬ p 42) → (¬ p 90) → (¬ p 78) → (p 76) → (p 51) → (p 7) → (¬ p 8) → (p 3) → (p 10) → (p 80) → (¬ p 9) → (¬ p 49) → False)
    (d5353 : (¬ p 2) → (¬ p 18) → (p 4) → (p 20) → False)
    (d5360 : (¬ p 2) → (¬ p 18) → (p 26) → (p 10) → False)
    (d5363 : (¬ p 2) → (¬ p 18) → (¬ p 21) → (¬ p 50) → (p 3) → False)
    (d1261 : (¬ p 20) → (¬ p 22) → (p 37) → (¬ p 18) → False)
    (d270 : (¬ p 20) → (¬ p 22) → (¬ p 64) → False)
    (d424 : (p 21) → (p 25) → (p 79) → False)
    (d10 : (¬ p 37) → (¬ p 40) → (¬ p 90) → False)
    (d900 : (¬ p 24) → (¬ p 55) → (p 64) → (¬ p 22) → (¬ p 26) → False)
    (d5301 : (¬ p 8) → (¬ p 9) → (p 39) → (p 40) → False)
    (d4970 : (¬ p 39) → (¬ p 42) → (p 27) → (p 24) → False)
    (d5319 : (¬ p 25) → (¬ p 27) → (¬ p 8) → (¬ p 9) → (¬ p 39) → (¬ p 42) → False)
    : (¬ p 42) → (¬ p 90) → (p 79) → (p 76) → (p 51) → (p 7) → (p 3) → (p 10) → (p 4) → (p 80) → (¬ p 9) → (¬ p 49) → False := by
  intro a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11
  have v0 : ¬ p 8 := (fun u => d4354 u a11 a6 a8)
  have v1 : ¬ p 78 := (fun u => d5304 v0 a10 a2 u)
  have v2 : ¬ p 22 := (fun u => d3227 a4 a3 u)
  have v3 : ¬ p 50 := (fun u => d822 u a4 a6)
  have v4 : ¬ p 2 := (fun u => d1215 a8 u a5)
  have v5 : ¬ p 55 := (fun u => d51 a6 a7 u)
  have v6 : ¬ p 18 := (fun u => d5462 u a0 a1 v1 a3 a4 a5 v0 a6 a7 a9 a10 a11)
  have v7 : ¬ p 20 := (fun u => d5353 v4 v6 a8 u)
  have v8 : ¬ p 26 := (fun u => d5360 v4 v6 u a7)
  have v9 : p 21 := Classical.byContradiction (fun u => d5363 v4 v6 u v3 a6)
  have v10 : ¬ p 37 := (fun u => d1261 v7 v2 u v6)
  have v11 : p 64 := Classical.byContradiction (fun u => d270 v7 v2 u)
  have v12 : ¬ p 25 := (fun u => d424 v9 u a2)
  have v13 : p 40 := Classical.byContradiction (fun u => d10 v10 u a1)
  have v14 : p 24 := Classical.byContradiction (fun u => d900 u v5 v11 v2 v8)
  have v15 : ¬ p 39 := (fun u => d5301 v0 a10 u v13)
  have v16 : ¬ p 27 := (fun u => d4970 v15 a0 u v14)
  exact d5319 v12 v16 v0 a10 v15 a0

theorem c5465 (p : Nat → Prop)
    (d844 : (p 40) → (p 18) → (p 42) → False)
    (d785 : (p 40) → (p 38) → (p 7) → (¬ p 25) → (p 42) → False)
    (d5363 : (¬ p 2) → (¬ p 18) → (¬ p 21) → (¬ p 50) → (p 3) → False)
    (d424 : (p 21) → (p 25) → (p 79) → False)
    : (p 42) → (p 38) → (p 40) → (p 79) → (¬ p 50) → (¬ p 2) → (p 7) → (p 3) → False := by
  intro a0 a1 a2 a3 a4 a5 a6 a7
  have v0 : ¬ p 18 := (fun u => d844 a2 u a0)
  have v1 : p 25 := Classical.byContradiction (fun u => d785 a2 a1 a6 u a0)
  have v2 : p 21 := Classical.byContradiction (fun u => d5363 a5 v0 u a4 a7)
  exact d424 v2 v1 a3

theorem c5466 (p : Nat → Prop)
    (d4354 : (p 8) → (¬ p 49) → (p 3) → (p 4) → False)
    (d5304 : (¬ p 8) → (¬ p 9) → (p 79) → (p 78) → False)
    (d3227 : (p 51) → (p 76) → (p 22) → False)
    (d822 : (p 50) → (p 51) → (p 3) → False)
    (d1215 : (p 4) → (p 2) → (p 7) → False)
    (d5301 : (¬ p 8) → (¬ p 9) → (p 39) → (p 40) → False)
    (d5235 : (¬ p 78) → (¬ p 39) → (p 80) → (p 41) → False)
    (d5278 : (¬ p 41) → (¬ p 38) → (p 7) → (p 10) → False)
    (d5465 : (p 42) → (p 38) → (p 40) → (p 79) → (¬ p 50) → (¬ p 2) → (p 7) → (p 3) → False)
    (d5463 : (¬ p 42) → (¬ p 90) → (p 79) → (p 76) → (p 51) → (p 7) → (p 3) → (p 10) → (p 4) → (p 80) → (¬ p 9) → (¬ p 49) → False)
    (d5302 : (¬ p 8) → (¬ p 9) → (p 89) → (p 90) → False)
    (d400 : (¬ p 22) → (¬ p 24) → (¬ p 89) → False)
    (d5299 : (¬ p 8) → (¬ p 9) → (p 25) → (p 24) → False)
    (d4970 : (¬ p 39) → (¬ p 42) → (p 27) → (p 24) → False)
    (d5319 : (¬ p 25) → (¬ p 27) → (¬ p 8) → (¬ p 9) → (¬ p 39) → (¬ p 42) → False)
    : (p 40) → (p 79) → (p 76) → (p 51) → (p 7) → (p 3) → (p 10) → (p 4) → (p 80) → (¬ p 9) → (¬ p 49) → False := by
  intro a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10
  have v0 : ¬ p 8 := (fun u => d4354 u a10 a5 a7)
  have v1 : ¬ p 78 := (fun u => d5304 v0 a9 a1 u)
  have v2 : ¬ p 22 := (fun u => d3227 a3 a2 u)
  have v3 : ¬ p 50 := (fun u => d822 u a3 a5)
  have v4 : ¬ p 2 := (fun u => d1215 a7 u a4)
  have v5 : ¬ p 39 := (fun u => d5301 v0 a9 u a0)
  have v6 : ¬ p 41 := (fun u => d5235 v1 v5 a8 u)
  have v7 : p 38 := Classical.byContradiction (fun u => d5278 v6 u a4 a6)
  have v8 : ¬ p 42 := (fun u => d5465 u v7 a0 a1 v3 v4 a4 a5)
  have v9 : p 90 := Classical.byContradiction (fun u => d5463 v8 u a1 a2 a3 a4 a5 a6 a7 a8 a9 a10)
  have v10 : ¬ p 89 := (fun u => d5302 v0 a9 u v9)
  have v11 : p 24 := Classical.byContradiction (fun u => d400 v2 u v10)
  have v12 : ¬ p 25 := (fun u => d5299 v0 a9 u v11)
  have v13 : ¬ p 27 := (fun u => d4970 v5 v8 u v11)
  exact d5319 v12 v13 v0 a9 v5 v8

theorem c5467 (p : Nat → Prop)
    (d5299 : (¬ p 8) → (¬ p 9) → (p 25) → (p 24) → False)
    (d5319 : (¬ p 25) → (¬ p 27) → (¬ p 8) → (¬ p 9) → (¬ p 39) → (¬ p 42) → False)
    (d4970 : (¬ p 39) → (¬ p 42) → (p 27) → (p 24) → False)
    : (¬ p 39) → (¬ p 42) → (p 24) → (¬ p 8) → (¬ p 9) → False := by
  intro a0 a1 a2 a3 a4
  have v0 : ¬ p 25 := (fun u => d5299 a3 a4 u a2)
  have v1 : p 27 := Classical.byContradiction (fun u => d5319 v0 u a3 a4 a0 a1)
  exact d4970 a0 a1 v1 a2

theorem c5468 (p : Nat → Prop)
    (d5213 : (¬ p 14) → (¬ p 15) → (p 30) → (p 31) → False)
    (d2438 : (¬ p 13) → (¬ p 30) → (¬ p 12) → (¬ p 11) → (¬ p 14) → (¬ p 29) → False)
    : (¬ p 14) → (p 31) → (¬ p 29) → (¬ p 11) → (¬ p 13) → (¬ p 12) → (¬ p 15) → False := by
  intro a0 a1 a2 a3 a4 a5 a6
  have v0 : ¬ p 30 := (fun u => d5213 a0 a6 u a1)
  exact d2438 a4 v0 a5 a3 a0 a2

theorem c5469 (p : Nat → Prop)
    (d59 : (p 4) → (p 14) → (p 72) → False)
    (d5356 : (¬ p 2) → (¬ p 18) → (p 14) → (p 30) → False)
    (d5200 : (¬ p 30) → (¬ p 28) → (¬ p 72) → (¬ p 67) → (¬ p 40) → (¬ p 43) → False)
    : (p 14) → (¬ p 67) → (¬ p 43) → (¬ p 28) → (¬ p 18) → (¬ p 40) → (¬ p 2) → (p 4) → False := by
  intro a0 a1 a2 a3 a4 a5 a6 a7
  have v0 : ¬ p 72 := (fun u => d59 a7 a0 u)
  have v1 : ¬ p 30 := (fun u => d5356 a6 a4 a0 u)
  exact d5200 v1 a3 v0 a1 a5 a2

theorem c5470 (p : Nat → Prop)
    (d1530 : (¬ p 18) → (¬ p 35) → (¬ p 2) → (p 4) → False)
    (d4587 : (p 33) → (p 27) → (p 21) → False)
    (d5355 : (¬ p 2) → (¬ p 18) → (p 27) → (p 11) → False)
    (d5390 : (¬ p 138) → (¬ p 87) → (p 27) → (p 21) → False)
    (d5324 : (¬ p 11) → (¬ p 12) → (p 27) → (p 28) → False)
    (d5153 : (¬ p 26) → (¬ p 28) → (p 141) → (p 130) → False)
    (d5190 : (¬ p 13) → (¬ p 12) → (¬ p 26) → (¬ p 28) → (¬ p 41) → (¬ p 44) → False)
    (d1150 : (p 44) → (p 35) → (p 39) → (¬ p 66) → False)
    (d5184 : (¬ p 13) → (¬ p 12) → (p 44) → (p 43) → False)
    (d565 : (p 38) → (p 44) → (p 104) → False)
    (d5303 : (¬ p 8) → (¬ p 9) → (p 67) → (p 66) → False)
    (d4914 : (¬ p 104) → (¬ p 77) → (p 21) → (p 29) → False)
    (d5469 : (p 14) → (¬ p 67) → (¬ p 43) → (¬ p 28) → (¬ p 18) → (¬ p 40) → (¬ p 2) → (p 4) → False)
    (d5216 : (¬ p 14) → (¬ p 15) → (¬ p 43) → (¬ p 141) → (p 45) → False)
    (d5468 : (¬ p 14) → (p 31) → (¬ p 29) → (¬ p 11) → (¬ p 13) → (¬ p 12) → (¬ p 15) → False)
    (d5335 : (¬ p 42) → (¬ p 45) → (p 138) → (p 150) → False)
    (d5351 : (¬ p 31) → (¬ p 33) → (¬ p 150) → (¬ p 45) → (¬ p 43) → (¬ p 141) → False)
    : (p 27) → (p 38) → (¬ p 41) → (¬ p 13) → (¬ p 77) → (p 21) → (¬ p 26) → (¬ p 18) → (p 39) → (¬ p 42) → (¬ p 40) → (¬ p 87) → (¬ p 12) → (¬ p 2) → (¬ p 8) → (¬ p 15) → (p 4) → (p 130) → (¬ p 9) → False := by
  intro a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18
  have v0 : p 35 := Classical.byContradiction (fun u => d1530 a7 u a13 a16)
  have v1 : ¬ p 33 := (fun u => d4587 u a0 a5)
  have v2 : ¬ p 11 := (fun u => d5355 a13 a7 a0 u)
  have v3 : p 138 := Classical.byContradiction (fun u => d5390 u a11 a0 a5)
  have v4 : ¬ p 28 := (fun u => d5324 v2 a12 a0 u)
  have v5 : ¬ p 141 := (fun u => d5153 a6 v4 u a17)
  have v6 : p 44 := Classical.byContradiction (fun u => d5190 a3 a12 a6 v4 a2 u)
  have v7 : p 66 := Classical.byContradiction (fun u => d1150 v6 v0 a8 u)
  have v8 : ¬ p 43 := (fun u => d5184 a3 a12 v6 u)
  have v9 : ¬ p 104 := (fun u => d565 a1 v6 u)
  have v10 : ¬ p 67 := (fun u => d5303 a14 a18 u v7)
  have v11 : ¬ p 29 := (fun u => d4914 v9 a4 a5 u)
  have v12 : ¬ p 14 := (fun u => d5469 u v10 v8 v4 a7 a10 a13 a16)
  have v13 : ¬ p 45 := (fun u => d5216 v12 a15 v8 v5 u)
  have v14 : ¬ p 31 := (fun u => d5468 v12 u v11 v2 a3 a12 a15)
  have v15 : ¬ p 150 := (fun u => d5335 a9 v13 v3 u)
  exact d5351 v14 v1 v15 v13 v8 v5

theorem c5471 (p : Nat → Prop)
    (d5208 : (¬ p 44) → (¬ p 47) → (¬ p 13) → (¬ p 12) → (p 142) → False)
    (d5205 : (¬ p 44) → (¬ p 47) → (¬ p 142) → (¬ p 57) → (p 58) → False)
    : (¬ p 44) → (¬ p 47) → (¬ p 57) → (¬ p 13) → (p 58) → (¬ p 12) → False := by
  intro a0 a1 a2 a3 a4 a5
  have v0 : ¬ p 142 := (fun u => d5208 a0 a1 a3 a5 u)
  exact d5205 a0 a1 v0 a2 a4

theorem c5472 (p : Nat → Prop)
    (d4579 : (p 57) → (p 58) → (p 3) → False)
    (d231 : (p 3) → (p 13) → (p 58) → False)
    (d1215 : (p 4) → (p 2) → (p 7) → False)
    (d5360 : (¬ p 2) → (¬ p 18) → (p 26) → (p 10) → False)
    (d1530 : (¬ p 18) → (¬ p 35) → (¬ p 2) → (p 4) → False)
    (d4556 : (p 12) → (p 4) → (p 7) → False)
    (d373 : (p 10) → (p 15) → (p 130) → False)
    (d5278 : (¬ p 41) → (¬ p 38) → (p 7) → (p 10) → False)
    (d2479 : (p 47) → (p 39) → (p 38) → False)
    (d5470 : (p 27) → (p 38) → (¬ p 41) → (¬ p 13) → (¬ p 77) → (p 21) → (¬ p 26) → (¬ p 18) → (p 39) → (¬ p 42) → (¬ p 40) → (¬ p 87) → (¬ p 12) → (¬ p 2) → (¬ p 8) → (¬ p 15) → (p 4) → (p 130) → (¬ p 9) → False)
    (d5471 : (¬ p 44) → (¬ p 47) → (¬ p 57) → (¬ p 13) → (p 58) → (¬ p 12) → False)
    (d1150 : (p 44) → (p 35) → (p 39) → (¬ p 66) → False)
    (d565 : (p 38) → (p 44) → (p 104) → False)
    (d5303 : (¬ p 8) → (¬ p 9) → (p 67) → (p 66) → False)
    (d4914 : (¬ p 104) → (¬ p 77) → (p 21) → (p 29) → False)
    (d5174 : (¬ p 27) → (¬ p 29) → (p 56) → (p 58) → False)
    (d4948 : (¬ p 102) → (¬ p 56) → (p 7) → (p 3) → False)
    (d931 : (p 38) → (p 105) → (p 102) → False)
    (d5139 : (¬ p 72) → (¬ p 67) → (¬ p 105) → (¬ p 88) → (p 90) → False)
    (d5051 : (¬ p 105) → (¬ p 88) → (p 64) → (p 72) → False)
    : (¬ p 41) → (¬ p 88) → (¬ p 77) → (p 58) → (p 64) → (p 21) → (¬ p 18) → (p 39) → (¬ p 42) → (p 90) → (¬ p 40) → (¬ p 87) → (p 7) → (¬ p 8) → (p 3) → (p 10) → (p 4) → (p 130) → (¬ p 9) → False := by
  intro a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18
  have v0 : ¬ p 57 := (fun u => d4579 u a3 a14)
  have v1 : ¬ p 13 := (fun u => d231 a14 u a3)
  have v2 : ¬ p 2 := (fun u => d1215 a16 u a12)
  have v3 : ¬ p 26 := (fun u => d5360 v2 a6 u a15)
  have v4 : p 35 := Classical.byContradiction (fun u => d1530 a6 u v2 a16)
  have v5 : ¬ p 12 := (fun u => d4556 u a16 a12)
  have v6 : ¬ p 15 := (fun u => d373 a15 u a17)
  have v7 : p 38 := Classical.byContradiction (fun u => d5278 a0 u a12 a15)
  have v8 : ¬ p 47 := (fun u => d2479 u a7 v7)
  have v9 : ¬ p 27 := (fun u => d5470 u v7 a0 v1 a2 a5 v3 a6 a7 a8 a10 a11 v5 v2 a13 v6 a16 a17 a18)
  have v10 : p 44 := Classical.byContradiction (fun u => d5471 u v8 v0 v1 a3 v5)
  have v11 : p 66 := Classical.byContradiction (fun u => d1150 v10 v4 a7 u)
  have v12 : ¬ p 104 := (fun u => d565 v7 v10 u)
  have v13 : ¬ p 67 := (fun u => d5303 a13 a18 u v11)
  have v14 : ¬ p 29 := (fun u => d4914 v12 a2 a5 u)
  have v15 : ¬ p 56 := (fun u => d5174 v9 v14 u a3)
  have v16 : p 102 := Classical.byContradiction (fun u => d4948 u v15 a12 a14)
  have v17 : ¬ p 105 := (fun u => d931 v7 u v16)
  have v18 : p 72 := Classical.byContradiction (fun u => d5139 u v13 v17 a1 a9)
  exact d5051 v17 a1 a4 v18

theorem c5473 (p : Nat → Prop)
    (d59 : (p 4) → (p 14) → (p 72) → False)
    (d5051 : (¬ p 105) → (¬ p 88) → (p 64) → (p 72) → False)
    (d4992 : (¬ p 14) → (¬ p 13) → (p 104) → (p 105) → False)
    : (p 72) → (p 104) → (¬ p 13) → (¬ p 88) → (p 64) → (p 4) → False := by
  intro a0 a1 a2 a3 a4 a5
  have v0 : ¬ p 14 := (fun u => d59 a5 u a0)
  have v1 : p 105 := Classical.byContradiction (fun u => d5051 u a3 a4 a0)
  exact d4992 v0 a2 a1 v1

theorem c5474 (p : Nat → Prop)
    (d5304 : (¬ p 8) → (¬ p 9) → (p 79) → (p 78) → False)
    (d1150 : (p 44) → (p 35) → (p 39) → (¬ p 66) → False)
    (d5184 : (¬ p 13) → (¬ p 12) → (p 44) → (p 43) → False)
    (d5303 : (¬ p 8) → (¬ p 9) → (p 67) → (p 66) → False)
    (d4995 : (¬ p 43) → (¬ p 141) → (p 41) → (p 130) → False)
    (d631 : (p 130) → (p 31) → (p 141) → False)
    (d5186 : (¬ p 13) → (¬ p 12) → (¬ p 31) → (¬ p 29) → (p 141) → False)
    (d2719 : (¬ p 77) → (¬ p 104) → (p 29) → (¬ p 23) → False)
    (d5473 : (p 72) → (p 104) → (¬ p 13) → (¬ p 88) → (p 64) → (p 4) → False)
    (d5308 : (¬ p 8) → (¬ p 9) → (¬ p 72) → (¬ p 67) → (p 114) → False)
    (d5262 : (¬ p 114) → (¬ p 78) → (¬ p 72) → (¬ p 67) → (p 79) → False)
    : (p 44) → (p 41) → (¬ p 13) → (¬ p 88) → (¬ p 77) → (p 64) → (¬ p 23) → (p 35) → (p 39) → (p 79) → (¬ p 12) → (¬ p 8) → (p 4) → (p 130) → (¬ p 9) → False := by
  intro a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14
  have v0 : ¬ p 78 := (fun u => d5304 a11 a14 a9 u)
  have v1 : p 66 := Classical.byContradiction (fun u => d1150 a0 a7 a8 u)
  have v2 : ¬ p 43 := (fun u => d5184 a2 a10 a0 u)
  have v3 : ¬ p 67 := (fun u => d5303 a11 a14 u v1)
  have v4 : p 141 := Classical.byContradiction (fun u => d4995 v2 u a1 a13)
  have v5 : ¬ p 31 := (fun u => d631 a13 u v4)
  have v6 : p 29 := Classical.byContradiction (fun u => d5186 a2 a10 v5 u v4)
  have v7 : p 104 := Classical.byContradiction (fun u => d2719 a4 u v6 a6)
  have v8 : ¬ p 72 := (fun u => d5473 u v7 a2 a3 a5 a12)
  have v9 : ¬ p 114 := (fun u => d5308 a11 a14 v8 v3 u)
  exact d5262 v9 v0 v8 v3 a9

theorem c5475 (p : Nat → Prop)
    (d5304 : (¬ p 8) → (¬ p 9) → (p 79) → (p 78) → False)
    (d5308 : (¬ p 8) → (¬ p 9) → (¬ p 72) → (¬ p 67) → (p 114) → False)
    (d5262 : (¬ p 114) → (¬ p 78) → (¬ p 72) → (¬ p 67) → (p 79) → False)
    : (¬ p 67) → (¬ p 72) → (p 79) → (¬ p 8) → (¬ p 9) → False := by
  intro a0 a1 a2 a3 a4
  have v0 : ¬ p 78 := (fun u => d5304 a3 a4 a2 u)
  have v1 : ¬ p 114 := (fun u => d5308 a3 a4 a1 a0 u)
  exact d5262 v1 v0 a1 a0 a2

theorem c5476 (p : Nat → Prop)
    (d5378 : (¬ p 74) → (¬ p 69) → (p 107) → (p 102) → False)
    (d5380 : (¬ p 74) → (¬ p 69) → (¬ p 142) → (¬ p 57) → (p 56) → False)
    (d4948 : (¬ p 102) → (¬ p 56) → (p 7) → (p 3) → False)
    : (¬ p 69) → (¬ p 142) → (p 107) → (¬ p 74) → (¬ p 57) → (p 7) → (p 3) → False := by
  intro a0 a1 a2 a3 a4 a5 a6
  have v0 : ¬ p 102 := (fun u => d5378 a3 a0 a2 u)
  have v1 : ¬ p 56 := (fun u => d5380 a3 a0 a1 a4 u)
  exact d4948 v0 v1 a5 a6

theorem c5477 (p : Nat → Prop)
    (d4556 : (p 12) → (p 4) → (p 7) → False)
    (d418 : (p 4) → (p 7) → (p 65) → False)
    (d1306 : (p 70) → (p 67) → (p 35) → False)
    (d5294 : (¬ p 70) → (¬ p 65) → (¬ p 40) → (¬ p 43) → (p 100) → False)
    (d5290 : (¬ p 70) → (¬ p 65) → (p 107) → (p 142) → False)
    (d5156 : (¬ p 26) → (¬ p 28) → (p 43) → (p 41) → False)
    (d5476 : (¬ p 69) → (¬ p 142) → (p 107) → (¬ p 74) → (¬ p 57) → (p 7) → (p 3) → False)
    (d22 : (p 4) → (p 11) → (p 69) → False)
    (d5310 : (¬ p 25) → (¬ p 27) → (p 67) → (p 69) → False)
    (d5324 : (¬ p 11) → (¬ p 12) → (p 27) → (p 28) → False)
    : (p 67) → (p 107) → (¬ p 74) → (p 41) → (¬ p 57) → (p 100) → (¬ p 26) → (p 35) → (¬ p 25) → (¬ p 40) → (p 7) → (p 3) → (p 4) → False := by
  intro a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12
  have v0 : ¬ p 12 := (fun u => d4556 u a12 a10)
  have v1 : ¬ p 65 := (fun u => d418 a12 a10 u)
  have v2 : ¬ p 70 := (fun u => d1306 u a0 a7)
  have v3 : p 43 := Classical.byContradiction (fun u => d5294 v2 v1 a9 u a5)
  have v4 : ¬ p 142 := (fun u => d5290 v2 v1 a1 u)
  have v5 : p 28 := Classical.byContradiction (fun u => d5156 a6 u v3 a3)
  have v6 : p 69 := Classical.byContradiction (fun u => d5476 u v4 a1 a2 a4 a10 a11)
  have v7 : ¬ p 11 := (fun u => d22 a12 u v6)
  have v8 : p 27 := Classical.byContradiction (fun u => d5310 a8 u a0 v6)
  exact d5324 v7 v0 v8 v5

theorem c5478 (p : Nat → Prop)
    (d5302 : (¬ p 8) → (¬ p 9) → (p 89) → (p 90) → False)
    (d400 : (¬ p 22) → (¬ p 24) → (¬ p 89) → False)
    (d5299 : (¬ p 8) → (¬ p 9) → (p 25) → (p 24) → False)
    (d4556 : (p 12) → (p 4) → (p 7) → False)
    (d1215 : (p 4) → (p 2) → (p 7) → False)
    (d373 : (p 10) → (p 15) → (p 130) → False)
    (d5467 : (¬ p 39) → (¬ p 42) → (p 24) → (¬ p 8) → (¬ p 9) → False)
    (d127 : (p 18) → (p 24) → (p 39) → False)
    (d5353 : (¬ p 2) → (¬ p 18) → (p 4) → (p 20) → False)
    (d1530 : (¬ p 18) → (¬ p 35) → (¬ p 2) → (p 4) → False)
    (d5360 : (¬ p 2) → (¬ p 18) → (p 26) → (p 10) → False)
    (d5358 : (¬ p 2) → (¬ p 18) → (p 7) → (p 23) → False)
    (d5363 : (¬ p 2) → (¬ p 18) → (¬ p 21) → (¬ p 50) → (p 3) → False)
    (d270 : (¬ p 20) → (¬ p 22) → (¬ p 64) → False)
    (d442 : (¬ p 23) → (¬ p 25) → (¬ p 100) → False)
    (d1519 : (¬ p 54) → (p 21) → (¬ p 58) → (¬ p 50) → (¬ p 23) → False)
    (d264 : (p 77) → (p 79) → (p 100) → False)
    (d175 : (p 88) → (p 90) → (p 100) → False)
    (d231 : (p 3) → (p 13) → (p 58) → False)
    (d4579 : (p 57) → (p 58) → (p 3) → False)
    (d5472 : (¬ p 41) → (¬ p 88) → (¬ p 77) → (p 58) → (p 64) → (p 21) → (¬ p 18) → (p 39) → (¬ p 42) → (p 90) → (¬ p 40) → (¬ p 87) → (p 7) → (¬ p 8) → (p 3) → (p 10) → (p 4) → (p 130) → (¬ p 9) → False)
    (d5298 : (¬ p 8) → (¬ p 9) → (p 100) → (p 99) → False)
    (d5474 : (p 44) → (p 41) → (¬ p 13) → (¬ p 88) → (¬ p 77) → (p 64) → (¬ p 23) → (p 35) → (p 39) → (p 79) → (¬ p 12) → (¬ p 8) → (p 4) → (p 130) → (¬ p 9) → False)
    (d5471 : (¬ p 44) → (¬ p 47) → (¬ p 57) → (¬ p 13) → (p 58) → (¬ p 12) → False)
    (d563 : (p 35) → (p 47) → (p 74) → False)
    (d5124 : (¬ p 107) → (¬ p 99) → (p 39) → (p 47) → False)
    (d353 : (p 7) → (p 16) → (p 107) → False)
    (d5477 : (p 67) → (p 107) → (¬ p 74) → (p 41) → (¬ p 57) → (p 100) → (¬ p 26) → (p 35) → (¬ p 25) → (¬ p 40) → (p 7) → (p 3) → (p 4) → False)
    (d5475 : (¬ p 67) → (¬ p 72) → (p 79) → (¬ p 8) → (¬ p 9) → False)
    (d199 : (p 35) → (p 45) → (p 72) → False)
    (d5333 : (¬ p 42) → (¬ p 45) → (p 72) → (p 69) → False)
    (d5476 : (¬ p 69) → (¬ p 142) → (p 107) → (¬ p 74) → (¬ p 57) → (p 7) → (p 3) → False)
    (d47 : (p 43) → (p 47) → (p 142) → False)
    (d5094 : (¬ p 16) → (¬ p 15) → (p 142) → (p 141) → False)
    (d4995 : (¬ p 43) → (¬ p 141) → (p 41) → (p 130) → False)
    : (¬ p 42) → (¬ p 54) → (p 90) → (¬ p 40) → (p 79) → (¬ p 87) → (¬ p 22) → (¬ p 50) → (p 7) → (¬ p 8) → (p 3) → (p 10) → (p 4) → (p 130) → (¬ p 9) → False := by
  intro a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14
  have v0 : ¬ p 89 := (fun u => d5302 a9 a14 u a2)
  have v1 : p 24 := Classical.byContradiction (fun u => d400 a6 u v0)
  have v2 : ¬ p 25 := (fun u => d5299 a9 a14 u v1)
  have v3 : ¬ p 12 := (fun u => d4556 u a12 a8)
  have v4 : ¬ p 2 := (fun u => d1215 a12 u a8)
  have v5 : ¬ p 15 := (fun u => d373 a11 u a13)
  have v6 : p 39 := Classical.byContradiction (fun u => d5467 u a0 v1 a9 a14)
  have v7 : ¬ p 18 := (fun u => d127 u v1 v6)
  have v8 : ¬ p 20 := (fun u => d5353 v4 v7 a12 u)
  have v9 : p 35 := Classical.byContradiction (fun u => d1530 v7 u v4 a12)
  have v10 : ¬ p 26 := (fun u => d5360 v4 v7 u a11)
  have v11 : ¬ p 23 := (fun u => d5358 v4 v7 a8 u)
  have v12 : p 21 := Classical.byContradiction (fun u => d5363 v4 v7 u a7 a10)
  have v13 : p 64 := Classical.byContradiction (fun u => d270 v8 a6 u)
  have v14 : p 100 := Classical.byContradiction (fun u => d442 v11 v2 u)
  have v15 : p 58 := Classical.byContradiction (fun u => d1519 a1 v12 u a7 v11)
  have v16 : ¬ p 77 := (fun u => d264 u a4 v14)
  have v17 : ¬ p 88 := (fun u => d175 u a2 v14)
  have v18 : ¬ p 13 := (fun u => d231 a10 u v15)
  have v19 : ¬ p 57 := (fun u => d4579 u v15 a10)
  have v20 : p 41 := Classical.byContradiction (fun u => d5472 u v17 v16 v15 v13 v12 v7 v6 a0 a2 a3 a5 a8 a9 a10 a11 a12 a13 a14)
  have v21 : ¬ p 99 := (fun u => d5298 a9 a14 v14 u)
  have v22 : ¬ p 44 := (fun u => d5474 u v20 v18 v17 v16 v13 v11 v9 v6 a4 v3 a9 a12 a13 a14)
  have v23 : p 47 := Classical.byContradiction (fun u => d5471 v22 u v19 v18 v15 v3)
  have v24 : ¬ p 74 := (fun u => d563 v9 v23 u)
  have v25 : p 107 := Classical.byContradiction (fun u => d5124 u v21 v6 v23)
  have v26 : ¬ p 16 := (fun u => d353 a8 u v25)
  have v27 : ¬ p 67 := (fun u => d5477 u v25 v24 v20 v19 v14 v10 v9 v2 a3 a8 a10 a12)
  have v28 : p 72 := Classical.byContradiction (fun u => d5475 v27 u a4 a9 a14)
  have v29 : ¬ p 45 := (fun u => d199 v9 u v28)
  have v30 : ¬ p 69 := (fun u => d5333 a0 v29 v28 u)
  have v31 : p 142 := Classical.byContradiction (fun u => d5476 v30 u v25 v24 v19 a8 a10)
  have v32 : ¬ p 43 := (fun u => d47 u v23 v31)
  have v33 : ¬ p 141 := (fun u => d5094 v26 v5 v31 u)
  exact d4995 v32 v33 v20 a13

theorem c5479 (p : Nat → Prop)
    (d4579 : (p 57) → (p 58) → (p 3) → False)
    (d231 : (p 3) → (p 13) → (p 58) → False)
    (d59 : (p 4) → (p 14) → (p 72) → False)
    (d5302 : (¬ p 8) → (¬ p 9) → (p 89) → (p 90) → False)
    (d400 : (¬ p 22) → (¬ p 24) → (¬ p 89) → False)
    (d5299 : (¬ p 8) → (¬ p 9) → (p 25) → (p 24) → False)
    (d5304 : (¬ p 8) → (¬ p 9) → (p 79) → (p 78) → False)
    (d4556 : (p 12) → (p 4) → (p 7) → False)
    (d1215 : (p 4) → (p 2) → (p 7) → False)
    (d127 : (p 18) → (p 24) → (p 39) → False)
    (d5353 : (¬ p 2) → (¬ p 18) → (p 4) → (p 20) → False)
    (d1530 : (¬ p 18) → (¬ p 35) → (¬ p 2) → (p 4) → False)
    (d5358 : (¬ p 2) → (¬ p 18) → (p 7) → (p 23) → False)
    (d5363 : (¬ p 2) → (¬ p 18) → (¬ p 21) → (¬ p 50) → (p 3) → False)
    (d270 : (¬ p 20) → (¬ p 22) → (¬ p 64) → False)
    (d4613 : (p 47) → (p 35) → (p 42) → False)
    (d442 : (¬ p 23) → (¬ p 25) → (¬ p 100) → False)
    (d5471 : (¬ p 44) → (¬ p 47) → (¬ p 57) → (¬ p 13) → (p 58) → (¬ p 12) → False)
    (d264 : (p 77) → (p 79) → (p 100) → False)
    (d175 : (p 88) → (p 90) → (p 100) → False)
    (d1150 : (p 44) → (p 35) → (p 39) → (¬ p 66) → False)
    (d5474 : (p 44) → (p 41) → (¬ p 13) → (¬ p 88) → (¬ p 77) → (p 64) → (¬ p 23) → (p 35) → (p 39) → (p 79) → (¬ p 12) → (¬ p 8) → (p 4) → (p 130) → (¬ p 9) → False)
    (d5473 : (p 72) → (p 104) → (¬ p 13) → (¬ p 88) → (p 64) → (p 4) → False)
    (d5051 : (¬ p 105) → (¬ p 88) → (p 64) → (p 72) → False)
    (d247 : (p 66) → (p 72) → (p 114) → False)
    (d5278 : (¬ p 41) → (¬ p 38) → (p 7) → (p 10) → False)
    (d4914 : (¬ p 104) → (¬ p 77) → (p 21) → (p 29) → False)
    (d931 : (p 38) → (p 105) → (p 102) → False)
    (d5258 : (¬ p 114) → (¬ p 78) → (p 30) → (p 21) → False)
    (d4948 : (¬ p 102) → (¬ p 56) → (p 7) → (p 3) → False)
    (d2438 : (¬ p 13) → (¬ p 30) → (¬ p 12) → (¬ p 11) → (¬ p 14) → (¬ p 29) → False)
    (d120 : (p 3) → (p 11) → (p 56) → False)
    : (p 39) → (p 58) → (p 72) → (p 42) → (p 90) → (p 79) → (¬ p 22) → (¬ p 50) → (p 7) → (¬ p 8) → (p 3) → (p 10) → (p 4) → (p 130) → (¬ p 9) → False := by
  intro a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14
  have v0 : ¬ p 57 := (fun u => d4579 u a1 a10)
  have v1 : ¬ p 13 := (fun u => d231 a10 u a1)
  have v2 : ¬ p 14 := (fun u => d59 a12 u a2)
  have v3 : ¬ p 89 := (fun u => d5302 a9 a14 u a4)
  have v4 : p 24 := Classical.byContradiction (fun u => d400 a6 u v3)
  have v5 : ¬ p 25 := (fun u => d5299 a9 a14 u v4)
  have v6 : ¬ p 78 := (fun u => d5304 a9 a14 a5 u)
  have v7 : ¬ p 12 := (fun u => d4556 u a12 a8)
  have v8 : ¬ p 2 := (fun u => d1215 a12 u a8)
  have v9 : ¬ p 18 := (fun u => d127 u v4 a0)
  have v10 : ¬ p 20 := (fun u => d5353 v8 v9 a12 u)
  have v11 : p 35 := Classical.byContradiction (fun u => d1530 v9 u v8 a12)
  have v12 : ¬ p 23 := (fun u => d5358 v8 v9 a8 u)
  have v13 : p 21 := Classical.byContradiction (fun u => d5363 v8 v9 u a7 a10)
  have v14 : p 64 := Classical.byContradiction (fun u => d270 v10 a6 u)
  have v15 : ¬ p 47 := (fun u => d4613 u v11 a3)
  have v16 : p 100 := Classical.byContradiction (fun u => d442 v12 v5 u)
  have v17 : p 44 := Classical.byContradiction (fun u => d5471 u v15 v0 v1 a1 v7)
  have v18 : ¬ p 77 := (fun u => d264 u a5 v16)
  have v19 : ¬ p 88 := (fun u => d175 u a4 v16)
  have v20 : p 66 := Classical.byContradiction (fun u => d1150 v17 v11 a0 u)
  have v21 : ¬ p 41 := (fun u => d5474 v17 u v1 v19 v18 v14 v12 v11 a0 a5 v7 a9 a12 a13 a14)
  have v22 : ¬ p 104 := (fun u => d5473 a2 u v1 v19 v14 a12)
  have v23 : p 105 := Classical.byContradiction (fun u => d5051 u v19 v14 a2)
  have v24 : ¬ p 114 := (fun u => d247 v20 a2 u)
  have v25 : p 38 := Classical.byContradiction (fun u => d5278 v21 u a8 a11)
  have v26 : ¬ p 29 := (fun u => d4914 v22 v18 v13 u)
  have v27 : ¬ p 102 := (fun u => d931 v25 v23 u)
  have v28 : ¬ p 30 := (fun u => d5258 v24 v6 u v13)
  have v29 : p 56 := Classical.byContradiction (fun u => d4948 v27 u a8 a10)
  have v30 : p 11 := Classical.byContradiction (fun u => d2438 v1 v28 v7 u v2 v26)
  exact d120 a10 v30 v29

theorem c5480 (p : Nat → Prop)
    (d4613 : (p 47) → (p 35) → (p 42) → False)
    (d199 : (p 35) → (p 45) → (p 72) → False)
    (d5471 : (¬ p 44) → (¬ p 47) → (¬ p 57) → (¬ p 13) → (p 58) → (¬ p 12) → False)
    (d5006 : (¬ p 150) → (¬ p 45) → (p 138) → (p 42) → False)
    (d483 : (p 35) → (p 44) → (p 71) → False)
    (d565 : (p 38) → (p 44) → (p 104) → False)
    (d5011 : (¬ p 143) → (¬ p 70) → (p 72) → (p 150) → False)
    (d3761 : (¬ p 66) → (¬ p 71) → (p 58) → (¬ p 49) → False)
    (d5240 : (¬ p 78) → (¬ p 39) → (¬ p 104) → (¬ p 77) → (p 44) → False)
    (d5115 : (¬ p 57) → (¬ p 53) → (p 66) → (p 70) → False)
    (d264 : (p 77) → (p 79) → (p 100) → False)
    (d4942 : (¬ p 21) → (¬ p 50) → (p 53) → (p 24) → False)
    (d442 : (¬ p 23) → (¬ p 25) → (¬ p 100) → False)
    (d135 : (p 21) → (p 23) → (p 77) → False)
    : (p 35) → (¬ p 143) → (p 38) → (p 138) → (¬ p 39) → (¬ p 57) → (¬ p 13) → (p 58) → (p 72) → (p 42) → (¬ p 25) → (p 24) → (¬ p 78) → (p 79) → (¬ p 50) → (¬ p 12) → (¬ p 49) → False := by
  intro a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16
  have v0 : ¬ p 47 := (fun u => d4613 u a0 a9)
  have v1 : ¬ p 45 := (fun u => d199 a0 u a8)
  have v2 : p 44 := Classical.byContradiction (fun u => d5471 u v0 a5 a6 a7 a15)
  have v3 : p 150 := Classical.byContradiction (fun u => d5006 u v1 a3 a9)
  have v4 : ¬ p 71 := (fun u => d483 a0 v2 u)
  have v5 : ¬ p 104 := (fun u => d565 a2 v2 u)
  have v6 : p 70 := Classical.byContradiction (fun u => d5011 a1 u a8 v3)
  have v7 : p 66 := Classical.byContradiction (fun u => d3761 u v4 a7 a16)
  have v8 : p 77 := Classical.byContradiction (fun u => d5240 a12 a4 v5 u v2)
  have v9 : p 53 := Classical.byContradiction (fun u => d5115 a5 u v7 v6)
  have v10 : ¬ p 100 := (fun u => d264 v8 a13 u)
  have v11 : p 21 := Classical.byContradiction (fun u => d4942 u a14 v9 a11)
  have v12 : p 23 := Classical.byContradiction (fun u => d442 u a10 v10)
  exact d135 v11 v12 v8

theorem c5481 (p : Nat → Prop)
    (d4354 : (p 8) → (¬ p 49) → (p 3) → (p 4) → False)
    (d5302 : (¬ p 8) → (¬ p 9) → (p 89) → (p 90) → False)
    (d400 : (¬ p 22) → (¬ p 24) → (¬ p 89) → False)
    (d5299 : (¬ p 8) → (¬ p 9) → (p 25) → (p 24) → False)
    (d5304 : (¬ p 8) → (¬ p 9) → (p 79) → (p 78) → False)
    (d755 : (p 80) → (p 130) → (¬ p 9) → (p 5) → False)
    (d5453 : (¬ p 10) → (p 130) → (p 80) → (¬ p 9) → False)
    (d798 : (p 6) → (p 10) → (p 3) → False)
    (d213 : (¬ p 5) → (¬ p 6) → (¬ p 76) → False)
    (d4131 : (p 87) → (p 76) → (p 80) → False)
    (d5450 : (p 3) → (p 10) → (¬ p 7) → (p 4) → (¬ p 5) → (¬ p 49) → False)
    (d4556 : (p 12) → (p 4) → (p 7) → False)
    (d1215 : (p 4) → (p 2) → (p 7) → False)
    (d231 : (p 3) → (p 13) → (p 58) → False)
    (d4579 : (p 57) → (p 58) → (p 3) → False)
    (d5479 : (p 39) → (p 58) → (p 72) → (p 42) → (p 90) → (p 79) → (¬ p 22) → (¬ p 50) → (p 7) → (¬ p 8) → (p 3) → (p 10) → (p 4) → (p 130) → (¬ p 9) → False)
    (d5235 : (¬ p 78) → (¬ p 39) → (p 80) → (p 41) → False)
    (d5397 : (¬ p 138) → (¬ p 87) → (¬ p 78) → (¬ p 39) → (p 42) → False)
    (d5278 : (¬ p 41) → (¬ p 38) → (p 7) → (p 10) → False)
    (d149 : (p 38) → (p 42) → (p 102) → False)
    (d4948 : (¬ p 102) → (¬ p 56) → (p 7) → (p 3) → False)
    (d120 : (p 3) → (p 11) → (p 56) → False)
    (d5325 : (¬ p 11) → (¬ p 12) → (p 143) → (p 138) → False)
    (d5480 : (p 35) → (¬ p 143) → (p 38) → (p 138) → (¬ p 39) → (¬ p 57) → (¬ p 13) → (p 58) → (p 72) → (p 42) → (¬ p 25) → (p 24) → (¬ p 78) → (p 79) → (¬ p 50) → (¬ p 12) → (¬ p 49) → False)
    (d1530 : (¬ p 18) → (¬ p 35) → (¬ p 2) → (p 4) → False)
    (d582 : (p 18) → (p 27) → (p 42) → False)
    (d5439 : (p 21) → (p 80) → (¬ p 39) → (p 18) → False)
    (d5330 : (¬ p 11) → (¬ p 12) → (¬ p 13) → (¬ p 27) → (¬ p 29) → False)
    (d4943 : (¬ p 21) → (¬ p 50) → (p 58) → (p 29) → False)
    : (p 58) → (p 72) → (p 42) → (p 90) → (p 79) → (¬ p 22) → (¬ p 50) → (p 3) → (p 4) → (p 130) → (p 80) → (¬ p 9) → (¬ p 49) → False := by
  intro a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12
  have v0 : ¬ p 8 := (fun u => d4354 u a12 a7 a8)
  have v1 : ¬ p 89 := (fun u => d5302 v0 a11 u a3)
  have v2 : p 24 := Classical.byContradiction (fun u => d400 a5 u v1)
  have v3 : ¬ p 25 := (fun u => d5299 v0 a11 u v2)
  have v4 : ¬ p 78 := (fun u => d5304 v0 a11 a4 u)
  have v5 : ¬ p 5 := (fun u => d755 a10 a9 a11 u)
  have v6 : p 10 := Classical.byContradiction (fun u => d5453 u a9 a10 a11)
  have v7 : ¬ p 6 := (fun u => d798 u v6 a7)
  have v8 : p 76 := Classical.byContradiction (fun u => d213 v5 v7 u)
  have v9 : ¬ p 87 := (fun u => d4131 u v8 a10)
  have v10 : p 7 := Classical.byContradiction (fun u => d5450 a7 v6 u a8 v5 a12)
  have v11 : ¬ p 12 := (fun u => d4556 u a8 v10)
  have v12 : ¬ p 2 := (fun u => d1215 a8 u v10)
  have v13 : ¬ p 13 := (fun u => d231 a7 u a0)
  have v14 : ¬ p 57 := (fun u => d4579 u a0 a7)
  have v15 : ¬ p 39 := (fun u => d5479 u a0 a1 a2 a3 a4 a5 a6 v10 v0 a7 v6 a8 a9 a11)
  have v16 : ¬ p 41 := (fun u => d5235 v4 v15 a10 u)
  have v17 : p 138 := Classical.byContradiction (fun u => d5397 u v9 v4 v15 a2)
  have v18 : p 38 := Classical.byContradiction (fun u => d5278 v16 u v10 v6)
  have v19 : ¬ p 102 := (fun u => d149 v18 a2 u)
  have v20 : p 56 := Classical.byContradiction (fun u => d4948 v19 u v10 a7)
  have v21 : ¬ p 11 := (fun u => d120 a7 u v20)
  have v22 : ¬ p 143 := (fun u => d5325 v21 v11 u v17)
  have v23 : ¬ p 35 := (fun u => d5480 u v22 v18 v17 v15 v14 v13 a0 a1 a2 v3 v2 v4 a4 a6 v11 a12)
  have v24 : p 18 := Classical.byContradiction (fun u => d1530 u v23 v12 a8)
  have v25 : ¬ p 27 := (fun u => d582 v24 u a2)
  have v26 : ¬ p 21 := (fun u => d5439 u a10 v15 v24)
  have v27 : p 29 := Classical.byContradiction (fun u => d5330 v21 v11 v13 v25 u)
  exact d4943 v26 a6 a0 v27

theorem c5483 (p : Nat → Prop)
    (d5358 : (¬ p 2) → (¬ p 18) → (p 7) → (p 23) → False)
    (d5363 : (¬ p 2) → (¬ p 18) → (¬ p 21) → (¬ p 50) → (p 3) → False)
    (d1519 : (¬ p 54) → (p 21) → (¬ p 58) → (¬ p 50) → (¬ p 23) → False)
    : (¬ p 18) → (¬ p 58) → (¬ p 54) → (¬ p 50) → (¬ p 2) → (p 7) → (p 3) → False := by
  intro a0 a1 a2 a3 a4 a5 a6
  have v0 : ¬ p 23 := (fun u => d5358 a4 a0 a5 u)
  have v1 : p 21 := Classical.byContradiction (fun u => d5363 a4 a0 u a3 a6)
  exact d1519 a2 v1 a1 a3 v0

theorem c5484 (p : Nat → Prop)
    (d5483 : (¬ p 18) → (¬ p 58) → (¬ p 54) → (¬ p 50) → (¬ p 2) → (p 7) → (p 3) → False)
    (d582 : (p 18) → (p 27) → (p 42) → False)
    (d1849 : (p 21) → (p 76) → (p 18) → (¬ p 89) → False)
    (d127 : (p 18) → (p 24) → (p 39) → False)
    (d5318 : (¬ p 25) → (¬ p 27) → (¬ p 29) → (¬ p 54) → (¬ p 58) → False)
    (d4942 : (¬ p 21) → (¬ p 50) → (p 53) → (p 24) → False)
    (d5235 : (¬ p 78) → (¬ p 39) → (p 80) → (p 41) → False)
    (d284 : (p 18) → (p 29) → (p 44) → False)
    (d889 : (p 26) → (p 29) → (p 18) → False)
    (d5085 : (¬ p 41) → (¬ p 44) → (p 13) → (p 10) → False)
    (d5190 : (¬ p 13) → (¬ p 12) → (¬ p 26) → (¬ p 28) → (¬ p 41) → (¬ p 44) → False)
    (d4938 : (¬ p 21) → (¬ p 50) → (p 57) → (p 28) → False)
    (d5111 : (¬ p 57) → (¬ p 53) → (p 28) → (p 24) → False)
    : (¬ p 58) → (p 42) → (¬ p 25) → (p 24) → (¬ p 89) → (¬ p 54) → (¬ p 78) → (¬ p 50) → (p 76) → (¬ p 12) → (¬ p 2) → (p 7) → (p 3) → (p 10) → (p 80) → False := by
  intro a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14
  have v0 : p 18 := Classical.byContradiction (fun u => d5483 u a0 a5 a7 a10 a11 a12)
  have v1 : ¬ p 27 := (fun u => d582 v0 u a1)
  have v2 : ¬ p 21 := (fun u => d1849 u a8 v0 a4)
  have v3 : ¬ p 39 := (fun u => d127 v0 a3 u)
  have v4 : p 29 := Classical.byContradiction (fun u => d5318 a2 v1 u a5 a0)
  have v5 : ¬ p 53 := (fun u => d4942 v2 a7 u a3)
  have v6 : ¬ p 41 := (fun u => d5235 a6 v3 a14 u)
  have v7 : ¬ p 44 := (fun u => d284 v0 v4 u)
  have v8 : ¬ p 26 := (fun u => d889 u v4 v0)
  have v9 : ¬ p 13 := (fun u => d5085 v6 v7 u a13)
  have v10 : p 28 := Classical.byContradiction (fun u => d5190 v9 a9 v8 u v6 v7)
  have v11 : ¬ p 57 := (fun u => d4938 v2 a7 u v10)
  exact d5111 v11 v5 v10 a3

theorem c5485 (p : Nat → Prop)
    (d5453 : (¬ p 10) → (p 130) → (p 80) → (¬ p 9) → False)
    (d755 : (p 80) → (p 130) → (¬ p 9) → (p 5) → False)
    (d5450 : (p 3) → (p 10) → (¬ p 7) → (p 4) → (¬ p 5) → (¬ p 49) → False)
    (d798 : (p 6) → (p 10) → (p 3) → False)
    (d213 : (¬ p 5) → (¬ p 6) → (¬ p 76) → False)
    (d5459 : (¬ p 79) → (p 51) → (p 3) → (p 4) → (p 130) → (p 80) → (¬ p 9) → (¬ p 49) → False)
    (d5466 : (p 40) → (p 79) → (p 76) → (p 51) → (p 7) → (p 3) → (p 10) → (p 4) → (p 80) → (¬ p 9) → (¬ p 49) → False)
    (d4354 : (p 8) → (¬ p 49) → (p 3) → (p 4) → False)
    (d5304 : (¬ p 8) → (¬ p 9) → (p 79) → (p 78) → False)
    (d4131 : (p 87) → (p 76) → (p 80) → False)
    (d3227 : (p 51) → (p 76) → (p 22) → False)
    (d822 : (p 50) → (p 51) → (p 3) → False)
    (d4556 : (p 12) → (p 4) → (p 7) → False)
    (d1215 : (p 4) → (p 2) → (p 7) → False)
    (d17 : (p 51) → (p 54) → (p 90) → False)
    (d5302 : (¬ p 8) → (¬ p 9) → (p 89) → (p 90) → False)
    (d400 : (¬ p 22) → (¬ p 24) → (¬ p 89) → False)
    (d5299 : (¬ p 8) → (¬ p 9) → (p 25) → (p 24) → False)
    (d5478 : (¬ p 42) → (¬ p 54) → (p 90) → (¬ p 40) → (p 79) → (¬ p 87) → (¬ p 22) → (¬ p 50) → (p 7) → (¬ p 8) → (p 3) → (p 10) → (p 4) → (p 130) → (¬ p 9) → False)
    (d5484 : (¬ p 58) → (p 42) → (¬ p 25) → (p 24) → (¬ p 89) → (¬ p 54) → (¬ p 78) → (¬ p 50) → (p 76) → (¬ p 12) → (¬ p 2) → (p 7) → (p 3) → (p 10) → (p 80) → False)
    (d231 : (p 3) → (p 13) → (p 58) → False)
    (d4579 : (p 57) → (p 58) → (p 3) → False)
    (d5481 : (p 58) → (p 72) → (p 42) → (p 90) → (p 79) → (¬ p 22) → (¬ p 50) → (p 3) → (p 4) → (p 130) → (p 80) → (¬ p 9) → (¬ p 49) → False)
    (d5475 : (¬ p 67) → (¬ p 72) → (p 79) → (¬ p 8) → (¬ p 9) → False)
    (d5303 : (¬ p 8) → (¬ p 9) → (p 67) → (p 66) → False)
    (d273 : (¬ p 49) → (¬ p 53) → (¬ p 66) → False)
    (d3761 : (¬ p 66) → (¬ p 71) → (p 58) → (¬ p 49) → False)
    (d4942 : (¬ p 21) → (¬ p 50) → (p 53) → (p 24) → False)
    (d1425 : (p 18) → (p 24) → (p 21) → False)
    (d1530 : (¬ p 18) → (¬ p 35) → (¬ p 2) → (p 4) → False)
    (d4613 : (p 47) → (p 35) → (p 42) → False)
    (d483 : (p 35) → (p 44) → (p 71) → False)
    (d5471 : (¬ p 44) → (¬ p 47) → (¬ p 57) → (¬ p 13) → (p 58) → (¬ p 12) → False)
    : (p 90) → (p 51) → (p 3) → (p 4) → (p 130) → (p 80) → (¬ p 9) → (¬ p 49) → False := by
  intro a0 a1 a2 a3 a4 a5 a6 a7
  have v0 : p 10 := Classical.byContradiction (fun u => d5453 u a4 a5 a6)
  have v1 : ¬ p 5 := (fun u => d755 a5 a4 a6 u)
  have v2 : p 7 := Classical.byContradiction (fun u => d5450 a2 v0 u a3 v1 a7)
  have v3 : ¬ p 6 := (fun u => d798 u v0 a2)
  have v4 : p 76 := Classical.byContradiction (fun u => d213 v1 v3 u)
  have v5 : p 79 := Classical.byContradiction (fun u => d5459 u a1 a2 a3 a4 a5 a6 a7)
  have v6 : ¬ p 40 := (fun u => d5466 u v5 v4 a1 v2 a2 v0 a3 a5 a6 a7)
  have v7 : ¬ p 8 := (fun u => d4354 u a7 a2 a3)
  have v8 : ¬ p 78 := (fun u => d5304 v7 a6 v5 u)
  have v9 : ¬ p 87 := (fun u => d4131 u v4 a5)
  have v10 : ¬ p 22 := (fun u => d3227 a1 v4 u)
  have v11 : ¬ p 50 := (fun u => d822 u a1 a2)
  have v12 : ¬ p 12 := (fun u => d4556 u a3 v2)
  have v13 : ¬ p 2 := (fun u => d1215 a3 u v2)
  have v14 : ¬ p 54 := (fun u => d17 a1 u a0)
  have v15 : ¬ p 89 := (fun u => d5302 v7 a6 u a0)
  have v16 : p 24 := Classical.byContradiction (fun u => d400 v10 u v15)
  have v17 : ¬ p 25 := (fun u => d5299 v7 a6 u v16)
  have v18 : p 42 := Classical.byContradiction (fun u => d5478 u v14 a0 v6 v5 v9 v10 v11 v2 v7 a2 v0 a3 a4 a6)
  have v19 : p 58 := Classical.byContradiction (fun u => d5484 u v18 v17 v16 v15 v14 v8 v11 v4 v12 v13 v2 a2 v0 a5)
  have v20 : ¬ p 13 := (fun u => d231 a2 u v19)
  have v21 : ¬ p 57 := (fun u => d4579 u v19 a2)
  have v22 : ¬ p 72 := (fun u => d5481 v19 u v18 a0 v5 v10 v11 a2 a3 a4 a5 a6 a7)
  have v23 : p 67 := Classical.byContradiction (fun u => d5475 u v22 v5 v7 a6)
  have v24 : ¬ p 66 := (fun u => d5303 v7 a6 v23 u)
  have v25 : p 53 := Classical.byContradiction (fun u => d273 a7 u v24)
  have v26 : p 71 := Classical.byContradiction (fun u => d3761 v24 u v19 a7)
  have v27 : p 21 := Classical.byContradiction (fun u => d4942 u v11 v25 v16)
  have v28 : ¬ p 18 := (fun u => d1425 u v16 v27)
  have v29 : p 35 := Classical.byContradiction (fun u => d1530 v28 u v13 a3)
  have v30 : ¬ p 47 := (fun u => d4613 u v29 v18)
  have v31 : ¬ p 44 := (fun u => d483 v29 u v26)
  exact d5471 v31 v30 v21 v20 v19 v12

theorem c5486 (p : Nat → Prop)
    (d5453 : (¬ p 10) → (p 130) → (p 80) → (¬ p 9) → False)
    (d755 : (p 80) → (p 130) → (¬ p 9) → (p 5) → False)
    (d20 : (¬ p 4) → (¬ p 5) → (¬ p 63) → False)
    (d4354 : (p 8) → (¬ p 49) → (p 3) → (p 4) → False)
    (d5450 : (p 3) → (p 10) → (¬ p 7) → (p 4) → (¬ p 5) → (¬ p 49) → False)
    (d798 : (p 6) → (p 10) → (p 3) → False)
    (d4886 : (¬ p 51) → (¬ p 63) → (p 10) → (p 4) → (p 3) → False)
    (d1215 : (p 4) → (p 2) → (p 7) → False)
    (d213 : (¬ p 5) → (¬ p 6) → (¬ p 76) → False)
    (d5459 : (¬ p 79) → (p 51) → (p 3) → (p 4) → (p 130) → (p 80) → (¬ p 9) → (¬ p 49) → False)
    (d5304 : (¬ p 8) → (¬ p 9) → (p 79) → (p 78) → False)
    (d5466 : (p 40) → (p 79) → (p 76) → (p 51) → (p 7) → (p 3) → (p 10) → (p 4) → (p 80) → (¬ p 9) → (¬ p 49) → False)
    (d5485 : (p 90) → (p 51) → (p 3) → (p 4) → (p 130) → (p 80) → (¬ p 9) → (¬ p 49) → False)
    (d5463 : (¬ p 42) → (¬ p 90) → (p 79) → (p 76) → (p 51) → (p 7) → (p 3) → (p 10) → (p 4) → (p 80) → (¬ p 9) → (¬ p 49) → False)
    (d10 : (¬ p 37) → (¬ p 40) → (¬ p 90) → False)
    (d2715 : (p 37) → (p 42) → (p 35) → False)
    (d5460 : (p 37) → (p 18) → (¬ p 78) → (p 76) → False)
    (d1530 : (¬ p 18) → (¬ p 35) → (¬ p 2) → (p 4) → False)
    : (p 3) → (p 130) → (p 80) → (¬ p 63) → (¬ p 9) → (¬ p 49) → False := by
  intro a0 a1 a2 a3 a4 a5
  have v0 : p 10 := Classical.byContradiction (fun u => d5453 u a1 a2 a4)
  have v1 : ¬ p 5 := (fun u => d755 a2 a1 a4 u)
  have v2 : p 4 := Classical.byContradiction (fun u => d20 u v1 a3)
  have v3 : ¬ p 8 := (fun u => d4354 u a5 a0 v2)
  have v4 : p 7 := Classical.byContradiction (fun u => d5450 a0 v0 u v2 v1 a5)
  have v5 : ¬ p 6 := (fun u => d798 u v0 a0)
  have v6 : p 51 := Classical.byContradiction (fun u => d4886 u a3 v0 v2 a0)
  have v7 : ¬ p 2 := (fun u => d1215 v2 u v4)
  have v8 : p 76 := Classical.byContradiction (fun u => d213 v1 v5 u)
  have v9 : p 79 := Classical.byContradiction (fun u => d5459 u v6 a0 v2 a1 a2 a4 a5)
  have v10 : ¬ p 78 := (fun u => d5304 v3 a4 v9 u)
  have v11 : ¬ p 40 := (fun u => d5466 u v9 v8 v6 v4 a0 v0 v2 a2 a4 a5)
  have v12 : ¬ p 90 := (fun u => d5485 u v6 a0 v2 a1 a2 a4 a5)
  have v13 : p 42 := Classical.byContradiction (fun u => d5463 u v12 v9 v8 v6 v4 a0 v0 v2 a2 a4 a5)
  have v14 : p 37 := Classical.byContradiction (fun u => d10 u v11 v12)
  have v15 : ¬ p 35 := (fun u => d2715 v14 v13 u)
  have v16 : ¬ p 18 := (fun u => d5460 v14 u v10 v8)
  exact d1530 v16 v15 v7 v2

theorem c5487 (p : Nat → Prop)
    (d5304 : (¬ p 8) → (¬ p 9) → (p 79) → (p 78) → False)
    (d5301 : (¬ p 8) → (¬ p 9) → (p 39) → (p 40) → False)
    (d5235 : (¬ p 78) → (¬ p 39) → (p 80) → (p 41) → False)
    : (¬ p 8) → (p 40) → (p 41) → (p 79) → (p 80) → (¬ p 9) → False := by
  intro a0 a1 a2 a3 a4 a5
  have v0 : ¬ p 78 := (fun u => d5304 a0 a5 a3 u)
  have v1 : ¬ p 39 := (fun u => d5301 a0 a5 u a1)
  exact d5235 v0 v1 a4 a2

theorem c5488 (p : Nat → Prop)
    (d5486 : (p 3) → (p 130) → (p 80) → (¬ p 63) → (¬ p 9) → (¬ p 49) → False)
    (d755 : (p 80) → (p 130) → (¬ p 9) → (p 5) → False)
    (d20 : (¬ p 4) → (¬ p 5) → (¬ p 63) → False)
    (d1215 : (p 4) → (p 2) → (p 7) → False)
    (d505 : (¬ p 2) → (¬ p 3) → (¬ p 34) → False)
    (d5453 : (¬ p 10) → (p 130) → (p 80) → (¬ p 9) → False)
    (d5440 : (p 7) → (¬ p 3) → (p 4) → (¬ p 35) → (p 42) → False)
    (d1134 : (p 34) → (p 38) → (p 42) → False)
    (d2715 : (p 37) → (p 42) → (p 35) → False)
    (d5278 : (¬ p 41) → (¬ p 38) → (p 7) → (p 10) → False)
    (d10 : (¬ p 37) → (¬ p 40) → (¬ p 90) → False)
    (d873 : (p 54) → (p 51) → (p 34) → (¬ p 37) → False)
    (d844 : (p 40) → (p 18) → (p 42) → False)
    (d5360 : (¬ p 2) → (¬ p 18) → (p 26) → (p 10) → False)
    (d5487 : (¬ p 8) → (p 40) → (p 41) → (p 79) → (p 80) → (¬ p 9) → False)
    (d3727 : (¬ p 49) → (¬ p 53) → (¬ p 54) → (p 8) → (p 80) → (¬ p 63) → False)
    (d5102 : (¬ p 24) → (¬ p 26) → (p 8) → (p 10) → False)
    (d1263 : (p 24) → (p 53) → (p 78) → False)
    (d4601 : (p 39) → (p 53) → (p 8) → False)
    (d5235 : (¬ p 78) → (¬ p 39) → (p 80) → (p 41) → False)
    : (p 42) → (¬ p 90) → (p 51) → (p 79) → (p 7) → (p 130) → (p 80) → (¬ p 63) → (¬ p 9) → (¬ p 49) → False := by
  intro a0 a1 a2 a3 a4 a5 a6 a7 a8 a9
  have v0 : ¬ p 3 := (fun u => d5486 u a5 a6 a7 a8 a9)
  have v1 : ¬ p 5 := (fun u => d755 a6 a5 a8 u)
  have v2 : p 4 := Classical.byContradiction (fun u => d20 u v1 a7)
  have v3 : ¬ p 2 := (fun u => d1215 v2 u a4)
  have v4 : p 34 := Classical.byContradiction (fun u => d505 v3 v0 u)
  have v5 : p 10 := Classical.byContradiction (fun u => d5453 u a5 a6 a8)
  have v6 : p 35 := Classical.byContradiction (fun u => d5440 a4 v0 v2 u a0)
  have v7 : ¬ p 38 := (fun u => d1134 v4 u a0)
  have v8 : ¬ p 37 := (fun u => d2715 u a0 v6)
  have v9 : p 41 := Classical.byContradiction (fun u => d5278 u v7 a4 v5)
  have v10 : p 40 := Classical.byContradiction (fun u => d10 v8 u a1)
  have v11 : ¬ p 54 := (fun u => d873 u a2 v4 v8)
  have v12 : ¬ p 18 := (fun u => d844 v10 u a0)
  have v13 : ¬ p 26 := (fun u => d5360 v3 v12 u v5)
  have v14 : p 8 := Classical.byContradiction (fun u => d5487 u v10 v9 a3 a6 a8)
  have v15 : p 53 := Classical.byContradiction (fun u => d3727 a9 u v11 v14 a6 a7)
  have v16 : p 24 := Classical.byContradiction (fun u => d5102 u v13 v14 v5)
  have v17 : ¬ p 78 := (fun u => d1263 v16 v15 u)
  have v18 : ¬ p 39 := (fun u => d4601 u v15 v14)
  exact d5235 v17 v18 a6 v9

theorem c5489 (p : Nat → Prop)
    (d4601 : (p 39) → (p 53) → (p 8) → False)
    (d5235 : (¬ p 78) → (¬ p 39) → (p 80) → (p 41) → False)
    (d859 : (p 34) → (p 53) → (p 18) → (¬ p 78) → False)
    (d5278 : (¬ p 41) → (¬ p 38) → (p 7) → (p 10) → False)
    (d5360 : (¬ p 2) → (¬ p 18) → (p 26) → (p 10) → False)
    (d5358 : (¬ p 2) → (¬ p 18) → (p 7) → (p 23) → False)
    (d541 : (p 38) → (p 40) → (p 100) → False)
    (d5102 : (¬ p 24) → (¬ p 26) → (p 8) → (p 10) → False)
    (d442 : (¬ p 23) → (¬ p 25) → (¬ p 100) → False)
    (d4631 : (p 53) → (p 24) → (¬ p 21) → (p 34) → False)
    (d424 : (p 21) → (p 25) → (p 79) → False)
    : (¬ p 78) → (p 40) → (p 53) → (p 8) → (p 79) → (p 34) → (¬ p 2) → (p 7) → (p 10) → (p 80) → False := by
  intro a0 a1 a2 a3 a4 a5 a6 a7 a8 a9
  have v0 : ¬ p 39 := (fun u => d4601 u a2 a3)
  have v1 : ¬ p 41 := (fun u => d5235 a0 v0 a9 u)
  have v2 : ¬ p 18 := (fun u => d859 a5 a2 u a0)
  have v3 : p 38 := Classical.byContradiction (fun u => d5278 v1 u a7 a8)
  have v4 : ¬ p 26 := (fun u => d5360 a6 v2 u a8)
  have v5 : ¬ p 23 := (fun u => d5358 a6 v2 a7 u)
  have v6 : ¬ p 100 := (fun u => d541 v3 a1 u)
  have v7 : p 24 := Classical.byContradiction (fun u => d5102 u v4 a3 a8)
  have v8 : p 25 := Classical.byContradiction (fun u => d442 v5 u v6)
  have v9 : p 21 := Classical.byContradiction (fun u => d4631 a2 v7 u a5)
  exact d424 v9 v8 a4

theorem c5490 (p : Nat → Prop)
    (d356 : (p 51) → (p 53) → (p 89) → False)
    (d4536 : (p 78) → (p 80) → (p 21) → False)
    (d1263 : (p 24) → (p 53) → (p 78) → False)
    (d4939 : (¬ p 21) → (¬ p 50) → (p 22) → (p 51) → False)
    (d400 : (¬ p 22) → (¬ p 24) → (¬ p 89) → False)
    : (p 78) → (¬ p 50) → (p 53) → (p 51) → (p 80) → False := by
  intro a0 a1 a2 a3 a4
  have v0 : ¬ p 89 := (fun u => d356 a3 a2 u)
  have v1 : ¬ p 21 := (fun u => d4536 a0 a4 u)
  have v2 : ¬ p 24 := (fun u => d1263 u a2 a0)
  have v3 : ¬ p 22 := (fun u => d4939 v1 a1 u a3)
  exact d400 v3 v2 v0

theorem c5491 (p : Nat → Prop)
    (d1215 : (p 4) → (p 2) → (p 7) → False)
    (d505 : (¬ p 2) → (¬ p 3) → (¬ p 34) → False)
    (d3743 : (¬ p 49) → (¬ p 3) → (¬ p 53) → (p 8) → False)
    (d4601 : (p 39) → (p 53) → (p 8) → False)
    (d2710 : (p 53) → (p 50) → (p 34) → False)
    (d5490 : (p 78) → (¬ p 50) → (p 53) → (p 51) → (p 80) → False)
    (d859 : (p 34) → (p 53) → (p 18) → (¬ p 78) → False)
    (d5489 : (¬ p 78) → (p 40) → (p 53) → (p 8) → (p 79) → (p 34) → (¬ p 2) → (p 7) → (p 10) → (p 80) → False)
    (d5353 : (¬ p 2) → (¬ p 18) → (p 4) → (p 20) → False)
    (d10 : (¬ p 37) → (¬ p 40) → (¬ p 90) → False)
    (d5232 : (¬ p 78) → (¬ p 39) → (p 37) → (p 76) → False)
    (d4619 : (p 6) → (p 37) → (¬ p 20) → (¬ p 18) → False)
    (d213 : (¬ p 5) → (¬ p 6) → (¬ p 76) → False)
    : (p 8) → (¬ p 90) → (p 51) → (p 79) → (p 7) → (¬ p 3) → (p 10) → (p 4) → (¬ p 5) → (p 80) → (¬ p 49) → False := by
  intro a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10
  have v0 : ¬ p 2 := (fun u => d1215 a7 u a4)
  have v1 : p 34 := Classical.byContradiction (fun u => d505 v0 a5 u)
  have v2 : p 53 := Classical.byContradiction (fun u => d3743 a10 a5 u a0)
  have v3 : ¬ p 39 := (fun u => d4601 u v2 a0)
  have v4 : ¬ p 50 := (fun u => d2710 v2 u v1)
  have v5 : ¬ p 78 := (fun u => d5490 u v4 v2 a2 a9)
  have v6 : ¬ p 18 := (fun u => d859 v1 v2 u v5)
  have v7 : ¬ p 40 := (fun u => d5489 v5 u v2 a0 a3 v1 v0 a4 a6 a9)
  have v8 : ¬ p 20 := (fun u => d5353 v0 v6 a7 u)
  have v9 : p 37 := Classical.byContradiction (fun u => d10 u v7 a1)
  have v10 : ¬ p 76 := (fun u => d5232 v5 v3 v9 u)
  have v11 : ¬ p 6 := (fun u => d4619 u v9 v8 v6)
  exact d213 a8 v11 v10

theorem c5492 (p : Nat → Prop)
    (d351 : (p 34) → (p 39) → (p 53) → False)
    (d859 : (p 34) → (p 53) → (p 18) → (¬ p 78) → False)
    (d5232 : (¬ p 78) → (¬ p 39) → (p 37) → (p 76) → False)
    (d5353 : (¬ p 2) → (¬ p 18) → (p 4) → (p 20) → False)
    (d213 : (¬ p 5) → (¬ p 6) → (¬ p 76) → False)
    (d4619 : (p 6) → (p 37) → (¬ p 20) → (¬ p 18) → False)
    : (p 53) → (p 37) → (¬ p 78) → (p 34) → (¬ p 2) → (p 4) → (¬ p 5) → False := by
  intro a0 a1 a2 a3 a4 a5 a6
  have v0 : ¬ p 39 := (fun u => d351 a3 u a0)
  have v1 : ¬ p 18 := (fun u => d859 a3 a0 u a2)
  have v2 : ¬ p 76 := (fun u => d5232 a2 v0 a1 u)
  have v3 : ¬ p 20 := (fun u => d5353 a4 v1 a5 u)
  have v4 : p 6 := Classical.byContradiction (fun u => d213 a6 u v2)
  exact d4619 v4 a1 v3 v1

theorem c5493 (p : Nat → Prop)
    (d20 : (¬ p 4) → (¬ p 5) → (¬ p 63) → False)
    (d5236 : (¬ p 78) → (¬ p 39) → (p 50) → (p 34) → False)
    (d5232 : (¬ p 78) → (¬ p 39) → (p 37) → (p 76) → False)
    (d213 : (¬ p 5) → (¬ p 6) → (¬ p 76) → False)
    (d32 : (p 4) → (p 6) → (p 64) → False)
    (d4001 : (¬ p 63) → (¬ p 5) → (p 6) → (p 37) → (¬ p 68) → (p 21) → (¬ p 2) → False)
    (d4640 : (¬ p 64) → (p 37) → (p 6) → (¬ p 20) → False)
    (d4940 : (¬ p 21) → (¬ p 50) → (p 34) → (p 18) → False)
    (d5353 : (¬ p 2) → (¬ p 18) → (p 4) → (p 20) → False)
    : (¬ p 39) → (p 37) → (¬ p 78) → (p 34) → (¬ p 2) → (¬ p 68) → (¬ p 5) → (¬ p 63) → False := by
  intro a0 a1 a2 a3 a4 a5 a6 a7
  have v0 : p 4 := Classical.byContradiction (fun u => d20 u a6 a7)
  have v1 : ¬ p 50 := (fun u => d5236 a2 a0 u a3)
  have v2 : ¬ p 76 := (fun u => d5232 a2 a0 a1 u)
  have v3 : p 6 := Classical.byContradiction (fun u => d213 a6 u v2)
  have v4 : ¬ p 64 := (fun u => d32 v0 v3 u)
  have v5 : ¬ p 21 := (fun u => d4001 a7 a6 v3 a1 a5 u a4)
  have v6 : p 20 := Classical.byContradiction (fun u => d4640 v4 a1 v3 u)
  have v7 : ¬ p 18 := (fun u => d4940 v5 v1 a3 u)
  exact d5353 a4 v7 v0 v6

theorem c5494 (p : Nat → Prop)
    (d20 : (¬ p 4) → (¬ p 5) → (¬ p 63) → False)
    (d5492 : (p 53) → (p 37) → (¬ p 78) → (p 34) → (¬ p 2) → (p 4) → (¬ p 5) → False)
    (d273 : (¬ p 49) → (¬ p 53) → (¬ p 66) → False)
    (d5493 : (¬ p 39) → (p 37) → (¬ p 78) → (p 34) → (¬ p 2) → (¬ p 68) → (¬ p 5) → (¬ p 63) → False)
    (d668 : (p 18) → (p 39) → (p 37) → False)
    (d5353 : (¬ p 2) → (¬ p 18) → (p 4) → (p 20) → False)
    (d5457 : (¬ p 18) → (¬ p 42) → (p 66) → (¬ p 90) → (¬ p 22) → (¬ p 2) → (¬ p 8) → (p 4) → (¬ p 9) → False)
    (d4619 : (p 6) → (p 37) → (¬ p 20) → (¬ p 18) → False)
    (d3227 : (p 51) → (p 76) → (p 22) → False)
    (d213 : (¬ p 5) → (¬ p 6) → (¬ p 76) → False)
    : (p 37) → (¬ p 78) → (¬ p 8) → (¬ p 42) → (¬ p 90) → (p 51) → (p 34) → (¬ p 2) → (¬ p 68) → (¬ p 5) → (¬ p 63) → (¬ p 9) → (¬ p 49) → False := by
  intro a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12
  have v0 : p 4 := Classical.byContradiction (fun u => d20 u a9 a10)
  have v1 : ¬ p 53 := (fun u => d5492 u a0 a1 a6 a7 v0 a9)
  have v2 : p 66 := Classical.byContradiction (fun u => d273 a12 v1 u)
  have v3 : p 39 := Classical.byContradiction (fun u => d5493 u a0 a1 a6 a7 a8 a9 a10)
  have v4 : ¬ p 18 := (fun u => d668 u v3 a0)
  have v5 : ¬ p 20 := (fun u => d5353 a7 v4 v0 u)
  have v6 : p 22 := Classical.byContradiction (fun u => d5457 v4 a3 v2 a4 u a7 a2 v0 a11)
  have v7 : ¬ p 6 := (fun u => d4619 u a0 v5 v4)
  have v8 : ¬ p 76 := (fun u => d3227 a5 u v6)
  exact d213 a9 v7 v8

theorem c5495 (p : Nat → Prop)
    (d1215 : (p 4) → (p 2) → (p 7) → False)
    (d5353 : (¬ p 2) → (¬ p 18) → (p 4) → (p 20) → False)
    (d5358 : (¬ p 2) → (¬ p 18) → (p 7) → (p 23) → False)
    (d442 : (¬ p 23) → (¬ p 25) → (¬ p 100) → False)
    (d424 : (p 21) → (p 25) → (p 79) → False)
    (d4939 : (¬ p 21) → (¬ p 50) → (p 22) → (p 51) → False)
    (d270 : (¬ p 20) → (¬ p 22) → (¬ p 64) → False)
    (d400 : (¬ p 22) → (¬ p 24) → (¬ p 89) → False)
    (d777 : (p 51) → (p 89) → (p 64) → False)
    : (¬ p 18) → (¬ p 100) → (¬ p 50) → (¬ p 24) → (p 51) → (p 79) → (p 7) → (p 4) → False := by
  intro a0 a1 a2 a3 a4 a5 a6 a7
  have v0 : ¬ p 2 := (fun u => d1215 a7 u a6)
  have v1 : ¬ p 20 := (fun u => d5353 v0 a0 a7 u)
  have v2 : ¬ p 23 := (fun u => d5358 v0 a0 a6 u)
  have v3 : p 25 := Classical.byContradiction (fun u => d442 v2 u a1)
  have v4 : ¬ p 21 := (fun u => d424 u v3 a5)
  have v5 : ¬ p 22 := (fun u => d4939 v4 a2 u a4)
  have v6 : p 64 := Classical.byContradiction (fun u => d270 v1 v5 u)
  have v7 : p 89 := Classical.byContradiction (fun u => d400 v5 a3 u)
  exact d777 a4 v7 v6

theorem c5496 (p : Nat → Prop)
    (d5486 : (p 3) → (p 130) → (p 80) → (¬ p 63) → (¬ p 9) → (¬ p 49) → False)
    (d755 : (p 80) → (p 130) → (¬ p 9) → (p 5) → False)
    (d20 : (¬ p 4) → (¬ p 5) → (¬ p 63) → False)
    (d1215 : (p 4) → (p 2) → (p 7) → False)
    (d505 : (¬ p 2) → (¬ p 3) → (¬ p 34) → False)
    (d5453 : (¬ p 10) → (p 130) → (p 80) → (¬ p 9) → False)
    (d281 : (p 4) → (p 10) → (p 68) → False)
    (d5488 : (p 42) → (¬ p 90) → (p 51) → (p 79) → (p 7) → (p 130) → (p 80) → (¬ p 63) → (¬ p 9) → (¬ p 49) → False)
    (d5491 : (p 8) → (¬ p 90) → (p 51) → (p 79) → (p 7) → (¬ p 3) → (p 10) → (p 4) → (¬ p 5) → (p 80) → (¬ p 49) → False)
    (d5304 : (¬ p 8) → (¬ p 9) → (p 79) → (p 78) → False)
    (d5494 : (p 37) → (¬ p 78) → (¬ p 8) → (¬ p 42) → (¬ p 90) → (p 51) → (p 34) → (¬ p 2) → (¬ p 68) → (¬ p 5) → (¬ p 63) → (¬ p 9) → (¬ p 49) → False)
    (d10 : (¬ p 37) → (¬ p 40) → (¬ p 90) → False)
    (d5487 : (¬ p 8) → (p 40) → (p 41) → (p 79) → (p 80) → (¬ p 9) → False)
    (d5301 : (¬ p 8) → (¬ p 9) → (p 39) → (p 40) → False)
    (d5278 : (¬ p 41) → (¬ p 38) → (p 7) → (p 10) → False)
    (d5467 : (¬ p 39) → (¬ p 42) → (p 24) → (¬ p 8) → (¬ p 9) → False)
    (d5236 : (¬ p 78) → (¬ p 39) → (p 50) → (p 34) → False)
    (d541 : (p 38) → (p 40) → (p 100) → False)
    (d5495 : (¬ p 18) → (¬ p 100) → (¬ p 50) → (¬ p 24) → (p 51) → (p 79) → (p 7) → (p 4) → False)
    (d5439 : (p 21) → (p 80) → (¬ p 39) → (p 18) → False)
    (d5433 : (¬ p 3) → (p 79) → (¬ p 21) → (¬ p 2) → (¬ p 49) → (¬ p 9) → (¬ p 39) → (p 18) → False)
    : (¬ p 90) → (p 51) → (p 79) → (p 7) → (p 130) → (p 80) → (¬ p 63) → (¬ p 9) → (¬ p 49) → False := by
  intro a0 a1 a2 a3 a4 a5 a6 a7 a8
  have v0 : ¬ p 3 := (fun u => d5486 u a4 a5 a6 a7 a8)
  have v1 : ¬ p 5 := (fun u => d755 a5 a4 a7 u)
  have v2 : p 4 := Classical.byContradiction (fun u => d20 u v1 a6)
  have v3 : ¬ p 2 := (fun u => d1215 v2 u a3)
  have v4 : p 34 := Classical.byContradiction (fun u => d505 v3 v0 u)
  have v5 : p 10 := Classical.byContradiction (fun u => d5453 u a4 a5 a7)
  have v6 : ¬ p 68 := (fun u => d281 v2 v5 u)
  have v7 : ¬ p 42 := (fun u => d5488 u a0 a1 a2 a3 a4 a5 a6 a7 a8)
  have v8 : ¬ p 8 := (fun u => d5491 u a0 a1 a2 a3 v0 v5 v2 v1 a5 a8)
  have v9 : ¬ p 78 := (fun u => d5304 v8 a7 a2 u)
  have v10 : ¬ p 37 := (fun u => d5494 u v9 v8 v7 a0 a1 v4 v3 v6 v1 a6 a7 a8)
  have v11 : p 40 := Classical.byContradiction (fun u => d10 v10 u a0)
  have v12 : ¬ p 41 := (fun u => d5487 v8 v11 u a2 a5 a7)
  have v13 : ¬ p 39 := (fun u => d5301 v8 a7 u v11)
  have v14 : p 38 := Classical.byContradiction (fun u => d5278 v12 u a3 v5)
  have v15 : ¬ p 24 := (fun u => d5467 v13 v7 u v8 a7)
  have v16 : ¬ p 50 := (fun u => d5236 v9 v13 u v4)
  have v17 : ¬ p 100 := (fun u => d541 v14 v11 u)
  have v18 : p 18 := Classical.byContradiction (fun u => d5495 u v17 v16 v15 a1 a2 a3 v2)
  have v19 : ¬ p 21 := (fun u => d5439 u a5 v13 v18)
  exact d5433 v0 a2 v19 v3 a8 a7 v13 v18

theorem c5497 (p : Nat → Prop)
    (d5304 : (¬ p 8) → (¬ p 9) → (p 79) → (p 78) → False)
    (d5487 : (¬ p 8) → (p 40) → (p 41) → (p 79) → (p 80) → (¬ p 9) → False)
    (d5301 : (¬ p 8) → (¬ p 9) → (p 39) → (p 40) → False)
    (d5278 : (¬ p 41) → (¬ p 38) → (p 7) → (p 10) → False)
    (d5236 : (¬ p 78) → (¬ p 39) → (p 50) → (p 34) → False)
    (d541 : (p 38) → (p 40) → (p 100) → False)
    (d1134 : (p 34) → (p 38) → (p 42) → False)
    (d5467 : (¬ p 39) → (¬ p 42) → (p 24) → (¬ p 8) → (¬ p 9) → False)
    (d400 : (¬ p 22) → (¬ p 24) → (¬ p 89) → False)
    (d5495 : (¬ p 18) → (¬ p 100) → (¬ p 50) → (¬ p 24) → (p 51) → (p 79) → (p 7) → (p 4) → False)
    (d4939 : (¬ p 21) → (¬ p 50) → (p 22) → (p 51) → False)
    (d5439 : (p 21) → (p 80) → (¬ p 39) → (p 18) → False)
    : (p 40) → (¬ p 89) → (¬ p 8) → (p 51) → (p 79) → (p 34) → (p 7) → (p 10) → (p 4) → (p 80) → (¬ p 9) → False := by
  intro a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10
  have v0 : ¬ p 78 := (fun u => d5304 a2 a10 a4 u)
  have v1 : ¬ p 41 := (fun u => d5487 a2 a0 u a4 a9 a10)
  have v2 : ¬ p 39 := (fun u => d5301 a2 a10 u a0)
  have v3 : p 38 := Classical.byContradiction (fun u => d5278 v1 u a6 a7)
  have v4 : ¬ p 50 := (fun u => d5236 v0 v2 u a5)
  have v5 : ¬ p 100 := (fun u => d541 v3 a0 u)
  have v6 : ¬ p 42 := (fun u => d1134 a5 v3 u)
  have v7 : ¬ p 24 := (fun u => d5467 v2 v6 u a2 a10)
  have v8 : p 22 := Classical.byContradiction (fun u => d400 u v7 a1)
  have v9 : p 18 := Classical.byContradiction (fun u => d5495 u v5 v4 v7 a3 a4 a6 a8)
  have v10 : p 21 := Classical.byContradiction (fun u => d4939 u v4 v8 a3)
  exact d5439 v10 a9 v2 v9

theorem c5498 (p : Nat → Prop)
    (d5453 : (¬ p 10) → (p 130) → (p 80) → (¬ p 9) → False)
    (d755 : (p 80) → (p 130) → (¬ p 9) → (p 5) → False)
    (d5236 : (¬ p 78) → (¬ p 39) → (p 50) → (p 34) → False)
    (d5235 : (¬ p 78) → (¬ p 39) → (p 80) → (p 41) → False)
    (d5278 : (¬ p 41) → (¬ p 38) → (p 7) → (p 10) → False)
    (d1134 : (p 34) → (p 38) → (p 42) → False)
    (d5467 : (¬ p 39) → (¬ p 42) → (p 24) → (¬ p 8) → (¬ p 9) → False)
    (d400 : (¬ p 22) → (¬ p 24) → (¬ p 89) → False)
    (d3227 : (p 51) → (p 76) → (p 22) → False)
    (d4939 : (¬ p 21) → (¬ p 50) → (p 22) → (p 51) → False)
    (d213 : (¬ p 5) → (¬ p 6) → (¬ p 76) → False)
    (d5439 : (p 21) → (p 80) → (¬ p 39) → (p 18) → False)
    (d5359 : (¬ p 2) → (¬ p 18) → (p 6) → (p 22) → False)
    : (¬ p 39) → (¬ p 89) → (¬ p 78) → (¬ p 8) → (p 51) → (p 34) → (¬ p 2) → (p 7) → (p 130) → (p 80) → (¬ p 9) → False := by
  intro a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10
  have v0 : p 10 := Classical.byContradiction (fun u => d5453 u a8 a9 a10)
  have v1 : ¬ p 5 := (fun u => d755 a9 a8 a10 u)
  have v2 : ¬ p 50 := (fun u => d5236 a2 a0 u a5)
  have v3 : ¬ p 41 := (fun u => d5235 a2 a0 a9 u)
  have v4 : p 38 := Classical.byContradiction (fun u => d5278 v3 u a7 v0)
  have v5 : ¬ p 42 := (fun u => d1134 a5 v4 u)
  have v6 : ¬ p 24 := (fun u => d5467 a0 v5 u a3 a10)
  have v7 : p 22 := Classical.byContradiction (fun u => d400 u v6 a1)
  have v8 : ¬ p 76 := (fun u => d3227 a4 u v7)
  have v9 : p 21 := Classical.byContradiction (fun u => d4939 u v2 v7 a4)
  have v10 : p 6 := Classical.byContradiction (fun u => d213 v1 u v8)
  have v11 : ¬ p 18 := (fun u => d5439 v9 a9 a0 u)
  exact d5359 a6 v11 v10 v7

theorem c5499 (p : Nat → Prop)
    (d1171 : (p 39) → (p 34) → (p 43) → False)
    (d351 : (p 34) → (p 39) → (p 53) → False)
    (d424 : (p 21) → (p 25) → (p 79) → False)
    (d1519 : (¬ p 54) → (p 21) → (¬ p 58) → (¬ p 50) → (¬ p 23) → False)
    (d442 : (¬ p 23) → (¬ p 25) → (¬ p 100) → False)
    (d4561 : (p 55) → (p 58) → (p 34) → False)
    (d5294 : (¬ p 70) → (¬ p 65) → (¬ p 40) → (¬ p 43) → (p 100) → False)
    (d5337 : (¬ p 42) → (¬ p 45) → (¬ p 129) → (¬ p 55) → (p 56) → False)
    (d5115 : (¬ p 57) → (¬ p 53) → (p 66) → (p 70) → False)
    (d4967 : (¬ p 136) → (¬ p 56) → (p 51) → (p 96) → False)
    (d4963 : (¬ p 136) → (¬ p 56) → (p 141) → (p 57) → False)
    (d5001 : (¬ p 43) → (¬ p 141) → (¬ p 96) → (¬ p 89) → (p 39) → False)
    : (p 21) → (¬ p 50) → (¬ p 136) → (¬ p 42) → (¬ p 45) → (¬ p 23) → (¬ p 129) → (p 66) → (p 39) → (¬ p 40) → (¬ p 89) → (¬ p 54) → (p 51) → (p 79) → (p 34) → (¬ p 65) → False := by
  intro a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15
  have v0 : ¬ p 43 := (fun u => d1171 a8 a14 u)
  have v1 : ¬ p 53 := (fun u => d351 a14 a8 u)
  have v2 : ¬ p 25 := (fun u => d424 a0 u a13)
  have v3 : p 58 := Classical.byContradiction (fun u => d1519 a11 a0 u a1 a5)
  have v4 : p 100 := Classical.byContradiction (fun u => d442 a5 v2 u)
  have v5 : ¬ p 55 := (fun u => d4561 u v3 a14)
  have v6 : p 70 := Classical.byContradiction (fun u => d5294 u a15 a9 v0 v4)
  have v7 : ¬ p 56 := (fun u => d5337 a3 a4 a6 v5 u)
  have v8 : p 57 := Classical.byContradiction (fun u => d5115 u v1 a7 v6)
  have v9 : ¬ p 96 := (fun u => d4967 a2 v7 a12 u)
  have v10 : ¬ p 141 := (fun u => d4963 a2 v7 u v8)
  exact d5001 v0 v10 v9 a10 a8

theorem c5500 (p : Nat → Prop)
    (d5499 : (p 21) → (¬ p 50) → (¬ p 136) → (¬ p 42) → (¬ p 45) → (¬ p 23) → (¬ p 129) → (p 66) → (p 39) → (¬ p 40) → (¬ p 89) → (¬ p 54) → (p 51) → (p 79) → (p 34) → (¬ p 65) → False)
    (d4939 : (¬ p 21) → (¬ p 50) → (p 22) → (p 51) → False)
    (d1044 : (¬ p 23) → (p 79) → (¬ p 21) → (¬ p 25) → False)
    (d400 : (¬ p 22) → (¬ p 24) → (¬ p 89) → False)
    (d5299 : (¬ p 8) → (¬ p 9) → (p 25) → (p 24) → False)
    : (¬ p 50) → (¬ p 136) → (¬ p 42) → (¬ p 45) → (¬ p 23) → (¬ p 129) → (p 66) → (p 39) → (¬ p 40) → (¬ p 89) → (¬ p 8) → (¬ p 54) → (p 51) → (p 79) → (p 34) → (¬ p 65) → (¬ p 9) → False := by
  intro a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16
  have v0 : ¬ p 21 := (fun u => d5499 u a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a11 a12 a13 a14 a15)
  have v1 : ¬ p 22 := (fun u => d4939 v0 a0 u a12)
  have v2 : p 25 := Classical.byContradiction (fun u => d1044 a4 a13 v0 u)
  have v3 : p 24 := Classical.byContradiction (fun u => d400 v1 u a9)
  exact d5299 a10 a16 v2 v3

theorem c5501 (p : Nat → Prop)
    (d5303 : (¬ p 8) → (¬ p 9) → (p 67) → (p 66) → False)
    (d5475 : (¬ p 67) → (¬ p 72) → (p 79) → (¬ p 8) → (¬ p 9) → False)
    (d247 : (p 66) → (p 72) → (p 114) → False)
    (d59 : (p 4) → (p 14) → (p 72) → False)
    (d5304 : (¬ p 8) → (¬ p 9) → (p 79) → (p 78) → False)
    (d5338 : (¬ p 42) → (¬ p 45) → (¬ p 14) → (¬ p 15) → (p 136) → False)
    (d5500 : (¬ p 50) → (¬ p 136) → (¬ p 42) → (¬ p 45) → (¬ p 23) → (¬ p 129) → (p 66) → (p 39) → (¬ p 40) → (¬ p 89) → (¬ p 8) → (¬ p 54) → (p 51) → (p 79) → (p 34) → (¬ p 65) → (¬ p 9) → False)
    (d5261 : (¬ p 114) → (¬ p 78) → (¬ p 129) → (¬ p 55) → (p 50) → False)
    (d122 : (p 50) → (p 51) → (p 76) → False)
    (d4961 : (¬ p 136) → (¬ p 56) → (p 55) → (p 130) → False)
    (d213 : (¬ p 5) → (¬ p 6) → (¬ p 76) → False)
    (d5044 : (¬ p 64) → (¬ p 69) → (p 56) → (p 51) → False)
    (d32 : (p 4) → (p 6) → (p 64) → False)
    : (¬ p 42) → (¬ p 69) → (¬ p 45) → (¬ p 23) → (¬ p 129) → (p 66) → (p 39) → (¬ p 40) → (¬ p 89) → (¬ p 8) → (¬ p 54) → (p 51) → (p 79) → (p 34) → (¬ p 65) → (¬ p 15) → (p 4) → (¬ p 5) → (p 130) → (¬ p 9) → False := by
  intro a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19
  have v0 : ¬ p 67 := (fun u => d5303 a9 a19 u a5)
  have v1 : p 72 := Classical.byContradiction (fun u => d5475 v0 u a12 a9 a19)
  have v2 : ¬ p 114 := (fun u => d247 a5 v1 u)
  have v3 : ¬ p 14 := (fun u => d59 a16 u v1)
  have v4 : ¬ p 78 := (fun u => d5304 a9 a19 a12 u)
  have v5 : ¬ p 136 := (fun u => d5338 a0 a2 v3 a15 u)
  have v6 : p 50 := Classical.byContradiction (fun u => d5500 u v5 a0 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a19)
  have v7 : p 55 := Classical.byContradiction (fun u => d5261 v2 v4 a4 u v6)
  have v8 : ¬ p 76 := (fun u => d122 v6 a11 u)
  have v9 : p 56 := Classical.byContradiction (fun u => d4961 v5 u v7 a18)
  have v10 : p 6 := Classical.byContradiction (fun u => d213 a17 u v8)
  have v11 : p 64 := Classical.byContradiction (fun u => d5044 u a1 v9 a11)
  exact d32 a16 v10 v11

theorem c5502 (p : Nat → Prop)
    (d5303 : (¬ p 8) → (¬ p 9) → (p 67) → (p 66) → False)
    (d5475 : (¬ p 67) → (¬ p 72) → (p 79) → (¬ p 8) → (¬ p 9) → False)
    (d247 : (p 66) → (p 72) → (p 114) → False)
    (d1171 : (p 39) → (p 34) → (p 43) → False)
    (d351 : (p 34) → (p 39) → (p 53) → False)
    (d5304 : (¬ p 8) → (¬ p 9) → (p 79) → (p 78) → False)
    (d4556 : (p 12) → (p 4) → (p 7) → False)
    (d418 : (p 4) → (p 7) → (p 65) → False)
    (d1215 : (p 4) → (p 2) → (p 7) → False)
    (d373 : (p 10) → (p 15) → (p 130) → False)
    (d1530 : (¬ p 18) → (¬ p 35) → (¬ p 2) → (p 4) → False)
    (d5360 : (¬ p 2) → (¬ p 18) → (p 26) → (p 10) → False)
    (d5358 : (¬ p 2) → (¬ p 18) → (p 7) → (p 23) → False)
    (d199 : (p 35) → (p 45) → (p 72) → False)
    (d3991 : (p 69) → (p 72) → (p 35) → False)
    (d5501 : (¬ p 42) → (¬ p 69) → (¬ p 45) → (¬ p 23) → (¬ p 129) → (p 66) → (p 39) → (¬ p 40) → (¬ p 89) → (¬ p 8) → (¬ p 54) → (p 51) → (p 79) → (p 34) → (¬ p 65) → (¬ p 15) → (p 4) → (¬ p 5) → (p 130) → (¬ p 9) → False)
    (d1134 : (p 34) → (p 38) → (p 42) → False)
    (d4613 : (p 47) → (p 35) → (p 42) → False)
    (d5278 : (¬ p 41) → (¬ p 38) → (p 7) → (p 10) → False)
    (d559 : (p 34) → (p 41) → (p 55) → False)
    (d5106 : (¬ p 24) → (¬ p 26) → (p 39) → (p 41) → False)
    (d4995 : (¬ p 43) → (¬ p 141) → (p 41) → (p 130) → False)
    (d5261 : (¬ p 114) → (¬ p 78) → (¬ p 129) → (¬ p 55) → (p 50) → False)
    (d5299 : (¬ p 8) → (¬ p 9) → (p 25) → (p 24) → False)
    (d5153 : (¬ p 26) → (¬ p 28) → (p 141) → (p 130) → False)
    (d631 : (p 130) → (p 31) → (p 141) → False)
    (d1044 : (¬ p 23) → (p 79) → (¬ p 21) → (¬ p 25) → False)
    (d442 : (¬ p 23) → (¬ p 25) → (¬ p 100) → False)
    (d5111 : (¬ p 57) → (¬ p 53) → (p 28) → (p 24) → False)
    (d1519 : (¬ p 54) → (p 21) → (¬ p 58) → (¬ p 50) → (¬ p 23) → False)
    (d264 : (p 77) → (p 79) → (p 100) → False)
    (d5185 : (¬ p 13) → (¬ p 12) → (p 57) → (p 58) → False)
    (d209 : (p 34) → (p 44) → (p 58) → False)
    (d132 : (p 7) → (p 13) → (p 104) → False)
    (d5201 : (¬ p 44) → (¬ p 47) → (p 16) → (p 13) → False)
    (d4914 : (¬ p 104) → (¬ p 77) → (p 21) → (p 29) → False)
    (d5209 : (¬ p 44) → (¬ p 47) → (¬ p 16) → (¬ p 15) → (¬ p 31) → (¬ p 29) → False)
    : (¬ p 18) → (¬ p 129) → (p 66) → (p 39) → (¬ p 40) → (¬ p 89) → (¬ p 8) → (¬ p 54) → (p 51) → (p 79) → (p 34) → (p 7) → (p 10) → (p 4) → (¬ p 5) → (p 130) → (¬ p 9) → False := by
  intro a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16
  have v0 : ¬ p 67 := (fun u => d5303 a6 a16 u a2)
  have v1 : p 72 := Classical.byContradiction (fun u => d5475 v0 u a9 a6 a16)
  have v2 : ¬ p 114 := (fun u => d247 a2 v1 u)
  have v3 : ¬ p 43 := (fun u => d1171 a3 a10 u)
  have v4 : ¬ p 53 := (fun u => d351 a10 a3 u)
  have v5 : ¬ p 78 := (fun u => d5304 a6 a16 a9 u)
  have v6 : ¬ p 12 := (fun u => d4556 u a13 a11)
  have v7 : ¬ p 65 := (fun u => d418 a13 a11 u)
  have v8 : ¬ p 2 := (fun u => d1215 a13 u a11)
  have v9 : ¬ p 15 := (fun u => d373 a12 u a15)
  have v10 : p 35 := Classical.byContradiction (fun u => d1530 a0 u v8 a13)
  have v11 : ¬ p 26 := (fun u => d5360 v8 a0 u a12)
  have v12 : ¬ p 23 := (fun u => d5358 v8 a0 a11 u)
  have v13 : ¬ p 45 := (fun u => d199 v10 u v1)
  have v14 : ¬ p 69 := (fun u => d3991 u v1 v10)
  have v15 : p 42 := Classical.byContradiction (fun u => d5501 u v14 v13 v12 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 v7 v9 a13 a14 a15 a16)
  have v16 : ¬ p 38 := (fun u => d1134 a10 u v15)
  have v17 : ¬ p 47 := (fun u => d4613 u v10 v15)
  have v18 : p 41 := Classical.byContradiction (fun u => d5278 u v16 a11 a12)
  have v19 : ¬ p 55 := (fun u => d559 a10 v18 u)
  have v20 : p 24 := Classical.byContradiction (fun u => d5106 u v11 a3 v18)
  have v21 : p 141 := Classical.byContradiction (fun u => d4995 v3 u v18 a15)
  have v22 : ¬ p 50 := (fun u => d5261 v2 v5 a1 v19 u)
  have v23 : ¬ p 25 := (fun u => d5299 a6 a16 u v20)
  have v24 : p 28 := Classical.byContradiction (fun u => d5153 v11 u v21 a15)
  have v25 : ¬ p 31 := (fun u => d631 a15 u v21)
  have v26 : p 21 := Classical.byContradiction (fun u => d1044 v12 a9 u v23)
  have v27 : p 100 := Classical.byContradiction (fun u => d442 v12 v23 u)
  have v28 : p 57 := Classical.byContradiction (fun u => d5111 u v4 v24 v20)
  have v29 : p 58 := Classical.byContradiction (fun u => d1519 a7 v26 u v22 v12)
  have v30 : ¬ p 77 := (fun u => d264 u a9 v27)
  have v31 : p 13 := Classical.byContradiction (fun u => d5185 u v6 v28 v29)
  have v32 : ¬ p 44 := (fun u => d209 a10 u v29)
  have v33 : ¬ p 104 := (fun u => d132 a11 v31 u)
  have v34 : ¬ p 16 := (fun u => d5201 v32 v17 u v31)
  have v35 : ¬ p 29 := (fun u => d4914 v33 v30 v26 u)
  exact d5209 v32 v17 v34 v9 v25 v35

theorem c5503 (p : Nat → Prop)
    (d1171 : (p 39) → (p 34) → (p 43) → False)
    (d442 : (¬ p 23) → (¬ p 25) → (¬ p 100) → False)
    (d1519 : (¬ p 54) → (p 21) → (¬ p 58) → (¬ p 50) → (¬ p 23) → False)
    (d5294 : (¬ p 70) → (¬ p 65) → (¬ p 40) → (¬ p 43) → (p 100) → False)
    (d4561 : (p 55) → (p 58) → (p 34) → False)
    (d4611 : (p 70) → (p 4) → (p 69) → False)
    (d4956 : (¬ p 129) → (¬ p 55) → (p 45) → (p 34) → False)
    (d5501 : (¬ p 42) → (¬ p 69) → (¬ p 45) → (¬ p 23) → (¬ p 129) → (p 66) → (p 39) → (¬ p 40) → (¬ p 89) → (¬ p 8) → (¬ p 54) → (p 51) → (p 79) → (p 34) → (¬ p 65) → (¬ p 15) → (p 4) → (¬ p 5) → (p 130) → (¬ p 9) → False)
    : (¬ p 23) → (p 21) → (¬ p 50) → (¬ p 42) → (¬ p 25) → (¬ p 129) → (p 66) → (p 39) → (¬ p 40) → (¬ p 89) → (¬ p 8) → (¬ p 54) → (p 51) → (p 79) → (p 34) → (¬ p 65) → (¬ p 15) → (p 4) → (¬ p 5) → (p 130) → (¬ p 9) → False := by
  intro a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20
  have v0 : ¬ p 43 := (fun u => d1171 a7 a14 u)
  have v1 : p 100 := Classical.byContradiction (fun u => d442 a0 a4 u)
  have v2 : p 58 := Classical.byContradiction (fun u => d1519 a11 a1 u a2 a0)
  have v3 : p 70 := Classical.byContradiction (fun u => d5294 u a15 a8 v0 v1)
  have v4 : ¬ p 55 := (fun u => d4561 u v2 a14)
  have v5 : ¬ p 69 := (fun u => d4611 v3 a17 u)
  have v6 : ¬ p 45 := (fun u => d4956 a5 v4 u a14)
  exact d5501 a3 v5 v6 a0 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20

theorem c5504 (p : Nat → Prop)
    (d1134 : (p 34) → (p 38) → (p 42) → False)
    (d2479 : (p 47) → (p 39) → (p 38) → False)
    (d5304 : (¬ p 8) → (¬ p 9) → (p 79) → (p 78) → False)
    (d3361 : (p 18) → (¬ p 78) → (p 24) → (p 34) → False)
    (d400 : (¬ p 22) → (¬ p 24) → (¬ p 89) → False)
    (d966 : (p 39) → (p 41) → (p 18) → False)
    (d5303 : (¬ p 8) → (¬ p 9) → (p 67) → (p 66) → False)
    (d5475 : (¬ p 67) → (¬ p 72) → (p 79) → (¬ p 8) → (¬ p 9) → False)
    (d247 : (p 66) → (p 72) → (p 114) → False)
    (d5255 : (¬ p 114) → (¬ p 78) → (p 129) → (p 80) → False)
    (d59 : (p 4) → (p 14) → (p 72) → False)
    (d5453 : (¬ p 10) → (p 130) → (p 80) → (¬ p 9) → False)
    (d373 : (p 10) → (p 15) → (p 130) → False)
    (d755 : (p 80) → (p 130) → (¬ p 9) → (p 5) → False)
    (d4940 : (¬ p 21) → (¬ p 50) → (p 34) → (p 18) → False)
    (d263 : (p 21) → (p 26) → (p 80) → False)
    (d5258 : (¬ p 114) → (¬ p 78) → (p 30) → (p 21) → False)
    (d5110 : (¬ p 24) → (¬ p 26) → (¬ p 96) → (¬ p 89) → (p 130) → False)
    (d19 : (p 22) → (p 31) → (p 96) → False)
    (d5503 : (¬ p 23) → (p 21) → (¬ p 50) → (¬ p 42) → (¬ p 25) → (¬ p 129) → (p 66) → (p 39) → (¬ p 40) → (¬ p 89) → (¬ p 8) → (¬ p 54) → (p 51) → (p 79) → (p 34) → (¬ p 65) → (¬ p 15) → (p 4) → (¬ p 5) → (p 130) → (¬ p 9) → False)
    (d135 : (p 21) → (p 23) → (p 77) → False)
    (d2349 : (p 44) → (p 79) → (¬ p 54) → (p 38) → (p 34) → (¬ p 77) → False)
    (d5085 : (¬ p 41) → (¬ p 44) → (p 13) → (p 10) → False)
    (d5206 : (¬ p 44) → (¬ p 47) → (¬ p 14) → (¬ p 13) → (p 149) → False)
    (d5090 : (¬ p 41) → (¬ p 44) → (¬ p 31) → (¬ p 29) → (p 130) → False)
    (d5231 : (¬ p 30) → (¬ p 149) → (¬ p 44) → (¬ p 47) → (p 29) → False)
    : (¬ p 50) → (¬ p 25) → (p 38) → (p 18) → (p 66) → (p 39) → (¬ p 40) → (¬ p 89) → (¬ p 8) → (¬ p 54) → (p 51) → (p 79) → (p 34) → (¬ p 65) → (p 4) → (p 130) → (p 80) → (¬ p 9) → False := by
  intro a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17
  have v0 : ¬ p 42 := (fun u => d1134 a12 a2 u)
  have v1 : ¬ p 47 := (fun u => d2479 u a5 a2)
  have v2 : ¬ p 78 := (fun u => d5304 a8 a17 a11 u)
  have v3 : ¬ p 24 := (fun u => d3361 a3 v2 u a12)
  have v4 : p 22 := Classical.byContradiction (fun u => d400 u v3 a7)
  have v5 : ¬ p 41 := (fun u => d966 a5 u a3)
  have v6 : ¬ p 67 := (fun u => d5303 a8 a17 u a4)
  have v7 : p 72 := Classical.byContradiction (fun u => d5475 v6 u a11 a8 a17)
  have v8 : ¬ p 114 := (fun u => d247 a4 v7 u)
  have v9 : ¬ p 129 := (fun u => d5255 v8 v2 u a16)
  have v10 : ¬ p 14 := (fun u => d59 a14 u v7)
  have v11 : p 10 := Classical.byContradiction (fun u => d5453 u a15 a16 a17)
  have v12 : ¬ p 15 := (fun u => d373 v11 u a15)
  have v13 : ¬ p 5 := (fun u => d755 a16 a15 a17 u)
  have v14 : p 21 := Classical.byContradiction (fun u => d4940 u a0 a12 a3)
  have v15 : ¬ p 26 := (fun u => d263 v14 u a16)
  have v16 : ¬ p 30 := (fun u => d5258 v8 v2 u v14)
  have v17 : p 96 := Classical.byContradiction (fun u => d5110 v3 v15 u a7 a15)
  have v18 : ¬ p 31 := (fun u => d19 v4 u v17)
  have v19 : p 23 := Classical.byContradiction (fun u => d5503 u v14 a0 v0 a1 v9 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 v12 a14 v13 a15 a17)
  have v20 : ¬ p 77 := (fun u => d135 v14 v19 u)
  have v21 : ¬ p 44 := (fun u => d2349 u a11 a9 a2 a12 v20)
  have v22 : ¬ p 13 := (fun u => d5085 v5 v21 u v11)
  have v23 : ¬ p 149 := (fun u => d5206 v21 v1 v10 v22 u)
  have v24 : p 29 := Classical.byContradiction (fun u => d5090 v5 v21 v18 u a15)
  exact d5231 v16 v23 v21 v1 v24

theorem c5505 (p : Nat → Prop)
    (d17 : (p 51) → (p 54) → (p 90) → False)
    (d4556 : (p 12) → (p 4) → (p 7) → False)
    (d418 : (p 4) → (p 7) → (p 65) → False)
    (d1215 : (p 4) → (p 2) → (p 7) → False)
    (d5453 : (¬ p 10) → (p 130) → (p 80) → (¬ p 9) → False)
    (d755 : (p 80) → (p 130) → (¬ p 9) → (p 5) → False)
    (d5304 : (¬ p 8) → (¬ p 9) → (p 79) → (p 78) → False)
    (d5302 : (¬ p 8) → (¬ p 9) → (p 89) → (p 90) → False)
    (d5497 : (p 40) → (¬ p 89) → (¬ p 8) → (p 51) → (p 79) → (p 34) → (p 7) → (p 10) → (p 4) → (p 80) → (¬ p 9) → False)
    (d5498 : (¬ p 39) → (¬ p 89) → (¬ p 78) → (¬ p 8) → (p 51) → (p 34) → (¬ p 2) → (p 7) → (p 130) → (p 80) → (¬ p 9) → False)
    (d351 : (p 34) → (p 39) → (p 53) → False)
    (d1171 : (p 39) → (p 34) → (p 43) → False)
    (d273 : (¬ p 49) → (¬ p 53) → (¬ p 66) → False)
    (d5068 : (¬ p 40) → (¬ p 43) → (p 93) → (p 90) → False)
    (d5303 : (¬ p 8) → (¬ p 9) → (p 67) → (p 66) → False)
    (d5475 : (¬ p 67) → (¬ p 72) → (p 79) → (¬ p 8) → (¬ p 9) → False)
    (d59 : (p 4) → (p 14) → (p 72) → False)
    (d247 : (p 66) → (p 72) → (p 114) → False)
    (d5255 : (¬ p 114) → (¬ p 78) → (p 129) → (p 80) → False)
    (d5502 : (¬ p 18) → (¬ p 129) → (p 66) → (p 39) → (¬ p 40) → (¬ p 89) → (¬ p 8) → (¬ p 54) → (p 51) → (p 79) → (p 34) → (p 7) → (p 10) → (p 4) → (¬ p 5) → (p 130) → (¬ p 9) → False)
    (d3361 : (p 18) → (¬ p 78) → (p 24) → (p 34) → False)
    (d966 : (p 39) → (p 41) → (p 18) → False)
    (d400 : (¬ p 22) → (¬ p 24) → (¬ p 89) → False)
    (d5278 : (¬ p 41) → (¬ p 38) → (p 7) → (p 10) → False)
    (d26 : (p 22) → (p 25) → (p 90) → False)
    (d3227 : (p 51) → (p 76) → (p 22) → False)
    (d5504 : (¬ p 50) → (¬ p 25) → (p 38) → (p 18) → (p 66) → (p 39) → (¬ p 40) → (¬ p 89) → (¬ p 8) → (¬ p 54) → (p 51) → (p 79) → (p 34) → (¬ p 65) → (p 4) → (p 130) → (p 80) → (¬ p 9) → False)
    (d3347 : (p 57) → (p 51) → (p 50) → False)
    (d5115 : (¬ p 57) → (¬ p 53) → (p 66) → (p 70) → False)
    (d5293 : (¬ p 70) → (¬ p 65) → (¬ p 93) → (¬ p 76) → (p 77) → False)
    (d5294 : (¬ p 70) → (¬ p 65) → (¬ p 40) → (¬ p 43) → (p 100) → False)
    (d2349 : (p 44) → (p 79) → (¬ p 54) → (p 38) → (p 34) → (¬ p 77) → False)
    (d442 : (¬ p 23) → (¬ p 25) → (¬ p 100) → False)
    (d5085 : (¬ p 41) → (¬ p 44) → (p 13) → (p 10) → False)
    (d1286 : (p 23) → (p 30) → (p 22) → False)
    (d5288 : (¬ p 70) → (¬ p 65) → (p 28) → (p 23) → False)
    (d5199 : (¬ p 30) → (¬ p 28) → (¬ p 13) → (¬ p 12) → (¬ p 14) → False)
    : (¬ p 8) → (p 90) → (p 51) → (p 79) → (p 34) → (p 7) → (p 4) → (p 130) → (p 80) → (¬ p 9) → (¬ p 49) → False := by
  intro a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10
  have v0 : ¬ p 54 := (fun u => d17 a2 u a1)
  have v1 : ¬ p 12 := (fun u => d4556 u a6 a5)
  have v2 : ¬ p 65 := (fun u => d418 a6 a5 u)
  have v3 : ¬ p 2 := (fun u => d1215 a6 u a5)
  have v4 : p 10 := Classical.byContradiction (fun u => d5453 u a7 a8 a9)
  have v5 : ¬ p 5 := (fun u => d755 a8 a7 a9 u)
  have v6 : ¬ p 78 := (fun u => d5304 a0 a9 a3 u)
  have v7 : ¬ p 89 := (fun u => d5302 a0 a9 u a1)
  have v8 : ¬ p 40 := (fun u => d5497 u v7 a0 a2 a3 a4 a5 v4 a6 a8 a9)
  have v9 : p 39 := Classical.byContradiction (fun u => d5498 u v7 v6 a0 a2 a4 v3 a5 a7 a8 a9)
  have v10 : ¬ p 53 := (fun u => d351 a4 v9 u)
  have v11 : ¬ p 43 := (fun u => d1171 v9 a4 u)
  have v12 : p 66 := Classical.byContradiction (fun u => d273 a10 v10 u)
  have v13 : ¬ p 93 := (fun u => d5068 v8 v11 u a1)
  have v14 : ¬ p 67 := (fun u => d5303 a0 a9 u v12)
  have v15 : p 72 := Classical.byContradiction (fun u => d5475 v14 u a3 a0 a9)
  have v16 : ¬ p 14 := (fun u => d59 a6 u v15)
  have v17 : ¬ p 114 := (fun u => d247 v12 v15 u)
  have v18 : ¬ p 129 := (fun u => d5255 v17 v6 u a8)
  have v19 : p 18 := Classical.byContradiction (fun u => d5502 u v18 v12 v9 v8 v7 a0 v0 a2 a3 a4 a5 v4 a6 v5 a7 a9)
  have v20 : ¬ p 24 := (fun u => d3361 v19 v6 u a4)
  have v21 : ¬ p 41 := (fun u => d966 v9 u v19)
  have v22 : p 22 := Classical.byContradiction (fun u => d400 u v20 v7)
  have v23 : p 38 := Classical.byContradiction (fun u => d5278 v21 u a5 v4)
  have v24 : ¬ p 25 := (fun u => d26 v22 u a1)
  have v25 : ¬ p 76 := (fun u => d3227 a2 u v22)
  have v26 : p 50 := Classical.byContradiction (fun u => d5504 u v24 v23 v19 v12 v9 v8 v7 a0 v0 a2 a3 a4 v2 a6 a7 a8 a9)
  have v27 : ¬ p 57 := (fun u => d3347 u a2 v26)
  have v28 : ¬ p 70 := (fun u => d5115 v27 v10 v12 u)
  have v29 : ¬ p 77 := (fun u => d5293 v28 v2 v13 v25 u)
  have v30 : ¬ p 100 := (fun u => d5294 v28 v2 v8 v11 u)
  have v31 : ¬ p 44 := (fun u => d2349 u a3 v0 v23 a4 v29)
  have v32 : p 23 := Classical.byContradiction (fun u => d442 u v24 v30)
  have v33 : ¬ p 13 := (fun u => d5085 v21 v31 u v4)
  have v34 : ¬ p 30 := (fun u => d1286 v32 u v22)
  have v35 : ¬ p 28 := (fun u => d5288 v28 v2 u v32)
  exact d5199 v34 v35 v33 v1 v16

theorem c5506 (p : Nat → Prop)
    (d5486 : (p 3) → (p 130) → (p 80) → (¬ p 63) → (¬ p 9) → (¬ p 49) → False)
    (d755 : (p 80) → (p 130) → (¬ p 9) → (p 5) → False)
    (d20 : (¬ p 4) → (¬ p 5) → (¬ p 63) → False)
    (d1215 : (p 4) → (p 2) → (p 7) → False)
    (d505 : (¬ p 2) → (¬ p 3) → (¬ p 34) → False)
    (d4556 : (p 12) → (p 4) → (p 7) → False)
    (d418 : (p 4) → (p 7) → (p 65) → False)
    (d5453 : (¬ p 10) → (p 130) → (p 80) → (¬ p 9) → False)
    (d5496 : (¬ p 90) → (p 51) → (p 79) → (p 7) → (p 130) → (p 80) → (¬ p 63) → (¬ p 9) → (¬ p 49) → False)
    (d17 : (p 51) → (p 54) → (p 90) → False)
    (d5505 : (¬ p 8) → (p 90) → (p 51) → (p 79) → (p 34) → (p 7) → (p 4) → (p 130) → (p 80) → (¬ p 9) → (¬ p 49) → False)
    (d13 : (p 4) → (p 8) → (p 66) → False)
    (d3743 : (¬ p 49) → (¬ p 3) → (¬ p 53) → (p 8) → False)
    (d4601 : (p 39) → (p 53) → (p 8) → False)
    (d2710 : (p 53) → (p 50) → (p 34) → False)
    (d5490 : (p 78) → (¬ p 50) → (p 53) → (p 51) → (p 80) → False)
    (d859 : (p 34) → (p 53) → (p 18) → (¬ p 78) → False)
    (d5235 : (¬ p 78) → (¬ p 39) → (p 80) → (p 41) → False)
    (d5360 : (¬ p 2) → (¬ p 18) → (p 26) → (p 10) → False)
    (d5358 : (¬ p 2) → (¬ p 18) → (p 7) → (p 23) → False)
    (d5278 : (¬ p 41) → (¬ p 38) → (p 7) → (p 10) → False)
    (d5102 : (¬ p 24) → (¬ p 26) → (p 8) → (p 10) → False)
    (d1134 : (p 34) → (p 38) → (p 42) → False)
    (d884 : (¬ p 102) → (p 34) → (p 53) → (p 38) → False)
    (d4631 : (p 53) → (p 24) → (¬ p 21) → (p 34) → False)
    (d4969 : (¬ p 39) → (¬ p 42) → (p 8) → (p 11) → False)
    (d1519 : (¬ p 54) → (p 21) → (¬ p 58) → (¬ p 50) → (¬ p 23) → False)
    (d5328 : (¬ p 11) → (¬ p 12) → (¬ p 70) → (¬ p 65) → (p 102) → False)
    (d209 : (p 34) → (p 44) → (p 58) → False)
    (d3761 : (¬ p 66) → (¬ p 71) → (p 58) → (¬ p 49) → False)
    (d5085 : (¬ p 41) → (¬ p 44) → (p 13) → (p 10) → False)
    (d5183 : (¬ p 13) → (¬ p 12) → (p 70) → (p 71) → False)
    : (p 51) → (p 79) → (p 7) → (p 130) → (p 80) → (¬ p 63) → (¬ p 9) → (¬ p 49) → False := by
  intro a0 a1 a2 a3 a4 a5 a6 a7
  have v0 : ¬ p 3 := (fun u => d5486 u a3 a4 a5 a6 a7)
  have v1 : ¬ p 5 := (fun u => d755 a4 a3 a6 u)
  have v2 : p 4 := Classical.byContradiction (fun u => d20 u v1 a5)
  have v3 : ¬ p 2 := (fun u => d1215 v2 u a2)
  have v4 : p 34 := Classical.byContradiction (fun u => d505 v3 v0 u)
  have v5 : ¬ p 12 := (fun u => d4556 u v2 a2)
  have v6 : ¬ p 65 := (fun u => d418 v2 a2 u)
  have v7 : p 10 := Classical.byContradiction (fun u => d5453 u a3 a4 a6)
  have v8 : p 90 := Classical.byContradiction (fun u => d5496 u a0 a1 a2 a3 a4 a5 a6 a7)
  have v9 : ¬ p 54 := (fun u => d17 a0 u v8)
  have v10 : p 8 := Classical.byContradiction (fun u => d5505 u v8 a0 a1 v4 a2 v2 a3 a4 a6 a7)
  have v11 : ¬ p 66 := (fun u => d13 v2 v10 u)
  have v12 : p 53 := Classical.byContradiction (fun u => d3743 a7 v0 u v10)
  have v13 : ¬ p 39 := (fun u => d4601 u v12 v10)
  have v14 : ¬ p 50 := (fun u => d2710 v12 u v4)
  have v15 : ¬ p 78 := (fun u => d5490 u v14 v12 a0 a4)
  have v16 : ¬ p 18 := (fun u => d859 v4 v12 u v15)
  have v17 : ¬ p 41 := (fun u => d5235 v15 v13 a4 u)
  have v18 : ¬ p 26 := (fun u => d5360 v3 v16 u v7)
  have v19 : ¬ p 23 := (fun u => d5358 v3 v16 a2 u)
  have v20 : p 38 := Classical.byContradiction (fun u => d5278 v17 u a2 v7)
  have v21 : p 24 := Classical.byContradiction (fun u => d5102 u v18 v10 v7)
  have v22 : ¬ p 42 := (fun u => d1134 v4 v20 u)
  have v23 : p 102 := Classical.byContradiction (fun u => d884 u v4 v12 v20)
  have v24 : p 21 := Classical.byContradiction (fun u => d4631 v12 v21 u v4)
  have v25 : ¬ p 11 := (fun u => d4969 v13 v22 v10 u)
  have v26 : p 58 := Classical.byContradiction (fun u => d1519 v9 v24 u v14 v19)
  have v27 : p 70 := Classical.byContradiction (fun u => d5328 v25 v5 u v6 v23)
  have v28 : ¬ p 44 := (fun u => d209 v4 u v26)
  have v29 : p 71 := Classical.byContradiction (fun u => d3761 v11 u v26 a7)
  have v30 : ¬ p 13 := (fun u => d5085 v17 v28 u v7)
  exact d5183 v30 v5 v27 v29

theorem c5507 (p : Nat → Prop)
    (d13 : (p 4) → (p 8) → (p 66) → False)
    (d1530 : (¬ p 18) → (¬ p 35) → (¬ p 2) → (p 4) → False)
    (d5360 : (¬ p 2) → (¬ p 18) → (p 26) → (p 10) → False)
    (d3982 : (p 74) → (p 71) → (p 35) → False)
    (d5102 : (¬ p 24) → (¬ p 26) → (p 8) → (p 10) → False)
    (d5057 : (¬ p 71) → (¬ p 66) → (p 24) → (p 29) → False)
    (d4970 : (¬ p 39) → (¬ p 42) → (p 27) → (p 24) → False)
    (d5180 : (¬ p 27) → (¬ p 29) → (¬ p 71) → (¬ p 66) → (¬ p 39) → (¬ p 42) → False)
    : (¬ p 18) → (p 74) → (¬ p 39) → (p 8) → (¬ p 42) → (¬ p 2) → (p 10) → (p 4) → False := by
  intro a0 a1 a2 a3 a4 a5 a6 a7
  have v0 : ¬ p 66 := (fun u => d13 a7 a3 u)
  have v1 : p 35 := Classical.byContradiction (fun u => d1530 a0 u a5 a7)
  have v2 : ¬ p 26 := (fun u => d5360 a5 a0 u a6)
  have v3 : ¬ p 71 := (fun u => d3982 a1 u v1)
  have v4 : p 24 := Classical.byContradiction (fun u => d5102 u v2 a3 a6)
  have v5 : ¬ p 29 := (fun u => d5057 v3 v0 v4 u)
  have v6 : ¬ p 27 := (fun u => d4970 a2 a4 u v4)
  exact d5180 v6 v5 v3 v0 a2 a4

theorem c5508 (p : Nat → Prop)
    (d1215 : (p 4) → (p 2) → (p 7) → False)
    (d505 : (¬ p 2) → (¬ p 3) → (¬ p 34) → False)
    (d5453 : (¬ p 10) → (p 130) → (p 80) → (¬ p 9) → False)
    (d559 : (p 34) → (p 41) → (p 55) → False)
    (d5278 : (¬ p 41) → (¬ p 38) → (p 7) → (p 10) → False)
    (d1134 : (p 34) → (p 38) → (p 42) → False)
    (d4556 : (p 12) → (p 4) → (p 7) → False)
    (d418 : (p 4) → (p 7) → (p 65) → False)
    (d373 : (p 10) → (p 15) → (p 130) → False)
    (d3743 : (¬ p 49) → (¬ p 3) → (¬ p 53) → (p 8) → False)
    (d1880 : (p 16) → (p 8) → (p 7) → False)
    (d4601 : (p 39) → (p 53) → (p 8) → False)
    (d4106 : (p 56) → (p 34) → (p 53) → False)
    (d884 : (¬ p 102) → (p 34) → (p 53) → (p 38) → False)
    (d4969 : (¬ p 39) → (¬ p 42) → (p 8) → (p 11) → False)
    (d4961 : (¬ p 136) → (¬ p 56) → (p 55) → (p 130) → False)
    (d5328 : (¬ p 11) → (¬ p 12) → (¬ p 70) → (¬ p 65) → (p 102) → False)
    (d4611 : (p 70) → (p 4) → (p 69) → False)
    (d5382 : (¬ p 74) → (¬ p 69) → (¬ p 16) → (¬ p 15) → (p 136) → False)
    (d5507 : (¬ p 18) → (p 74) → (¬ p 39) → (p 8) → (¬ p 42) → (¬ p 2) → (p 10) → (p 4) → False)
    (d5439 : (p 21) → (p 80) → (¬ p 39) → (p 18) → False)
    (d5433 : (¬ p 3) → (p 79) → (¬ p 21) → (¬ p 2) → (¬ p 49) → (¬ p 9) → (¬ p 39) → (p 18) → False)
    : (p 8) → (p 55) → (p 79) → (p 7) → (¬ p 3) → (p 4) → (p 130) → (p 80) → (¬ p 9) → (¬ p 49) → False := by
  intro a0 a1 a2 a3 a4 a5 a6 a7 a8 a9
  have v0 : ¬ p 2 := (fun u => d1215 a5 u a3)
  have v1 : p 34 := Classical.byContradiction (fun u => d505 v0 a4 u)
  have v2 : p 10 := Classical.byContradiction (fun u => d5453 u a6 a7 a8)
  have v3 : ¬ p 41 := (fun u => d559 v1 u a1)
  have v4 : p 38 := Classical.byContradiction (fun u => d5278 v3 u a3 v2)
  have v5 : ¬ p 42 := (fun u => d1134 v1 v4 u)
  have v6 : ¬ p 12 := (fun u => d4556 u a5 a3)
  have v7 : ¬ p 65 := (fun u => d418 a5 a3 u)
  have v8 : ¬ p 15 := (fun u => d373 v2 u a6)
  have v9 : p 53 := Classical.byContradiction (fun u => d3743 a9 a4 u a0)
  have v10 : ¬ p 16 := (fun u => d1880 u a0 a3)
  have v11 : ¬ p 39 := (fun u => d4601 u v9 a0)
  have v12 : ¬ p 56 := (fun u => d4106 u v1 v9)
  have v13 : p 102 := Classical.byContradiction (fun u => d884 u v1 v9 v4)
  have v14 : ¬ p 11 := (fun u => d4969 v11 v5 a0 u)
  have v15 : p 136 := Classical.byContradiction (fun u => d4961 u v12 a1 a6)
  have v16 : p 70 := Classical.byContradiction (fun u => d5328 v14 v6 u v7 v13)
  have v17 : ¬ p 69 := (fun u => d4611 v16 a5 u)
  have v18 : p 74 := Classical.byContradiction (fun u => d5382 u v17 v10 v8 v15)
  have v19 : p 18 := Classical.byContradiction (fun u => d5507 u v18 v11 a0 v5 v0 v2 a5)
  have v20 : ¬ p 21 := (fun u => d5439 u a7 v11 v19)
  exact d5433 a4 a2 v20 v0 a9 a8 v11 v19

theorem c5509 (p : Nat → Prop)
    (d5439 : (p 21) → (p 80) → (¬ p 39) → (p 18) → False)
    (d5433 : (¬ p 3) → (p 79) → (¬ p 21) → (¬ p 2) → (¬ p 49) → (¬ p 9) → (¬ p 39) → (p 18) → False)
    : (p 18) → (¬ p 39) → (p 79) → (¬ p 2) → (¬ p 3) → (p 80) → (¬ p 9) → (¬ p 49) → False := by
  intro a0 a1 a2 a3 a4 a5 a6 a7
  have v0 : ¬ p 21 := (fun u => d5439 u a5 a1 a0)
  exact d5433 a4 a2 v0 a3 a7 a6 a1 a0

theorem c5510 (p : Nat → Prop)
    (d1530 : (¬ p 18) → (¬ p 35) → (¬ p 2) → (p 4) → False)
    (d5353 : (¬ p 2) → (¬ p 18) → (p 4) → (p 20) → False)
    (d373 : (p 10) → (p 15) → (p 130) → False)
    (d5303 : (¬ p 8) → (¬ p 9) → (p 67) → (p 66) → False)
    (d2797 : (¬ p 22) → (p 66) → (¬ p 24) → (¬ p 20) → False)
    (d5475 : (¬ p 67) → (¬ p 72) → (p 79) → (¬ p 8) → (¬ p 9) → False)
    (d26 : (p 22) → (p 25) → (p 90) → False)
    (d59 : (p 4) → (p 14) → (p 72) → False)
    (d199 : (p 35) → (p 45) → (p 72) → False)
    (d1808 : (¬ p 37) → (¬ p 90) → (¬ p 51) → (p 54) → False)
    (d10 : (¬ p 37) → (¬ p 40) → (¬ p 90) → False)
    (d748 : (¬ p 54) → (¬ p 58) → (¬ p 23) → (p 29) → (¬ p 50) → False)
    (d1383 : (p 44) → (p 40) → (p 34) → False)
    (d5085 : (¬ p 41) → (¬ p 44) → (p 13) → (p 10) → False)
    (d5090 : (¬ p 41) → (¬ p 44) → (¬ p 31) → (¬ p 29) → (p 130) → False)
    (d5340 : (¬ p 42) → (¬ p 45) → (¬ p 27) → (¬ p 29) → (¬ p 14) → (¬ p 13) → False)
    (d5468 : (¬ p 14) → (p 31) → (¬ p 29) → (¬ p 11) → (¬ p 13) → (¬ p 12) → (¬ p 15) → False)
    (d5355 : (¬ p 2) → (¬ p 18) → (p 27) → (p 11) → False)
    : (p 66) → (p 25) → (¬ p 23) → (¬ p 18) → (¬ p 37) → (¬ p 24) → (¬ p 50) → (¬ p 8) → (¬ p 42) → (¬ p 41) → (¬ p 58) → (¬ p 51) → (p 79) → (p 34) → (¬ p 12) → (¬ p 2) → (p 10) → (p 4) → (p 130) → (¬ p 9) → False := by
  intro a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19
  have v0 : p 35 := Classical.byContradiction (fun u => d1530 a3 u a15 a17)
  have v1 : ¬ p 20 := (fun u => d5353 a15 a3 a17 u)
  have v2 : ¬ p 15 := (fun u => d373 a16 u a18)
  have v3 : ¬ p 67 := (fun u => d5303 a7 a19 u a0)
  have v4 : p 22 := Classical.byContradiction (fun u => d2797 u a0 a5 v1)
  have v5 : p 72 := Classical.byContradiction (fun u => d5475 v3 u a12 a7 a19)
  have v6 : ¬ p 90 := (fun u => d26 v4 a1 u)
  have v7 : ¬ p 14 := (fun u => d59 a17 u v5)
  have v8 : ¬ p 45 := (fun u => d199 v0 u v5)
  have v9 : ¬ p 54 := (fun u => d1808 a4 v6 a11 u)
  have v10 : p 40 := Classical.byContradiction (fun u => d10 a4 u v6)
  have v11 : ¬ p 29 := (fun u => d748 v9 a10 a2 u a6)
  have v12 : ¬ p 44 := (fun u => d1383 u v10 a13)
  have v13 : ¬ p 13 := (fun u => d5085 a9 v12 u a16)
  have v14 : p 31 := Classical.byContradiction (fun u => d5090 a9 v12 u v11 a18)
  have v15 : p 27 := Classical.byContradiction (fun u => d5340 a8 v8 u v11 v7 v13)
  have v16 : p 11 := Classical.byContradiction (fun u => d5468 v7 v14 v11 u v13 a14 v2)
  exact d5355 a15 a3 v15 v16

theorem c5511 (p : Nat → Prop)
    (d1530 : (¬ p 18) → (¬ p 35) → (¬ p 2) → (p 4) → False)
    (d1134 : (p 34) → (p 38) → (p 42) → False)
    (d444 : (¬ p 51) → (¬ p 55) → (¬ p 91) → False)
    (d559 : (p 34) → (p 41) → (p 55) → False)
    (d4561 : (p 55) → (p 58) → (p 34) → False)
    (d373 : (p 10) → (p 15) → (p 130) → False)
    (d1044 : (¬ p 23) → (p 79) → (¬ p 21) → (¬ p 25) → False)
    (d75 : (¬ p 21) → (¬ p 23) → (¬ p 77) → False)
    (d264 : (p 77) → (p 79) → (p 100) → False)
    (d5510 : (p 66) → (p 25) → (¬ p 23) → (¬ p 18) → (¬ p 37) → (¬ p 24) → (¬ p 50) → (¬ p 8) → (¬ p 42) → (¬ p 41) → (¬ p 58) → (¬ p 51) → (p 79) → (p 34) → (¬ p 12) → (¬ p 2) → (p 10) → (p 4) → (p 130) → (¬ p 9) → False)
    (d273 : (¬ p 49) → (¬ p 53) → (¬ p 66) → False)
    (d5300 : (¬ p 8) → (¬ p 9) → (p 53) → (p 54) → False)
    (d4106 : (p 56) → (p 34) → (p 53) → False)
    (d884 : (¬ p 102) → (p 34) → (p 53) → (p 38) → False)
    (d4961 : (¬ p 136) → (¬ p 56) → (p 55) → (p 130) → False)
    (d3692 : (p 77) → (p 108) → (p 102) → False)
    (d5147 : (¬ p 100) → (¬ p 108) → (¬ p 54) → (¬ p 58) → (p 147) → False)
    (d4904 : (¬ p 147) → (¬ p 58) → (p 55) → (p 132) → False)
    (d5275 : (¬ p 132) → (¬ p 91) → (¬ p 100) → (¬ p 108) → (p 90) → False)
    (d10 : (¬ p 37) → (¬ p 40) → (¬ p 90) → False)
    (d291 : (p 35) → (p 40) → (p 67) → False)
    (d4559 : (p 35) → (p 45) → (p 40) → False)
    (d5475 : (¬ p 67) → (¬ p 72) → (p 79) → (¬ p 8) → (¬ p 9) → False)
    (d5338 : (¬ p 42) → (¬ p 45) → (¬ p 14) → (¬ p 15) → (p 136) → False)
    (d59 : (p 4) → (p 14) → (p 72) → False)
    : (¬ p 21) → (¬ p 23) → (¬ p 18) → (¬ p 37) → (¬ p 24) → (¬ p 50) → (¬ p 8) → (p 38) → (¬ p 51) → (p 79) → (p 34) → (¬ p 12) → (¬ p 2) → (¬ p 91) → (p 10) → (p 4) → (p 130) → (¬ p 9) → (¬ p 49) → False := by
  intro a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18
  have v0 : p 35 := Classical.byContradiction (fun u => d1530 a2 u a12 a15)
  have v1 : ¬ p 42 := (fun u => d1134 a10 a7 u)
  have v2 : p 55 := Classical.byContradiction (fun u => d444 a8 u a13)
  have v3 : ¬ p 41 := (fun u => d559 a10 u v2)
  have v4 : ¬ p 58 := (fun u => d4561 v2 u a10)
  have v5 : ¬ p 15 := (fun u => d373 a14 u a16)
  have v6 : p 25 := Classical.byContradiction (fun u => d1044 a1 a9 a0 u)
  have v7 : p 77 := Classical.byContradiction (fun u => d75 a0 a1 u)
  have v8 : ¬ p 100 := (fun u => d264 v7 a9 u)
  have v9 : ¬ p 66 := (fun u => d5510 u v6 a1 a2 a3 a4 a5 a6 v1 v3 v4 a8 a9 a10 a11 a12 a14 a15 a16 a17)
  have v10 : p 53 := Classical.byContradiction (fun u => d273 a18 u v9)
  have v11 : ¬ p 54 := (fun u => d5300 a6 a17 v10 u)
  have v12 : ¬ p 56 := (fun u => d4106 u a10 v10)
  have v13 : p 102 := Classical.byContradiction (fun u => d884 u a10 v10 a7)
  have v14 : p 136 := Classical.byContradiction (fun u => d4961 u v12 v2 a16)
  have v15 : ¬ p 108 := (fun u => d3692 v7 u v13)
  have v16 : ¬ p 147 := (fun u => d5147 v8 v15 v11 v4 u)
  have v17 : ¬ p 132 := (fun u => d4904 v16 v4 v2 u)
  have v18 : ¬ p 90 := (fun u => d5275 v17 a13 v8 v15 u)
  have v19 : p 40 := Classical.byContradiction (fun u => d10 a3 u v18)
  have v20 : ¬ p 67 := (fun u => d291 v0 v19 u)
  have v21 : ¬ p 45 := (fun u => d4559 v0 u v19)
  have v22 : p 72 := Classical.byContradiction (fun u => d5475 v20 u a9 a6 a17)
  have v23 : p 14 := Classical.byContradiction (fun u => d5338 v1 v21 u v5 v14)
  exact d59 a15 v23 v22

theorem c5512 (p : Nat → Prop)
    (d755 : (p 80) → (p 130) → (¬ p 9) → (p 5) → False)
    (d20 : (¬ p 4) → (¬ p 5) → (¬ p 63) → False)
    (d5486 : (p 3) → (p 130) → (p 80) → (¬ p 63) → (¬ p 9) → (¬ p 49) → False)
    (d5453 : (¬ p 10) → (p 130) → (p 80) → (¬ p 9) → False)
    (d4617 : (p 91) → (p 10) → (p 80) → False)
    (d5506 : (p 51) → (p 79) → (p 7) → (p 130) → (p 80) → (¬ p 63) → (¬ p 9) → (¬ p 49) → False)
    (d444 : (¬ p 51) → (¬ p 55) → (¬ p 91) → False)
    (d5508 : (p 8) → (p 55) → (p 79) → (p 7) → (¬ p 3) → (p 4) → (p 130) → (p 80) → (¬ p 9) → (¬ p 49) → False)
    (d5304 : (¬ p 8) → (¬ p 9) → (p 79) → (p 78) → False)
    (d1215 : (p 4) → (p 2) → (p 7) → False)
    (d505 : (¬ p 2) → (¬ p 3) → (¬ p 34) → False)
    (d559 : (p 34) → (p 41) → (p 55) → False)
    (d5278 : (¬ p 41) → (¬ p 38) → (p 7) → (p 10) → False)
    (d1134 : (p 34) → (p 38) → (p 42) → False)
    (d4561 : (p 55) → (p 58) → (p 34) → False)
    (d4556 : (p 12) → (p 4) → (p 7) → False)
    (d281 : (p 4) → (p 10) → (p 68) → False)
    (d5236 : (¬ p 78) → (¬ p 39) → (p 50) → (p 34) → False)
    (d5467 : (¬ p 39) → (¬ p 42) → (p 24) → (¬ p 8) → (¬ p 9) → False)
    (d5493 : (¬ p 39) → (p 37) → (¬ p 78) → (p 34) → (¬ p 2) → (¬ p 68) → (¬ p 5) → (¬ p 63) → False)
    (d5509 : (p 18) → (¬ p 39) → (p 79) → (¬ p 2) → (¬ p 3) → (p 80) → (¬ p 9) → (¬ p 49) → False)
    (d5358 : (¬ p 2) → (¬ p 18) → (p 7) → (p 23) → False)
    (d5511 : (¬ p 21) → (¬ p 23) → (¬ p 18) → (¬ p 37) → (¬ p 24) → (¬ p 50) → (¬ p 8) → (p 38) → (¬ p 51) → (p 79) → (p 34) → (¬ p 12) → (¬ p 2) → (¬ p 91) → (p 10) → (p 4) → (p 130) → (¬ p 9) → (¬ p 49) → False)
    (d424 : (p 21) → (p 25) → (p 79) → False)
    (d1519 : (¬ p 54) → (p 21) → (¬ p 58) → (¬ p 50) → (¬ p 23) → False)
    (d5319 : (¬ p 25) → (¬ p 27) → (¬ p 8) → (¬ p 9) → (¬ p 39) → (¬ p 42) → False)
    (d5300 : (¬ p 8) → (¬ p 9) → (p 53) → (p 54) → False)
    (d944 : (p 54) → (p 57) → (p 34) → False)
    (d5355 : (¬ p 2) → (¬ p 18) → (p 27) → (p 11) → False)
    (d5329 : (¬ p 11) → (¬ p 12) → (¬ p 57) → (¬ p 53) → (¬ p 39) → (¬ p 42) → False)
    : (¬ p 39) → (p 79) → (p 7) → (p 130) → (p 80) → (¬ p 63) → (¬ p 9) → (¬ p 49) → False := by
  intro a0 a1 a2 a3 a4 a5 a6 a7
  have v0 : ¬ p 5 := (fun u => d755 a4 a3 a6 u)
  have v1 : p 4 := Classical.byContradiction (fun u => d20 u v0 a5)
  have v2 : ¬ p 3 := (fun u => d5486 u a3 a4 a5 a6 a7)
  have v3 : p 10 := Classical.byContradiction (fun u => d5453 u a3 a4 a6)
  have v4 : ¬ p 91 := (fun u => d4617 u v3 a4)
  have v5 : ¬ p 51 := (fun u => d5506 u a1 a2 a3 a4 a5 a6 a7)
  have v6 : p 55 := Classical.byContradiction (fun u => d444 v5 u v4)
  have v7 : ¬ p 8 := (fun u => d5508 u v6 a1 a2 v2 v1 a3 a4 a6 a7)
  have v8 : ¬ p 78 := (fun u => d5304 v7 a6 a1 u)
  have v9 : ¬ p 2 := (fun u => d1215 v1 u a2)
  have v10 : p 34 := Classical.byContradiction (fun u => d505 v9 v2 u)
  have v11 : ¬ p 41 := (fun u => d559 v10 u v6)
  have v12 : p 38 := Classical.byContradiction (fun u => d5278 v11 u a2 v3)
  have v13 : ¬ p 42 := (fun u => d1134 v10 v12 u)
  have v14 : ¬ p 58 := (fun u => d4561 v6 u v10)
  have v15 : ¬ p 12 := (fun u => d4556 u v1 a2)
  have v16 : ¬ p 68 := (fun u => d281 v1 v3 u)
  have v17 : ¬ p 50 := (fun u => d5236 v8 a0 u v10)
  have v18 : ¬ p 24 := (fun u => d5467 a0 v13 u v7 a6)
  have v19 : ¬ p 37 := (fun u => d5493 a0 u v8 v10 v9 v16 v0 a5)
  have v20 : ¬ p 18 := (fun u => d5509 u a0 a1 v9 v2 a4 a6 a7)
  have v21 : ¬ p 23 := (fun u => d5358 v9 v20 a2 u)
  have v22 : p 21 := Classical.byContradiction (fun u => d5511 u v21 v20 v19 v18 v17 v7 v12 v5 a1 v10 v15 v9 v4 v3 v1 a3 a6 a7)
  have v23 : ¬ p 25 := (fun u => d424 v22 u a1)
  have v24 : p 54 := Classical.byContradiction (fun u => d1519 u v22 v14 v17 v21)
  have v25 : p 27 := Classical.byContradiction (fun u => d5319 v23 u v7 a6 a0 v13)
  have v26 : ¬ p 53 := (fun u => d5300 v7 a6 u v24)
  have v27 : ¬ p 57 := (fun u => d944 v24 u v10)
  have v28 : ¬ p 11 := (fun u => d5355 v9 v20 v25 u)
  exact d5329 v28 v15 v27 v26 a0 v13

theorem c5513 (p : Nat → Prop)
    (d264 : (p 77) → (p 79) → (p 100) → False)
    (d5294 : (¬ p 70) → (¬ p 65) → (¬ p 40) → (¬ p 43) → (p 100) → False)
    (d5115 : (¬ p 57) → (¬ p 53) → (p 66) → (p 70) → False)
    (d944 : (p 54) → (p 57) → (p 34) → False)
    (d4917 : (¬ p 54) → (¬ p 58) → (p 104) → (p 100) → False)
    (d4922 : (¬ p 54) → (¬ p 58) → (¬ p 104) → (¬ p 77) → (p 79) → False)
    : (p 100) → (p 66) → (¬ p 43) → (¬ p 53) → (¬ p 40) → (¬ p 58) → (p 79) → (p 34) → (¬ p 65) → False := by
  intro a0 a1 a2 a3 a4 a5 a6 a7 a8
  have v0 : ¬ p 77 := (fun u => d264 u a6 a0)
  have v1 : p 70 := Classical.byContradiction (fun u => d5294 u a8 a4 a2 a0)
  have v2 : p 57 := Classical.byContradiction (fun u => d5115 u a3 a1 v1)
  have v3 : ¬ p 54 := (fun u => d944 u v2 a7)
  have v4 : ¬ p 104 := (fun u => d4917 v3 a5 u a0)
  exact d4922 v3 a5 v4 v0 a6

theorem c5514 (p : Nat → Prop)
    (d1171 : (p 39) → (p 34) → (p 43) → False)
    (d5301 : (¬ p 8) → (¬ p 9) → (p 39) → (p 40) → False)
    (d1215 : (p 4) → (p 2) → (p 7) → False)
    (d5353 : (¬ p 2) → (¬ p 18) → (p 4) → (p 20) → False)
    (d5360 : (¬ p 2) → (¬ p 18) → (p 26) → (p 10) → False)
    (d5358 : (¬ p 2) → (¬ p 18) → (p 7) → (p 23) → False)
    (d442 : (¬ p 23) → (¬ p 25) → (¬ p 100) → False)
    (d5299 : (¬ p 8) → (¬ p 9) → (p 25) → (p 24) → False)
    (d5065 : (¬ p 40) → (¬ p 43) → (p 25) → (p 28) → False)
    (d2797 : (¬ p 22) → (p 66) → (¬ p 24) → (¬ p 20) → False)
    (d5153 : (¬ p 26) → (¬ p 28) → (p 141) → (p 130) → False)
    (d26 : (p 22) → (p 25) → (p 90) → False)
    (d4625 : (¬ p 141) → (p 37) → (p 39) → (p 34) → False)
    (d10 : (¬ p 37) → (¬ p 40) → (¬ p 90) → False)
    : (¬ p 18) → (¬ p 100) → (p 66) → (p 39) → (¬ p 8) → (p 34) → (p 7) → (p 10) → (p 4) → (p 130) → (¬ p 9) → False := by
  intro a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10
  have v0 : ¬ p 43 := (fun u => d1171 a3 a5 u)
  have v1 : ¬ p 40 := (fun u => d5301 a4 a10 a3 u)
  have v2 : ¬ p 2 := (fun u => d1215 a8 u a6)
  have v3 : ¬ p 20 := (fun u => d5353 v2 a0 a8 u)
  have v4 : ¬ p 26 := (fun u => d5360 v2 a0 u a7)
  have v5 : ¬ p 23 := (fun u => d5358 v2 a0 a6 u)
  have v6 : p 25 := Classical.byContradiction (fun u => d442 v5 u a1)
  have v7 : ¬ p 24 := (fun u => d5299 a4 a10 v6 u)
  have v8 : ¬ p 28 := (fun u => d5065 v1 v0 v6 u)
  have v9 : p 22 := Classical.byContradiction (fun u => d2797 u a2 v7 v3)
  have v10 : ¬ p 141 := (fun u => d5153 v4 v8 u a9)
  have v11 : ¬ p 90 := (fun u => d26 v9 v6 u)
  have v12 : ¬ p 37 := (fun u => d4625 v10 u a3 a5)
  exact d10 v12 v1 v11

theorem c5515 (p : Nat → Prop)
    (d373 : (p 10) → (p 15) → (p 130) → False)
    (d5153 : (¬ p 26) → (¬ p 28) → (p 141) → (p 130) → False)
    (d5199 : (¬ p 30) → (¬ p 28) → (¬ p 13) → (¬ p 12) → (¬ p 14) → False)
    (d5216 : (¬ p 14) → (¬ p 15) → (¬ p 43) → (¬ p 141) → (p 45) → False)
    (d5085 : (¬ p 41) → (¬ p 44) → (p 13) → (p 10) → False)
    (d5333 : (¬ p 42) → (¬ p 45) → (p 72) → (p 69) → False)
    (d5338 : (¬ p 42) → (¬ p 45) → (¬ p 14) → (¬ p 15) → (p 136) → False)
    (d5385 : (¬ p 74) → (¬ p 69) → (¬ p 42) → (¬ p 45) → (p 149) → False)
    (d284 : (p 18) → (p 29) → (p 44) → False)
    (d4961 : (¬ p 136) → (¬ p 56) → (p 55) → (p 130) → False)
    (d5384 : (¬ p 74) → (¬ p 69) → (¬ p 30) → (¬ p 149) → (p 27) → False)
    (d5171 : (¬ p 27) → (¬ p 29) → (p 13) → (p 11) → False)
    (d5314 : (¬ p 25) → (¬ p 27) → (¬ p 64) → (¬ p 69) → (p 90) → False)
    (d5320 : (¬ p 11) → (¬ p 12) → (p 57) → (p 56) → False)
    (d5051 : (¬ p 105) → (¬ p 88) → (p 64) → (p 72) → False)
    (d5115 : (¬ p 57) → (¬ p 53) → (p 66) → (p 70) → False)
    (d5296 : (¬ p 70) → (¬ p 65) → (¬ p 30) → (¬ p 28) → (p 105) → False)
    : (¬ p 28) → (¬ p 26) → (¬ p 74) → (¬ p 30) → (¬ p 88) → (¬ p 25) → (p 90) → (p 18) → (¬ p 14) → (p 72) → (p 66) → (¬ p 43) → (¬ p 53) → (¬ p 42) → (¬ p 41) → (p 55) → (¬ p 12) → (¬ p 65) → (p 10) → (p 130) → False := by
  intro a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19
  have v0 : ¬ p 15 := (fun u => d373 a18 u a19)
  have v1 : ¬ p 141 := (fun u => d5153 a1 a0 u a19)
  have v2 : p 13 := Classical.byContradiction (fun u => d5199 a3 a0 u a16 a8)
  have v3 : ¬ p 45 := (fun u => d5216 a8 v0 a11 v1 u)
  have v4 : p 44 := Classical.byContradiction (fun u => d5085 a14 u v2 a18)
  have v5 : ¬ p 69 := (fun u => d5333 a13 v3 a9 u)
  have v6 : ¬ p 136 := (fun u => d5338 a13 v3 a8 v0 u)
  have v7 : ¬ p 149 := (fun u => d5385 a2 v5 a13 v3 u)
  have v8 : ¬ p 29 := (fun u => d284 a7 u v4)
  have v9 : p 56 := Classical.byContradiction (fun u => d4961 v6 u a15 a19)
  have v10 : ¬ p 27 := (fun u => d5384 a2 v5 a3 v7 u)
  have v11 : ¬ p 11 := (fun u => d5171 v10 v8 v2 u)
  have v12 : p 64 := Classical.byContradiction (fun u => d5314 a5 v10 u v5 a6)
  have v13 : ¬ p 57 := (fun u => d5320 v11 a16 u v9)
  have v14 : p 105 := Classical.byContradiction (fun u => d5051 u a4 v12 a9)
  have v15 : ¬ p 70 := (fun u => d5115 v13 a12 a10 u)
  exact d5296 v15 a17 a3 a0 v14

theorem c5516 (p : Nat → Prop)
    (d5384 : (¬ p 74) → (¬ p 69) → (¬ p 30) → (¬ p 149) → (p 27) → False)
    (d5318 : (¬ p 25) → (¬ p 27) → (¬ p 29) → (¬ p 54) → (¬ p 58) → False)
    (d284 : (p 18) → (p 29) → (p 44) → False)
    (d5231 : (¬ p 30) → (¬ p 149) → (¬ p 44) → (¬ p 47) → (p 29) → False)
    : (¬ p 149) → (¬ p 54) → (¬ p 69) → (¬ p 74) → (¬ p 30) → (¬ p 25) → (p 18) → (¬ p 47) → (¬ p 58) → False := by
  intro a0 a1 a2 a3 a4 a5 a6 a7 a8
  have v0 : ¬ p 27 := (fun u => d5384 a3 a2 a4 a0 u)
  have v1 : p 29 := Classical.byContradiction (fun u => d5318 a5 v0 u a1 a8)
  have v2 : ¬ p 44 := (fun u => d284 a6 v1 u)
  exact d5231 a4 a0 v2 a7 v1

theorem c5517 (p : Nat → Prop)
    (d1134 : (p 34) → (p 38) → (p 42) → False)
    (d4611 : (p 70) → (p 4) → (p 69) → False)
    (d5115 : (¬ p 57) → (¬ p 53) → (p 66) → (p 70) → False)
    (d944 : (p 54) → (p 57) → (p 34) → False)
    (d5516 : (¬ p 149) → (¬ p 54) → (¬ p 69) → (¬ p 74) → (¬ p 30) → (¬ p 25) → (p 18) → (¬ p 47) → (¬ p 58) → False)
    (d5385 : (¬ p 74) → (¬ p 69) → (¬ p 42) → (¬ p 45) → (p 149) → False)
    (d437 : (p 38) → (p 45) → (p 105) → False)
    (d5051 : (¬ p 105) → (¬ p 88) → (p 64) → (p 72) → False)
    (d626 : (¬ p 64) → (¬ p 20) → (¬ p 69) → (p 27) → False)
    (d5314 : (¬ p 25) → (¬ p 27) → (¬ p 64) → (¬ p 69) → (p 90) → False)
    : (p 70) → (¬ p 20) → (¬ p 74) → (¬ p 30) → (¬ p 88) → (¬ p 25) → (p 90) → (p 18) → (p 72) → (p 66) → (¬ p 47) → (¬ p 53) → (p 38) → (¬ p 58) → (p 34) → (p 4) → False := by
  intro a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15
  have v0 : ¬ p 42 := (fun u => d1134 a14 a12 u)
  have v1 : ¬ p 69 := (fun u => d4611 a0 a15 u)
  have v2 : p 57 := Classical.byContradiction (fun u => d5115 u a11 a9 a0)
  have v3 : ¬ p 54 := (fun u => d944 u v2 a14)
  have v4 : p 149 := Classical.byContradiction (fun u => d5516 u v3 v1 a2 a3 a5 a7 a10 a13)
  have v5 : p 45 := Classical.byContradiction (fun u => d5385 a2 v1 v0 u v4)
  have v6 : ¬ p 105 := (fun u => d437 a12 v5 u)
  have v7 : ¬ p 64 := (fun u => d5051 v6 a4 u a8)
  have v8 : ¬ p 27 := (fun u => d626 v7 a1 v1 u)
  exact d5314 a5 v8 v7 v1 a6

theorem c5518 (p : Nat → Prop)
    (d127 : (p 18) → (p 24) → (p 39) → False)
    (d400 : (¬ p 22) → (¬ p 24) → (¬ p 89) → False)
    (d1957 : (p 90) → (p 88) → (p 22) → False)
    (d26 : (p 22) → (p 25) → (p 90) → False)
    (d373 : (p 10) → (p 15) → (p 130) → False)
    (d5220 : (¬ p 14) → (¬ p 15) → (¬ p 30) → (¬ p 28) → (p 141) → False)
    (d5515 : (¬ p 28) → (¬ p 26) → (¬ p 74) → (¬ p 30) → (¬ p 88) → (¬ p 25) → (p 90) → (p 18) → (¬ p 14) → (p 72) → (p 66) → (¬ p 43) → (¬ p 53) → (¬ p 42) → (¬ p 41) → (p 55) → (¬ p 12) → (¬ p 65) → (p 10) → (p 130) → False)
    (d4996 : (¬ p 43) → (¬ p 141) → (p 18) → (p 31) → False)
    (d5001 : (¬ p 43) → (¬ p 141) → (¬ p 96) → (¬ p 89) → (p 39) → False)
    (d4404 : (p 26) → (p 130) → (p 132) → False)
    (d1488 : (p 33) → (p 26) → (p 22) → False)
    (d5349 : (¬ p 31) → (¬ p 33) → (¬ p 132) → (¬ p 91) → (p 96) → False)
    : (¬ p 28) → (¬ p 74) → (¬ p 30) → (¬ p 89) → (p 90) → (p 18) → (¬ p 14) → (p 72) → (p 66) → (¬ p 43) → (¬ p 53) → (p 39) → (¬ p 42) → (¬ p 41) → (p 55) → (¬ p 12) → (¬ p 65) → (¬ p 91) → (p 10) → (p 130) → False := by
  intro a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19
  have v0 : ¬ p 24 := (fun u => d127 a5 u a11)
  have v1 : p 22 := Classical.byContradiction (fun u => d400 u v0 a3)
  have v2 : ¬ p 88 := (fun u => d1957 a4 u v1)
  have v3 : ¬ p 25 := (fun u => d26 v1 u a4)
  have v4 : ¬ p 15 := (fun u => d373 a18 u a19)
  have v5 : ¬ p 141 := (fun u => d5220 a6 v4 a2 a0 u)
  have v6 : p 26 := Classical.byContradiction (fun u => d5515 a0 u a1 a2 v2 v3 a4 a5 a6 a7 a8 a9 a10 a12 a13 a14 a15 a16 a18 a19)
  have v7 : ¬ p 31 := (fun u => d4996 a9 v5 a5 u)
  have v8 : p 96 := Classical.byContradiction (fun u => d5001 a9 v5 u a3 a11)
  have v9 : ¬ p 132 := (fun u => d4404 v6 a19 u)
  have v10 : ¬ p 33 := (fun u => d1488 u v6 v1)
  exact d5349 v7 v10 v9 a17 v8

theorem c5519 (p : Nat → Prop)
    (d5486 : (p 3) → (p 130) → (p 80) → (¬ p 63) → (¬ p 9) → (¬ p 49) → False)
    (d755 : (p 80) → (p 130) → (¬ p 9) → (p 5) → False)
    (d20 : (¬ p 4) → (¬ p 5) → (¬ p 63) → False)
    (d1215 : (p 4) → (p 2) → (p 7) → False)
    (d505 : (¬ p 2) → (¬ p 3) → (¬ p 34) → False)
    (d4556 : (p 12) → (p 4) → (p 7) → False)
    (d418 : (p 4) → (p 7) → (p 65) → False)
    (d5453 : (¬ p 10) → (p 130) → (p 80) → (¬ p 9) → False)
    (d4617 : (p 91) → (p 10) → (p 80) → False)
    (d5506 : (p 51) → (p 79) → (p 7) → (p 130) → (p 80) → (¬ p 63) → (¬ p 9) → (¬ p 49) → False)
    (d444 : (¬ p 51) → (¬ p 55) → (¬ p 91) → False)
    (d4561 : (p 55) → (p 58) → (p 34) → False)
    (d559 : (p 34) → (p 41) → (p 55) → False)
    (d5278 : (¬ p 41) → (¬ p 38) → (p 7) → (p 10) → False)
    (d1134 : (p 34) → (p 38) → (p 42) → False)
    (d5508 : (p 8) → (p 55) → (p 79) → (p 7) → (¬ p 3) → (p 4) → (p 130) → (p 80) → (¬ p 9) → (¬ p 49) → False)
    (d5512 : (¬ p 39) → (p 79) → (p 7) → (p 130) → (p 80) → (¬ p 63) → (¬ p 9) → (¬ p 49) → False)
    (d5301 : (¬ p 8) → (¬ p 9) → (p 39) → (p 40) → False)
    (d351 : (p 34) → (p 39) → (p 53) → False)
    (d1171 : (p 39) → (p 34) → (p 43) → False)
    (d106 : (p 38) → (p 39) → (p 99) → False)
    (d2479 : (p 47) → (p 39) → (p 38) → False)
    (d273 : (¬ p 49) → (¬ p 53) → (¬ p 66) → False)
    (d5303 : (¬ p 8) → (¬ p 9) → (p 67) → (p 66) → False)
    (d5475 : (¬ p 67) → (¬ p 72) → (p 79) → (¬ p 8) → (¬ p 9) → False)
    (d59 : (p 4) → (p 14) → (p 72) → False)
    (d5513 : (p 100) → (p 66) → (¬ p 43) → (¬ p 53) → (¬ p 40) → (¬ p 58) → (p 79) → (p 34) → (¬ p 65) → False)
    (d5514 : (¬ p 18) → (¬ p 100) → (p 66) → (p 39) → (¬ p 8) → (p 34) → (p 7) → (p 10) → (p 4) → (p 130) → (¬ p 9) → False)
    (d127 : (p 18) → (p 24) → (p 39) → False)
    (d668 : (p 18) → (p 39) → (p 37) → False)
    (d10 : (¬ p 37) → (¬ p 40) → (¬ p 90) → False)
    (d5302 : (¬ p 8) → (¬ p 9) → (p 89) → (p 90) → False)
    (d400 : (¬ p 22) → (¬ p 24) → (¬ p 89) → False)
    (d26 : (p 22) → (p 25) → (p 90) → False)
    (d1957 : (p 90) → (p 88) → (p 22) → False)
    (d442 : (¬ p 23) → (¬ p 25) → (¬ p 100) → False)
    (d1286 : (p 23) → (p 30) → (p 22) → False)
    (d863 : (p 74) → (¬ p 99) → (¬ p 30) → (p 23) → (p 66) → (p 72) → False)
    (d5518 : (¬ p 28) → (¬ p 74) → (¬ p 30) → (¬ p 89) → (p 90) → (p 18) → (¬ p 14) → (p 72) → (p 66) → (¬ p 43) → (¬ p 53) → (p 39) → (¬ p 42) → (¬ p 41) → (p 55) → (¬ p 12) → (¬ p 65) → (¬ p 91) → (p 10) → (p 130) → False)
    (d5288 : (¬ p 70) → (¬ p 65) → (p 28) → (p 23) → False)
    (d4590 : (p 28) → (p 20) → (p 23) → False)
    (d5517 : (p 70) → (¬ p 20) → (¬ p 74) → (¬ p 30) → (¬ p 88) → (¬ p 25) → (p 90) → (p 18) → (p 72) → (p 66) → (¬ p 47) → (¬ p 53) → (p 38) → (¬ p 58) → (p 34) → (p 4) → False)
    : (p 79) → (p 7) → (p 130) → (p 80) → (¬ p 63) → (¬ p 9) → (¬ p 49) → False := by
  intro a0 a1 a2 a3 a4 a5 a6
  have v0 : ¬ p 3 := (fun u => d5486 u a2 a3 a4 a5 a6)
  have v1 : ¬ p 5 := (fun u => d755 a3 a2 a5 u)
  have v2 : p 4 := Classical.byContradiction (fun u => d20 u v1 a4)
  have v3 : ¬ p 2 := (fun u => d1215 v2 u a1)
  have v4 : p 34 := Classical.byContradiction (fun u => d505 v3 v0 u)
  have v5 : ¬ p 12 := (fun u => d4556 u v2 a1)
  have v6 : ¬ p 65 := (fun u => d418 v2 a1 u)
  have v7 : p 10 := Classical.byContradiction (fun u => d5453 u a2 a3 a5)
  have v8 : ¬ p 91 := (fun u => d4617 u v7 a3)
  have v9 : ¬ p 51 := (fun u => d5506 u a0 a1 a2 a3 a4 a5 a6)
  have v10 : p 55 := Classical.byContradiction (fun u => d444 v9 u v8)
  have v11 : ¬ p 58 := (fun u => d4561 v10 u v4)
  have v12 : ¬ p 41 := (fun u => d559 v4 u v10)
  have v13 : p 38 := Classical.byContradiction (fun u => d5278 v12 u a1 v7)
  have v14 : ¬ p 42 := (fun u => d1134 v4 v13 u)
  have v15 : ¬ p 8 := (fun u => d5508 u v10 a0 a1 v0 v2 a2 a3 a5 a6)
  have v16 : p 39 := Classical.byContradiction (fun u => d5512 u a0 a1 a2 a3 a4 a5 a6)
  have v17 : ¬ p 40 := (fun u => d5301 v15 a5 v16 u)
  have v18 : ¬ p 53 := (fun u => d351 v4 v16 u)
  have v19 : ¬ p 43 := (fun u => d1171 v16 v4 u)
  have v20 : ¬ p 99 := (fun u => d106 v13 v16 u)
  have v21 : ¬ p 47 := (fun u => d2479 u v16 v13)
  have v22 : p 66 := Classical.byContradiction (fun u => d273 a6 v18 u)
  have v23 : ¬ p 67 := (fun u => d5303 v15 a5 u v22)
  have v24 : p 72 := Classical.byContradiction (fun u => d5475 v23 u a0 v15 a5)
  have v25 : ¬ p 14 := (fun u => d59 v2 u v24)
  have v26 : ¬ p 100 := (fun u => d5513 u v22 v19 v18 v17 v11 a0 v4 v6)
  have v27 : p 18 := Classical.byContradiction (fun u => d5514 u v26 v22 v16 v15 v4 a1 v7 v2 a2 a5)
  have v28 : ¬ p 24 := (fun u => d127 v27 u v16)
  have v29 : ¬ p 37 := (fun u => d668 v27 v16 u)
  have v30 : p 90 := Classical.byContradiction (fun u => d10 v29 v17 u)
  have v31 : ¬ p 89 := (fun u => d5302 v15 a5 u v30)
  have v32 : p 22 := Classical.byContradiction (fun u => d400 u v28 v31)
  have v33 : ¬ p 25 := (fun u => d26 v32 u v30)
  have v34 : ¬ p 88 := (fun u => d1957 v30 u v32)
  have v35 : p 23 := Classical.byContradiction (fun u => d442 u v33 v26)
  have v36 : ¬ p 30 := (fun u => d1286 v35 u v32)
  have v37 : ¬ p 74 := (fun u => d863 u v20 v36 v35 v22 v24)
  have v38 : p 28 := Classical.byContradiction (fun u => d5518 u v37 v36 v31 v30 v27 v25 v24 v22 v19 v18 v16 v14 v12 v10 v5 v6 v8 v7 a2)
  have v39 : p 70 := Classical.byContradiction (fun u => d5288 u v6 v38 v35)
  have v40 : ¬ p 20 := (fun u => d4590 v38 u v35)
  exact d5517 v39 v40 v37 v36 v34 v33 v30 v27 v24 v22 v21 v18 v13 v11 v4 v2

theorem c5520 (p : Nat → Prop)
    (d351 : (p 34) → (p 39) → (p 53) → False)
    (d1171 : (p 39) → (p 34) → (p 43) → False)
    (d3743 : (¬ p 49) → (¬ p 3) → (¬ p 53) → (p 8) → False)
    (d5461 : (p 90) → (p 123) → (¬ p 8) → (¬ p 9) → False)
    (d5301 : (¬ p 8) → (¬ p 9) → (p 39) → (p 40) → False)
    (d10 : (¬ p 37) → (¬ p 40) → (¬ p 90) → False)
    (d5066 : (¬ p 40) → (¬ p 43) → (p 141) → (p 123) → False)
    (d4625 : (¬ p 141) → (p 37) → (p 39) → (p 34) → False)
    : (p 39) → (p 123) → (p 34) → (¬ p 3) → (¬ p 9) → (¬ p 49) → False := by
  intro a0 a1 a2 a3 a4 a5
  have v0 : ¬ p 53 := (fun u => d351 a2 a0 u)
  have v1 : ¬ p 43 := (fun u => d1171 a0 a2 u)
  have v2 : ¬ p 8 := (fun u => d3743 a5 a3 v0 u)
  have v3 : ¬ p 90 := (fun u => d5461 u a1 v2 a4)
  have v4 : ¬ p 40 := (fun u => d5301 v2 a4 a0 u)
  have v5 : p 37 := Classical.byContradiction (fun u => d10 u v4 v3)
  have v6 : ¬ p 141 := (fun u => d5066 v4 v1 u a1)
  exact d4625 v6 v5 a0 a2

theorem c5521 (p : Nat → Prop)
    (d59 : (p 4) → (p 14) → (p 72) → False)
    (d4588 : (p 72) → (p 74) → (p 20) → False)
    (d432 : (p 20) → (p 30) → (p 72) → False)
    (d5216 : (¬ p 14) → (¬ p 15) → (¬ p 43) → (¬ p 141) → (p 45) → False)
    (d5384 : (¬ p 74) → (¬ p 69) → (¬ p 30) → (¬ p 149) → (p 27) → False)
    (d5385 : (¬ p 74) → (¬ p 69) → (¬ p 42) → (¬ p 45) → (p 149) → False)
    : (p 72) → (p 27) → (p 20) → (¬ p 69) → (¬ p 42) → (¬ p 141) → (¬ p 43) → (¬ p 15) → (p 4) → False := by
  intro a0 a1 a2 a3 a4 a5 a6 a7 a8
  have v0 : ¬ p 14 := (fun u => d59 a8 u a0)
  have v1 : ¬ p 74 := (fun u => d4588 a0 u a2)
  have v2 : ¬ p 30 := (fun u => d432 a2 u a0)
  have v3 : ¬ p 45 := (fun u => d5216 v0 a7 a6 a5 u)
  have v4 : p 149 := Classical.byContradiction (fun u => d5384 v1 a3 v2 u a1)
  exact d5385 v1 a3 a4 v3 v4

theorem c5522 (p : Nat → Prop)
    (d4590 : (p 28) → (p 20) → (p 23) → False)
    (d1134 : (p 34) → (p 38) → (p 42) → False)
    (d5066 : (¬ p 40) → (¬ p 43) → (p 141) → (p 123) → False)
    (d557 : (p 23) → (p 27) → (p 102) → False)
    (d4950 : (¬ p 102) → (¬ p 56) → (p 38) → (p 34) → False)
    (d5393 : (¬ p 138) → (¬ p 87) → (p 50) → (p 56) → False)
    (d4643 : (p 87) → (¬ p 91) → (p 143) → (p 80) → False)
    (d4902 : (¬ p 147) → (¬ p 58) → (p 50) → (p 87) → False)
    (d2025 : (¬ p 31) → (p 147) → (¬ p 33) → (¬ p 29) → False)
    (d5017 : (¬ p 143) → (¬ p 70) → (p 20) → (p 33) → False)
    (d5115 : (¬ p 57) → (¬ p 53) → (p 66) → (p 70) → False)
    (d5320 : (¬ p 11) → (¬ p 12) → (p 57) → (p 56) → False)
    (d5521 : (p 72) → (p 27) → (p 20) → (¬ p 69) → (¬ p 42) → (¬ p 141) → (¬ p 43) → (¬ p 15) → (p 4) → False)
    (d5219 : (¬ p 14) → (¬ p 15) → (¬ p 72) → (¬ p 67) → (p 123) → False)
    (d5200 : (¬ p 30) → (¬ p 28) → (¬ p 72) → (¬ p 67) → (¬ p 40) → (¬ p 43) → False)
    (d5331 : (¬ p 42) → (¬ p 45) → (p 14) → (p 11) → False)
    (d552 : (p 18) → (p 30) → (p 45) → False)
    : (p 27) → (p 23) → (¬ p 29) → (p 50) → (¬ p 138) → (¬ p 58) → (p 18) → (¬ p 31) → (p 20) → (¬ p 69) → (p 38) → (¬ p 43) → (¬ p 40) → (¬ p 67) → (p 66) → (¬ p 53) → (p 123) → (p 34) → (¬ p 12) → (¬ p 91) → (¬ p 15) → (p 4) → (p 80) → False := by
  intro a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22
  have v0 : ¬ p 28 := (fun u => d4590 u a8 a1)
  have v1 : ¬ p 42 := (fun u => d1134 a17 a10 u)
  have v2 : ¬ p 141 := (fun u => d5066 a12 a11 u a16)
  have v3 : ¬ p 102 := (fun u => d557 a1 a0 u)
  have v4 : p 56 := Classical.byContradiction (fun u => d4950 v3 u a10 a17)
  have v5 : p 87 := Classical.byContradiction (fun u => d5393 a4 u a3 v4)
  have v6 : ¬ p 143 := (fun u => d4643 v5 a19 u a22)
  have v7 : p 147 := Classical.byContradiction (fun u => d4902 u a5 a3 v5)
  have v8 : p 33 := Classical.byContradiction (fun u => d2025 a7 v7 u a2)
  have v9 : p 70 := Classical.byContradiction (fun u => d5017 v6 u a8 v8)
  have v10 : p 57 := Classical.byContradiction (fun u => d5115 u a15 a14 v9)
  have v11 : p 11 := Classical.byContradiction (fun u => d5320 u a18 v10 v4)
  have v12 : ¬ p 72 := (fun u => d5521 u a0 a8 a9 v1 v2 a11 a20 a21)
  have v13 : p 14 := Classical.byContradiction (fun u => d5219 u a20 v12 a13 a16)
  have v14 : p 30 := Classical.byContradiction (fun u => d5200 u v0 v12 a13 a12 a11)
  have v15 : p 45 := Classical.byContradiction (fun u => d5331 v1 u v13 v11)
  exact d552 a6 v14 v15

theorem c5523 (p : Nat → Prop)
    (d4561 : (p 55) → (p 58) → (p 34) → False)
    (d5461 : (p 90) → (p 123) → (¬ p 8) → (¬ p 9) → False)
    (d10 : (¬ p 37) → (¬ p 40) → (¬ p 90) → False)
    (d5066 : (¬ p 40) → (¬ p 43) → (p 141) → (p 123) → False)
    (d5000 : (¬ p 43) → (¬ p 141) → (p 96) → (p 37) → False)
    (d5306 : (¬ p 8) → (¬ p 9) → (¬ p 96) → (¬ p 89) → (p 123) → False)
    (d471 : (p 64) → (p 66) → (p 89) → False)
    (d755 : (p 80) → (p 130) → (¬ p 9) → (p 5) → False)
    (d2347 : (p 37) → (p 89) → (p 76) → False)
    (d213 : (¬ p 5) → (¬ p 6) → (¬ p 76) → False)
    (d4640 : (¬ p 64) → (p 37) → (p 6) → (¬ p 20) → False)
    (d1134 : (p 34) → (p 38) → (p 42) → False)
    (d4972 : (¬ p 39) → (¬ p 42) → (p 66) → (p 69) → False)
    (d5303 : (¬ p 8) → (¬ p 9) → (p 67) → (p 66) → False)
    (d5453 : (¬ p 10) → (p 130) → (p 80) → (¬ p 9) → False)
    (d4617 : (p 91) → (p 10) → (p 80) → False)
    (d373 : (p 10) → (p 15) → (p 130) → False)
    (d4590 : (p 28) → (p 20) → (p 23) → False)
    (d5522 : (p 27) → (p 23) → (¬ p 29) → (p 50) → (¬ p 138) → (¬ p 58) → (p 18) → (¬ p 31) → (p 20) → (¬ p 69) → (p 38) → (¬ p 43) → (¬ p 40) → (¬ p 67) → (p 66) → (¬ p 53) → (p 123) → (p 34) → (¬ p 12) → (¬ p 91) → (¬ p 15) → (p 4) → (p 80) → False)
    (d5319 : (¬ p 25) → (¬ p 27) → (¬ p 8) → (¬ p 9) → (¬ p 39) → (¬ p 42) → False)
    (d1049 : (¬ p 29) → (¬ p 27) → (p 136) → (¬ p 31) → False)
    (d638 : (p 25) → (p 20) → (p 30) → False)
    (d4961 : (¬ p 136) → (¬ p 56) → (p 55) → (p 130) → False)
    (d5200 : (¬ p 30) → (¬ p 28) → (¬ p 72) → (¬ p 67) → (¬ p 40) → (¬ p 43) → False)
    (d59 : (p 4) → (p 14) → (p 72) → False)
    (d5199 : (¬ p 30) → (¬ p 28) → (¬ p 13) → (¬ p 12) → (¬ p 14) → False)
    (d5171 : (¬ p 27) → (¬ p 29) → (p 13) → (p 11) → False)
    (d5329 : (¬ p 11) → (¬ p 12) → (¬ p 57) → (¬ p 53) → (¬ p 39) → (¬ p 42) → False)
    (d5320 : (¬ p 11) → (¬ p 12) → (p 57) → (p 56) → False)
    : (p 23) → (¬ p 29) → (p 50) → (¬ p 138) → (p 18) → (¬ p 31) → (p 55) → (p 38) → (¬ p 43) → (¬ p 40) → (p 66) → (¬ p 53) → (¬ p 8) → (¬ p 39) → (p 123) → (p 34) → (¬ p 12) → (p 4) → (p 130) → (p 80) → (¬ p 9) → False := by
  intro a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20
  have v0 : ¬ p 58 := (fun u => d4561 a6 u a15)
  have v1 : ¬ p 90 := (fun u => d5461 u a14 a12 a20)
  have v2 : p 37 := Classical.byContradiction (fun u => d10 u a9 v1)
  have v3 : ¬ p 141 := (fun u => d5066 a9 a8 u a14)
  have v4 : ¬ p 96 := (fun u => d5000 a8 v3 u v2)
  have v5 : p 89 := Classical.byContradiction (fun u => d5306 a12 a20 v4 u a14)
  have v6 : ¬ p 64 := (fun u => d471 u a10 v5)
  have v7 : ¬ p 5 := (fun u => d755 a19 a18 a20 u)
  have v8 : ¬ p 76 := (fun u => d2347 v2 v5 u)
  have v9 : p 6 := Classical.byContradiction (fun u => d213 v7 u v8)
  have v10 : p 20 := Classical.byContradiction (fun u => d4640 v6 v2 v9 u)
  have v11 : ¬ p 42 := (fun u => d1134 a15 a7 u)
  have v12 : ¬ p 69 := (fun u => d4972 a13 v11 a10 u)
  have v13 : ¬ p 67 := (fun u => d5303 a12 a20 u a10)
  have v14 : p 10 := Classical.byContradiction (fun u => d5453 u a18 a19 a20)
  have v15 : ¬ p 91 := (fun u => d4617 u v14 a19)
  have v16 : ¬ p 15 := (fun u => d373 v14 u a18)
  have v17 : ¬ p 28 := (fun u => d4590 u v10 a0)
  have v18 : ¬ p 27 := (fun u => d5522 u a0 a1 a2 a3 v0 a4 a5 v10 v12 a7 a8 a9 v13 a10 a11 a14 a15 a16 v15 v16 a17 a19)
  have v19 : p 25 := Classical.byContradiction (fun u => d5319 u v18 a12 a20 a13 v11)
  have v20 : ¬ p 136 := (fun u => d1049 a1 v18 u a5)
  have v21 : ¬ p 30 := (fun u => d638 v19 v10 u)
  have v22 : p 56 := Classical.byContradiction (fun u => d4961 v20 u a6 a18)
  have v23 : p 72 := Classical.byContradiction (fun u => d5200 v21 v17 u v13 a9 a8)
  have v24 : ¬ p 14 := (fun u => d59 a17 u v23)
  have v25 : p 13 := Classical.byContradiction (fun u => d5199 v21 v17 u a16 v24)
  have v26 : ¬ p 11 := (fun u => d5171 v18 a1 v25 u)
  have v27 : p 57 := Classical.byContradiction (fun u => d5329 v26 a16 u a11 a13 v11)
  exact d5320 v26 a16 v27 v22

theorem c5524 (p : Nat → Prop)
    (d638 : (p 25) → (p 20) → (p 30) → False)
    (d3714 : (p 28) → (p 25) → (p 18) → False)
    (d5200 : (¬ p 30) → (¬ p 28) → (¬ p 72) → (¬ p 67) → (¬ p 40) → (¬ p 43) → False)
    (d59 : (p 4) → (p 14) → (p 72) → False)
    (d5521 : (p 72) → (p 27) → (p 20) → (¬ p 69) → (¬ p 42) → (¬ p 141) → (¬ p 43) → (¬ p 15) → (p 4) → False)
    (d5199 : (¬ p 30) → (¬ p 28) → (¬ p 13) → (¬ p 12) → (¬ p 14) → False)
    (d1049 : (¬ p 29) → (¬ p 27) → (p 136) → (¬ p 31) → False)
    (d5171 : (¬ p 27) → (¬ p 29) → (p 13) → (p 11) → False)
    (d4961 : (¬ p 136) → (¬ p 56) → (p 55) → (p 130) → False)
    (d5329 : (¬ p 11) → (¬ p 12) → (¬ p 57) → (¬ p 53) → (¬ p 39) → (¬ p 42) → False)
    (d5320 : (¬ p 11) → (¬ p 12) → (p 57) → (p 56) → False)
    : (p 25) → (¬ p 29) → (p 18) → (¬ p 31) → (p 20) → (p 55) → (¬ p 69) → (¬ p 42) → (¬ p 141) → (¬ p 43) → (¬ p 40) → (¬ p 67) → (¬ p 53) → (¬ p 39) → (¬ p 12) → (¬ p 15) → (p 4) → (p 130) → False := by
  intro a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17
  have v0 : ¬ p 30 := (fun u => d638 a0 a4 u)
  have v1 : ¬ p 28 := (fun u => d3714 u a0 a2)
  have v2 : p 72 := Classical.byContradiction (fun u => d5200 v0 v1 u a11 a10 a9)
  have v3 : ¬ p 14 := (fun u => d59 a16 u v2)
  have v4 : ¬ p 27 := (fun u => d5521 v2 u a4 a6 a7 a8 a9 a15 a16)
  have v5 : p 13 := Classical.byContradiction (fun u => d5199 v0 v1 u a14 v3)
  have v6 : ¬ p 136 := (fun u => d1049 a1 v4 u a3)
  have v7 : ¬ p 11 := (fun u => d5171 v4 a1 v5 u)
  have v8 : p 56 := Classical.byContradiction (fun u => d4961 v6 u a5 a17)
  have v9 : p 57 := Classical.byContradiction (fun u => d5329 v7 a14 u a12 a13 a7)
  exact d5320 v7 a14 v9 v8

theorem c5525 (p : Nat → Prop)
    (d4536 : (p 78) → (p 80) → (p 21) → False)
    (d5029 : (¬ p 123) → (¬ p 79) → (p 80) → (p 130) → False)
    (d5461 : (p 90) → (p 123) → (¬ p 8) → (¬ p 9) → False)
    (d10 : (¬ p 37) → (¬ p 40) → (¬ p 90) → False)
    (d5303 : (¬ p 8) → (¬ p 9) → (p 67) → (p 66) → False)
    (d4556 : (p 12) → (p 4) → (p 7) → False)
    (d418 : (p 4) → (p 7) → (p 65) → False)
    (d1215 : (p 4) → (p 2) → (p 7) → False)
    (d5453 : (¬ p 10) → (p 130) → (p 80) → (¬ p 9) → False)
    (d4617 : (p 91) → (p 10) → (p 80) → False)
    (d373 : (p 10) → (p 15) → (p 130) → False)
    (d755 : (p 80) → (p 130) → (¬ p 9) → (p 5) → False)
    (d5066 : (¬ p 40) → (¬ p 43) → (p 141) → (p 123) → False)
    (d4995 : (¬ p 43) → (¬ p 141) → (p 41) → (p 130) → False)
    (d5000 : (¬ p 43) → (¬ p 141) → (p 96) → (p 37) → False)
    (d5278 : (¬ p 41) → (¬ p 38) → (p 7) → (p 10) → False)
    (d5306 : (¬ p 8) → (¬ p 9) → (¬ p 96) → (¬ p 89) → (p 123) → False)
    (d1134 : (p 34) → (p 38) → (p 42) → False)
    (d471 : (p 64) → (p 66) → (p 89) → False)
    (d2347 : (p 37) → (p 89) → (p 76) → False)
    (d4589 : (p 89) → (p 66) → (p 24) → False)
    (d987 : (p 51) → (p 89) → (p 78) → (p 34) → (¬ p 79) → False)
    (d4972 : (¬ p 39) → (¬ p 42) → (p 66) → (p 69) → False)
    (d213 : (¬ p 5) → (¬ p 6) → (¬ p 76) → False)
    (d5105 : (¬ p 24) → (¬ p 26) → (p 78) → (p 80) → False)
    (d444 : (¬ p 51) → (¬ p 55) → (¬ p 91) → False)
    (d4640 : (¬ p 64) → (p 37) → (p 6) → (¬ p 20) → False)
    (d11 : (p 26) → (p 31) → (p 130) → False)
    (d4404 : (p 26) → (p 130) → (p 132) → False)
    (d5360 : (¬ p 2) → (¬ p 18) → (p 26) → (p 10) → False)
    (d5273 : (¬ p 132) → (¬ p 91) → (¬ p 64) → (¬ p 69) → (p 138) → False)
    (d4940 : (¬ p 21) → (¬ p 50) → (p 34) → (p 18) → False)
    (d889 : (p 26) → (p 29) → (p 18) → False)
    (d5523 : (p 23) → (¬ p 29) → (p 50) → (¬ p 138) → (p 18) → (¬ p 31) → (p 55) → (p 38) → (¬ p 43) → (¬ p 40) → (p 66) → (¬ p 53) → (¬ p 8) → (¬ p 39) → (p 123) → (p 34) → (¬ p 12) → (p 4) → (p 130) → (p 80) → (¬ p 9) → False)
    (d5524 : (p 25) → (¬ p 29) → (p 18) → (¬ p 31) → (p 20) → (p 55) → (¬ p 69) → (¬ p 42) → (¬ p 141) → (¬ p 43) → (¬ p 40) → (¬ p 67) → (¬ p 53) → (¬ p 39) → (¬ p 12) → (¬ p 15) → (p 4) → (p 130) → False)
    (d5319 : (¬ p 25) → (¬ p 27) → (¬ p 8) → (¬ p 9) → (¬ p 39) → (¬ p 42) → False)
    (d442 : (¬ p 23) → (¬ p 25) → (¬ p 100) → False)
    (d5521 : (p 72) → (p 27) → (p 20) → (¬ p 69) → (¬ p 42) → (¬ p 141) → (¬ p 43) → (¬ p 15) → (p 4) → False)
    (d5294 : (¬ p 70) → (¬ p 65) → (¬ p 40) → (¬ p 43) → (p 100) → False)
    (d5219 : (¬ p 14) → (¬ p 15) → (¬ p 72) → (¬ p 67) → (p 123) → False)
    (d5136 : (¬ p 72) → (¬ p 67) → (p 105) → (p 100) → False)
    (d5115 : (¬ p 57) → (¬ p 53) → (p 66) → (p 70) → False)
    (d587 : (p 20) → (p 28) → (p 70) → False)
    (d5200 : (¬ p 30) → (¬ p 28) → (¬ p 72) → (¬ p 67) → (¬ p 40) → (¬ p 43) → False)
    (d552 : (p 18) → (p 30) → (p 45) → False)
    (d5271 : (¬ p 132) → (¬ p 91) → (¬ p 150) → (¬ p 45) → (p 37) → False)
    (d5331 : (¬ p 42) → (¬ p 45) → (p 14) → (p 11) → False)
    (d5274 : (¬ p 132) → (¬ p 91) → (¬ p 105) → (¬ p 88) → (p 150) → False)
    (d5320 : (¬ p 11) → (¬ p 12) → (p 57) → (p 56) → False)
    (d5039 : (¬ p 64) → (¬ p 69) → (p 102) → (p 88) → False)
    (d4950 : (¬ p 102) → (¬ p 56) → (p 38) → (p 34) → False)
    : (¬ p 43) → (p 78) → (¬ p 40) → (p 66) → (¬ p 53) → (¬ p 8) → (¬ p 39) → (¬ p 79) → (p 34) → (p 7) → (p 4) → (p 130) → (p 80) → (¬ p 9) → False := by
  intro a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13
  have v0 : ¬ p 21 := (fun u => d4536 a1 a12 u)
  have v1 : p 123 := Classical.byContradiction (fun u => d5029 u a7 a12 a11)
  have v2 : ¬ p 90 := (fun u => d5461 u v1 a5 a13)
  have v3 : p 37 := Classical.byContradiction (fun u => d10 u a2 v2)
  have v4 : ¬ p 67 := (fun u => d5303 a5 a13 u a3)
  have v5 : ¬ p 12 := (fun u => d4556 u a10 a9)
  have v6 : ¬ p 65 := (fun u => d418 a10 a9 u)
  have v7 : ¬ p 2 := (fun u => d1215 a10 u a9)
  have v8 : p 10 := Classical.byContradiction (fun u => d5453 u a11 a12 a13)
  have v9 : ¬ p 91 := (fun u => d4617 u v8 a12)
  have v10 : ¬ p 15 := (fun u => d373 v8 u a11)
  have v11 : ¬ p 5 := (fun u => d755 a12 a11 a13 u)
  have v12 : ¬ p 141 := (fun u => d5066 a2 a0 u v1)
  have v13 : ¬ p 41 := (fun u => d4995 a0 v12 u a11)
  have v14 : ¬ p 96 := (fun u => d5000 a0 v12 u v3)
  have v15 : p 38 := Classical.byContradiction (fun u => d5278 v13 u a9 v8)
  have v16 : p 89 := Classical.byContradiction (fun u => d5306 a5 a13 v14 u v1)
  have v17 : ¬ p 42 := (fun u => d1134 a8 v15 u)
  have v18 : ¬ p 64 := (fun u => d471 u a3 v16)
  have v19 : ¬ p 76 := (fun u => d2347 v3 v16 u)
  have v20 : ¬ p 24 := (fun u => d4589 v16 a3 u)
  have v21 : ¬ p 51 := (fun u => d987 u v16 a1 a8 a7)
  have v22 : ¬ p 69 := (fun u => d4972 a6 v17 a3 u)
  have v23 : p 6 := Classical.byContradiction (fun u => d213 v11 u v19)
  have v24 : p 26 := Classical.byContradiction (fun u => d5105 v20 u a1 a12)
  have v25 : p 55 := Classical.byContradiction (fun u => d444 v21 u v9)
  have v26 : p 20 := Classical.byContradiction (fun u => d4640 v18 v3 v23 u)
  have v27 : ¬ p 31 := (fun u => d11 v24 u a11)
  have v28 : ¬ p 132 := (fun u => d4404 v24 a11 u)
  have v29 : p 18 := Classical.byContradiction (fun u => d5360 v7 u v24 v8)
  have v30 : ¬ p 138 := (fun u => d5273 v28 v9 v18 v22 u)
  have v31 : p 50 := Classical.byContradiction (fun u => d4940 v0 u a8 v29)
  have v32 : ¬ p 29 := (fun u => d889 v24 u v29)
  have v33 : ¬ p 23 := (fun u => d5523 u v32 v31 v30 v29 v27 v25 v15 a0 a2 a3 a4 a5 a6 v1 a8 v5 a10 a11 a12 a13)
  have v34 : ¬ p 25 := (fun u => d5524 u v32 v29 v27 v26 v25 v22 v17 v12 a0 a2 v4 a4 a6 v5 v10 a10 a11)
  have v35 : p 27 := Classical.byContradiction (fun u => d5319 v34 u a5 a13 a6 v17)
  have v36 : p 100 := Classical.byContradiction (fun u => d442 v33 v34 u)
  have v37 : ¬ p 72 := (fun u => d5521 u v35 v26 v22 v17 v12 a0 v10 a10)
  have v38 : p 70 := Classical.byContradiction (fun u => d5294 u v6 a2 a0 v36)
  have v39 : p 14 := Classical.byContradiction (fun u => d5219 u v10 v37 v4 v1)
  have v40 : ¬ p 105 := (fun u => d5136 v37 v4 u v36)
  have v41 : p 57 := Classical.byContradiction (fun u => d5115 u a4 a3 v38)
  have v42 : ¬ p 28 := (fun u => d587 v26 u v38)
  have v43 : p 30 := Classical.byContradiction (fun u => d5200 u v42 v37 v4 a2 a0)
  have v44 : ¬ p 45 := (fun u => d552 v29 v43 u)
  have v45 : p 150 := Classical.byContradiction (fun u => d5271 v28 v9 u v44 v3)
  have v46 : ¬ p 11 := (fun u => d5331 v17 v44 v39 u)
  have v47 : p 88 := Classical.byContradiction (fun u => d5274 v28 v9 v40 u v45)
  have v48 : ¬ p 56 := (fun u => d5320 v46 v5 v41 u)
  have v49 : ¬ p 102 := (fun u => d5039 v18 v22 u v47)
  exact d4950 v49 v48 v15 a8

theorem c5526 (p : Nat → Prop)
    (d5115 : (¬ p 57) → (¬ p 53) → (p 66) → (p 70) → False)
    (d5453 : (¬ p 10) → (p 130) → (p 80) → (¬ p 9) → False)
    (d4617 : (p 91) → (p 10) → (p 80) → False)
    (d373 : (p 10) → (p 15) → (p 130) → False)
    (d5467 : (¬ p 39) → (¬ p 42) → (p 24) → (¬ p 8) → (¬ p 9) → False)
    (d5329 : (¬ p 11) → (¬ p 12) → (¬ p 57) → (¬ p 53) → (¬ p 39) → (¬ p 42) → False)
    (d5319 : (¬ p 25) → (¬ p 27) → (¬ p 8) → (¬ p 9) → (¬ p 39) → (¬ p 42) → False)
    (d5105 : (¬ p 24) → (¬ p 26) → (p 78) → (p 80) → False)
    (d5355 : (¬ p 2) → (¬ p 18) → (p 27) → (p 11) → False)
    (d11 : (p 26) → (p 31) → (p 130) → False)
    (d4404 : (p 26) → (p 130) → (p 132) → False)
    (d55 : (p 18) → (p 22) → (p 37) → False)
    (d3721 : (p 43) → (p 18) → (p 45) → False)
    (d2797 : (¬ p 22) → (p 66) → (¬ p 24) → (¬ p 20) → False)
    (d5271 : (¬ p 132) → (¬ p 91) → (¬ p 150) → (¬ p 45) → (p 37) → False)
    (d5331 : (¬ p 42) → (¬ p 45) → (p 14) → (p 11) → False)
    (d5348 : (¬ p 31) → (¬ p 33) → (¬ p 14) → (¬ p 15) → (p 150) → False)
    (d4204 : (p 33) → (¬ p 70) → (p 150) → (p 20) → False)
    : (¬ p 42) → (¬ p 25) → (¬ p 57) → (p 43) → (p 78) → (p 37) → (p 66) → (¬ p 53) → (¬ p 8) → (¬ p 39) → (¬ p 12) → (¬ p 2) → (p 130) → (p 80) → (¬ p 9) → False := by
  intro a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14
  have v0 : ¬ p 70 := (fun u => d5115 a2 a7 a6 u)
  have v1 : p 10 := Classical.byContradiction (fun u => d5453 u a12 a13 a14)
  have v2 : ¬ p 91 := (fun u => d4617 u v1 a13)
  have v3 : ¬ p 15 := (fun u => d373 v1 u a12)
  have v4 : ¬ p 24 := (fun u => d5467 a9 a0 u a8 a14)
  have v5 : p 11 := Classical.byContradiction (fun u => d5329 u a10 a2 a7 a9 a0)
  have v6 : p 27 := Classical.byContradiction (fun u => d5319 a1 u a8 a14 a9 a0)
  have v7 : p 26 := Classical.byContradiction (fun u => d5105 v4 u a4 a13)
  have v8 : p 18 := Classical.byContradiction (fun u => d5355 a11 u v6 v5)
  have v9 : ¬ p 31 := (fun u => d11 v7 u a12)
  have v10 : ¬ p 132 := (fun u => d4404 v7 a12 u)
  have v11 : ¬ p 22 := (fun u => d55 v8 u a5)
  have v12 : ¬ p 45 := (fun u => d3721 a3 v8 u)
  have v13 : p 20 := Classical.byContradiction (fun u => d2797 v11 a6 v4 u)
  have v14 : p 150 := Classical.byContradiction (fun u => d5271 v10 v2 u v12 a5)
  have v15 : ¬ p 14 := (fun u => d5331 a0 v12 u v5)
  have v16 : p 33 := Classical.byContradiction (fun u => d5348 v9 u v15 v3 v14)
  exact d4204 v16 v0 v14 v13

theorem c5527 (p : Nat → Prop)
    (d5440 : (p 7) → (¬ p 3) → (p 4) → (¬ p 35) → (p 42) → False)
    (d2715 : (p 37) → (p 42) → (p 35) → False)
    : (p 42) → (p 37) → (p 7) → (¬ p 3) → (p 4) → False := by
  intro a0 a1 a2 a3 a4
  have v0 : p 35 := Classical.byContradiction (fun u => d5440 a2 a3 a4 u a0)
  exact d2715 a1 a0 v0

theorem c5528 (p : Nat → Prop)
    (d5029 : (¬ p 123) → (¬ p 79) → (p 80) → (p 130) → False)
    (d5461 : (p 90) → (p 123) → (¬ p 8) → (¬ p 9) → False)
    (d755 : (p 80) → (p 130) → (¬ p 9) → (p 5) → False)
    (d20 : (¬ p 4) → (¬ p 5) → (¬ p 63) → False)
    (d1215 : (p 4) → (p 2) → (p 7) → False)
    (d505 : (¬ p 2) → (¬ p 3) → (¬ p 34) → False)
    (d4556 : (p 12) → (p 4) → (p 7) → False)
    (d5453 : (¬ p 10) → (p 130) → (p 80) → (¬ p 9) → False)
    (d4617 : (p 91) → (p 10) → (p 80) → False)
    (d373 : (p 10) → (p 15) → (p 130) → False)
    (d281 : (p 4) → (p 10) → (p 68) → False)
    (d10 : (¬ p 37) → (¬ p 40) → (¬ p 90) → False)
    (d5493 : (¬ p 39) → (p 37) → (¬ p 78) → (p 34) → (¬ p 2) → (¬ p 68) → (¬ p 5) → (¬ p 63) → False)
    (d5525 : (¬ p 43) → (p 78) → (¬ p 40) → (p 66) → (¬ p 53) → (¬ p 8) → (¬ p 39) → (¬ p 79) → (p 34) → (p 7) → (p 4) → (p 130) → (p 80) → (¬ p 9) → False)
    (d52 : (p 34) → (p 43) → (p 57) → False)
    (d5115 : (¬ p 57) → (¬ p 53) → (p 66) → (p 70) → False)
    (d5527 : (p 42) → (p 37) → (p 7) → (¬ p 3) → (p 4) → False)
    (d5467 : (¬ p 39) → (¬ p 42) → (p 24) → (¬ p 8) → (¬ p 9) → False)
    (d5329 : (¬ p 11) → (¬ p 12) → (¬ p 57) → (¬ p 53) → (¬ p 39) → (¬ p 42) → False)
    (d5526 : (¬ p 42) → (¬ p 25) → (¬ p 57) → (p 43) → (p 78) → (p 37) → (p 66) → (¬ p 53) → (¬ p 8) → (¬ p 39) → (¬ p 12) → (¬ p 2) → (p 130) → (p 80) → (¬ p 9) → False)
    (d5105 : (¬ p 24) → (¬ p 26) → (p 78) → (p 80) → False)
    (d114 : (p 25) → (p 31) → (p 123) → False)
    (d4404 : (p 26) → (p 130) → (p 132) → False)
    (d5360 : (¬ p 2) → (¬ p 18) → (p 26) → (p 10) → False)
    (d55 : (p 18) → (p 22) → (p 37) → False)
    (d3721 : (p 43) → (p 18) → (p 45) → False)
    (d2797 : (¬ p 22) → (p 66) → (¬ p 24) → (¬ p 20) → False)
    (d5271 : (¬ p 132) → (¬ p 91) → (¬ p 150) → (¬ p 45) → (p 37) → False)
    (d5331 : (¬ p 42) → (¬ p 45) → (p 14) → (p 11) → False)
    (d5348 : (¬ p 31) → (¬ p 33) → (¬ p 14) → (¬ p 15) → (p 150) → False)
    (d4204 : (p 33) → (¬ p 70) → (p 150) → (p 20) → False)
    : (¬ p 40) → (p 66) → (¬ p 53) → (¬ p 8) → (¬ p 39) → (¬ p 79) → (p 7) → (¬ p 3) → (p 130) → (p 80) → (¬ p 63) → (¬ p 9) → False := by
  intro a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11
  have v0 : p 123 := Classical.byContradiction (fun u => d5029 u a5 a9 a8)
  have v1 : ¬ p 90 := (fun u => d5461 u v0 a3 a11)
  have v2 : ¬ p 5 := (fun u => d755 a9 a8 a11 u)
  have v3 : p 4 := Classical.byContradiction (fun u => d20 u v2 a10)
  have v4 : ¬ p 2 := (fun u => d1215 v3 u a6)
  have v5 : p 34 := Classical.byContradiction (fun u => d505 v4 a7 u)
  have v6 : ¬ p 12 := (fun u => d4556 u v3 a6)
  have v7 : p 10 := Classical.byContradiction (fun u => d5453 u a8 a9 a11)
  have v8 : ¬ p 91 := (fun u => d4617 u v7 a9)
  have v9 : ¬ p 15 := (fun u => d373 v7 u a8)
  have v10 : ¬ p 68 := (fun u => d281 v3 v7 u)
  have v11 : p 37 := Classical.byContradiction (fun u => d10 u a0 v1)
  have v12 : p 78 := Classical.byContradiction (fun u => d5493 a4 v11 u v5 v4 v10 v2 a10)
  have v13 : p 43 := Classical.byContradiction (fun u => d5525 u v12 a0 a1 a2 a3 a4 a5 v5 a6 v3 a8 a9 a11)
  have v14 : ¬ p 57 := (fun u => d52 v5 v13 u)
  have v15 : ¬ p 70 := (fun u => d5115 v14 a2 a1 u)
  have v16 : ¬ p 42 := (fun u => d5527 u v11 a6 a7 v3)
  have v17 : ¬ p 24 := (fun u => d5467 a4 v16 u a3 a11)
  have v18 : p 11 := Classical.byContradiction (fun u => d5329 u v6 v14 a2 a4 v16)
  have v19 : p 25 := Classical.byContradiction (fun u => d5526 v16 u v14 v13 v12 v11 a1 a2 a3 a4 v6 v4 a8 a9 a11)
  have v20 : p 26 := Classical.byContradiction (fun u => d5105 v17 u v12 a9)
  have v21 : ¬ p 31 := (fun u => d114 v19 u v0)
  have v22 : ¬ p 132 := (fun u => d4404 v20 a8 u)
  have v23 : p 18 := Classical.byContradiction (fun u => d5360 v4 u v20 v7)
  have v24 : ¬ p 22 := (fun u => d55 v23 u v11)
  have v25 : ¬ p 45 := (fun u => d3721 v13 v23 u)
  have v26 : p 20 := Classical.byContradiction (fun u => d2797 v24 a1 v17 u)
  have v27 : p 150 := Classical.byContradiction (fun u => d5271 v22 v8 u v25 v11)
  have v28 : ¬ p 14 := (fun u => d5331 v16 v25 u v18)
  have v29 : p 33 := Classical.byContradiction (fun u => d5348 v21 u v28 v9 v27)
  exact d4204 v29 v15 v27 v26

theorem c5529 (p : Nat → Prop)
    (d225 : (p 18) → (p 25) → (p 40) → False)
    (d5299 : (¬ p 8) → (¬ p 9) → (p 25) → (p 24) → False)
    (d5360 : (¬ p 2) → (¬ p 18) → (p 26) → (p 10) → False)
    (d5105 : (¬ p 24) → (¬ p 26) → (p 78) → (p 80) → False)
    : (p 25) → (p 78) → (p 40) → (¬ p 8) → (¬ p 2) → (p 10) → (p 80) → (¬ p 9) → False := by
  intro a0 a1 a2 a3 a4 a5 a6 a7
  have v0 : ¬ p 18 := (fun u => d225 u a0 a2)
  have v1 : ¬ p 24 := (fun u => d5299 a3 a7 a0 u)
  have v2 : ¬ p 26 := (fun u => d5360 a4 v0 u a5)
  exact d5105 v1 v2 a1 a6

theorem c5530 (p : Nat → Prop)
    (d5453 : (¬ p 10) → (p 130) → (p 80) → (¬ p 9) → False)
    (d5529 : (p 25) → (p 78) → (p 40) → (¬ p 8) → (¬ p 2) → (p 10) → (p 80) → (¬ p 9) → False)
    (d1383 : (p 44) → (p 40) → (p 34) → False)
    (d52 : (p 34) → (p 43) → (p 57) → False)
    (d4051 : (p 42) → (¬ p 25) → (p 40) → (p 43) → (¬ p 12) → False)
    (d5467 : (¬ p 39) → (¬ p 42) → (p 24) → (¬ p 8) → (¬ p 9) → False)
    (d5329 : (¬ p 11) → (¬ p 12) → (¬ p 57) → (¬ p 53) → (¬ p 39) → (¬ p 42) → False)
    (d5319 : (¬ p 25) → (¬ p 27) → (¬ p 8) → (¬ p 9) → (¬ p 39) → (¬ p 42) → False)
    (d5105 : (¬ p 24) → (¬ p 26) → (p 78) → (p 80) → False)
    (d5355 : (¬ p 2) → (¬ p 18) → (p 27) → (p 11) → False)
    (d11 : (p 26) → (p 31) → (p 130) → False)
    (d387 : (p 18) → (p 26) → (p 41) → False)
    (d889 : (p 26) → (p 29) → (p 18) → False)
    (d5090 : (¬ p 41) → (¬ p 44) → (¬ p 31) → (¬ p 29) → (p 130) → False)
    : (p 43) → (p 78) → (p 40) → (¬ p 53) → (¬ p 8) → (¬ p 39) → (p 34) → (¬ p 12) → (¬ p 2) → (p 130) → (p 80) → (¬ p 9) → False := by
  intro a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11
  have v0 : p 10 := Classical.byContradiction (fun u => d5453 u a9 a10 a11)
  have v1 : ¬ p 25 := (fun u => d5529 u a1 a2 a4 a8 v0 a10 a11)
  have v2 : ¬ p 44 := (fun u => d1383 u a2 a6)
  have v3 : ¬ p 57 := (fun u => d52 a6 a0 u)
  have v4 : ¬ p 42 := (fun u => d4051 u v1 a2 a0 a7)
  have v5 : ¬ p 24 := (fun u => d5467 a5 v4 u a4 a11)
  have v6 : p 11 := Classical.byContradiction (fun u => d5329 u a7 v3 a3 a5 v4)
  have v7 : p 27 := Classical.byContradiction (fun u => d5319 v1 u a4 a11 a5 v4)
  have v8 : p 26 := Classical.byContradiction (fun u => d5105 v5 u a1 a10)
  have v9 : p 18 := Classical.byContradiction (fun u => d5355 a8 u v7 v6)
  have v10 : ¬ p 31 := (fun u => d11 v8 u a9)
  have v11 : ¬ p 41 := (fun u => d387 v9 v8 u)
  have v12 : ¬ p 29 := (fun u => d889 v8 u v9)
  exact d5090 v11 v2 v10 v12 a9

theorem c5531 (p : Nat → Prop)
    (d844 : (p 40) → (p 18) → (p 42) → False)
    (d5467 : (¬ p 39) → (¬ p 42) → (p 24) → (¬ p 8) → (¬ p 9) → False)
    (d5105 : (¬ p 24) → (¬ p 26) → (p 78) → (p 80) → False)
    (d387 : (p 18) → (p 26) → (p 41) → False)
    (d889 : (p 26) → (p 29) → (p 18) → False)
    (d5090 : (¬ p 41) → (¬ p 44) → (¬ p 31) → (¬ p 29) → (p 130) → False)
    : (p 18) → (¬ p 31) → (p 78) → (¬ p 44) → (p 40) → (¬ p 8) → (¬ p 39) → (p 130) → (p 80) → (¬ p 9) → False := by
  intro a0 a1 a2 a3 a4 a5 a6 a7 a8 a9
  have v0 : ¬ p 42 := (fun u => d844 a4 a0 u)
  have v1 : ¬ p 24 := (fun u => d5467 a6 v0 u a5 a9)
  have v2 : p 26 := Classical.byContradiction (fun u => d5105 v1 u a2 a8)
  have v3 : ¬ p 41 := (fun u => d387 a0 v2 u)
  have v4 : ¬ p 29 := (fun u => d889 v2 u a0)
  exact d5090 v3 a3 a1 v4 a7

theorem c5532 (p : Nat → Prop)
    (d5486 : (p 3) → (p 130) → (p 80) → (¬ p 63) → (¬ p 9) → (¬ p 49) → False)
    (d755 : (p 80) → (p 130) → (¬ p 9) → (p 5) → False)
    (d20 : (¬ p 4) → (¬ p 5) → (¬ p 63) → False)
    (d1215 : (p 4) → (p 2) → (p 7) → False)
    (d505 : (¬ p 2) → (¬ p 3) → (¬ p 34) → False)
    (d5519 : (p 79) → (p 7) → (p 130) → (p 80) → (¬ p 63) → (¬ p 9) → (¬ p 49) → False)
    (d5029 : (¬ p 123) → (¬ p 79) → (p 80) → (p 130) → False)
    (d5520 : (p 39) → (p 123) → (p 34) → (¬ p 3) → (¬ p 9) → (¬ p 49) → False)
    (d4556 : (p 12) → (p 4) → (p 7) → False)
    (d5453 : (¬ p 10) → (p 130) → (p 80) → (¬ p 9) → False)
    (d273 : (¬ p 49) → (¬ p 53) → (¬ p 66) → False)
    (d5528 : (¬ p 40) → (p 66) → (¬ p 53) → (¬ p 8) → (¬ p 39) → (¬ p 79) → (p 7) → (¬ p 3) → (p 130) → (p 80) → (¬ p 63) → (¬ p 9) → False)
    (d380 : (p 34) → (p 40) → (p 54) → False)
    (d1383 : (p 44) → (p 40) → (p 34) → False)
    (d235 : (¬ p 50) → (¬ p 54) → (¬ p 79) → False)
    (d5236 : (¬ p 78) → (¬ p 39) → (p 50) → (p 34) → False)
    (d5529 : (p 25) → (p 78) → (p 40) → (¬ p 8) → (¬ p 2) → (p 10) → (p 80) → (¬ p 9) → False)
    (d5530 : (p 43) → (p 78) → (p 40) → (¬ p 53) → (¬ p 8) → (¬ p 39) → (p 34) → (¬ p 12) → (¬ p 2) → (p 130) → (p 80) → (¬ p 9) → False)
    (d4994 : (¬ p 43) → (¬ p 141) → (p 123) → (p 40) → False)
    (d631 : (p 130) → (p 31) → (p 141) → False)
    (d5531 : (p 18) → (¬ p 31) → (p 78) → (¬ p 44) → (p 40) → (¬ p 8) → (¬ p 39) → (p 130) → (p 80) → (¬ p 9) → False)
    (d5360 : (¬ p 2) → (¬ p 18) → (p 26) → (p 10) → False)
    (d5105 : (¬ p 24) → (¬ p 26) → (p 78) → (p 80) → False)
    (d5153 : (¬ p 26) → (¬ p 28) → (p 141) → (p 130) → False)
    (d5467 : (¬ p 39) → (¬ p 42) → (p 24) → (¬ p 8) → (¬ p 9) → False)
    (d5313 : (¬ p 25) → (¬ p 27) → (p 40) → (p 42) → False)
    (d625 : (p 42) → (p 27) → (p 11) → False)
    (d5324 : (¬ p 11) → (¬ p 12) → (p 27) → (p 28) → False)
    : (¬ p 53) → (¬ p 8) → (p 7) → (p 130) → (p 80) → (¬ p 63) → (¬ p 9) → (¬ p 49) → False := by
  intro a0 a1 a2 a3 a4 a5 a6 a7
  have v0 : ¬ p 3 := (fun u => d5486 u a3 a4 a5 a6 a7)
  have v1 : ¬ p 5 := (fun u => d755 a4 a3 a6 u)
  have v2 : p 4 := Classical.byContradiction (fun u => d20 u v1 a5)
  have v3 : ¬ p 2 := (fun u => d1215 v2 u a2)
  have v4 : p 34 := Classical.byContradiction (fun u => d505 v3 v0 u)
  have v5 : ¬ p 79 := (fun u => d5519 u a2 a3 a4 a5 a6 a7)
  have v6 : p 123 := Classical.byContradiction (fun u => d5029 u v5 a4 a3)
  have v7 : ¬ p 39 := (fun u => d5520 u v6 v4 v0 a6 a7)
  have v8 : ¬ p 12 := (fun u => d4556 u v2 a2)
  have v9 : p 10 := Classical.byContradiction (fun u => d5453 u a3 a4 a6)
  have v10 : p 66 := Classical.byContradiction (fun u => d273 a7 a0 u)
  have v11 : p 40 := Classical.byContradiction (fun u => d5528 u v10 a0 a1 v7 v5 a2 v0 a3 a4 a5 a6)
  have v12 : ¬ p 54 := (fun u => d380 v4 v11 u)
  have v13 : ¬ p 44 := (fun u => d1383 u v11 v4)
  have v14 : p 50 := Classical.byContradiction (fun u => d235 u v12 v5)
  have v15 : p 78 := Classical.byContradiction (fun u => d5236 u v7 v14 v4)
  have v16 : ¬ p 25 := (fun u => d5529 u v15 v11 a1 v3 v9 a4 a6)
  have v17 : ¬ p 43 := (fun u => d5530 u v15 v11 a0 a1 v7 v4 v8 v3 a3 a4 a6)
  have v18 : p 141 := Classical.byContradiction (fun u => d4994 v17 u v6 v11)
  have v19 : ¬ p 31 := (fun u => d631 a3 u v18)
  have v20 : ¬ p 18 := (fun u => d5531 u v19 v15 v13 v11 a1 v7 a3 a4 a6)
  have v21 : ¬ p 26 := (fun u => d5360 v3 v20 u v9)
  have v22 : p 24 := Classical.byContradiction (fun u => d5105 u v21 v15 a4)
  have v23 : p 28 := Classical.byContradiction (fun u => d5153 v21 u v18 a3)
  have v24 : p 42 := Classical.byContradiction (fun u => d5467 v7 u v22 a1 a6)
  have v25 : p 27 := Classical.byContradiction (fun u => d5313 v16 u v11 v24)
  have v26 : ¬ p 11 := (fun u => d625 v24 v25 u)
  exact d5324 v26 v8 v25 v23

theorem c5533 (p : Nat → Prop)
    (d5519 : (p 79) → (p 7) → (p 130) → (p 80) → (¬ p 63) → (¬ p 9) → (¬ p 49) → False)
    (d5486 : (p 3) → (p 130) → (p 80) → (¬ p 63) → (¬ p 9) → (¬ p 49) → False)
    (d755 : (p 80) → (p 130) → (¬ p 9) → (p 5) → False)
    (d20 : (¬ p 4) → (¬ p 5) → (¬ p 63) → False)
    (d1215 : (p 4) → (p 2) → (p 7) → False)
    (d505 : (¬ p 2) → (¬ p 3) → (¬ p 34) → False)
    (d5532 : (¬ p 53) → (¬ p 8) → (p 7) → (p 130) → (p 80) → (¬ p 63) → (¬ p 9) → (¬ p 49) → False)
    (d5300 : (¬ p 8) → (¬ p 9) → (p 53) → (p 54) → False)
    (d2710 : (p 53) → (p 50) → (p 34) → False)
    (d235 : (¬ p 50) → (¬ p 54) → (¬ p 79) → False)
    : (¬ p 8) → (p 7) → (p 130) → (p 80) → (¬ p 63) → (¬ p 9) → (¬ p 49) → False := by
  intro a0 a1 a2 a3 a4 a5 a6
  have v0 : ¬ p 79 := (fun u => d5519 u a1 a2 a3 a4 a5 a6)
  have v1 : ¬ p 3 := (fun u => d5486 u a2 a3 a4 a5 a6)
  have v2 : ¬ p 5 := (fun u => d755 a3 a2 a5 u)
  have v3 : p 4 := Classical.byContradiction (fun u => d20 u v2 a4)
  have v4 : ¬ p 2 := (fun u => d1215 v3 u a1)
  have v5 : p 34 := Classical.byContradiction (fun u => d505 v4 v1 u)
  have v6 : p 53 := Classical.byContradiction (fun u => d5532 u a0 a1 a2 a3 a4 a5 a6)
  have v7 : ¬ p 54 := (fun u => d5300 a0 a5 v6 u)
  have v8 : ¬ p 50 := (fun u => d2710 v6 u v5)
  exact d235 v8 v7 v0

theorem c5534 (p : Nat → Prop)
    (d2710 : (p 53) → (p 50) → (p 34) → False)
    (d4536 : (p 78) → (p 80) → (p 21) → False)
    (d1263 : (p 24) → (p 53) → (p 78) → False)
    (d4940 : (¬ p 21) → (¬ p 50) → (p 34) → (p 18) → False)
    (d5102 : (¬ p 24) → (¬ p 26) → (p 8) → (p 10) → False)
    (d5360 : (¬ p 2) → (¬ p 18) → (p 26) → (p 10) → False)
    : (p 78) → (p 53) → (p 8) → (p 34) → (¬ p 2) → (p 10) → (p 80) → False := by
  intro a0 a1 a2 a3 a4 a5 a6
  have v0 : ¬ p 50 := (fun u => d2710 a1 u a3)
  have v1 : ¬ p 21 := (fun u => d4536 a0 a6 u)
  have v2 : ¬ p 24 := (fun u => d1263 u a1 a0)
  have v3 : ¬ p 18 := (fun u => d4940 v1 v0 a3 u)
  have v4 : p 26 := Classical.byContradiction (fun u => d5102 v2 u a2 a5)
  exact d5360 a4 v3 v4 a5

theorem c5535 (p : Nat → Prop)
    (d5486 : (p 3) → (p 130) → (p 80) → (¬ p 63) → (¬ p 9) → (¬ p 49) → False)
    (d5453 : (¬ p 10) → (p 130) → (p 80) → (¬ p 9) → False)
    (d4617 : (p 91) → (p 10) → (p 80) → False)
    (d373 : (p 10) → (p 15) → (p 130) → False)
    (d755 : (p 80) → (p 130) → (¬ p 9) → (p 5) → False)
    (d20 : (¬ p 4) → (¬ p 5) → (¬ p 63) → False)
    (d281 : (p 4) → (p 10) → (p 68) → False)
    (d1215 : (p 4) → (p 2) → (p 7) → False)
    (d418 : (p 4) → (p 7) → (p 65) → False)
    (d4556 : (p 12) → (p 4) → (p 7) → False)
    (d505 : (¬ p 2) → (¬ p 3) → (¬ p 34) → False)
    (d5519 : (p 79) → (p 7) → (p 130) → (p 80) → (¬ p 63) → (¬ p 9) → (¬ p 49) → False)
    (d5029 : (¬ p 123) → (¬ p 79) → (p 80) → (p 130) → False)
    (d5520 : (p 39) → (p 123) → (p 34) → (¬ p 3) → (¬ p 9) → (¬ p 49) → False)
    (d5533 : (¬ p 8) → (p 7) → (p 130) → (p 80) → (¬ p 63) → (¬ p 9) → (¬ p 49) → False)
    (d3743 : (¬ p 49) → (¬ p 3) → (¬ p 53) → (p 8) → False)
    (d1880 : (p 16) → (p 8) → (p 7) → False)
    (d2710 : (p 53) → (p 50) → (p 34) → False)
    (d4106 : (p 56) → (p 34) → (p 53) → False)
    (d235 : (¬ p 50) → (¬ p 54) → (¬ p 79) → False)
    (d5534 : (p 78) → (p 53) → (p 8) → (p 34) → (¬ p 2) → (p 10) → (p 80) → False)
    (d5235 : (¬ p 78) → (¬ p 39) → (p 80) → (p 41) → False)
    (d5493 : (¬ p 39) → (p 37) → (¬ p 78) → (p 34) → (¬ p 2) → (¬ p 68) → (¬ p 5) → (¬ p 63) → False)
    (d859 : (p 34) → (p 53) → (p 18) → (¬ p 78) → False)
    (d5278 : (¬ p 41) → (¬ p 38) → (p 7) → (p 10) → False)
    (d873 : (p 54) → (p 51) → (p 34) → (¬ p 37) → False)
    (d1134 : (p 34) → (p 38) → (p 42) → False)
    (d884 : (¬ p 102) → (p 34) → (p 53) → (p 38) → False)
    (d444 : (¬ p 51) → (¬ p 55) → (¬ p 91) → False)
    (d4969 : (¬ p 39) → (¬ p 42) → (p 8) → (p 11) → False)
    (d5507 : (¬ p 18) → (p 74) → (¬ p 39) → (p 8) → (¬ p 42) → (¬ p 2) → (p 10) → (p 4) → False)
    (d4961 : (¬ p 136) → (¬ p 56) → (p 55) → (p 130) → False)
    (d5328 : (¬ p 11) → (¬ p 12) → (¬ p 70) → (¬ p 65) → (p 102) → False)
    (d5382 : (¬ p 74) → (¬ p 69) → (¬ p 16) → (¬ p 15) → (p 136) → False)
    (d4611 : (p 70) → (p 4) → (p 69) → False)
    : (p 7) → (p 130) → (p 80) → (¬ p 63) → (¬ p 9) → (¬ p 49) → False := by
  intro a0 a1 a2 a3 a4 a5
  have v0 : ¬ p 3 := (fun u => d5486 u a1 a2 a3 a4 a5)
  have v1 : p 10 := Classical.byContradiction (fun u => d5453 u a1 a2 a4)
  have v2 : ¬ p 91 := (fun u => d4617 u v1 a2)
  have v3 : ¬ p 15 := (fun u => d373 v1 u a1)
  have v4 : ¬ p 5 := (fun u => d755 a2 a1 a4 u)
  have v5 : p 4 := Classical.byContradiction (fun u => d20 u v4 a3)
  have v6 : ¬ p 68 := (fun u => d281 v5 v1 u)
  have v7 : ¬ p 2 := (fun u => d1215 v5 u a0)
  have v8 : ¬ p 65 := (fun u => d418 v5 a0 u)
  have v9 : ¬ p 12 := (fun u => d4556 u v5 a0)
  have v10 : p 34 := Classical.byContradiction (fun u => d505 v7 v0 u)
  have v11 : ¬ p 79 := (fun u => d5519 u a0 a1 a2 a3 a4 a5)
  have v12 : p 123 := Classical.byContradiction (fun u => d5029 u v11 a2 a1)
  have v13 : ¬ p 39 := (fun u => d5520 u v12 v10 v0 a4 a5)
  have v14 : p 8 := Classical.byContradiction (fun u => d5533 u a0 a1 a2 a3 a4 a5)
  have v15 : p 53 := Classical.byContradiction (fun u => d3743 a5 v0 u v14)
  have v16 : ¬ p 16 := (fun u => d1880 u v14 a0)
  have v17 : ¬ p 50 := (fun u => d2710 v15 u v10)
  have v18 : ¬ p 56 := (fun u => d4106 u v10 v15)
  have v19 : p 54 := Classical.byContradiction (fun u => d235 v17 u v11)
  have v20 : ¬ p 78 := (fun u => d5534 u v15 v14 v10 v7 v1 a2)
  have v21 : ¬ p 41 := (fun u => d5235 v20 v13 a2 u)
  have v22 : ¬ p 37 := (fun u => d5493 v13 u v20 v10 v7 v6 v4 a3)
  have v23 : ¬ p 18 := (fun u => d859 v10 v15 u v20)
  have v24 : p 38 := Classical.byContradiction (fun u => d5278 v21 u a0 v1)
  have v25 : ¬ p 51 := (fun u => d873 v19 u v10 v22)
  have v26 : ¬ p 42 := (fun u => d1134 v10 v24 u)
  have v27 : p 102 := Classical.byContradiction (fun u => d884 u v10 v15 v24)
  have v28 : p 55 := Classical.byContradiction (fun u => d444 v25 u v2)
  have v29 : ¬ p 11 := (fun u => d4969 v13 v26 v14 u)
  have v30 : ¬ p 74 := (fun u => d5507 v23 u v13 v14 v26 v7 v1 v5)
  have v31 : p 136 := Classical.byContradiction (fun u => d4961 u v18 v28 a1)
  have v32 : p 70 := Classical.byContradiction (fun u => d5328 v29 v9 u v8 v27)
  have v33 : p 69 := Classical.byContradiction (fun u => d5382 v30 u v16 v3 v31)
  exact d4611 v32 v5 v33

theorem c5536 (p : Nat → Prop)
    (d5183 : (¬ p 13) → (¬ p 12) → (p 70) → (p 71) → False)
    (d338 : (p 4) → (p 13) → (p 71) → False)
    : (p 71) → (p 70) → (¬ p 12) → (p 4) → False := by
  intro a0 a1 a2 a3
  have v0 : p 13 := Classical.byContradiction (fun u => d5183 u a2 a1 a0)
  exact d338 a3 v0 a0

theorem c5537 (p : Nat → Prop)
    (d4970 : (¬ p 39) → (¬ p 42) → (p 27) → (p 24) → False)
    (d5057 : (¬ p 71) → (¬ p 66) → (p 24) → (p 29) → False)
    (d5180 : (¬ p 27) → (¬ p 29) → (¬ p 71) → (¬ p 66) → (¬ p 39) → (¬ p 42) → False)
    : (¬ p 71) → (¬ p 42) → (p 24) → (¬ p 39) → (¬ p 66) → False := by
  intro a0 a1 a2 a3 a4
  have v0 : ¬ p 27 := (fun u => d4970 a3 a1 u a2)
  have v1 : ¬ p 29 := (fun u => d5057 a0 a4 a2 u)
  exact d5180 v0 v1 a0 a4 a3 a1

theorem c5538 (p : Nat → Prop)
    (d884 : (¬ p 102) → (p 34) → (p 53) → (p 38) → False)
    (d414 : (p 35) → (p 38) → (p 65) → False)
    (d5328 : (¬ p 11) → (¬ p 12) → (¬ p 70) → (¬ p 65) → (p 102) → False)
    : (p 38) → (¬ p 70) → (¬ p 12) → (¬ p 11) → (p 35) → (p 34) → (p 53) → False := by
  intro a0 a1 a2 a3 a4 a5 a6
  have v0 : p 102 := Classical.byContradiction (fun u => d884 u a5 a6 a0)
  have v1 : ¬ p 65 := (fun u => d414 a4 a0 u)
  exact d5328 a3 a2 a1 v1 v0

theorem c5539 (p : Nat → Prop)
    (d338 : (p 4) → (p 13) → (p 71) → False)
    (d1530 : (¬ p 18) → (¬ p 35) → (¬ p 2) → (p 4) → False)
    (d5353 : (¬ p 2) → (¬ p 18) → (p 4) → (p 20) → False)
    (d4106 : (p 56) → (p 34) → (p 53) → False)
    (d5536 : (p 71) → (p 70) → (¬ p 12) → (p 4) → False)
    (d5330 : (¬ p 11) → (¬ p 12) → (¬ p 13) → (¬ p 27) → (¬ p 29) → False)
    (d5538 : (p 38) → (¬ p 70) → (¬ p 12) → (¬ p 11) → (p 35) → (p 34) → (p 53) → False)
    (d5283 : (¬ p 41) → (¬ p 38) → (¬ p 102) → (¬ p 56) → (p 55) → False)
    (d5328 : (¬ p 11) → (¬ p 12) → (¬ p 70) → (¬ p 65) → (p 102) → False)
    (d647 : (p 65) → (p 64) → (p 4) → False)
    (d488 : (p 65) → (p 71) → (p 104) → False)
    (d270 : (¬ p 20) → (¬ p 22) → (¬ p 64) → False)
    (d4914 : (¬ p 104) → (¬ p 77) → (p 21) → (p 29) → False)
    (d5359 : (¬ p 2) → (¬ p 18) → (p 6) → (p 22) → False)
    (d4209 : (¬ p 6) → (p 77) → (¬ p 7) → (¬ p 5) → False)
    : (¬ p 12) → (p 71) → (¬ p 27) → (¬ p 11) → (p 55) → (p 21) → (¬ p 2) → (¬ p 18) → (¬ p 41) → (p 34) → (p 53) → (¬ p 7) → (p 4) → (¬ p 5) → False := by
  intro a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13
  have v0 : ¬ p 13 := (fun u => d338 a12 u a1)
  have v1 : p 35 := Classical.byContradiction (fun u => d1530 a7 u a6 a12)
  have v2 : ¬ p 20 := (fun u => d5353 a6 a7 a12 u)
  have v3 : ¬ p 56 := (fun u => d4106 u a9 a10)
  have v4 : ¬ p 70 := (fun u => d5536 a1 u a0 a12)
  have v5 : p 29 := Classical.byContradiction (fun u => d5330 a3 a0 v0 a2 u)
  have v6 : ¬ p 38 := (fun u => d5538 u v4 a0 a3 v1 a9 a10)
  have v7 : p 102 := Classical.byContradiction (fun u => d5283 a8 v6 u v3 a4)
  have v8 : p 65 := Classical.byContradiction (fun u => d5328 a3 a0 v4 u v7)
  have v9 : ¬ p 64 := (fun u => d647 v8 u a12)
  have v10 : ¬ p 104 := (fun u => d488 v8 a1 u)
  have v11 : p 22 := Classical.byContradiction (fun u => d270 v2 u v9)
  have v12 : p 77 := Classical.byContradiction (fun u => d4914 v10 u a5 v5)
  have v13 : ¬ p 6 := (fun u => d5359 a6 a7 u v11)
  exact d4209 v13 v12 a11 a13

theorem c5540 (p : Nat → Prop)
    (d5360 : (¬ p 2) → (¬ p 18) → (p 26) → (p 10) → False)
    (d5155 : (¬ p 26) → (¬ p 28) → (p 12) → (p 10) → False)
    (d5357 : (¬ p 2) → (¬ p 18) → (p 12) → (p 28) → False)
    : (p 12) → (¬ p 2) → (¬ p 18) → (p 10) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 26 := (fun u => d5360 a1 a2 u a3)
  have v1 : p 28 := Classical.byContradiction (fun u => d5155 v0 u a0 a3)
  exact d5357 a1 a2 a0 v1

theorem c5541 (p : Nat → Prop)
    (d5324 : (¬ p 11) → (¬ p 12) → (p 27) → (p 28) → False)
    (d5539 : (¬ p 12) → (p 71) → (¬ p 27) → (¬ p 11) → (p 55) → (p 21) → (¬ p 2) → (¬ p 18) → (¬ p 41) → (p 34) → (p 53) → (¬ p 7) → (p 4) → (¬ p 5) → False)
    : (¬ p 11) → (p 28) → (p 71) → (p 55) → (¬ p 12) → (p 21) → (¬ p 2) → (¬ p 18) → (¬ p 41) → (p 34) → (p 53) → (¬ p 7) → (p 4) → (¬ p 5) → False := by
  intro a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13
  have v0 : ¬ p 27 := (fun u => d5324 a0 a4 u a1)
  exact d5539 a4 a2 v0 a0 a3 a5 a6 a7 a8 a9 a10 a11 a12 a13

theorem c5542 (p : Nat → Prop)
    (d859 : (p 34) → (p 53) → (p 18) → (¬ p 78) → False)
    (d1530 : (¬ p 18) → (¬ p 35) → (¬ p 2) → (p 4) → False)
    (d5353 : (¬ p 2) → (¬ p 18) → (p 4) → (p 20) → False)
    (d4601 : (p 39) → (p 53) → (p 8) → False)
    (d5235 : (¬ p 78) → (¬ p 39) → (p 80) → (p 41) → False)
    (d338 : (p 4) → (p 13) → (p 71) → False)
    (d483 : (p 35) → (p 44) → (p 71) → False)
    (d3982 : (p 74) → (p 71) → (p 35) → False)
    (d5536 : (p 71) → (p 70) → (¬ p 12) → (p 4) → False)
    (d5190 : (¬ p 13) → (¬ p 12) → (¬ p 26) → (¬ p 28) → (¬ p 41) → (¬ p 44) → False)
    (d5541 : (¬ p 11) → (p 28) → (p 71) → (p 55) → (¬ p 12) → (p 21) → (¬ p 2) → (¬ p 18) → (¬ p 41) → (p 34) → (p 53) → (¬ p 7) → (p 4) → (¬ p 5) → False)
    (d22 : (p 4) → (p 11) → (p 69) → False)
    (d4969 : (¬ p 39) → (¬ p 42) → (p 8) → (p 11) → False)
    (d625 : (p 42) → (p 27) → (p 11) → False)
    (d4613 : (p 47) → (p 35) → (p 42) → False)
    (d4236 : (¬ p 44) → (¬ p 70) → (¬ p 9) → (p 4) → (¬ p 47) → (¬ p 20) → (¬ p 18) → (p 42) → (p 29) → (¬ p 41) → (p 80) → (¬ p 68) → False)
    (d5387 : (¬ p 74) → (¬ p 69) → (¬ p 44) → (¬ p 47) → (¬ p 27) → (¬ p 29) → False)
    : (p 71) → (p 55) → (¬ p 12) → (p 21) → (¬ p 26) → (¬ p 2) → (¬ p 78) → (p 34) → (p 53) → (p 8) → (¬ p 7) → (¬ p 68) → (p 4) → (¬ p 5) → (p 80) → (¬ p 9) → False := by
  intro a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15
  have v0 : ¬ p 18 := (fun u => d859 a7 a8 u a6)
  have v1 : p 35 := Classical.byContradiction (fun u => d1530 v0 u a5 a12)
  have v2 : ¬ p 20 := (fun u => d5353 a5 v0 a12 u)
  have v3 : ¬ p 39 := (fun u => d4601 u a8 a9)
  have v4 : ¬ p 41 := (fun u => d5235 a6 v3 a14 u)
  have v5 : ¬ p 13 := (fun u => d338 a12 u a0)
  have v6 : ¬ p 44 := (fun u => d483 v1 u a0)
  have v7 : ¬ p 74 := (fun u => d3982 u a0 v1)
  have v8 : ¬ p 70 := (fun u => d5536 a0 u a2 a12)
  have v9 : p 28 := Classical.byContradiction (fun u => d5190 v5 a2 a4 u v4 v6)
  have v10 : p 11 := Classical.byContradiction (fun u => d5541 u v9 a0 a1 a2 a3 a5 v0 v4 a7 a8 a10 a12 a13)
  have v11 : ¬ p 69 := (fun u => d22 a12 v10 u)
  have v12 : p 42 := Classical.byContradiction (fun u => d4969 v3 u a9 v10)
  have v13 : ¬ p 27 := (fun u => d625 v12 u v10)
  have v14 : ¬ p 47 := (fun u => d4613 u v1 v12)
  have v15 : ¬ p 29 := (fun u => d4236 v6 v8 a15 a12 v14 v2 v0 v12 u v4 a14 a11)
  exact d5387 v7 v11 v6 v14 v13 v15

theorem c5543 (p : Nat → Prop)
    (d5453 : (¬ p 10) → (p 130) → (p 80) → (¬ p 9) → False)
    (d859 : (p 34) → (p 53) → (p 18) → (¬ p 78) → False)
    (d5540 : (p 12) → (¬ p 2) → (¬ p 18) → (p 10) → False)
    (d5360 : (¬ p 2) → (¬ p 18) → (p 26) → (p 10) → False)
    (d5102 : (¬ p 24) → (¬ p 26) → (p 8) → (p 10) → False)
    (d4631 : (p 53) → (p 24) → (¬ p 21) → (p 34) → False)
    (d1530 : (¬ p 18) → (¬ p 35) → (¬ p 2) → (p 4) → False)
    (d4601 : (p 39) → (p 53) → (p 8) → False)
    (d5235 : (¬ p 78) → (¬ p 39) → (p 80) → (p 41) → False)
    (d4106 : (p 56) → (p 34) → (p 53) → False)
    (d2710 : (p 53) → (p 50) → (p 34) → False)
    (d13 : (p 4) → (p 8) → (p 66) → False)
    (d4617 : (p 91) → (p 10) → (p 80) → False)
    (d281 : (p 4) → (p 10) → (p 68) → False)
    (d755 : (p 80) → (p 130) → (¬ p 9) → (p 5) → False)
    (d5029 : (¬ p 123) → (¬ p 79) → (p 80) → (p 130) → False)
    (d235 : (¬ p 50) → (¬ p 54) → (¬ p 79) → False)
    (d380 : (p 34) → (p 40) → (p 54) → False)
    (d873 : (p 54) → (p 51) → (p 34) → (¬ p 37) → False)
    (d1808 : (¬ p 37) → (¬ p 90) → (¬ p 51) → (p 54) → False)
    (d444 : (¬ p 51) → (¬ p 55) → (¬ p 91) → False)
    (d4961 : (¬ p 136) → (¬ p 56) → (p 55) → (p 130) → False)
    (d5542 : (p 71) → (p 55) → (¬ p 12) → (p 21) → (¬ p 26) → (¬ p 2) → (¬ p 78) → (p 34) → (p 53) → (p 8) → (¬ p 7) → (¬ p 68) → (p 4) → (¬ p 5) → (p 80) → (¬ p 9) → False)
    (d5057 : (¬ p 71) → (¬ p 66) → (p 24) → (p 29) → False)
    (d5537 : (¬ p 71) → (¬ p 42) → (p 24) → (¬ p 39) → (¬ p 66) → False)
    (d101 : (p 35) → (p 42) → (p 69) → False)
    (d5443 : (p 123) → (¬ p 43) → (¬ p 51) → (p 130) → (¬ p 56) → (¬ p 9) → (p 80) → (¬ p 40) → (p 42) → False)
    (d81 : (p 35) → (p 43) → (p 70) → False)
    (d5322 : (¬ p 11) → (¬ p 12) → (p 43) → (p 42) → False)
    (d625 : (p 42) → (p 27) → (p 11) → False)
    (d5171 : (¬ p 27) → (¬ p 29) → (p 13) → (p 11) → False)
    (d1049 : (¬ p 29) → (¬ p 27) → (p 136) → (¬ p 31) → False)
    (d5184 : (¬ p 13) → (¬ p 12) → (p 44) → (p 43) → False)
    (d114 : (p 25) → (p 31) → (p 123) → False)
    (d5190 : (¬ p 13) → (¬ p 12) → (¬ p 26) → (¬ p 28) → (¬ p 41) → (¬ p 44) → False)
    (d5314 : (¬ p 25) → (¬ p 27) → (¬ p 64) → (¬ p 69) → (p 90) → False)
    (d32 : (p 4) → (p 6) → (p 64) → False)
    (d647 : (p 65) → (p 64) → (p 4) → False)
    (d207 : (¬ p 6) → (¬ p 7) → (¬ p 88) → False)
    (d5288 : (¬ p 70) → (¬ p 65) → (p 28) → (p 23) → False)
    (d175 : (p 88) → (p 90) → (p 100) → False)
    (d442 : (¬ p 23) → (¬ p 25) → (¬ p 100) → False)
    : (¬ p 79) → (¬ p 37) → (¬ p 2) → (¬ p 78) → (p 34) → (p 53) → (p 8) → (¬ p 7) → (p 4) → (p 130) → (p 80) → (¬ p 9) → False := by
  intro a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11
  have v0 : p 10 := Classical.byContradiction (fun u => d5453 u a9 a10 a11)
  have v1 : ¬ p 18 := (fun u => d859 a4 a5 u a3)
  have v2 : ¬ p 12 := (fun u => d5540 u a2 v1 v0)
  have v3 : ¬ p 26 := (fun u => d5360 a2 v1 u v0)
  have v4 : p 24 := Classical.byContradiction (fun u => d5102 u v3 a6 v0)
  have v5 : p 21 := Classical.byContradiction (fun u => d4631 a5 v4 u a4)
  have v6 : p 35 := Classical.byContradiction (fun u => d1530 v1 u a2 a8)
  have v7 : ¬ p 39 := (fun u => d4601 u a5 a6)
  have v8 : ¬ p 41 := (fun u => d5235 a3 v7 a10 u)
  have v9 : ¬ p 56 := (fun u => d4106 u a4 a5)
  have v10 : ¬ p 50 := (fun u => d2710 a5 u a4)
  have v11 : ¬ p 66 := (fun u => d13 a8 a6 u)
  have v12 : ¬ p 91 := (fun u => d4617 u v0 a10)
  have v13 : ¬ p 68 := (fun u => d281 a8 v0 u)
  have v14 : ¬ p 5 := (fun u => d755 a10 a9 a11 u)
  have v15 : p 123 := Classical.byContradiction (fun u => d5029 u a0 a10 a9)
  have v16 : p 54 := Classical.byContradiction (fun u => d235 v10 u a0)
  have v17 : ¬ p 40 := (fun u => d380 a4 u v16)
  have v18 : ¬ p 51 := (fun u => d873 v16 u a4 a1)
  have v19 : p 90 := Classical.byContradiction (fun u => d1808 a1 u v18 v16)
  have v20 : p 55 := Classical.byContradiction (fun u => d444 v18 u v12)
  have v21 : p 136 := Classical.byContradiction (fun u => d4961 u v9 v20 a9)
  have v22 : ¬ p 71 := (fun u => d5542 u v20 v2 v5 v3 a2 a3 a4 a5 a6 a7 v13 a8 v14 a10 a11)
  have v23 : ¬ p 29 := (fun u => d5057 v22 v11 v4 u)
  have v24 : p 42 := Classical.byContradiction (fun u => d5537 v22 u v4 v7 v11)
  have v25 : ¬ p 69 := (fun u => d101 v6 v24 u)
  have v26 : p 43 := Classical.byContradiction (fun u => d5443 v15 u v18 a9 v9 a11 a10 v17 v24)
  have v27 : ¬ p 70 := (fun u => d81 v6 v26 u)
  have v28 : p 11 := Classical.byContradiction (fun u => d5322 u v2 v26 v24)
  have v29 : ¬ p 27 := (fun u => d625 v24 u v28)
  have v30 : ¬ p 13 := (fun u => d5171 v29 v23 u v28)
  have v31 : p 31 := Classical.byContradiction (fun u => d1049 v23 v29 v21 u)
  have v32 : ¬ p 44 := (fun u => d5184 v30 v2 u v26)
  have v33 : ¬ p 25 := (fun u => d114 u v31 v15)
  have v34 : p 28 := Classical.byContradiction (fun u => d5190 v30 v2 v3 u v8 v32)
  have v35 : p 64 := Classical.byContradiction (fun u => d5314 v33 v29 u v25 v19)
  have v36 : ¬ p 6 := (fun u => d32 a8 u v35)
  have v37 : ¬ p 65 := (fun u => d647 u v35 a8)
  have v38 : p 88 := Classical.byContradiction (fun u => d207 v36 a7 u)
  have v39 : ¬ p 23 := (fun u => d5288 v27 v37 v34 u)
  have v40 : ¬ p 100 := (fun u => d175 v38 v19 u)
  exact d442 v39 v33 v40

theorem c5544 (p : Nat → Prop)
    (d1134 : (p 34) → (p 38) → (p 42) → False)
    (d5313 : (¬ p 25) → (¬ p 27) → (p 40) → (p 42) → False)
    (d5318 : (¬ p 25) → (¬ p 27) → (¬ p 29) → (¬ p 54) → (¬ p 58) → False)
    (d10 : (¬ p 37) → (¬ p 40) → (¬ p 90) → False)
    (d873 : (p 54) → (p 51) → (p 34) → (¬ p 37) → False)
    (d5314 : (¬ p 25) → (¬ p 27) → (¬ p 64) → (¬ p 69) → (p 90) → False)
    (d444 : (¬ p 51) → (¬ p 55) → (¬ p 91) → False)
    (d32 : (p 4) → (p 6) → (p 64) → False)
    (d5283 : (¬ p 41) → (¬ p 38) → (¬ p 102) → (¬ p 56) → (p 55) → False)
    (d213 : (¬ p 5) → (¬ p 6) → (¬ p 76) → False)
    (d207 : (¬ p 6) → (¬ p 7) → (¬ p 88) → False)
    (d4131 : (p 87) → (p 76) → (p 80) → False)
    (d175 : (p 88) → (p 90) → (p 100) → False)
    (d5398 : (¬ p 138) → (¬ p 87) → (¬ p 25) → (¬ p 27) → (p 79) → False)
    (d5317 : (¬ p 25) → (¬ p 27) → (¬ p 100) → (¬ p 108) → (p 138) → False)
    (d372 : (p 102) → (p 108) → (p 138) → False)
    : (¬ p 27) → (¬ p 69) → (p 42) → (¬ p 29) → (¬ p 58) → (¬ p 25) → (p 79) → (¬ p 37) → (¬ p 41) → (¬ p 56) → (p 34) → (¬ p 7) → (¬ p 91) → (p 4) → (¬ p 5) → (p 80) → False := by
  intro a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15
  have v0 : ¬ p 38 := (fun u => d1134 a10 u a2)
  have v1 : ¬ p 40 := (fun u => d5313 a5 a0 u a2)
  have v2 : p 54 := Classical.byContradiction (fun u => d5318 a5 a0 a3 u a4)
  have v3 : p 90 := Classical.byContradiction (fun u => d10 a7 v1 u)
  have v4 : ¬ p 51 := (fun u => d873 v2 u a10 a7)
  have v5 : p 64 := Classical.byContradiction (fun u => d5314 a5 a0 u a1 v3)
  have v6 : p 55 := Classical.byContradiction (fun u => d444 v4 u a12)
  have v7 : ¬ p 6 := (fun u => d32 a13 u v5)
  have v8 : p 102 := Classical.byContradiction (fun u => d5283 a8 v0 u a9 v6)
  have v9 : p 76 := Classical.byContradiction (fun u => d213 a14 v7 u)
  have v10 : p 88 := Classical.byContradiction (fun u => d207 v7 a11 u)
  have v11 : ¬ p 87 := (fun u => d4131 u v9 a15)
  have v12 : ¬ p 100 := (fun u => d175 v10 v3 u)
  have v13 : p 138 := Classical.byContradiction (fun u => d5398 u v11 a5 a0 a6)
  have v14 : p 108 := Classical.byContradiction (fun u => d5317 a5 a0 v12 u v13)
  exact d372 v8 v14 v13

theorem c5545 (p : Nat → Prop)
    (d4961 : (¬ p 136) → (¬ p 56) → (p 55) → (p 130) → False)
    (d444 : (¬ p 51) → (¬ p 55) → (¬ p 91) → False)
    (d356 : (p 51) → (p 53) → (p 89) → False)
    (d4967 : (¬ p 136) → (¬ p 56) → (p 51) → (p 96) → False)
    (d4984 : (¬ p 96) → (¬ p 89) → (¬ p 136) → (¬ p 56) → (p 53) → False)
    : (¬ p 136) → (¬ p 56) → (p 53) → (¬ p 91) → (p 130) → False := by
  intro a0 a1 a2 a3 a4
  have v0 : ¬ p 55 := (fun u => d4961 a0 a1 u a4)
  have v1 : p 51 := Classical.byContradiction (fun u => d444 u v0 a3)
  have v2 : ¬ p 89 := (fun u => d356 v1 a2 u)
  have v3 : ¬ p 96 := (fun u => d4967 a0 a1 v1 u)
  exact d4984 v3 v2 a0 a1 a2

theorem c5546 (p : Nat → Prop)
    (d4613 : (p 47) → (p 35) → (p 42) → False)
    (d5057 : (¬ p 71) → (¬ p 66) → (p 24) → (p 29) → False)
    (d483 : (p 35) → (p 44) → (p 71) → False)
    (d5536 : (p 71) → (p 70) → (¬ p 12) → (p 4) → False)
    (d4236 : (¬ p 44) → (¬ p 70) → (¬ p 9) → (p 4) → (¬ p 47) → (¬ p 20) → (¬ p 18) → (p 42) → (p 29) → (¬ p 41) → (p 80) → (¬ p 68) → False)
    : (p 29) → (p 42) → (¬ p 12) → (p 24) → (p 35) → (¬ p 20) → (¬ p 18) → (¬ p 41) → (¬ p 66) → (¬ p 68) → (p 4) → (p 80) → (¬ p 9) → False := by
  intro a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12
  have v0 : ¬ p 47 := (fun u => d4613 u a4 a1)
  have v1 : p 71 := Classical.byContradiction (fun u => d5057 u a8 a3 a0)
  have v2 : ¬ p 44 := (fun u => d483 a4 u v1)
  have v3 : ¬ p 70 := (fun u => d5536 v1 u a2 a10)
  exact d4236 v2 v3 a12 a10 v0 a5 a6 a1 a0 a7 a11 a9

theorem c5547 (p : Nat → Prop)
    (d101 : (p 35) → (p 42) → (p 69) → False)
    (d4613 : (p 47) → (p 35) → (p 42) → False)
    (d338 : (p 4) → (p 13) → (p 71) → False)
    (d483 : (p 35) → (p 44) → (p 71) → False)
    (d3982 : (p 74) → (p 71) → (p 35) → False)
    (d5190 : (¬ p 13) → (¬ p 12) → (¬ p 26) → (¬ p 28) → (¬ p 41) → (¬ p 44) → False)
    (d5387 : (¬ p 74) → (¬ p 69) → (¬ p 44) → (¬ p 47) → (¬ p 27) → (¬ p 29) → False)
    (d1722 : (¬ p 11) → (p 28) → (¬ p 29) → (¬ p 12) → (¬ p 13) → False)
    (d625 : (p 42) → (p 27) → (p 11) → False)
    : (p 71) → (¬ p 29) → (p 42) → (¬ p 12) → (¬ p 26) → (p 35) → (¬ p 41) → (p 4) → False := by
  intro a0 a1 a2 a3 a4 a5 a6 a7
  have v0 : ¬ p 69 := (fun u => d101 a5 a2 u)
  have v1 : ¬ p 47 := (fun u => d4613 u a5 a2)
  have v2 : ¬ p 13 := (fun u => d338 a7 u a0)
  have v3 : ¬ p 44 := (fun u => d483 a5 u a0)
  have v4 : ¬ p 74 := (fun u => d3982 u a0 a5)
  have v5 : p 28 := Classical.byContradiction (fun u => d5190 v2 a3 a4 u a6 v3)
  have v6 : p 27 := Classical.byContradiction (fun u => d5387 v4 v0 v3 v1 u a1)
  have v7 : p 11 := Classical.byContradiction (fun u => d1722 u v5 a1 a3 v2)
  exact d625 a2 v6 v7

theorem c5548 (p : Nat → Prop)
    (d101 : (p 35) → (p 42) → (p 69) → False)
    (d5546 : (p 29) → (p 42) → (¬ p 12) → (p 24) → (p 35) → (¬ p 20) → (¬ p 18) → (¬ p 41) → (¬ p 66) → (¬ p 68) → (p 4) → (p 80) → (¬ p 9) → False)
    (d5547 : (p 71) → (¬ p 29) → (p 42) → (¬ p 12) → (¬ p 26) → (p 35) → (¬ p 41) → (p 4) → False)
    (d3761 : (¬ p 66) → (¬ p 71) → (p 58) → (¬ p 49) → False)
    (d1519 : (¬ p 54) → (p 21) → (¬ p 58) → (¬ p 50) → (¬ p 23) → False)
    (d5318 : (¬ p 25) → (¬ p 27) → (¬ p 29) → (¬ p 54) → (¬ p 58) → False)
    (d557 : (p 23) → (p 27) → (p 102) → False)
    (d626 : (¬ p 64) → (¬ p 20) → (¬ p 69) → (p 27) → False)
    (d4946 : (¬ p 102) → (¬ p 56) → (p 51) → (p 88) → False)
    (d32 : (p 4) → (p 6) → (p 64) → False)
    (d207 : (¬ p 6) → (¬ p 7) → (¬ p 88) → False)
    : (p 42) → (¬ p 54) → (p 51) → (¬ p 25) → (¬ p 12) → (p 21) → (p 24) → (¬ p 26) → (p 35) → (¬ p 20) → (¬ p 18) → (¬ p 41) → (¬ p 56) → (¬ p 50) → (¬ p 66) → (¬ p 7) → (¬ p 68) → (p 4) → (p 80) → (¬ p 9) → (¬ p 49) → False := by
  intro a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20
  have v0 : ¬ p 69 := (fun u => d101 a8 a0 u)
  have v1 : ¬ p 29 := (fun u => d5546 u a0 a4 a6 a8 a9 a10 a11 a14 a16 a17 a18 a19)
  have v2 : ¬ p 71 := (fun u => d5547 u v1 a0 a4 a7 a8 a11 a17)
  have v3 : ¬ p 58 := (fun u => d3761 a14 v2 u a20)
  have v4 : p 23 := Classical.byContradiction (fun u => d1519 a1 a5 v3 a13 u)
  have v5 : p 27 := Classical.byContradiction (fun u => d5318 a3 u v1 a1 v3)
  have v6 : ¬ p 102 := (fun u => d557 v4 v5 u)
  have v7 : p 64 := Classical.byContradiction (fun u => d626 u a9 v0 v5)
  have v8 : ¬ p 88 := (fun u => d4946 v6 a12 a2 u)
  have v9 : ¬ p 6 := (fun u => d32 a17 u v7)
  exact d207 v9 a15 v8

end JSP000746.RUP
