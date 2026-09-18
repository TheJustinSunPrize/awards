import Init.Classical

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace JSP000746.RUP

theorem c4187 (p : Nat → Prop)
    (d504 : (p 140) → (p 143) → (p 150) → False)
    (d427 : (¬ p 28) → (¬ p 30) → (¬ p 140) → False)
    (d3601 : (p 30) → (¬ p 67) → (p 20) → (¬ p 27) → (p 40) → False)
    (d638 : (p 25) → (p 20) → (p 30) → False)
    (d173 : (¬ p 40) → (¬ p 43) → (¬ p 120) → False)
    (d1355 : (¬ p 100) → (¬ p 125) → (p 143) → (¬ p 70) → (¬ p 25) → (p 20) → False)
    (d171 : (p 120) → (p 125) → (p 143) → False)
    : (p 143) → (¬ p 70) → (¬ p 28) → (¬ p 100) → (p 150) → (¬ p 67) → (¬ p 43) → (p 20) → (¬ p 27) → False := by
  intro a0 a1 a2 a3 a4 a5 a6 a7 a8
  have v0 : ¬ p 140 := (fun u => d504 u a0 a4)
  have v1 : p 30 := Classical.byContradiction (fun u => d427 a2 u v0)
  have v2 : ¬ p 40 := (fun u => d3601 v1 a5 a7 a8 u)
  have v3 : ¬ p 25 := (fun u => d638 u a7 v1)
  have v4 : p 120 := Classical.byContradiction (fun u => d173 v2 a6 u)
  have v5 : p 125 := Classical.byContradiction (fun u => d1355 a3 u a0 a1 v3 a7)
  exact d171 v4 v5 a0

theorem c4190 (p : Nat → Prop)
    (d119 : (p 4) → (p 12) → (p 70) → False)
    (d306 : (p 69) → (p 70) → (p 133) → False)
    (d166 : (¬ p 11) → (¬ p 12) → (¬ p 133) → False)
    : (p 70) → (p 4) → (¬ p 11) → (p 69) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 12 := (fun u => d119 a1 u a0)
  have v1 : ¬ p 133 := (fun u => d306 a3 a0 u)
  exact d166 a2 v0 v1

theorem c4193 (p : Nat → Prop)
    (d59 : (p 4) → (p 14) → (p 72) → False)
    (d2263 : (p 72) → (p 4) → (p 73) → False)
    (d27 : (¬ p 14) → (¬ p 15) → (¬ p 148) → False)
    (d138 : (¬ p 68) → (¬ p 73) → (¬ p 130) → False)
    (d229 : (p 148) → (p 150) → (p 152) → False)
    (d11 : (p 26) → (p 31) → (p 130) → False)
    (d107 : (¬ p 31) → (¬ p 33) → (¬ p 152) → False)
    : (p 72) → (¬ p 33) → (p 26) → (¬ p 15) → (p 150) → (p 4) → (¬ p 68) → False := by
  intro a0 a1 a2 a3 a4 a5 a6
  have v0 : ¬ p 14 := (fun u => d59 a5 u a0)
  have v1 : ¬ p 73 := (fun u => d2263 a0 a5 u)
  have v2 : p 148 := Classical.byContradiction (fun u => d27 v0 a3 u)
  have v3 : p 130 := Classical.byContradiction (fun u => d138 a6 v1 u)
  have v4 : ¬ p 152 := (fun u => d229 v2 a4 u)
  have v5 : ¬ p 31 := (fun u => d11 a2 u v3)
  exact d107 v5 a1 v4

theorem c4194 (p : Nat → Prop)
    (d726 : (p 130) → (p 118) → (p 80) → False)
    (d11 : (p 26) → (p 31) → (p 130) → False)
    (d564 : (¬ p 9) → (¬ p 10) → (¬ p 118) → False)
    (d107 : (¬ p 31) → (¬ p 33) → (¬ p 152) → False)
    (d534 : (p 6) → (p 10) → (p 91) → False)
    (d1247 : (¬ p 16) → (p 152) → (¬ p 17) → (¬ p 15) → False)
    (d474 : (p 130) → (p 132) → (p 152) → False)
    (d136 : (¬ p 91) → (¬ p 98) → (¬ p 132) → False)
    (d499 : (p 6) → (p 16) → (p 97) → False)
    (d603 : (p 98) → (p 108) → (p 150) → False)
    (d54 : (¬ p 100) → (¬ p 108) → (¬ p 125) → False)
    (d493 : (p 119) → (p 125) → (p 138) → False)
    (d457 : (p 90) → (p 98) → (p 125) → False)
    (d49 : (¬ p 25) → (¬ p 27) → (¬ p 119) → False)
    (d43 : (¬ p 90) → (¬ p 97) → (¬ p 124) → False)
    (d638 : (p 25) → (p 20) → (p 30) → False)
    (d254 : (p 25) → (p 32) → (p 124) → False)
    (d145 : (¬ p 30) → (¬ p 32) → (¬ p 149) → False)
    : (p 130) → (¬ p 17) → (¬ p 149) → (p 138) → (¬ p 33) → (¬ p 100) → (¬ p 9) → (p 6) → (p 26) → (¬ p 15) → (p 150) → (p 20) → (¬ p 27) → (p 80) → False := by
  intro a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13
  have v0 : ¬ p 118 := (fun u => d726 a0 u a13)
  have v1 : ¬ p 31 := (fun u => d11 a8 u a0)
  have v2 : p 10 := Classical.byContradiction (fun u => d564 a6 u v0)
  have v3 : p 152 := Classical.byContradiction (fun u => d107 v1 a4 u)
  have v4 : ¬ p 91 := (fun u => d534 a7 v2 u)
  have v5 : p 16 := Classical.byContradiction (fun u => d1247 u v3 a1 a9)
  have v6 : ¬ p 132 := (fun u => d474 a0 u v3)
  have v7 : p 98 := Classical.byContradiction (fun u => d136 v4 u v6)
  have v8 : ¬ p 97 := (fun u => d499 a7 v5 u)
  have v9 : ¬ p 108 := (fun u => d603 v7 u a10)
  have v10 : p 125 := Classical.byContradiction (fun u => d54 a5 v9 u)
  have v11 : ¬ p 119 := (fun u => d493 u v10 a3)
  have v12 : ¬ p 90 := (fun u => d457 u v7 v10)
  have v13 : p 25 := Classical.byContradiction (fun u => d49 u a12 v11)
  have v14 : p 124 := Classical.byContradiction (fun u => d43 v12 v8 u)
  have v15 : ¬ p 30 := (fun u => d638 v13 a11 u)
  have v16 : ¬ p 32 := (fun u => d254 v13 u v14)
  exact d145 v15 v16 a2

theorem c4202 (p : Nat → Prop)
    (d397 : (p 20) → (p 31) → (p 73) → False)
    (d11 : (p 26) → (p 31) → (p 130) → False)
    (d138 : (¬ p 68) → (¬ p 73) → (¬ p 130) → False)
    : (p 31) → (p 26) → (p 20) → (¬ p 68) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 73 := (fun u => d397 a2 a0 u)
  have v1 : ¬ p 130 := (fun u => d11 a1 a0 u)
  exact d138 a3 v0 v1

theorem c4204 (p : Nat → Prop)
    (d523 : (p 20) → (p 33) → (p 75) → False)
    (d611 : (p 33) → (p 143) → (p 150) → False)
    (d34 : (¬ p 70) → (¬ p 75) → (¬ p 143) → False)
    : (p 33) → (¬ p 70) → (p 150) → (p 20) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 75 := (fun u => d523 a3 a0 u)
  have v1 : ¬ p 143 := (fun u => d611 a0 u a2)
  exact d34 a1 v0 v1

theorem c4209 (p : Nat → Prop)
    (d207 : (¬ p 6) → (¬ p 7) → (¬ p 88) → False)
    (d213 : (¬ p 5) → (¬ p 6) → (¬ p 76) → False)
    (d45 : (p 76) → (p 77) → (p 88) → False)
    : (¬ p 6) → (p 77) → (¬ p 7) → (¬ p 5) → False := by
  intro a0 a1 a2 a3
  have v0 : p 88 := Classical.byContradiction (fun u => d207 a0 a2 u)
  have v1 : p 76 := Classical.byContradiction (fun u => d213 a3 a0 u)
  exact d45 v1 a1 v0

theorem c4212 (p : Nat → Prop)
    (d1440 : (p 15) → (p 10) → (p 4) → False)
    (d574 : (p 4) → (p 15) → (p 73) → False)
    (d564 : (¬ p 9) → (¬ p 10) → (¬ p 118) → False)
    (d138 : (¬ p 68) → (¬ p 73) → (¬ p 130) → False)
    (d726 : (p 130) → (p 118) → (p 80) → False)
    : (p 15) → (¬ p 9) → (p 4) → (p 80) → (¬ p 68) → False := by
  intro a0 a1 a2 a3 a4
  have v0 : ¬ p 10 := (fun u => d1440 a0 u a2)
  have v1 : ¬ p 73 := (fun u => d574 a2 a0 u)
  have v2 : p 118 := Classical.byContradiction (fun u => d564 a1 v0 u)
  have v3 : p 130 := Classical.byContradiction (fun u => d138 a4 v1 u)
  exact d726 v3 v2 a3

theorem c4230 (p : Nat → Prop)
    (d563 : (p 35) → (p 47) → (p 74) → False)
    (d194 : (p 42) → (p 47) → (p 137) → False)
    (d589 : (¬ p 69) → (¬ p 74) → (¬ p 137) → False)
    : (p 47) → (p 35) → (¬ p 69) → (p 42) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 74 := (fun u => d563 a1 a0 u)
  have v1 : ¬ p 137 := (fun u => d194 a3 a0 u)
  exact d589 a2 v0 v1

theorem c4232 (p : Nat → Prop)
    (d508 : (¬ p 18) → (¬ p 20) → (¬ p 35) → False)
    (d208 : (p 2) → (p 4) → (p 35) → False)
    (d170 : (¬ p 1) → (¬ p 2) → (¬ p 18) → False)
    (d3435 : (p 34) → (p 1) → False)
    (d505 : (¬ p 2) → (¬ p 3) → (¬ p 34) → False)
    (d1560 : (p 6) → (p 4) → (p 1) → False)
    (d1063 : (p 7) → (p 1) → (p 9) → False)
    (d703 : (p 3) → (p 9) → (p 5) → False)
    (d84 : (p 3) → (p 9) → (p 54) → False)
    (d207 : (¬ p 6) → (¬ p 7) → (¬ p 88) → False)
    (d4016 : (¬ p 6) → (p 99) → (¬ p 7) → (¬ p 5) → (p 3) → False)
    (d213 : (¬ p 5) → (¬ p 6) → (¬ p 76) → False)
    (d2174 : (p 76) → (p 88) → (p 22) → False)
    (d111 : (¬ p 7) → (¬ p 8) → (¬ p 99) → False)
    (d1469 : (¬ p 20) → (p 49) → (¬ p 18) → (¬ p 22) → False)
    (d62 : (p 3) → (p 8) → (p 53) → False)
    (d3727 : (¬ p 49) → (¬ p 53) → (¬ p 54) → (p 8) → (p 80) → (¬ p 63) → False)
    : (p 9) → (p 4) → (¬ p 20) → (¬ p 18) → (p 80) → (¬ p 63) → False := by
  intro a0 a1 a2 a3 a4 a5
  have v0 : p 35 := Classical.byContradiction (fun u => d508 a3 a2 u)
  have v1 : ¬ p 2 := (fun u => d208 u a1 v0)
  have v2 : p 1 := Classical.byContradiction (fun u => d170 u v1 a3)
  have v3 : ¬ p 34 := (fun u => d3435 u v2)
  have v4 : p 3 := Classical.byContradiction (fun u => d505 v1 u v3)
  have v5 : ¬ p 6 := (fun u => d1560 u a1 v2)
  have v6 : ¬ p 7 := (fun u => d1063 u v2 a0)
  have v7 : ¬ p 5 := (fun u => d703 v4 a0 u)
  have v8 : ¬ p 54 := (fun u => d84 v4 a0 u)
  have v9 : p 88 := Classical.byContradiction (fun u => d207 v5 v6 u)
  have v10 : ¬ p 99 := (fun u => d4016 v5 u v6 v7 v4)
  have v11 : p 76 := Classical.byContradiction (fun u => d213 v7 v5 u)
  have v12 : ¬ p 22 := (fun u => d2174 v11 v9 u)
  have v13 : p 8 := Classical.byContradiction (fun u => d111 v6 u v10)
  have v14 : ¬ p 49 := (fun u => d1469 a2 u a3 v12)
  have v15 : ¬ p 53 := (fun u => d62 v4 v13 u)
  exact d3727 v14 v15 v8 v13 a4 a5

theorem c4233 (p : Nat → Prop)
    (d508 : (¬ p 18) → (¬ p 20) → (¬ p 35) → False)
    (d208 : (p 2) → (p 4) → (p 35) → False)
    (d170 : (¬ p 1) → (¬ p 2) → (¬ p 18) → False)
    (d3435 : (p 34) → (p 1) → False)
    (d505 : (¬ p 2) → (¬ p 3) → (¬ p 34) → False)
    (d473 : (p 1) → (p 3) → (p 19) → False)
    (d822 : (p 50) → (p 51) → (p 3) → False)
    (d381 : (¬ p 19) → (¬ p 21) → (¬ p 50) → False)
    (d3227 : (p 51) → (p 76) → (p 22) → False)
    (d1371 : (¬ p 24) → (¬ p 22) → (¬ p 26) → (p 76) → (¬ p 84) → (p 129) → False)
    (d1469 : (¬ p 20) → (p 49) → (¬ p 18) → (¬ p 22) → False)
    (d201 : (p 21) → (p 24) → (p 78) → False)
    (d273 : (¬ p 49) → (¬ p 53) → (¬ p 66) → False)
    (d125 : (¬ p 78) → (¬ p 84) → (¬ p 114) → False)
    (d13 : (p 4) → (p 8) → (p 66) → False)
    (d112 : (p 109) → (p 114) → (p 122) → False)
    (d394 : (¬ p 8) → (¬ p 9) → (¬ p 109) → False)
    : (p 76) → (¬ p 84) → (p 129) → (p 122) → (¬ p 53) → (¬ p 9) → (¬ p 26) → (p 51) → (p 4) → (¬ p 20) → (¬ p 18) → False := by
  intro a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10
  have v0 : p 35 := Classical.byContradiction (fun u => d508 a10 a9 u)
  have v1 : ¬ p 2 := (fun u => d208 u a8 v0)
  have v2 : p 1 := Classical.byContradiction (fun u => d170 u v1 a10)
  have v3 : ¬ p 34 := (fun u => d3435 u v2)
  have v4 : p 3 := Classical.byContradiction (fun u => d505 v1 u v3)
  have v5 : ¬ p 19 := (fun u => d473 v2 v4 u)
  have v6 : ¬ p 50 := (fun u => d822 u a7 v4)
  have v7 : p 21 := Classical.byContradiction (fun u => d381 v5 u v6)
  have v8 : ¬ p 22 := (fun u => d3227 a7 a0 u)
  have v9 : p 24 := Classical.byContradiction (fun u => d1371 u v8 a6 a0 a1 a2)
  have v10 : ¬ p 49 := (fun u => d1469 a9 u a10 v8)
  have v11 : ¬ p 78 := (fun u => d201 v7 v9 u)
  have v12 : p 66 := Classical.byContradiction (fun u => d273 v10 a4 u)
  have v13 : p 114 := Classical.byContradiction (fun u => d125 v11 a1 u)
  have v14 : ¬ p 8 := (fun u => d13 a8 u v12)
  have v15 : ¬ p 109 := (fun u => d112 u v13 a3)
  exact d394 v14 a5 v15

theorem c4234 (p : Nat → Prop)
    (d2677 : (p 23) → (¬ p 6) → (¬ p 8) → (p 1) → False)
    (d394 : (¬ p 8) → (¬ p 9) → (¬ p 109) → False)
    (d442 : (¬ p 23) → (¬ p 25) → (¬ p 100) → False)
    (d265 : (p 109) → (p 110) → (p 118) → False)
    (d140 : (p 24) → (p 25) → (p 109) → False)
    (d341 : (¬ p 24) → (¬ p 26) → (¬ p 110) → False)
    : (¬ p 8) → (¬ p 100) → (p 118) → (¬ p 9) → (¬ p 26) → (¬ p 6) → (p 1) → False := by
  intro a0 a1 a2 a3 a4 a5 a6
  have v0 : ¬ p 23 := (fun u => d2677 u a5 a0 a6)
  have v1 : p 109 := Classical.byContradiction (fun u => d394 a0 a3 u)
  have v2 : p 25 := Classical.byContradiction (fun u => d442 v0 u a1)
  have v3 : ¬ p 110 := (fun u => d265 v1 u a2)
  have v4 : ¬ p 24 := (fun u => d140 u v2 v1)
  exact d341 v4 a4 v3

theorem c4235 (p : Nat → Prop)
    (d508 : (¬ p 18) → (¬ p 20) → (¬ p 35) → False)
    (d208 : (p 2) → (p 4) → (p 35) → False)
    (d170 : (¬ p 1) → (¬ p 2) → (¬ p 18) → False)
    (d3435 : (p 34) → (p 1) → False)
    (d505 : (¬ p 2) → (¬ p 3) → (¬ p 34) → False)
    (d473 : (p 1) → (p 3) → (p 19) → False)
    (d3 : (¬ p 34) → (¬ p 37) → (¬ p 51) → False)
    (d822 : (p 50) → (p 51) → (p 3) → False)
    (d381 : (¬ p 19) → (¬ p 21) → (¬ p 50) → False)
    (d263 : (p 21) → (p 26) → (p 80) → False)
    (d1560 : (p 6) → (p 4) → (p 1) → False)
    (d726 : (p 130) → (p 118) → (p 80) → False)
    (d519 : (p 79) → (p 80) → (p 118) → False)
    (d138 : (¬ p 68) → (¬ p 73) → (¬ p 130) → False)
    (d235 : (¬ p 50) → (¬ p 54) → (¬ p 79) → False)
    (d2263 : (p 72) → (p 4) → (p 73) → False)
    (d797 : (p 54) → (p 53) → (p 3) → False)
    (d79 : (p 54) → (p 55) → (p 118) → False)
    (d614 : (¬ p 37) → (¬ p 34) → (p 54) → (¬ p 40) → False)
    (d291 : (p 35) → (p 40) → (p 67) → False)
    (d3440 : (p 100) → (p 40) → (p 118) → False)
    (d323 : (¬ p 67) → (¬ p 72) → (¬ p 122) → False)
    (d532 : (p 54) → (p 59) → (p 122) → False)
    (d560 : (¬ p 55) → (¬ p 59) → (¬ p 129) → False)
    (d379 : (p 80) → (p 84) → (p 129) → False)
    (d374 : (p 128) → (p 129) → (p 144) → False)
    (d4233 : (p 76) → (¬ p 84) → (p 129) → (p 122) → (¬ p 53) → (¬ p 9) → (¬ p 26) → (p 51) → (p 4) → (¬ p 20) → (¬ p 18) → False)
    (d213 : (¬ p 5) → (¬ p 6) → (¬ p 76) → False)
    (d4234 : (¬ p 8) → (¬ p 100) → (p 118) → (¬ p 9) → (¬ p 26) → (¬ p 6) → (p 1) → False)
    (d5 : (p 5) → (p 8) → (p 78) → False)
    (d13 : (p 4) → (p 8) → (p 66) → False)
    (d2955 : (p 5) → (p 8) → (p 14) → False)
    (d2252 : (p 80) → (p 129) → (p 21) → (¬ p 78) → (¬ p 24) → False)
    (d494 : (¬ p 13) → (¬ p 14) → (¬ p 144) → False)
    (d292 : (p 24) → (p 29) → (p 113) → False)
    (d338 : (p 4) → (p 13) → (p 71) → False)
    (d384 : (¬ p 66) → (¬ p 71) → (¬ p 113) → False)
    : (p 118) → (p 128) → (¬ p 9) → (p 4) → (¬ p 37) → (¬ p 20) → (¬ p 18) → (p 29) → (p 80) → (¬ p 68) → False := by
  intro a0 a1 a2 a3 a4 a5 a6 a7 a8 a9
  have v0 : p 35 := Classical.byContradiction (fun u => d508 a6 a5 u)
  have v1 : ¬ p 2 := (fun u => d208 u a3 v0)
  have v2 : p 1 := Classical.byContradiction (fun u => d170 u v1 a6)
  have v3 : ¬ p 34 := (fun u => d3435 u v2)
  have v4 : p 3 := Classical.byContradiction (fun u => d505 v1 u v3)
  have v5 : ¬ p 19 := (fun u => d473 v2 v4 u)
  have v6 : p 51 := Classical.byContradiction (fun u => d3 v3 a4 u)
  have v7 : ¬ p 50 := (fun u => d822 u v6 v4)
  have v8 : p 21 := Classical.byContradiction (fun u => d381 v5 u v7)
  have v9 : ¬ p 26 := (fun u => d263 v8 u a8)
  have v10 : ¬ p 6 := (fun u => d1560 u a3 v2)
  have v11 : ¬ p 130 := (fun u => d726 u a0 a8)
  have v12 : ¬ p 79 := (fun u => d519 u a8 a0)
  have v13 : p 73 := Classical.byContradiction (fun u => d138 a9 u v11)
  have v14 : p 54 := Classical.byContradiction (fun u => d235 v7 u v12)
  have v15 : ¬ p 72 := (fun u => d2263 u a3 v13)
  have v16 : ¬ p 53 := (fun u => d797 v14 u v4)
  have v17 : ¬ p 55 := (fun u => d79 v14 u a0)
  have v18 : p 40 := Classical.byContradiction (fun u => d614 a4 v3 v14 u)
  have v19 : ¬ p 67 := (fun u => d291 v0 v18 u)
  have v20 : ¬ p 100 := (fun u => d3440 u v18 a0)
  have v21 : p 122 := Classical.byContradiction (fun u => d323 v19 v15 u)
  have v22 : ¬ p 59 := (fun u => d532 v14 u v21)
  have v23 : p 129 := Classical.byContradiction (fun u => d560 v17 v22 u)
  have v24 : ¬ p 84 := (fun u => d379 a8 u v23)
  have v25 : ¬ p 144 := (fun u => d374 a1 v23 u)
  have v26 : ¬ p 76 := (fun u => d4233 u v24 v23 v21 v16 a2 v9 v6 a3 a5 a6)
  have v27 : p 5 := Classical.byContradiction (fun u => d213 u v10 v26)
  have v28 : p 8 := Classical.byContradiction (fun u => d4234 u v20 a0 a2 v9 v10 v2)
  have v29 : ¬ p 78 := (fun u => d5 v27 v28 u)
  have v30 : ¬ p 66 := (fun u => d13 a3 v28 u)
  have v31 : ¬ p 14 := (fun u => d2955 v27 v28 u)
  have v32 : p 24 := Classical.byContradiction (fun u => d2252 a8 v23 v8 v29 u)
  have v33 : p 13 := Classical.byContradiction (fun u => d494 u v31 v25)
  have v34 : ¬ p 113 := (fun u => d292 v32 a7 u)
  have v35 : ¬ p 71 := (fun u => d338 a3 v33 u)
  exact d384 v30 v35 v34

theorem c4236 (p : Nat → Prop)
    (d508 : (¬ p 18) → (¬ p 20) → (¬ p 35) → False)
    (d208 : (p 2) → (p 4) → (p 35) → False)
    (d170 : (¬ p 1) → (¬ p 2) → (¬ p 18) → False)
    (d3435 : (p 34) → (p 1) → False)
    (d505 : (¬ p 2) → (¬ p 3) → (¬ p 34) → False)
    (d473 : (p 1) → (p 3) → (p 19) → False)
    (d2715 : (p 37) → (p 42) → (p 35) → False)
    (d3 : (¬ p 34) → (¬ p 37) → (¬ p 51) → False)
    (d822 : (p 50) → (p 51) → (p 3) → False)
    (d381 : (¬ p 19) → (¬ p 21) → (¬ p 50) → False)
    (d263 : (p 21) → (p 26) → (p 80) → False)
    (d1560 : (p 6) → (p 4) → (p 1) → False)
    (d88 : (¬ p 41) → (¬ p 44) → (¬ p 128) → False)
    (d463 : (¬ p 44) → (¬ p 47) → (¬ p 146) → False)
    (d4235 : (p 118) → (p 128) → (¬ p 9) → (p 4) → (¬ p 37) → (¬ p 20) → (¬ p 18) → (p 29) → (p 80) → (¬ p 68) → False)
    (d564 : (¬ p 9) → (¬ p 10) → (¬ p 118) → False)
    (d147 : (p 5) → (p 10) → (p 80) → False)
    (d1137 : (p 10) → (p 12) → (p 1) → False)
    (d51 : (p 3) → (p 10) → (p 55) → False)
    (d4167 : (p 127) → (p 10) → (p 128) → False)
    (d233 : (p 10) → (p 13) → (p 128) → False)
    (d213 : (¬ p 5) → (¬ p 6) → (¬ p 76) → False)
    (d92 : (¬ p 12) → (¬ p 13) → (¬ p 139) → False)
    (d4124 : (p 1) → (¬ p 127) → (p 10) → (p 27) → False)
    (d492 : (¬ p 26) → (¬ p 28) → (¬ p 127) → False)
    (d3227 : (p 51) → (p 76) → (p 22) → False)
    (d3483 : (p 146) → (p 58) → (p 139) → False)
    (d270 : (¬ p 20) → (¬ p 22) → (¬ p 64) → False)
    (d1469 : (¬ p 20) → (p 49) → (¬ p 18) → (¬ p 22) → False)
    (d647 : (p 65) → (p 64) → (p 4) → False)
    (d900 : (¬ p 24) → (¬ p 55) → (p 64) → (¬ p 22) → (¬ p 26) → False)
    (d154 : (¬ p 65) → (¬ p 70) → (¬ p 103) → False)
    (d146 : (p 23) → (p 28) → (p 103) → False)
    (d748 : (¬ p 54) → (¬ p 58) → (¬ p 23) → (p 29) → (¬ p 50) → False)
    (d797 : (p 54) → (p 53) → (p 3) → False)
    (d614 : (¬ p 37) → (¬ p 34) → (p 54) → (¬ p 40) → False)
    (d273 : (¬ p 49) → (¬ p 53) → (¬ p 66) → False)
    (d227 : (p 40) → (p 42) → (p 119) → False)
    (d13 : (p 4) → (p 8) → (p 66) → False)
    (d49 : (¬ p 25) → (¬ p 27) → (¬ p 119) → False)
    (d394 : (¬ p 8) → (¬ p 9) → (¬ p 109) → False)
    (d140 : (p 24) → (p 25) → (p 109) → False)
    : (¬ p 44) → (¬ p 70) → (¬ p 9) → (p 4) → (¬ p 47) → (¬ p 20) → (¬ p 18) → (p 42) → (p 29) → (¬ p 41) → (p 80) → (¬ p 68) → False := by
  intro a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11
  have v0 : p 35 := Classical.byContradiction (fun u => d508 a6 a5 u)
  have v1 : ¬ p 2 := (fun u => d208 u a3 v0)
  have v2 : p 1 := Classical.byContradiction (fun u => d170 u v1 a6)
  have v3 : ¬ p 34 := (fun u => d3435 u v2)
  have v4 : p 3 := Classical.byContradiction (fun u => d505 v1 u v3)
  have v5 : ¬ p 19 := (fun u => d473 v2 v4 u)
  have v6 : ¬ p 37 := (fun u => d2715 u a7 v0)
  have v7 : p 51 := Classical.byContradiction (fun u => d3 v3 v6 u)
  have v8 : ¬ p 50 := (fun u => d822 u v7 v4)
  have v9 : p 21 := Classical.byContradiction (fun u => d381 v5 u v8)
  have v10 : ¬ p 26 := (fun u => d263 v9 u a10)
  have v11 : ¬ p 6 := (fun u => d1560 u a3 v2)
  have v12 : p 128 := Classical.byContradiction (fun u => d88 a9 a0 u)
  have v13 : p 146 := Classical.byContradiction (fun u => d463 a0 a4 u)
  have v14 : ¬ p 118 := (fun u => d4235 u v12 a2 a3 v6 a5 a6 a8 a10 a11)
  have v15 : p 10 := Classical.byContradiction (fun u => d564 a2 u v14)
  have v16 : ¬ p 5 := (fun u => d147 u v15 a10)
  have v17 : ¬ p 12 := (fun u => d1137 v15 u v2)
  have v18 : ¬ p 55 := (fun u => d51 v4 v15 u)
  have v19 : ¬ p 127 := (fun u => d4167 u v15 v12)
  have v20 : ¬ p 13 := (fun u => d233 v15 u v12)
  have v21 : p 76 := Classical.byContradiction (fun u => d213 v16 v11 u)
  have v22 : p 139 := Classical.byContradiction (fun u => d92 v17 v20 u)
  have v23 : ¬ p 27 := (fun u => d4124 v2 v19 v15 u)
  have v24 : p 28 := Classical.byContradiction (fun u => d492 v10 u v19)
  have v25 : ¬ p 22 := (fun u => d3227 v7 v21 u)
  have v26 : ¬ p 58 := (fun u => d3483 v13 u v22)
  have v27 : p 64 := Classical.byContradiction (fun u => d270 a5 v25 u)
  have v28 : ¬ p 49 := (fun u => d1469 a5 u a6 v25)
  have v29 : ¬ p 65 := (fun u => d647 u v27 a3)
  have v30 : p 24 := Classical.byContradiction (fun u => d900 u v18 v27 v25 v10)
  have v31 : p 103 := Classical.byContradiction (fun u => d154 v29 a1 u)
  have v32 : ¬ p 23 := (fun u => d146 u v24 v31)
  have v33 : p 54 := Classical.byContradiction (fun u => d748 u v26 v32 a8 v8)
  have v34 : ¬ p 53 := (fun u => d797 v33 u v4)
  have v35 : p 40 := Classical.byContradiction (fun u => d614 v6 v3 v33 u)
  have v36 : p 66 := Classical.byContradiction (fun u => d273 v28 v34 u)
  have v37 : ¬ p 119 := (fun u => d227 v35 a7 u)
  have v38 : ¬ p 8 := (fun u => d13 a3 u v36)
  have v39 : p 25 := Classical.byContradiction (fun u => d49 u v23 v37)
  have v40 : p 109 := Classical.byContradiction (fun u => d394 v38 a2 u)
  exact d140 v30 v39 v40

theorem c4245 (p : Nat → Prop)
    (d118 : (p 22) → (p 24) → (p 89) → False)
    (d777 : (p 51) → (p 89) → (p 64) → False)
    (d270 : (¬ p 20) → (¬ p 22) → (¬ p 64) → False)
    : (p 89) → (p 24) → (p 51) → (¬ p 20) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 22 := (fun u => d118 u a1 a0)
  have v1 : ¬ p 64 := (fun u => d777 a2 a0 u)
  exact d270 a3 v0 v1

theorem c4259 (p : Nat → Prop)
    (d3 : (¬ p 34) → (¬ p 37) → (¬ p 51) → False)
    (d614 : (¬ p 37) → (¬ p 34) → (p 54) → (¬ p 40) → False)
    (d822 : (p 50) → (p 51) → (p 3) → False)
    (d235 : (¬ p 50) → (¬ p 54) → (¬ p 79) → False)
    : (¬ p 37) → (¬ p 79) → (p 3) → (¬ p 40) → (¬ p 34) → False := by
  intro a0 a1 a2 a3 a4
  have v0 : p 51 := Classical.byContradiction (fun u => d3 a4 a0 u)
  have v1 : ¬ p 54 := (fun u => d614 a0 a4 u a3)
  have v2 : ¬ p 50 := (fun u => d822 u v0 a2)
  exact d235 v2 v1 a1

theorem c4272 (p : Nat → Prop)
    (d144 : (p 28) → (p 31) → (p 141) → False)
    (d475 : (p 18) → (p 31) → (p 46) → False)
    (d521 : (¬ p 43) → (¬ p 46) → (¬ p 141) → False)
    : (p 31) → (p 28) → (¬ p 43) → (p 18) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 141 := (fun u => d144 a1 a0 u)
  have v1 : ¬ p 46 := (fun u => d475 a3 a0 u)
  exact d521 a2 v1 v0

theorem c4301 (p : Nat → Prop)
    (d4209 : (¬ p 6) → (p 77) → (¬ p 7) → (¬ p 5) → False)
    (d111 : (¬ p 7) → (¬ p 8) → (¬ p 99) → False)
    (d75 : (¬ p 21) → (¬ p 23) → (¬ p 77) → False)
    (d308 : (p 23) → (p 24) → (p 99) → False)
    : (¬ p 7) → (¬ p 8) → (p 24) → (¬ p 6) → (¬ p 5) → (¬ p 21) → False := by
  intro a0 a1 a2 a3 a4 a5
  have v0 : ¬ p 77 := (fun u => d4209 a3 u a0 a4)
  have v1 : p 99 := Classical.byContradiction (fun u => d111 a0 a1 u)
  have v2 : p 23 := Classical.byContradiction (fun u => d75 a5 u v0)
  exact d308 v2 a2 v1

theorem c4314 (p : Nat → Prop)
    (d957 : (¬ p 11) → (¬ p 12) → (p 127) → (¬ p 10) → False)
    (d2012 : (¬ p 11) → (¬ p 12) → (¬ p 25) → (¬ p 9) → (¬ p 10) → False)
    (d492 : (¬ p 26) → (¬ p 28) → (¬ p 127) → False)
    (d3714 : (p 28) → (p 25) → (p 18) → False)
    : (¬ p 12) → (¬ p 11) → (¬ p 9) → (¬ p 10) → (¬ p 26) → (p 18) → False := by
  intro a0 a1 a2 a3 a4 a5
  have v0 : ¬ p 127 := (fun u => d957 a1 a0 u a3)
  have v1 : p 25 := Classical.byContradiction (fun u => d2012 a1 a0 u a2 a3)
  have v2 : p 28 := Classical.byContradiction (fun u => d492 a4 u v0)
  exact d3714 v2 v1 a5

theorem c4345 (p : Nat → Prop)
    (d3727 : (¬ p 49) → (¬ p 53) → (¬ p 54) → (p 8) → (p 80) → (¬ p 63) → False)
    (d3671 : (¬ p 53) → (p 99) → (¬ p 57) → (¬ p 49) → False)
    (d111 : (¬ p 7) → (¬ p 8) → (¬ p 99) → False)
    : (¬ p 49) → (¬ p 53) → (¬ p 57) → (¬ p 54) → (¬ p 7) → (p 80) → (¬ p 63) → False := by
  intro a0 a1 a2 a3 a4 a5 a6
  have v0 : ¬ p 8 := (fun u => d3727 a0 a1 a3 u a5 a6)
  have v1 : ¬ p 99 := (fun u => d3671 a1 u a2 a0)
  exact d111 a4 v0 v1

theorem c4354 (p : Nat → Prop)
    (d13 : (p 4) → (p 8) → (p 66) → False)
    (d62 : (p 3) → (p 8) → (p 53) → False)
    (d273 : (¬ p 49) → (¬ p 53) → (¬ p 66) → False)
    : (p 8) → (¬ p 49) → (p 3) → (p 4) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 66 := (fun u => d13 a3 a0 u)
  have v1 : ¬ p 53 := (fun u => d62 a2 a0 u)
  exact d273 a1 v1 v0

theorem c4366 (p : Nat → Prop)
    (d587 : (p 20) → (p 28) → (p 70) → False)
    (d3136 : (p 33) → (p 28) → (¬ p 70) → (p 20) → False)
    : (p 28) → (p 33) → (p 20) → False := by
  intro a0 a1 a2
  have v0 : ¬ p 70 := (fun u => d587 a2 a0 u)
  exact d3136 a1 a0 v0 a2

theorem c4369 (p : Nat → Prop)
    (d515 : (p 2) → (p 13) → (p 44) → False)
    (d233 : (p 10) → (p 13) → (p 128) → False)
    (d88 : (¬ p 41) → (¬ p 44) → (¬ p 128) → False)
    : (p 13) → (p 2) → (p 10) → (¬ p 41) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 44 := (fun u => d515 a1 a0 u)
  have v1 : ¬ p 128 := (fun u => d233 a2 a0 u)
  exact d88 a3 v0 v1

theorem c4383 (p : Nat → Prop)
    (d222 : (p 20) → (p 23) → (p 65) → False)
    (d666 : (p 104) → (p 99) → (p 65) → False)
    (d2719 : (¬ p 77) → (¬ p 104) → (p 29) → (¬ p 23) → False)
    : (p 65) → (¬ p 77) → (p 99) → (p 20) → (p 29) → False := by
  intro a0 a1 a2 a3 a4
  have v0 : ¬ p 23 := (fun u => d222 a3 u a0)
  have v1 : ¬ p 104 := (fun u => d666 u a2 a0)
  exact d2719 a1 v1 a4 v0

theorem c4388 (p : Nat → Prop)
    (d32 : (p 4) → (p 6) → (p 64) → False)
    (d4169 : (p 24) → (p 20) → (p 29) → False)
    (d4152 : (p 8) → (p 10) → (¬ p 26) → (p 4) → (p 20) → (p 29) → False)
    (d46 : (p 6) → (p 8) → (p 89) → False)
    (d44 : (p 26) → (p 29) → (p 128) → False)
    (d400 : (¬ p 22) → (¬ p 24) → (¬ p 89) → False)
    (d88 : (¬ p 41) → (¬ p 44) → (¬ p 128) → False)
    (d2150 : (p 44) → (p 45) → (p 2) → False)
    (d1383 : (p 44) → (p 40) → (p 34) → False)
    (d417 : (¬ p 42) → (¬ p 45) → (¬ p 135) → False)
    (d10 : (¬ p 37) → (¬ p 40) → (¬ p 90) → False)
    (d1229 : (p 22) → (p 90) → (p 92) → False)
    (d26 : (p 22) → (p 25) → (p 90) → False)
    (d16 : (¬ p 64) → (¬ p 69) → (¬ p 92) → False)
    (d257 : (p 20) → (p 27) → (p 69) → False)
    (d1178 : (p 135) → (p 119) → (p 69) → False)
    (d49 : (¬ p 25) → (¬ p 27) → (¬ p 119) → False)
    : (p 8) → (p 6) → (p 34) → (p 20) → (¬ p 37) → (p 2) → (p 4) → (p 10) → (¬ p 42) → (p 29) → (¬ p 41) → False := by
  intro a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10
  have v0 : ¬ p 64 := (fun u => d32 a6 a1 u)
  have v1 : ¬ p 24 := (fun u => d4169 u a3 a9)
  have v2 : p 26 := Classical.byContradiction (fun u => d4152 a0 a7 u a6 a3 a9)
  have v3 : ¬ p 89 := (fun u => d46 a1 a0 u)
  have v4 : ¬ p 128 := (fun u => d44 v2 a9 u)
  have v5 : p 22 := Classical.byContradiction (fun u => d400 u v1 v3)
  have v6 : p 44 := Classical.byContradiction (fun u => d88 a10 u v4)
  have v7 : ¬ p 45 := (fun u => d2150 v6 u a5)
  have v8 : ¬ p 40 := (fun u => d1383 v6 u a2)
  have v9 : p 135 := Classical.byContradiction (fun u => d417 a8 v7 u)
  have v10 : p 90 := Classical.byContradiction (fun u => d10 a4 v8 u)
  have v11 : ¬ p 92 := (fun u => d1229 v5 v10 u)
  have v12 : ¬ p 25 := (fun u => d26 v5 u v10)
  have v13 : p 69 := Classical.byContradiction (fun u => d16 v0 u v11)
  have v14 : ¬ p 27 := (fun u => d257 a3 u v13)
  have v15 : ¬ p 119 := (fun u => d1178 v9 u v13)
  exact d49 v12 v14 v15

theorem c4390 (p : Nat → Prop)
    (d3 : (¬ p 34) → (¬ p 37) → (¬ p 51) → False)
    (d10 : (¬ p 37) → (¬ p 40) → (¬ p 90) → False)
    (d1808 : (¬ p 37) → (¬ p 90) → (¬ p 51) → (p 54) → False)
    (d1383 : (p 44) → (p 40) → (p 34) → False)
    (d748 : (¬ p 54) → (¬ p 58) → (¬ p 23) → (p 29) → (¬ p 50) → False)
    (d88 : (¬ p 41) → (¬ p 44) → (¬ p 128) → False)
    (d222 : (p 20) → (p 23) → (p 65) → False)
    (d44 : (p 26) → (p 29) → (p 128) → False)
    (d4167 : (p 127) → (p 10) → (p 128) → False)
    (d2684 : (p 28) → (p 23) → (¬ p 65) → (p 20) → False)
    (d492 : (¬ p 26) → (¬ p 28) → (¬ p 127) → False)
    : (¬ p 90) → (¬ p 58) → (¬ p 50) → (¬ p 51) → (p 20) → (¬ p 37) → (p 10) → (p 29) → (¬ p 41) → False := by
  intro a0 a1 a2 a3 a4 a5 a6 a7 a8
  have v0 : p 34 := Classical.byContradiction (fun u => d3 u a5 a3)
  have v1 : p 40 := Classical.byContradiction (fun u => d10 a5 u a0)
  have v2 : ¬ p 54 := (fun u => d1808 a5 a0 a3 u)
  have v3 : ¬ p 44 := (fun u => d1383 u v1 v0)
  have v4 : p 23 := Classical.byContradiction (fun u => d748 v2 a1 u a7 a2)
  have v5 : p 128 := Classical.byContradiction (fun u => d88 a8 v3 u)
  have v6 : ¬ p 65 := (fun u => d222 a4 v4 u)
  have v7 : ¬ p 26 := (fun u => d44 u a7 v5)
  have v8 : ¬ p 127 := (fun u => d4167 u a6 v5)
  have v9 : ¬ p 28 := (fun u => d2684 u v4 v6 a4)
  exact d492 v7 v9 v8

theorem c4392 (p : Nat → Prop)
    (d46 : (p 6) → (p 8) → (p 89) → False)
    (d327 : (p 89) → (p 90) → (p 109) → False)
    (d394 : (¬ p 8) → (¬ p 9) → (¬ p 109) → False)
    : (p 89) → (¬ p 9) → (p 6) → (p 90) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 8 := (fun u => d46 a2 u a0)
  have v1 : ¬ p 109 := (fun u => d327 a0 a3 u)
  exact d394 v0 a1 v1

theorem c4402 (p : Nat → Prop)
    (d534 : (p 6) → (p 10) → (p 91) → False)
    (d275 : (p 76) → (p 80) → (p 91) → False)
    (d213 : (¬ p 5) → (¬ p 6) → (¬ p 76) → False)
    : (p 91) → (p 10) → (¬ p 5) → (p 80) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 6 := (fun u => d534 u a1 a0)
  have v1 : ¬ p 76 := (fun u => d275 u a3 a0)
  exact d213 a2 v0 v1

theorem c4404 (p : Nat → Prop)
    (d1258 : (p 26) → (p 130) → (¬ p 152) → (p 132) → False)
    (d474 : (p 130) → (p 132) → (p 152) → False)
    : (p 26) → (p 130) → (p 132) → False := by
  intro a0 a1 a2
  have v0 : p 152 := Classical.byContradiction (fun u => d1258 a0 a1 u a2)
  exact d474 a1 a2 v0

theorem c4414 (p : Nat → Prop)
    (d1758 : (p 27) → (p 32) → (p 20) → False)
    (d464 : (p 27) → (p 33) → (p 138) → False)
    (d145 : (¬ p 30) → (¬ p 32) → (¬ p 149) → False)
    (d107 : (¬ p 31) → (¬ p 33) → (¬ p 152) → False)
    (d906 : (p 150) → (p 14) → (p 149) → False)
    (d229 : (p 148) → (p 150) → (p 152) → False)
    (d27 : (¬ p 14) → (¬ p 15) → (¬ p 148) → False)
    : (p 27) → (p 150) → (p 138) → (¬ p 30) → (¬ p 31) → (¬ p 15) → (p 20) → False := by
  intro a0 a1 a2 a3 a4 a5 a6
  have v0 : ¬ p 32 := (fun u => d1758 a0 u a6)
  have v1 : ¬ p 33 := (fun u => d464 a0 u a2)
  have v2 : p 149 := Classical.byContradiction (fun u => d145 a3 v0 u)
  have v3 : p 152 := Classical.byContradiction (fun u => d107 a4 v1 u)
  have v4 : ¬ p 14 := (fun u => d906 a1 u v2)
  have v5 : ¬ p 148 := (fun u => d229 u a1 v3)
  exact d27 v4 a5 v5

theorem c4426 (p : Nat → Prop)
    (d550 : (p 80) → (p 87) → (p 132) → False)
    (d1253 : (p 143) → (p 98) → (¬ p 76) → (p 87) → False)
    (d136 : (¬ p 91) → (¬ p 98) → (¬ p 132) → False)
    : (p 87) → (p 143) → (¬ p 76) → (¬ p 91) → (p 80) → False := by
  intro a0 a1 a2 a3 a4
  have v0 : ¬ p 132 := (fun u => d550 a4 a0 u)
  have v1 : ¬ p 98 := (fun u => d1253 a1 u a2 a0)
  exact d136 a3 v1 v0

theorem c4462 (p : Nat → Prop)
    (d3699 : (¬ p 24) → (¬ p 93) → (p 78) → (¬ p 19) → (p 80) → (¬ p 22) → False)
    (d572 : (p 77) → (p 78) → (p 99) → False)
    (d75 : (¬ p 21) → (¬ p 23) → (¬ p 77) → False)
    (d364 : (p 19) → (p 23) → (p 52) → False)
    (d557 : (p 23) → (p 27) → (p 102) → False)
    (d366 : (¬ p 52) → (¬ p 56) → (¬ p 102) → False)
    : (p 78) → (¬ p 21) → (¬ p 93) → (p 99) → (¬ p 24) → (¬ p 56) → (p 27) → (¬ p 22) → (p 80) → False := by
  intro a0 a1 a2 a3 a4 a5 a6 a7 a8
  have v0 : p 19 := Classical.byContradiction (fun u => d3699 a4 a2 a0 u a8 a7)
  have v1 : ¬ p 77 := (fun u => d572 u a0 a3)
  have v2 : p 23 := Classical.byContradiction (fun u => d75 a1 u v1)
  have v3 : ¬ p 52 := (fun u => d364 v0 v2 u)
  have v4 : ¬ p 102 := (fun u => d557 v2 a6 u)
  exact d366 v3 a5 v4

theorem c4478 (p : Nat → Prop)
    (d4016 : (¬ p 6) → (p 99) → (¬ p 7) → (¬ p 5) → (p 3) → False)
    (d207 : (¬ p 6) → (¬ p 7) → (¬ p 88) → False)
    (d111 : (¬ p 7) → (¬ p 8) → (¬ p 99) → False)
    (d1476 : (p 92) → (p 51) → (p 88) → False)
    (d4354 : (p 8) → (¬ p 49) → (p 3) → (p 4) → False)
    (d16 : (¬ p 64) → (¬ p 69) → (¬ p 92) → False)
    (d105 : (p 49) → (p 51) → (p 64) → False)
    : (¬ p 7) → (¬ p 69) → (p 51) → (¬ p 6) → (p 3) → (p 4) → (¬ p 5) → False := by
  intro a0 a1 a2 a3 a4 a5 a6
  have v0 : ¬ p 99 := (fun u => d4016 a3 u a0 a6 a4)
  have v1 : p 88 := Classical.byContradiction (fun u => d207 a3 a0 u)
  have v2 : p 8 := Classical.byContradiction (fun u => d111 a0 u v0)
  have v3 : ¬ p 92 := (fun u => d1476 u a2 v1)
  have v4 : p 49 := Classical.byContradiction (fun u => d4354 v2 u a4 a5)
  have v5 : p 64 := Classical.byContradiction (fun u => d16 u a1 v3)
  exact d105 v4 a2 v5

theorem c4498 (p : Nat → Prop)
    (d143 : (p 9) → (p 11) → (p 119) → False)
    (d181 : (p 4) → (p 9) → (p 67) → False)
    (d8 : (¬ p 27) → (¬ p 29) → (¬ p 134) → False)
    (d49 : (¬ p 25) → (¬ p 27) → (¬ p 119) → False)
    (d3695 : (p 135) → (p 134) → (p 11) → False)
    (d393 : (p 11) → (p 13) → (p 134) → False)
    (d3714 : (p 28) → (p 25) → (p 18) → False)
    (d225 : (p 18) → (p 25) → (p 40) → False)
    (d417 : (¬ p 42) → (¬ p 45) → (¬ p 135) → False)
    (d3721 : (p 43) → (p 18) → (p 45) → False)
    (d3694 : (p 45) → (¬ p 67) → (p 4) → (¬ p 28) → (¬ p 13) → (p 25) → (¬ p 12) → (p 18) → False)
    (d173 : (¬ p 40) → (¬ p 43) → (¬ p 120) → False)
    (d301 : (p 9) → (p 12) → (p 120) → False)
    : (¬ p 27) → (¬ p 42) → (p 11) → (p 4) → (p 9) → (p 18) → (¬ p 29) → False := by
  intro a0 a1 a2 a3 a4 a5 a6
  have v0 : ¬ p 119 := (fun u => d143 a4 a2 u)
  have v1 : ¬ p 67 := (fun u => d181 a3 a4 u)
  have v2 : p 134 := Classical.byContradiction (fun u => d8 a0 a6 u)
  have v3 : p 25 := Classical.byContradiction (fun u => d49 u a0 v0)
  have v4 : ¬ p 135 := (fun u => d3695 u v2 a2)
  have v5 : ¬ p 13 := (fun u => d393 a2 u v2)
  have v6 : ¬ p 28 := (fun u => d3714 u v3 a5)
  have v7 : ¬ p 40 := (fun u => d225 a5 v3 u)
  have v8 : p 45 := Classical.byContradiction (fun u => d417 a1 u v4)
  have v9 : ¬ p 43 := (fun u => d3721 u a5 v8)
  have v10 : p 12 := Classical.byContradiction (fun u => d3694 v8 v1 a3 v6 v5 v3 u a5)
  have v11 : p 120 := Classical.byContradiction (fun u => d173 v7 v9 u)
  exact d301 a4 v10 v11

theorem c4519 (p : Nat → Prop)
    (d129 : (p 3) → (p 7) → (p 52) → False)
    (d370 : (p 5) → (p 7) → (p 77) → False)
    (d366 : (¬ p 52) → (¬ p 56) → (¬ p 102) → False)
    (d75 : (¬ p 21) → (¬ p 23) → (¬ p 77) → False)
    (d3501 : (p 42) → (p 102) → (p 37) → (¬ p 65) → False)
    (d222 : (p 20) → (p 23) → (p 65) → False)
    : (p 7) → (p 5) → (p 42) → (¬ p 56) → (p 3) → (p 37) → (p 20) → (¬ p 21) → False := by
  intro a0 a1 a2 a3 a4 a5 a6 a7
  have v0 : ¬ p 52 := (fun u => d129 a4 a0 u)
  have v1 : ¬ p 77 := (fun u => d370 a1 a0 u)
  have v2 : p 102 := Classical.byContradiction (fun u => d366 v0 a3 u)
  have v3 : p 23 := Classical.byContradiction (fun u => d75 a7 u v1)
  have v4 : p 65 := Classical.byContradiction (fun u => d3501 a2 v2 a5 u)
  exact d222 a6 v3 v4

theorem c4533 (p : Nat → Prop)
    (d637 : (p 100) → (p 7) → (p 99) → (¬ p 8) → False)
    (d276 : (p 7) → (p 8) → (p 99) → False)
    : (p 99) → (p 100) → (p 7) → False := by
  intro a0 a1 a2
  have v0 : p 8 := Classical.byContradiction (fun u => d637 a1 a2 a0 u)
  exact d276 a2 v0 a0

theorem c4535 (p : Nat → Prop)
    (d1340 : (p 21) → (p 76) → (¬ p 64) → (p 63) → False)
    (d469 : (p 63) → (p 64) → (p 76) → False)
    : (p 63) → (p 21) → (p 76) → False := by
  intro a0 a1 a2
  have v0 : p 64 := Classical.byContradiction (fun u => d1340 a1 a2 u a0)
  exact d469 a0 v0 a2

theorem c4536 (p : Nat → Prop)
    (d1245 : (p 80) → (p 21) → (¬ p 24) → (p 78) → False)
    (d201 : (p 21) → (p 24) → (p 78) → False)
    : (p 78) → (p 80) → (p 21) → False := by
  intro a0 a1 a2
  have v0 : p 24 := Classical.byContradiction (fun u => d1245 a1 a2 u a0)
  exact d201 a2 v0 a0

theorem c4538 (p : Nat → Prop)
    (d1042 : (p 130) → (p 15) → (p 136) → (¬ p 11) → False)
    (d91 : (p 11) → (p 15) → (p 136) → False)
    : (p 136) → (p 15) → (p 130) → False := by
  intro a0 a1 a2
  have v0 : p 11 := Classical.byContradiction (fun u => d1042 a2 a1 a0 u)
  exact d91 v0 a1 a0

theorem c4540 (p : Nat → Prop)
    (d1288 : (p 11) → (p 14) → (¬ p 45) → (p 2) → False)
    (d244 : (p 2) → (p 14) → (p 45) → False)
    : (p 14) → (p 11) → (p 2) → False := by
  intro a0 a1 a2
  have v0 : p 45 := Classical.byContradiction (fun u => d1288 a1 a0 u a2)
  exact d244 a2 a0 v0

theorem c4544 (p : Nat → Prop)
    (d826 : (p 28) → (p 43) → (p 12) → (¬ p 2) → False)
    (d18 : (p 2) → (p 12) → (p 43) → False)
    : (p 43) → (p 28) → (p 12) → False := by
  intro a0 a1 a2
  have v0 : p 2 := Classical.byContradiction (fun u => d826 a1 a0 a2 u)
  exact d18 v0 a2 a0

theorem c4549 (p : Nat → Prop)
    (d623 : (p 12) → (p 141) → (p 142) → (¬ p 151) → False)
    (d496 : (p 141) → (p 142) → (p 151) → False)
    : (p 142) → (p 141) → (p 12) → False := by
  intro a0 a1 a2
  have v0 : p 151 := Classical.byContradiction (fun u => d623 a2 a1 a0 u)
  exact d496 a1 a0 v0

theorem c4553 (p : Nat → Prop)
    (d1270 : (p 91) → (p 22) → (¬ p 24) → (p 89) → False)
    (d118 : (p 22) → (p 24) → (p 89) → False)
    : (p 89) → (p 22) → (p 91) → False := by
  intro a0 a1 a2
  have v0 : p 24 := Classical.byContradiction (fun u => d1270 a2 a1 u a0)
  exact d118 a1 v0 a0

theorem c4556 (p : Nat → Prop)
    (d886 : (p 12) → (p 7) → (¬ p 65) → (p 4) → False)
    (d418 : (p 4) → (p 7) → (p 65) → False)
    : (p 12) → (p 4) → (p 7) → False := by
  intro a0 a1 a2
  have v0 : p 65 := Classical.byContradiction (fun u => d886 a0 a2 u a1)
  exact d418 a1 a2 v0

theorem c4557 (p : Nat → Prop)
    (d1163 : (p 78) → (p 77) → (p 5) → (¬ p 7) → False)
    (d370 : (p 5) → (p 7) → (p 77) → False)
    : (p 77) → (p 78) → (p 5) → False := by
  intro a0 a1 a2
  have v0 : p 7 := Classical.byContradiction (fun u => d1163 a1 a0 a2 u)
  exact d370 a2 v0 a0

theorem c4559 (p : Nat → Prop)
    (d1433 : (p 45) → (p 40) → (p 35) → (¬ p 67) → False)
    (d291 : (p 35) → (p 40) → (p 67) → False)
    : (p 35) → (p 45) → (p 40) → False := by
  intro a0 a1 a2
  have v0 : p 67 := Classical.byContradiction (fun u => d1433 a1 a2 a0 u)
  exact d291 a0 a2 v0

theorem c4561 (p : Nat → Prop)
    (d922 : (p 55) → (p 58) → (¬ p 44) → (p 34) → False)
    (d209 : (p 34) → (p 44) → (p 58) → False)
    : (p 55) → (p 58) → (p 34) → False := by
  intro a0 a1 a2
  have v0 : p 44 := Classical.byContradiction (fun u => d922 a0 a1 u a2)
  exact d209 a2 v0 a1

theorem c4563 (p : Nat → Prop)
    (d1158 : (p 104) → (p 44) → (p 71) → (¬ p 35) → False)
    (d483 : (p 35) → (p 44) → (p 71) → False)
    : (p 104) → (p 71) → (p 44) → False := by
  intro a0 a1 a2
  have v0 : p 35 := Classical.byContradiction (fun u => d1158 a0 a2 a1 u)
  exact d483 v0 a2 a1

theorem c4566 (p : Nat → Prop)
    (d2271 : (p 78) → (p 8) → (p 89) → (¬ p 6) → False)
    (d46 : (p 6) → (p 8) → (p 89) → False)
    : (p 78) → (p 8) → (p 89) → False := by
  intro a0 a1 a2
  have v0 : p 6 := Classical.byContradiction (fun u => d2271 a0 a1 a2 u)
  exact d46 v0 a1 a2

theorem c4571 (p : Nat → Prop)
    (d2075 : (p 87) → (p 77) → (p 79) → (¬ p 100) → False)
    (d264 : (p 77) → (p 79) → (p 100) → False)
    : (p 77) → (p 87) → (p 79) → False := by
  intro a0 a1 a2
  have v0 : p 100 := Classical.byContradiction (fun u => d2075 a1 a0 a2 u)
  exact d264 a0 a2 v0

theorem c4574 (p : Nat → Prop)
    (d1757 : (p 149) → (p 105) → (¬ p 99) → (p 114) → False)
    (d297 : (p 99) → (p 105) → (p 114) → False)
    : (p 114) → (p 105) → (p 149) → False := by
  intro a0 a1 a2
  have v0 : p 99 := Classical.byContradiction (fun u => d1757 a2 a1 u a0)
  exact d297 v0 a1 a0

theorem c4578 (p : Nat → Prop)
    (d1478 : (p 56) → (¬ p 12) → (p 57) → (p 3) → False)
    (d329 : (p 3) → (p 12) → (p 57) → False)
    : (p 57) → (p 3) → (p 56) → False := by
  intro a0 a1 a2
  have v0 : p 12 := Classical.byContradiction (fun u => d1478 a2 u a0 a1)
  exact d329 a1 v0 a0

theorem c4579 (p : Nat → Prop)
    (d1546 : (p 58) → (p 57) → (¬ p 12) → (p 3) → False)
    (d329 : (p 3) → (p 12) → (p 57) → False)
    : (p 57) → (p 58) → (p 3) → False := by
  intro a0 a1 a2
  have v0 : p 12 := Classical.byContradiction (fun u => d1546 a1 a0 u a2)
  exact d329 a2 v0 a0

theorem c4584 (p : Nat → Prop)
    (d2723 : (p 41) → (p 68) → (p 26) → (¬ p 20) → False)
    (d359 : (p 20) → (p 26) → (p 68) → False)
    : (p 68) → (p 26) → (p 41) → False := by
  intro a0 a1 a2
  have v0 : p 20 := Classical.byContradiction (fun u => d2723 a2 a0 a1 u)
  exact d359 v0 a1 a0

theorem c4587 (p : Nat → Prop)
    (d2504 : (p 33) → (p 21) → (¬ p 81) → (p 27) → False)
    (d151 : (p 21) → (p 27) → (p 81) → False)
    : (p 33) → (p 27) → (p 21) → False := by
  intro a0 a1 a2
  have v0 : p 81 := Classical.byContradiction (fun u => d2504 a0 a2 u a1)
  exact d151 a2 a1 v0

theorem c4588 (p : Nat → Prop)
    (d2969 : (p 74) → (p 72) → (p 20) → (¬ p 30) → False)
    (d432 : (p 20) → (p 30) → (p 72) → False)
    : (p 72) → (p 74) → (p 20) → False := by
  intro a0 a1 a2
  have v0 : p 30 := Classical.byContradiction (fun u => d2969 a1 a0 a2 u)
  exact d432 a2 v0 a0

theorem c4589 (p : Nat → Prop)
    (d3196 : (p 89) → (p 24) → (p 66) → (¬ p 20) → False)
    (d489 : (p 20) → (p 24) → (p 66) → False)
    : (p 89) → (p 66) → (p 24) → False := by
  intro a0 a1 a2
  have v0 : p 20 := Classical.byContradiction (fun u => d3196 a0 a2 a1 u)
  exact d489 v0 a2 a1

theorem c4590 (p : Nat → Prop)
    (d2684 : (p 28) → (p 23) → (¬ p 65) → (p 20) → False)
    (d222 : (p 20) → (p 23) → (p 65) → False)
    : (p 28) → (p 20) → (p 23) → False := by
  intro a0 a1 a2
  have v0 : p 65 := Classical.byContradiction (fun u => d2684 a0 a2 u a1)
  exact d222 a1 a2 v0

theorem c4594 (p : Nat → Prop)
    (d2833 : (p 72) → (¬ p 78) → (p 66) → (p 63) → False)
    (d403 : (p 63) → (p 66) → (p 78) → False)
    : (p 66) → (p 63) → (p 72) → False := by
  intro a0 a1 a2
  have v0 : p 78 := Classical.byContradiction (fun u => d2833 a2 u a0 a1)
  exact d403 a1 a0 v0

theorem c4596 (p : Nat → Prop)
    (d3600 : (p 15) → (p 12) → (¬ p 43) → (p 2) → False)
    (d18 : (p 2) → (p 12) → (p 43) → False)
    : (p 15) → (p 12) → (p 2) → False := by
  intro a0 a1 a2
  have v0 : p 43 := Classical.byContradiction (fun u => d3600 a0 a1 u a2)
  exact d18 a2 a1 v0

theorem c4600 (p : Nat → Prop)
    (d3730 : (p 24) → (p 27) → (¬ p 42) → (p 18) → False)
    (d582 : (p 18) → (p 27) → (p 42) → False)
    : (p 27) → (p 24) → (p 18) → False := by
  intro a0 a1 a2
  have v0 : p 42 := Classical.byContradiction (fun u => d3730 a1 a0 u a2)
  exact d582 a2 a0 v0

theorem c4601 (p : Nat → Prop)
    (d3763 : (p 53) → (p 39) → (¬ p 2) → (p 8) → False)
    (d386 : (p 2) → (p 8) → (p 39) → False)
    : (p 39) → (p 53) → (p 8) → False := by
  intro a0 a1 a2
  have v0 : p 2 := Classical.byContradiction (fun u => d3763 a1 a0 u a2)
  exact d386 v0 a2 a0

theorem c4609 (p : Nat → Prop)
    (d4148 : (p 67) → (p 20) → (¬ p 27) → (p 69) → False)
    (d257 : (p 20) → (p 27) → (p 69) → False)
    : (p 67) → (p 69) → (p 20) → False := by
  intro a0 a1 a2
  have v0 : p 27 := Classical.byContradiction (fun u => d4148 a0 a2 u a1)
  exact d257 a2 v0 a1

theorem c4611 (p : Nat → Prop)
    (d4190 : (p 70) → (p 4) → (¬ p 11) → (p 69) → False)
    (d22 : (p 4) → (p 11) → (p 69) → False)
    : (p 70) → (p 4) → (p 69) → False := by
  intro a0 a1 a2
  have v0 : p 11 := Classical.byContradiction (fun u => d4190 a0 a1 u a2)
  exact d22 a1 v0 a2

theorem c4612 (p : Nat → Prop)
    (d4202 : (p 31) → (p 26) → (p 20) → (¬ p 68) → False)
    (d359 : (p 20) → (p 26) → (p 68) → False)
    : (p 31) → (p 26) → (p 20) → False := by
  intro a0 a1 a2
  have v0 : p 68 := Classical.byContradiction (fun u => d4202 a0 a1 a2 u)
  exact d359 a2 a1 v0

theorem c4613 (p : Nat → Prop)
    (d4230 : (p 47) → (p 35) → (¬ p 69) → (p 42) → False)
    (d101 : (p 35) → (p 42) → (p 69) → False)
    : (p 47) → (p 35) → (p 42) → False := by
  intro a0 a1 a2
  have v0 : p 69 := Classical.byContradiction (fun u => d4230 a0 a1 u a2)
  exact d101 a1 a2 v0

theorem c4614 (p : Nat → Prop)
    (d4272 : (p 31) → (p 28) → (¬ p 43) → (p 18) → False)
    (d242 : (p 18) → (p 28) → (p 43) → False)
    : (p 31) → (p 28) → (p 18) → False := by
  intro a0 a1 a2
  have v0 : p 43 := Classical.byContradiction (fun u => d4272 a0 a1 u a2)
  exact d242 a2 a1 v0

theorem c4616 (p : Nat → Prop)
    (d4392 : (p 89) → (¬ p 9) → (p 6) → (p 90) → False)
    (d536 : (p 6) → (p 9) → (p 90) → False)
    : (p 6) → (p 90) → (p 89) → False := by
  intro a0 a1 a2
  have v0 : p 9 := Classical.byContradiction (fun u => d4392 a2 u a0 a1)
  exact d536 a0 v0 a1

theorem c4617 (p : Nat → Prop)
    (d4402 : (p 91) → (p 10) → (¬ p 5) → (p 80) → False)
    (d147 : (p 5) → (p 10) → (p 80) → False)
    : (p 91) → (p 10) → (p 80) → False := by
  intro a0 a1 a2
  have v0 : p 5 := Classical.byContradiction (fun u => d4402 a0 a1 u a2)
  exact d147 v0 a1 a2

theorem c4619 (p : Nat → Prop)
    (d669 : (¬ p 18) → (p 37) → (¬ p 2) → (¬ p 20) → (p 6) → False)
    (d452 : (p 2) → (p 6) → (p 37) → False)
    : (p 6) → (p 37) → (¬ p 20) → (¬ p 18) → False := by
  intro a0 a1 a2 a3
  have v0 : p 2 := Classical.byContradiction (fun u => d669 a3 a1 u a2 a0)
  exact d452 v0 a0 a1

theorem c4621 (p : Nat → Prop)
    (d1227 : (p 99) → (p 63) → (p 65) → (¬ p 77) → (p 78) → False)
    (d572 : (p 77) → (p 78) → (p 99) → False)
    : (p 78) → (p 99) → (p 63) → (p 65) → False := by
  intro a0 a1 a2 a3
  have v0 : p 77 := Classical.byContradiction (fun u => d1227 a1 a2 a3 u a0)
  exact d572 v0 a0 a1

theorem c4622 (p : Nat → Prop)
    (d701 : (p 77) → (¬ p 4) → (p 78) → (¬ p 7) → (p 65) → False)
    (d697 : (p 7) → (p 77) → (p 65) → False)
    : (p 77) → (p 78) → (p 65) → (¬ p 4) → False := by
  intro a0 a1 a2 a3
  have v0 : p 7 := Classical.byContradiction (fun u => d701 a0 a3 a1 u a2)
  exact d697 v0 a0 a2

theorem c4625 (p : Nat → Prop)
    (d1100 : (p 39) → (¬ p 53) → (p 34) → (¬ p 141) → (p 37) → False)
    (d351 : (p 34) → (p 39) → (p 53) → False)
    : (¬ p 141) → (p 37) → (p 39) → (p 34) → False := by
  intro a0 a1 a2 a3
  have v0 : p 53 := Classical.byContradiction (fun u => d1100 a2 u a3 a0 a1)
  exact d351 a3 a2 v0

theorem c4627 (p : Nat → Prop)
    (d1790 : (p 11) → (p 136) → (¬ p 14) → (¬ p 45) → (p 2) → False)
    (d4540 : (p 14) → (p 11) → (p 2) → False)
    : (¬ p 45) → (p 11) → (p 136) → (p 2) → False := by
  intro a0 a1 a2 a3
  have v0 : p 14 := Classical.byContradiction (fun u => d1790 a1 a2 u a0 a3)
  exact d4540 v0 a1 a3

theorem c4628 (p : Nat → Prop)
    (d2252 : (p 80) → (p 129) → (p 21) → (¬ p 78) → (¬ p 24) → False)
    (d4536 : (p 78) → (p 80) → (p 21) → False)
    : (p 129) → (¬ p 24) → (p 21) → (p 80) → False := by
  intro a0 a1 a2 a3
  have v0 : p 78 := Classical.byContradiction (fun u => d2252 a3 a0 a2 u a1)
  exact d4536 v0 a3 a2

theorem c4630 (p : Nat → Prop)
    (d1862 : (p 35) → (p 49) → (¬ p 64) → (p 42) → (p 88) → False)
    (d1308 : (p 64) → (p 49) → (p 35) → False)
    : (p 49) → (p 88) → (p 35) → (p 42) → False := by
  intro a0 a1 a2 a3
  have v0 : p 64 := Classical.byContradiction (fun u => d1862 a2 a0 u a3 a1)
  exact d1308 v0 a0 a2

theorem c4631 (p : Nat → Prop)
    (d2648 : (p 53) → (¬ p 21) → (¬ p 78) → (p 24) → (p 34) → False)
    (d1263 : (p 24) → (p 53) → (p 78) → False)
    : (p 53) → (p 24) → (¬ p 21) → (p 34) → False := by
  intro a0 a1 a2 a3
  have v0 : p 78 := Classical.byContradiction (fun u => d2648 a0 a2 u a1 a3)
  exact d1263 a1 a0 v0

theorem c4635 (p : Nat → Prop)
    (d2740 : (p 51) → (p 53) → (¬ p 50) → (p 76) → (¬ p 24) → False)
    (d122 : (p 50) → (p 51) → (p 76) → False)
    : (p 53) → (p 76) → (¬ p 24) → (p 51) → False := by
  intro a0 a1 a2 a3
  have v0 : p 50 := Classical.byContradiction (fun u => d2740 a3 a0 u a1 a2)
  exact d122 v0 a3 a1

theorem c4636 (p : Nat → Prop)
    (d3266 : (p 18) → (¬ p 39) → (p 24) → (p 63) → (p 34) → False)
    (d127 : (p 18) → (p 24) → (p 39) → False)
    : (p 63) → (p 34) → (p 18) → (p 24) → False := by
  intro a0 a1 a2 a3
  have v0 : p 39 := Classical.byContradiction (fun u => d3266 a2 u a3 a0 a1)
  exact d127 a2 a3 v0

theorem c4640 (p : Nat → Prop)
    (d4002 : (¬ p 20) → (p 6) → (p 37) → (¬ p 2) → (¬ p 64) → False)
    (d452 : (p 2) → (p 6) → (p 37) → False)
    : (¬ p 64) → (p 37) → (p 6) → (¬ p 20) → False := by
  intro a0 a1 a2 a3
  have v0 : p 2 := Classical.byContradiction (fun u => d4002 a3 a2 a1 u a0)
  exact d452 v0 a2 a1

theorem c4643 (p : Nat → Prop)
    (d4426 : (p 87) → (p 143) → (¬ p 76) → (¬ p 91) → (p 80) → False)
    (d4131 : (p 87) → (p 76) → (p 80) → False)
    : (p 87) → (¬ p 91) → (p 143) → (p 80) → False := by
  intro a0 a1 a2 a3
  have v0 : p 76 := Classical.byContradiction (fun u => d4426 a0 a2 u a1 a3)
  exact d4131 a0 v0 a3

theorem c4647 (p : Nat → Prop)
    (d1344 : (p 76) → (p 63) → (¬ p 50) → (¬ p 49) → (p 51) → (p 37) → False)
    (d122 : (p 50) → (p 51) → (p 76) → False)
    : (p 51) → (p 37) → (p 76) → (p 63) → (¬ p 49) → False := by
  intro a0 a1 a2 a3 a4
  have v0 : p 50 := Classical.byContradiction (fun u => d1344 a2 a3 u a4 a0 a1)
  exact d122 v0 a0 a2

theorem c4648 (p : Nat → Prop)
    (d783 : (¬ p 10) → (p 100) → (p 40) → (¬ p 38) → (¬ p 9) → (p 7) → False)
    (d324 : (p 7) → (p 9) → (p 100) → False)
    : (p 100) → (p 40) → (¬ p 10) → (¬ p 38) → (p 7) → False := by
  intro a0 a1 a2 a3 a4
  have v0 : p 9 := Classical.byContradiction (fun u => d783 a2 a0 a1 a3 u a4)
  exact d324 a4 v0 a0

theorem c4650 (p : Nat → Prop)
    (d744 : (p 97) → (¬ p 89) → (p 88) → (¬ p 15) → (p 8) → (¬ p 99) → False)
    (d652 : (p 97) → (p 88) → (p 89) → False)
    : (p 97) → (p 88) → (p 8) → (¬ p 15) → (¬ p 99) → False := by
  intro a0 a1 a2 a3 a4
  have v0 : p 89 := Classical.byContradiction (fun u => d744 a0 u a1 a3 a2 a4)
  exact d652 a0 a1 v0

theorem c4651 (p : Nat → Prop)
    (d1200 : (p 63) → (p 77) → (¬ p 70) → (p 88) → (¬ p 76) → (p 87) → False)
    (d45 : (p 76) → (p 77) → (p 88) → False)
    : (p 77) → (p 63) → (p 88) → (p 87) → (¬ p 70) → False := by
  intro a0 a1 a2 a3 a4
  have v0 : p 76 := Classical.byContradiction (fun u => d1200 a1 a0 a4 a2 u a3)
  exact d45 v0 a0 a2

theorem c4652 (p : Nat → Prop)
    (d735 : (p 53) → (p 18) → (¬ p 2) → (¬ p 21) → (p 24) → (p 8) → False)
    (d1425 : (p 18) → (p 24) → (p 21) → False)
    : (p 53) → (p 24) → (p 18) → (¬ p 2) → (p 8) → False := by
  intro a0 a1 a2 a3 a4
  have v0 : p 21 := Classical.byContradiction (fun u => d735 a0 a2 a3 u a1 a4)
  exact d1425 a2 a1 v0

theorem c4653 (p : Nat → Prop)
    (d937 : (p 80) → (p 41) → (¬ p 26) → (p 18) → (¬ p 93) → (p 34) → False)
    (d387 : (p 18) → (p 26) → (p 41) → False)
    : (p 34) → (p 41) → (p 18) → (p 80) → (¬ p 93) → False := by
  intro a0 a1 a2 a3 a4
  have v0 : p 26 := Classical.byContradiction (fun u => d937 a3 a1 u a2 a4 a0)
  exact d387 a2 v0 a1

theorem c4658 (p : Nat → Prop)
    (d1642 : (p 79) → (p 45) → (p 63) → (¬ p 9) → (p 5) → (p 2) → False)
    (d503 : (p 5) → (p 9) → (p 79) → False)
    : (p 45) → (p 63) → (p 79) → (p 5) → (p 2) → False := by
  intro a0 a1 a2 a3 a4
  have v0 : p 9 := Classical.byContradiction (fun u => d1642 a2 a0 a1 u a3 a4)
  exact d503 a3 v0 a2

theorem c4660 (p : Nat → Prop)
    (d1566 : (p 99) → (¬ p 5) → (p 3) → (¬ p 89) → (p 88) → (¬ p 6) → False)
    (d95 : (p 88) → (p 89) → (p 99) → False)
    : (p 88) → (¬ p 6) → (¬ p 5) → (p 3) → (p 99) → False := by
  intro a0 a1 a2 a3 a4
  have v0 : p 89 := Classical.byContradiction (fun u => d1566 a4 a2 a3 u a0 a1)
  exact d95 a0 v0 a4

theorem c4662 (p : Nat → Prop)
    (d2269 : (p 78) → (p 5) → (¬ p 23) → (p 80) → (¬ p 24) → (¬ p 7) → False)
    (d978 : (p 78) → (¬ p 23) → (p 5) → (p 24) → False)
    : (¬ p 23) → (p 78) → (p 5) → (p 80) → (¬ p 7) → False := by
  intro a0 a1 a2 a3 a4
  have v0 : p 24 := Classical.byContradiction (fun u => d2269 a1 a2 a0 a3 u a4)
  exact d978 a1 a0 a2 v0

theorem c4663 (p : Nat → Prop)
    (d1730 : (p 5) → (¬ p 39) → (¬ p 54) → (¬ p 9) → (p 3) → (p 2) → False)
    (d703 : (p 3) → (p 9) → (p 5) → False)
    : (p 5) → (¬ p 54) → (¬ p 39) → (p 3) → (p 2) → False := by
  intro a0 a1 a2 a3 a4
  have v0 : p 9 := Classical.byContradiction (fun u => d1730 a0 a2 a1 u a3 a4)
  exact d703 a3 v0 a0

theorem c4668 (p : Nat → Prop)
    (d2963 : (¬ p 72) → (¬ p 43) → (p 45) → (p 25) → (p 20) → (¬ p 67) → False)
    (d142 : (p 20) → (p 25) → (p 67) → False)
    : (p 45) → (¬ p 43) → (p 25) → (¬ p 72) → (p 20) → False := by
  intro a0 a1 a2 a3 a4
  have v0 : p 67 := Classical.byContradiction (fun u => d2963 a3 a1 a0 a2 a4 u)
  exact d142 a4 a2 v0

theorem c4672 (p : Nat → Prop)
    (d3581 : (p 18) → (p 63) → (¬ p 51) → (p 22) → (¬ p 39) → (p 24) → False)
    (d127 : (p 18) → (p 24) → (p 39) → False)
    : (p 22) → (¬ p 51) → (p 63) → (p 18) → (p 24) → False := by
  intro a0 a1 a2 a3 a4
  have v0 : p 39 := Classical.byContradiction (fun u => d3581 a3 a2 a1 a0 u a4)
  exact d127 a3 a4 v0

theorem c4674 (p : Nat → Prop)
    (d4015 : (¬ p 8) → (¬ p 7) → (¬ p 5) → (p 2) → (p 24) → (p 3) → False)
    (d4011 : (p 2) → (¬ p 7) → (p 5) → (p 24) → (p 3) → False)
    : (¬ p 8) → (p 24) → (p 3) → (p 2) → (¬ p 7) → False := by
  intro a0 a1 a2 a3 a4
  have v0 : p 5 := Classical.byContradiction (fun u => d4015 a0 a4 u a3 a1 a2)
  exact d4011 a3 a4 v0 a1 a2

theorem c4675 (p : Nat → Prop)
    (d4101 : (p 39) → (p 35) → (¬ p 4) → (p 2) → (p 78) → (p 89) → False)
    (d208 : (p 2) → (p 4) → (p 35) → False)
    : (p 78) → (p 35) → (p 2) → (p 39) → (p 89) → False := by
  intro a0 a1 a2 a3 a4
  have v0 : p 4 := Classical.byContradiction (fun u => d4101 a3 a1 u a2 a0 a4)
  exact d208 a2 v0 a1

theorem c4680 (p : Nat → Prop)
    (d733 : (¬ p 23) → (¬ p 7) → (¬ p 77) → (p 78) → (¬ p 89) → (¬ p 6) → (p 76) → False)
    (d25 : (p 76) → (p 78) → (p 89) → False)
    : (¬ p 23) → (¬ p 77) → (¬ p 7) → (p 76) → (¬ p 6) → (p 78) → False := by
  intro a0 a1 a2 a3 a4 a5
  have v0 : p 89 := Classical.byContradiction (fun u => d733 a0 a2 a1 a5 u a4 a3)
  exact d25 a3 a5 v0

theorem c4681 (p : Nat → Prop)
    (d1252 : (p 65) → (p 99) → (p 35) → (¬ p 80) → (¬ p 38) → (¬ p 77) → (p 78) → False)
    (d572 : (p 77) → (p 78) → (p 99) → False)
    : (p 99) → (p 78) → (p 65) → (¬ p 80) → (¬ p 38) → (p 35) → False := by
  intro a0 a1 a2 a3 a4 a5
  have v0 : p 77 := Classical.byContradiction (fun u => d1252 a2 a0 a5 a3 a4 u a1)
  exact d572 v0 a1 a0

theorem c4686 (p : Nat → Prop)
    (d965 : (¬ p 39) → (p 34) → (p 51) → (¬ p 22) → (p 27) → (p 41) → (p 18) → False)
    (d966 : (p 39) → (p 41) → (p 18) → False)
    : (p 27) → (p 34) → (p 41) → (p 18) → (p 51) → (¬ p 22) → False := by
  intro a0 a1 a2 a3 a4 a5
  have v0 : p 39 := Classical.byContradiction (fun u => d965 u a1 a4 a5 a0 a2 a3)
  exact d966 v0 a2 a3

theorem c4688 (p : Nat → Prop)
    (d1537 : (p 4) → (p 5) → (p 99) → (¬ p 89) → (¬ p 23) → (p 88) → (p 3) → False)
    (d4074 : (p 99) → (p 23) → (p 88) → False)
    : (p 99) → (¬ p 89) → (p 4) → (p 3) → (p 5) → (p 88) → False := by
  intro a0 a1 a2 a3 a4 a5
  have v0 : p 23 := Classical.byContradiction (fun u => d1537 a2 a4 a0 a1 u a5 a3)
  exact d4074 a0 v0 a5

theorem c4696 (p : Nat → Prop)
    (d2990 : (p 5) → (p 80) → (¬ p 114) → (p 7) → (¬ p 24) → (¬ p 23) → (p 14) → False)
    (d3000 : (p 5) → (p 24) → (¬ p 114) → (¬ p 23) → (p 14) → False)
    : (¬ p 23) → (p 7) → (p 5) → (p 80) → (¬ p 114) → (p 14) → False := by
  intro a0 a1 a2 a3 a4 a5
  have v0 : p 24 := Classical.byContradiction (fun u => d2990 a2 a3 a4 a1 u a0 a5)
  exact d3000 a2 v0 a4 a0 a5

theorem c4699 (p : Nat → Prop)
    (d4478 : (¬ p 7) → (¬ p 69) → (p 51) → (¬ p 6) → (p 3) → (p 4) → (¬ p 5) → False)
    (d38 : (p 3) → (p 6) → (p 51) → False)
    : (p 4) → (¬ p 69) → (p 51) → (p 3) → (¬ p 7) → (¬ p 5) → False := by
  intro a0 a1 a2 a3 a4 a5
  have v0 : p 6 := Classical.byContradiction (fun u => d4478 a4 a1 a2 u a3 a0 a5)
  exact d38 a3 v0 a2

theorem c4702 (p : Nat → Prop)
    (d819 : (p 22) → (p 90) → (p 12) → (¬ p 65) → (¬ p 25) → (p 21) → (p 64) → (¬ p 6) → False)
    (d26 : (p 22) → (p 25) → (p 90) → False)
    : (p 64) → (p 22) → (¬ p 6) → (p 21) → (p 12) → (p 90) → (¬ p 65) → False := by
  intro a0 a1 a2 a3 a4 a5 a6
  have v0 : p 25 := Classical.byContradiction (fun u => d819 a1 a5 a4 a6 u a3 a0 a2)
  exact d26 a1 v0 a5

theorem c4703 (p : Nat → Prop)
    (d1506 : (p 69) → (¬ p 65) → (¬ p 76) → (p 63) → (¬ p 12) → (p 4) → (p 5) → (p 88) → False)
    (d3427 : (p 12) → (¬ p 65) → (¬ p 76) → (p 5) → (p 88) → (p 4) → False)
    : (p 63) → (¬ p 65) → (p 88) → (p 5) → (¬ p 76) → (p 69) → (p 4) → False := by
  intro a0 a1 a2 a3 a4 a5 a6
  have v0 : p 12 := Classical.byContradiction (fun u => d1506 a5 a1 a4 a0 u a6 a3 a2)
  exact d3427 v0 a1 a4 a3 a2 a6

theorem c4705 (p : Nat → Prop)
    (d3406 : (¬ p 4) → (¬ p 49) → (¬ p 20) → (¬ p 54) → (p 10) → (p 63) → (¬ p 7) → (p 9) → False)
    (d3306 : (¬ p 4) → (¬ p 49) → (¬ p 63) → (p 9) → False)
    : (¬ p 54) → (p 10) → (¬ p 49) → (¬ p 7) → (p 9) → (¬ p 20) → (¬ p 4) → False := by
  intro a0 a1 a2 a3 a4 a5 a6
  have v0 : ¬ p 63 := (fun u => d3406 a6 a2 a5 a0 a1 u a3 a4)
  exact d3306 a6 a2 v0 a4

theorem c4714 (p : Nat → Prop)
    (d3694 : (p 45) → (¬ p 67) → (p 4) → (¬ p 28) → (¬ p 13) → (p 25) → (¬ p 12) → (p 18) → False)
    (d3714 : (p 28) → (p 25) → (p 18) → False)
    : (¬ p 12) → (p 45) → (p 4) → (p 25) → (p 18) → (¬ p 67) → (¬ p 13) → False := by
  intro a0 a1 a2 a3 a4 a5 a6
  have v0 : p 28 := Classical.byContradiction (fun u => d3694 a1 a5 a2 u a6 a3 a0 a4)
  exact d3714 v0 a3 a4

theorem c4721 (p : Nat → Prop)
    (d1216 : (p 34) → (p 49) → (¬ p 38) → (¬ p 77) → (¬ p 79) → (p 5) → (p 78) → (p 89) → (¬ p 18) → False)
    (d4557 : (p 77) → (p 78) → (p 5) → False)
    : (p 78) → (p 5) → (¬ p 18) → (¬ p 79) → (p 49) → (p 89) → (p 34) → (¬ p 38) → False := by
  intro a0 a1 a2 a3 a4 a5 a6 a7
  have v0 : p 77 := Classical.byContradiction (fun u => d1216 a6 a4 a7 u a3 a1 a0 a5 a2)
  exact d4557 v0 a0 a1

theorem c4730 (p : Nat → Prop)
    (d1948 : (p 100) → (¬ p 34) → (p 77) → (¬ p 38) → (¬ p 9) → (p 7) → (¬ p 37) → (¬ p 50) → (¬ p 10) → False)
    (d324 : (p 7) → (p 9) → (p 100) → False)
    : (¬ p 38) → (p 77) → (¬ p 37) → (p 7) → (p 100) → (¬ p 34) → (¬ p 50) → (¬ p 10) → False := by
  intro a0 a1 a2 a3 a4 a5 a6 a7
  have v0 : p 9 := Classical.byContradiction (fun u => d1948 a4 a5 a1 a0 u a3 a2 a6 a7)
  exact d324 a3 v0 a4

theorem c4743 (p : Nat → Prop)
    (d4462 : (p 78) → (¬ p 21) → (¬ p 93) → (p 99) → (¬ p 24) → (¬ p 56) → (p 27) → (¬ p 22) → (p 80) → False)
    (d4536 : (p 78) → (p 80) → (p 21) → False)
    : (p 78) → (¬ p 93) → (p 99) → (¬ p 24) → (¬ p 56) → (p 27) → (¬ p 22) → (p 80) → False := by
  intro a0 a1 a2 a3 a4 a5 a6 a7
  have v0 : p 21 := Classical.byContradiction (fun u => d4462 a0 u a1 a2 a3 a4 a5 a6 a7)
  exact d4536 a0 a7 v0

theorem c4782 (p : Nat → Prop)
    (d4388 : (p 8) → (p 6) → (p 34) → (p 20) → (¬ p 37) → (p 2) → (p 4) → (p 10) → (¬ p 42) → (p 29) → (¬ p 41) → False)
    (d452 : (p 2) → (p 6) → (p 37) → False)
    : (p 8) → (¬ p 42) → (p 34) → (p 20) → (p 2) → (p 4) → (p 10) → (p 6) → (p 29) → (¬ p 41) → False := by
  intro a0 a1 a2 a3 a4 a5 a6 a7 a8 a9
  have v0 : p 37 := Classical.byContradiction (fun u => d4388 a0 a7 a2 a3 u a4 a5 a6 a1 a8 a9)
  exact d452 a4 a7 v0

theorem c4886 (p : Nat → Prop)
    (d51 : (p 3) → (p 10) → (p 55) → False)
    (d281 : (p 4) → (p 10) → (p 68) → False)
    (d74 : (¬ p 63) → (¬ p 68) → (¬ p 80) → False)
    (d4617 : (p 91) → (p 10) → (p 80) → False)
    (d444 : (¬ p 51) → (¬ p 55) → (¬ p 91) → False)
    : (¬ p 51) → (¬ p 63) → (p 10) → (p 4) → (p 3) → False := by
  intro a0 a1 a2 a3 a4
  have v0 : ¬ p 55 := (fun u => d51 a4 a2 u)
  have v1 : ¬ p 68 := (fun u => d281 a3 a2 u)
  have v2 : p 80 := Classical.byContradiction (fun u => d74 a1 v1 u)
  have v3 : ¬ p 91 := (fun u => d4617 u a2 v2)
  exact d444 a0 v0 v3

theorem c4897 (p : Nat → Prop)
    (d287 : (p 58) → (p 61) → (p 146) → False)
    (d141 : (¬ p 57) → (¬ p 61) → (¬ p 142) → False)
    : (¬ p 142) → (¬ p 57) → (p 146) → (p 58) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 61 := (fun u => d287 a3 u a2)
  exact d141 a1 v0 a0

theorem c4898 (p : Nat → Prop)
    (d456 : (p 56) → (p 61) → (p 137) → False)
    (d141 : (¬ p 57) → (¬ p 61) → (¬ p 142) → False)
    : (¬ p 142) → (¬ p 57) → (p 137) → (p 56) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 61 := (fun u => d456 a3 u a2)
  exact d141 a1 v0 a0

theorem c4899 (p : Nat → Prop)
    (d342 : (p 54) → (p 61) → (p 124) → False)
    (d141 : (¬ p 57) → (¬ p 61) → (¬ p 142) → False)
    : (¬ p 142) → (¬ p 57) → (p 124) → (p 54) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 61 := (fun u => d342 a3 u a2)
  exact d141 a1 v0 a0

theorem c4900 (p : Nat → Prop)
    (d188 : (p 49) → (p 61) → (p 74) → False)
    (d141 : (¬ p 57) → (¬ p 61) → (¬ p 142) → False)
    : (¬ p 142) → (¬ p 57) → (p 49) → (p 74) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 61 := (fun u => d188 a2 u a3)
  exact d141 a1 v0 a0

theorem c4901 (p : Nat → Prop)
    (d352 : (p 50) → (p 61) → (p 86) → False)
    (d141 : (¬ p 57) → (¬ p 61) → (¬ p 142) → False)
    : (¬ p 142) → (¬ p 57) → (p 86) → (p 50) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 61 := (fun u => d352 a3 u a2)
  exact d141 a1 v0 a0

theorem c4902 (p : Nat → Prop)
    (d535 : (p 50) → (p 62) → (p 87) → False)
    (d192 : (¬ p 58) → (¬ p 62) → (¬ p 147) → False)
    : (¬ p 147) → (¬ p 58) → (p 50) → (p 87) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 62 := (fun u => d535 a2 u a3)
  exact d192 a1 v0 a0

theorem c4903 (p : Nat → Prop)
    (d184 : (p 57) → (p 62) → (p 143) → False)
    (d192 : (¬ p 58) → (¬ p 62) → (¬ p 147) → False)
    : (¬ p 147) → (¬ p 58) → (p 57) → (p 143) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 62 := (fun u => d184 a2 u a3)
  exact d192 a1 v0 a0

theorem c4904 (p : Nat → Prop)
    (d4 : (p 55) → (p 62) → (p 132) → False)
    (d192 : (¬ p 58) → (¬ p 62) → (¬ p 147) → False)
    : (¬ p 147) → (¬ p 58) → (p 55) → (p 132) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 62 := (fun u => d4 a2 u a3)
  exact d192 a1 v0 a0

theorem c4905 (p : Nat → Prop)
    (d313 : (p 51) → (p 62) → (p 98) → False)
    (d192 : (¬ p 58) → (¬ p 62) → (¬ p 147) → False)
    : (¬ p 147) → (¬ p 58) → (p 98) → (p 51) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 62 := (fun u => d313 a3 u a2)
  exact d192 a1 v0 a0

theorem c4906 (p : Nat → Prop)
    (d529 : (p 56) → (p 62) → (p 138) → False)
    (d192 : (¬ p 58) → (¬ p 62) → (¬ p 147) → False)
    : (¬ p 147) → (¬ p 58) → (p 56) → (p 138) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 62 := (fun u => d529 a2 u a3)
  exact d192 a1 v0 a0

theorem c4907 (p : Nat → Prop)
    (d461 : (p 60) → (p 62) → (p 152) → False)
    (d192 : (¬ p 58) → (¬ p 62) → (¬ p 147) → False)
    : (¬ p 147) → (¬ p 58) → (p 152) → (p 60) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 62 := (fun u => d461 a3 u a2)
  exact d192 a1 v0 a0

theorem c4908 (p : Nat → Prop)
    (d599 : (p 52) → (p 62) → (p 108) → False)
    (d192 : (¬ p 58) → (¬ p 62) → (¬ p 147) → False)
    : (¬ p 147) → (¬ p 58) → (p 52) → (p 108) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 62 := (fun u => d599 a2 u a3)
  exact d192 a1 v0 a0

theorem c4909 (p : Nat → Prop)
    (d445 : (p 5) → (p 13) → (p 83) → False)
    (d15 : (¬ p 77) → (¬ p 83) → (¬ p 104) → False)
    : (¬ p 104) → (¬ p 77) → (p 5) → (p 13) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 83 := (fun u => d445 a2 a3 u)
  exact d15 a1 v0 a0

theorem c4910 (p : Nat → Prop)
    (d404 : (p 78) → (p 83) → (p 113) → False)
    (d15 : (¬ p 77) → (¬ p 83) → (¬ p 104) → False)
    : (¬ p 104) → (¬ p 77) → (p 78) → (p 113) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 83 := (fun u => d404 a2 u a3)
  exact d15 a1 v0 a0

theorem c4911 (p : Nat → Prop)
    (d226 : (p 79) → (p 83) → (p 121) → False)
    (d15 : (¬ p 77) → (¬ p 83) → (¬ p 104) → False)
    : (¬ p 104) → (¬ p 77) → (p 121) → (p 79) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 83 := (fun u => d226 a3 u a2)
  exact d15 a1 v0 a0

theorem c4912 (p : Nat → Prop)
    (d178 : (p 83) → (p 87) → (p 147) → False)
    (d15 : (¬ p 77) → (¬ p 83) → (¬ p 104) → False)
    : (¬ p 104) → (¬ p 77) → (p 147) → (p 87) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 83 := (fun u => d178 u a3 a2)
  exact d15 a1 v0 a0

theorem c4913 (p : Nat → Prop)
    (d160 : (p 63) → (p 71) → (p 83) → False)
    (d15 : (¬ p 77) → (¬ p 83) → (¬ p 104) → False)
    : (¬ p 104) → (¬ p 77) → (p 63) → (p 71) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 83 := (fun u => d160 a2 a3 u)
  exact d15 a1 v0 a0

theorem c4914 (p : Nat → Prop)
    (d450 : (p 21) → (p 29) → (p 83) → False)
    (d15 : (¬ p 77) → (¬ p 83) → (¬ p 104) → False)
    : (¬ p 104) → (¬ p 77) → (p 21) → (p 29) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 83 := (fun u => d450 a2 a3 u)
  exact d15 a1 v0 a0

theorem c4915 (p : Nat → Prop)
    (d210 : (p 36) → (p 44) → (p 83) → False)
    (d15 : (¬ p 77) → (¬ p 83) → (¬ p 104) → False)
    : (¬ p 104) → (¬ p 77) → (p 44) → (p 36) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 83 := (fun u => d210 a3 a2 u)
  exact d15 a1 v0 a0

theorem c4916 (p : Nat → Prop)
    (d94 : (p 118) → (p 121) → (p 128) → False)
    (d575 : (¬ p 54) → (¬ p 58) → (¬ p 121) → False)
    : (¬ p 54) → (¬ p 58) → (p 128) → (p 118) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 121 := (fun u => d94 a3 u a2)
  exact d575 a0 a1 v0

theorem c4917 (p : Nat → Prop)
    (d402 : (p 100) → (p 104) → (p 121) → False)
    (d575 : (¬ p 54) → (¬ p 58) → (¬ p 121) → False)
    : (¬ p 54) → (¬ p 58) → (p 104) → (p 100) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 121 := (fun u => d402 a3 a2 u)
  exact d575 a0 a1 v0

theorem c4918 (p : Nat → Prop)
    (d262 : (p 25) → (p 29) → (p 121) → False)
    (d575 : (¬ p 54) → (¬ p 58) → (¬ p 121) → False)
    : (¬ p 54) → (¬ p 58) → (p 25) → (p 29) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 121 := (fun u => d262 a2 a3 u)
  exact d575 a0 a1 v0

theorem c4919 (p : Nat → Prop)
    (d580 : (p 121) → (p 125) → (p 147) → False)
    (d575 : (¬ p 54) → (¬ p 58) → (¬ p 121) → False)
    : (¬ p 54) → (¬ p 58) → (p 147) → (p 125) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 121 := (fun u => d580 u a3 a2)
  exact d575 a0 a1 v0

theorem c4920 (p : Nat → Prop)
    (d443 : (p 119) → (p 121) → (p 134) → False)
    (d575 : (¬ p 54) → (¬ p 58) → (¬ p 121) → False)
    : (¬ p 54) → (¬ p 58) → (p 119) → (p 134) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 121 := (fun u => d443 a2 u a3)
  exact d575 a0 a1 v0

theorem c4921 (p : Nat → Prop)
    (d513 : (p 40) → (p 44) → (p 121) → False)
    (d575 : (¬ p 54) → (¬ p 58) → (¬ p 121) → False)
    : (¬ p 54) → (¬ p 58) → (p 44) → (p 40) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 121 := (fun u => d513 a3 a2 u)
  exact d575 a0 a1 v0

theorem c4922 (p : Nat → Prop)
    (d4911 : (¬ p 104) → (¬ p 77) → (p 121) → (p 79) → False)
    (d575 : (¬ p 54) → (¬ p 58) → (¬ p 121) → False)
    : (¬ p 54) → (¬ p 58) → (¬ p 104) → (¬ p 77) → (p 79) → False := by
  intro a0 a1 a2 a3 a4
  have v0 : ¬ p 121 := (fun u => d4911 a2 a3 u a4)
  exact d575 a0 a1 v0

theorem c4923 (p : Nat → Prop)
    (d189 : (p 128) → (p 130) → (p 145) → False)
    (d134 : (¬ p 29) → (¬ p 31) → (¬ p 145) → False)
    : (¬ p 31) → (¬ p 29) → (p 130) → (p 128) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 145 := (fun u => d189 a3 a2 u)
  exact d134 a1 a0 v0

theorem c4925 (p : Nat → Prop)
    (d24 : (p 13) → (p 15) → (p 145) → False)
    (d134 : (¬ p 29) → (¬ p 31) → (¬ p 145) → False)
    : (¬ p 31) → (¬ p 29) → (p 13) → (p 15) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 145 := (fun u => d24 a2 a3 u)
  exact d134 a1 a0 v0

theorem c4926 (p : Nat → Prop)
    (d598 : (p 145) → (p 146) → (p 151) → False)
    (d134 : (¬ p 29) → (¬ p 31) → (¬ p 145) → False)
    : (¬ p 31) → (¬ p 29) → (p 151) → (p 146) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 145 := (fun u => d598 u a3 a2)
  exact d134 a1 a0 v0

theorem c4927 (p : Nat → Prop)
    (d29 : (p 139) → (p 141) → (p 145) → False)
    (d134 : (¬ p 29) → (¬ p 31) → (¬ p 145) → False)
    : (¬ p 31) → (¬ p 29) → (p 141) → (p 139) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 145 := (fun u => d29 a3 a2 u)
  exact d134 a1 a0 v0

theorem c4928 (p : Nat → Prop)
    (d577 : (p 71) → (p 73) → (p 145) → False)
    (d134 : (¬ p 29) → (¬ p 31) → (¬ p 145) → False)
    : (¬ p 31) → (¬ p 29) → (p 73) → (p 71) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 145 := (fun u => d577 a3 a2 u)
  exact d134 a1 a0 v0

theorem c4930 (p : Nat → Prop)
    (d426 : (p 86) → (p 87) → (p 153) → False)
    (d99 : (¬ p 16) → (¬ p 17) → (¬ p 153) → False)
    : (¬ p 17) → (¬ p 16) → (p 86) → (p 87) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 153 := (fun u => d426 a2 a3 u)
  exact d99 a1 a0 v0

theorem c4931 (p : Nat → Prop)
    (d553 : (p 131) → (p 132) → (p 153) → False)
    (d99 : (¬ p 16) → (¬ p 17) → (¬ p 153) → False)
    : (¬ p 17) → (¬ p 16) → (p 131) → (p 132) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 153 := (fun u => d553 a2 a3 u)
  exact d99 a1 a0 v0

theorem c4932 (p : Nat → Prop)
    (d500 : (p 137) → (p 138) → (p 153) → False)
    (d99 : (¬ p 16) → (¬ p 17) → (¬ p 153) → False)
    : (¬ p 17) → (¬ p 16) → (p 137) → (p 138) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 153 := (fun u => d500 a2 a3 u)
  exact d99 a1 a0 v0

theorem c4933 (p : Nat → Prop)
    (d33 : (p 151) → (p 152) → (p 153) → False)
    (d99 : (¬ p 16) → (¬ p 17) → (¬ p 153) → False)
    : (¬ p 17) → (¬ p 16) → (p 152) → (p 151) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 153 := (fun u => d33 a3 a2 u)
  exact d99 a1 a0 v0

theorem c4934 (p : Nat → Prop)
    (d177 : (p 149) → (p 150) → (p 153) → False)
    (d99 : (¬ p 16) → (¬ p 17) → (¬ p 153) → False)
    : (¬ p 17) → (¬ p 16) → (p 149) → (p 150) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 153 := (fun u => d177 a2 a3 u)
  exact d99 a1 a0 v0

theorem c4935 (p : Nat → Prop)
    (d50 : (p 107) → (p 108) → (p 153) → False)
    (d99 : (¬ p 16) → (¬ p 17) → (¬ p 153) → False)
    : (¬ p 17) → (¬ p 16) → (p 107) → (p 108) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 153 := (fun u => d50 a2 a3 u)
  exact d99 a1 a0 v0

theorem c4936 (p : Nat → Prop)
    (d165 : (p 124) → (p 125) → (p 153) → False)
    (d99 : (¬ p 16) → (¬ p 17) → (¬ p 153) → False)
    : (¬ p 17) → (¬ p 16) → (p 124) → (p 125) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 153 := (fun u => d165 a2 a3 u)
  exact d99 a1 a0 v0

theorem c4937 (p : Nat → Prop)
    (d364 : (p 19) → (p 23) → (p 52) → False)
    (d381 : (¬ p 19) → (¬ p 21) → (¬ p 50) → False)
    : (¬ p 21) → (¬ p 50) → (p 52) → (p 23) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 19 := (fun u => d364 u a3 a2)
  exact d381 v0 a0 a1

theorem c4938 (p : Nat → Prop)
    (d468 : (p 19) → (p 28) → (p 57) → False)
    (d381 : (¬ p 19) → (¬ p 21) → (¬ p 50) → False)
    : (¬ p 21) → (¬ p 50) → (p 57) → (p 28) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 19 := (fun u => d468 u a3 a2)
  exact d381 v0 a0 a1

theorem c4939 (p : Nat → Prop)
    (d438 : (p 19) → (p 22) → (p 51) → False)
    (d381 : (¬ p 19) → (¬ p 21) → (¬ p 50) → False)
    : (¬ p 21) → (¬ p 50) → (p 22) → (p 51) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 19 := (fun u => d438 u a2 a3)
  exact d381 v0 a0 a1

theorem c4940 (p : Nat → Prop)
    (d375 : (p 18) → (p 19) → (p 34) → False)
    (d381 : (¬ p 19) → (¬ p 21) → (¬ p 50) → False)
    : (¬ p 21) → (¬ p 50) → (p 34) → (p 18) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 19 := (fun u => d375 a3 u a2)
  exact d381 v0 a0 a1

theorem c4941 (p : Nat → Prop)
    (d473 : (p 1) → (p 3) → (p 19) → False)
    (d381 : (¬ p 19) → (¬ p 21) → (¬ p 50) → False)
    : (¬ p 21) → (¬ p 50) → (p 1) → (p 3) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 19 := (fun u => d473 a2 a3 u)
  exact d381 v0 a0 a1

theorem c4942 (p : Nat → Prop)
    (d102 : (p 19) → (p 24) → (p 53) → False)
    (d381 : (¬ p 19) → (¬ p 21) → (¬ p 50) → False)
    : (¬ p 21) → (¬ p 50) → (p 53) → (p 24) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 19 := (fun u => d102 u a3 a2)
  exact d381 v0 a0 a1

theorem c4943 (p : Nat → Prop)
    (d453 : (p 19) → (p 29) → (p 58) → False)
    (d381 : (¬ p 19) → (¬ p 21) → (¬ p 50) → False)
    : (¬ p 21) → (¬ p 50) → (p 58) → (p 29) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 19 := (fun u => d453 u a3 a2)
  exact d381 v0 a0 a1

theorem c4944 (p : Nat → Prop)
    (d600 : (p 19) → (p 30) → (p 59) → False)
    (d381 : (¬ p 19) → (¬ p 21) → (¬ p 50) → False)
    : (¬ p 21) → (¬ p 50) → (p 30) → (p 59) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 19 := (fun u => d600 u a2 a3)
  exact d381 v0 a0 a1

theorem c4945 (p : Nat → Prop)
    (d290 : (p 52) → (p 53) → (p 99) → False)
    (d366 : (¬ p 52) → (¬ p 56) → (¬ p 102) → False)
    : (¬ p 102) → (¬ p 56) → (p 99) → (p 53) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 52 := (fun u => d290 u a3 a2)
  exact d366 v0 a1 a0

theorem c4946 (p : Nat → Prop)
    (d556 : (p 51) → (p 52) → (p 88) → False)
    (d366 : (¬ p 52) → (¬ p 56) → (¬ p 102) → False)
    : (¬ p 102) → (¬ p 56) → (p 51) → (p 88) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 52 := (fun u => d556 a2 u a3)
  exact d366 v0 a1 a0

theorem c4947 (p : Nat → Prop)
    (d567 : (p 52) → (p 55) → (p 101) → False)
    (d366 : (¬ p 52) → (¬ p 56) → (¬ p 102) → False)
    : (¬ p 102) → (¬ p 56) → (p 55) → (p 101) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 52 := (fun u => d567 u a2 a3)
  exact d366 v0 a1 a0

theorem c4948 (p : Nat → Prop)
    (d129 : (p 3) → (p 7) → (p 52) → False)
    (d366 : (¬ p 52) → (¬ p 56) → (¬ p 102) → False)
    : (¬ p 102) → (¬ p 56) → (p 7) → (p 3) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 52 := (fun u => d129 a3 a2 u)
  exact d366 v0 a1 a0

theorem c4949 (p : Nat → Prop)
    (d358 : (p 49) → (p 52) → (p 65) → False)
    (d366 : (¬ p 52) → (¬ p 56) → (¬ p 102) → False)
    : (¬ p 102) → (¬ p 56) → (p 65) → (p 49) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 52 := (fun u => d358 a3 u a2)
  exact d366 v0 a1 a0

theorem c4950 (p : Nat → Prop)
    (d278 : (p 34) → (p 38) → (p 52) → False)
    (d366 : (¬ p 52) → (¬ p 56) → (¬ p 102) → False)
    : (¬ p 102) → (¬ p 56) → (p 38) → (p 34) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 52 := (fun u => d278 a3 a2 u)
  exact d366 v0 a1 a0

theorem c4951 (p : Nat → Prop)
    (d4908 : (¬ p 147) → (¬ p 58) → (p 52) → (p 108) → False)
    (d366 : (¬ p 52) → (¬ p 56) → (¬ p 102) → False)
    : (¬ p 102) → (¬ p 56) → (¬ p 147) → (¬ p 58) → (p 108) → False := by
  intro a0 a1 a2 a3 a4
  have v0 : ¬ p 52 := (fun u => d4908 a2 a3 u a4)
  exact d366 v0 a1 a0

theorem c4952 (p : Nat → Prop)
    (d4937 : (¬ p 21) → (¬ p 50) → (p 52) → (p 23) → False)
    (d366 : (¬ p 52) → (¬ p 56) → (¬ p 102) → False)
    : (¬ p 102) → (¬ p 56) → (¬ p 21) → (¬ p 50) → (p 23) → False := by
  intro a0 a1 a2 a3 a4
  have v0 : ¬ p 52 := (fun u => d4937 a2 a3 u a4)
  exact d366 v0 a1 a0

theorem c4953 (p : Nat → Prop)
    (d532 : (p 54) → (p 59) → (p 122) → False)
    (d560 : (¬ p 55) → (¬ p 59) → (¬ p 129) → False)
    : (¬ p 129) → (¬ p 55) → (p 122) → (p 54) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 59 := (fun u => d532 a3 u a2)
  exact d560 a1 v0 a0

theorem c4954 (p : Nat → Prop)
    (d307 : (p 53) → (p 59) → (p 114) → False)
    (d560 : (¬ p 55) → (¬ p 59) → (¬ p 129) → False)
    : (¬ p 129) → (¬ p 55) → (p 114) → (p 53) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 59 := (fun u => d307 a3 u a2)
  exact d560 a1 v0 a0

theorem c4955 (p : Nat → Prop)
    (d602 : (p 56) → (p 59) → (p 135) → False)
    (d560 : (¬ p 55) → (¬ p 59) → (¬ p 129) → False)
    : (¬ p 129) → (¬ p 55) → (p 56) → (p 135) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 59 := (fun u => d602 a2 u a3)
  exact d560 a1 v0 a0

theorem c4956 (p : Nat → Prop)
    (d408 : (p 34) → (p 45) → (p 59) → False)
    (d560 : (¬ p 55) → (¬ p 59) → (¬ p 129) → False)
    : (¬ p 129) → (¬ p 55) → (p 45) → (p 34) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 59 := (fun u => d408 a3 a2 u)
  exact d560 a1 v0 a0

theorem c4957 (p : Nat → Prop)
    (d185 : (p 49) → (p 59) → (p 72) → False)
    (d560 : (¬ p 55) → (¬ p 59) → (¬ p 129) → False)
    : (¬ p 129) → (¬ p 55) → (p 72) → (p 49) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 59 := (fun u => d185 a3 u a2)
  exact d560 a1 v0 a0

theorem c4958 (p : Nat → Prop)
    (d528 : (p 50) → (p 59) → (p 84) → False)
    (d560 : (¬ p 55) → (¬ p 59) → (¬ p 129) → False)
    : (¬ p 129) → (¬ p 55) → (p 50) → (p 84) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 59 := (fun u => d528 a2 u a3)
  exact d560 a1 v0 a0

theorem c4959 (p : Nat → Prop)
    (d215 : (p 57) → (p 59) → (p 140) → False)
    (d560 : (¬ p 55) → (¬ p 59) → (¬ p 129) → False)
    : (¬ p 129) → (¬ p 55) → (p 140) → (p 57) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 59 := (fun u => d215 a3 u a2)
  exact d560 a1 v0 a0

theorem c4960 (p : Nat → Prop)
    (d4944 : (¬ p 21) → (¬ p 50) → (p 30) → (p 59) → False)
    (d560 : (¬ p 55) → (¬ p 59) → (¬ p 129) → False)
    : (¬ p 129) → (¬ p 55) → (¬ p 21) → (¬ p 50) → (p 30) → False := by
  intro a0 a1 a2 a3 a4
  have v0 : ¬ p 59 := (fun u => d4944 a2 a3 a4 u)
  exact d560 a1 v0 a0

theorem c4961 (p : Nat → Prop)
    (d162 : (p 55) → (p 60) → (p 130) → False)
    (d506 : (¬ p 56) → (¬ p 60) → (¬ p 136) → False)
    : (¬ p 136) → (¬ p 56) → (p 55) → (p 130) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 60 := (fun u => d162 a2 u a3)
  exact d506 a1 v0 a0

theorem c4962 (p : Nat → Prop)
    (d90 : (p 53) → (p 60) → (p 115) → False)
    (d506 : (¬ p 56) → (¬ p 60) → (¬ p 136) → False)
    : (¬ p 136) → (¬ p 56) → (p 115) → (p 53) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 60 := (fun u => d90 a3 u a2)
  exact d506 a1 v0 a0

theorem c4963 (p : Nat → Prop)
    (d298 : (p 57) → (p 60) → (p 141) → False)
    (d506 : (¬ p 56) → (¬ p 60) → (¬ p 136) → False)
    : (¬ p 136) → (¬ p 56) → (p 141) → (p 57) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 60 := (fun u => d298 a3 u a2)
  exact d506 a1 v0 a0

theorem c4964 (p : Nat → Prop)
    (d246 : (p 49) → (p 60) → (p 73) → False)
    (d506 : (¬ p 56) → (¬ p 60) → (¬ p 136) → False)
    : (¬ p 136) → (¬ p 56) → (p 73) → (p 49) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 60 := (fun u => d246 a3 u a2)
  exact d506 a1 v0 a0

theorem c4965 (p : Nat → Prop)
    (d48 : (p 3) → (p 15) → (p 60) → False)
    (d506 : (¬ p 56) → (¬ p 60) → (¬ p 136) → False)
    : (¬ p 136) → (¬ p 56) → (p 15) → (p 3) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 60 := (fun u => d48 a3 a2 u)
  exact d506 a1 v0 a0

theorem c4966 (p : Nat → Prop)
    (d333 : (p 50) → (p 60) → (p 85) → False)
    (d506 : (¬ p 56) → (¬ p 60) → (¬ p 136) → False)
    : (¬ p 136) → (¬ p 56) → (p 85) → (p 50) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 60 := (fun u => d333 a3 u a2)
  exact d506 a1 v0 a0

theorem c4967 (p : Nat → Prop)
    (d531 : (p 51) → (p 60) → (p 96) → False)
    (d506 : (¬ p 56) → (¬ p 60) → (¬ p 136) → False)
    : (¬ p 136) → (¬ p 56) → (p 51) → (p 96) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 60 := (fun u => d531 a2 u a3)
  exact d506 a1 v0 a0

theorem c4968 (p : Nat → Prop)
    (d4907 : (¬ p 147) → (¬ p 58) → (p 152) → (p 60) → False)
    (d506 : (¬ p 56) → (¬ p 60) → (¬ p 136) → False)
    : (¬ p 136) → (¬ p 56) → (¬ p 147) → (¬ p 58) → (p 152) → False := by
  intro a0 a1 a2 a3 a4
  have v0 : ¬ p 60 := (fun u => d4907 a2 a3 a4 u)
  exact d506 a1 v0 a0

theorem c4969 (p : Nat → Prop)
    (d423 : (p 8) → (p 11) → (p 111) → False)
    (d518 : (¬ p 39) → (¬ p 42) → (¬ p 111) → False)
    : (¬ p 39) → (¬ p 42) → (p 8) → (p 11) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 111 := (fun u => d423 a2 a3 u)
  exact d518 a0 a1 v0

theorem c4970 (p : Nat → Prop)
    (d332 : (p 24) → (p 27) → (p 111) → False)
    (d518 : (¬ p 39) → (¬ p 42) → (¬ p 111) → False)
    : (¬ p 39) → (¬ p 42) → (p 27) → (p 24) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 111 := (fun u => d332 a3 a2 u)
  exact d518 a0 a1 v0

theorem c4971 (p : Nat → Prop)
    (d228 : (p 111) → (p 116) → (p 137) → False)
    (d518 : (¬ p 39) → (¬ p 42) → (¬ p 111) → False)
    : (¬ p 39) → (¬ p 42) → (p 116) → (p 137) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 111 := (fun u => d228 u a2 a3)
  exact d518 a0 a1 v0

theorem c4972 (p : Nat → Prop)
    (d392 : (p 66) → (p 69) → (p 111) → False)
    (d518 : (¬ p 39) → (¬ p 42) → (¬ p 111) → False)
    : (¬ p 39) → (¬ p 42) → (p 66) → (p 69) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 111 := (fun u => d392 a2 a3 u)
  exact d518 a0 a1 v0

theorem c4973 (p : Nat → Prop)
    (d305 : (p 53) → (p 56) → (p 111) → False)
    (d518 : (¬ p 39) → (¬ p 42) → (¬ p 111) → False)
    : (¬ p 39) → (¬ p 42) → (p 56) → (p 53) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 111 := (fun u => d305 a3 a2 u)
  exact d518 a0 a1 v0

theorem c4974 (p : Nat → Prop)
    (d363 : (p 109) → (p 111) → (p 119) → False)
    (d518 : (¬ p 39) → (¬ p 42) → (¬ p 111) → False)
    : (¬ p 39) → (¬ p 42) → (p 109) → (p 119) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 111 := (fun u => d363 a2 u a3)
  exact d518 a0 a1 v0

theorem c4975 (p : Nat → Prop)
    (d422 : (p 111) → (p 112) → (p 133) → False)
    (d518 : (¬ p 39) → (¬ p 42) → (¬ p 111) → False)
    : (¬ p 39) → (¬ p 42) → (p 112) → (p 133) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 111 := (fun u => d422 u a2 a3)
  exact d518 a0 a1 v0

theorem c4976 (p : Nat → Prop)
    (d286 : (p 111) → (p 113) → (p 134) → False)
    (d518 : (¬ p 39) → (¬ p 42) → (¬ p 111) → False)
    : (¬ p 39) → (¬ p 42) → (p 113) → (p 134) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 111 := (fun u => d286 u a2 a3)
  exact d518 a0 a1 v0

theorem c4977 (p : Nat → Prop)
    (d248 : (p 39) → (p 46) → (p 115) → False)
    (d203 : (¬ p 89) → (¬ p 96) → (¬ p 115) → False)
    : (¬ p 96) → (¬ p 89) → (p 39) → (p 46) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 115 := (fun u => d248 a2 a3 u)
  exact d203 a1 a0 v0

theorem c4978 (p : Nat → Prop)
    (d350 : (p 110) → (p 115) → (p 130) → False)
    (d203 : (¬ p 89) → (¬ p 96) → (¬ p 115) → False)
    : (¬ p 96) → (¬ p 89) → (p 110) → (p 130) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 115 := (fun u => d350 a2 u a3)
  exact d203 a1 a0 v0

theorem c4979 (p : Nat → Prop)
    (d507 : (p 109) → (p 115) → (p 123) → False)
    (d203 : (¬ p 89) → (¬ p 96) → (¬ p 115) → False)
    : (¬ p 96) → (¬ p 89) → (p 123) → (p 109) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 115 := (fun u => d507 a3 u a2)
  exact d203 a1 a0 v0

theorem c4980 (p : Nat → Prop)
    (d293 : (p 78) → (p 85) → (p 115) → False)
    (d203 : (¬ p 89) → (¬ p 96) → (¬ p 115) → False)
    : (¬ p 96) → (¬ p 89) → (p 85) → (p 78) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 115 := (fun u => d293 a3 a2 u)
  exact d203 a1 a0 v0

theorem c4981 (p : Nat → Prop)
    (d249 : (p 114) → (p 115) → (p 148) → False)
    (d203 : (¬ p 89) → (¬ p 96) → (¬ p 115) → False)
    : (¬ p 96) → (¬ p 89) → (p 114) → (p 148) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 115 := (fun u => d249 a2 u a3)
  exact d203 a1 a0 v0

theorem c4982 (p : Nat → Prop)
    (d472 : (p 112) → (p 115) → (p 141) → False)
    (d203 : (¬ p 89) → (¬ p 96) → (¬ p 115) → False)
    : (¬ p 96) → (¬ p 89) → (p 112) → (p 141) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 115 := (fun u => d472 a2 u a3)
  exact d203 a1 a0 v0

theorem c4983 (p : Nat → Prop)
    (d41 : (p 115) → (p 116) → (p 151) → False)
    (d203 : (¬ p 89) → (¬ p 96) → (¬ p 115) → False)
    : (¬ p 96) → (¬ p 89) → (p 116) → (p 151) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 115 := (fun u => d41 u a2 a3)
  exact d203 a1 a0 v0

theorem c4984 (p : Nat → Prop)
    (d4962 : (¬ p 136) → (¬ p 56) → (p 115) → (p 53) → False)
    (d203 : (¬ p 89) → (¬ p 96) → (¬ p 115) → False)
    : (¬ p 96) → (¬ p 89) → (¬ p 136) → (¬ p 56) → (p 53) → False := by
  intro a0 a1 a2 a3 a4
  have v0 : ¬ p 115 := (fun u => d4962 a2 a3 u a4)
  exact d203 a1 a0 v0

theorem c4985 (p : Nat → Prop)
    (d164 : (p 144) → (p 146) → (p 149) → False)
    (d494 : (¬ p 13) → (¬ p 14) → (¬ p 144) → False)
    : (¬ p 14) → (¬ p 13) → (p 149) → (p 146) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 144 := (fun u => d164 u a3 a2)
  exact d494 a1 a0 v0

theorem c4986 (p : Nat → Prop)
    (d374 : (p 128) → (p 129) → (p 144) → False)
    (d494 : (¬ p 13) → (¬ p 14) → (¬ p 144) → False)
    : (¬ p 14) → (¬ p 13) → (p 129) → (p 128) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 144 := (fun u => d374 a3 a2 u)
  exact d494 a1 a0 v0

theorem c4987 (p : Nat → Prop)
    (d113 : (p 113) → (p 114) → (p 144) → False)
    (d494 : (¬ p 13) → (¬ p 14) → (¬ p 144) → False)
    : (¬ p 14) → (¬ p 13) → (p 114) → (p 113) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 144 := (fun u => d113 a3 a2 u)
  exact d494 a1 a0 v0

theorem c4988 (p : Nat → Prop)
    (d61 : (p 134) → (p 135) → (p 144) → False)
    (d494 : (¬ p 13) → (¬ p 14) → (¬ p 144) → False)
    : (¬ p 14) → (¬ p 13) → (p 135) → (p 134) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 144 := (fun u => d61 a3 a2 u)
  exact d494 a1 a0 v0

theorem c4989 (p : Nat → Prop)
    (d214 : (p 44) → (p 45) → (p 144) → False)
    (d494 : (¬ p 13) → (¬ p 14) → (¬ p 144) → False)
    : (¬ p 14) → (¬ p 13) → (p 45) → (p 44) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 144 := (fun u => d214 a3 a2 u)
  exact d494 a1 a0 v0

theorem c4990 (p : Nat → Prop)
    (d355 : (p 139) → (p 140) → (p 144) → False)
    (d494 : (¬ p 13) → (¬ p 14) → (¬ p 144) → False)
    : (¬ p 14) → (¬ p 13) → (p 140) → (p 139) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 144 := (fun u => d355 a3 a2 u)
  exact d494 a1 a0 v0

theorem c4991 (p : Nat → Prop)
    (d526 : (p 29) → (p 30) → (p 144) → False)
    (d494 : (¬ p 13) → (¬ p 14) → (¬ p 144) → False)
    : (¬ p 14) → (¬ p 13) → (p 30) → (p 29) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 144 := (fun u => d526 a3 a2 u)
  exact d494 a1 a0 v0

theorem c4992 (p : Nat → Prop)
    (d186 : (p 104) → (p 105) → (p 144) → False)
    (d494 : (¬ p 13) → (¬ p 14) → (¬ p 144) → False)
    : (¬ p 14) → (¬ p 13) → (p 104) → (p 105) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 144 := (fun u => d186 a2 a3 u)
  exact d494 a1 a0 v0

theorem c4993 (p : Nat → Prop)
    (d57 : (p 42) → (p 46) → (p 136) → False)
    (d521 : (¬ p 43) → (¬ p 46) → (¬ p 141) → False)
    : (¬ p 43) → (¬ p 141) → (p 136) → (p 42) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 46 := (fun u => d57 a3 u a2)
  exact d521 a0 v0 a1

theorem c4994 (p : Nat → Prop)
    (d322 : (p 40) → (p 46) → (p 123) → False)
    (d521 : (¬ p 43) → (¬ p 46) → (¬ p 141) → False)
    : (¬ p 43) → (¬ p 141) → (p 123) → (p 40) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 46 := (fun u => d322 a3 u a2)
  exact d521 a0 v0 a1

theorem c4995 (p : Nat → Prop)
    (d411 : (p 41) → (p 46) → (p 130) → False)
    (d521 : (¬ p 43) → (¬ p 46) → (¬ p 141) → False)
    : (¬ p 43) → (¬ p 141) → (p 41) → (p 130) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 46 := (fun u => d411 a2 u a3)
  exact d521 a0 v0 a1

theorem c4996 (p : Nat → Prop)
    (d475 : (p 18) → (p 31) → (p 46) → False)
    (d521 : (¬ p 43) → (¬ p 46) → (¬ p 141) → False)
    : (¬ p 43) → (¬ p 141) → (p 18) → (p 31) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 46 := (fun u => d475 a2 a3 u)
  exact d521 a0 v0 a1

theorem c4997 (p : Nat → Prop)
    (d159 : (p 2) → (p 15) → (p 46) → False)
    (d521 : (¬ p 43) → (¬ p 46) → (¬ p 141) → False)
    : (¬ p 43) → (¬ p 141) → (p 15) → (p 2) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 46 := (fun u => d159 a3 a2 u)
  exact d521 a0 v0 a1

theorem c4998 (p : Nat → Prop)
    (d320 : (p 45) → (p 46) → (p 148) → False)
    (d521 : (¬ p 43) → (¬ p 46) → (¬ p 141) → False)
    : (¬ p 43) → (¬ p 141) → (p 45) → (p 148) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 46 := (fun u => d320 a2 u a3)
  exact d521 a0 v0 a1

theorem c4999 (p : Nat → Prop)
    (d93 : (p 46) → (p 48) → (p 152) → False)
    (d521 : (¬ p 43) → (¬ p 46) → (¬ p 141) → False)
    : (¬ p 43) → (¬ p 141) → (p 152) → (p 48) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 46 := (fun u => d93 u a3 a2)
  exact d521 a0 v0 a1

theorem c5000 (p : Nat → Prop)
    (d240 : (p 37) → (p 46) → (p 96) → False)
    (d521 : (¬ p 43) → (¬ p 46) → (¬ p 141) → False)
    : (¬ p 43) → (¬ p 141) → (p 96) → (p 37) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 46 := (fun u => d240 a3 u a2)
  exact d521 a0 v0 a1

theorem c5001 (p : Nat → Prop)
    (d4977 : (¬ p 96) → (¬ p 89) → (p 39) → (p 46) → False)
    (d521 : (¬ p 43) → (¬ p 46) → (¬ p 141) → False)
    : (¬ p 43) → (¬ p 141) → (¬ p 96) → (¬ p 89) → (p 39) → False := by
  intro a0 a1 a2 a3 a4
  have v0 : ¬ p 46 := (fun u => d4977 a2 a3 a4 u)
  exact d521 a0 v0 a1

theorem c5002 (p : Nat → Prop)
    (d361 : (p 36) → (p 48) → (p 87) → False)
    (d576 : (¬ p 45) → (¬ p 48) → (¬ p 150) → False)
    : (¬ p 150) → (¬ p 45) → (p 87) → (p 36) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 48 := (fun u => d361 a3 u a2)
  exact d576 a1 v0 a0

theorem c5003 (p : Nat → Prop)
    (d388 : (p 41) → (p 48) → (p 132) → False)
    (d576 : (¬ p 45) → (¬ p 48) → (¬ p 150) → False)
    : (¬ p 150) → (¬ p 45) → (p 132) → (p 41) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 48 := (fun u => d388 a3 u a2)
  exact d576 a1 v0 a0

theorem c5004 (p : Nat → Prop)
    (d148 : (p 44) → (p 48) → (p 147) → False)
    (d576 : (¬ p 45) → (¬ p 48) → (¬ p 150) → False)
    : (¬ p 150) → (¬ p 45) → (p 147) → (p 44) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 48 := (fun u => d148 a3 u a2)
  exact d576 a1 v0 a0

theorem c5005 (p : Nat → Prop)
    (d562 : (p 18) → (p 33) → (p 48) → False)
    (d576 : (¬ p 45) → (¬ p 48) → (¬ p 150) → False)
    : (¬ p 150) → (¬ p 45) → (p 18) → (p 33) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 48 := (fun u => d562 a2 a3 u)
  exact d576 a1 v0 a0

theorem c5006 (p : Nat → Prop)
    (d316 : (p 42) → (p 48) → (p 138) → False)
    (d576 : (¬ p 45) → (¬ p 48) → (¬ p 150) → False)
    : (¬ p 150) → (¬ p 45) → (p 138) → (p 42) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 48 := (fun u => d316 a3 u a2)
  exact d576 a1 v0 a0

theorem c5007 (p : Nat → Prop)
    (d68 : (p 37) → (p 48) → (p 98) → False)
    (d576 : (¬ p 45) → (¬ p 48) → (¬ p 150) → False)
    : (¬ p 150) → (¬ p 45) → (p 98) → (p 37) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 48 := (fun u => d68 a3 u a2)
  exact d576 a1 v0 a0

theorem c5008 (p : Nat → Prop)
    (d410 : (p 2) → (p 17) → (p 48) → False)
    (d576 : (¬ p 45) → (¬ p 48) → (¬ p 150) → False)
    : (¬ p 150) → (¬ p 45) → (p 17) → (p 2) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 48 := (fun u => d410 a3 a2 u)
  exact d576 a1 v0 a0

theorem c5009 (p : Nat → Prop)
    (d269 : (p 35) → (p 48) → (p 75) → False)
    (d576 : (¬ p 45) → (¬ p 48) → (¬ p 150) → False)
    : (¬ p 150) → (¬ p 45) → (p 75) → (p 35) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 48 := (fun u => d269 a3 u a2)
  exact d576 a1 v0 a0

theorem c5010 (p : Nat → Prop)
    (d4999 : (¬ p 43) → (¬ p 141) → (p 152) → (p 48) → False)
    (d576 : (¬ p 45) → (¬ p 48) → (¬ p 150) → False)
    : (¬ p 150) → (¬ p 45) → (¬ p 43) → (¬ p 141) → (p 152) → False := by
  intro a0 a1 a2 a3 a4
  have v0 : ¬ p 48 := (fun u => d4999 a2 a3 a4 u)
  exact d576 a1 v0 a0

theorem c5011 (p : Nat → Prop)
    (d573 : (p 72) → (p 75) → (p 150) → False)
    (d34 : (¬ p 70) → (¬ p 75) → (¬ p 143) → False)
    : (¬ p 143) → (¬ p 70) → (p 72) → (p 150) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 75 := (fun u => d573 a2 u a3)
  exact d34 a1 v0 a0

theorem c5012 (p : Nat → Prop)
    (d40 : (p 63) → (p 75) → (p 87) → False)
    (d34 : (¬ p 70) → (¬ p 75) → (¬ p 143) → False)
    : (¬ p 143) → (¬ p 70) → (p 63) → (p 87) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 75 := (fun u => d40 a2 u a3)
  exact d34 a1 v0 a0

theorem c5013 (p : Nat → Prop)
    (d174 : (p 67) → (p 75) → (p 125) → False)
    (d34 : (¬ p 70) → (¬ p 75) → (¬ p 143) → False)
    : (¬ p 143) → (¬ p 70) → (p 67) → (p 125) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 75 := (fun u => d174 a2 u a3)
  exact d34 a1 v0 a0

theorem c5014 (p : Nat → Prop)
    (d36 : (p 68) → (p 75) → (p 132) → False)
    (d34 : (¬ p 70) → (¬ p 75) → (¬ p 143) → False)
    : (¬ p 143) → (¬ p 70) → (p 68) → (p 132) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 75 := (fun u => d36 a2 u a3)
  exact d34 a1 v0 a0

theorem c5015 (p : Nat → Prop)
    (d421 : (p 64) → (p 75) → (p 98) → False)
    (d34 : (¬ p 70) → (¬ p 75) → (¬ p 143) → False)
    : (¬ p 143) → (¬ p 70) → (p 64) → (p 98) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 75 := (fun u => d421 a2 u a3)
  exact d34 a1 v0 a0

theorem c5016 (p : Nat → Prop)
    (d594 : (p 69) → (p 75) → (p 138) → False)
    (d34 : (¬ p 70) → (¬ p 75) → (¬ p 143) → False)
    : (¬ p 143) → (¬ p 70) → (p 138) → (p 69) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 75 := (fun u => d594 a3 u a2)
  exact d34 a1 v0 a0

theorem c5017 (p : Nat → Prop)
    (d523 : (p 20) → (p 33) → (p 75) → False)
    (d34 : (¬ p 70) → (¬ p 75) → (¬ p 143) → False)
    : (¬ p 143) → (¬ p 70) → (p 20) → (p 33) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 75 := (fun u => d523 a2 a3 u)
  exact d34 a1 v0 a0

theorem c5018 (p : Nat → Prop)
    (d487 : (p 73) → (p 75) → (p 152) → False)
    (d34 : (¬ p 70) → (¬ p 75) → (¬ p 143) → False)
    : (¬ p 143) → (¬ p 70) → (p 152) → (p 73) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 75 := (fun u => d487 a3 u a2)
  exact d34 a1 v0 a0

theorem c5019 (p : Nat → Prop)
    (d5009 : (¬ p 150) → (¬ p 45) → (p 75) → (p 35) → False)
    (d34 : (¬ p 70) → (¬ p 75) → (¬ p 143) → False)
    : (¬ p 143) → (¬ p 70) → (¬ p 150) → (¬ p 45) → (p 35) → False := by
  intro a0 a1 a2 a3 a4
  have v0 : ¬ p 75 := (fun u => d5009 a2 a3 u a4)
  exact d34 a1 v0 a0

theorem c5020 (p : Nat → Prop)
    (d219 : (p 81) → (p 82) → (p 133) → False)
    (d35 : (¬ p 76) → (¬ p 82) → (¬ p 93) → False)
    : (¬ p 93) → (¬ p 76) → (p 81) → (p 133) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 82 := (fun u => d219 a2 u a3)
  exact d35 a1 v0 a0

theorem c5021 (p : Nat → Prop)
    (d128 : (p 82) → (p 87) → (p 143) → False)
    (d35 : (¬ p 76) → (¬ p 82) → (¬ p 93) → False)
    : (¬ p 93) → (¬ p 76) → (p 143) → (p 87) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 82 := (fun u => d128 u a3 a2)
  exact d35 a1 v0 a0

theorem c5022 (p : Nat → Prop)
    (d288 : (p 50) → (p 57) → (p 82) → False)
    (d35 : (¬ p 76) → (¬ p 82) → (¬ p 93) → False)
    : (¬ p 93) → (¬ p 76) → (p 50) → (p 57) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 82 := (fun u => d288 a2 a3 u)
  exact d35 a1 v0 a0

theorem c5023 (p : Nat → Prop)
    (d2 : (p 5) → (p 12) → (p 82) → False)
    (d35 : (¬ p 76) → (¬ p 82) → (¬ p 93) → False)
    : (¬ p 93) → (¬ p 76) → (p 5) → (p 12) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 82 := (fun u => d2 a2 a3 u)
  exact d35 a1 v0 a0

theorem c5024 (p : Nat → Prop)
    (d312 : (p 63) → (p 70) → (p 82) → False)
    (d35 : (¬ p 76) → (¬ p 82) → (¬ p 93) → False)
    : (¬ p 93) → (¬ p 76) → (p 63) → (p 70) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 82 := (fun u => d312 a2 a3 u)
  exact d35 a1 v0 a0

theorem c5025 (p : Nat → Prop)
    (d37 : (p 36) → (p 43) → (p 82) → False)
    (d35 : (¬ p 76) → (¬ p 82) → (¬ p 93) → False)
    : (¬ p 93) → (¬ p 76) → (p 43) → (p 36) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 82 := (fun u => d37 a3 a2 u)
  exact d35 a1 v0 a0

theorem c5026 (p : Nat → Prop)
    (d460 : (p 78) → (p 82) → (p 112) → False)
    (d35 : (¬ p 76) → (¬ p 82) → (¬ p 93) → False)
    : (¬ p 93) → (¬ p 76) → (p 112) → (p 78) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 82 := (fun u => d460 a3 u a2)
  exact d35 a1 v0 a0

theorem c5027 (p : Nat → Prop)
    (d139 : (p 77) → (p 82) → (p 103) → False)
    (d35 : (¬ p 76) → (¬ p 82) → (¬ p 93) → False)
    : (¬ p 93) → (¬ p 76) → (p 103) → (p 77) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 82 := (fun u => d139 a3 u a2)
  exact d35 a1 v0 a0

theorem c5028 (p : Nat → Prop)
    (d479 : (p 82) → (p 86) → (p 142) → False)
    (d35 : (¬ p 76) → (¬ p 82) → (¬ p 93) → False)
    : (¬ p 93) → (¬ p 76) → (p 142) → (p 86) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 82 := (fun u => d479 u a3 a2)
  exact d35 a1 v0 a0

theorem c5029 (p : Nat → Prop)
    (d430 : (p 80) → (p 85) → (p 130) → False)
    (d239 : (¬ p 79) → (¬ p 85) → (¬ p 123) → False)
    : (¬ p 123) → (¬ p 79) → (p 80) → (p 130) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 85 := (fun u => d430 a2 u a3)
  exact d239 a1 v0 a0

theorem c5030 (p : Nat → Prop)
    (d596 : (p 81) → (p 85) → (p 136) → False)
    (d239 : (¬ p 79) → (¬ p 85) → (¬ p 123) → False)
    : (¬ p 123) → (¬ p 79) → (p 81) → (p 136) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 85 := (fun u => d596 a2 u a3)
  exact d239 a1 v0 a0

theorem c5031 (p : Nat → Prop)
    (d9 : (p 63) → (p 73) → (p 85) → False)
    (d239 : (¬ p 79) → (¬ p 85) → (¬ p 123) → False)
    : (¬ p 123) → (¬ p 79) → (p 73) → (p 63) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 85 := (fun u => d9 a3 a2 u)
  exact d239 a1 v0 a0

theorem c5032 (p : Nat → Prop)
    (d459 : (p 21) → (p 31) → (p 85) → False)
    (d239 : (¬ p 79) → (¬ p 85) → (¬ p 123) → False)
    : (¬ p 123) → (¬ p 79) → (p 21) → (p 31) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 85 := (fun u => d459 a2 a3 u)
  exact d239 a1 v0 a0

theorem c5033 (p : Nat → Prop)
    (d72 : (p 5) → (p 15) → (p 85) → False)
    (d239 : (¬ p 79) → (¬ p 85) → (¬ p 123) → False)
    : (¬ p 123) → (¬ p 79) → (p 5) → (p 15) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 85 := (fun u => d72 a2 a3 u)
  exact d239 a1 v0 a0

theorem c5034 (p : Nat → Prop)
    (d485 : (p 84) → (p 85) → (p 148) → False)
    (d239 : (¬ p 79) → (¬ p 85) → (¬ p 123) → False)
    : (¬ p 123) → (¬ p 79) → (p 84) → (p 148) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 85 := (fun u => d485 a2 u a3)
  exact d239 a1 v0 a0

theorem c5035 (p : Nat → Prop)
    (d251 : (p 85) → (p 87) → (p 152) → False)
    (d239 : (¬ p 79) → (¬ p 85) → (¬ p 123) → False)
    : (¬ p 123) → (¬ p 79) → (p 152) → (p 87) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 85 := (fun u => d251 u a3 a2)
  exact d239 a1 v0 a0

theorem c5036 (p : Nat → Prop)
    (d4966 : (¬ p 136) → (¬ p 56) → (p 85) → (p 50) → False)
    (d239 : (¬ p 79) → (¬ p 85) → (¬ p 123) → False)
    : (¬ p 123) → (¬ p 79) → (¬ p 136) → (¬ p 56) → (p 50) → False := by
  intro a0 a1 a2 a3 a4
  have v0 : ¬ p 85 := (fun u => d4966 a2 a3 u a4)
  exact d239 a1 v0 a0

theorem c5037 (p : Nat → Prop)
    (d4980 : (¬ p 96) → (¬ p 89) → (p 85) → (p 78) → False)
    (d239 : (¬ p 79) → (¬ p 85) → (¬ p 123) → False)
    : (¬ p 123) → (¬ p 79) → (¬ p 96) → (¬ p 89) → (p 78) → False := by
  intro a0 a1 a2 a3 a4
  have v0 : ¬ p 85 := (fun u => d4980 a2 a3 u a4)
  exact d239 a1 v0 a0

theorem c5038 (p : Nat → Prop)
    (d389 : (p 76) → (p 81) → (p 92) → False)
    (d16 : (¬ p 64) → (¬ p 69) → (¬ p 92) → False)
    : (¬ p 64) → (¬ p 69) → (p 81) → (p 76) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 92 := (fun u => d389 a3 a2 u)
  exact d16 a0 a1 v0

end JSP000746.RUP
