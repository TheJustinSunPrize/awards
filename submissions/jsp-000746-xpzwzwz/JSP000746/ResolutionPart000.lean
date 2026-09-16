import Init.Classical

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace JSP000746.RUP

theorem c603 (p : Nat → Prop)
    (d271 : (p 105) → (p 108) → (p 150) → False)
    (d448 : (p 88) → (p 98) → (p 108) → False)
    (d527 : (p 95) → (p 98) → (p 150) → False)
    (d12 : (¬ p 88) → (¬ p 95) → (¬ p 105) → False)
    : (p 98) → (p 108) → (p 150) → False := by
  intro a0 a1 a2
  have v0 : ¬ p 105 := (fun u => d271 u a1 a2)
  have v1 : ¬ p 88 := (fun u => d448 u a0 a1)
  have v2 : ¬ p 95 := (fun u => d527 u a0 a2)
  exact d12 v1 v2 v0

theorem c604 (p : Nat → Prop)
    (d236 : (p 104) → (p 108) → (p 147) → False)
    (d178 : (p 83) → (p 87) → (p 147) → False)
    (d202 : (p 77) → (p 87) → (p 108) → False)
    (d15 : (¬ p 77) → (¬ p 83) → (¬ p 104) → False)
    : (p 87) → (p 108) → (p 147) → False := by
  intro a0 a1 a2
  have v0 : ¬ p 104 := (fun u => d236 u a1 a2)
  have v1 : ¬ p 83 := (fun u => d178 u a0 a2)
  have v2 : ¬ p 77 := (fun u => d202 u a0 a1)
  exact d15 v2 v1 v0

theorem c605 (p : Nat → Prop)
    (d474 : (p 130) → (p 132) → (p 152) → False)
    (d36 : (p 68) → (p 75) → (p 132) → False)
    (d487 : (p 73) → (p 75) → (p 152) → False)
    (d138 : (¬ p 68) → (¬ p 73) → (¬ p 130) → False)
    : (p 75) → (p 132) → (p 152) → False := by
  intro a0 a1 a2
  have v0 : ¬ p 130 := (fun u => d474 u a1 a2)
  have v1 : ¬ p 68 := (fun u => d36 u a0 a1)
  have v2 : ¬ p 73 := (fun u => d487 u a0 a2)
  exact d138 v1 v2 v0

theorem c607 (p : Nat → Prop)
    (d73 : (p 69) → (p 71) → (p 134) → False)
    (d110 : (p 71) → (p 74) → (p 146) → False)
    (d589 : (¬ p 69) → (¬ p 74) → (¬ p 137) → False)
    : (p 71) → (p 134) → (¬ p 137) → (p 146) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 69 := (fun u => d73 u a0 a1)
  have v1 : ¬ p 74 := (fun u => d110 a0 u a3)
  exact d589 v0 v1 a2

theorem c608 (p : Nat → Prop)
    (d63 : (p 136) → (p 138) → (p 152) → False)
    (d461 : (p 60) → (p 62) → (p 152) → False)
    (d529 : (p 56) → (p 62) → (p 138) → False)
    (d506 : (¬ p 56) → (¬ p 60) → (¬ p 136) → False)
    : (p 62) → (p 138) → (p 152) → False := by
  intro a0 a1 a2
  have v0 : ¬ p 136 := (fun u => d63 u a1 a2)
  have v1 : ¬ p 60 := (fun u => d461 u a0 a2)
  have v2 : ¬ p 56 := (fun u => d529 u a0 a1)
  exact d506 v2 v1 v0

theorem c609 (p : Nat → Prop)
    (d511 : (p 128) → (p 132) → (p 147) → False)
    (d148 : (p 44) → (p 48) → (p 147) → False)
    (d388 : (p 41) → (p 48) → (p 132) → False)
    (d88 : (¬ p 41) → (¬ p 44) → (¬ p 128) → False)
    : (p 48) → (p 132) → (p 147) → False := by
  intro a0 a1 a2
  have v0 : ¬ p 128 := (fun u => d511 u a1 a2)
  have v1 : ¬ p 44 := (fun u => d148 u a0 a2)
  have v2 : ¬ p 41 := (fun u => d388 u a0 a1)
  exact d88 v2 v1 v0

theorem c610 (p : Nat → Prop)
    (d150 : (p 78) → (p 80) → (p 110) → False)
    (d14 : (p 39) → (p 41) → (p 110) → False)
    (d360 : (p 36) → (p 41) → (p 80) → False)
    (d58 : (¬ p 36) → (¬ p 39) → (¬ p 78) → False)
    : (p 41) → (p 80) → (p 110) → False := by
  intro a0 a1 a2
  have v0 : ¬ p 78 := (fun u => d150 u a1 a2)
  have v1 : ¬ p 39 := (fun u => d14 u a0 a2)
  have v2 : ¬ p 36 := (fun u => d360 u a0 a1)
  exact d58 v2 v1 v0

theorem c611 (p : Nat → Prop)
    (d504 : (p 140) → (p 143) → (p 150) → False)
    (d230 : (p 28) → (p 33) → (p 143) → False)
    (d268 : (p 30) → (p 33) → (p 150) → False)
    (d427 : (¬ p 28) → (¬ p 30) → (¬ p 140) → False)
    : (p 33) → (p 143) → (p 150) → False := by
  intro a0 a1 a2
  have v0 : ¬ p 140 := (fun u => d504 u a1 a2)
  have v1 : ¬ p 28 := (fun u => d230 u a0 a1)
  have v2 : ¬ p 30 := (fun u => d268 u a0 a2)
  exact d427 v1 v2 v0

theorem c612 (p : Nat → Prop)
    (d145 : (¬ p 30) → (¬ p 32) → (¬ p 149) → False)
    (d427 : (¬ p 28) → (¬ p 30) → (¬ p 140) → False)
    (d104 : (p 29) → (p 32) → (p 146) → False)
    (d144 : (p 28) → (p 31) → (p 141) → False)
    (d134 : (¬ p 29) → (¬ p 31) → (¬ p 145) → False)
    : (¬ p 30) → (p 141) → (¬ p 140) → (p 146) → (¬ p 145) → (¬ p 149) → False := by
  intro a0 a1 a2 a3 a4 a5
  have v0 : p 32 := Classical.byContradiction (fun u => d145 a0 u a5)
  have v1 : p 28 := Classical.byContradiction (fun u => d427 u a0 a2)
  have v2 : ¬ p 29 := (fun u => d104 u v0 a3)
  have v3 : ¬ p 31 := (fun u => d144 v1 u a1)
  exact d134 v2 v3 a4

theorem c613 (p : Nat → Prop)
    (d257 : (p 20) → (p 27) → (p 69) → False)
    (d582 : (p 18) → (p 27) → (p 42) → False)
    (d508 : (¬ p 18) → (¬ p 20) → (¬ p 35) → False)
    (d101 : (p 35) → (p 42) → (p 69) → False)
    : (p 42) → (p 69) → (p 27) → False := by
  intro a0 a1 a2
  have v0 : ¬ p 20 := (fun u => d257 u a2 a1)
  have v1 : ¬ p 18 := (fun u => d582 u a2 a0)
  have v2 : p 35 := Classical.byContradiction (fun u => d508 v1 v0 u)
  exact d101 v2 a0 a1

theorem c614 (p : Nat → Prop)
    (d3 : (¬ p 34) → (¬ p 37) → (¬ p 51) → False)
    (d10 : (¬ p 37) → (¬ p 40) → (¬ p 90) → False)
    (d17 : (p 51) → (p 54) → (p 90) → False)
    : (¬ p 37) → (¬ p 34) → (p 54) → (¬ p 40) → False := by
  intro a0 a1 a2 a3
  have v0 : p 51 := Classical.byContradiction (fun u => d3 a1 a0 u)
  have v1 : p 90 := Classical.byContradiction (fun u => d10 a0 a3 u)
  exact d17 v0 a2 v1

theorem c615 (p : Nat → Prop)
    (d517 : (p 22) → (p 23) → (p 88) → False)
    (d175 : (p 88) → (p 90) → (p 100) → False)
    (d442 : (¬ p 23) → (¬ p 25) → (¬ p 100) → False)
    : (p 88) → (p 90) → (p 22) → (¬ p 25) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 23 := (fun u => d517 a2 u a0)
  have v1 : ¬ p 100 := (fun u => d175 a0 a1 u)
  exact d442 v0 a3 v1

theorem c616 (p : Nat → Prop)
    (d454 : (p 25) → (p 30) → (p 122) → False)
    (d331 : (p 100) → (p 105) → (p 122) → False)
    (d520 : (p 23) → (p 30) → (p 105) → False)
    (d442 : (¬ p 23) → (¬ p 25) → (¬ p 100) → False)
    : (p 105) → (p 122) → (p 30) → False := by
  intro a0 a1 a2
  have v0 : ¬ p 25 := (fun u => d454 u a2 a1)
  have v1 : ¬ p 100 := (fun u => d331 u a0 a1)
  have v2 : ¬ p 23 := (fun u => d520 u a2 a0)
  exact d442 v2 v0 v1

theorem c617 (p : Nat → Prop)
    (d532 : (p 54) → (p 59) → (p 122) → False)
    (d614 : (¬ p 37) → (¬ p 34) → (p 54) → (¬ p 40) → False)
    (d560 : (¬ p 55) → (¬ p 59) → (¬ p 129) → False)
    (d559 : (p 34) → (p 41) → (p 55) → False)
    : (p 54) → (¬ p 37) → (p 41) → (¬ p 40) → (p 122) → (¬ p 129) → False := by
  intro a0 a1 a2 a3 a4 a5
  have v0 : ¬ p 59 := (fun u => d532 a0 u a4)
  have v1 : p 34 := Classical.byContradiction (fun u => d614 a1 u a0 a3)
  have v2 : p 55 := Classical.byContradiction (fun u => d560 u v0 a5)
  exact d559 v1 a2 v2

theorem c618 (p : Nat → Prop)
    (d472 : (p 112) → (p 115) → (p 141) → False)
    (d90 : (p 53) → (p 60) → (p 115) → False)
    (d298 : (p 57) → (p 60) → (p 141) → False)
    (d538 : (¬ p 53) → (¬ p 57) → (¬ p 112) → False)
    : (p 60) → (p 115) → (p 141) → False := by
  intro a0 a1 a2
  have v0 : ¬ p 112 := (fun u => d472 u a1 a2)
  have v1 : ¬ p 53 := (fun u => d90 u a0 a1)
  have v2 : ¬ p 57 := (fun u => d298 u a0 a2)
  exact d538 v1 v2 v0

theorem c619 (p : Nat → Prop)
    (d229 : (p 148) → (p 150) → (p 152) → False)
    (d447 : (p 15) → (p 17) → (p 152) → False)
    (d486 : (p 14) → (p 17) → (p 150) → False)
    (d27 : (¬ p 14) → (¬ p 15) → (¬ p 148) → False)
    : (p 17) → (p 150) → (p 152) → False := by
  intro a0 a1 a2
  have v0 : ¬ p 148 := (fun u => d229 u a1 a2)
  have v1 : ¬ p 15 := (fun u => d447 u a0 a2)
  have v2 : ¬ p 14 := (fun u => d486 u a0 a1)
  exact d27 v2 v1 v0

theorem c621 (p : Nat → Prop)
    (d266 : (p 49) → (p 56) → (p 69) → False)
    (d549 : (¬ p 3) → (¬ p 4) → (¬ p 49) → False)
    (d120 : (p 3) → (p 11) → (p 56) → False)
    : (p 56) → (p 11) → (¬ p 4) → (p 69) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 49 := (fun u => d266 u a0 a3)
  have v1 : p 3 := Classical.byContradiction (fun u => d549 u a2 v0)
  exact d120 v1 a1 a0

theorem c622 (p : Nat → Prop)
    (d166 : (¬ p 11) → (¬ p 12) → (¬ p 133) → False)
    (d92 : (¬ p 12) → (¬ p 13) → (¬ p 139) → False)
    (d393 : (p 11) → (p 13) → (p 134) → False)
    : (¬ p 12) → (p 134) → (¬ p 133) → (¬ p 139) → False := by
  intro a0 a1 a2 a3
  have v0 : p 11 := Classical.byContradiction (fun u => d166 u a0 a2)
  have v1 : p 13 := Classical.byContradiction (fun u => d92 a0 u a3)
  exact d393 v0 v1 a1

theorem c623 (p : Nat → Prop)
    (d243 : (p 12) → (p 15) → (p 141) → False)
    (d401 : (p 12) → (p 16) → (p 142) → False)
    (d153 : (¬ p 15) → (¬ p 16) → (¬ p 151) → False)
    : (p 12) → (p 141) → (p 142) → (¬ p 151) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 15 := (fun u => d243 a0 u a1)
  have v1 : ¬ p 16 := (fun u => d401 a0 u a2)
  exact d153 v0 v1 a3

theorem c624 (p : Nat → Prop)
    (d22 : (p 4) → (p 11) → (p 69) → False)
    (d621 : (p 56) → (p 11) → (¬ p 4) → (p 69) → False)
    : (p 69) → (p 56) → (p 11) → False := by
  intro a0 a1 a2
  have v0 : ¬ p 4 := (fun u => d22 u a2 a0)
  exact d621 a1 a2 v0 a0

theorem c625 (p : Nat → Prop)
    (d398 : (p 1) → (p 11) → (p 27) → False)
    (d582 : (p 18) → (p 27) → (p 42) → False)
    (d300 : (p 2) → (p 11) → (p 42) → False)
    (d170 : (¬ p 1) → (¬ p 2) → (¬ p 18) → False)
    : (p 42) → (p 27) → (p 11) → False := by
  intro a0 a1 a2
  have v0 : ¬ p 1 := (fun u => d398 u a2 a1)
  have v1 : ¬ p 18 := (fun u => d582 u a1 a0)
  have v2 : ¬ p 2 := (fun u => d300 u a2 a0)
  exact d170 v0 v2 v1

theorem c626 (p : Nat → Prop)
    (d16 : (¬ p 64) → (¬ p 69) → (¬ p 92) → False)
    (d270 : (¬ p 20) → (¬ p 22) → (¬ p 64) → False)
    (d30 : (p 22) → (p 27) → (p 92) → False)
    : (¬ p 64) → (¬ p 20) → (¬ p 69) → (p 27) → False := by
  intro a0 a1 a2 a3
  have v0 : p 92 := Classical.byContradiction (fun u => d16 a0 a2 u)
  have v1 : p 22 := Classical.byContradiction (fun u => d270 a1 u a0)
  exact d30 v1 a3 v0

theorem c627 (p : Nat → Prop)
    (d508 : (¬ p 18) → (¬ p 20) → (¬ p 35) → False)
    (d462 : (p 34) → (p 35) → (p 49) → False)
    (d626 : (¬ p 64) → (¬ p 20) → (¬ p 69) → (p 27) → False)
    (d330 : (p 35) → (p 37) → (p 64) → False)
    (d105 : (p 49) → (p 51) → (p 64) → False)
    (d3 : (¬ p 34) → (¬ p 37) → (¬ p 51) → False)
    : (¬ p 20) → (p 49) → (¬ p 69) → (¬ p 18) → (p 27) → False := by
  intro a0 a1 a2 a3 a4
  have v0 : p 35 := Classical.byContradiction (fun u => d508 a3 a0 u)
  have v1 : ¬ p 34 := (fun u => d462 u v0 a1)
  have v2 : p 64 := Classical.byContradiction (fun u => d626 u a0 a2 a4)
  have v3 : ¬ p 37 := (fun u => d330 v0 u v2)
  have v4 : ¬ p 51 := (fun u => d105 a1 u v2)
  exact d3 v1 v3 v4

theorem c628 (p : Nat → Prop)
    (d305 : (p 53) → (p 56) → (p 111) → False)
    (d351 : (p 34) → (p 39) → (p 53) → False)
    (d518 : (¬ p 39) → (¬ p 42) → (¬ p 111) → False)
    : (p 53) → (p 34) → (p 56) → (¬ p 42) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 111 := (fun u => d305 a0 a2 u)
  have v1 : ¬ p 39 := (fun u => d351 a1 u a0)
  exact d518 v1 a3 v0

theorem c631 (p : Nat → Prop)
    (d144 : (p 28) → (p 31) → (p 141) → False)
    (d282 : (p 127) → (p 130) → (p 141) → False)
    (d11 : (p 26) → (p 31) → (p 130) → False)
    (d492 : (¬ p 26) → (¬ p 28) → (¬ p 127) → False)
    : (p 130) → (p 31) → (p 141) → False := by
  intro a0 a1 a2
  have v0 : ¬ p 28 := (fun u => d144 u a1 a2)
  have v1 : ¬ p 127 := (fun u => d282 u a0 a2)
  have v2 : ¬ p 26 := (fun u => d11 u a1 a0)
  exact d492 v2 v0 v1

theorem c632 (p : Nat → Prop)
    (d583 : (p 49) → (p 55) → (p 68) → False)
    (d105 : (p 49) → (p 51) → (p 64) → False)
    (d512 : (p 64) → (p 68) → (p 91) → False)
    (d444 : (¬ p 51) → (¬ p 55) → (¬ p 91) → False)
    : (p 64) → (p 68) → (p 49) → False := by
  intro a0 a1 a2
  have v0 : ¬ p 55 := (fun u => d583 a2 u a1)
  have v1 : ¬ p 51 := (fun u => d105 a2 u a0)
  have v2 : ¬ p 91 := (fun u => d512 a0 a1 u)
  exact d444 v1 v0 v2

theorem c633 (p : Nat → Prop)
    (d400 : (¬ p 22) → (¬ p 24) → (¬ p 89) → False)
    (d341 : (¬ p 24) → (¬ p 26) → (¬ p 110) → False)
    (d97 : (p 89) → (p 91) → (p 110) → False)
    : (¬ p 24) → (p 91) → (¬ p 22) → (¬ p 26) → False := by
  intro a0 a1 a2 a3
  have v0 : p 89 := Classical.byContradiction (fun u => d400 a2 a0 u)
  have v1 : p 110 := Classical.byContradiction (fun u => d341 a0 a3 u)
  exact d97 v0 a1 v1

theorem c635 (p : Nat → Prop)
    (d386 : (p 2) → (p 8) → (p 39) → False)
    (d106 : (p 38) → (p 39) → (p 99) → False)
    (d117 : (p 2) → (p 7) → (p 38) → False)
    (d111 : (¬ p 7) → (¬ p 8) → (¬ p 99) → False)
    : (p 38) → (p 39) → (p 2) → False := by
  intro a0 a1 a2
  have v0 : ¬ p 8 := (fun u => d386 a2 u a1)
  have v1 : ¬ p 99 := (fun u => d106 a0 a1 u)
  have v2 : ¬ p 7 := (fun u => d117 a2 u a0)
  exact d111 v2 v0 v1

theorem c636 (p : Nat → Prop)
    (d593 : (p 101) → (p 103) → (p 127) → False)
    (d221 : (p 65) → (p 68) → (p 101) → False)
    (d154 : (¬ p 65) → (¬ p 70) → (¬ p 103) → False)
    : (p 101) → (p 127) → (p 68) → (¬ p 70) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 103 := (fun u => d593 a0 u a1)
  have v1 : ¬ p 65 := (fun u => d221 u a2 a0)
  exact d154 v1 a3 v0

theorem c637 (p : Nat → Prop)
    (d324 : (p 7) → (p 9) → (p 100) → False)
    (d7 : (p 99) → (p 100) → (p 109) → False)
    (d394 : (¬ p 8) → (¬ p 9) → (¬ p 109) → False)
    : (p 100) → (p 7) → (p 99) → (¬ p 8) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 9 := (fun u => d324 a1 u a0)
  have v1 : ¬ p 109 := (fun u => d7 a2 a0 u)
  exact d394 a3 v0 v1

theorem c638 (p : Nat → Prop)
    (d432 : (p 20) → (p 30) → (p 72) → False)
    (d142 : (p 20) → (p 25) → (p 67) → False)
    (d454 : (p 25) → (p 30) → (p 122) → False)
    (d323 : (¬ p 67) → (¬ p 72) → (¬ p 122) → False)
    : (p 25) → (p 20) → (p 30) → False := by
  intro a0 a1 a2
  have v0 : ¬ p 72 := (fun u => d432 a1 a2 u)
  have v1 : ¬ p 67 := (fun u => d142 a1 a0 u)
  have v2 : ¬ p 122 := (fun u => d454 a0 a2 u)
  exact d323 v1 v0 v2

theorem c640 (p : Nat → Prop)
    (d512 : (p 64) → (p 68) → (p 91) → False)
    (d31 : (p 37) → (p 41) → (p 91) → False)
    (d16 : (¬ p 64) → (¬ p 69) → (¬ p 92) → False)
    (d3 : (¬ p 34) → (¬ p 37) → (¬ p 51) → False)
    (d429 : (p 51) → (p 56) → (p 92) → False)
    : (p 91) → (¬ p 34) → (p 41) → (p 68) → (¬ p 69) → (p 56) → False := by
  intro a0 a1 a2 a3 a4 a5
  have v0 : ¬ p 64 := (fun u => d512 u a3 a0)
  have v1 : ¬ p 37 := (fun u => d31 u a2 a0)
  have v2 : p 92 := Classical.byContradiction (fun u => d16 v0 a4 u)
  have v3 : p 51 := Classical.byContradiction (fun u => d3 a1 v1 u)
  exact d429 v3 a5 v2

theorem c646 (p : Nat → Prop)
    (d512 : (p 64) → (p 68) → (p 91) → False)
    (d633 : (¬ p 24) → (p 91) → (¬ p 22) → (¬ p 26) → False)
    (d16 : (¬ p 64) → (¬ p 69) → (¬ p 92) → False)
    (d30 : (p 22) → (p 27) → (p 92) → False)
    : (p 91) → (¬ p 24) → (¬ p 26) → (p 68) → (¬ p 69) → (p 27) → False := by
  intro a0 a1 a2 a3 a4 a5
  have v0 : ¬ p 64 := (fun u => d512 u a3 a0)
  have v1 : p 22 := Classical.byContradiction (fun u => d633 a1 a0 u a2)
  have v2 : p 92 := Classical.byContradiction (fun u => d16 v0 a4 u)
  exact d30 v1 a5 v2

theorem c647 (p : Nat → Prop)
    (d32 : (p 4) → (p 6) → (p 64) → False)
    (d418 : (p 4) → (p 7) → (p 65) → False)
    (d21 : (p 64) → (p 65) → (p 88) → False)
    (d207 : (¬ p 6) → (¬ p 7) → (¬ p 88) → False)
    : (p 65) → (p 64) → (p 4) → False := by
  intro a0 a1 a2
  have v0 : ¬ p 6 := (fun u => d32 a2 u a1)
  have v1 : ¬ p 7 := (fun u => d418 a2 u a0)
  have v2 : ¬ p 88 := (fun u => d21 a1 a0 u)
  exact d207 v0 v1 v2

theorem c650 (p : Nat → Prop)
    (d636 : (p 101) → (p 127) → (p 68) → (¬ p 70) → False)
    (d530 : (p 68) → (p 70) → (p 127) → False)
    : (p 127) → (p 101) → (p 68) → False := by
  intro a0 a1 a2
  have v0 : p 70 := Classical.byContradiction (fun u => d636 a1 a0 a2 u)
  exact d530 a2 v0 a0

theorem c651 (p : Nat → Prop)
    (d571 : (p 100) → (p 101) → (p 118) → False)
    (d324 : (p 7) → (p 9) → (p 100) → False)
    (d564 : (¬ p 9) → (¬ p 10) → (¬ p 118) → False)
    : (p 100) → (p 7) → (p 101) → (¬ p 10) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 118 := (fun u => d571 a0 a2 u)
  have v1 : ¬ p 9 := (fun u => d324 a1 u a0)
  exact d564 v1 a3 v0

theorem c652 (p : Nat → Prop)
    (d95 : (p 88) → (p 89) → (p 99) → False)
    (d155 : (p 88) → (p 97) → (p 107) → False)
    (d476 : (p 89) → (p 97) → (p 116) → False)
    (d83 : (¬ p 99) → (¬ p 107) → (¬ p 116) → False)
    : (p 97) → (p 88) → (p 89) → False := by
  intro a0 a1 a2
  have v0 : ¬ p 99 := (fun u => d95 a1 a2 u)
  have v1 : ¬ p 107 := (fun u => d155 a1 a0 u)
  have v2 : ¬ p 116 := (fun u => d476 a2 a0 u)
  exact d83 v0 v1 v2

theorem c653 (p : Nat → Prop)
    (d386 : (p 2) → (p 8) → (p 39) → False)
    (d423 : (p 8) → (p 11) → (p 111) → False)
    (d518 : (¬ p 39) → (¬ p 42) → (¬ p 111) → False)
    : (p 8) → (p 2) → (¬ p 42) → (p 11) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 39 := (fun u => d386 a1 a0 u)
  have v1 : ¬ p 111 := (fun u => d423 a0 a3 u)
  exact d518 v0 a2 v1

theorem c658 (p : Nat → Prop)
    (d91 : (p 11) → (p 15) → (p 136) → False)
    (d120 : (p 3) → (p 11) → (p 56) → False)
    (d48 : (p 3) → (p 15) → (p 60) → False)
    (d506 : (¬ p 56) → (¬ p 60) → (¬ p 136) → False)
    : (p 3) → (p 11) → (p 15) → False := by
  intro a0 a1 a2
  have v0 : ¬ p 136 := (fun u => d91 a1 a2 u)
  have v1 : ¬ p 56 := (fun u => d120 a0 a1 u)
  have v2 : ¬ p 60 := (fun u => d48 a0 a2 u)
  exact d506 v1 v2 v0

theorem c659 (p : Nat → Prop)
    (d208 : (p 2) → (p 4) → (p 35) → False)
    (d647 : (p 65) → (p 64) → (p 4) → False)
    (d259 : (¬ p 35) → (¬ p 38) → (¬ p 65) → False)
    : (p 4) → (p 64) → (¬ p 38) → (p 2) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 35 := (fun u => d208 a3 a0 u)
  have v1 : ¬ p 65 := (fun u => d647 u a1 a0)
  exact d259 v0 a2 v1

theorem c661 (p : Nat → Prop)
    (d452 : (p 2) → (p 6) → (p 37) → False)
    (d536 : (p 6) → (p 9) → (p 90) → False)
    (d10 : (¬ p 37) → (¬ p 40) → (¬ p 90) → False)
    : (p 6) → (p 9) → (¬ p 40) → (p 2) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 37 := (fun u => d452 a3 a0 u)
  have v1 : ¬ p 90 := (fun u => d536 a0 a1 u)
  exact d10 v0 a2 v1

theorem c662 (p : Nat → Prop)
    (d60 : (p 81) → (p 86) → (p 137) → False)
    (d426 : (p 86) → (p 87) → (p 153) → False)
    (d561 : (¬ p 81) → (¬ p 87) → (¬ p 138) → False)
    : (p 86) → (p 137) → (p 153) → (¬ p 138) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 81 := (fun u => d60 u a0 a1)
  have v1 : ¬ p 87 := (fun u => d426 a0 u a2)
  exact d561 v0 v1 a3

theorem c663 (p : Nat → Prop)
    (d78 : (p 63) → (p 65) → (p 77) → False)
    (d370 : (p 5) → (p 7) → (p 77) → False)
    (d20 : (¬ p 4) → (¬ p 5) → (¬ p 63) → False)
    : (p 77) → (p 7) → (p 65) → (¬ p 4) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 63 := (fun u => d78 u a2 a0)
  have v1 : ¬ p 5 := (fun u => d370 u a1 a0)
  exact d20 a3 v1 v0

theorem c664 (p : Nat → Prop)
    (d15 : (¬ p 77) → (¬ p 83) → (¬ p 104) → False)
    (d75 : (¬ p 21) → (¬ p 23) → (¬ p 77) → False)
    (d226 : (p 79) → (p 83) → (p 121) → False)
    (d459 : (p 21) → (p 31) → (p 85) → False)
    (d239 : (¬ p 79) → (¬ p 85) → (¬ p 123) → False)
    : (¬ p 77) → (¬ p 104) → (p 31) → (¬ p 123) → (p 121) → (¬ p 23) → False := by
  intro a0 a1 a2 a3 a4 a5
  have v0 : p 83 := Classical.byContradiction (fun u => d15 a0 u a1)
  have v1 : p 21 := Classical.byContradiction (fun u => d75 u a5 a0)
  have v2 : ¬ p 79 := (fun u => d226 u v0 a4)
  have v3 : ¬ p 85 := (fun u => d459 v1 a2 u)
  exact d239 v2 v3 a3

theorem c666 (p : Nat → Prop)
    (d435 : (p 65) → (p 66) → (p 99) → False)
    (d157 : (p 99) → (p 104) → (p 113) → False)
    (d488 : (p 65) → (p 71) → (p 104) → False)
    (d384 : (¬ p 66) → (¬ p 71) → (¬ p 113) → False)
    : (p 104) → (p 99) → (p 65) → False := by
  intro a0 a1 a2
  have v0 : ¬ p 66 := (fun u => d435 a2 u a1)
  have v1 : ¬ p 113 := (fun u => d157 a1 a0 u)
  have v2 : ¬ p 71 := (fun u => d488 a2 u a0)
  exact d384 v0 v2 v1

theorem c668 (p : Nat → Prop)
    (d357 : (p 37) → (p 39) → (p 89) → False)
    (d55 : (p 18) → (p 22) → (p 37) → False)
    (d127 : (p 18) → (p 24) → (p 39) → False)
    (d400 : (¬ p 22) → (¬ p 24) → (¬ p 89) → False)
    : (p 18) → (p 39) → (p 37) → False := by
  intro a0 a1 a2
  have v0 : ¬ p 89 := (fun u => d357 a2 a1 u)
  have v1 : ¬ p 22 := (fun u => d55 a0 u a2)
  have v2 : ¬ p 24 := (fun u => d127 a0 u a1)
  exact d400 v1 v2 v0

theorem c669 (p : Nat → Prop)
    (d170 : (¬ p 1) → (¬ p 2) → (¬ p 18) → False)
    (d508 : (¬ p 18) → (¬ p 20) → (¬ p 35) → False)
    (d477 : (p 1) → (p 6) → (p 22) → False)
    (d330 : (p 35) → (p 37) → (p 64) → False)
    (d270 : (¬ p 20) → (¬ p 22) → (¬ p 64) → False)
    : (¬ p 18) → (p 37) → (¬ p 2) → (¬ p 20) → (p 6) → False := by
  intro a0 a1 a2 a3 a4
  have v0 : p 1 := Classical.byContradiction (fun u => d170 u a2 a0)
  have v1 : p 35 := Classical.byContradiction (fun u => d508 a0 a3 u)
  have v2 : ¬ p 22 := (fun u => d477 v0 a4 u)
  have v3 : ¬ p 64 := (fun u => d330 v1 a1 u)
  exact d270 a3 v2 v3

theorem c671 (p : Nat → Prop)
    (d462 : (p 34) → (p 35) → (p 49) → False)
    (d105 : (p 49) → (p 51) → (p 64) → False)
    (d3 : (¬ p 34) → (¬ p 37) → (¬ p 51) → False)
    : (p 49) → (p 64) → (p 35) → (¬ p 37) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 34 := (fun u => d462 u a2 a0)
  have v1 : ¬ p 51 := (fun u => d105 a0 u a1)
  exact d3 v0 a3 v1

theorem c674 (p : Nat → Prop)
    (d572 : (p 77) → (p 78) → (p 99) → False)
    (d404 : (p 78) → (p 83) → (p 113) → False)
    (d157 : (p 99) → (p 104) → (p 113) → False)
    (d15 : (¬ p 77) → (¬ p 83) → (¬ p 104) → False)
    : (p 113) → (p 99) → (p 78) → False := by
  intro a0 a1 a2
  have v0 : ¬ p 77 := (fun u => d572 u a2 a1)
  have v1 : ¬ p 83 := (fun u => d404 a2 u a0)
  have v2 : ¬ p 104 := (fun u => d157 a1 u a0)
  exact d15 v0 v1 v2

theorem c675 (p : Nat → Prop)
    (d334 : (p 78) → (p 79) → (p 109) → False)
    (d507 : (p 109) → (p 115) → (p 123) → False)
    (d293 : (p 78) → (p 85) → (p 115) → False)
    (d239 : (¬ p 79) → (¬ p 85) → (¬ p 123) → False)
    : (p 115) → (p 109) → (p 78) → False := by
  intro a0 a1 a2
  have v0 : ¬ p 79 := (fun u => d334 a2 u a1)
  have v1 : ¬ p 123 := (fun u => d507 a1 a0 u)
  have v2 : ¬ p 85 := (fun u => d293 a2 u a0)
  exact d239 v0 v2 v1

theorem c677 (p : Nat → Prop)
    (d147 : (p 5) → (p 10) → (p 80) → False)
    (d281 : (p 4) → (p 10) → (p 68) → False)
    (d74 : (¬ p 63) → (¬ p 68) → (¬ p 80) → False)
    : (p 10) → (¬ p 63) → (p 4) → (p 5) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 80 := (fun u => d147 a3 a0 u)
  have v1 : ¬ p 68 := (fun u => d281 a2 a0 u)
  exact d74 a1 v1 v0

theorem c679 (p : Nat → Prop)
    (d412 : (p 73) → (p 74) → (p 151) → False)
    (d131 : (p 148) → (p 149) → (p 151) → False)
    (d589 : (¬ p 69) → (¬ p 74) → (¬ p 137) → False)
    (d145 : (¬ p 30) → (¬ p 32) → (¬ p 149) → False)
    (d187 : (p 27) → (p 32) → (p 137) → False)
    : (p 151) → (p 148) → (p 27) → (¬ p 69) → (¬ p 30) → (p 73) → False := by
  intro a0 a1 a2 a3 a4 a5
  have v0 : ¬ p 74 := (fun u => d412 a5 u a0)
  have v1 : ¬ p 149 := (fun u => d131 a1 u a0)
  have v2 : p 137 := Classical.byContradiction (fun u => d589 a3 v0 u)
  have v3 : p 32 := Classical.byContradiction (fun u => d145 a4 u v1)
  exact d187 a2 v3 v2

theorem c681 (p : Nat → Prop)
    (d101 : (p 35) → (p 42) → (p 69) → False)
    (d392 : (p 66) → (p 69) → (p 111) → False)
    (d518 : (¬ p 39) → (¬ p 42) → (¬ p 111) → False)
    : (p 69) → (p 35) → (¬ p 39) → (p 66) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 42 := (fun u => d101 a1 u a0)
  have v1 : ¬ p 111 := (fun u => d392 a3 a0 u)
  exact d518 a2 v0 v1

theorem c682 (p : Nat → Prop)
    (d187 : (p 27) → (p 32) → (p 137) → False)
    (d478 : (p 20) → (p 32) → (p 74) → False)
    (d589 : (¬ p 69) → (¬ p 74) → (¬ p 137) → False)
    : (p 32) → (p 20) → (p 27) → (¬ p 69) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 137 := (fun u => d187 a2 a0 u)
  have v1 : ¬ p 74 := (fun u => d478 a1 a0 u)
  exact d589 a3 v1 v0

theorem c687 (p : Nat → Prop)
    (d212 : (p 126) → (p 128) → (p 134) → False)
    (d566 : (p 91) → (p 92) → (p 126) → False)
    (d88 : (¬ p 41) → (¬ p 44) → (¬ p 128) → False)
    (d444 : (¬ p 51) → (¬ p 55) → (¬ p 91) → False)
    (d559 : (p 34) → (p 41) → (p 55) → False)
    : (p 126) → (p 34) → (¬ p 51) → (p 134) → (p 92) → (¬ p 44) → False := by
  intro a0 a1 a2 a3 a4 a5
  have v0 : ¬ p 128 := (fun u => d212 a0 u a3)
  have v1 : ¬ p 91 := (fun u => d566 u a4 a0)
  have v2 : p 41 := Classical.byContradiction (fun u => d88 u a5 v0)
  have v3 : p 55 := Classical.byContradiction (fun u => d444 a2 u v1)
  exact d559 a1 v2 v3

theorem c691 (p : Nat → Prop)
    (d278 : (p 34) → (p 38) → (p 52) → False)
    (d149 : (p 38) → (p 42) → (p 102) → False)
    (d366 : (¬ p 52) → (¬ p 56) → (¬ p 102) → False)
    : (p 38) → (p 42) → (¬ p 56) → (p 34) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 52 := (fun u => d278 a3 a0 u)
  have v1 : ¬ p 102 := (fun u => d149 a0 a1 u)
  exact d366 v0 a2 v1

theorem c692 (p : Nat → Prop)
    (d325 : (p 65) → (p 74) → (p 107) → False)
    (d551 : (p 66) → (p 74) → (p 116) → False)
    (d435 : (p 65) → (p 66) → (p 99) → False)
    (d83 : (¬ p 99) → (¬ p 107) → (¬ p 116) → False)
    : (p 66) → (p 65) → (p 74) → False := by
  intro a0 a1 a2
  have v0 : ¬ p 107 := (fun u => d325 a1 a2 u)
  have v1 : ¬ p 116 := (fun u => d551 a0 a2 u)
  have v2 : ¬ p 99 := (fun u => d435 a1 a0 u)
  exact d83 v2 v0 v1

theorem c693 (p : Nat → Prop)
    (d90 : (p 53) → (p 60) → (p 115) → False)
    (d356 : (p 51) → (p 53) → (p 89) → False)
    (d203 : (¬ p 89) → (¬ p 96) → (¬ p 115) → False)
    : (p 53) → (p 51) → (¬ p 96) → (p 60) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 115 := (fun u => d90 a0 a3 u)
  have v1 : ¬ p 89 := (fun u => d356 a1 a0 u)
  exact d203 v1 a2 v0

theorem c696 (p : Nat → Prop)
    (d248 : (p 39) → (p 46) → (p 115) → False)
    (d521 : (¬ p 43) → (¬ p 46) → (¬ p 141) → False)
    (d167 : (p 39) → (p 43) → (p 112) → False)
    (d52 : (p 34) → (p 43) → (p 57) → False)
    (d538 : (¬ p 53) → (¬ p 57) → (¬ p 112) → False)
    : (p 39) → (p 34) → (¬ p 141) → (p 115) → (¬ p 53) → False := by
  intro a0 a1 a2 a3 a4
  have v0 : ¬ p 46 := (fun u => d248 a0 u a3)
  have v1 : p 43 := Classical.byContradiction (fun u => d521 u v0 a2)
  have v2 : ¬ p 112 := (fun u => d167 a0 v1 u)
  have v3 : ¬ p 57 := (fun u => d52 a1 v1 u)
  exact d538 a4 v3 v2

theorem c697 (p : Nat → Prop)
    (d418 : (p 4) → (p 7) → (p 65) → False)
    (d663 : (p 77) → (p 7) → (p 65) → (¬ p 4) → False)
    : (p 7) → (p 77) → (p 65) → False := by
  intro a0 a1 a2
  have v0 : ¬ p 4 := (fun u => d418 u a0 a2)
  exact d663 a1 a0 a2 v0

theorem c698 (p : Nat → Prop)
    (d188 : (p 49) → (p 61) → (p 74) → False)
    (d478 : (p 20) → (p 32) → (p 74) → False)
    (d141 : (¬ p 57) → (¬ p 61) → (¬ p 142) → False)
    (d145 : (¬ p 30) → (¬ p 32) → (¬ p 149) → False)
    (d568 : (p 140) → (p 142) → (p 149) → False)
    : (p 74) → (p 140) → (¬ p 57) → (p 49) → (¬ p 30) → (p 20) → False := by
  intro a0 a1 a2 a3 a4 a5
  have v0 : ¬ p 61 := (fun u => d188 a3 u a0)
  have v1 : ¬ p 32 := (fun u => d478 a5 u a0)
  have v2 : p 142 := Classical.byContradiction (fun u => d141 a2 v0 u)
  have v3 : p 149 := Classical.byContradiction (fun u => d145 a4 v1 u)
  exact d568 a1 v2 v3

theorem c700 (p : Nat → Prop)
    (d375 : (p 18) → (p 19) → (p 34) → False)
    (d76 : (p 34) → (p 36) → (p 50) → False)
    (d156 : (p 18) → (p 21) → (p 36) → False)
    (d381 : (¬ p 19) → (¬ p 21) → (¬ p 50) → False)
    : (p 36) → (p 18) → (p 34) → False := by
  intro a0 a1 a2
  have v0 : ¬ p 19 := (fun u => d375 a1 u a2)
  have v1 : ¬ p 50 := (fun u => d76 a2 a0 u)
  have v2 : ¬ p 21 := (fun u => d156 a1 u a0)
  exact d381 v0 v2 v1

theorem c701 (p : Nat → Prop)
    (d78 : (p 63) → (p 65) → (p 77) → False)
    (d20 : (¬ p 4) → (¬ p 5) → (¬ p 63) → False)
    (d572 : (p 77) → (p 78) → (p 99) → False)
    (d5 : (p 5) → (p 8) → (p 78) → False)
    (d111 : (¬ p 7) → (¬ p 8) → (¬ p 99) → False)
    : (p 77) → (¬ p 4) → (p 78) → (¬ p 7) → (p 65) → False := by
  intro a0 a1 a2 a3 a4
  have v0 : ¬ p 63 := (fun u => d78 u a4 a0)
  have v1 : p 5 := Classical.byContradiction (fun u => d20 a1 u v0)
  have v2 : ¬ p 99 := (fun u => d572 a0 a2 u)
  have v3 : ¬ p 8 := (fun u => d5 v1 u a2)
  exact d111 a3 v3 v2

theorem c702 (p : Nat → Prop)
    (d207 : (¬ p 6) → (¬ p 7) → (¬ p 88) → False)
    (d201 : (p 21) → (p 24) → (p 78) → False)
    (d75 : (¬ p 21) → (¬ p 23) → (¬ p 77) → False)
    (d572 : (p 77) → (p 78) → (p 99) → False)
    (d45 : (p 76) → (p 77) → (p 88) → False)
    (d111 : (¬ p 7) → (¬ p 8) → (¬ p 99) → False)
    (d213 : (¬ p 5) → (¬ p 6) → (¬ p 76) → False)
    (d5 : (p 5) → (p 8) → (p 78) → False)
    : (p 78) → (p 24) → (¬ p 6) → (¬ p 7) → (¬ p 23) → False := by
  intro a0 a1 a2 a3 a4
  have v0 : p 88 := Classical.byContradiction (fun u => d207 a2 a3 u)
  have v1 : ¬ p 21 := (fun u => d201 u a1 a0)
  have v2 : p 77 := Classical.byContradiction (fun u => d75 v1 a4 u)
  have v3 : ¬ p 99 := (fun u => d572 v2 a0 u)
  have v4 : ¬ p 76 := (fun u => d45 u v2 v0)
  have v5 : p 8 := Classical.byContradiction (fun u => d111 a3 u v3)
  have v6 : p 5 := Classical.byContradiction (fun u => d213 u a2 v4)
  exact d5 v6 v5 a0

theorem c703 (p : Nat → Prop)
    (d503 : (p 5) → (p 9) → (p 79) → False)
    (d84 : (p 3) → (p 9) → (p 54) → False)
    (d245 : (p 3) → (p 5) → (p 50) → False)
    (d235 : (¬ p 50) → (¬ p 54) → (¬ p 79) → False)
    : (p 3) → (p 9) → (p 5) → False := by
  intro a0 a1 a2
  have v0 : ¬ p 79 := (fun u => d503 a2 a1 u)
  have v1 : ¬ p 54 := (fun u => d84 a0 a1 u)
  have v2 : ¬ p 50 := (fun u => d245 a0 a2 u)
  exact d235 v2 v1 v0

theorem c705 (p : Nat → Prop)
    (d53 : (¬ p 10) → (¬ p 11) → (¬ p 126) → False)
    (d564 : (¬ p 9) → (¬ p 10) → (¬ p 118) → False)
    (d289 : (p 118) → (p 119) → (p 126) → False)
    : (¬ p 10) → (p 119) → (¬ p 9) → (¬ p 11) → False := by
  intro a0 a1 a2 a3
  have v0 : p 126 := Classical.byContradiction (fun u => d53 a0 a3 u)
  have v1 : p 118 := Classical.byContradiction (fun u => d564 a2 a0 u)
  exact d289 v1 a1 v0

theorem c706 (p : Nat → Prop)
    (d185 : (p 49) → (p 59) → (p 72) → False)
    (d261 : (p 68) → (p 72) → (p 129) → False)
    (d583 : (p 49) → (p 55) → (p 68) → False)
    (d560 : (¬ p 55) → (¬ p 59) → (¬ p 129) → False)
    : (p 68) → (p 72) → (p 49) → False := by
  intro a0 a1 a2
  have v0 : ¬ p 59 := (fun u => d185 a2 u a1)
  have v1 : ¬ p 129 := (fun u => d261 a0 a1 u)
  have v2 : ¬ p 55 := (fun u => d583 a2 u a0)
  exact d560 v2 v0 v1

theorem c709 (p : Nat → Prop)
    (d503 : (p 5) → (p 9) → (p 79) → False)
    (d519 : (p 79) → (p 80) → (p 118) → False)
    (d147 : (p 5) → (p 10) → (p 80) → False)
    (d564 : (¬ p 9) → (¬ p 10) → (¬ p 118) → False)
    : (p 80) → (p 79) → (p 5) → False := by
  intro a0 a1 a2
  have v0 : ¬ p 9 := (fun u => d503 a2 u a1)
  have v1 : ¬ p 118 := (fun u => d519 a1 a0 u)
  have v2 : ¬ p 10 := (fun u => d147 a2 u a0)
  exact d564 v0 v2 v1

theorem c710 (p : Nat → Prop)
    (d52 : (p 34) → (p 43) → (p 57) → False)
    (d468 : (p 19) → (p 28) → (p 57) → False)
    (d173 : (¬ p 40) → (¬ p 43) → (¬ p 120) → False)
    (d427 : (¬ p 28) → (¬ p 30) → (¬ p 140) → False)
    (d255 : (p 120) → (p 122) → (p 140) → False)
    : (p 57) → (¬ p 40) → (p 19) → (¬ p 30) → (p 122) → (p 34) → False := by
  intro a0 a1 a2 a3 a4 a5
  have v0 : ¬ p 43 := (fun u => d52 a5 u a0)
  have v1 : ¬ p 28 := (fun u => d468 a2 u a0)
  have v2 : p 120 := Classical.byContradiction (fun u => d173 a1 v0 u)
  have v3 : p 140 := Classical.byContradiction (fun u => d427 v1 a3 u)
  exact d255 v2 a4 v3

theorem c711 (p : Nat → Prop)
    (d255 : (p 120) → (p 122) → (p 140) → False)
    (d396 : (p 25) → (p 28) → (p 120) → False)
    (d427 : (¬ p 28) → (¬ p 30) → (¬ p 140) → False)
    : (p 120) → (¬ p 30) → (p 25) → (p 122) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 140 := (fun u => d255 a0 a3 u)
  have v1 : ¬ p 28 := (fun u => d396 a2 u a0)
  exact d427 v1 a1 v0

theorem c713 (p : Nat → Prop)
    (d167 : (p 39) → (p 43) → (p 112) → False)
    (d422 : (p 111) → (p 112) → (p 133) → False)
    (d285 : (p 42) → (p 43) → (p 133) → False)
    (d518 : (¬ p 39) → (¬ p 42) → (¬ p 111) → False)
    : (p 133) → (p 112) → (p 43) → False := by
  intro a0 a1 a2
  have v0 : ¬ p 39 := (fun u => d167 u a2 a1)
  have v1 : ¬ p 111 := (fun u => d422 u a1 a0)
  have v2 : ¬ p 42 := (fun u => d285 u a2 a0)
  exact d518 v0 v2 v1

theorem c714 (p : Nat → Prop)
    (d217 : (p 79) → (p 84) → (p 122) → False)
    (d112 : (p 109) → (p 114) → (p 122) → False)
    (d334 : (p 78) → (p 79) → (p 109) → False)
    (d125 : (¬ p 78) → (¬ p 84) → (¬ p 114) → False)
    : (p 109) → (p 79) → (p 122) → False := by
  intro a0 a1 a2
  have v0 : ¬ p 84 := (fun u => d217 a1 u a2)
  have v1 : ¬ p 114 := (fun u => d112 a0 u a2)
  have v2 : ¬ p 78 := (fun u => d334 u a1 a0)
  exact d125 v2 v0 v1

theorem c716 (p : Nat → Prop)
    (d225 : (p 18) → (p 25) → (p 40) → False)
    (d238 : (p 2) → (p 9) → (p 40) → False)
    (d258 : (p 1) → (p 9) → (p 25) → False)
    (d170 : (¬ p 1) → (¬ p 2) → (¬ p 18) → False)
    : (p 9) → (p 40) → (p 25) → False := by
  intro a0 a1 a2
  have v0 : ¬ p 18 := (fun u => d225 u a2 a1)
  have v1 : ¬ p 2 := (fun u => d238 u a0 a1)
  have v2 : ¬ p 1 := (fun u => d258 u a0 a2)
  exact d170 v2 v1 v0

theorem c718 (p : Nat → Prop)
    (d489 : (p 20) → (p 24) → (p 66) → False)
    (d359 : (p 20) → (p 26) → (p 68) → False)
    (d391 : (p 66) → (p 68) → (p 110) → False)
    (d341 : (¬ p 24) → (¬ p 26) → (¬ p 110) → False)
    : (p 68) → (p 66) → (p 20) → False := by
  intro a0 a1 a2
  have v0 : ¬ p 24 := (fun u => d489 a2 u a1)
  have v1 : ¬ p 26 := (fun u => d359 a2 u a0)
  have v2 : ¬ p 110 := (fun u => d391 a1 a0 u)
  exact d341 v0 v1 v2

theorem c719 (p : Nat → Prop)
    (d222 : (p 20) → (p 23) → (p 65) → False)
    (d78 : (p 63) → (p 65) → (p 77) → False)
    (d75 : (¬ p 21) → (¬ p 23) → (¬ p 77) → False)
    : (p 65) → (p 63) → (¬ p 21) → (p 20) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 23 := (fun u => d222 a3 u a0)
  have v1 : ¬ p 77 := (fun u => d78 a1 a0 u)
  exact d75 a2 v0 v1

theorem c720 (p : Nat → Prop)
    (d537 : (p 36) → (p 37) → (p 76) → False)
    (d122 : (p 50) → (p 51) → (p 76) → False)
    (d3 : (¬ p 34) → (¬ p 37) → (¬ p 51) → False)
    : (p 76) → (p 36) → (p 50) → (¬ p 34) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 37 := (fun u => d537 a1 u a0)
  have v1 : ¬ p 51 := (fun u => d122 a2 u a0)
  exact d3 a3 v0 v1

theorem c724 (p : Nat → Prop)
    (d581 : (p 64) → (p 70) → (p 93) → False)
    (d200 : (p 88) → (p 93) → (p 103) → False)
    (d154 : (¬ p 65) → (¬ p 70) → (¬ p 103) → False)
    : (p 93) → (p 88) → (¬ p 65) → (p 64) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 70 := (fun u => d581 a3 u a0)
  have v1 : ¬ p 103 := (fun u => d200 a1 a0 u)
  exact d154 a2 v0 v1

theorem c726 (p : Nat → Prop)
    (d519 : (p 79) → (p 80) → (p 118) → False)
    (d430 : (p 80) → (p 85) → (p 130) → False)
    (d543 : (p 118) → (p 123) → (p 130) → False)
    (d239 : (¬ p 79) → (¬ p 85) → (¬ p 123) → False)
    : (p 130) → (p 118) → (p 80) → False := by
  intro a0 a1 a2
  have v0 : ¬ p 79 := (fun u => d519 u a2 a1)
  have v1 : ¬ p 85 := (fun u => d430 a2 u a0)
  have v2 : ¬ p 123 := (fun u => d543 a1 u a0)
  exact d239 v0 v1 v2

theorem c727 (p : Nat → Prop)
    (d296 : (p 14) → (p 16) → (p 149) → False)
    (d220 : (p 8) → (p 16) → (p 116) → False)
    (d145 : (¬ p 30) → (¬ p 32) → (¬ p 149) → False)
    (d83 : (¬ p 99) → (¬ p 107) → (¬ p 116) → False)
    (d524 : (p 23) → (p 32) → (p 107) → False)
    : (p 16) → (¬ p 30) → (¬ p 99) → (p 23) → (p 14) → (p 8) → False := by
  intro a0 a1 a2 a3 a4 a5
  have v0 : ¬ p 149 := (fun u => d296 a4 a0 u)
  have v1 : ¬ p 116 := (fun u => d220 a5 a0 u)
  have v2 : p 32 := Classical.byContradiction (fun u => d145 a1 u v0)
  have v3 : p 107 := Classical.byContradiction (fun u => d83 a2 u v1)
  exact d524 a3 v2 v3

theorem c728 (p : Nat → Prop)
    (d412 : (p 73) → (p 74) → (p 151) → False)
    (d547 : (p 136) → (p 137) → (p 151) → False)
    (d589 : (¬ p 69) → (¬ p 74) → (¬ p 137) → False)
    : (p 151) → (p 136) → (p 73) → (¬ p 69) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 74 := (fun u => d412 a2 u a0)
  have v1 : ¬ p 137 := (fun u => d547 a1 u a0)
  exact d589 a3 v0 v1

theorem c729 (p : Nat → Prop)
    (d463 : (¬ p 44) → (¬ p 47) → (¬ p 146) → False)
    (d88 : (¬ p 41) → (¬ p 44) → (¬ p 128) → False)
    (d287 : (p 58) → (p 61) → (p 146) → False)
    (d94 : (p 118) → (p 121) → (p 128) → False)
    (d575 : (¬ p 54) → (¬ p 58) → (¬ p 121) → False)
    : (¬ p 44) → (p 61) → (¬ p 41) → (¬ p 47) → (¬ p 54) → (p 118) → False := by
  intro a0 a1 a2 a3 a4 a5
  have v0 : p 146 := Classical.byContradiction (fun u => d463 a0 a3 u)
  have v1 : p 128 := Classical.byContradiction (fun u => d88 a2 a0 u)
  have v2 : ¬ p 58 := (fun u => d287 u a1 v0)
  have v3 : ¬ p 121 := (fun u => d94 a5 u v1)
  exact d575 a4 v2 v3

theorem c731 (p : Nat → Prop)
    (d71 : (p 20) → (p 29) → (p 71) → False)
    (d384 : (¬ p 66) → (¬ p 71) → (¬ p 113) → False)
    (d292 : (p 24) → (p 29) → (p 113) → False)
    : (p 29) → (p 24) → (p 20) → (¬ p 66) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 71 := (fun u => d71 a2 a0 u)
  have v1 : p 113 := Classical.byContradiction (fun u => d384 a3 v0 u)
  exact d292 a1 a0 v1

theorem c733 (p : Nat → Prop)
    (d75 : (¬ p 21) → (¬ p 23) → (¬ p 77) → False)
    (d702 : (p 78) → (p 24) → (¬ p 6) → (¬ p 7) → (¬ p 23) → False)
    (d299 : (p 21) → (p 22) → (p 76) → False)
    (d400 : (¬ p 22) → (¬ p 24) → (¬ p 89) → False)
    : (¬ p 23) → (¬ p 7) → (¬ p 77) → (p 78) → (¬ p 89) → (¬ p 6) → (p 76) → False := by
  intro a0 a1 a2 a3 a4 a5 a6
  have v0 : p 21 := Classical.byContradiction (fun u => d75 u a0 a2)
  have v1 : ¬ p 24 := (fun u => d702 a3 u a5 a1 a0)
  have v2 : ¬ p 22 := (fun u => d299 v0 u a6)
  exact d400 v2 v1 a4

theorem c735 (p : Nat → Prop)
    (d127 : (p 18) → (p 24) → (p 39) → False)
    (d102 : (p 19) → (p 24) → (p 53) → False)
    (d62 : (p 3) → (p 8) → (p 53) → False)
    (d381 : (¬ p 19) → (¬ p 21) → (¬ p 50) → False)
    (d505 : (¬ p 2) → (¬ p 3) → (¬ p 34) → False)
    (d250 : (p 50) → (p 53) → (p 78) → False)
    (d700 : (p 36) → (p 18) → (p 34) → False)
    (d58 : (¬ p 36) → (¬ p 39) → (¬ p 78) → False)
    : (p 53) → (p 18) → (¬ p 2) → (¬ p 21) → (p 24) → (p 8) → False := by
  intro a0 a1 a2 a3 a4 a5
  have v0 : ¬ p 39 := (fun u => d127 a1 a4 u)
  have v1 : ¬ p 19 := (fun u => d102 u a4 a0)
  have v2 : ¬ p 3 := (fun u => d62 u a5 a0)
  have v3 : p 50 := Classical.byContradiction (fun u => d381 v1 a3 u)
  have v4 : p 34 := Classical.byContradiction (fun u => d505 a2 v2 u)
  have v5 : ¬ p 78 := (fun u => d250 v3 a0 u)
  have v6 : ¬ p 36 := (fun u => d700 u a1 v4)
  exact d58 v6 v0 v5

theorem c738 (p : Nat → Prop)
    (d227 : (p 40) → (p 42) → (p 119) → False)
    (d241 : (p 90) → (p 92) → (p 119) → False)
    (d354 : (p 37) → (p 42) → (p 92) → False)
    (d10 : (¬ p 37) → (¬ p 40) → (¬ p 90) → False)
    : (p 92) → (p 119) → (p 42) → False := by
  intro a0 a1 a2
  have v0 : ¬ p 40 := (fun u => d227 u a2 a1)
  have v1 : ¬ p 90 := (fun u => d241 u a0 a1)
  have v2 : ¬ p 37 := (fun u => d354 u a2 a0)
  exact d10 v2 v0 v1

theorem c739 (p : Nat → Prop)
    (d547 : (p 136) → (p 137) → (p 151) → False)
    (d116 : (p 119) → (p 124) → (p 137) → False)
    (d153 : (¬ p 15) → (¬ p 16) → (¬ p 151) → False)
    (d43 : (¬ p 90) → (¬ p 97) → (¬ p 124) → False)
    (d499 : (p 6) → (p 16) → (p 97) → False)
    : (p 137) → (p 6) → (¬ p 90) → (p 119) → (¬ p 15) → (p 136) → False := by
  intro a0 a1 a2 a3 a4 a5
  have v0 : ¬ p 151 := (fun u => d547 a5 a0 u)
  have v1 : ¬ p 124 := (fun u => d116 a3 u a0)
  have v2 : p 16 := Classical.byContradiction (fun u => d153 a4 u v0)
  have v3 : p 97 := Classical.byContradiction (fun u => d43 a2 u v1)
  exact d499 a1 v2 v3

theorem c740 (p : Nat → Prop)
    (d70 : (p 8) → (p 12) → (p 112) → False)
    (d329 : (p 3) → (p 12) → (p 57) → False)
    (d538 : (¬ p 53) → (¬ p 57) → (¬ p 112) → False)
    : (p 12) → (p 8) → (p 3) → (¬ p 53) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 112 := (fun u => d70 a1 a0 u)
  have v1 : ¬ p 57 := (fun u => d329 a2 a0 u)
  exact d538 a3 v1 v0

theorem c742 (p : Nat → Prop)
    (d393 : (p 11) → (p 13) → (p 134) → False)
    (d443 : (p 119) → (p 121) → (p 134) → False)
    (d92 : (¬ p 12) → (¬ p 13) → (¬ p 139) → False)
    (d575 : (¬ p 54) → (¬ p 58) → (¬ p 121) → False)
    (d302 : (p 57) → (p 58) → (p 139) → False)
    : (p 134) → (¬ p 54) → (p 11) → (p 119) → (p 57) → (¬ p 12) → False := by
  intro a0 a1 a2 a3 a4 a5
  have v0 : ¬ p 13 := (fun u => d393 a2 u a0)
  have v1 : ¬ p 121 := (fun u => d443 a3 u a0)
  have v2 : p 139 := Classical.byContradiction (fun u => d92 a5 v0 u)
  have v3 : p 58 := Classical.byContradiction (fun u => d575 a1 u v1)
  exact d302 a4 v3 v2

theorem c743 (p : Nat → Prop)
    (d477 : (p 1) → (p 6) → (p 22) → False)
    (d46 : (p 6) → (p 8) → (p 89) → False)
    (d400 : (¬ p 22) → (¬ p 24) → (¬ p 89) → False)
    : (p 6) → (¬ p 24) → (p 1) → (p 8) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 22 := (fun u => d477 a2 a0 u)
  have v1 : ¬ p 89 := (fun u => d46 a0 a3 u)
  exact d400 v0 a1 v1

theorem c744 (p : Nat → Prop)
    (d155 : (p 88) → (p 97) → (p 107) → False)
    (d83 : (¬ p 99) → (¬ p 107) → (¬ p 116) → False)
    (d220 : (p 8) → (p 16) → (p 116) → False)
    (d153 : (¬ p 15) → (¬ p 16) → (¬ p 151) → False)
    (d585 : (p 96) → (p 97) → (p 151) → False)
    (d41 : (p 115) → (p 116) → (p 151) → False)
    (d203 : (¬ p 89) → (¬ p 96) → (¬ p 115) → False)
    : (p 97) → (¬ p 89) → (p 88) → (¬ p 15) → (p 8) → (¬ p 99) → False := by
  intro a0 a1 a2 a3 a4 a5
  have v0 : ¬ p 107 := (fun u => d155 a2 a0 u)
  have v1 : p 116 := Classical.byContradiction (fun u => d83 a5 v0 u)
  have v2 : ¬ p 16 := (fun u => d220 a4 u v1)
  have v3 : p 151 := Classical.byContradiction (fun u => d153 a3 v2 u)
  have v4 : ¬ p 96 := (fun u => d585 u a0 v3)
  have v5 : ¬ p 115 := (fun u => d41 u v1 v3)
  exact d203 a1 v4 v5

theorem c746 (p : Nat → Prop)
    (d402 : (p 100) → (p 104) → (p 121) → False)
    (d264 : (p 77) → (p 79) → (p 100) → False)
    (d226 : (p 79) → (p 83) → (p 121) → False)
    (d15 : (¬ p 77) → (¬ p 83) → (¬ p 104) → False)
    : (p 79) → (p 100) → (p 121) → False := by
  intro a0 a1 a2
  have v0 : ¬ p 104 := (fun u => d402 a1 u a2)
  have v1 : ¬ p 77 := (fun u => d264 u a0 a1)
  have v2 : ¬ p 83 := (fun u => d226 a0 u a2)
  exact d15 v1 v2 v0

theorem c747 (p : Nat → Prop)
    (d245 : (p 3) → (p 5) → (p 50) → False)
    (d42 : (p 49) → (p 50) → (p 63) → False)
    (d20 : (¬ p 4) → (¬ p 5) → (¬ p 63) → False)
    : (p 50) → (¬ p 4) → (p 49) → (p 3) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 5 := (fun u => d245 a3 u a0)
  have v1 : ¬ p 63 := (fun u => d42 a2 a0 u)
  exact d20 a1 v0 v1

theorem c748 (p : Nat → Prop)
    (d575 : (¬ p 54) → (¬ p 58) → (¬ p 121) → False)
    (d235 : (¬ p 50) → (¬ p 54) → (¬ p 79) → False)
    (d262 : (p 25) → (p 29) → (p 121) → False)
    (d746 : (p 79) → (p 100) → (p 121) → False)
    (d442 : (¬ p 23) → (¬ p 25) → (¬ p 100) → False)
    : (¬ p 54) → (¬ p 58) → (¬ p 23) → (p 29) → (¬ p 50) → False := by
  intro a0 a1 a2 a3 a4
  have v0 : p 121 := Classical.byContradiction (fun u => d575 a0 a1 u)
  have v1 : p 79 := Classical.byContradiction (fun u => d235 a4 a0 u)
  have v2 : ¬ p 25 := (fun u => d262 u a3 v0)
  have v3 : ¬ p 100 := (fun u => d746 v1 u v0)
  exact d442 a2 v2 v3

theorem c750 (p : Nat → Prop)
    (d272 : (p 49) → (p 54) → (p 67) → False)
    (d359 : (p 20) → (p 26) → (p 68) → False)
    (d583 : (p 49) → (p 55) → (p 68) → False)
    (d706 : (p 68) → (p 72) → (p 49) → False)
    (d341 : (¬ p 24) → (¬ p 26) → (¬ p 110) → False)
    (d323 : (¬ p 67) → (¬ p 72) → (¬ p 122) → False)
    (d532 : (p 54) → (p 59) → (p 122) → False)
    (d560 : (¬ p 55) → (¬ p 59) → (¬ p 129) → False)
    (d465 : (p 110) → (p 114) → (p 129) → False)
    (d125 : (¬ p 78) → (¬ p 84) → (¬ p 114) → False)
    (d326 : (p 5) → (p 14) → (p 84) → False)
    (d27 : (¬ p 14) → (¬ p 15) → (¬ p 148) → False)
    (d595 : (p 122) → (p 123) → (p 148) → False)
    (d485 : (p 84) → (p 85) → (p 148) → False)
    (d239 : (¬ p 79) → (¬ p 85) → (¬ p 123) → False)
    : (p 68) → (p 54) → (¬ p 79) → (¬ p 24) → (¬ p 78) → (p 5) → (p 20) → (p 49) → (¬ p 15) → False := by
  intro a0 a1 a2 a3 a4 a5 a6 a7 a8
  have v0 : ¬ p 67 := (fun u => d272 a7 a1 u)
  have v1 : ¬ p 26 := (fun u => d359 a6 u a0)
  have v2 : ¬ p 55 := (fun u => d583 a7 u a0)
  have v3 : ¬ p 72 := (fun u => d706 a0 u a7)
  have v4 : p 110 := Classical.byContradiction (fun u => d341 a3 v1 u)
  have v5 : p 122 := Classical.byContradiction (fun u => d323 v0 v3 u)
  have v6 : ¬ p 59 := (fun u => d532 a1 u v5)
  have v7 : p 129 := Classical.byContradiction (fun u => d560 v2 v6 u)
  have v8 : ¬ p 114 := (fun u => d465 v4 u v7)
  have v9 : p 84 := Classical.byContradiction (fun u => d125 a4 u v8)
  have v10 : ¬ p 14 := (fun u => d326 a5 u v9)
  have v11 : p 148 := Classical.byContradiction (fun u => d27 v10 a8 u)
  have v12 : ¬ p 123 := (fun u => d595 v5 u v11)
  have v13 : ¬ p 85 := (fun u => d485 v9 u v11)
  exact d239 a2 v13 v12

theorem c751 (p : Nat → Prop)
    (d246 : (p 49) → (p 60) → (p 73) → False)
    (d412 : (p 73) → (p 74) → (p 151) → False)
    (d506 : (¬ p 56) → (¬ p 60) → (¬ p 136) → False)
    (d589 : (¬ p 69) → (¬ p 74) → (¬ p 137) → False)
    (d601 : (p 69) → (p 73) → (p 136) → False)
    : (p 73) → (¬ p 137) → (p 49) → (p 151) → (¬ p 56) → False := by
  intro a0 a1 a2 a3 a4
  have v0 : ¬ p 60 := (fun u => d246 a2 u a0)
  have v1 : ¬ p 74 := (fun u => d412 a0 u a3)
  have v2 : p 136 := Classical.byContradiction (fun u => d506 a4 v0 u)
  have v3 : p 69 := Classical.byContradiction (fun u => d589 u v1 a1)
  exact d601 v3 a0 v2

theorem c753 (p : Nat → Prop)
    (d246 : (p 49) → (p 60) → (p 73) → False)
    (d751 : (p 73) → (¬ p 137) → (p 49) → (p 151) → (¬ p 56) → False)
    (d506 : (¬ p 56) → (¬ p 60) → (¬ p 136) → False)
    (d547 : (p 136) → (p 137) → (p 151) → False)
    : (p 73) → (p 49) → (p 151) → (¬ p 56) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 60 := (fun u => d246 a1 u a0)
  have v1 : p 137 := Classical.byContradiction (fun u => d751 a0 u a1 a2 a3)
  have v2 : p 136 := Classical.byContradiction (fun u => d506 a3 v0 u)
  exact d547 v2 v1 a2

theorem c754 (p : Nat → Prop)
    (d74 : (¬ p 63) → (¬ p 68) → (¬ p 80) → False)
    (d138 : (¬ p 68) → (¬ p 73) → (¬ p 130) → False)
    (d147 : (p 5) → (p 10) → (p 80) → False)
    (d726 : (p 130) → (p 118) → (p 80) → False)
    (d564 : (¬ p 9) → (¬ p 10) → (¬ p 118) → False)
    : (¬ p 68) → (¬ p 9) → (p 5) → (¬ p 63) → (¬ p 73) → False := by
  intro a0 a1 a2 a3 a4
  have v0 : p 80 := Classical.byContradiction (fun u => d74 a3 a0 u)
  have v1 : p 130 := Classical.byContradiction (fun u => d138 a0 a4 u)
  have v2 : ¬ p 10 := (fun u => d147 a2 u v0)
  have v3 : ¬ p 118 := (fun u => d726 v1 u v0)
  exact d564 a1 v2 v3

theorem c755 (p : Nat → Prop)
    (d147 : (p 5) → (p 10) → (p 80) → False)
    (d726 : (p 130) → (p 118) → (p 80) → False)
    (d564 : (¬ p 9) → (¬ p 10) → (¬ p 118) → False)
    : (p 80) → (p 130) → (¬ p 9) → (p 5) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 10 := (fun u => d147 a3 u a0)
  have v1 : ¬ p 118 := (fun u => d726 a1 u a0)
  exact d564 a2 v0 v1

theorem c756 (p : Nat → Prop)
    (d459 : (p 21) → (p 31) → (p 85) → False)
    (d424 : (p 21) → (p 25) → (p 79) → False)
    (d114 : (p 25) → (p 31) → (p 123) → False)
    (d239 : (¬ p 79) → (¬ p 85) → (¬ p 123) → False)
    : (p 25) → (p 31) → (p 21) → False := by
  intro a0 a1 a2
  have v0 : ¬ p 85 := (fun u => d459 a2 a1 u)
  have v1 : ¬ p 79 := (fun u => d424 a2 a0 u)
  have v2 : ¬ p 123 := (fun u => d114 a0 a1 u)
  exact d239 v1 v0 v2

theorem c759 (p : Nat → Prop)
    (d27 : (¬ p 14) → (¬ p 15) → (¬ p 148) → False)
    (d494 : (¬ p 13) → (¬ p 14) → (¬ p 144) → False)
    (d485 : (p 84) → (p 85) → (p 148) → False)
    (d113 : (p 113) → (p 114) → (p 144) → False)
    (d125 : (¬ p 78) → (¬ p 84) → (¬ p 114) → False)
    : (¬ p 14) → (p 85) → (p 113) → (¬ p 78) → (¬ p 13) → (¬ p 15) → False := by
  intro a0 a1 a2 a3 a4 a5
  have v0 : p 148 := Classical.byContradiction (fun u => d27 a0 a5 u)
  have v1 : p 144 := Classical.byContradiction (fun u => d494 a4 a0 u)
  have v2 : ¬ p 84 := (fun u => d485 u a1 v0)
  have v3 : ¬ p 114 := (fun u => d113 a2 u v1)
  exact d125 a3 v2 v3

theorem c760 (p : Nat → Prop)
    (d218 : (p 8) → (p 14) → (p 114) → False)
    (d326 : (p 5) → (p 14) → (p 84) → False)
    (d125 : (¬ p 78) → (¬ p 84) → (¬ p 114) → False)
    : (p 14) → (p 8) → (p 5) → (¬ p 78) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 114 := (fun u => d218 a1 a0 u)
  have v1 : ¬ p 84 := (fun u => d326 a2 a0 u)
  exact d125 a3 v1 v0

theorem c761 (p : Nat → Prop)
    (d27 : (¬ p 14) → (¬ p 15) → (¬ p 148) → False)
    (d494 : (¬ p 13) → (¬ p 14) → (¬ p 144) → False)
    (d759 : (¬ p 14) → (p 85) → (p 113) → (¬ p 78) → (¬ p 13) → (¬ p 15) → False)
    (d595 : (p 122) → (p 123) → (p 148) → False)
    (d113 : (p 113) → (p 114) → (p 144) → False)
    (d239 : (¬ p 79) → (¬ p 85) → (¬ p 123) → False)
    (d125 : (¬ p 78) → (¬ p 84) → (¬ p 114) → False)
    (d217 : (p 79) → (p 84) → (p 122) → False)
    : (¬ p 14) → (p 113) → (¬ p 78) → (¬ p 13) → (¬ p 15) → (p 122) → False := by
  intro a0 a1 a2 a3 a4 a5
  have v0 : p 148 := Classical.byContradiction (fun u => d27 a0 a4 u)
  have v1 : p 144 := Classical.byContradiction (fun u => d494 a3 a0 u)
  have v2 : ¬ p 85 := (fun u => d759 a0 u a1 a2 a3 a4)
  have v3 : ¬ p 123 := (fun u => d595 a5 u v0)
  have v4 : ¬ p 114 := (fun u => d113 a1 u v1)
  have v5 : p 79 := Classical.byContradiction (fun u => d239 u v2 v3)
  have v6 : p 84 := Classical.byContradiction (fun u => d125 a2 u v4)
  exact d217 v5 v6 a5

theorem c762 (p : Nat → Prop)
    (d393 : (p 11) → (p 13) → (p 134) → False)
    (d22 : (p 4) → (p 11) → (p 69) → False)
    (d73 : (p 69) → (p 71) → (p 134) → False)
    (d20 : (¬ p 4) → (¬ p 5) → (¬ p 63) → False)
    (d384 : (¬ p 66) → (¬ p 71) → (¬ p 113) → False)
    (d761 : (¬ p 14) → (p 113) → (¬ p 78) → (¬ p 13) → (¬ p 15) → (p 122) → False)
    (d326 : (p 5) → (p 14) → (p 84) → False)
    (d760 : (p 14) → (p 8) → (p 5) → (¬ p 78) → False)
    (d125 : (¬ p 78) → (¬ p 84) → (¬ p 114) → False)
    (d394 : (¬ p 8) → (¬ p 9) → (¬ p 109) → False)
    (d112 : (p 109) → (p 114) → (p 122) → False)
    : (p 69) → (¬ p 78) → (p 11) → (¬ p 66) → (¬ p 63) → (¬ p 15) → (p 122) → (¬ p 9) → (p 134) → False := by
  intro a0 a1 a2 a3 a4 a5 a6 a7 a8
  have v0 : ¬ p 13 := (fun u => d393 a2 u a8)
  have v1 : ¬ p 4 := (fun u => d22 u a2 a0)
  have v2 : ¬ p 71 := (fun u => d73 a0 u a8)
  have v3 : p 5 := Classical.byContradiction (fun u => d20 v1 u a4)
  have v4 : p 113 := Classical.byContradiction (fun u => d384 a3 v2 u)
  have v5 : p 14 := Classical.byContradiction (fun u => d761 u v4 a1 v0 a5 a6)
  have v6 : ¬ p 84 := (fun u => d326 v3 v5 u)
  have v7 : ¬ p 8 := (fun u => d760 v5 u v3 a1)
  have v8 : p 114 := Classical.byContradiction (fun u => d125 a1 v6 u)
  have v9 : p 109 := Classical.byContradiction (fun u => d394 v7 a7 u)
  exact d112 v9 v8 a6

theorem c763 (p : Nat → Prop)
    (d518 : (¬ p 39) → (¬ p 42) → (¬ p 111) → False)
    (d417 : (¬ p 42) → (¬ p 45) → (¬ p 135) → False)
    (d458 : (p 39) → (p 45) → (p 114) → False)
    : (¬ p 42) → (¬ p 111) → (¬ p 135) → (p 114) → False := by
  intro a0 a1 a2 a3
  have v0 : p 39 := Classical.byContradiction (fun u => d518 u a0 a1)
  have v1 : p 45 := Classical.byContradiction (fun u => d417 a0 u a2)
  exact d458 v0 v1 a3

theorem c764 (p : Nat → Prop)
    (d182 : (p 67) → (p 68) → (p 118) → False)
    (d632 : (p 64) → (p 68) → (p 49) → False)
    (d564 : (¬ p 9) → (¬ p 10) → (¬ p 118) → False)
    (d273 : (¬ p 49) → (¬ p 53) → (¬ p 66) → False)
    (d51 : (p 3) → (p 10) → (p 55) → False)
    (d115 : (p 10) → (p 14) → (p 129) → False)
    (d307 : (p 53) → (p 59) → (p 114) → False)
    (d560 : (¬ p 55) → (¬ p 59) → (¬ p 129) → False)
    : (p 68) → (p 64) → (p 67) → (¬ p 66) → (¬ p 9) → (p 3) → (p 114) → (p 14) → False := by
  intro a0 a1 a2 a3 a4 a5 a6 a7
  have v0 : ¬ p 118 := (fun u => d182 a2 a0 u)
  have v1 : ¬ p 49 := (fun u => d632 a1 a0 u)
  have v2 : p 10 := Classical.byContradiction (fun u => d564 a4 u v0)
  have v3 : p 53 := Classical.byContradiction (fun u => d273 v1 u a3)
  have v4 : ¬ p 55 := (fun u => d51 a5 v2 u)
  have v5 : ¬ p 129 := (fun u => d115 v2 a7 u)
  have v6 : ¬ p 59 := (fun u => d307 v3 u a6)
  exact d560 v4 v6 v5

theorem c767 (p : Nat → Prop)
    (d51 : (p 3) → (p 10) → (p 55) → False)
    (d115 : (p 10) → (p 14) → (p 129) → False)
    (d560 : (¬ p 55) → (¬ p 59) → (¬ p 129) → False)
    : (p 10) → (¬ p 59) → (p 3) → (p 14) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 55 := (fun u => d51 a2 a0 u)
  have v1 : ¬ p 129 := (fun u => d115 a0 a3 u)
  exact d560 v0 a1 v1

theorem c768 (p : Nat → Prop)
    (d170 : (¬ p 1) → (¬ p 2) → (¬ p 18) → False)
    (d508 : (¬ p 18) → (¬ p 20) → (¬ p 35) → False)
    (d473 : (p 1) → (p 3) → (p 19) → False)
    (d28 : (p 20) → (p 21) → (p 63) → False)
    (d381 : (¬ p 19) → (¬ p 21) → (¬ p 50) → False)
    : (¬ p 18) → (¬ p 2) → (¬ p 35) → (p 63) → (¬ p 50) → (p 3) → False := by
  intro a0 a1 a2 a3 a4 a5
  have v0 : p 1 := Classical.byContradiction (fun u => d170 u a1 a0)
  have v1 : p 20 := Classical.byContradiction (fun u => d508 a0 u a2)
  have v2 : ¬ p 19 := (fun u => d473 v0 a5 u)
  have v3 : ¬ p 21 := (fun u => d28 v1 u a3)
  exact d381 v2 v3 a4

theorem c769 (p : Nat → Prop)
    (d284 : (p 18) → (p 29) → (p 44) → False)
    (d44 : (p 26) → (p 29) → (p 128) → False)
    (d88 : (¬ p 41) → (¬ p 44) → (¬ p 128) → False)
    : (p 29) → (¬ p 41) → (p 26) → (p 18) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 44 := (fun u => d284 a3 a0 u)
  have v1 : ¬ p 128 := (fun u => d44 a2 a0 u)
  exact d88 a1 v0 v1

theorem c770 (p : Nat → Prop)
    (d179 : (p 134) → (p 137) → (p 146) → False)
    (d194 : (p 42) → (p 47) → (p 137) → False)
    (d463 : (¬ p 44) → (¬ p 47) → (¬ p 146) → False)
    : (p 137) → (¬ p 44) → (p 134) → (p 42) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 146 := (fun u => d179 a2 a0 u)
  have v1 : ¬ p 47 := (fun u => d194 a3 u a0)
  exact d463 a1 v1 v0

theorem c775 (p : Nat → Prop)
    (d531 : (p 51) → (p 60) → (p 96) → False)
    (d467 : (p 64) → (p 73) → (p 96) → False)
    (d138 : (¬ p 68) → (¬ p 73) → (¬ p 130) → False)
    (d439 : (p 91) → (p 96) → (p 130) → False)
    (d162 : (p 55) → (p 60) → (p 130) → False)
    (d444 : (¬ p 51) → (¬ p 55) → (¬ p 91) → False)
    : (p 96) → (p 60) → (p 64) → (¬ p 68) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 51 := (fun u => d531 u a1 a0)
  have v1 : ¬ p 73 := (fun u => d467 a2 u a0)
  have v2 : p 130 := Classical.byContradiction (fun u => d138 a3 v1 u)
  have v3 : ¬ p 91 := (fun u => d439 u a0 v2)
  have v4 : ¬ p 55 := (fun u => d162 u a1 v2)
  exact d444 v0 v4 v3

theorem c777 (p : Nat → Prop)
    (d471 : (p 64) → (p 66) → (p 89) → False)
    (d105 : (p 49) → (p 51) → (p 64) → False)
    (d356 : (p 51) → (p 53) → (p 89) → False)
    (d273 : (¬ p 49) → (¬ p 53) → (¬ p 66) → False)
    : (p 51) → (p 89) → (p 64) → False := by
  intro a0 a1 a2
  have v0 : ¬ p 66 := (fun u => d471 a2 u a1)
  have v1 : ¬ p 49 := (fun u => d105 u a0 a2)
  have v2 : ¬ p 53 := (fun u => d356 a0 u a1)
  exact d273 v1 v2 v0

theorem c778 (p : Nat → Prop)
    (d162 : (p 55) → (p 60) → (p 130) → False)
    (d246 : (p 49) → (p 60) → (p 73) → False)
    (d138 : (¬ p 68) → (¬ p 73) → (¬ p 130) → False)
    : (p 60) → (p 49) → (p 55) → (¬ p 68) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 130 := (fun u => d162 a2 a0 u)
  have v1 : ¬ p 73 := (fun u => d246 a1 a0 u)
  exact d138 a3 v1 v0

theorem c780 (p : Nat → Prop)
    (d95 : (p 88) → (p 89) → (p 99) → False)
    (d297 : (p 99) → (p 105) → (p 114) → False)
    (d12 : (¬ p 88) → (¬ p 95) → (¬ p 105) → False)
    : (p 99) → (p 114) → (¬ p 95) → (p 89) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 88 := (fun u => d95 u a3 a0)
  have v1 : ¬ p 105 := (fun u => d297 a0 u a1)
  exact d12 v0 a2 v1

theorem c782 (p : Nat → Prop)
    (d365 : (p 1) → (p 10) → (p 26) → False)
    (d588 : (p 26) → (p 27) → (p 126) → False)
    (d53 : (¬ p 10) → (¬ p 11) → (¬ p 126) → False)
    : (p 26) → (p 27) → (p 1) → (¬ p 11) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 10 := (fun u => d365 a2 u a0)
  have v1 : ¬ p 126 := (fun u => d588 a0 a1 u)
  exact d53 v0 a3 v1

theorem c783 (p : Nat → Prop)
    (d564 : (¬ p 9) → (¬ p 10) → (¬ p 118) → False)
    (d651 : (p 100) → (p 7) → (p 101) → (¬ p 10) → False)
    (d495 : (p 40) → (p 41) → (p 118) → False)
    (d23 : (¬ p 38) → (¬ p 41) → (¬ p 101) → False)
    : (¬ p 10) → (p 100) → (p 40) → (¬ p 38) → (¬ p 9) → (p 7) → False := by
  intro a0 a1 a2 a3 a4 a5
  have v0 : p 118 := Classical.byContradiction (fun u => d564 a4 a0 u)
  have v1 : ¬ p 101 := (fun u => d651 a1 a5 u a0)
  have v2 : ¬ p 41 := (fun u => d495 a2 u v0)
  exact d23 a3 v2 v1

theorem c785 (p : Nat → Prop)
    (d117 : (p 2) → (p 7) → (p 38) → False)
    (d227 : (p 40) → (p 42) → (p 119) → False)
    (d541 : (p 38) → (p 40) → (p 100) → False)
    (d49 : (¬ p 25) → (¬ p 27) → (¬ p 119) → False)
    (d442 : (¬ p 23) → (¬ p 25) → (¬ p 100) → False)
    (d582 : (p 18) → (p 27) → (p 42) → False)
    (d336 : (p 1) → (p 7) → (p 23) → False)
    (d170 : (¬ p 1) → (¬ p 2) → (¬ p 18) → False)
    : (p 40) → (p 38) → (p 7) → (¬ p 25) → (p 42) → False := by
  intro a0 a1 a2 a3 a4
  have v0 : ¬ p 2 := (fun u => d117 u a2 a1)
  have v1 : ¬ p 119 := (fun u => d227 a0 a4 u)
  have v2 : ¬ p 100 := (fun u => d541 a1 a0 u)
  have v3 : p 27 := Classical.byContradiction (fun u => d49 a3 u v1)
  have v4 : p 23 := Classical.byContradiction (fun u => d442 u a3 v2)
  have v5 : ¬ p 18 := (fun u => d582 u v3 a4)
  have v6 : ¬ p 1 := (fun u => d336 u a2 v4)
  exact d170 v6 v0 v5

theorem c786 (p : Nat → Prop)
    (d5 : (p 5) → (p 8) → (p 78) → False)
    (d334 : (p 78) → (p 79) → (p 109) → False)
    (d394 : (¬ p 8) → (¬ p 9) → (¬ p 109) → False)
    : (p 78) → (p 79) → (¬ p 9) → (p 5) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 8 := (fun u => d5 a3 u a0)
  have v1 : ¬ p 109 := (fun u => d334 a0 a1 u)
  exact d394 v0 a2 v1

theorem c787 (p : Nat → Prop)
    (d520 : (p 23) → (p 30) → (p 105) → False)
    (d146 : (p 23) → (p 28) → (p 103) → False)
    (d490 : (p 103) → (p 105) → (p 140) → False)
    (d427 : (¬ p 28) → (¬ p 30) → (¬ p 140) → False)
    : (p 103) → (p 105) → (p 23) → False := by
  intro a0 a1 a2
  have v0 : ¬ p 30 := (fun u => d520 a2 u a1)
  have v1 : ¬ p 28 := (fun u => d146 a2 u a0)
  have v2 : ¬ p 140 := (fun u => d490 a0 a1 u)
  exact d427 v1 v0 v2

theorem c788 (p : Nat → Prop)
    (d469 : (p 63) → (p 64) → (p 76) → False)
    (d581 : (p 64) → (p 70) → (p 93) → False)
    (d312 : (p 63) → (p 70) → (p 82) → False)
    (d35 : (¬ p 76) → (¬ p 82) → (¬ p 93) → False)
    : (p 70) → (p 63) → (p 64) → False := by
  intro a0 a1 a2
  have v0 : ¬ p 76 := (fun u => d469 a1 a2 u)
  have v1 : ¬ p 93 := (fun u => d581 a2 a0 u)
  have v2 : ¬ p 82 := (fun u => d312 a1 a0 u)
  exact d35 v0 v2 v1

theorem c794 (p : Nat → Prop)
    (d479 : (p 82) → (p 86) → (p 142) → False)
    (d314 : (p 76) → (p 86) → (p 97) → False)
    (d85 : (p 93) → (p 97) → (p 142) → False)
    (d35 : (¬ p 76) → (¬ p 82) → (¬ p 93) → False)
    : (p 97) → (p 86) → (p 142) → False := by
  intro a0 a1 a2
  have v0 : ¬ p 82 := (fun u => d479 u a1 a2)
  have v1 : ¬ p 76 := (fun u => d314 u a1 a0)
  have v2 : ¬ p 93 := (fun u => d85 u a0 a2)
  exact d35 v1 v0 v2

theorem c796 (p : Nat → Prop)
    (d272 : (p 49) → (p 54) → (p 67) → False)
    (d632 : (p 64) → (p 68) → (p 49) → False)
    (d74 : (¬ p 63) → (¬ p 68) → (¬ p 80) → False)
    (d42 : (p 49) → (p 50) → (p 63) → False)
    (d180 : (p 63) → (p 67) → (p 79) → False)
    (d235 : (¬ p 50) → (¬ p 54) → (¬ p 79) → False)
    : (p 49) → (p 64) → (p 67) → (¬ p 80) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 54 := (fun u => d272 a0 u a2)
  have v1 : ¬ p 68 := (fun u => d632 a1 u a0)
  have v2 : p 63 := Classical.byContradiction (fun u => d74 u v1 a3)
  have v3 : ¬ p 50 := (fun u => d42 a0 u v2)
  have v4 : ¬ p 79 := (fun u => d180 v2 a2 u)
  exact d235 v3 v0 v4

theorem c797 (p : Nat → Prop)
    (d62 : (p 3) → (p 8) → (p 53) → False)
    (d84 : (p 3) → (p 9) → (p 54) → False)
    (d252 : (p 53) → (p 54) → (p 109) → False)
    (d394 : (¬ p 8) → (¬ p 9) → (¬ p 109) → False)
    : (p 54) → (p 53) → (p 3) → False := by
  intro a0 a1 a2
  have v0 : ¬ p 8 := (fun u => d62 a2 u a1)
  have v1 : ¬ p 9 := (fun u => d84 a2 u a0)
  have v2 : ¬ p 109 := (fun u => d252 a1 a0 u)
  exact d394 v0 v1 v2

theorem c798 (p : Nat → Prop)
    (d51 : (p 3) → (p 10) → (p 55) → False)
    (d38 : (p 3) → (p 6) → (p 51) → False)
    (d534 : (p 6) → (p 10) → (p 91) → False)
    (d444 : (¬ p 51) → (¬ p 55) → (¬ p 91) → False)
    : (p 6) → (p 10) → (p 3) → False := by
  intro a0 a1 a2
  have v0 : ¬ p 55 := (fun u => d51 a2 a1 u)
  have v1 : ¬ p 51 := (fun u => d38 a2 a0 u)
  have v2 : ¬ p 91 := (fun u => d534 a0 a1 u)
  exact d444 v1 v0 v2

theorem c799 (p : Nat → Prop)
    (d363 : (p 109) → (p 111) → (p 119) → False)
    (d227 : (p 40) → (p 42) → (p 119) → False)
    (d539 : (p 39) → (p 40) → (p 109) → False)
    (d518 : (¬ p 39) → (¬ p 42) → (¬ p 111) → False)
    : (p 40) → (p 109) → (p 119) → False := by
  intro a0 a1 a2
  have v0 : ¬ p 111 := (fun u => d363 a1 u a2)
  have v1 : ¬ p 42 := (fun u => d227 a0 u a2)
  have v2 : ¬ p 39 := (fun u => d539 u a0 a1)
  exact d518 v2 v1 v0

theorem c801 (p : Nat → Prop)
    (d578 : (p 67) → (p 69) → (p 119) → False)
    (d16 : (¬ p 64) → (¬ p 69) → (¬ p 92) → False)
    (d796 : (p 49) → (p 64) → (p 67) → (¬ p 80) → False)
    (d273 : (¬ p 49) → (¬ p 53) → (¬ p 66) → False)
    (d471 : (p 64) → (p 66) → (p 89) → False)
    (d400 : (¬ p 22) → (¬ p 24) → (¬ p 89) → False)
    (d489 : (p 20) → (p 24) → (p 66) → False)
    (d291 : (p 35) → (p 40) → (p 67) → False)
    (d508 : (¬ p 18) → (¬ p 20) → (¬ p 35) → False)
    (d127 : (p 18) → (p 24) → (p 39) → False)
    : (p 67) → (p 39) → (p 40) → (¬ p 53) → (¬ p 92) → (p 119) → (¬ p 22) → (¬ p 80) → False := by
  intro a0 a1 a2 a3 a4 a5 a6 a7
  have v0 : ¬ p 69 := (fun u => d578 a0 u a5)
  have v1 : p 64 := Classical.byContradiction (fun u => d16 u v0 a4)
  have v2 : ¬ p 49 := (fun u => d796 u v1 a0 a7)
  have v3 : p 66 := Classical.byContradiction (fun u => d273 v2 a3 u)
  have v4 : ¬ p 89 := (fun u => d471 v1 v3 u)
  have v5 : p 24 := Classical.byContradiction (fun u => d400 a6 u v4)
  have v6 : ¬ p 20 := (fun u => d489 u v5 v3)
  have v7 : ¬ p 35 := (fun u => d291 u a2 a0)
  have v8 : p 18 := Classical.byContradiction (fun u => d508 u v6 v7)
  exact d127 v8 v5 a1

theorem c808 (p : Nat → Prop)
    (d180 : (p 63) → (p 67) → (p 79) → False)
    (d182 : (p 67) → (p 68) → (p 118) → False)
    (d74 : (¬ p 63) → (¬ p 68) → (¬ p 80) → False)
    : (p 67) → (p 118) → (¬ p 80) → (p 79) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 63 := (fun u => d180 u a0 a3)
  have v1 : ¬ p 68 := (fun u => d182 a0 u a1)
  exact d74 v0 v1 a2

theorem c809 (p : Nat → Prop)
    (d548 : (p 35) → (p 41) → (p 68) → False)
    (d508 : (¬ p 18) → (¬ p 20) → (¬ p 35) → False)
    (d259 : (¬ p 35) → (¬ p 38) → (¬ p 65) → False)
    (d359 : (p 20) → (p 26) → (p 68) → False)
    (d718 : (p 68) → (p 66) → (p 20) → False)
    (d222 : (p 20) → (p 23) → (p 65) → False)
    (d542 : (p 65) → (p 72) → (p 105) → False)
    (d341 : (¬ p 24) → (¬ p 26) → (¬ p 110) → False)
    (d12 : (¬ p 88) → (¬ p 95) → (¬ p 105) → False)
    (d140 : (p 24) → (p 25) → (p 109) → False)
    (d731 : (p 29) → (p 24) → (p 20) → (¬ p 66) → False)
    (d137 : (p 64) → (p 72) → (p 95) → False)
    (d442 : (¬ p 23) → (¬ p 25) → (¬ p 100) → False)
    (d16 : (¬ p 64) → (¬ p 69) → (¬ p 92) → False)
    (d746 : (p 79) → (p 100) → (p 121) → False)
    (d257 : (p 20) → (p 27) → (p 69) → False)
    (d575 : (¬ p 54) → (¬ p 58) → (¬ p 121) → False)
    (d8 : (¬ p 27) → (¬ p 29) → (¬ p 134) → False)
    (d197 : (p 53) → (p 58) → (p 113) → False)
    (d73 : (p 69) → (p 71) → (p 134) → False)
    (d384 : (¬ p 66) → (¬ p 71) → (¬ p 113) → False)
    : (p 68) → (¬ p 88) → (p 72) → (¬ p 110) → (p 41) → (¬ p 38) → (¬ p 18) → (¬ p 92) → (p 79) → (p 109) → (¬ p 54) → (p 53) → False := by
  intro a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11
  have v0 : ¬ p 35 := (fun u => d548 u a4 a0)
  have v1 : p 20 := Classical.byContradiction (fun u => d508 a6 u v0)
  have v2 : p 65 := Classical.byContradiction (fun u => d259 v0 a5 u)
  have v3 : ¬ p 26 := (fun u => d359 v1 u a0)
  have v4 : ¬ p 66 := (fun u => d718 a0 u v1)
  have v5 : ¬ p 23 := (fun u => d222 v1 u v2)
  have v6 : ¬ p 105 := (fun u => d542 v2 a2 u)
  have v7 : p 24 := Classical.byContradiction (fun u => d341 u v3 a3)
  have v8 : p 95 := Classical.byContradiction (fun u => d12 a1 u v6)
  have v9 : ¬ p 25 := (fun u => d140 v7 u a9)
  have v10 : ¬ p 29 := (fun u => d731 u v7 v1 v4)
  have v11 : ¬ p 64 := (fun u => d137 u a2 v8)
  have v12 : p 100 := Classical.byContradiction (fun u => d442 v5 v9 u)
  have v13 : p 69 := Classical.byContradiction (fun u => d16 v11 u a7)
  have v14 : ¬ p 121 := (fun u => d746 a8 v12 u)
  have v15 : ¬ p 27 := (fun u => d257 v1 u v13)
  have v16 : p 58 := Classical.byContradiction (fun u => d575 a10 u v14)
  have v17 : p 134 := Classical.byContradiction (fun u => d8 v15 v10 u)
  have v18 : ¬ p 113 := (fun u => d197 a11 v16 u)
  have v19 : ¬ p 71 := (fun u => d73 v13 u v17)
  exact d384 v4 v19 v18

theorem c811 (p : Nat → Prop)
    (d508 : (¬ p 18) → (¬ p 20) → (¬ p 35) → False)
    (d259 : (¬ p 35) → (¬ p 38) → (¬ p 65) → False)
    (d28 : (p 20) → (p 21) → (p 63) → False)
    (d719 : (p 65) → (p 63) → (¬ p 21) → (p 20) → False)
    : (¬ p 35) → (¬ p 38) → (¬ p 18) → (p 63) → False := by
  intro a0 a1 a2 a3
  have v0 : p 20 := Classical.byContradiction (fun u => d508 a2 u a0)
  have v1 : p 65 := Classical.byContradiction (fun u => d259 a0 a1 u)
  have v2 : ¬ p 21 := (fun u => d28 v0 u a3)
  exact d719 v1 a3 v2 v0

theorem c812 (p : Nat → Prop)
    (d176 : (p 69) → (p 72) → (p 135) → False)
    (d101 : (p 35) → (p 42) → (p 69) → False)
    (d763 : (¬ p 42) → (¬ p 111) → (¬ p 135) → (p 114) → False)
    : (p 69) → (p 35) → (p 114) → (¬ p 111) → (p 72) → False := by
  intro a0 a1 a2 a3 a4
  have v0 : ¬ p 135 := (fun u => d176 a0 a4 u)
  have v1 : ¬ p 42 := (fun u => d101 a1 u a0)
  exact d763 v1 a3 v0 a2

theorem c813 (p : Nat → Prop)
    (d102 : (p 19) → (p 24) → (p 53) → False)
    (d438 : (p 19) → (p 22) → (p 51) → False)
    (d400 : (¬ p 22) → (¬ p 24) → (¬ p 89) → False)
    : (p 19) → (p 51) → (¬ p 89) → (p 53) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 24 := (fun u => d102 a0 u a3)
  have v1 : ¬ p 22 := (fun u => d438 a0 u a1)
  exact d400 v1 v0 a2

theorem c815 (p : Nat → Prop)
    (d505 : (¬ p 2) → (¬ p 3) → (¬ p 34) → False)
    (d549 : (¬ p 3) → (¬ p 4) → (¬ p 49) → False)
    (d208 : (p 2) → (p 4) → (p 35) → False)
    : (¬ p 3) → (¬ p 49) → (p 35) → (¬ p 34) → False := by
  intro a0 a1 a2 a3
  have v0 : p 2 := Classical.byContradiction (fun u => d505 u a0 a3)
  have v1 : p 4 := Classical.byContradiction (fun u => d549 a0 u a1)
  exact d208 v0 v1 a2

theorem c818 (p : Nat → Prop)
    (d588 : (p 26) → (p 27) → (p 126) → False)
    (d124 : (p 27) → (p 28) → (p 133) → False)
    (d428 : (p 126) → (p 127) → (p 133) → False)
    (d492 : (¬ p 26) → (¬ p 28) → (¬ p 127) → False)
    : (p 133) → (p 126) → (p 27) → False := by
  intro a0 a1 a2
  have v0 : ¬ p 26 := (fun u => d588 u a2 a1)
  have v1 : ¬ p 28 := (fun u => d124 a2 u a0)
  have v2 : ¬ p 127 := (fun u => d428 a1 u a0)
  exact d492 v0 v1 v2

theorem c819 (p : Nat → Prop)
    (d615 : (p 88) → (p 90) → (p 22) → (¬ p 25) → False)
    (d299 : (p 21) → (p 22) → (p 76) → False)
    (d207 : (¬ p 6) → (¬ p 7) → (¬ p 88) → False)
    (d213 : (¬ p 5) → (¬ p 6) → (¬ p 76) → False)
    (d2 : (p 5) → (p 12) → (p 82) → False)
    (d434 : (p 7) → (p 12) → (p 103) → False)
    (d35 : (¬ p 76) → (¬ p 82) → (¬ p 93) → False)
    (d154 : (¬ p 65) → (¬ p 70) → (¬ p 103) → False)
    (d581 : (p 64) → (p 70) → (p 93) → False)
    : (p 22) → (p 90) → (p 12) → (¬ p 65) → (¬ p 25) → (p 21) → (p 64) → (¬ p 6) → False := by
  intro a0 a1 a2 a3 a4 a5 a6 a7
  have v0 : ¬ p 88 := (fun u => d615 u a1 a0 a4)
  have v1 : ¬ p 76 := (fun u => d299 a5 a0 u)
  have v2 : p 7 := Classical.byContradiction (fun u => d207 a7 u v0)
  have v3 : p 5 := Classical.byContradiction (fun u => d213 u a7 v1)
  have v4 : ¬ p 82 := (fun u => d2 v3 a2 u)
  have v5 : ¬ p 103 := (fun u => d434 v2 a2 u)
  have v6 : p 93 := Classical.byContradiction (fun u => d35 v1 v4 u)
  have v7 : p 70 := Classical.byContradiction (fun u => d154 a3 u v5)
  exact d581 a6 v7 v6

theorem c822 (p : Nat → Prop)
    (d38 : (p 3) → (p 6) → (p 51) → False)
    (d245 : (p 3) → (p 5) → (p 50) → False)
    (d122 : (p 50) → (p 51) → (p 76) → False)
    (d213 : (¬ p 5) → (¬ p 6) → (¬ p 76) → False)
    : (p 50) → (p 51) → (p 3) → False := by
  intro a0 a1 a2
  have v0 : ¬ p 6 := (fun u => d38 a2 u a1)
  have v1 : ¬ p 5 := (fun u => d245 a2 u a0)
  have v2 : ¬ p 76 := (fun u => d122 a0 a1 u)
  exact d213 v1 v0 v2

theorem c826 (p : Nat → Prop)
    (d242 : (p 18) → (p 28) → (p 43) → False)
    (d191 : (p 1) → (p 12) → (p 28) → False)
    (d170 : (¬ p 1) → (¬ p 2) → (¬ p 18) → False)
    : (p 28) → (p 43) → (p 12) → (¬ p 2) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 18 := (fun u => d242 u a0 a1)
  have v1 : ¬ p 1 := (fun u => d191 u a2 a0)
  exact d170 v1 a3 v0

theorem c832 (p : Nat → Prop)
    (d247 : (p 66) → (p 72) → (p 114) → False)
    (d328 : (p 66) → (p 67) → (p 109) → False)
    (d323 : (¬ p 67) → (¬ p 72) → (¬ p 122) → False)
    : (p 66) → (p 114) → (¬ p 122) → (p 109) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 72 := (fun u => d247 a0 u a1)
  have v1 : ¬ p 67 := (fun u => d328 a0 u a3)
  exact d323 v1 v0 a2

theorem c833 (p : Nat → Prop)
    (d21 : (p 64) → (p 65) → (p 88) → False)
    (d724 : (p 93) → (p 88) → (¬ p 65) → (p 64) → False)
    : (p 88) → (p 93) → (p 64) → False := by
  intro a0 a1 a2
  have v0 : ¬ p 65 := (fun u => d21 a2 u a0)
  exact d724 a1 a0 v0 a2

theorem c841 (p : Nat → Prop)
    (d700 : (p 36) → (p 18) → (p 34) → False)
    (d156 : (p 18) → (p 21) → (p 36) → False)
    (d537 : (p 36) → (p 37) → (p 76) → False)
    (d3 : (¬ p 34) → (¬ p 37) → (¬ p 51) → False)
    (d381 : (¬ p 19) → (¬ p 21) → (¬ p 50) → False)
    (d777 : (p 51) → (p 89) → (p 64) → False)
    (d438 : (p 19) → (p 22) → (p 51) → False)
    (d400 : (¬ p 22) → (¬ p 24) → (¬ p 89) → False)
    : (p 36) → (¬ p 24) → (p 18) → (¬ p 50) → (p 76) → (p 64) → False := by
  intro a0 a1 a2 a3 a4 a5
  have v0 : ¬ p 34 := (fun u => d700 a0 a2 u)
  have v1 : ¬ p 21 := (fun u => d156 a2 u a0)
  have v2 : ¬ p 37 := (fun u => d537 a0 u a4)
  have v3 : p 51 := Classical.byContradiction (fun u => d3 v0 v2 u)
  have v4 : p 19 := Classical.byContradiction (fun u => d381 u v1 a3)
  have v5 : ¬ p 89 := (fun u => d777 v3 u a5)
  have v6 : ¬ p 22 := (fun u => d438 v4 u v3)
  exact d400 v6 a1 v5

theorem c842 (p : Nat → Prop)
    (d327 : (p 89) → (p 90) → (p 109) → False)
    (d400 : (¬ p 22) → (¬ p 24) → (¬ p 89) → False)
    (d26 : (p 22) → (p 25) → (p 90) → False)
    (d615 : (p 88) → (p 90) → (p 22) → (¬ p 25) → False)
    : (p 90) → (¬ p 24) → (p 109) → (p 88) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 89 := (fun u => d327 u a0 a2)
  have v1 : p 22 := Classical.byContradiction (fun u => d400 u a1 v0)
  have v2 : ¬ p 25 := (fun u => d26 v1 u a0)
  exact d615 a3 a0 v1 v2

theorem c844 (p : Nat → Prop)
    (d582 : (p 18) → (p 27) → (p 42) → False)
    (d227 : (p 40) → (p 42) → (p 119) → False)
    (d225 : (p 18) → (p 25) → (p 40) → False)
    (d49 : (¬ p 25) → (¬ p 27) → (¬ p 119) → False)
    : (p 40) → (p 18) → (p 42) → False := by
  intro a0 a1 a2
  have v0 : ¬ p 27 := (fun u => d582 a1 u a2)
  have v1 : ¬ p 119 := (fun u => d227 a0 a2 u)
  have v2 : ¬ p 25 := (fun u => d225 a1 u a0)
  exact d49 v2 v0 v1

theorem c845 (p : Nat → Prop)
    (d842 : (p 90) → (¬ p 24) → (p 109) → (p 88) → False)
    (d10 : (¬ p 37) → (¬ p 40) → (¬ p 90) → False)
    (d668 : (p 18) → (p 39) → (p 37) → False)
    (d537 : (p 36) → (p 37) → (p 76) → False)
    (d55 : (p 18) → (p 22) → (p 37) → False)
    (d58 : (¬ p 36) → (¬ p 39) → (¬ p 78) → False)
    (d400 : (¬ p 22) → (¬ p 24) → (¬ p 89) → False)
    (d25 : (p 76) → (p 78) → (p 89) → False)
    : (¬ p 24) → (p 76) → (p 88) → (¬ p 40) → (p 18) → (p 109) → False := by
  intro a0 a1 a2 a3 a4 a5
  have v0 : ¬ p 90 := (fun u => d842 u a0 a5 a2)
  have v1 : p 37 := Classical.byContradiction (fun u => d10 u a3 v0)
  have v2 : ¬ p 39 := (fun u => d668 a4 u v1)
  have v3 : ¬ p 36 := (fun u => d537 u v1 a1)
  have v4 : ¬ p 22 := (fun u => d55 a4 u v1)
  have v5 : p 78 := Classical.byContradiction (fun u => d58 v3 v2 u)
  have v6 : p 89 := Classical.byContradiction (fun u => d400 v4 a0 u)
  exact d25 a1 v5 v6

theorem c851 (p : Nat → Prop)
    (d327 : (p 89) → (p 90) → (p 109) → False)
    (d334 : (p 78) → (p 79) → (p 109) → False)
    (d675 : (p 115) → (p 109) → (p 78) → False)
    (d203 : (¬ p 89) → (¬ p 96) → (¬ p 115) → False)
    (d467 : (p 64) → (p 73) → (p 96) → False)
    (d211 : (p 90) → (p 96) → (p 123) → False)
    (d138 : (¬ p 68) → (¬ p 73) → (¬ p 130) → False)
    (d239 : (¬ p 79) → (¬ p 85) → (¬ p 123) → False)
    (d430 : (p 80) → (p 85) → (p 130) → False)
    : (p 78) → (p 90) → (p 109) → (p 80) → (p 64) → (¬ p 68) → False := by
  intro a0 a1 a2 a3 a4 a5
  have v0 : ¬ p 89 := (fun u => d327 u a1 a2)
  have v1 : ¬ p 79 := (fun u => d334 a0 u a2)
  have v2 : ¬ p 115 := (fun u => d675 u a2 a0)
  have v3 : p 96 := Classical.byContradiction (fun u => d203 v0 u v2)
  have v4 : ¬ p 73 := (fun u => d467 a4 u v3)
  have v5 : ¬ p 123 := (fun u => d211 a1 v3 u)
  have v6 : p 130 := Classical.byContradiction (fun u => d138 a5 v4 u)
  have v7 : p 85 := Classical.byContradiction (fun u => d239 v1 u v5)
  exact d430 a3 v7 v6

theorem c859 (p : Nat → Prop)
    (d700 : (p 36) → (p 18) → (p 34) → False)
    (d351 : (p 34) → (p 39) → (p 53) → False)
    (d58 : (¬ p 36) → (¬ p 39) → (¬ p 78) → False)
    : (p 34) → (p 53) → (p 18) → (¬ p 78) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 36 := (fun u => d700 u a2 a0)
  have v1 : ¬ p 39 := (fun u => d351 a0 u a1)
  exact d58 v0 v1 a3

theorem c860 (p : Nat → Prop)
    (d505 : (¬ p 2) → (¬ p 3) → (¬ p 34) → False)
    (d3 : (¬ p 34) → (¬ p 37) → (¬ p 51) → False)
    (d822 : (p 50) → (p 51) → (p 3) → False)
    (d438 : (p 19) → (p 22) → (p 51) → False)
    (d381 : (¬ p 19) → (¬ p 21) → (¬ p 50) → False)
    : (¬ p 34) → (¬ p 2) → (¬ p 37) → (¬ p 21) → (p 22) → False := by
  intro a0 a1 a2 a3 a4
  have v0 : p 3 := Classical.byContradiction (fun u => d505 a1 u a0)
  have v1 : p 51 := Classical.byContradiction (fun u => d3 a0 a2 u)
  have v2 : ¬ p 50 := (fun u => d822 u v1 v0)
  have v3 : ¬ p 19 := (fun u => d438 u a4 v1)
  exact d381 v3 a3 v2

theorem c861 (p : Nat → Prop)
    (d382 : (p 126) → (p 130) → (p 136) → False)
    (d57 : (p 42) → (p 46) → (p 136) → False)
    (d53 : (¬ p 10) → (¬ p 11) → (¬ p 126) → False)
    (d417 : (¬ p 42) → (¬ p 45) → (¬ p 135) → False)
    (d91 : (p 11) → (p 15) → (p 136) → False)
    (d315 : (p 135) → (p 136) → (p 148) → False)
    (d27 : (¬ p 14) → (¬ p 15) → (¬ p 148) → False)
    : (p 136) → (p 46) → (p 130) → (¬ p 45) → (¬ p 14) → (¬ p 10) → False := by
  intro a0 a1 a2 a3 a4 a5
  have v0 : ¬ p 126 := (fun u => d382 u a2 a0)
  have v1 : ¬ p 42 := (fun u => d57 u a1 a0)
  have v2 : p 11 := Classical.byContradiction (fun u => d53 a5 u v0)
  have v3 : p 135 := Classical.byContradiction (fun u => d417 v1 a3 u)
  have v4 : ¬ p 15 := (fun u => d91 v2 u a0)
  have v5 : ¬ p 148 := (fun u => d315 v3 a0 u)
  exact d27 a4 v4 v5

theorem c863 (p : Nat → Prop)
    (d449 : (p 72) → (p 74) → (p 149) → False)
    (d551 : (p 66) → (p 74) → (p 116) → False)
    (d145 : (¬ p 30) → (¬ p 32) → (¬ p 149) → False)
    (d83 : (¬ p 99) → (¬ p 107) → (¬ p 116) → False)
    (d524 : (p 23) → (p 32) → (p 107) → False)
    : (p 74) → (¬ p 99) → (¬ p 30) → (p 23) → (p 66) → (p 72) → False := by
  intro a0 a1 a2 a3 a4 a5
  have v0 : ¬ p 149 := (fun u => d449 a5 a0 u)
  have v1 : ¬ p 116 := (fun u => d551 a4 a0 u)
  have v2 : p 32 := Classical.byContradiction (fun u => d145 a2 u v0)
  have v3 : p 107 := Classical.byContradiction (fun u => d83 a1 u v1)
  exact d524 a3 v2 v3

theorem c864 (p : Nat → Prop)
    (d337 : (p 135) → (p 137) → (p 149) → False)
    (d187 : (p 27) → (p 32) → (p 137) → False)
    (d145 : (¬ p 30) → (¬ p 32) → (¬ p 149) → False)
    : (p 137) → (¬ p 30) → (p 27) → (p 135) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 149 := (fun u => d337 a3 a0 u)
  have v1 : ¬ p 32 := (fun u => d187 a2 u a0)
  exact d145 a1 v1 v0

theorem c866 (p : Nat → Prop)
    (d544 : (p 23) → (p 26) → (p 101) → False)
    (d308 : (p 23) → (p 24) → (p 99) → False)
    (d237 : (p 99) → (p 101) → (p 110) → False)
    (d341 : (¬ p 24) → (¬ p 26) → (¬ p 110) → False)
    : (p 99) → (p 101) → (p 23) → False := by
  intro a0 a1 a2
  have v0 : ¬ p 26 := (fun u => d544 a2 u a1)
  have v1 : ¬ p 24 := (fun u => d308 a2 u a0)
  have v2 : ¬ p 110 := (fun u => d237 a0 a1 u)
  exact d341 v1 v0 v2

theorem c867 (p : Nat → Prop)
    (d520 : (p 23) → (p 30) → (p 105) → False)
    (d195 : (p 105) → (p 107) → (p 149) → False)
    (d524 : (p 23) → (p 32) → (p 107) → False)
    (d145 : (¬ p 30) → (¬ p 32) → (¬ p 149) → False)
    : (p 107) → (p 105) → (p 23) → False := by
  intro a0 a1 a2
  have v0 : ¬ p 30 := (fun u => d520 a2 u a1)
  have v1 : ¬ p 149 := (fun u => d195 a1 a0 u)
  have v2 : ¬ p 32 := (fun u => d524 a2 u a0)
  exact d145 v0 v2 v1

theorem c870 (p : Nat → Prop)
    (d700 : (p 36) → (p 18) → (p 34) → False)
    (d156 : (p 18) → (p 21) → (p 36) → False)
    (d860 : (¬ p 34) → (¬ p 2) → (¬ p 37) → (¬ p 21) → (p 22) → False)
    : (p 36) → (¬ p 2) → (p 22) → (¬ p 37) → (p 18) → False := by
  intro a0 a1 a2 a3 a4
  have v0 : ¬ p 34 := (fun u => d700 a0 a4 u)
  have v1 : ¬ p 21 := (fun u => d156 a4 u a0)
  exact d860 v0 a1 a3 v1 a2

theorem c872 (p : Nat → Prop)
    (d263 : (p 21) → (p 26) → (p 80) → False)
    (d198 : (p 26) → (p 32) → (p 131) → False)
    (d309 : (p 21) → (p 32) → (p 86) → False)
    (d378 : (¬ p 80) → (¬ p 86) → (¬ p 131) → False)
    : (p 32) → (p 21) → (p 26) → False := by
  intro a0 a1 a2
  have v0 : ¬ p 80 := (fun u => d263 a1 a2 u)
  have v1 : ¬ p 131 := (fun u => d198 a2 a0 u)
  have v2 : ¬ p 86 := (fun u => d309 a1 a0 u)
  exact d378 v0 v2 v1

theorem c873 (p : Nat → Prop)
    (d17 : (p 51) → (p 54) → (p 90) → False)
    (d380 : (p 34) → (p 40) → (p 54) → False)
    (d10 : (¬ p 37) → (¬ p 40) → (¬ p 90) → False)
    : (p 54) → (p 51) → (p 34) → (¬ p 37) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 90 := (fun u => d17 a1 a0 u)
  have v1 : ¬ p 40 := (fun u => d380 a2 u a0)
  exact d10 a3 v1 v0

theorem c874 (p : Nat → Prop)
    (d503 : (p 5) → (p 9) → (p 79) → False)
    (d786 : (p 78) → (p 79) → (¬ p 9) → (p 5) → False)
    : (p 79) → (p 5) → (p 78) → False := by
  intro a0 a1 a2
  have v0 : ¬ p 9 := (fun u => d503 a1 u a0)
  exact d786 a2 a0 v0 a1

theorem c879 (p : Nat → Prop)
    (d263 : (p 21) → (p 26) → (p 80) → False)
    (d359 : (p 20) → (p 26) → (p 68) → False)
    (d28 : (p 20) → (p 21) → (p 63) → False)
    (d74 : (¬ p 63) → (¬ p 68) → (¬ p 80) → False)
    : (p 20) → (p 26) → (p 21) → False := by
  intro a0 a1 a2
  have v0 : ¬ p 80 := (fun u => d263 a2 a1 u)
  have v1 : ¬ p 68 := (fun u => d359 a0 a1 u)
  have v2 : ¬ p 63 := (fun u => d28 a0 a2 u)
  exact d74 v2 v1 v0

theorem c880 (p : Nat → Prop)
    (d569 : (p 90) → (p 95) → (p 122) → False)
    (d137 : (p 64) → (p 72) → (p 95) → False)
    (d323 : (¬ p 67) → (¬ p 72) → (¬ p 122) → False)
    : (p 95) → (p 90) → (¬ p 67) → (p 64) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 122 := (fun u => d569 a1 a0 u)
  have v1 : ¬ p 72 := (fun u => d137 a3 u a0)
  exact d323 a2 v1 v0

theorem c881 (p : Nat → Prop)
    (d278 : (p 34) → (p 38) → (p 52) → False)
    (d628 : (p 53) → (p 34) → (p 56) → (¬ p 42) → False)
    (d366 : (¬ p 52) → (¬ p 56) → (¬ p 102) → False)
    : (p 34) → (¬ p 42) → (¬ p 102) → (p 53) → (p 38) → False := by
  intro a0 a1 a2 a3 a4
  have v0 : ¬ p 52 := (fun u => d278 a0 a4 u)
  have v1 : ¬ p 56 := (fun u => d628 a3 a0 u a1)
  exact d366 v0 v1 a2

theorem c882 (p : Nat → Prop)
    (d207 : (¬ p 6) → (¬ p 7) → (¬ p 88) → False)
    (d111 : (¬ p 7) → (¬ p 8) → (¬ p 99) → False)
    (d95 : (p 88) → (p 89) → (p 99) → False)
    : (¬ p 7) → (¬ p 8) → (¬ p 6) → (p 89) → False := by
  intro a0 a1 a2 a3
  have v0 : p 88 := Classical.byContradiction (fun u => d207 a2 a0 u)
  have v1 : p 99 := Classical.byContradiction (fun u => d111 a0 a1 u)
  exact d95 v0 a3 v1

theorem c883 (p : Nat → Prop)
    (d557 : (p 23) → (p 27) → (p 102) → False)
    (d582 : (p 18) → (p 27) → (p 42) → False)
    (d881 : (p 34) → (¬ p 42) → (¬ p 102) → (p 53) → (p 38) → False)
    : (p 27) → (p 34) → (p 53) → (p 18) → (p 23) → (p 38) → False := by
  intro a0 a1 a2 a3 a4 a5
  have v0 : ¬ p 102 := (fun u => d557 a4 a0 u)
  have v1 : ¬ p 42 := (fun u => d582 a3 a0 u)
  exact d881 a1 v1 v0 a2 a5

theorem c884 (p : Nat → Prop)
    (d278 : (p 34) → (p 38) → (p 52) → False)
    (d881 : (p 34) → (¬ p 42) → (¬ p 102) → (p 53) → (p 38) → False)
    (d366 : (¬ p 52) → (¬ p 56) → (¬ p 102) → False)
    (d502 : (p 34) → (p 42) → (p 56) → False)
    : (¬ p 102) → (p 34) → (p 53) → (p 38) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 52 := (fun u => d278 a1 a3 u)
  have v1 : p 42 := Classical.byContradiction (fun u => d881 a1 u a0 a2 a3)
  have v2 : p 56 := Classical.byContradiction (fun u => d366 v0 u a0)
  exact d502 a1 v1 v2

theorem c886 (p : Nat → Prop)
    (d119 : (p 4) → (p 12) → (p 70) → False)
    (d434 : (p 7) → (p 12) → (p 103) → False)
    (d154 : (¬ p 65) → (¬ p 70) → (¬ p 103) → False)
    : (p 12) → (p 7) → (¬ p 65) → (p 4) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 70 := (fun u => d119 a3 a0 u)
  have v1 : ¬ p 103 := (fun u => d434 a1 a0 u)
  exact d154 a2 v0 v1

theorem c889 (p : Nat → Prop)
    (d387 : (p 18) → (p 26) → (p 41) → False)
    (d769 : (p 29) → (¬ p 41) → (p 26) → (p 18) → False)
    : (p 26) → (p 29) → (p 18) → False := by
  intro a0 a1 a2
  have v0 : ¬ p 41 := (fun u => d387 a2 a0 u)
  exact d769 a1 v0 a0 a2

theorem c891 (p : Nat → Prop)
    (d225 : (p 18) → (p 25) → (p 40) → False)
    (d501 : (p 40) → (p 45) → (p 122) → False)
    (d49 : (¬ p 25) → (¬ p 27) → (¬ p 119) → False)
    (d417 : (¬ p 42) → (¬ p 45) → (¬ p 135) → False)
    (d64 : (p 119) → (p 122) → (p 135) → False)
    : (p 40) → (p 122) → (p 18) → (¬ p 27) → (¬ p 42) → False := by
  intro a0 a1 a2 a3 a4
  have v0 : ¬ p 25 := (fun u => d225 a2 u a0)
  have v1 : ¬ p 45 := (fun u => d501 a0 u a1)
  have v2 : p 119 := Classical.byContradiction (fun u => d49 v0 a3 u)
  have v3 : p 135 := Classical.byContradiction (fun u => d417 a4 v1 u)
  exact d64 v2 a1 v3

theorem c894 (p : Nat → Prop)
    (d270 : (¬ p 20) → (¬ p 22) → (¬ p 64) → False)
    (d16 : (¬ p 64) → (¬ p 69) → (¬ p 92) → False)
    (d55 : (p 18) → (p 22) → (p 37) → False)
    (d241 : (p 90) → (p 92) → (p 119) → False)
    (d10 : (¬ p 37) → (¬ p 40) → (¬ p 90) → False)
    : (¬ p 64) → (¬ p 20) → (¬ p 69) → (p 119) → (¬ p 40) → (p 18) → False := by
  intro a0 a1 a2 a3 a4 a5
  have v0 : p 22 := Classical.byContradiction (fun u => d270 a1 u a0)
  have v1 : p 92 := Classical.byContradiction (fun u => d16 a0 a2 u)
  have v2 : ¬ p 37 := (fun u => d55 a5 v0 u)
  have v3 : ¬ p 90 := (fun u => d241 u v1 a3)
  exact d10 v2 a4 v3

theorem c896 (p : Nat → Prop)
    (d569 : (p 90) → (p 95) → (p 122) → False)
    (d234 : (p 37) → (p 45) → (p 95) → False)
    (d10 : (¬ p 37) → (¬ p 40) → (¬ p 90) → False)
    : (p 95) → (p 45) → (¬ p 40) → (p 122) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 90 := (fun u => d569 u a0 a3)
  have v1 : ¬ p 37 := (fun u => d234 u a1 a0)
  exact d10 v1 a2 v0

theorem c897 (p : Nat → Prop)
    (d517 : (p 22) → (p 23) → (p 88) → False)
    (d222 : (p 20) → (p 23) → (p 65) → False)
    (d21 : (p 64) → (p 65) → (p 88) → False)
    (d270 : (¬ p 20) → (¬ p 22) → (¬ p 64) → False)
    : (p 65) → (p 88) → (p 23) → False := by
  intro a0 a1 a2
  have v0 : ¬ p 22 := (fun u => d517 u a2 a1)
  have v1 : ¬ p 20 := (fun u => d222 u a2 a0)
  have v2 : ¬ p 64 := (fun u => d21 u a0 a1)
  exact d270 v1 v0 v2

theorem c899 (p : Nat → Prop)
    (d250 : (p 50) → (p 53) → (p 78) → False)
    (d538 : (¬ p 53) → (¬ p 57) → (¬ p 112) → False)
    (d288 : (p 50) → (p 57) → (p 82) → False)
    (d35 : (¬ p 76) → (¬ p 82) → (¬ p 93) → False)
    (d122 : (p 50) → (p 51) → (p 76) → False)
    (d444 : (¬ p 51) → (¬ p 55) → (¬ p 91) → False)
    (d275 : (p 76) → (p 80) → (p 91) → False)
    (d512 : (p 64) → (p 68) → (p 91) → False)
    (d74 : (¬ p 63) → (¬ p 68) → (¬ p 80) → False)
    : (p 50) → (¬ p 112) → (p 78) → (¬ p 55) → (¬ p 63) → (¬ p 93) → (p 64) → False := by
  intro a0 a1 a2 a3 a4 a5 a6
  have v0 : ¬ p 53 := (fun u => d250 a0 u a2)
  have v1 : p 57 := Classical.byContradiction (fun u => d538 v0 u a1)
  have v2 : ¬ p 82 := (fun u => d288 a0 v1 u)
  have v3 : p 76 := Classical.byContradiction (fun u => d35 u v2 a5)
  have v4 : ¬ p 51 := (fun u => d122 a0 u v3)
  have v5 : p 91 := Classical.byContradiction (fun u => d444 v4 a3 u)
  have v6 : ¬ p 80 := (fun u => d275 v3 u v5)
  have v7 : ¬ p 68 := (fun u => d512 a6 u v5)
  exact d74 a4 v7 v6

theorem c900 (p : Nat → Prop)
    (d400 : (¬ p 22) → (¬ p 24) → (¬ p 89) → False)
    (d633 : (¬ p 24) → (p 91) → (¬ p 22) → (¬ p 26) → False)
    (d777 : (p 51) → (p 89) → (p 64) → False)
    (d444 : (¬ p 51) → (¬ p 55) → (¬ p 91) → False)
    : (¬ p 24) → (¬ p 55) → (p 64) → (¬ p 22) → (¬ p 26) → False := by
  intro a0 a1 a2 a3 a4
  have v0 : p 89 := Classical.byContradiction (fun u => d400 a3 a0 u)
  have v1 : ¬ p 91 := (fun u => d633 a0 u a3 a4)
  have v2 : ¬ p 51 := (fun u => d777 u v0 a2)
  exact d444 v2 a1 v1

theorem c904 (p : Nat → Prop)
    (d164 : (p 144) → (p 146) → (p 149) → False)
    (d158 : (p 45) → (p 47) → (p 149) → False)
    (d463 : (¬ p 44) → (¬ p 47) → (¬ p 146) → False)
    : (p 149) → (p 144) → (p 45) → (¬ p 44) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 146 := (fun u => d164 a1 u a0)
  have v1 : ¬ p 47 := (fun u => d158 a2 u a0)
  exact d463 a3 v1 v0

theorem c905 (p : Nat → Prop)
    (d284 : (p 18) → (p 29) → (p 44) → False)
    (d470 : (p 18) → (p 32) → (p 47) → False)
    (d104 : (p 29) → (p 32) → (p 146) → False)
    (d463 : (¬ p 44) → (¬ p 47) → (¬ p 146) → False)
    : (p 32) → (p 29) → (p 18) → False := by
  intro a0 a1 a2
  have v0 : ¬ p 44 := (fun u => d284 a2 a1 u)
  have v1 : ¬ p 47 := (fun u => d470 a2 a0 u)
  have v2 : ¬ p 146 := (fun u => d104 a1 a0 u)
  exact d463 v0 v1 v2

theorem c906 (p : Nat → Prop)
    (d296 : (p 14) → (p 16) → (p 149) → False)
    (d486 : (p 14) → (p 17) → (p 150) → False)
    (d177 : (p 149) → (p 150) → (p 153) → False)
    (d99 : (¬ p 16) → (¬ p 17) → (¬ p 153) → False)
    : (p 150) → (p 14) → (p 149) → False := by
  intro a0 a1 a2
  have v0 : ¬ p 16 := (fun u => d296 a1 u a2)
  have v1 : ¬ p 17 := (fun u => d486 a1 u a0)
  have v2 : ¬ p 153 := (fun u => d177 a2 a0 u)
  exact d99 v0 v1 v2

theorem c907 (p : Nat → Prop)
    (d324 : (p 7) → (p 9) → (p 100) → False)
    (d399 : (p 7) → (p 17) → (p 108) → False)
    (d525 : (p 9) → (p 17) → (p 125) → False)
    (d54 : (¬ p 100) → (¬ p 108) → (¬ p 125) → False)
    : (p 17) → (p 9) → (p 7) → False := by
  intro a0 a1 a2
  have v0 : ¬ p 100 := (fun u => d324 a2 a1 u)
  have v1 : ¬ p 108 := (fun u => d399 a2 a0 u)
  have v2 : ¬ p 125 := (fun u => d525 a1 a0 u)
  exact d54 v0 v1 v2

theorem c910 (p : Nat → Prop)
    (d127 : (p 18) → (p 24) → (p 39) → False)
    (d308 : (p 23) → (p 24) → (p 99) → False)
    (d518 : (¬ p 39) → (¬ p 42) → (¬ p 111) → False)
    (d83 : (¬ p 99) → (¬ p 107) → (¬ p 116) → False)
    (d228 : (p 111) → (p 116) → (p 137) → False)
    : (p 24) → (¬ p 107) → (p 137) → (p 18) → (p 23) → (¬ p 42) → False := by
  intro a0 a1 a2 a3 a4 a5
  have v0 : ¬ p 39 := (fun u => d127 a3 a0 u)
  have v1 : ¬ p 99 := (fun u => d308 a4 a0 u)
  have v2 : p 111 := Classical.byContradiction (fun u => d518 v0 a5 u)
  have v3 : p 116 := Classical.byContradiction (fun u => d83 v1 a1 u)
  exact d228 v2 v3 a2

theorem c912 (p : Nat → Prop)
    (d514 : (p 55) → (p 58) → (p 128) → False)
    (d511 : (p 128) → (p 132) → (p 147) → False)
    (d4 : (p 55) → (p 62) → (p 132) → False)
    (d192 : (¬ p 58) → (¬ p 62) → (¬ p 147) → False)
    : (p 132) → (p 128) → (p 55) → False := by
  intro a0 a1 a2
  have v0 : ¬ p 58 := (fun u => d514 a2 u a1)
  have v1 : ¬ p 147 := (fun u => d511 a1 a0 u)
  have v2 : ¬ p 62 := (fun u => d4 a2 u a0)
  exact d192 v0 v2 v1

theorem c913 (p : Nat → Prop)
    (d250 : (p 50) → (p 53) → (p 78) → False)
    (d288 : (p 50) → (p 57) → (p 82) → False)
    (d538 : (¬ p 53) → (¬ p 57) → (¬ p 112) → False)
    : (p 50) → (p 82) → (p 78) → (¬ p 112) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 53 := (fun u => d250 a0 u a2)
  have v1 : ¬ p 57 := (fun u => d288 a0 u a1)
  exact d538 v0 v1 a3

theorem c920 (p : Nat → Prop)
    (d469 : (p 63) → (p 64) → (p 76) → False)
    (d40 : (p 63) → (p 75) → (p 87) → False)
    (d35 : (¬ p 76) → (¬ p 82) → (¬ p 93) → False)
    (d561 : (¬ p 81) → (¬ p 87) → (¬ p 138) → False)
    (d219 : (p 81) → (p 82) → (p 133) → False)
    : (p 63) → (¬ p 138) → (p 75) → (¬ p 93) → (p 64) → (p 133) → False := by
  intro a0 a1 a2 a3 a4 a5
  have v0 : ¬ p 76 := (fun u => d469 a0 a4 u)
  have v1 : ¬ p 87 := (fun u => d40 a0 a2 u)
  have v2 : p 82 := Classical.byContradiction (fun u => d35 v0 u a3)
  have v3 : p 81 := Classical.byContradiction (fun u => d561 u v1 a1)
  exact d219 v3 v2 a5

theorem c922 (p : Nat → Prop)
    (d559 : (p 34) → (p 41) → (p 55) → False)
    (d514 : (p 55) → (p 58) → (p 128) → False)
    (d88 : (¬ p 41) → (¬ p 44) → (¬ p 128) → False)
    : (p 55) → (p 58) → (¬ p 44) → (p 34) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 41 := (fun u => d559 a3 u a0)
  have v1 : ¬ p 128 := (fun u => d514 a0 a1 u)
  exact d88 v0 a2 v1

theorem c923 (p : Nat → Prop)
    (d197 : (p 53) → (p 58) → (p 113) → False)
    (d98 : (p 112) → (p 113) → (p 139) → False)
    (d538 : (¬ p 53) → (¬ p 57) → (¬ p 112) → False)
    : (p 113) → (p 139) → (¬ p 57) → (p 58) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 53 := (fun u => d197 u a3 a0)
  have v1 : ¬ p 112 := (fun u => d98 u a0 a1)
  exact d538 v0 a2 v1

theorem c925 (p : Nat → Prop)
    (d520 : (p 23) → (p 30) → (p 105) → False)
    (d295 : (p 22) → (p 30) → (p 95) → False)
    (d12 : (¬ p 88) → (¬ p 95) → (¬ p 105) → False)
    : (p 30) → (p 22) → (p 23) → (¬ p 88) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 105 := (fun u => d520 a2 a0 u)
  have v1 : ¬ p 95 := (fun u => d295 a1 a0 u)
  exact d12 a3 v1 v0

theorem c926 (p : Nat → Prop)
    (d913 : (p 50) → (p 82) → (p 78) → (¬ p 112) → False)
    (d460 : (p 78) → (p 82) → (p 112) → False)
    : (p 78) → (p 82) → (p 50) → False := by
  intro a0 a1 a2
  have v0 : p 112 := Classical.byContradiction (fun u => d913 a2 a1 a0 u)
  exact d460 a0 a1 v0

theorem c927 (p : Nat → Prop)
    (d528 : (p 50) → (p 59) → (p 84) → False)
    (d379 : (p 80) → (p 84) → (p 129) → False)
    (d560 : (¬ p 55) → (¬ p 59) → (¬ p 129) → False)
    : (p 84) → (¬ p 55) → (p 50) → (p 80) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 59 := (fun u => d528 a2 u a0)
  have v1 : ¬ p 129 := (fun u => d379 a3 a0 u)
  exact d560 a1 v0 v1

theorem c929 (p : Nat → Prop)
    (d421 : (p 64) → (p 75) → (p 98) → False)
    (d512 : (p 64) → (p 68) → (p 91) → False)
    (d36 : (p 68) → (p 75) → (p 132) → False)
    (d136 : (¬ p 91) → (¬ p 98) → (¬ p 132) → False)
    : (p 68) → (p 75) → (p 64) → False := by
  intro a0 a1 a2
  have v0 : ¬ p 98 := (fun u => d421 a2 a1 u)
  have v1 : ¬ p 91 := (fun u => d512 a2 a0 u)
  have v2 : ¬ p 132 := (fun u => d36 a0 a1 u)
  exact d136 v1 v0 v2

theorem c930 (p : Nat → Prop)
    (d147 : (p 5) → (p 10) → (p 80) → False)
    (d348 : (p 5) → (p 11) → (p 81) → False)
    (d96 : (p 80) → (p 81) → (p 126) → False)
    (d53 : (¬ p 10) → (¬ p 11) → (¬ p 126) → False)
    : (p 81) → (p 5) → (p 80) → False := by
  intro a0 a1 a2
  have v0 : ¬ p 10 := (fun u => d147 a1 u a2)
  have v1 : ¬ p 11 := (fun u => d348 a1 u a0)
  have v2 : ¬ p 126 := (fun u => d96 a2 a0 u)
  exact d53 v0 v1 v2

theorem c931 (p : Nat → Prop)
    (d579 : (p 102) → (p 105) → (p 135) → False)
    (d149 : (p 38) → (p 42) → (p 102) → False)
    (d437 : (p 38) → (p 45) → (p 105) → False)
    (d417 : (¬ p 42) → (¬ p 45) → (¬ p 135) → False)
    : (p 38) → (p 105) → (p 102) → False := by
  intro a0 a1 a2
  have v0 : ¬ p 135 := (fun u => d579 a2 a1 u)
  have v1 : ¬ p 42 := (fun u => d149 a0 u a2)
  have v2 : ¬ p 45 := (fun u => d437 a0 u a1)
  exact d417 v1 v2 v0

theorem c932 (p : Nat → Prop)
    (d700 : (p 36) → (p 18) → (p 34) → False)
    (d375 : (p 18) → (p 19) → (p 34) → False)
    (d127 : (p 18) → (p 24) → (p 39) → False)
    (d58 : (¬ p 36) → (¬ p 39) → (¬ p 78) → False)
    (d926 : (p 78) → (p 82) → (p 50) → False)
    (d201 : (p 21) → (p 24) → (p 78) → False)
    (d381 : (¬ p 19) → (¬ p 21) → (¬ p 50) → False)
    : (p 24) → (p 34) → (p 82) → (p 18) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 36 := (fun u => d700 u a3 a1)
  have v1 : ¬ p 19 := (fun u => d375 a3 u a1)
  have v2 : ¬ p 39 := (fun u => d127 a3 a0 u)
  have v3 : p 78 := Classical.byContradiction (fun u => d58 v0 v2 u)
  have v4 : ¬ p 50 := (fun u => d926 v3 a2 u)
  have v5 : ¬ p 21 := (fun u => d201 u a0 v3)
  exact d381 v1 v5 v4

theorem c934 (p : Nat → Prop)
    (d505 : (¬ p 2) → (¬ p 3) → (¬ p 34) → False)
    (d3 : (¬ p 34) → (¬ p 37) → (¬ p 51) → False)
    (d117 : (p 2) → (p 7) → (p 38) → False)
    (d31 : (p 37) → (p 41) → (p 91) → False)
    (d23 : (¬ p 38) → (¬ p 41) → (¬ p 101) → False)
    : (¬ p 34) → (¬ p 51) → (¬ p 101) → (p 7) → (¬ p 3) → (p 91) → False := by
  intro a0 a1 a2 a3 a4 a5
  have v0 : p 2 := Classical.byContradiction (fun u => d505 u a4 a0)
  have v1 : p 37 := Classical.byContradiction (fun u => d3 a0 u a1)
  have v2 : ¬ p 38 := (fun u => d117 v0 a3 u)
  have v3 : ¬ p 41 := (fun u => d31 v1 u a5)
  exact d23 v2 v3 a2

theorem c937 (p : Nat → Prop)
    (d559 : (p 34) → (p 41) → (p 55) → False)
    (d700 : (p 36) → (p 18) → (p 34) → False)
    (d375 : (p 18) → (p 19) → (p 34) → False)
    (d610 : (p 41) → (p 80) → (p 110) → False)
    (d341 : (¬ p 24) → (¬ p 26) → (¬ p 110) → False)
    (d127 : (p 18) → (p 24) → (p 39) → False)
    (d932 : (p 24) → (p 34) → (p 82) → (p 18) → False)
    (d58 : (¬ p 36) → (¬ p 39) → (¬ p 78) → False)
    (d35 : (¬ p 76) → (¬ p 82) → (¬ p 93) → False)
    (d201 : (p 21) → (p 24) → (p 78) → False)
    (d275 : (p 76) → (p 80) → (p 91) → False)
    (d381 : (¬ p 19) → (¬ p 21) → (¬ p 50) → False)
    (d444 : (¬ p 51) → (¬ p 55) → (¬ p 91) → False)
    (d122 : (p 50) → (p 51) → (p 76) → False)
    : (p 80) → (p 41) → (¬ p 26) → (p 18) → (¬ p 93) → (p 34) → False := by
  intro a0 a1 a2 a3 a4 a5
  have v0 : ¬ p 55 := (fun u => d559 a5 a1 u)
  have v1 : ¬ p 36 := (fun u => d700 u a3 a5)
  have v2 : ¬ p 19 := (fun u => d375 a3 u a5)
  have v3 : ¬ p 110 := (fun u => d610 a1 a0 u)
  have v4 : p 24 := Classical.byContradiction (fun u => d341 u a2 v3)
  have v5 : ¬ p 39 := (fun u => d127 a3 v4 u)
  have v6 : ¬ p 82 := (fun u => d932 v4 a5 u a3)
  have v7 : p 78 := Classical.byContradiction (fun u => d58 v1 v5 u)
  have v8 : p 76 := Classical.byContradiction (fun u => d35 u v6 a4)
  have v9 : ¬ p 21 := (fun u => d201 u v4 v7)
  have v10 : ¬ p 91 := (fun u => d275 v8 a0 u)
  have v11 : p 50 := Classical.byContradiction (fun u => d381 v2 v9 u)
  have v12 : p 51 := Classical.byContradiction (fun u => d444 u v0 v10)
  exact d122 v11 v12 v8

theorem c938 (p : Nat → Prop)
    (d127 : (p 18) → (p 24) → (p 39) → False)
    (d201 : (p 21) → (p 24) → (p 78) → False)
    (d58 : (¬ p 36) → (¬ p 39) → (¬ p 78) → False)
    : (p 24) → (p 21) → (¬ p 36) → (p 18) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 39 := (fun u => d127 a3 a0 u)
  have v1 : ¬ p 78 := (fun u => d201 a1 a0 u)
  exact d58 a2 v0 v1

theorem c939 (p : Nat → Prop)
    (d122 : (p 50) → (p 51) → (p 76) → False)
    (d381 : (¬ p 19) → (¬ p 21) → (¬ p 50) → False)
    (d299 : (p 21) → (p 22) → (p 76) → False)
    (d938 : (p 24) → (p 21) → (¬ p 36) → (p 18) → False)
    (d341 : (¬ p 24) → (¬ p 26) → (¬ p 110) → False)
    (d400 : (¬ p 22) → (¬ p 24) → (¬ p 89) → False)
    (d14 : (p 39) → (p 41) → (p 110) → False)
    (d25 : (p 76) → (p 78) → (p 89) → False)
    (d58 : (¬ p 36) → (¬ p 39) → (¬ p 78) → False)
    : (p 76) → (p 51) → (p 41) → (¬ p 26) → (¬ p 36) → (¬ p 19) → (p 18) → False := by
  intro a0 a1 a2 a3 a4 a5 a6
  have v0 : ¬ p 50 := (fun u => d122 u a1 a0)
  have v1 : p 21 := Classical.byContradiction (fun u => d381 a5 u v0)
  have v2 : ¬ p 22 := (fun u => d299 v1 u a0)
  have v3 : ¬ p 24 := (fun u => d938 u v1 a4 a6)
  have v4 : p 110 := Classical.byContradiction (fun u => d341 v3 a3 u)
  have v5 : p 89 := Classical.byContradiction (fun u => d400 v2 v3 u)
  have v6 : ¬ p 39 := (fun u => d14 u a2 v4)
  have v7 : ¬ p 78 := (fun u => d25 a0 u v5)
  exact d58 a4 v6 v7

theorem c940 (p : Nat → Prop)
    (d266 : (p 49) → (p 56) → (p 69) → False)
    (d429 : (p 51) → (p 56) → (p 92) → False)
    (d16 : (¬ p 64) → (¬ p 69) → (¬ p 92) → False)
    : (p 56) → (p 49) → (¬ p 64) → (p 51) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 69 := (fun u => d266 a1 a0 u)
  have v1 : ¬ p 92 := (fun u => d429 a3 a0 u)
  exact d16 a2 v0 v1

theorem c941 (p : Nat → Prop)
    (d358 : (p 49) → (p 52) → (p 65) → False)
    (d278 : (p 34) → (p 38) → (p 52) → False)
    (d259 : (¬ p 35) → (¬ p 38) → (¬ p 65) → False)
    : (p 52) → (p 49) → (¬ p 35) → (p 34) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 65 := (fun u => d358 a1 a0 u)
  have v1 : ¬ p 38 := (fun u => d278 a3 u a0)
  exact d259 a2 v1 v0

theorem c942 (p : Nat → Prop)
    (d149 : (p 38) → (p 42) → (p 102) → False)
    (d301 : (p 9) → (p 12) → (p 120) → False)
    (d181 : (p 4) → (p 9) → (p 67) → False)
    (d173 : (¬ p 40) → (¬ p 43) → (¬ p 120) → False)
    (d323 : (¬ p 67) → (¬ p 72) → (¬ p 122) → False)
    (d225 : (p 18) → (p 25) → (p 40) → False)
    (d541 : (p 38) → (p 40) → (p 100) → False)
    (d891 : (p 40) → (p 122) → (p 18) → (¬ p 27) → (¬ p 42) → False)
    (d442 : (¬ p 23) → (¬ p 25) → (¬ p 100) → False)
    (d557 : (p 23) → (p 27) → (p 102) → False)
    : (p 9) → (p 4) → (p 12) → (p 38) → (p 102) → (¬ p 72) → (¬ p 43) → (p 18) → False := by
  intro a0 a1 a2 a3 a4 a5 a6 a7
  have v0 : ¬ p 42 := (fun u => d149 a3 u a4)
  have v1 : ¬ p 120 := (fun u => d301 a0 a2 u)
  have v2 : ¬ p 67 := (fun u => d181 a1 a0 u)
  have v3 : p 40 := Classical.byContradiction (fun u => d173 u a6 v1)
  have v4 : p 122 := Classical.byContradiction (fun u => d323 v2 a5 u)
  have v5 : ¬ p 25 := (fun u => d225 a7 u v3)
  have v6 : ¬ p 100 := (fun u => d541 a3 v3 u)
  have v7 : p 27 := Classical.byContradiction (fun u => d891 v3 v4 a7 u v0)
  have v8 : p 23 := Classical.byContradiction (fun u => d442 u v5 v6)
  exact d557 v8 v7 a4

theorem c943 (p : Nat → Prop)
    (d2 : (p 5) → (p 12) → (p 82) → False)
    (d20 : (¬ p 4) → (¬ p 5) → (¬ p 63) → False)
    (d213 : (¬ p 5) → (¬ p 6) → (¬ p 76) → False)
    (d281 : (p 4) → (p 10) → (p 68) → False)
    (d46 : (p 6) → (p 8) → (p 89) → False)
    (d942 : (p 9) → (p 4) → (p 12) → (p 38) → (p 102) → (¬ p 72) → (¬ p 43) → (p 18) → False)
    (d564 : (¬ p 9) → (¬ p 10) → (¬ p 118) → False)
    (d394 : (¬ p 8) → (¬ p 9) → (¬ p 109) → False)
    (d265 : (p 109) → (p 110) → (p 118) → False)
    : (p 12) → (p 38) → (p 102) → (¬ p 72) → (¬ p 43) → (p 68) → (¬ p 63) → (p 89) → (p 82) → (¬ p 76) → (p 110) → (p 18) → False := by
  intro a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11
  have v0 : ¬ p 5 := (fun u => d2 u a0 a8)
  have v1 : p 4 := Classical.byContradiction (fun u => d20 u v0 a6)
  have v2 : p 6 := Classical.byContradiction (fun u => d213 v0 u a9)
  have v3 : ¬ p 10 := (fun u => d281 v1 u a5)
  have v4 : ¬ p 8 := (fun u => d46 v2 u a7)
  have v5 : ¬ p 9 := (fun u => d942 u v1 a0 a1 a2 a3 a4 a11)
  have v6 : p 118 := Classical.byContradiction (fun u => d564 v5 v3 u)
  have v7 : p 109 := Classical.byContradiction (fun u => d394 v4 v5 u)
  exact d265 v7 a10 v6

theorem c944 (p : Nat → Prop)
    (d52 : (p 34) → (p 43) → (p 57) → False)
    (d380 : (p 34) → (p 40) → (p 54) → False)
    (d555 : (p 54) → (p 57) → (p 120) → False)
    (d173 : (¬ p 40) → (¬ p 43) → (¬ p 120) → False)
    : (p 54) → (p 57) → (p 34) → False := by
  intro a0 a1 a2
  have v0 : ¬ p 43 := (fun u => d52 a2 u a1)
  have v1 : ¬ p 40 := (fun u => d380 a2 u a0)
  have v2 : ¬ p 120 := (fun u => d555 a0 a1 u)
  exact d173 v1 v0 v2

theorem c945 (p : Nat → Prop)
    (d259 : (¬ p 35) → (¬ p 38) → (¬ p 65) → False)
    (d154 : (¬ p 65) → (¬ p 70) → (¬ p 103) → False)
    (d149 : (p 38) → (p 42) → (p 102) → False)
    (d570 : (p 102) → (p 103) → (p 133) → False)
    (d518 : (¬ p 39) → (¬ p 42) → (¬ p 111) → False)
    (d943 : (p 12) → (p 38) → (p 102) → (¬ p 72) → (¬ p 43) → (p 68) → (¬ p 63) → (p 89) → (p 82) → (¬ p 76) → (p 110) → (p 18) → False)
    (d166 : (¬ p 11) → (¬ p 12) → (¬ p 133) → False)
    (d423 : (p 8) → (p 11) → (p 111) → False)
    (d394 : (¬ p 8) → (¬ p 9) → (¬ p 109) → False)
    (d143 : (p 9) → (p 11) → (p 119) → False)
    (d49 : (¬ p 25) → (¬ p 27) → (¬ p 119) → False)
    (d557 : (p 23) → (p 27) → (p 102) → False)
    (d442 : (¬ p 23) → (¬ p 25) → (¬ p 100) → False)
    (d319 : (p 100) → (p 103) → (p 120) → False)
    (d541 : (p 38) → (p 40) → (p 100) → False)
    (d173 : (¬ p 40) → (¬ p 43) → (¬ p 120) → False)
    : (¬ p 65) → (¬ p 25) → (¬ p 109) → (p 102) → (¬ p 72) → (¬ p 70) → (¬ p 35) → (¬ p 43) → (p 68) → (¬ p 63) → (p 89) → (p 82) → (¬ p 76) → (¬ p 39) → (p 110) → (p 18) → False := by
  intro a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15
  have v0 : p 38 := Classical.byContradiction (fun u => d259 a6 u a0)
  have v1 : p 103 := Classical.byContradiction (fun u => d154 a0 a5 u)
  have v2 : ¬ p 42 := (fun u => d149 v0 u a3)
  have v3 : ¬ p 133 := (fun u => d570 a3 v1 u)
  have v4 : p 111 := Classical.byContradiction (fun u => d518 a13 v2 u)
  have v5 : ¬ p 12 := (fun u => d943 u v0 a3 a4 a7 a8 a9 a10 a11 a12 a14 a15)
  have v6 : p 11 := Classical.byContradiction (fun u => d166 u v5 v3)
  have v7 : ¬ p 8 := (fun u => d423 u v6 v4)
  have v8 : p 9 := Classical.byContradiction (fun u => d394 v7 u a2)
  have v9 : ¬ p 119 := (fun u => d143 v8 v6 u)
  have v10 : p 27 := Classical.byContradiction (fun u => d49 a1 u v9)
  have v11 : ¬ p 23 := (fun u => d557 u v10 a3)
  have v12 : p 100 := Classical.byContradiction (fun u => d442 v11 a1 u)
  have v13 : ¬ p 120 := (fun u => d319 v12 v1 u)
  have v14 : ¬ p 40 := (fun u => d541 v0 u v12)
  exact d173 v14 a7 v13

theorem c946 (p : Nat → Prop)
    (d460 : (p 78) → (p 82) → (p 112) → False)
    (d375 : (p 18) → (p 19) → (p 34) → False)
    (d700 : (p 36) → (p 18) → (p 34) → False)
    (d939 : (p 76) → (p 51) → (p 41) → (¬ p 26) → (¬ p 36) → (¬ p 19) → (p 18) → False)
    (d559 : (p 34) → (p 41) → (p 55) → False)
    (d150 : (p 78) → (p 80) → (p 110) → False)
    (d381 : (¬ p 19) → (¬ p 21) → (¬ p 50) → False)
    (d900 : (¬ p 24) → (¬ p 55) → (p 64) → (¬ p 22) → (¬ p 26) → False)
    (d400 : (¬ p 22) → (¬ p 24) → (¬ p 89) → False)
    (d270 : (¬ p 20) → (¬ p 22) → (¬ p 64) → False)
    (d356 : (p 51) → (p 53) → (p 89) → False)
    (d28 : (p 20) → (p 21) → (p 63) → False)
    (d538 : (¬ p 53) → (¬ p 57) → (¬ p 112) → False)
    (d74 : (¬ p 63) → (¬ p 68) → (¬ p 80) → False)
    (d52 : (p 34) → (p 43) → (p 57) → False)
    (d548 : (p 35) → (p 41) → (p 68) → False)
    (d391 : (p 66) → (p 68) → (p 110) → False)
    (d273 : (¬ p 49) → (¬ p 53) → (¬ p 66) → False)
    (d100 : (p 49) → (p 57) → (p 70) → False)
    (d706 : (p 68) → (p 72) → (p 49) → False)
    (d940 : (p 56) → (p 49) → (¬ p 64) → (p 51) → False)
    (d941 : (p 52) → (p 49) → (¬ p 35) → (p 34) → False)
    (d366 : (¬ p 52) → (¬ p 56) → (¬ p 102) → False)
    (d944 : (p 54) → (p 57) → (p 34) → False)
    (d235 : (¬ p 50) → (¬ p 54) → (¬ p 79) → False)
    (d334 : (p 78) → (p 79) → (p 109) → False)
    (d424 : (p 21) → (p 25) → (p 79) → False)
    (d874 : (p 79) → (p 5) → (p 78) → False)
    (d20 : (¬ p 4) → (¬ p 5) → (¬ p 63) → False)
    (d213 : (¬ p 5) → (¬ p 6) → (¬ p 76) → False)
    (d945 : (¬ p 65) → (¬ p 25) → (¬ p 109) → (p 102) → (¬ p 72) → (¬ p 70) → (¬ p 35) → (¬ p 43) → (p 68) → (¬ p 63) → (p 89) → (p 82) → (¬ p 76) → (¬ p 39) → (p 110) → (p 18) → False)
    (d418 : (p 4) → (p 7) → (p 65) → False)
    (d46 : (p 6) → (p 8) → (p 89) → False)
    (d222 : (p 20) → (p 23) → (p 65) → False)
    (d111 : (¬ p 7) → (¬ p 8) → (¬ p 99) → False)
    (d442 : (¬ p 23) → (¬ p 25) → (¬ p 100) → False)
    (d674 : (p 113) → (p 99) → (p 78) → False)
    (d746 : (p 79) → (p 100) → (p 121) → False)
    (d384 : (¬ p 66) → (¬ p 71) → (¬ p 113) → False)
    (d575 : (¬ p 54) → (¬ p 58) → (¬ p 121) → False)
    (d86 : (p 49) → (p 58) → (p 71) → False)
    : (¬ p 22) → (p 82) → (p 51) → (p 41) → (¬ p 39) → (p 78) → (¬ p 50) → (¬ p 24) → (p 110) → (¬ p 26) → (p 18) → (p 34) → False := by
  intro a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11
  have v0 : ¬ p 112 := (fun u => d460 a5 a1 u)
  have v1 : ¬ p 19 := (fun u => d375 a10 u a11)
  have v2 : ¬ p 36 := (fun u => d700 u a10 a11)
  have v3 : ¬ p 76 := (fun u => d939 u a2 a3 a9 v2 v1 a10)
  have v4 : ¬ p 55 := (fun u => d559 a11 a3 u)
  have v5 : ¬ p 80 := (fun u => d150 a5 u a8)
  have v6 : p 21 := Classical.byContradiction (fun u => d381 v1 u a6)
  have v7 : ¬ p 64 := (fun u => d900 a7 v4 u a0 a9)
  have v8 : p 89 := Classical.byContradiction (fun u => d400 a0 a7 u)
  have v9 : p 20 := Classical.byContradiction (fun u => d270 u a0 v7)
  have v10 : ¬ p 53 := (fun u => d356 a2 u v8)
  have v11 : ¬ p 63 := (fun u => d28 v9 v6 u)
  have v12 : p 57 := Classical.byContradiction (fun u => d538 v10 u v0)
  have v13 : p 68 := Classical.byContradiction (fun u => d74 v11 u v5)
  have v14 : ¬ p 43 := (fun u => d52 a11 u v12)
  have v15 : ¬ p 35 := (fun u => d548 u a3 v13)
  have v16 : ¬ p 66 := (fun u => d391 u v13 a8)
  have v17 : p 49 := Classical.byContradiction (fun u => d273 u v10 v16)
  have v18 : ¬ p 70 := (fun u => d100 v17 v12 u)
  have v19 : ¬ p 72 := (fun u => d706 v13 u v17)
  have v20 : ¬ p 56 := (fun u => d940 u v17 v7 a2)
  have v21 : ¬ p 52 := (fun u => d941 u v17 v15 a11)
  have v22 : p 102 := Classical.byContradiction (fun u => d366 v21 v20 u)
  have v23 : ¬ p 54 := (fun u => d944 u v12 a11)
  have v24 : p 79 := Classical.byContradiction (fun u => d235 a6 v23 u)
  have v25 : ¬ p 109 := (fun u => d334 a5 v24 u)
  have v26 : ¬ p 25 := (fun u => d424 v6 u v24)
  have v27 : ¬ p 5 := (fun u => d874 v24 u a5)
  have v28 : p 4 := Classical.byContradiction (fun u => d20 u v27 v11)
  have v29 : p 6 := Classical.byContradiction (fun u => d213 v27 u v3)
  have v30 : p 65 := Classical.byContradiction (fun u => d945 u v26 v25 v22 v19 v18 v15 v14 v13 v11 v8 a1 v3 a4 a8 a10)
  have v31 : ¬ p 7 := (fun u => d418 v28 u v30)
  have v32 : ¬ p 8 := (fun u => d46 v29 u v8)
  have v33 : ¬ p 23 := (fun u => d222 v9 u v30)
  have v34 : p 99 := Classical.byContradiction (fun u => d111 v31 v32 u)
  have v35 : p 100 := Classical.byContradiction (fun u => d442 v33 v26 u)
  have v36 : ¬ p 113 := (fun u => d674 u v34 a5)
  have v37 : ¬ p 121 := (fun u => d746 v24 v35 u)
  have v38 : p 71 := Classical.byContradiction (fun u => d384 v16 u v36)
  have v39 : p 58 := Classical.byContradiction (fun u => d575 v23 u v37)
  exact d86 v17 v39 v38

theorem c950 (p : Nat → Prop)
    (d569 : (p 90) → (p 95) → (p 122) → False)
    (d26 : (p 22) → (p 25) → (p 90) → False)
    (d615 : (p 88) → (p 90) → (p 22) → (¬ p 25) → False)
    (d442 : (¬ p 23) → (¬ p 25) → (¬ p 100) → False)
    (d12 : (¬ p 88) → (¬ p 95) → (¬ p 105) → False)
    (d331 : (p 100) → (p 105) → (p 122) → False)
    : (p 22) → (p 90) → (p 122) → (¬ p 23) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 95 := (fun u => d569 a1 u a2)
  have v1 : ¬ p 25 := (fun u => d26 a0 u a1)
  have v2 : ¬ p 88 := (fun u => d615 u a1 a0 v1)
  have v3 : p 100 := Classical.byContradiction (fun u => d442 a3 v1 u)
  have v4 : p 105 := Classical.byContradiction (fun u => d12 v2 v0 u)
  exact d331 v3 v4 a2

theorem c951 (p : Nat → Prop)
    (d569 : (p 90) → (p 95) → (p 122) → False)
    (d331 : (p 100) → (p 105) → (p 122) → False)
    (d175 : (p 88) → (p 90) → (p 100) → False)
    (d12 : (¬ p 88) → (¬ p 95) → (¬ p 105) → False)
    : (p 100) → (p 90) → (p 122) → False := by
  intro a0 a1 a2
  have v0 : ¬ p 95 := (fun u => d569 a1 u a2)
  have v1 : ¬ p 105 := (fun u => d331 a0 u a2)
  have v2 : ¬ p 88 := (fun u => d175 u a1 a0)
  exact d12 v2 v0 v1

theorem c952 (p : Nat → Prop)
    (d387 : (p 18) → (p 26) → (p 41) → False)
    (d242 : (p 18) → (p 28) → (p 43) → False)
    (d440 : (p 41) → (p 43) → (p 127) → False)
    (d492 : (¬ p 26) → (¬ p 28) → (¬ p 127) → False)
    : (p 43) → (p 41) → (p 18) → False := by
  intro a0 a1 a2
  have v0 : ¬ p 26 := (fun u => d387 a2 u a1)
  have v1 : ¬ p 28 := (fun u => d242 a2 u a0)
  have v2 : ¬ p 127 := (fun u => d440 a1 a0 u)
  exact d492 v0 v1 v2

theorem c953 (p : Nat → Prop)
    (d26 : (p 22) → (p 25) → (p 90) → False)
    (d270 : (¬ p 20) → (¬ p 22) → (¬ p 64) → False)
    (d638 : (p 25) → (p 20) → (p 30) → False)
    (d142 : (p 20) → (p 25) → (p 67) → False)
    (d711 : (p 120) → (¬ p 30) → (p 25) → (p 122) → False)
    (d323 : (¬ p 67) → (¬ p 72) → (¬ p 122) → False)
    : (p 25) → (p 90) → (p 120) → (¬ p 72) → (¬ p 64) → False := by
  intro a0 a1 a2 a3 a4
  have v0 : ¬ p 22 := (fun u => d26 u a0 a1)
  have v1 : p 20 := Classical.byContradiction (fun u => d270 u v0 a4)
  have v2 : ¬ p 30 := (fun u => d638 a0 v1 u)
  have v3 : ¬ p 67 := (fun u => d142 v1 a0 u)
  have v4 : ¬ p 122 := (fun u => d711 a2 v2 a0 u)
  exact d323 v3 a3 v4

theorem c954 (p : Nat → Prop)
    (d281 : (p 4) → (p 10) → (p 68) → False)
    (d181 : (p 4) → (p 9) → (p 67) → False)
    (d182 : (p 67) → (p 68) → (p 118) → False)
    (d564 : (¬ p 9) → (¬ p 10) → (¬ p 118) → False)
    : (p 67) → (p 4) → (p 68) → False := by
  intro a0 a1 a2
  have v0 : ¬ p 10 := (fun u => d281 a1 u a2)
  have v1 : ¬ p 9 := (fun u => d181 a1 u a0)
  have v2 : ¬ p 118 := (fun u => d182 a0 a2 u)
  exact d564 v1 v0 v2

theorem c957 (p : Nat → Prop)
    (d166 : (¬ p 11) → (¬ p 12) → (¬ p 133) → False)
    (d53 : (¬ p 10) → (¬ p 11) → (¬ p 126) → False)
    (d428 : (p 126) → (p 127) → (p 133) → False)
    : (¬ p 11) → (¬ p 12) → (p 127) → (¬ p 10) → False := by
  intro a0 a1 a2 a3
  have v0 : p 133 := Classical.byContradiction (fun u => d166 a0 a1 u)
  have v1 : p 126 := Classical.byContradiction (fun u => d53 a3 a0 u)
  exact d428 v1 a2 v0

theorem c958 (p : Nat → Prop)
    (d946 : (¬ p 22) → (p 82) → (p 51) → (p 41) → (¬ p 39) → (p 78) → (¬ p 50) → (¬ p 24) → (p 110) → (¬ p 26) → (p 18) → (p 34) → False)
    (d926 : (p 78) → (p 82) → (p 50) → False)
    : (p 82) → (p 34) → (p 51) → (p 41) → (¬ p 22) → (¬ p 39) → (p 78) → (¬ p 24) → (p 110) → (¬ p 26) → (p 18) → False := by
  intro a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10
  have v0 : p 50 := Classical.byContradiction (fun u => d946 a4 a0 a2 a3 a5 a6 u a7 a8 a9 a10 a1)
  exact d926 a6 a0 v0

theorem c961 (p : Nat → Prop)
    (d64 : (p 119) → (p 122) → (p 135) → False)
    (d738 : (p 92) → (p 119) → (p 42) → False)
    (d232 : (p 88) → (p 92) → (p 102) → False)
    (d417 : (¬ p 42) → (¬ p 45) → (¬ p 135) → False)
    (d12 : (¬ p 88) → (¬ p 95) → (¬ p 105) → False)
    (d896 : (p 95) → (p 45) → (¬ p 40) → (p 122) → False)
    : (p 92) → (p 119) → (¬ p 105) → (¬ p 40) → (p 122) → (p 102) → False := by
  intro a0 a1 a2 a3 a4 a5
  have v0 : ¬ p 135 := (fun u => d64 a1 a4 u)
  have v1 : ¬ p 42 := (fun u => d738 a0 a1 u)
  have v2 : ¬ p 88 := (fun u => d232 u a0 a5)
  have v3 : p 45 := Classical.byContradiction (fun u => d417 v1 u v0)
  have v4 : p 95 := Classical.byContradiction (fun u => d12 v2 u a2)
  exact d896 v4 v3 a3 a4

theorem c962 (p : Nat → Prop)
    (d281 : (p 4) → (p 10) → (p 68) → False)
    (d66 : (p 68) → (p 69) → (p 126) → False)
    (d22 : (p 4) → (p 11) → (p 69) → False)
    (d53 : (¬ p 10) → (¬ p 11) → (¬ p 126) → False)
    : (p 69) → (p 4) → (p 68) → False := by
  intro a0 a1 a2
  have v0 : ¬ p 10 := (fun u => d281 a1 u a2)
  have v1 : ¬ p 126 := (fun u => d66 a2 a0 u)
  have v2 : ¬ p 11 := (fun u => d22 a1 u a0)
  exact d53 v0 v2 v1

theorem c965 (p : Nat → Prop)
    (d375 : (p 18) → (p 19) → (p 34) → False)
    (d387 : (p 18) → (p 26) → (p 41) → False)
    (d700 : (p 36) → (p 18) → (p 34) → False)
    (d939 : (p 76) → (p 51) → (p 41) → (¬ p 26) → (¬ p 36) → (¬ p 19) → (p 18) → False)
    (d582 : (p 18) → (p 27) → (p 42) → False)
    (d518 : (¬ p 39) → (¬ p 42) → (¬ p 111) → False)
    (d58 : (¬ p 36) → (¬ p 39) → (¬ p 78) → False)
    (d332 : (p 24) → (p 27) → (p 111) → False)
    (d341 : (¬ p 24) → (¬ p 26) → (¬ p 110) → False)
    (d400 : (¬ p 22) → (¬ p 24) → (¬ p 89) → False)
    (d958 : (p 82) → (p 34) → (p 51) → (p 41) → (¬ p 22) → (¬ p 39) → (p 78) → (¬ p 24) → (p 110) → (¬ p 26) → (p 18) → False)
    (d356 : (p 51) → (p 53) → (p 89) → False)
    (d35 : (¬ p 76) → (¬ p 82) → (¬ p 93) → False)
    (d558 : (p 51) → (p 57) → (p 93) → False)
    (d497 : (p 89) → (p 93) → (p 112) → False)
    (d538 : (¬ p 53) → (¬ p 57) → (¬ p 112) → False)
    : (¬ p 39) → (p 34) → (p 51) → (¬ p 22) → (p 27) → (p 41) → (p 18) → False := by
  intro a0 a1 a2 a3 a4 a5 a6
  have v0 : ¬ p 19 := (fun u => d375 a6 u a1)
  have v1 : ¬ p 26 := (fun u => d387 a6 u a5)
  have v2 : ¬ p 36 := (fun u => d700 u a6 a1)
  have v3 : ¬ p 76 := (fun u => d939 u a2 a5 v1 v2 v0 a6)
  have v4 : ¬ p 42 := (fun u => d582 a6 a4 u)
  have v5 : p 111 := Classical.byContradiction (fun u => d518 a0 v4 u)
  have v6 : p 78 := Classical.byContradiction (fun u => d58 v2 a0 u)
  have v7 : ¬ p 24 := (fun u => d332 u a4 v5)
  have v8 : p 110 := Classical.byContradiction (fun u => d341 v7 v1 u)
  have v9 : p 89 := Classical.byContradiction (fun u => d400 a3 v7 u)
  have v10 : ¬ p 82 := (fun u => d958 u a1 a2 a5 a3 a0 v6 v7 v8 v1 a6)
  have v11 : ¬ p 53 := (fun u => d356 a2 u v9)
  have v12 : p 93 := Classical.byContradiction (fun u => d35 v3 v10 u)
  have v13 : ¬ p 57 := (fun u => d558 a2 u v12)
  have v14 : ¬ p 112 := (fun u => d497 v9 v12 u)
  exact d538 v11 v13 v14

theorem c966 (p : Nat → Prop)
    (d387 : (p 18) → (p 26) → (p 41) → False)
    (d127 : (p 18) → (p 24) → (p 39) → False)
    (d14 : (p 39) → (p 41) → (p 110) → False)
    (d341 : (¬ p 24) → (¬ p 26) → (¬ p 110) → False)
    : (p 39) → (p 41) → (p 18) → False := by
  intro a0 a1 a2
  have v0 : ¬ p 26 := (fun u => d387 a2 u a1)
  have v1 : ¬ p 24 := (fun u => d127 a2 u a0)
  have v2 : ¬ p 110 := (fun u => d14 a0 a1 u)
  exact d341 v1 v0 v2

theorem c967 (p : Nat → Prop)
    (d356 : (p 51) → (p 53) → (p 89) → False)
    (d558 : (p 51) → (p 57) → (p 93) → False)
    (d497 : (p 89) → (p 93) → (p 112) → False)
    (d538 : (¬ p 53) → (¬ p 57) → (¬ p 112) → False)
    : (p 93) → (p 51) → (p 89) → False := by
  intro a0 a1 a2
  have v0 : ¬ p 53 := (fun u => d356 a1 u a2)
  have v1 : ¬ p 57 := (fun u => d558 a1 u a0)
  have v2 : ¬ p 112 := (fun u => d497 a2 a0 u)
  exact d538 v0 v1 v2

theorem c968 (p : Nat → Prop)
    (d495 : (p 40) → (p 41) → (p 118) → False)
    (d238 : (p 2) → (p 9) → (p 40) → False)
    (d564 : (¬ p 9) → (¬ p 10) → (¬ p 118) → False)
    : (p 40) → (p 2) → (¬ p 10) → (p 41) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 118 := (fun u => d495 a0 a3 u)
  have v1 : ¬ p 9 := (fun u => d238 a1 u a0)
  exact d564 v1 a2 v0

theorem c969 (p : Nat → Prop)
    (d38 : (p 3) → (p 6) → (p 51) → False)
    (d46 : (p 6) → (p 8) → (p 89) → False)
    (d505 : (¬ p 2) → (¬ p 3) → (¬ p 34) → False)
    (d452 : (p 2) → (p 6) → (p 37) → False)
    (d968 : (p 40) → (p 2) → (¬ p 10) → (p 41) → False)
    (d661 : (p 6) → (p 9) → (¬ p 40) → (p 2) → False)
    (d10 : (¬ p 37) → (¬ p 40) → (¬ p 90) → False)
    (d394 : (¬ p 8) → (¬ p 9) → (¬ p 109) → False)
    (d327 : (p 89) → (p 90) → (p 109) → False)
    : (p 6) → (¬ p 34) → (p 51) → (p 89) → (¬ p 10) → (p 41) → False := by
  intro a0 a1 a2 a3 a4 a5
  have v0 : ¬ p 3 := (fun u => d38 u a0 a2)
  have v1 : ¬ p 8 := (fun u => d46 a0 u a3)
  have v2 : p 2 := Classical.byContradiction (fun u => d505 u v0 a1)
  have v3 : ¬ p 37 := (fun u => d452 v2 a0 u)
  have v4 : ¬ p 40 := (fun u => d968 u v2 a4 a5)
  have v5 : ¬ p 9 := (fun u => d661 a0 u v4 v2)
  have v6 : p 90 := Classical.byContradiction (fun u => d10 v3 v4 u)
  have v7 : p 109 := Classical.byContradiction (fun u => d394 v1 v5 u)
  exact d327 a3 v6 v7

theorem c978 (p : Nat → Prop)
    (d5 : (p 5) → (p 8) → (p 78) → False)
    (d201 : (p 21) → (p 24) → (p 78) → False)
    (d75 : (¬ p 21) → (¬ p 23) → (¬ p 77) → False)
    (d370 : (p 5) → (p 7) → (p 77) → False)
    (d572 : (p 77) → (p 78) → (p 99) → False)
    (d111 : (¬ p 7) → (¬ p 8) → (¬ p 99) → False)
    : (p 78) → (¬ p 23) → (p 5) → (p 24) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 8 := (fun u => d5 a2 u a0)
  have v1 : ¬ p 21 := (fun u => d201 u a3 a0)
  have v2 : p 77 := Classical.byContradiction (fun u => d75 v1 a1 u)
  have v3 : ¬ p 7 := (fun u => d370 a2 u v2)
  have v4 : ¬ p 99 := (fun u => d572 v2 a0 u)
  exact d111 v3 v0 v4

theorem c979 (p : Nat → Prop)
    (d55 : (p 18) → (p 22) → (p 37) → False)
    (d870 : (p 36) → (¬ p 2) → (p 22) → (¬ p 37) → (p 18) → False)
    (d283 : (p 2) → (p 5) → (p 36) → False)
    : (p 36) → (p 5) → (p 18) → (p 22) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 37 := (fun u => d55 a2 a3 u)
  have v1 : p 2 := Classical.byContradiction (fun u => d870 a0 u a3 v0 a2)
  exact d283 v1 a1 a0

theorem c986 (p : Nat → Prop)
    (d238 : (p 2) → (p 9) → (p 40) → False)
    (d661 : (p 6) → (p 9) → (¬ p 40) → (p 2) → False)
    : (p 2) → (p 6) → (p 9) → False := by
  intro a0 a1 a2
  have v0 : ¬ p 40 := (fun u => d238 a0 a2 u)
  exact d661 a1 a2 v0 a0

theorem c987 (p : Nat → Prop)
    (d25 : (p 76) → (p 78) → (p 89) → False)
    (d356 : (p 51) → (p 53) → (p 89) → False)
    (d967 : (p 93) → (p 51) → (p 89) → False)
    (d35 : (¬ p 76) → (¬ p 82) → (¬ p 93) → False)
    (d460 : (p 78) → (p 82) → (p 112) → False)
    (d926 : (p 78) → (p 82) → (p 50) → False)
    (d538 : (¬ p 53) → (¬ p 57) → (¬ p 112) → False)
    (d235 : (¬ p 50) → (¬ p 54) → (¬ p 79) → False)
    (d944 : (p 54) → (p 57) → (p 34) → False)
    : (p 51) → (p 89) → (p 78) → (p 34) → (¬ p 79) → False := by
  intro a0 a1 a2 a3 a4
  have v0 : ¬ p 76 := (fun u => d25 u a2 a1)
  have v1 : ¬ p 53 := (fun u => d356 a0 u a1)
  have v2 : ¬ p 93 := (fun u => d967 u a0 a1)
  have v3 : p 82 := Classical.byContradiction (fun u => d35 v0 u v2)
  have v4 : ¬ p 112 := (fun u => d460 a2 v3 u)
  have v5 : ¬ p 50 := (fun u => d926 a2 v3 u)
  have v6 : p 57 := Classical.byContradiction (fun u => d538 v1 u v4)
  have v7 : p 54 := Classical.byContradiction (fun u => d235 v5 u a4)
  exact d944 v7 v6 a3

theorem c988 (p : Nat → Prop)
    (d503 : (p 5) → (p 9) → (p 79) → False)
    (d368 : (p 9) → (p 15) → (p 123) → False)
    (d72 : (p 5) → (p 15) → (p 85) → False)
    (d239 : (¬ p 79) → (¬ p 85) → (¬ p 123) → False)
    : (p 15) → (p 5) → (p 9) → False := by
  intro a0 a1 a2
  have v0 : ¬ p 79 := (fun u => d503 a1 a2 u)
  have v1 : ¬ p 123 := (fun u => d368 a2 a0 u)
  have v2 : ¬ p 85 := (fun u => d72 a1 a0 u)
  exact d239 v0 v2 v1

theorem c989 (p : Nat → Prop)
    (d778 : (p 60) → (p 49) → (p 55) → (¬ p 68) → False)
    (d321 : (p 55) → (p 56) → (p 126) → False)
    (d506 : (¬ p 56) → (¬ p 60) → (¬ p 136) → False)
    : (p 55) → (¬ p 136) → (p 126) → (¬ p 68) → (p 49) → False := by
  intro a0 a1 a2 a3 a4
  have v0 : ¬ p 60 := (fun u => d778 u a4 a0 a3)
  have v1 : ¬ p 56 := (fun u => d321 a0 u a2)
  exact d506 v1 v0 a1

theorem c991 (p : Nat → Prop)
    (d222 : (p 20) → (p 23) → (p 65) → False)
    (d442 : (¬ p 23) → (¬ p 25) → (¬ p 100) → False)
    (d75 : (¬ p 21) → (¬ p 23) → (¬ p 77) → False)
    (d324 : (p 7) → (p 9) → (p 100) → False)
    (d701 : (p 77) → (¬ p 4) → (p 78) → (¬ p 7) → (p 65) → False)
    : (p 65) → (¬ p 21) → (p 78) → (¬ p 4) → (¬ p 25) → (p 20) → (p 9) → False := by
  intro a0 a1 a2 a3 a4 a5 a6
  have v0 : ¬ p 23 := (fun u => d222 a5 u a0)
  have v1 : p 100 := Classical.byContradiction (fun u => d442 v0 a4 u)
  have v2 : p 77 := Classical.byContradiction (fun u => d75 a1 v0 u)
  have v3 : ¬ p 7 := (fun u => d324 u a6 v1)
  exact d701 v2 a3 a2 v3 a0

theorem c992 (p : Nat → Prop)
    (d442 : (¬ p 23) → (¬ p 25) → (¬ p 100) → False)
    (d75 : (¬ p 21) → (¬ p 23) → (¬ p 77) → False)
    (d324 : (p 7) → (p 9) → (p 100) → False)
    (d572 : (p 77) → (p 78) → (p 99) → False)
    (d111 : (¬ p 7) → (¬ p 8) → (¬ p 99) → False)
    : (¬ p 23) → (¬ p 21) → (¬ p 8) → (p 78) → (¬ p 25) → (p 9) → False := by
  intro a0 a1 a2 a3 a4 a5
  have v0 : p 100 := Classical.byContradiction (fun u => d442 a0 a4 u)
  have v1 : p 77 := Classical.byContradiction (fun u => d75 a1 a0 u)
  have v2 : ¬ p 7 := (fun u => d324 u a5 v0)
  have v3 : ¬ p 99 := (fun u => d572 v1 a3 u)
  exact d111 v2 a2 v3

theorem c993 (p : Nat → Prop)
    (d272 : (p 49) → (p 54) → (p 67) → False)
    (d532 : (p 54) → (p 59) → (p 122) → False)
    (d185 : (p 49) → (p 59) → (p 72) → False)
    (d323 : (¬ p 67) → (¬ p 72) → (¬ p 122) → False)
    : (p 59) → (p 54) → (p 49) → False := by
  intro a0 a1 a2
  have v0 : ¬ p 67 := (fun u => d272 a2 a1 u)
  have v1 : ¬ p 122 := (fun u => d532 a1 a0 u)
  have v2 : ¬ p 72 := (fun u => d185 a2 a0 u)
  exact d323 v0 v2 v1

theorem c994 (p : Nat → Prop)
    (d365 : (p 1) → (p 10) → (p 26) → False)
    (d359 : (p 20) → (p 26) → (p 68) → False)
    (d988 : (p 15) → (p 5) → (p 9) → False)
    (d395 : (p 1) → (p 4) → (p 20) → False)
    (d703 : (p 3) → (p 9) → (p 5) → False)
    (d549 : (¬ p 3) → (¬ p 4) → (¬ p 49) → False)
    (d986 : (p 2) → (p 6) → (p 9) → False)
    (d505 : (¬ p 2) → (¬ p 3) → (¬ p 34) → False)
    (d462 : (p 34) → (p 35) → (p 49) → False)
    (d941 : (p 52) → (p 49) → (¬ p 35) → (p 34) → False)
    (d536 : (p 6) → (p 9) → (p 90) → False)
    (d143 : (p 9) → (p 11) → (p 119) → False)
    (d739 : (p 137) → (p 6) → (¬ p 90) → (p 119) → (¬ p 15) → (p 136) → False)
    (d53 : (¬ p 10) → (¬ p 11) → (¬ p 126) → False)
    (d782 : (p 26) → (p 27) → (p 1) → (¬ p 11) → False)
    (d989 : (p 55) → (¬ p 136) → (p 126) → (¬ p 68) → (p 49) → False)
    (d444 : (¬ p 51) → (¬ p 55) → (¬ p 91) → False)
    (d566 : (p 91) → (p 92) → (p 126) → False)
    (d16 : (¬ p 64) → (¬ p 69) → (¬ p 92) → False)
    (d471 : (p 64) → (p 66) → (p 89) → False)
    (d384 : (¬ p 66) → (¬ p 71) → (¬ p 113) → False)
    (d86 : (p 49) → (p 58) → (p 71) → False)
    (d71 : (p 20) → (p 29) → (p 71) → False)
    (d8 : (¬ p 27) → (¬ p 29) → (¬ p 134) → False)
    (d443 : (p 119) → (p 121) → (p 134) → False)
    (d575 : (¬ p 54) → (¬ p 58) → (¬ p 121) → False)
    (d993 : (p 59) → (p 54) → (p 49) → False)
    (d560 : (¬ p 55) → (¬ p 59) → (¬ p 129) → False)
    (d345 : (p 126) → (p 129) → (p 135) → False)
    (d510 : (p 91) → (p 95) → (p 129) → False)
    (d12 : (¬ p 88) → (¬ p 95) → (¬ p 105) → False)
    (d931 : (p 38) → (p 105) → (p 102) → False)
    (d437 : (p 38) → (p 45) → (p 105) → False)
    (d366 : (¬ p 52) → (¬ p 56) → (¬ p 102) → False)
    (d417 : (¬ p 42) → (¬ p 45) → (¬ p 135) → False)
    (d502 : (p 34) → (p 42) → (p 56) → False)
    : (p 119) → (¬ p 113) → (¬ p 88) → (p 38) → (p 26) → (¬ p 51) → (p 89) → (p 5) → (p 137) → (¬ p 69) → (p 20) → (p 1) → (p 6) → (p 9) → False := by
  intro a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13
  have v0 : ¬ p 10 := (fun u => d365 a11 u a4)
  have v1 : ¬ p 68 := (fun u => d359 a10 a4 u)
  have v2 : ¬ p 15 := (fun u => d988 u a7 a13)
  have v3 : ¬ p 4 := (fun u => d395 a11 u a10)
  have v4 : ¬ p 3 := (fun u => d703 u a13 a7)
  have v5 : p 49 := Classical.byContradiction (fun u => d549 v4 v3 u)
  have v6 : ¬ p 2 := (fun u => d986 u a12 a13)
  have v7 : p 34 := Classical.byContradiction (fun u => d505 v6 v4 u)
  have v8 : ¬ p 35 := (fun u => d462 v7 u v5)
  have v9 : ¬ p 52 := (fun u => d941 u v5 v8 v7)
  have v10 : ¬ p 90 := (fun u => d536 a12 a13 u)
  have v11 : ¬ p 11 := (fun u => d143 a13 u a0)
  have v12 : ¬ p 136 := (fun u => d739 a8 a12 v10 a0 v2 u)
  have v13 : p 126 := Classical.byContradiction (fun u => d53 v0 v11 u)
  have v14 : ¬ p 27 := (fun u => d782 a4 u a11 v11)
  have v15 : ¬ p 55 := (fun u => d989 u v12 v13 v1 v5)
  have v16 : p 91 := Classical.byContradiction (fun u => d444 a5 v15 u)
  have v17 : ¬ p 92 := (fun u => d566 v16 u v13)
  have v18 : p 64 := Classical.byContradiction (fun u => d16 u a9 v17)
  have v19 : ¬ p 66 := (fun u => d471 v18 u a6)
  have v20 : p 71 := Classical.byContradiction (fun u => d384 v19 u a1)
  have v21 : ¬ p 58 := (fun u => d86 v5 u v20)
  have v22 : ¬ p 29 := (fun u => d71 a10 u v20)
  have v23 : p 134 := Classical.byContradiction (fun u => d8 v14 v22 u)
  have v24 : ¬ p 121 := (fun u => d443 a0 u v23)
  have v25 : p 54 := Classical.byContradiction (fun u => d575 u v21 v24)
  have v26 : ¬ p 59 := (fun u => d993 u v25 v5)
  have v27 : p 129 := Classical.byContradiction (fun u => d560 v15 v26 u)
  have v28 : ¬ p 135 := (fun u => d345 v13 v27 u)
  have v29 : ¬ p 95 := (fun u => d510 v16 u v27)
  have v30 : p 105 := Classical.byContradiction (fun u => d12 a2 v29 u)
  have v31 : ¬ p 102 := (fun u => d931 a3 v30 u)
  have v32 : ¬ p 45 := (fun u => d437 a3 u v30)
  have v33 : p 56 := Classical.byContradiction (fun u => d366 v9 u v31)
  have v34 : p 42 := Classical.byContradiction (fun u => d417 u v32 v28)
  exact d502 v7 v34 v33

theorem c995 (p : Nat → Prop)
    (d503 : (p 5) → (p 9) → (p 79) → False)
    (d986 : (p 2) → (p 6) → (p 9) → False)
    (d703 : (p 3) → (p 9) → (p 5) → False)
    (d505 : (¬ p 2) → (¬ p 3) → (¬ p 34) → False)
    (d987 : (p 51) → (p 89) → (p 78) → (p 34) → (¬ p 79) → False)
    (d5 : (p 5) → (p 8) → (p 78) → False)
    (d395 : (p 1) → (p 4) → (p 20) → False)
    (d549 : (¬ p 3) → (¬ p 4) → (¬ p 49) → False)
    (d462 : (p 34) → (p 35) → (p 49) → False)
    (d258 : (p 1) → (p 9) → (p 25) → False)
    (d879 : (p 20) → (p 26) → (p 21) → False)
    (d991 : (p 65) → (¬ p 21) → (p 78) → (¬ p 4) → (¬ p 25) → (p 20) → (p 9) → False)
    (d259 : (¬ p 35) → (¬ p 38) → (¬ p 65) → False)
    (d992 : (¬ p 23) → (¬ p 21) → (¬ p 8) → (p 78) → (¬ p 25) → (p 9) → False)
    (d336 : (p 1) → (p 7) → (p 23) → False)
    (d111 : (¬ p 7) → (¬ p 8) → (¬ p 99) → False)
    (d95 : (p 88) → (p 89) → (p 99) → False)
    (d674 : (p 113) → (p 99) → (p 78) → False)
    (d994 : (p 119) → (¬ p 113) → (¬ p 88) → (p 38) → (p 26) → (¬ p 51) → (p 89) → (p 5) → (p 137) → (¬ p 69) → (p 20) → (p 1) → (p 6) → (p 9) → False)
    (d49 : (¬ p 25) → (¬ p 27) → (¬ p 119) → False)
    (d398 : (p 1) → (p 11) → (p 27) → False)
    (d782 : (p 26) → (p 27) → (p 1) → (¬ p 11) → False)
    : (p 26) → (p 89) → (p 78) → (p 5) → (p 137) → (¬ p 69) → (p 20) → (p 1) → (p 6) → (p 9) → False := by
  intro a0 a1 a2 a3 a4 a5 a6 a7 a8 a9
  have v0 : ¬ p 79 := (fun u => d503 a3 a9 u)
  have v1 : ¬ p 2 := (fun u => d986 u a8 a9)
  have v2 : ¬ p 3 := (fun u => d703 u a9 a3)
  have v3 : p 34 := Classical.byContradiction (fun u => d505 v1 v2 u)
  have v4 : ¬ p 51 := (fun u => d987 u a1 a2 v3 v0)
  have v5 : ¬ p 8 := (fun u => d5 a3 u a2)
  have v6 : ¬ p 4 := (fun u => d395 a7 u a6)
  have v7 : p 49 := Classical.byContradiction (fun u => d549 v2 v6 u)
  have v8 : ¬ p 35 := (fun u => d462 v3 u v7)
  have v9 : ¬ p 25 := (fun u => d258 a7 a9 u)
  have v10 : ¬ p 21 := (fun u => d879 a6 a0 u)
  have v11 : ¬ p 65 := (fun u => d991 u v10 a2 v6 v9 a6 a9)
  have v12 : p 38 := Classical.byContradiction (fun u => d259 v8 u v11)
  have v13 : p 23 := Classical.byContradiction (fun u => d992 u v10 v5 a2 v9 a9)
  have v14 : ¬ p 7 := (fun u => d336 a7 u v13)
  have v15 : p 99 := Classical.byContradiction (fun u => d111 v14 v5 u)
  have v16 : ¬ p 88 := (fun u => d95 u a1 v15)
  have v17 : ¬ p 113 := (fun u => d674 u v15 a2)
  have v18 : ¬ p 119 := (fun u => d994 u v17 v16 v12 a0 v4 a1 a3 a4 a5 a6 a7 a8 a9)
  have v19 : p 27 := Classical.byContradiction (fun u => d49 v9 u v18)
  have v20 : ¬ p 11 := (fun u => d398 a7 u v19)
  exact d782 a0 v19 a7 v20

theorem c996 (p : Nat → Prop)
    (d25 : (p 76) → (p 78) → (p 89) → False)
    (d497 : (p 89) → (p 93) → (p 112) → False)
    (d460 : (p 78) → (p 82) → (p 112) → False)
    (d35 : (¬ p 76) → (¬ p 82) → (¬ p 93) → False)
    : (p 112) → (p 89) → (p 78) → False := by
  intro a0 a1 a2
  have v0 : ¬ p 76 := (fun u => d25 u a2 a1)
  have v1 : ¬ p 93 := (fun u => d497 a1 u a0)
  have v2 : ¬ p 82 := (fun u => d460 a2 u a0)
  exact d35 v0 v2 v1

theorem c997 (p : Nat → Prop)
    (d5 : (p 5) → (p 8) → (p 78) → False)
    (d988 : (p 15) → (p 5) → (p 9) → False)
    (d986 : (p 2) → (p 6) → (p 9) → False)
    (d170 : (¬ p 1) → (¬ p 2) → (¬ p 18) → False)
    (d395 : (p 1) → (p 4) → (p 20) → False)
    (d703 : (p 3) → (p 9) → (p 5) → False)
    (d549 : (¬ p 3) → (¬ p 4) → (¬ p 49) → False)
    (d505 : (¬ p 2) → (¬ p 3) → (¬ p 34) → False)
    (d462 : (p 34) → (p 35) → (p 49) → False)
    (d503 : (p 5) → (p 9) → (p 79) → False)
    (d258 : (p 1) → (p 9) → (p 25) → False)
    (d477 : (p 1) → (p 6) → (p 22) → False)
    (d536 : (p 6) → (p 9) → (p 90) → False)
    (d400 : (¬ p 22) → (¬ p 24) → (¬ p 89) → False)
    (d987 : (p 51) → (p 89) → (p 78) → (p 34) → (¬ p 79) → False)
    (d995 : (p 26) → (p 89) → (p 78) → (p 5) → (p 137) → (¬ p 69) → (p 20) → (p 1) → (p 6) → (p 9) → False)
    (d341 : (¬ p 24) → (¬ p 26) → (¬ p 110) → False)
    (d633 : (¬ p 24) → (p 91) → (¬ p 22) → (¬ p 26) → False)
    (d150 : (p 78) → (p 80) → (p 110) → False)
    (d444 : (¬ p 51) → (¬ p 55) → (¬ p 91) → False)
    (d583 : (p 49) → (p 55) → (p 68) → False)
    (d74 : (¬ p 63) → (¬ p 68) → (¬ p 80) → False)
    (d778 : (p 60) → (p 49) → (p 55) → (¬ p 68) → False)
    (d28 : (p 20) → (p 21) → (p 63) → False)
    (d811 : (¬ p 35) → (¬ p 38) → (¬ p 18) → (p 63) → False)
    (d42 : (p 49) → (p 50) → (p 63) → False)
    (d992 : (¬ p 23) → (¬ p 21) → (¬ p 8) → (p 78) → (¬ p 25) → (p 9) → False)
    (d235 : (¬ p 50) → (¬ p 54) → (¬ p 79) → False)
    (d944 : (p 54) → (p 57) → (p 34) → False)
    (d996 : (p 112) → (p 89) → (p 78) → False)
    (d538 : (¬ p 53) → (¬ p 57) → (¬ p 112) → False)
    (d884 : (¬ p 102) → (p 34) → (p 53) → (p 38) → False)
    (d149 : (p 38) → (p 42) → (p 102) → False)
    (d557 : (p 23) → (p 27) → (p 102) → False)
    (d628 : (p 53) → (p 34) → (p 56) → (¬ p 42) → False)
    (d49 : (¬ p 25) → (¬ p 27) → (¬ p 119) → False)
    (d506 : (¬ p 56) → (¬ p 60) → (¬ p 136) → False)
    (d739 : (p 137) → (p 6) → (¬ p 90) → (p 119) → (¬ p 15) → (p 136) → False)
    : (¬ p 24) → (p 78) → (p 5) → (p 137) → (¬ p 69) → (p 20) → (p 6) → (p 9) → (¬ p 18) → False := by
  intro a0 a1 a2 a3 a4 a5 a6 a7 a8
  have v0 : ¬ p 8 := (fun u => d5 a2 u a1)
  have v1 : ¬ p 15 := (fun u => d988 u a2 a7)
  have v2 : ¬ p 2 := (fun u => d986 u a6 a7)
  have v3 : p 1 := Classical.byContradiction (fun u => d170 u v2 a8)
  have v4 : ¬ p 4 := (fun u => d395 v3 u a5)
  have v5 : ¬ p 3 := (fun u => d703 u a7 a2)
  have v6 : p 49 := Classical.byContradiction (fun u => d549 v5 v4 u)
  have v7 : p 34 := Classical.byContradiction (fun u => d505 v2 v5 u)
  have v8 : ¬ p 35 := (fun u => d462 v7 u v6)
  have v9 : ¬ p 79 := (fun u => d503 a2 a7 u)
  have v10 : ¬ p 25 := (fun u => d258 v3 a7 u)
  have v11 : ¬ p 22 := (fun u => d477 v3 a6 u)
  have v12 : ¬ p 90 := (fun u => d536 a6 a7 u)
  have v13 : p 89 := Classical.byContradiction (fun u => d400 v11 a0 u)
  have v14 : ¬ p 51 := (fun u => d987 u v13 a1 v7 v9)
  have v15 : ¬ p 26 := (fun u => d995 u v13 a1 a2 a3 a4 a5 v3 a6 a7)
  have v16 : p 110 := Classical.byContradiction (fun u => d341 a0 v15 u)
  have v17 : ¬ p 91 := (fun u => d633 a0 u v11 v15)
  have v18 : ¬ p 80 := (fun u => d150 a1 u v16)
  have v19 : p 55 := Classical.byContradiction (fun u => d444 v14 u v17)
  have v20 : ¬ p 68 := (fun u => d583 v6 v19 u)
  have v21 : p 63 := Classical.byContradiction (fun u => d74 u v20 v18)
  have v22 : ¬ p 60 := (fun u => d778 u v6 v19 v20)
  have v23 : ¬ p 21 := (fun u => d28 a5 u v21)
  have v24 : p 38 := Classical.byContradiction (fun u => d811 v8 u a8 v21)
  have v25 : ¬ p 50 := (fun u => d42 v6 u v21)
  have v26 : p 23 := Classical.byContradiction (fun u => d992 u v23 v0 a1 v10 a7)
  have v27 : p 54 := Classical.byContradiction (fun u => d235 v25 u v9)
  have v28 : ¬ p 57 := (fun u => d944 v27 u v7)
  have v29 : ¬ p 112 := (fun u => d996 u v13 a1)
  have v30 : p 53 := Classical.byContradiction (fun u => d538 u v28 v29)
  have v31 : p 102 := Classical.byContradiction (fun u => d884 u v7 v30 v24)
  have v32 : ¬ p 42 := (fun u => d149 v24 u v31)
  have v33 : ¬ p 27 := (fun u => d557 v26 u v31)
  have v34 : ¬ p 56 := (fun u => d628 v30 v7 u v32)
  have v35 : p 119 := Classical.byContradiction (fun u => d49 v10 v33 u)
  have v36 : p 136 := Classical.byContradiction (fun u => d506 v34 v22 u)
  exact d739 a3 a6 v12 v35 v1 v36

theorem c998 (p : Nat → Prop)
    (d986 : (p 2) → (p 6) → (p 9) → False)
    (d170 : (¬ p 1) → (¬ p 2) → (¬ p 18) → False)
    (d5 : (p 5) → (p 8) → (p 78) → False)
    (d997 : (¬ p 24) → (p 78) → (p 5) → (p 137) → (¬ p 69) → (p 20) → (p 6) → (p 9) → (¬ p 18) → False)
    (d978 : (p 78) → (¬ p 23) → (p 5) → (p 24) → False)
    (d308 : (p 23) → (p 24) → (p 99) → False)
    (d336 : (p 1) → (p 7) → (p 23) → False)
    (d111 : (¬ p 7) → (¬ p 8) → (¬ p 99) → False)
    : (p 78) → (p 5) → (p 137) → (¬ p 69) → (p 20) → (p 6) → (p 9) → (¬ p 18) → False := by
  intro a0 a1 a2 a3 a4 a5 a6 a7
  have v0 : ¬ p 2 := (fun u => d986 u a5 a6)
  have v1 : p 1 := Classical.byContradiction (fun u => d170 u v0 a7)
  have v2 : ¬ p 8 := (fun u => d5 a1 u a0)
  have v3 : p 24 := Classical.byContradiction (fun u => d997 u a0 a1 a2 a3 a4 a5 a6 a7)
  have v4 : p 23 := Classical.byContradiction (fun u => d978 a0 u a1 v3)
  have v5 : ¬ p 99 := (fun u => d308 v4 v3 u)
  have v6 : ¬ p 7 := (fun u => d336 v1 u v4)
  exact d111 v6 v2 v5

theorem c999 (p : Nat → Prop)
    (d351 : (p 34) → (p 39) → (p 53) → False)
    (d884 : (¬ p 102) → (p 34) → (p 53) → (p 38) → False)
    (d592 : (p 102) → (p 107) → (p 137) → False)
    (d149 : (p 38) → (p 42) → (p 102) → False)
    (d83 : (¬ p 99) → (¬ p 107) → (¬ p 116) → False)
    (d518 : (¬ p 39) → (¬ p 42) → (¬ p 111) → False)
    (d228 : (p 111) → (p 116) → (p 137) → False)
    : (p 53) → (p 38) → (¬ p 99) → (p 34) → (p 137) → False := by
  intro a0 a1 a2 a3 a4
  have v0 : ¬ p 39 := (fun u => d351 a3 u a0)
  have v1 : p 102 := Classical.byContradiction (fun u => d884 u a3 a0 a1)
  have v2 : ¬ p 107 := (fun u => d592 v1 u a4)
  have v3 : ¬ p 42 := (fun u => d149 a1 u v1)
  have v4 : p 116 := Classical.byContradiction (fun u => d83 a2 v2 u)
  have v5 : p 111 := Classical.byContradiction (fun u => d518 v0 v3 u)
  exact d228 v5 v4 a4

theorem c1000 (p : Nat → Prop)
    (d592 : (p 102) → (p 107) → (p 137) → False)
    (d557 : (p 23) → (p 27) → (p 102) → False)
    (d83 : (¬ p 99) → (¬ p 107) → (¬ p 116) → False)
    (d49 : (¬ p 25) → (¬ p 27) → (¬ p 119) → False)
    (d220 : (p 8) → (p 16) → (p 116) → False)
    (d116 : (p 119) → (p 124) → (p 137) → False)
    (d153 : (¬ p 15) → (¬ p 16) → (¬ p 151) → False)
    (d43 : (¬ p 90) → (¬ p 97) → (¬ p 124) → False)
    (d585 : (p 96) → (p 97) → (p 151) → False)
    (d41 : (p 115) → (p 116) → (p 151) → False)
    (d203 : (¬ p 89) → (¬ p 96) → (¬ p 115) → False)
    : (p 102) → (¬ p 89) → (p 8) → (¬ p 99) → (p 23) → (¬ p 15) → (p 137) → (¬ p 25) → (¬ p 90) → False := by
  intro a0 a1 a2 a3 a4 a5 a6 a7 a8
  have v0 : ¬ p 107 := (fun u => d592 a0 u a6)
  have v1 : ¬ p 27 := (fun u => d557 a4 u a0)
  have v2 : p 116 := Classical.byContradiction (fun u => d83 a3 v0 u)
  have v3 : p 119 := Classical.byContradiction (fun u => d49 a7 v1 u)
  have v4 : ¬ p 16 := (fun u => d220 a2 u v2)
  have v5 : ¬ p 124 := (fun u => d116 v3 u a6)
  have v6 : p 151 := Classical.byContradiction (fun u => d153 a5 v4 u)
  have v7 : p 97 := Classical.byContradiction (fun u => d43 a8 u v5)
  have v8 : ¬ p 96 := (fun u => d585 u v7 v6)
  have v9 : ¬ p 115 := (fun u => d41 u v2 v6)
  exact d203 a1 v8 v9

theorem c1002 (p : Nat → Prop)
    (d240 : (p 37) → (p 46) → (p 96) → False)
    (d585 : (p 96) → (p 97) → (p 151) → False)
    (d521 : (¬ p 43) → (¬ p 46) → (¬ p 141) → False)
    (d43 : (¬ p 90) → (¬ p 97) → (¬ p 124) → False)
    (d167 : (p 39) → (p 43) → (p 112) → False)
    (d116 : (p 119) → (p 124) → (p 137) → False)
    (d518 : (¬ p 39) → (¬ p 42) → (¬ p 111) → False)
    (d49 : (¬ p 25) → (¬ p 27) → (¬ p 119) → False)
    (d332 : (p 24) → (p 27) → (p 111) → False)
    : (p 96) → (¬ p 141) → (p 151) → (p 112) → (¬ p 42) → (p 24) → (p 137) → (¬ p 25) → (p 37) → (¬ p 90) → False := by
  intro a0 a1 a2 a3 a4 a5 a6 a7 a8 a9
  have v0 : ¬ p 46 := (fun u => d240 a8 u a0)
  have v1 : ¬ p 97 := (fun u => d585 a0 u a2)
  have v2 : p 43 := Classical.byContradiction (fun u => d521 u v0 a1)
  have v3 : p 124 := Classical.byContradiction (fun u => d43 a9 v1 u)
  have v4 : ¬ p 39 := (fun u => d167 u v2 a3)
  have v5 : ¬ p 119 := (fun u => d116 u v3 a6)
  have v6 : p 111 := Classical.byContradiction (fun u => d518 v4 a4 u)
  have v7 : p 27 := Classical.byContradiction (fun u => d49 a7 u v5)
  exact d332 a5 v7 v6

theorem c1003 (p : Nat → Prop)
    (d70 : (p 8) → (p 12) → (p 112) → False)
    (d423 : (p 8) → (p 11) → (p 111) → False)
    (d422 : (p 111) → (p 112) → (p 133) → False)
    (d166 : (¬ p 11) → (¬ p 12) → (¬ p 133) → False)
    : (p 111) → (p 112) → (p 8) → False := by
  intro a0 a1 a2
  have v0 : ¬ p 12 := (fun u => d70 a2 u a1)
  have v1 : ¬ p 11 := (fun u => d423 a2 u a0)
  have v2 : ¬ p 133 := (fun u => d422 a0 a1 u)
  exact d166 v1 v0 v2

theorem c1004 (p : Nat → Prop)
    (d496 : (p 141) → (p 142) → (p 151) → False)
    (d1002 : (p 96) → (¬ p 141) → (p 151) → (p 112) → (¬ p 42) → (p 24) → (p 137) → (¬ p 25) → (p 37) → (¬ p 90) → False)
    (d696 : (p 39) → (p 34) → (¬ p 141) → (p 115) → (¬ p 53) → False)
    (d203 : (¬ p 89) → (¬ p 96) → (¬ p 115) → False)
    : (p 151) → (p 39) → (p 142) → (p 112) → (¬ p 42) → (¬ p 53) → (¬ p 89) → (p 24) → (p 34) → (p 137) → (¬ p 25) → (p 37) → (¬ p 90) → False := by
  intro a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12
  have v0 : ¬ p 141 := (fun u => d496 u a2 a0)
  have v1 : ¬ p 96 := (fun u => d1002 u v0 a0 a3 a4 a7 a9 a10 a11 a12)
  have v2 : ¬ p 115 := (fun u => d696 a1 a8 v0 u a5)
  exact d203 a6 v1 v2

theorem c1005 (p : Nat → Prop)
    (d536 : (p 6) → (p 9) → (p 90) → False)
    (d103 : (p 9) → (p 16) → (p 124) → False)
    (d499 : (p 6) → (p 16) → (p 97) → False)
    (d43 : (¬ p 90) → (¬ p 97) → (¬ p 124) → False)
    : (p 16) → (p 6) → (p 9) → False := by
  intro a0 a1 a2
  have v0 : ¬ p 90 := (fun u => d536 a1 a2 u)
  have v1 : ¬ p 124 := (fun u => d103 a2 a0 u)
  have v2 : ¬ p 97 := (fun u => d499 a1 a0 u)
  exact d43 v0 v2 v1

theorem c1006 (p : Nat → Prop)
    (d258 : (p 1) → (p 9) → (p 25) → False)
    (d398 : (p 1) → (p 11) → (p 27) → False)
    (d143 : (p 9) → (p 11) → (p 119) → False)
    (d49 : (¬ p 25) → (¬ p 27) → (¬ p 119) → False)
    : (p 11) → (p 1) → (p 9) → False := by
  intro a0 a1 a2
  have v0 : ¬ p 25 := (fun u => d258 a1 a2 u)
  have v1 : ¬ p 27 := (fun u => d398 a1 a0 u)
  have v2 : ¬ p 119 := (fun u => d143 a2 a0 u)
  exact d49 v0 v1 v2

theorem c1007 (p : Nat → Prop)
    (d357 : (p 37) → (p 39) → (p 89) → False)
    (d203 : (¬ p 89) → (¬ p 96) → (¬ p 115) → False)
    (d696 : (p 39) → (p 34) → (¬ p 141) → (p 115) → (¬ p 53) → False)
    (d472 : (p 112) → (p 115) → (p 141) → False)
    (d618 : (p 60) → (p 115) → (p 141) → False)
    (d538 : (¬ p 53) → (¬ p 57) → (¬ p 112) → False)
    (d506 : (¬ p 56) → (¬ p 60) → (¬ p 136) → False)
    (d533 : (p 56) → (p 57) → (p 133) → False)
    : (p 39) → (p 133) → (¬ p 53) → (¬ p 96) → (¬ p 136) → (p 34) → (p 37) → False := by
  intro a0 a1 a2 a3 a4 a5 a6
  have v0 : ¬ p 89 := (fun u => d357 a6 a0 u)
  have v1 : p 115 := Classical.byContradiction (fun u => d203 v0 a3 u)
  have v2 : p 141 := Classical.byContradiction (fun u => d696 a0 a5 u v1 a2)
  have v3 : ¬ p 112 := (fun u => d472 u v1 v2)
  have v4 : ¬ p 60 := (fun u => d618 u v1 v2)
  have v5 : p 57 := Classical.byContradiction (fun u => d538 a2 u v3)
  have v6 : p 56 := Classical.byContradiction (fun u => d506 u v4 a4)
  exact d533 v6 v5 a1

theorem c1008 (p : Nat → Prop)
    (d1007 : (p 39) → (p 133) → (¬ p 53) → (¬ p 96) → (¬ p 136) → (p 34) → (p 37) → False)
    (d58 : (¬ p 36) → (¬ p 39) → (¬ p 78) → False)
    (d518 : (¬ p 39) → (¬ p 42) → (¬ p 111) → False)
    (d76 : (p 34) → (p 36) → (p 50) → False)
    (d422 : (p 111) → (p 112) → (p 133) → False)
    (d235 : (¬ p 50) → (¬ p 54) → (¬ p 79) → False)
    (d538 : (¬ p 53) → (¬ p 57) → (¬ p 112) → False)
    (d944 : (p 54) → (p 57) → (p 34) → False)
    : (p 133) → (¬ p 42) → (¬ p 53) → (¬ p 96) → (¬ p 136) → (¬ p 78) → (p 34) → (¬ p 79) → (p 37) → False := by
  intro a0 a1 a2 a3 a4 a5 a6 a7 a8
  have v0 : ¬ p 39 := (fun u => d1007 u a0 a2 a3 a4 a6 a8)
  have v1 : p 36 := Classical.byContradiction (fun u => d58 u v0 a5)
  have v2 : p 111 := Classical.byContradiction (fun u => d518 v0 a1 u)
  have v3 : ¬ p 50 := (fun u => d76 a6 v1 u)
  have v4 : ¬ p 112 := (fun u => d422 v2 u a0)
  have v5 : p 54 := Classical.byContradiction (fun u => d235 v3 u a7)
  have v6 : p 57 := Classical.byContradiction (fun u => d538 a2 u v4)
  exact d944 v5 v6 a6

theorem c1009 (p : Nat → Prop)
    (d232 : (p 88) → (p 92) → (p 102) → False)
    (d961 : (p 92) → (p 119) → (¬ p 105) → (¬ p 40) → (p 122) → (p 102) → False)
    (d12 : (¬ p 88) → (¬ p 95) → (¬ p 105) → False)
    (d323 : (¬ p 67) → (¬ p 72) → (¬ p 122) → False)
    (d304 : (p 93) → (p 95) → (p 140) → False)
    (d432 : (p 20) → (p 30) → (p 72) → False)
    (d427 : (¬ p 28) → (¬ p 30) → (¬ p 140) → False)
    : (p 92) → (¬ p 105) → (p 102) → (p 119) → (¬ p 67) → (p 93) → (¬ p 28) → (p 20) → (¬ p 40) → False := by
  intro a0 a1 a2 a3 a4 a5 a6 a7 a8
  have v0 : ¬ p 88 := (fun u => d232 u a0 a2)
  have v1 : ¬ p 122 := (fun u => d961 a0 a3 a1 a8 u a2)
  have v2 : p 95 := Classical.byContradiction (fun u => d12 v0 u a1)
  have v3 : p 72 := Classical.byContradiction (fun u => d323 a4 u v1)
  have v4 : ¬ p 140 := (fun u => d304 a5 v2 u)
  have v5 : ¬ p 30 := (fun u => d432 a7 u v3)
  exact d427 a6 v5 v4

theorem c1010 (p : Nat → Prop)
    (d1009 : (p 92) → (¬ p 105) → (p 102) → (p 119) → (¬ p 67) → (p 93) → (¬ p 28) → (p 20) → (¬ p 40) → False)
    (d16 : (¬ p 64) → (¬ p 69) → (¬ p 92) → False)
    (d833 : (p 88) → (p 93) → (p 64) → False)
    (d632 : (p 64) → (p 68) → (p 49) → False)
    (d105 : (p 49) → (p 51) → (p 64) → False)
    (d12 : (¬ p 88) → (¬ p 95) → (¬ p 105) → False)
    (d778 : (p 60) → (p 49) → (p 55) → (¬ p 68) → False)
    (d444 : (¬ p 51) → (¬ p 55) → (¬ p 91) → False)
    (d560 : (¬ p 55) → (¬ p 59) → (¬ p 129) → False)
    (d510 : (p 91) → (p 95) → (p 129) → False)
    : (¬ p 105) → (p 60) → (p 102) → (p 119) → (¬ p 59) → (¬ p 67) → (p 93) → (¬ p 28) → (p 49) → (¬ p 69) → (p 20) → (¬ p 40) → False := by
  intro a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11
  have v0 : ¬ p 92 := (fun u => d1009 u a0 a2 a3 a5 a6 a7 a10 a11)
  have v1 : p 64 := Classical.byContradiction (fun u => d16 u a9 v0)
  have v2 : ¬ p 88 := (fun u => d833 u a6 v1)
  have v3 : ¬ p 68 := (fun u => d632 v1 u a8)
  have v4 : ¬ p 51 := (fun u => d105 a8 u v1)
  have v5 : p 95 := Classical.byContradiction (fun u => d12 v2 u a0)
  have v6 : ¬ p 55 := (fun u => d778 a1 a8 u v3)
  have v7 : p 91 := Classical.byContradiction (fun u => d444 v4 v6 u)
  have v8 : p 129 := Classical.byContradiction (fun u => d560 v6 a4 u)
  exact d510 v7 v5 v8

theorem c1011 (p : Nat → Prop)
    (d395 : (p 1) → (p 4) → (p 20) → False)
    (d703 : (p 3) → (p 9) → (p 5) → False)
    (d549 : (¬ p 3) → (¬ p 4) → (¬ p 49) → False)
    (d462 : (p 34) → (p 35) → (p 49) → False)
    (d941 : (p 52) → (p 49) → (¬ p 35) → (p 34) → False)
    (d503 : (p 5) → (p 9) → (p 79) → False)
    (d1006 : (p 11) → (p 1) → (p 9) → False)
    (d258 : (p 1) → (p 9) → (p 25) → False)
    (d1008 : (p 133) → (¬ p 42) → (¬ p 53) → (¬ p 96) → (¬ p 136) → (¬ p 78) → (p 34) → (¬ p 79) → (p 37) → False)
    (d166 : (¬ p 11) → (¬ p 12) → (¬ p 133) → False)
    (d2 : (p 5) → (p 12) → (p 82) → False)
    (d191 : (p 1) → (p 12) → (p 28) → False)
    (d301 : (p 9) → (p 12) → (p 120) → False)
    (d173 : (¬ p 40) → (¬ p 43) → (¬ p 120) → False)
    (d52 : (p 34) → (p 43) → (p 57) → False)
    (d538 : (¬ p 53) → (¬ p 57) → (¬ p 112) → False)
    (d167 : (p 39) → (p 43) → (p 112) → False)
    (d58 : (¬ p 36) → (¬ p 39) → (¬ p 78) → False)
    (d518 : (¬ p 39) → (¬ p 42) → (¬ p 111) → False)
    (d76 : (p 34) → (p 36) → (p 50) → False)
    (d537 : (p 36) → (p 37) → (p 76) → False)
    (d228 : (p 111) → (p 116) → (p 137) → False)
    (d235 : (¬ p 50) → (¬ p 54) → (¬ p 79) → False)
    (d35 : (¬ p 76) → (¬ p 82) → (¬ p 93) → False)
    (d272 : (p 49) → (p 54) → (p 67) → False)
    (d993 : (p 59) → (p 54) → (p 49) → False)
    (d497 : (p 89) → (p 93) → (p 112) → False)
    (d85 : (p 93) → (p 97) → (p 142) → False)
    (d400 : (¬ p 22) → (¬ p 24) → (¬ p 89) → False)
    (d141 : (¬ p 57) → (¬ p 61) → (¬ p 142) → False)
    (d332 : (p 24) → (p 27) → (p 111) → False)
    (d456 : (p 56) → (p 61) → (p 137) → False)
    (d49 : (¬ p 25) → (¬ p 27) → (¬ p 119) → False)
    (d366 : (¬ p 52) → (¬ p 56) → (¬ p 102) → False)
    (d506 : (¬ p 56) → (¬ p 60) → (¬ p 136) → False)
    (d592 : (p 102) → (p 107) → (p 137) → False)
    (d83 : (¬ p 99) → (¬ p 107) → (¬ p 116) → False)
    (d1010 : (¬ p 105) → (p 60) → (p 102) → (p 119) → (¬ p 59) → (¬ p 67) → (p 93) → (¬ p 28) → (p 49) → (¬ p 69) → (p 20) → (¬ p 40) → False)
    (d579 : (p 102) → (p 105) → (p 135) → False)
    (d297 : (p 99) → (p 105) → (p 114) → False)
    (d417 : (¬ p 42) → (¬ p 45) → (¬ p 135) → False)
    (d125 : (¬ p 78) → (¬ p 84) → (¬ p 114) → False)
    (d280 : (p 36) → (p 45) → (p 84) → False)
    : (¬ p 42) → (¬ p 53) → (¬ p 96) → (p 97) → (¬ p 136) → (¬ p 78) → (p 34) → (p 5) → (p 137) → (¬ p 69) → (¬ p 22) → (p 20) → (p 1) → (p 37) → (p 9) → (¬ p 40) → False := by
  intro a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15
  have v0 : ¬ p 4 := (fun u => d395 a12 u a11)
  have v1 : ¬ p 3 := (fun u => d703 u a14 a7)
  have v2 : p 49 := Classical.byContradiction (fun u => d549 v1 v0 u)
  have v3 : ¬ p 35 := (fun u => d462 a6 u v2)
  have v4 : ¬ p 52 := (fun u => d941 u v2 v3 a6)
  have v5 : ¬ p 79 := (fun u => d503 a7 a14 u)
  have v6 : ¬ p 11 := (fun u => d1006 u a12 a14)
  have v7 : ¬ p 25 := (fun u => d258 a12 a14 u)
  have v8 : ¬ p 133 := (fun u => d1008 u a0 a1 a2 a4 a5 a6 v5 a13)
  have v9 : p 12 := Classical.byContradiction (fun u => d166 v6 u v8)
  have v10 : ¬ p 82 := (fun u => d2 a7 v9 u)
  have v11 : ¬ p 28 := (fun u => d191 a12 v9 u)
  have v12 : ¬ p 120 := (fun u => d301 a14 v9 u)
  have v13 : p 43 := Classical.byContradiction (fun u => d173 a15 u v12)
  have v14 : ¬ p 57 := (fun u => d52 a6 v13 u)
  have v15 : p 112 := Classical.byContradiction (fun u => d538 a1 v14 u)
  have v16 : ¬ p 39 := (fun u => d167 u v13 v15)
  have v17 : p 36 := Classical.byContradiction (fun u => d58 u v16 a5)
  have v18 : p 111 := Classical.byContradiction (fun u => d518 v16 a0 u)
  have v19 : ¬ p 50 := (fun u => d76 a6 v17 u)
  have v20 : ¬ p 76 := (fun u => d537 v17 a13 u)
  have v21 : ¬ p 116 := (fun u => d228 v18 u a8)
  have v22 : p 54 := Classical.byContradiction (fun u => d235 v19 u v5)
  have v23 : p 93 := Classical.byContradiction (fun u => d35 v20 v10 u)
  have v24 : ¬ p 67 := (fun u => d272 v2 v22 u)
  have v25 : ¬ p 59 := (fun u => d993 u v22 v2)
  have v26 : ¬ p 89 := (fun u => d497 u v23 v15)
  have v27 : ¬ p 142 := (fun u => d85 v23 a3 u)
  have v28 : p 24 := Classical.byContradiction (fun u => d400 a10 u v26)
  have v29 : p 61 := Classical.byContradiction (fun u => d141 v14 u v27)
  have v30 : ¬ p 27 := (fun u => d332 v28 u v18)
  have v31 : ¬ p 56 := (fun u => d456 u v29 a8)
  have v32 : p 119 := Classical.byContradiction (fun u => d49 v7 v30 u)
  have v33 : p 102 := Classical.byContradiction (fun u => d366 v4 v31 u)
  have v34 : p 60 := Classical.byContradiction (fun u => d506 v31 u a4)
  have v35 : ¬ p 107 := (fun u => d592 v33 u a8)
  have v36 : p 99 := Classical.byContradiction (fun u => d83 u v35 v21)
  have v37 : p 105 := Classical.byContradiction (fun u => d1010 u v34 v33 v32 v25 v24 v23 v11 v2 a9 a11 a15)
  have v38 : ¬ p 135 := (fun u => d579 v33 v37 u)
  have v39 : ¬ p 114 := (fun u => d297 v36 v37 u)
  have v40 : p 45 := Classical.byContradiction (fun u => d417 a0 u v38)
  have v41 : p 84 := Classical.byContradiction (fun u => d125 a5 u v39)
  exact d280 v17 v40 v41

theorem c1012 (p : Nat → Prop)
    (d462 : (p 34) → (p 35) → (p 49) → False)
    (d941 : (p 52) → (p 49) → (¬ p 35) → (p 34) → False)
    (d502 : (p 34) → (p 42) → (p 56) → False)
    (d354 : (p 37) → (p 42) → (p 92) → False)
    (d366 : (¬ p 52) → (¬ p 56) → (¬ p 102) → False)
    (d691 : (p 38) → (p 42) → (¬ p 56) → (p 34) → False)
    (d506 : (¬ p 56) → (¬ p 60) → (¬ p 136) → False)
    (d16 : (¬ p 64) → (¬ p 69) → (¬ p 92) → False)
    (d811 : (¬ p 35) → (¬ p 38) → (¬ p 18) → (p 63) → False)
    (d632 : (p 64) → (p 68) → (p 49) → False)
    (d105 : (p 49) → (p 51) → (p 64) → False)
    (d74 : (¬ p 63) → (¬ p 68) → (¬ p 80) → False)
    (d778 : (p 60) → (p 49) → (p 55) → (¬ p 68) → False)
    (d147 : (p 5) → (p 10) → (p 80) → False)
    (d444 : (¬ p 51) → (¬ p 55) → (¬ p 91) → False)
    (d53 : (¬ p 10) → (¬ p 11) → (¬ p 126) → False)
    (d31 : (p 37) → (p 41) → (p 91) → False)
    (d205 : (p 101) → (p 102) → (p 126) → False)
    (d23 : (¬ p 38) → (¬ p 41) → (¬ p 101) → False)
    : (p 42) → (¬ p 136) → (p 49) → (p 34) → (p 5) → (¬ p 69) → (¬ p 11) → (p 37) → (¬ p 18) → False := by
  intro a0 a1 a2 a3 a4 a5 a6 a7 a8
  have v0 : ¬ p 35 := (fun u => d462 a3 u a2)
  have v1 : ¬ p 52 := (fun u => d941 u a2 v0 a3)
  have v2 : ¬ p 56 := (fun u => d502 a3 a0 u)
  have v3 : ¬ p 92 := (fun u => d354 a7 a0 u)
  have v4 : p 102 := Classical.byContradiction (fun u => d366 v1 v2 u)
  have v5 : ¬ p 38 := (fun u => d691 u a0 v2 a3)
  have v6 : p 60 := Classical.byContradiction (fun u => d506 v2 u a1)
  have v7 : p 64 := Classical.byContradiction (fun u => d16 u a5 v3)
  have v8 : ¬ p 63 := (fun u => d811 v0 v5 a8 u)
  have v9 : ¬ p 68 := (fun u => d632 v7 u a2)
  have v10 : ¬ p 51 := (fun u => d105 a2 u v7)
  have v11 : p 80 := Classical.byContradiction (fun u => d74 v8 v9 u)
  have v12 : ¬ p 55 := (fun u => d778 v6 a2 u v9)
  have v13 : ¬ p 10 := (fun u => d147 a4 u v11)
  have v14 : p 91 := Classical.byContradiction (fun u => d444 v10 v12 u)
  have v15 : p 126 := Classical.byContradiction (fun u => d53 v13 a6 u)
  have v16 : ¬ p 41 := (fun u => d31 a7 u v14)
  have v17 : ¬ p 101 := (fun u => d205 u v4 v15)
  exact d23 v5 v16 v17

theorem c1013 (p : Nat → Prop)
    (d778 : (p 60) → (p 49) → (p 55) → (¬ p 68) → False)
    (d74 : (¬ p 63) → (¬ p 68) → (¬ p 80) → False)
    (d444 : (¬ p 51) → (¬ p 55) → (¬ p 91) → False)
    (d560 : (¬ p 55) → (¬ p 59) → (¬ p 129) → False)
    (d510 : (p 91) → (p 95) → (p 129) → False)
    (d379 : (p 80) → (p 84) → (p 129) → False)
    (d780 : (p 99) → (p 114) → (¬ p 95) → (p 89) → False)
    (d125 : (¬ p 78) → (¬ p 84) → (¬ p 114) → False)
    : (¬ p 68) → (¬ p 63) → (¬ p 59) → (p 89) → (p 99) → (¬ p 51) → (p 60) → (¬ p 78) → (p 49) → False := by
  intro a0 a1 a2 a3 a4 a5 a6 a7 a8
  have v0 : ¬ p 55 := (fun u => d778 a6 a8 u a0)
  have v1 : p 80 := Classical.byContradiction (fun u => d74 a1 a0 u)
  have v2 : p 91 := Classical.byContradiction (fun u => d444 a5 v0 u)
  have v3 : p 129 := Classical.byContradiction (fun u => d560 v0 a2 u)
  have v4 : ¬ p 95 := (fun u => d510 v2 u v3)
  have v5 : ¬ p 84 := (fun u => d379 v1 u v3)
  have v6 : ¬ p 114 := (fun u => d780 a4 u v4 a3)
  exact d125 a7 v5 v6

theorem c1014 (p : Nat → Prop)
    (d259 : (¬ p 35) → (¬ p 38) → (¬ p 65) → False)
    (d811 : (¬ p 35) → (¬ p 38) → (¬ p 18) → (p 63) → False)
    (d1013 : (¬ p 68) → (¬ p 63) → (¬ p 59) → (p 89) → (p 99) → (¬ p 51) → (p 60) → (¬ p 78) → (p 49) → False)
    (d583 : (p 49) → (p 55) → (p 68) → False)
    (d221 : (p 65) → (p 68) → (p 101) → False)
    (d444 : (¬ p 51) → (¬ p 55) → (¬ p 91) → False)
    (d23 : (¬ p 38) → (¬ p 41) → (¬ p 101) → False)
    (d31 : (p 37) → (p 41) → (p 91) → False)
    : (¬ p 38) → (¬ p 59) → (p 89) → (p 99) → (¬ p 51) → (p 60) → (¬ p 78) → (¬ p 35) → (p 49) → (p 37) → (¬ p 18) → False := by
  intro a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10
  have v0 : p 65 := Classical.byContradiction (fun u => d259 a7 a0 u)
  have v1 : ¬ p 63 := (fun u => d811 a7 a0 a10 u)
  have v2 : p 68 := Classical.byContradiction (fun u => d1013 u v1 a1 a2 a3 a4 a5 a6 a8)
  have v3 : ¬ p 55 := (fun u => d583 a8 u v2)
  have v4 : ¬ p 101 := (fun u => d221 v0 v2 u)
  have v5 : p 91 := Classical.byContradiction (fun u => d444 a4 v3 u)
  have v6 : p 41 := Classical.byContradiction (fun u => d23 a0 u v4)
  exact d31 a9 v6 v5

theorem c1015 (p : Nat → Prop)
    (d536 : (p 6) → (p 9) → (p 90) → False)
    (d10 : (¬ p 37) → (¬ p 40) → (¬ p 90) → False)
    (d986 : (p 2) → (p 6) → (p 9) → False)
    (d170 : (¬ p 1) → (¬ p 2) → (¬ p 18) → False)
    (d1006 : (p 11) → (p 1) → (p 9) → False)
    (d703 : (p 3) → (p 9) → (p 5) → False)
    (d505 : (¬ p 2) → (¬ p 3) → (¬ p 34) → False)
    (d669 : (¬ p 18) → (p 37) → (¬ p 2) → (¬ p 20) → (p 6) → False)
    (d395 : (p 1) → (p 4) → (p 20) → False)
    (d549 : (¬ p 3) → (¬ p 4) → (¬ p 49) → False)
    (d988 : (p 15) → (p 5) → (p 9) → False)
    (d1005 : (p 16) → (p 6) → (p 9) → False)
    (d153 : (¬ p 15) → (¬ p 16) → (¬ p 151) → False)
    (d547 : (p 136) → (p 137) → (p 151) → False)
    (d1012 : (p 42) → (¬ p 136) → (p 49) → (p 34) → (p 5) → (¬ p 69) → (¬ p 11) → (p 37) → (¬ p 18) → False)
    (d998 : (p 78) → (p 5) → (p 137) → (¬ p 69) → (p 20) → (p 6) → (p 9) → (¬ p 18) → False)
    (d462 : (p 34) → (p 35) → (p 49) → False)
    (d941 : (p 52) → (p 49) → (¬ p 35) → (p 34) → False)
    (d503 : (p 5) → (p 9) → (p 79) → False)
    (d477 : (p 1) → (p 6) → (p 22) → False)
    (d585 : (p 96) → (p 97) → (p 151) → False)
    (d1011 : (¬ p 42) → (¬ p 53) → (¬ p 96) → (p 97) → (¬ p 136) → (¬ p 78) → (p 34) → (p 5) → (p 137) → (¬ p 69) → (¬ p 22) → (p 20) → (p 1) → (p 37) → (p 9) → (¬ p 40) → False)
    (d351 : (p 34) → (p 39) → (p 53) → False)
    (d628 : (p 53) → (p 34) → (p 56) → (¬ p 42) → False)
    (d58 : (¬ p 36) → (¬ p 39) → (¬ p 78) → False)
    (d518 : (¬ p 39) → (¬ p 42) → (¬ p 111) → False)
    (d366 : (¬ p 52) → (¬ p 56) → (¬ p 102) → False)
    (d506 : (¬ p 56) → (¬ p 60) → (¬ p 136) → False)
    (d76 : (p 34) → (p 36) → (p 50) → False)
    (d228 : (p 111) → (p 116) → (p 137) → False)
    (d592 : (p 102) → (p 107) → (p 137) → False)
    (d693 : (p 53) → (p 51) → (¬ p 96) → (p 60) → False)
    (d90 : (p 53) → (p 60) → (p 115) → False)
    (d235 : (¬ p 50) → (¬ p 54) → (¬ p 79) → False)
    (d83 : (¬ p 99) → (¬ p 107) → (¬ p 116) → False)
    (d203 : (¬ p 89) → (¬ p 96) → (¬ p 115) → False)
    (d272 : (p 49) → (p 54) → (p 67) → False)
    (d993 : (p 59) → (p 54) → (p 49) → False)
    (d95 : (p 88) → (p 89) → (p 99) → False)
    (d1014 : (¬ p 38) → (¬ p 59) → (p 89) → (p 99) → (¬ p 51) → (p 60) → (¬ p 78) → (¬ p 35) → (p 49) → (p 37) → (¬ p 18) → False)
    (d931 : (p 38) → (p 105) → (p 102) → False)
    (d12 : (¬ p 88) → (¬ p 95) → (¬ p 105) → False)
    (d369 : (p 89) → (p 95) → (p 114) → False)
    (d125 : (¬ p 78) → (¬ p 84) → (¬ p 114) → False)
    (d326 : (p 5) → (p 14) → (p 84) → False)
    (d27 : (¬ p 14) → (¬ p 15) → (¬ p 148) → False)
    (d485 : (p 84) → (p 85) → (p 148) → False)
    (d239 : (¬ p 79) → (¬ p 85) → (¬ p 123) → False)
    (d595 : (p 122) → (p 123) → (p 148) → False)
    (d323 : (¬ p 67) → (¬ p 72) → (¬ p 122) → False)
    (d706 : (p 68) → (p 72) → (p 49) → False)
    (d161 : (p 63) → (p 72) → (p 84) → False)
    (d1013 : (¬ p 68) → (¬ p 63) → (¬ p 59) → (p 89) → (p 99) → (¬ p 51) → (p 60) → (¬ p 78) → (p 49) → False)
    : (p 97) → (p 5) → (p 137) → (¬ p 69) → (p 6) → (p 9) → (¬ p 40) → (¬ p 18) → False := by
  intro a0 a1 a2 a3 a4 a5 a6 a7
  have v0 : ¬ p 90 := (fun u => d536 a4 a5 u)
  have v1 : p 37 := Classical.byContradiction (fun u => d10 u a6 v0)
  have v2 : ¬ p 2 := (fun u => d986 u a4 a5)
  have v3 : p 1 := Classical.byContradiction (fun u => d170 u v2 a7)
  have v4 : ¬ p 11 := (fun u => d1006 u v3 a5)
  have v5 : ¬ p 3 := (fun u => d703 u a5 a1)
  have v6 : p 34 := Classical.byContradiction (fun u => d505 v2 v5 u)
  have v7 : p 20 := Classical.byContradiction (fun u => d669 a7 v1 v2 u a4)
  have v8 : ¬ p 4 := (fun u => d395 v3 u v7)
  have v9 : p 49 := Classical.byContradiction (fun u => d549 v5 v8 u)
  have v10 : ¬ p 15 := (fun u => d988 u a1 a5)
  have v11 : ¬ p 16 := (fun u => d1005 u a4 a5)
  have v12 : p 151 := Classical.byContradiction (fun u => d153 v10 v11 u)
  have v13 : ¬ p 136 := (fun u => d547 u a2 v12)
  have v14 : ¬ p 42 := (fun u => d1012 u v13 v9 v6 a1 a3 v4 v1 a7)
  have v15 : ¬ p 78 := (fun u => d998 u a1 a2 a3 v7 a4 a5 a7)
  have v16 : ¬ p 35 := (fun u => d462 v6 u v9)
  have v17 : ¬ p 52 := (fun u => d941 u v9 v16 v6)
  have v18 : ¬ p 79 := (fun u => d503 a1 a5 u)
  have v19 : ¬ p 22 := (fun u => d477 v3 a4 u)
  have v20 : ¬ p 96 := (fun u => d585 u a0 v12)
  have v21 : p 53 := Classical.byContradiction (fun u => d1011 v14 u v20 a0 v13 v15 v6 a1 a2 a3 v19 v7 v3 v1 a5 a6)
  have v22 : ¬ p 39 := (fun u => d351 v6 u v21)
  have v23 : ¬ p 56 := (fun u => d628 v21 v6 u v14)
  have v24 : p 36 := Classical.byContradiction (fun u => d58 u v22 v15)
  have v25 : p 111 := Classical.byContradiction (fun u => d518 v22 v14 u)
  have v26 : p 102 := Classical.byContradiction (fun u => d366 v17 v23 u)
  have v27 : p 60 := Classical.byContradiction (fun u => d506 v23 u v13)
  have v28 : ¬ p 50 := (fun u => d76 v6 v24 u)
  have v29 : ¬ p 116 := (fun u => d228 v25 u a2)
  have v30 : ¬ p 107 := (fun u => d592 v26 u a2)
  have v31 : ¬ p 51 := (fun u => d693 v21 u v20 v27)
  have v32 : ¬ p 115 := (fun u => d90 v21 v27 u)
  have v33 : p 54 := Classical.byContradiction (fun u => d235 v28 u v18)
  have v34 : p 99 := Classical.byContradiction (fun u => d83 u v30 v29)
  have v35 : p 89 := Classical.byContradiction (fun u => d203 u v20 v32)
  have v36 : ¬ p 67 := (fun u => d272 v9 v33 u)
  have v37 : ¬ p 59 := (fun u => d993 u v33 v9)
  have v38 : ¬ p 88 := (fun u => d95 u v35 v34)
  have v39 : p 38 := Classical.byContradiction (fun u => d1014 u v37 v35 v34 v31 v27 v15 v16 v9 v1 a7)
  have v40 : ¬ p 105 := (fun u => d931 v39 u v26)
  have v41 : p 95 := Classical.byContradiction (fun u => d12 v38 u v40)
  have v42 : ¬ p 114 := (fun u => d369 v35 v41 u)
  have v43 : p 84 := Classical.byContradiction (fun u => d125 v15 u v42)
  have v44 : ¬ p 14 := (fun u => d326 a1 u v43)
  have v45 : p 148 := Classical.byContradiction (fun u => d27 v44 v10 u)
  have v46 : ¬ p 85 := (fun u => d485 v43 u v45)
  have v47 : p 123 := Classical.byContradiction (fun u => d239 v18 v46 u)
  have v48 : ¬ p 122 := (fun u => d595 u v47 v45)
  have v49 : p 72 := Classical.byContradiction (fun u => d323 v36 u v48)
  have v50 : ¬ p 68 := (fun u => d706 u v49 v9)
  have v51 : ¬ p 63 := (fun u => d161 u v49 v43)
  exact d1013 v50 v51 v37 v35 v34 v31 v27 v15 v9

theorem c1016 (p : Nat → Prop)
    (d351 : (p 34) → (p 39) → (p 53) → False)
    (d58 : (¬ p 36) → (¬ p 39) → (¬ p 78) → False)
    (d518 : (¬ p 39) → (¬ p 42) → (¬ p 111) → False)
    (d76 : (p 34) → (p 36) → (p 50) → False)
    (d332 : (p 24) → (p 27) → (p 111) → False)
    (d235 : (¬ p 50) → (¬ p 54) → (¬ p 79) → False)
    (d400 : (¬ p 22) → (¬ p 24) → (¬ p 89) → False)
    (d633 : (¬ p 24) → (p 91) → (¬ p 22) → (¬ p 26) → False)
    (d750 : (p 68) → (p 54) → (¬ p 79) → (¬ p 24) → (¬ p 78) → (p 5) → (p 20) → (p 49) → (¬ p 15) → False)
    (d356 : (p 51) → (p 53) → (p 89) → False)
    (d444 : (¬ p 51) → (¬ p 55) → (¬ p 91) → False)
    (d778 : (p 60) → (p 49) → (p 55) → (¬ p 68) → False)
    : (p 53) → (p 60) → (¬ p 26) → (p 27) → (¬ p 42) → (¬ p 78) → (¬ p 15) → (p 49) → (p 34) → (¬ p 79) → (p 5) → (¬ p 22) → (p 20) → False := by
  intro a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12
  have v0 : ¬ p 39 := (fun u => d351 a8 u a0)
  have v1 : p 36 := Classical.byContradiction (fun u => d58 u v0 a5)
  have v2 : p 111 := Classical.byContradiction (fun u => d518 v0 a4 u)
  have v3 : ¬ p 50 := (fun u => d76 a8 v1 u)
  have v4 : ¬ p 24 := (fun u => d332 u a3 v2)
  have v5 : p 54 := Classical.byContradiction (fun u => d235 v3 u a9)
  have v6 : p 89 := Classical.byContradiction (fun u => d400 a11 v4 u)
  have v7 : ¬ p 91 := (fun u => d633 v4 u a11 a2)
  have v8 : ¬ p 68 := (fun u => d750 u v5 a9 v4 a5 a10 a12 a7 a6)
  have v9 : ¬ p 51 := (fun u => d356 u a0 v6)
  have v10 : p 55 := Classical.byContradiction (fun u => d444 v9 u v7)
  exact d778 a1 a7 v10 v8

theorem c1017 (p : Nat → Prop)
    (d782 : (p 26) → (p 27) → (p 1) → (¬ p 11) → False)
    (d778 : (p 60) → (p 49) → (p 55) → (¬ p 68) → False)
    (d138 : (¬ p 68) → (¬ p 73) → (¬ p 130) → False)
    (d444 : (¬ p 51) → (¬ p 55) → (¬ p 91) → False)
    (d439 : (p 91) → (p 96) → (p 130) → False)
    (d633 : (¬ p 24) → (p 91) → (¬ p 22) → (¬ p 26) → False)
    (d1008 : (p 133) → (¬ p 42) → (¬ p 53) → (¬ p 96) → (¬ p 136) → (¬ p 78) → (p 34) → (¬ p 79) → (p 37) → False)
    (d332 : (p 24) → (p 27) → (p 111) → False)
    (d166 : (¬ p 11) → (¬ p 12) → (¬ p 133) → False)
    (d518 : (¬ p 39) → (¬ p 42) → (¬ p 111) → False)
    (d191 : (p 1) → (p 12) → (p 28) → False)
    (d357 : (p 37) → (p 39) → (p 89) → False)
    (d492 : (¬ p 26) → (¬ p 28) → (¬ p 127) → False)
    (d203 : (¬ p 89) → (¬ p 96) → (¬ p 115) → False)
    (d282 : (p 127) → (p 130) → (p 141) → False)
    (d696 : (p 39) → (p 34) → (¬ p 141) → (p 115) → (¬ p 53) → False)
    : (¬ p 68) → (¬ p 51) → (¬ p 53) → (¬ p 73) → (p 60) → (p 27) → (¬ p 42) → (¬ p 136) → (¬ p 78) → (p 49) → (p 34) → (¬ p 79) → (¬ p 11) → (¬ p 22) → (p 1) → (p 37) → False := by
  intro a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15
  have v0 : ¬ p 26 := (fun u => d782 u a5 a14 a12)
  have v1 : ¬ p 55 := (fun u => d778 a4 a9 u a0)
  have v2 : p 130 := Classical.byContradiction (fun u => d138 a0 a3 u)
  have v3 : p 91 := Classical.byContradiction (fun u => d444 a1 v1 u)
  have v4 : ¬ p 96 := (fun u => d439 v3 u v2)
  have v5 : p 24 := Classical.byContradiction (fun u => d633 u v3 a13 v0)
  have v6 : ¬ p 133 := (fun u => d1008 u a6 a2 v4 a7 a8 a10 a11 a15)
  have v7 : ¬ p 111 := (fun u => d332 v5 a5 u)
  have v8 : p 12 := Classical.byContradiction (fun u => d166 a12 u v6)
  have v9 : p 39 := Classical.byContradiction (fun u => d518 u a6 v7)
  have v10 : ¬ p 28 := (fun u => d191 a14 v8 u)
  have v11 : ¬ p 89 := (fun u => d357 a15 v9 u)
  have v12 : p 127 := Classical.byContradiction (fun u => d492 v0 v10 u)
  have v13 : p 115 := Classical.byContradiction (fun u => d203 v11 v4 u)
  have v14 : ¬ p 141 := (fun u => d282 v12 v2 u)
  exact d696 v9 a10 v14 v13 a2

theorem c1018 (p : Nat → Prop)
    (d477 : (p 1) → (p 6) → (p 22) → False)
    (d1017 : (¬ p 68) → (¬ p 51) → (¬ p 53) → (¬ p 73) → (p 60) → (p 27) → (¬ p 42) → (¬ p 136) → (¬ p 78) → (p 49) → (p 34) → (¬ p 79) → (¬ p 11) → (¬ p 22) → (p 1) → (p 37) → False)
    (d583 : (p 49) → (p 55) → (p 68) → False)
    (d632 : (p 64) → (p 68) → (p 49) → False)
    (d444 : (¬ p 51) → (¬ p 55) → (¬ p 91) → False)
    (d16 : (¬ p 64) → (¬ p 69) → (¬ p 92) → False)
    (d534 : (p 6) → (p 10) → (p 91) → False)
    (d566 : (p 91) → (p 92) → (p 126) → False)
    (d53 : (¬ p 10) → (¬ p 11) → (¬ p 126) → False)
    : (¬ p 51) → (¬ p 53) → (¬ p 73) → (p 60) → (p 27) → (¬ p 42) → (¬ p 136) → (¬ p 78) → (p 49) → (p 34) → (¬ p 79) → (¬ p 69) → (¬ p 11) → (p 1) → (p 37) → (p 6) → False := by
  intro a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15
  have v0 : ¬ p 22 := (fun u => d477 a13 a15 u)
  have v1 : p 68 := Classical.byContradiction (fun u => d1017 u a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a12 v0 a13 a14)
  have v2 : ¬ p 55 := (fun u => d583 a8 u v1)
  have v3 : ¬ p 64 := (fun u => d632 u v1 a8)
  have v4 : p 91 := Classical.byContradiction (fun u => d444 a0 v2 u)
  have v5 : p 92 := Classical.byContradiction (fun u => d16 v3 a11 u)
  have v6 : ¬ p 10 := (fun u => d534 a15 u v4)
  have v7 : ¬ p 126 := (fun u => d566 v4 v5 u)
  exact d53 v6 a12 v7

theorem c1019 (p : Nat → Prop)
    (d1006 : (p 11) → (p 1) → (p 9) → False)
    (d782 : (p 26) → (p 27) → (p 1) → (¬ p 11) → False)
    (d988 : (p 15) → (p 5) → (p 9) → False)
    (d1005 : (p 16) → (p 6) → (p 9) → False)
    (d153 : (¬ p 15) → (¬ p 16) → (¬ p 151) → False)
    (d395 : (p 1) → (p 4) → (p 20) → False)
    (d703 : (p 3) → (p 9) → (p 5) → False)
    (d549 : (¬ p 3) → (¬ p 4) → (¬ p 49) → False)
    (d986 : (p 2) → (p 6) → (p 9) → False)
    (d505 : (¬ p 2) → (¬ p 3) → (¬ p 34) → False)
    (d503 : (p 5) → (p 9) → (p 79) → False)
    (d477 : (p 1) → (p 6) → (p 22) → False)
    (d536 : (p 6) → (p 9) → (p 90) → False)
    (d10 : (¬ p 37) → (¬ p 40) → (¬ p 90) → False)
    (d506 : (¬ p 56) → (¬ p 60) → (¬ p 136) → False)
    (d753 : (p 73) → (p 49) → (p 151) → (¬ p 56) → False)
    (d1016 : (p 53) → (p 60) → (¬ p 26) → (p 27) → (¬ p 42) → (¬ p 78) → (¬ p 15) → (p 49) → (p 34) → (¬ p 79) → (p 5) → (¬ p 22) → (p 20) → False)
    (d1018 : (¬ p 51) → (¬ p 53) → (¬ p 73) → (p 60) → (p 27) → (¬ p 42) → (¬ p 136) → (¬ p 78) → (p 49) → (p 34) → (¬ p 79) → (¬ p 69) → (¬ p 11) → (p 1) → (p 37) → (p 6) → False)
    (d531 : (p 51) → (p 60) → (p 96) → False)
    (d1008 : (p 133) → (¬ p 42) → (¬ p 53) → (¬ p 96) → (¬ p 136) → (¬ p 78) → (p 34) → (¬ p 79) → (p 37) → False)
    (d166 : (¬ p 11) → (¬ p 12) → (¬ p 133) → False)
    (d2 : (p 5) → (p 12) → (p 82) → False)
    (d301 : (p 9) → (p 12) → (p 120) → False)
    (d173 : (¬ p 40) → (¬ p 43) → (¬ p 120) → False)
    (d52 : (p 34) → (p 43) → (p 57) → False)
    (d538 : (¬ p 53) → (¬ p 57) → (¬ p 112) → False)
    (d167 : (p 39) → (p 43) → (p 112) → False)
    (d58 : (¬ p 36) → (¬ p 39) → (¬ p 78) → False)
    (d518 : (¬ p 39) → (¬ p 42) → (¬ p 111) → False)
    (d537 : (p 36) → (p 37) → (p 76) → False)
    (d332 : (p 24) → (p 27) → (p 111) → False)
    (d35 : (¬ p 76) → (¬ p 82) → (¬ p 93) → False)
    (d400 : (¬ p 22) → (¬ p 24) → (¬ p 89) → False)
    (d497 : (p 89) → (p 93) → (p 112) → False)
    : (¬ p 56) → (p 27) → (¬ p 42) → (¬ p 136) → (¬ p 78) → (p 5) → (¬ p 69) → (p 20) → (p 1) → (p 6) → (p 9) → (¬ p 40) → False := by
  intro a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11
  have v0 : ¬ p 11 := (fun u => d1006 u a8 a10)
  have v1 : ¬ p 26 := (fun u => d782 u a1 a8 v0)
  have v2 : ¬ p 15 := (fun u => d988 u a5 a10)
  have v3 : ¬ p 16 := (fun u => d1005 u a9 a10)
  have v4 : p 151 := Classical.byContradiction (fun u => d153 v2 v3 u)
  have v5 : ¬ p 4 := (fun u => d395 a8 u a7)
  have v6 : ¬ p 3 := (fun u => d703 u a10 a5)
  have v7 : p 49 := Classical.byContradiction (fun u => d549 v6 v5 u)
  have v8 : ¬ p 2 := (fun u => d986 u a9 a10)
  have v9 : p 34 := Classical.byContradiction (fun u => d505 v8 v6 u)
  have v10 : ¬ p 79 := (fun u => d503 a5 a10 u)
  have v11 : ¬ p 22 := (fun u => d477 a8 a9 u)
  have v12 : ¬ p 90 := (fun u => d536 a9 a10 u)
  have v13 : p 37 := Classical.byContradiction (fun u => d10 u a11 v12)
  have v14 : p 60 := Classical.byContradiction (fun u => d506 a0 u a3)
  have v15 : ¬ p 73 := (fun u => d753 u v7 v4 a0)
  have v16 : ¬ p 53 := (fun u => d1016 u v14 v1 a1 a2 a4 v2 v7 v9 v10 a5 v11 a7)
  have v17 : p 51 := Classical.byContradiction (fun u => d1018 u v16 v15 v14 a1 a2 a3 a4 v7 v9 v10 a6 v0 a8 v13 a9)
  have v18 : ¬ p 96 := (fun u => d531 v17 v14 u)
  have v19 : ¬ p 133 := (fun u => d1008 u a2 v16 v18 a3 a4 v9 v10 v13)
  have v20 : p 12 := Classical.byContradiction (fun u => d166 v0 u v19)
  have v21 : ¬ p 82 := (fun u => d2 a5 v20 u)
  have v22 : ¬ p 120 := (fun u => d301 a10 v20 u)
  have v23 : p 43 := Classical.byContradiction (fun u => d173 a11 u v22)
  have v24 : ¬ p 57 := (fun u => d52 v9 v23 u)
  have v25 : p 112 := Classical.byContradiction (fun u => d538 v16 v24 u)
  have v26 : ¬ p 39 := (fun u => d167 u v23 v25)
  have v27 : p 36 := Classical.byContradiction (fun u => d58 u v26 a4)
  have v28 : p 111 := Classical.byContradiction (fun u => d518 v26 a2 u)
  have v29 : ¬ p 76 := (fun u => d537 v27 v13 u)
  have v30 : ¬ p 24 := (fun u => d332 u a1 v28)
  have v31 : p 93 := Classical.byContradiction (fun u => d35 v29 v21 u)
  have v32 : p 89 := Classical.byContradiction (fun u => d400 v11 v30 u)
  exact d497 v32 v31 v25

theorem c1020 (p : Nat → Prop)
    (d105 : (p 49) → (p 51) → (p 64) → False)
    (d940 : (p 56) → (p 49) → (¬ p 64) → (p 51) → False)
    : (p 51) → (p 56) → (p 49) → False := by
  intro a0 a1 a2
  have v0 : ¬ p 64 := (fun u => d105 a2 a0 u)
  exact d940 a1 a2 v0 a0

theorem c1021 (p : Nat → Prop)
    (d246 : (p 49) → (p 60) → (p 73) → False)
    (d1018 : (¬ p 51) → (¬ p 53) → (¬ p 73) → (p 60) → (p 27) → (¬ p 42) → (¬ p 136) → (¬ p 78) → (p 49) → (p 34) → (¬ p 79) → (¬ p 69) → (¬ p 11) → (p 1) → (p 37) → (p 6) → False)
    : (p 60) → (¬ p 51) → (¬ p 53) → (p 27) → (¬ p 42) → (¬ p 136) → (¬ p 78) → (p 49) → (p 34) → (¬ p 79) → (¬ p 69) → (¬ p 11) → (p 1) → (p 37) → (p 6) → False := by
  intro a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14
  have v0 : ¬ p 73 := (fun u => d246 a7 a0 u)
  exact d1018 a1 a2 v0 a0 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14

theorem c1022 (p : Nat → Prop)
    (d357 : (p 37) → (p 39) → (p 89) → False)
    (d58 : (¬ p 36) → (¬ p 39) → (¬ p 78) → False)
    (d518 : (¬ p 39) → (¬ p 42) → (¬ p 111) → False)
    (d76 : (p 34) → (p 36) → (p 50) → False)
    (d537 : (p 36) → (p 37) → (p 76) → False)
    (d235 : (¬ p 50) → (¬ p 54) → (¬ p 79) → False)
    (d944 : (p 54) → (p 57) → (p 34) → False)
    (d538 : (¬ p 53) → (¬ p 57) → (¬ p 112) → False)
    (d422 : (p 111) → (p 112) → (p 133) → False)
    (d497 : (p 89) → (p 93) → (p 112) → False)
    (d166 : (¬ p 11) → (¬ p 12) → (¬ p 133) → False)
    (d35 : (¬ p 76) → (¬ p 82) → (¬ p 93) → False)
    (d2 : (p 5) → (p 12) → (p 82) → False)
    : (p 89) → (¬ p 53) → (¬ p 42) → (¬ p 78) → (p 34) → (¬ p 79) → (p 5) → (¬ p 11) → (p 37) → False := by
  intro a0 a1 a2 a3 a4 a5 a6 a7 a8
  have v0 : ¬ p 39 := (fun u => d357 a8 u a0)
  have v1 : p 36 := Classical.byContradiction (fun u => d58 u v0 a3)
  have v2 : p 111 := Classical.byContradiction (fun u => d518 v0 a2 u)
  have v3 : ¬ p 50 := (fun u => d76 a4 v1 u)
  have v4 : ¬ p 76 := (fun u => d537 v1 a8 u)
  have v5 : p 54 := Classical.byContradiction (fun u => d235 v3 u a5)
  have v6 : ¬ p 57 := (fun u => d944 v5 u a4)
  have v7 : p 112 := Classical.byContradiction (fun u => d538 a1 v6 u)
  have v8 : ¬ p 133 := (fun u => d422 v2 v7 u)
  have v9 : ¬ p 93 := (fun u => d497 a0 u v7)
  have v10 : p 12 := Classical.byContradiction (fun u => d166 a7 u v8)
  have v11 : p 82 := Classical.byContradiction (fun u => d35 v4 u v9)
  exact d2 a6 v10 v11

theorem c1023 (p : Nat → Prop)
    (d52 : (p 34) → (p 43) → (p 57) → False)
    (d167 : (p 39) → (p 43) → (p 112) → False)
    (d538 : (¬ p 53) → (¬ p 57) → (¬ p 112) → False)
    : (p 43) → (p 39) → (¬ p 53) → (p 34) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 57 := (fun u => d52 a3 a0 u)
  have v1 : ¬ p 112 := (fun u => d167 a1 a0 u)
  exact d538 a2 v0 v1

theorem c1024 (p : Nat → Prop)
    (d986 : (p 2) → (p 6) → (p 9) → False)
    (d170 : (¬ p 1) → (¬ p 2) → (¬ p 18) → False)
    (d1006 : (p 11) → (p 1) → (p 9) → False)
    (d1005 : (p 16) → (p 6) → (p 9) → False)
    (d536 : (p 6) → (p 9) → (p 90) → False)
    (d10 : (¬ p 37) → (¬ p 40) → (¬ p 90) → False)
    (d669 : (¬ p 18) → (p 37) → (¬ p 2) → (¬ p 20) → (p 6) → False)
    (d395 : (p 1) → (p 4) → (p 20) → False)
    (d258 : (p 1) → (p 9) → (p 25) → False)
    (d477 : (p 1) → (p 6) → (p 22) → False)
    (d503 : (p 5) → (p 9) → (p 79) → False)
    (d703 : (p 3) → (p 9) → (p 5) → False)
    (d505 : (¬ p 2) → (¬ p 3) → (¬ p 34) → False)
    (d549 : (¬ p 3) → (¬ p 4) → (¬ p 49) → False)
    (d988 : (p 15) → (p 5) → (p 9) → False)
    (d998 : (p 78) → (p 5) → (p 137) → (¬ p 69) → (p 20) → (p 6) → (p 9) → (¬ p 18) → False)
    (d153 : (¬ p 15) → (¬ p 16) → (¬ p 151) → False)
    (d547 : (p 136) → (p 137) → (p 151) → False)
    (d1012 : (p 42) → (¬ p 136) → (p 49) → (p 34) → (p 5) → (¬ p 69) → (¬ p 11) → (p 37) → (¬ p 18) → False)
    (d1015 : (p 97) → (p 5) → (p 137) → (¬ p 69) → (p 6) → (p 9) → (¬ p 40) → (¬ p 18) → False)
    (d43 : (¬ p 90) → (¬ p 97) → (¬ p 124) → False)
    (d116 : (p 119) → (p 124) → (p 137) → False)
    (d49 : (¬ p 25) → (¬ p 27) → (¬ p 119) → False)
    (d1019 : (¬ p 56) → (p 27) → (¬ p 42) → (¬ p 136) → (¬ p 78) → (p 5) → (¬ p 69) → (p 20) → (p 1) → (p 6) → (p 9) → (¬ p 40) → False)
    (d628 : (p 53) → (p 34) → (p 56) → (¬ p 42) → False)
    (d456 : (p 56) → (p 61) → (p 137) → False)
    (d1022 : (p 89) → (¬ p 53) → (¬ p 42) → (¬ p 78) → (p 34) → (¬ p 79) → (p 5) → (¬ p 11) → (p 37) → False)
    (d400 : (¬ p 22) → (¬ p 24) → (¬ p 89) → False)
    (d332 : (p 24) → (p 27) → (p 111) → False)
    (d518 : (¬ p 39) → (¬ p 42) → (¬ p 111) → False)
    (d1023 : (p 43) → (p 39) → (¬ p 53) → (p 34) → False)
    (d173 : (¬ p 40) → (¬ p 43) → (¬ p 120) → False)
    (d301 : (p 9) → (p 12) → (p 120) → False)
    (d166 : (¬ p 11) → (¬ p 12) → (¬ p 133) → False)
    (d533 : (p 56) → (p 57) → (p 133) → False)
    (d538 : (¬ p 53) → (¬ p 57) → (¬ p 112) → False)
    (d141 : (¬ p 57) → (¬ p 61) → (¬ p 142) → False)
    (d1004 : (p 151) → (p 39) → (p 142) → (p 112) → (¬ p 42) → (¬ p 53) → (¬ p 89) → (p 24) → (p 34) → (p 137) → (¬ p 25) → (p 37) → (¬ p 90) → False)
    : (p 5) → (p 137) → (¬ p 69) → (p 6) → (p 9) → (¬ p 40) → (¬ p 18) → False := by
  intro a0 a1 a2 a3 a4 a5 a6
  have v0 : ¬ p 2 := (fun u => d986 u a3 a4)
  have v1 : p 1 := Classical.byContradiction (fun u => d170 u v0 a6)
  have v2 : ¬ p 11 := (fun u => d1006 u v1 a4)
  have v3 : ¬ p 16 := (fun u => d1005 u a3 a4)
  have v4 : ¬ p 90 := (fun u => d536 a3 a4 u)
  have v5 : p 37 := Classical.byContradiction (fun u => d10 u a5 v4)
  have v6 : p 20 := Classical.byContradiction (fun u => d669 a6 v5 v0 u a3)
  have v7 : ¬ p 4 := (fun u => d395 v1 u v6)
  have v8 : ¬ p 25 := (fun u => d258 v1 a4 u)
  have v9 : ¬ p 22 := (fun u => d477 v1 a3 u)
  have v10 : ¬ p 79 := (fun u => d503 a0 a4 u)
  have v11 : ¬ p 3 := (fun u => d703 u a4 a0)
  have v12 : p 34 := Classical.byContradiction (fun u => d505 v0 v11 u)
  have v13 : p 49 := Classical.byContradiction (fun u => d549 v11 v7 u)
  have v14 : ¬ p 15 := (fun u => d988 u a0 a4)
  have v15 : ¬ p 78 := (fun u => d998 u a0 a1 a2 v6 a3 a4 a6)
  have v16 : p 151 := Classical.byContradiction (fun u => d153 v14 v3 u)
  have v17 : ¬ p 136 := (fun u => d547 u a1 v16)
  have v18 : ¬ p 42 := (fun u => d1012 u v17 v13 v12 a0 a2 v2 v5 a6)
  have v19 : ¬ p 97 := (fun u => d1015 u a0 a1 a2 a3 a4 a5 a6)
  have v20 : p 124 := Classical.byContradiction (fun u => d43 v4 v19 u)
  have v21 : ¬ p 119 := (fun u => d116 u v20 a1)
  have v22 : p 27 := Classical.byContradiction (fun u => d49 v8 u v21)
  have v23 : p 56 := Classical.byContradiction (fun u => d1019 u v22 v18 v17 v15 a0 a2 v6 v1 a3 a4 a5)
  have v24 : ¬ p 53 := (fun u => d628 u v12 v23 v18)
  have v25 : ¬ p 61 := (fun u => d456 v23 u a1)
  have v26 : ¬ p 89 := (fun u => d1022 u v24 v18 v15 v12 v10 a0 v2 v5)
  have v27 : p 24 := Classical.byContradiction (fun u => d400 v9 u v26)
  have v28 : ¬ p 111 := (fun u => d332 v27 v22 u)
  have v29 : p 39 := Classical.byContradiction (fun u => d518 u v18 v28)
  have v30 : ¬ p 43 := (fun u => d1023 u v29 v24 v12)
  have v31 : p 120 := Classical.byContradiction (fun u => d173 a5 v30 u)
  have v32 : ¬ p 12 := (fun u => d301 a4 u v31)
  have v33 : p 133 := Classical.byContradiction (fun u => d166 v2 v32 u)
  have v34 : ¬ p 57 := (fun u => d533 v23 u v33)
  have v35 : p 112 := Classical.byContradiction (fun u => d538 v24 v34 u)
  have v36 : p 142 := Classical.byContradiction (fun u => d141 v34 v25 u)
  exact d1004 v16 v29 v36 v35 v18 v24 v26 v27 v12 a1 v8 v5 v4

theorem c1025 (p : Nat → Prop)
    (d502 : (p 34) → (p 42) → (p 56) → False)
    (d456 : (p 56) → (p 61) → (p 137) → False)
    (d1006 : (p 11) → (p 1) → (p 9) → False)
    (d258 : (p 1) → (p 9) → (p 25) → False)
    (d10 : (¬ p 37) → (¬ p 40) → (¬ p 90) → False)
    (d357 : (p 37) → (p 39) → (p 89) → False)
    (d1023 : (p 43) → (p 39) → (¬ p 53) → (p 34) → False)
    (d400 : (¬ p 22) → (¬ p 24) → (¬ p 89) → False)
    (d173 : (¬ p 40) → (¬ p 43) → (¬ p 120) → False)
    (d489 : (p 20) → (p 24) → (p 66) → False)
    (d731 : (p 29) → (p 24) → (p 20) → (¬ p 66) → False)
    (d301 : (p 9) → (p 12) → (p 120) → False)
    (d166 : (¬ p 11) → (¬ p 12) → (¬ p 133) → False)
    (d533 : (p 56) → (p 57) → (p 133) → False)
    (d538 : (¬ p 53) → (¬ p 57) → (¬ p 112) → False)
    (d141 : (¬ p 57) → (¬ p 61) → (¬ p 142) → False)
    (d1004 : (p 151) → (p 39) → (p 142) → (p 112) → (¬ p 42) → (¬ p 53) → (¬ p 89) → (p 24) → (p 34) → (p 137) → (¬ p 25) → (p 37) → (¬ p 90) → False)
    (d153 : (¬ p 15) → (¬ p 16) → (¬ p 151) → False)
    (d451 : (p 1) → (p 15) → (p 31) → False)
    (d134 : (¬ p 29) → (¬ p 31) → (¬ p 145) → False)
    (d24 : (p 13) → (p 15) → (p 145) → False)
    (d92 : (¬ p 12) → (¬ p 13) → (¬ p 139) → False)
    (d29 : (p 139) → (p 141) → (p 145) → False)
    (d696 : (p 39) → (p 34) → (¬ p 141) → (p 115) → (¬ p 53) → False)
    (d521 : (¬ p 43) → (¬ p 46) → (¬ p 141) → False)
    (d203 : (¬ p 89) → (¬ p 96) → (¬ p 115) → False)
    (d240 : (p 37) → (p 46) → (p 96) → False)
    : (p 39) → (p 34) → (¬ p 53) → (p 56) → (p 137) → (¬ p 16) → (¬ p 22) → (p 20) → (p 1) → (¬ p 90) → (p 9) → (¬ p 40) → False := by
  intro a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11
  have v0 : ¬ p 42 := (fun u => d502 a1 u a3)
  have v1 : ¬ p 61 := (fun u => d456 a3 u a4)
  have v2 : ¬ p 11 := (fun u => d1006 u a8 a10)
  have v3 : ¬ p 25 := (fun u => d258 a8 a10 u)
  have v4 : p 37 := Classical.byContradiction (fun u => d10 u a11 a9)
  have v5 : ¬ p 89 := (fun u => d357 v4 a0 u)
  have v6 : ¬ p 43 := (fun u => d1023 u a0 a2 a1)
  have v7 : p 24 := Classical.byContradiction (fun u => d400 a6 u v5)
  have v8 : p 120 := Classical.byContradiction (fun u => d173 a11 v6 u)
  have v9 : ¬ p 66 := (fun u => d489 a7 v7 u)
  have v10 : ¬ p 29 := (fun u => d731 u v7 a7 v9)
  have v11 : ¬ p 12 := (fun u => d301 a10 u v8)
  have v12 : p 133 := Classical.byContradiction (fun u => d166 v2 v11 u)
  have v13 : ¬ p 57 := (fun u => d533 a3 u v12)
  have v14 : p 112 := Classical.byContradiction (fun u => d538 a2 v13 u)
  have v15 : p 142 := Classical.byContradiction (fun u => d141 v13 v1 u)
  have v16 : ¬ p 151 := (fun u => d1004 u a0 v15 v14 v0 a2 v5 v7 a1 a4 v3 v4 a9)
  have v17 : p 15 := Classical.byContradiction (fun u => d153 u a5 v16)
  have v18 : ¬ p 31 := (fun u => d451 a8 v17 u)
  have v19 : p 145 := Classical.byContradiction (fun u => d134 v10 v18 u)
  have v20 : ¬ p 13 := (fun u => d24 u v17 v19)
  have v21 : p 139 := Classical.byContradiction (fun u => d92 v11 v20 u)
  have v22 : ¬ p 141 := (fun u => d29 v21 u v19)
  have v23 : ¬ p 115 := (fun u => d696 a0 a1 v22 u a2)
  have v24 : p 46 := Classical.byContradiction (fun u => d521 v6 u v22)
  have v25 : p 96 := Classical.byContradiction (fun u => d203 v5 u v23)
  exact d240 v4 v24 v25

theorem c1026 (p : Nat → Prop)
    (d537 : (p 36) → (p 37) → (p 76) → False)
    (d37 : (p 36) → (p 43) → (p 82) → False)
    (d35 : (¬ p 76) → (¬ p 82) → (¬ p 93) → False)
    : (p 36) → (¬ p 93) → (p 43) → (p 37) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 76 := (fun u => d537 a0 a3 u)
  have v1 : ¬ p 82 := (fun u => d37 a0 a2 u)
  exact d35 v0 v1 a1

end JSP000746.RUP
