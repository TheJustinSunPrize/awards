import Init.Classical

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace JSP000746.RUP

theorem c5039 (p : Nat → Prop)
    (d232 : (p 88) → (p 92) → (p 102) → False)
    (d16 : (¬ p 64) → (¬ p 69) → (¬ p 92) → False)
    : (¬ p 64) → (¬ p 69) → (p 102) → (p 88) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 92 := (fun u => d232 a3 u a2)
  exact d16 a0 a1 v0

theorem c5040 (p : Nat → Prop)
    (d30 : (p 22) → (p 27) → (p 92) → False)
    (d16 : (¬ p 64) → (¬ p 69) → (¬ p 92) → False)
    : (¬ p 64) → (¬ p 69) → (p 27) → (p 22) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 92 := (fun u => d30 a3 a2 u)
  exact d16 a0 a1 v0

theorem c5041 (p : Nat → Prop)
    (d566 : (p 91) → (p 92) → (p 126) → False)
    (d16 : (¬ p 64) → (¬ p 69) → (¬ p 92) → False)
    : (¬ p 64) → (¬ p 69) → (p 91) → (p 126) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 92 := (fun u => d566 a2 u a3)
  exact d16 a0 a1 v0

theorem c5042 (p : Nat → Prop)
    (d354 : (p 37) → (p 42) → (p 92) → False)
    (d16 : (¬ p 64) → (¬ p 69) → (¬ p 92) → False)
    : (¬ p 64) → (¬ p 69) → (p 37) → (p 42) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 92 := (fun u => d354 a2 a3 u)
  exact d16 a0 a1 v0

theorem c5043 (p : Nat → Prop)
    (d335 : (p 92) → (p 96) → (p 136) → False)
    (d16 : (¬ p 64) → (¬ p 69) → (¬ p 92) → False)
    : (¬ p 64) → (¬ p 69) → (p 96) → (p 136) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 92 := (fun u => d335 u a2 a3)
  exact d16 a0 a1 v0

theorem c5044 (p : Nat → Prop)
    (d429 : (p 51) → (p 56) → (p 92) → False)
    (d16 : (¬ p 64) → (¬ p 69) → (¬ p 92) → False)
    : (¬ p 64) → (¬ p 69) → (p 56) → (p 51) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 92 := (fun u => d429 a3 a2 u)
  exact d16 a0 a1 v0

theorem c5045 (p : Nat → Prop)
    (d241 : (p 90) → (p 92) → (p 119) → False)
    (d16 : (¬ p 64) → (¬ p 69) → (¬ p 92) → False)
    : (¬ p 64) → (¬ p 69) → (p 119) → (p 90) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 92 := (fun u => d241 a3 u a2)
  exact d16 a0 a1 v0

theorem c5046 (p : Nat → Prop)
    (d340 : (p 92) → (p 98) → (p 138) → False)
    (d16 : (¬ p 64) → (¬ p 69) → (¬ p 92) → False)
    : (¬ p 64) → (¬ p 69) → (p 98) → (p 138) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 92 := (fun u => d340 u a2 a3)
  exact d16 a0 a1 v0

theorem c5047 (p : Nat → Prop)
    (d510 : (p 91) → (p 95) → (p 129) → False)
    (d12 : (¬ p 88) → (¬ p 95) → (¬ p 105) → False)
    : (¬ p 105) → (¬ p 88) → (p 129) → (p 91) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 95 := (fun u => d510 a3 u a2)
  exact d12 a1 v0 a0

theorem c5048 (p : Nat → Prop)
    (d369 : (p 89) → (p 95) → (p 114) → False)
    (d12 : (¬ p 88) → (¬ p 95) → (¬ p 105) → False)
    : (¬ p 105) → (¬ p 88) → (p 114) → (p 89) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 95 := (fun u => d369 a3 u a2)
  exact d12 a1 v0 a0

theorem c5049 (p : Nat → Prop)
    (d569 : (p 90) → (p 95) → (p 122) → False)
    (d12 : (¬ p 88) → (¬ p 95) → (¬ p 105) → False)
    : (¬ p 105) → (¬ p 88) → (p 122) → (p 90) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 95 := (fun u => d569 a3 u a2)
  exact d12 a1 v0 a0

theorem c5050 (p : Nat → Prop)
    (d234 : (p 37) → (p 45) → (p 95) → False)
    (d12 : (¬ p 88) → (¬ p 95) → (¬ p 105) → False)
    : (¬ p 105) → (¬ p 88) → (p 45) → (p 37) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 95 := (fun u => d234 a3 a2 u)
  exact d12 a1 v0 a0

theorem c5051 (p : Nat → Prop)
    (d137 : (p 64) → (p 72) → (p 95) → False)
    (d12 : (¬ p 88) → (¬ p 95) → (¬ p 105) → False)
    : (¬ p 105) → (¬ p 88) → (p 64) → (p 72) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 95 := (fun u => d137 a2 a3 u)
  exact d12 a1 v0 a0

theorem c5052 (p : Nat → Prop)
    (d295 : (p 22) → (p 30) → (p 95) → False)
    (d12 : (¬ p 88) → (¬ p 95) → (¬ p 105) → False)
    : (¬ p 105) → (¬ p 88) → (p 30) → (p 22) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 95 := (fun u => d295 a3 a2 u)
  exact d12 a1 v0 a0

theorem c5053 (p : Nat → Prop)
    (d169 : (p 95) → (p 97) → (p 149) → False)
    (d12 : (¬ p 88) → (¬ p 95) → (¬ p 105) → False)
    : (¬ p 105) → (¬ p 88) → (p 97) → (p 149) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 95 := (fun u => d169 u a2 a3)
  exact d12 a1 v0 a0

theorem c5054 (p : Nat → Prop)
    (d527 : (p 95) → (p 98) → (p 150) → False)
    (d12 : (¬ p 88) → (¬ p 95) → (¬ p 105) → False)
    : (¬ p 105) → (¬ p 88) → (p 98) → (p 150) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 95 := (fun u => d527 u a2 a3)
  exact d12 a1 v0 a0

theorem c5055 (p : Nat → Prop)
    (d304 : (p 93) → (p 95) → (p 140) → False)
    (d12 : (¬ p 88) → (¬ p 95) → (¬ p 105) → False)
    : (¬ p 105) → (¬ p 88) → (p 140) → (p 93) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 95 := (fun u => d304 a3 u a2)
  exact d12 a1 v0 a0

theorem c5056 (p : Nat → Prop)
    (d197 : (p 53) → (p 58) → (p 113) → False)
    (d384 : (¬ p 66) → (¬ p 71) → (¬ p 113) → False)
    : (¬ p 71) → (¬ p 66) → (p 58) → (p 53) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 113 := (fun u => d197 a3 a2 u)
  exact d384 a1 a0 v0

theorem c5057 (p : Nat → Prop)
    (d292 : (p 24) → (p 29) → (p 113) → False)
    (d384 : (¬ p 66) → (¬ p 71) → (¬ p 113) → False)
    : (¬ p 71) → (¬ p 66) → (p 24) → (p 29) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 113 := (fun u => d292 a2 a3 u)
  exact d384 a1 a0 v0

theorem c5058 (p : Nat → Prop)
    (d157 : (p 99) → (p 104) → (p 113) → False)
    (d384 : (¬ p 66) → (¬ p 71) → (¬ p 113) → False)
    : (¬ p 71) → (¬ p 66) → (p 104) → (p 99) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 113 := (fun u => d157 a3 a2 u)
  exact d384 a1 a0 v0

theorem c5059 (p : Nat → Prop)
    (d172 : (p 39) → (p 44) → (p 113) → False)
    (d384 : (¬ p 66) → (¬ p 71) → (¬ p 113) → False)
    : (¬ p 71) → (¬ p 66) → (p 39) → (p 44) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 113 := (fun u => d172 a2 a3 u)
  exact d384 a1 a0 v0

theorem c5060 (p : Nat → Prop)
    (d371 : (p 113) → (p 116) → (p 146) → False)
    (d384 : (¬ p 66) → (¬ p 71) → (¬ p 113) → False)
    : (¬ p 71) → (¬ p 66) → (p 116) → (p 146) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 113 := (fun u => d371 u a2 a3)
  exact d384 a1 a0 v0

theorem c5061 (p : Nat → Prop)
    (d98 : (p 112) → (p 113) → (p 139) → False)
    (d384 : (¬ p 66) → (¬ p 71) → (¬ p 113) → False)
    : (¬ p 71) → (¬ p 66) → (p 112) → (p 139) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 113 := (fun u => d98 a2 u a3)
  exact d384 a1 a0 v0

theorem c5062 (p : Nat → Prop)
    (d4910 : (¬ p 104) → (¬ p 77) → (p 78) → (p 113) → False)
    (d384 : (¬ p 66) → (¬ p 71) → (¬ p 113) → False)
    : (¬ p 71) → (¬ p 66) → (¬ p 104) → (¬ p 77) → (p 78) → False := by
  intro a0 a1 a2 a3 a4
  have v0 : ¬ p 113 := (fun u => d4910 a2 a3 a4 u)
  exact d384 a1 a0 v0

theorem c5063 (p : Nat → Prop)
    (d4976 : (¬ p 39) → (¬ p 42) → (p 113) → (p 134) → False)
    (d384 : (¬ p 66) → (¬ p 71) → (¬ p 113) → False)
    : (¬ p 71) → (¬ p 66) → (¬ p 39) → (¬ p 42) → (p 134) → False := by
  intro a0 a1 a2 a3 a4
  have v0 : ¬ p 113 := (fun u => d4976 a2 a3 u a4)
  exact d384 a1 a0 v0

theorem c5064 (p : Nat → Prop)
    (d4987 : (¬ p 14) → (¬ p 13) → (p 114) → (p 113) → False)
    (d384 : (¬ p 66) → (¬ p 71) → (¬ p 113) → False)
    : (¬ p 71) → (¬ p 66) → (¬ p 14) → (¬ p 13) → (p 114) → False := by
  intro a0 a1 a2 a3 a4
  have v0 : ¬ p 113 := (fun u => d4987 a2 a3 a4 u)
  exact d384 a1 a0 v0

theorem c5065 (p : Nat → Prop)
    (d396 : (p 25) → (p 28) → (p 120) → False)
    (d173 : (¬ p 40) → (¬ p 43) → (¬ p 120) → False)
    : (¬ p 40) → (¬ p 43) → (p 25) → (p 28) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 120 := (fun u => d396 a2 a3 u)
  exact d173 a0 a1 v0

theorem c5066 (p : Nat → Prop)
    (d433 : (p 120) → (p 123) → (p 141) → False)
    (d173 : (¬ p 40) → (¬ p 43) → (¬ p 120) → False)
    : (¬ p 40) → (¬ p 43) → (p 141) → (p 123) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 120 := (fun u => d433 u a3 a2)
  exact d173 a0 a1 v0

theorem c5067 (p : Nat → Prop)
    (d171 : (p 120) → (p 125) → (p 143) → False)
    (d173 : (¬ p 40) → (¬ p 43) → (¬ p 120) → False)
    : (¬ p 40) → (¬ p 43) → (p 143) → (p 125) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 120 := (fun u => d171 u a3 a2)
  exact d173 a0 a1 v0

theorem c5068 (p : Nat → Prop)
    (d343 : (p 90) → (p 93) → (p 120) → False)
    (d173 : (¬ p 40) → (¬ p 43) → (¬ p 120) → False)
    : (¬ p 40) → (¬ p 43) → (p 93) → (p 90) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 120 := (fun u => d343 a3 a2 u)
  exact d173 a0 a1 v0

theorem c5069 (p : Nat → Prop)
    (d376 : (p 67) → (p 70) → (p 120) → False)
    (d173 : (¬ p 40) → (¬ p 43) → (¬ p 120) → False)
    : (¬ p 40) → (¬ p 43) → (p 67) → (p 70) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 120 := (fun u => d376 a2 a3 u)
  exact d173 a0 a1 v0

theorem c5070 (p : Nat → Prop)
    (d301 : (p 9) → (p 12) → (p 120) → False)
    (d173 : (¬ p 40) → (¬ p 43) → (¬ p 120) → False)
    : (¬ p 40) → (¬ p 43) → (p 12) → (p 9) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 120 := (fun u => d301 a3 a2 u)
  exact d173 a0 a1 v0

theorem c5071 (p : Nat → Prop)
    (d255 : (p 120) → (p 122) → (p 140) → False)
    (d173 : (¬ p 40) → (¬ p 43) → (¬ p 120) → False)
    : (¬ p 40) → (¬ p 43) → (p 140) → (p 122) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 120 := (fun u => d255 u a3 a2)
  exact d173 a0 a1 v0

theorem c5072 (p : Nat → Prop)
    (d555 : (p 54) → (p 57) → (p 120) → False)
    (d173 : (¬ p 40) → (¬ p 43) → (¬ p 120) → False)
    : (¬ p 40) → (¬ p 43) → (p 57) → (p 54) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 120 := (fun u => d555 a3 a2 u)
  exact d173 a0 a1 v0

theorem c5073 (p : Nat → Prop)
    (d319 : (p 100) → (p 103) → (p 120) → False)
    (d173 : (¬ p 40) → (¬ p 43) → (¬ p 120) → False)
    : (¬ p 40) → (¬ p 43) → (p 103) → (p 100) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 120 := (fun u => d319 a3 a2 u)
  exact d173 a0 a1 v0

theorem c5074 (p : Nat → Prop)
    (d103 : (p 9) → (p 16) → (p 124) → False)
    (d43 : (¬ p 90) → (¬ p 97) → (¬ p 124) → False)
    : (¬ p 97) → (¬ p 90) → (p 9) → (p 16) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 124 := (fun u => d103 a2 a3 u)
  exact d43 a1 a0 v0

theorem c5075 (p : Nat → Prop)
    (d116 : (p 119) → (p 124) → (p 137) → False)
    (d43 : (¬ p 90) → (¬ p 97) → (¬ p 124) → False)
    : (¬ p 97) → (¬ p 90) → (p 137) → (p 119) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 124 := (fun u => d116 a3 u a2)
  exact d43 a1 a0 v0

theorem c5076 (p : Nat → Prop)
    (d522 : (p 67) → (p 74) → (p 124) → False)
    (d43 : (¬ p 90) → (¬ p 97) → (¬ p 124) → False)
    : (¬ p 97) → (¬ p 90) → (p 67) → (p 74) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 124 := (fun u => d522 a2 a3 u)
  exact d43 a1 a0 v0

theorem c5077 (p : Nat → Prop)
    (d254 : (p 25) → (p 32) → (p 124) → False)
    (d43 : (¬ p 90) → (¬ p 97) → (¬ p 124) → False)
    : (¬ p 97) → (¬ p 90) → (p 25) → (p 32) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 124 := (fun u => d254 a2 a3 u)
  exact d43 a1 a0 v0

theorem c5078 (p : Nat → Prop)
    (d516 : (p 40) → (p 47) → (p 124) → False)
    (d43 : (¬ p 90) → (¬ p 97) → (¬ p 124) → False)
    : (¬ p 97) → (¬ p 90) → (p 40) → (p 47) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 124 := (fun u => d516 a2 a3 u)
  exact d43 a1 a0 v0

theorem c5079 (p : Nat → Prop)
    (d65 : (p 79) → (p 86) → (p 124) → False)
    (d43 : (¬ p 90) → (¬ p 97) → (¬ p 124) → False)
    : (¬ p 97) → (¬ p 90) → (p 86) → (p 79) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 124 := (fun u => d65 a3 a2 u)
  exact d43 a1 a0 v0

theorem c5080 (p : Nat → Prop)
    (d126 : (p 118) → (p 124) → (p 131) → False)
    (d43 : (¬ p 90) → (¬ p 97) → (¬ p 124) → False)
    : (¬ p 97) → (¬ p 90) → (p 131) → (p 118) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 124 := (fun u => d126 a3 u a2)
  exact d43 a1 a0 v0

theorem c5081 (p : Nat → Prop)
    (d4899 : (¬ p 142) → (¬ p 57) → (p 124) → (p 54) → False)
    (d43 : (¬ p 90) → (¬ p 97) → (¬ p 124) → False)
    : (¬ p 97) → (¬ p 90) → (¬ p 142) → (¬ p 57) → (p 54) → False := by
  intro a0 a1 a2 a3 a4
  have v0 : ¬ p 124 := (fun u => d4899 a2 a3 u a4)
  exact d43 a1 a0 v0

theorem c5082 (p : Nat → Prop)
    (d4936 : (¬ p 17) → (¬ p 16) → (p 124) → (p 125) → False)
    (d43 : (¬ p 90) → (¬ p 97) → (¬ p 124) → False)
    : (¬ p 97) → (¬ p 90) → (¬ p 17) → (¬ p 16) → (p 125) → False := by
  intro a0 a1 a2 a3 a4
  have v0 : ¬ p 124 := (fun u => d4936 a2 a3 u a4)
  exact d43 a1 a0 v0

theorem c5083 (p : Nat → Prop)
    (d514 : (p 55) → (p 58) → (p 128) → False)
    (d88 : (¬ p 41) → (¬ p 44) → (¬ p 128) → False)
    : (¬ p 41) → (¬ p 44) → (p 55) → (p 58) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 128 := (fun u => d514 a2 a3 u)
  exact d88 a0 a1 v0

theorem c5084 (p : Nat → Prop)
    (d44 : (p 26) → (p 29) → (p 128) → False)
    (d88 : (¬ p 41) → (¬ p 44) → (¬ p 128) → False)
    : (¬ p 41) → (¬ p 44) → (p 29) → (p 26) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 128 := (fun u => d44 a3 a2 u)
  exact d88 a0 a1 v0

theorem c5085 (p : Nat → Prop)
    (d233 : (p 10) → (p 13) → (p 128) → False)
    (d88 : (¬ p 41) → (¬ p 44) → (¬ p 128) → False)
    : (¬ p 41) → (¬ p 44) → (p 13) → (p 10) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 128 := (fun u => d233 a3 a2 u)
  exact d88 a0 a1 v0

theorem c5086 (p : Nat → Prop)
    (d212 : (p 126) → (p 128) → (p 134) → False)
    (d88 : (¬ p 41) → (¬ p 44) → (¬ p 128) → False)
    : (¬ p 41) → (¬ p 44) → (p 134) → (p 126) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 128 := (fun u => d212 a3 u a2)
  exact d88 a0 a1 v0

theorem c5087 (p : Nat → Prop)
    (d377 : (p 127) → (p 128) → (p 139) → False)
    (d88 : (¬ p 41) → (¬ p 44) → (¬ p 128) → False)
    : (¬ p 41) → (¬ p 44) → (p 139) → (p 127) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 128 := (fun u => d377 a3 u a2)
  exact d88 a0 a1 v0

theorem c5088 (p : Nat → Prop)
    (d511 : (p 128) → (p 132) → (p 147) → False)
    (d88 : (¬ p 41) → (¬ p 44) → (¬ p 128) → False)
    : (¬ p 41) → (¬ p 44) → (p 147) → (p 132) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 128 := (fun u => d511 u a3 a2)
  exact d88 a0 a1 v0

theorem c5089 (p : Nat → Prop)
    (d4916 : (¬ p 54) → (¬ p 58) → (p 128) → (p 118) → False)
    (d88 : (¬ p 41) → (¬ p 44) → (¬ p 128) → False)
    : (¬ p 41) → (¬ p 44) → (¬ p 54) → (¬ p 58) → (p 118) → False := by
  intro a0 a1 a2 a3 a4
  have v0 : ¬ p 128 := (fun u => d4916 a2 a3 u a4)
  exact d88 a0 a1 v0

theorem c5090 (p : Nat → Prop)
    (d4923 : (¬ p 31) → (¬ p 29) → (p 130) → (p 128) → False)
    (d88 : (¬ p 41) → (¬ p 44) → (¬ p 128) → False)
    : (¬ p 41) → (¬ p 44) → (¬ p 31) → (¬ p 29) → (p 130) → False := by
  intro a0 a1 a2 a3 a4
  have v0 : ¬ p 128 := (fun u => d4923 a2 a3 a4 u)
  exact d88 a0 a1 v0

theorem c5091 (p : Nat → Prop)
    (d4986 : (¬ p 14) → (¬ p 13) → (p 129) → (p 128) → False)
    (d88 : (¬ p 41) → (¬ p 44) → (¬ p 128) → False)
    : (¬ p 41) → (¬ p 44) → (¬ p 14) → (¬ p 13) → (p 129) → False := by
  intro a0 a1 a2 a3 a4
  have v0 : ¬ p 128 := (fun u => d4986 a2 a3 a4 u)
  exact d88 a0 a1 v0

theorem c5092 (p : Nat → Prop)
    (d547 : (p 136) → (p 137) → (p 151) → False)
    (d153 : (¬ p 15) → (¬ p 16) → (¬ p 151) → False)
    : (¬ p 16) → (¬ p 15) → (p 137) → (p 136) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 151 := (fun u => d547 a3 a2 u)
  exact d153 a1 a0 v0

theorem c5093 (p : Nat → Prop)
    (d585 : (p 96) → (p 97) → (p 151) → False)
    (d153 : (¬ p 15) → (¬ p 16) → (¬ p 151) → False)
    : (¬ p 16) → (¬ p 15) → (p 97) → (p 96) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 151 := (fun u => d585 a3 a2 u)
  exact d153 a1 a0 v0

theorem c5094 (p : Nat → Prop)
    (d496 : (p 141) → (p 142) → (p 151) → False)
    (d153 : (¬ p 15) → (¬ p 16) → (¬ p 151) → False)
    : (¬ p 16) → (¬ p 15) → (p 142) → (p 141) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 151 := (fun u => d496 a3 a2 u)
  exact d153 a1 a0 v0

theorem c5096 (p : Nat → Prop)
    (d412 : (p 73) → (p 74) → (p 151) → False)
    (d153 : (¬ p 15) → (¬ p 16) → (¬ p 151) → False)
    : (¬ p 16) → (¬ p 15) → (p 73) → (p 74) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 151 := (fun u => d412 a2 a3 u)
  exact d153 a1 a0 v0

theorem c5097 (p : Nat → Prop)
    (d554 : (p 31) → (p 32) → (p 151) → False)
    (d153 : (¬ p 15) → (¬ p 16) → (¬ p 151) → False)
    : (¬ p 16) → (¬ p 15) → (p 32) → (p 31) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 151 := (fun u => d554 a3 a2 u)
  exact d153 a1 a0 v0

theorem c5098 (p : Nat → Prop)
    (d4926 : (¬ p 31) → (¬ p 29) → (p 151) → (p 146) → False)
    (d153 : (¬ p 15) → (¬ p 16) → (¬ p 151) → False)
    : (¬ p 16) → (¬ p 15) → (¬ p 31) → (¬ p 29) → (p 146) → False := by
  intro a0 a1 a2 a3 a4
  have v0 : ¬ p 151 := (fun u => d4926 a2 a3 u a4)
  exact d153 a1 a0 v0

theorem c5099 (p : Nat → Prop)
    (d4933 : (¬ p 17) → (¬ p 16) → (p 152) → (p 151) → False)
    (d153 : (¬ p 15) → (¬ p 16) → (¬ p 151) → False)
    : (¬ p 16) → (¬ p 15) → (¬ p 17) → (p 152) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 151 := (fun u => d4933 a2 a0 a3 u)
  exact d153 a1 a0 v0

theorem c5100 (p : Nat → Prop)
    (d4983 : (¬ p 96) → (¬ p 89) → (p 116) → (p 151) → False)
    (d153 : (¬ p 15) → (¬ p 16) → (¬ p 151) → False)
    : (¬ p 16) → (¬ p 15) → (¬ p 96) → (¬ p 89) → (p 116) → False := by
  intro a0 a1 a2 a3 a4
  have v0 : ¬ p 151 := (fun u => d4983 a2 a3 a4 u)
  exact d153 a1 a0 v0

theorem c5101 (p : Nat → Prop)
    (d465 : (p 110) → (p 114) → (p 129) → False)
    (d341 : (¬ p 24) → (¬ p 26) → (¬ p 110) → False)
    : (¬ p 24) → (¬ p 26) → (p 129) → (p 114) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 110 := (fun u => d465 u a3 a2)
  exact d341 a0 a1 v0

theorem c5102 (p : Nat → Prop)
    (d509 : (p 8) → (p 10) → (p 110) → False)
    (d341 : (¬ p 24) → (¬ p 26) → (¬ p 110) → False)
    : (¬ p 24) → (¬ p 26) → (p 8) → (p 10) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 110 := (fun u => d509 a2 a3 u)
  exact d341 a0 a1 v0

theorem c5103 (p : Nat → Prop)
    (d97 : (p 89) → (p 91) → (p 110) → False)
    (d341 : (¬ p 24) → (¬ p 26) → (¬ p 110) → False)
    : (¬ p 24) → (¬ p 26) → (p 91) → (p 89) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 110 := (fun u => d97 a3 a2 u)
  exact d341 a0 a1 v0

theorem c5104 (p : Nat → Prop)
    (d391 : (p 66) → (p 68) → (p 110) → False)
    (d341 : (¬ p 24) → (¬ p 26) → (¬ p 110) → False)
    : (¬ p 24) → (¬ p 26) → (p 66) → (p 68) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 110 := (fun u => d391 a2 a3 u)
  exact d341 a0 a1 v0

theorem c5105 (p : Nat → Prop)
    (d150 : (p 78) → (p 80) → (p 110) → False)
    (d341 : (¬ p 24) → (¬ p 26) → (¬ p 110) → False)
    : (¬ p 24) → (¬ p 26) → (p 78) → (p 80) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 110 := (fun u => d150 a2 a3 u)
  exact d341 a0 a1 v0

theorem c5106 (p : Nat → Prop)
    (d14 : (p 39) → (p 41) → (p 110) → False)
    (d341 : (¬ p 24) → (¬ p 26) → (¬ p 110) → False)
    : (¬ p 24) → (¬ p 26) → (p 39) → (p 41) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 110 := (fun u => d14 a2 a3 u)
  exact d341 a0 a1 v0

theorem c5107 (p : Nat → Prop)
    (d237 : (p 99) → (p 101) → (p 110) → False)
    (d341 : (¬ p 24) → (¬ p 26) → (¬ p 110) → False)
    : (¬ p 24) → (¬ p 26) → (p 101) → (p 99) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 110 := (fun u => d237 a3 a2 u)
  exact d341 a0 a1 v0

theorem c5108 (p : Nat → Prop)
    (d590 : (p 110) → (p 116) → (p 131) → False)
    (d341 : (¬ p 24) → (¬ p 26) → (¬ p 110) → False)
    : (¬ p 24) → (¬ p 26) → (p 116) → (p 131) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 110 := (fun u => d590 u a2 a3)
  exact d341 a0 a1 v0

theorem c5109 (p : Nat → Prop)
    (d265 : (p 109) → (p 110) → (p 118) → False)
    (d341 : (¬ p 24) → (¬ p 26) → (¬ p 110) → False)
    : (¬ p 24) → (¬ p 26) → (p 109) → (p 118) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 110 := (fun u => d265 a2 u a3)
  exact d341 a0 a1 v0

theorem c5110 (p : Nat → Prop)
    (d4978 : (¬ p 96) → (¬ p 89) → (p 110) → (p 130) → False)
    (d341 : (¬ p 24) → (¬ p 26) → (¬ p 110) → False)
    : (¬ p 24) → (¬ p 26) → (¬ p 96) → (¬ p 89) → (p 130) → False := by
  intro a0 a1 a2 a3 a4
  have v0 : ¬ p 110 := (fun u => d4978 a2 a3 u a4)
  exact d341 a0 a1 v0

theorem c5111 (p : Nat → Prop)
    (d294 : (p 24) → (p 28) → (p 112) → False)
    (d538 : (¬ p 53) → (¬ p 57) → (¬ p 112) → False)
    : (¬ p 57) → (¬ p 53) → (p 28) → (p 24) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 112 := (fun u => d294 a3 a2 u)
  exact d538 a1 a0 v0

theorem c5112 (p : Nat → Prop)
    (d70 : (p 8) → (p 12) → (p 112) → False)
    (d538 : (¬ p 53) → (¬ p 57) → (¬ p 112) → False)
    : (¬ p 57) → (¬ p 53) → (p 12) → (p 8) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 112 := (fun u => d70 a3 a2 u)
  exact d538 a1 a0 v0

theorem c5113 (p : Nat → Prop)
    (d497 : (p 89) → (p 93) → (p 112) → False)
    (d538 : (¬ p 53) → (¬ p 57) → (¬ p 112) → False)
    : (¬ p 57) → (¬ p 53) → (p 93) → (p 89) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 112 := (fun u => d497 a3 a2 u)
  exact d538 a1 a0 v0

theorem c5114 (p : Nat → Prop)
    (d167 : (p 39) → (p 43) → (p 112) → False)
    (d538 : (¬ p 53) → (¬ p 57) → (¬ p 112) → False)
    : (¬ p 57) → (¬ p 53) → (p 43) → (p 39) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 112 := (fun u => d167 a3 a2 u)
  exact d538 a1 a0 v0

theorem c5115 (p : Nat → Prop)
    (d367 : (p 66) → (p 70) → (p 112) → False)
    (d538 : (¬ p 53) → (¬ p 57) → (¬ p 112) → False)
    : (¬ p 57) → (¬ p 53) → (p 66) → (p 70) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 112 := (fun u => d367 a2 a3 u)
  exact d538 a1 a0 v0

theorem c5116 (p : Nat → Prop)
    (d416 : (p 99) → (p 103) → (p 112) → False)
    (d538 : (¬ p 53) → (¬ p 57) → (¬ p 112) → False)
    : (¬ p 57) → (¬ p 53) → (p 103) → (p 99) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 112 := (fun u => d416 a3 a2 u)
  exact d538 a1 a0 v0

theorem c5117 (p : Nat → Prop)
    (d4975 : (¬ p 39) → (¬ p 42) → (p 112) → (p 133) → False)
    (d538 : (¬ p 53) → (¬ p 57) → (¬ p 112) → False)
    : (¬ p 57) → (¬ p 53) → (¬ p 39) → (¬ p 42) → (p 133) → False := by
  intro a0 a1 a2 a3 a4
  have v0 : ¬ p 112 := (fun u => d4975 a2 a3 u a4)
  exact d538 a1 a0 v0

theorem c5118 (p : Nat → Prop)
    (d4982 : (¬ p 96) → (¬ p 89) → (p 112) → (p 141) → False)
    (d538 : (¬ p 53) → (¬ p 57) → (¬ p 112) → False)
    : (¬ p 57) → (¬ p 53) → (¬ p 96) → (¬ p 89) → (p 141) → False := by
  intro a0 a1 a2 a3 a4
  have v0 : ¬ p 112 := (fun u => d4982 a2 a3 u a4)
  exact d538 a1 a0 v0

theorem c5119 (p : Nat → Prop)
    (d5026 : (¬ p 93) → (¬ p 76) → (p 112) → (p 78) → False)
    (d538 : (¬ p 53) → (¬ p 57) → (¬ p 112) → False)
    : (¬ p 57) → (¬ p 53) → (¬ p 93) → (¬ p 76) → (p 78) → False := by
  intro a0 a1 a2 a3 a4
  have v0 : ¬ p 112 := (fun u => d5026 a2 a3 u a4)
  exact d538 a1 a0 v0

theorem c5120 (p : Nat → Prop)
    (d5061 : (¬ p 71) → (¬ p 66) → (p 112) → (p 139) → False)
    (d538 : (¬ p 53) → (¬ p 57) → (¬ p 112) → False)
    : (¬ p 57) → (¬ p 53) → (¬ p 71) → (¬ p 66) → (p 139) → False := by
  intro a0 a1 a2 a3 a4
  have v0 : ¬ p 112 := (fun u => d5061 a2 a3 u a4)
  exact d538 a1 a0 v0

theorem c5121 (p : Nat → Prop)
    (d220 : (p 8) → (p 16) → (p 116) → False)
    (d83 : (¬ p 99) → (¬ p 107) → (¬ p 116) → False)
    : (¬ p 107) → (¬ p 99) → (p 8) → (p 16) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 116 := (fun u => d220 a2 a3 u)
  exact d83 a1 a0 v0

theorem c5122 (p : Nat → Prop)
    (d476 : (p 89) → (p 97) → (p 116) → False)
    (d83 : (¬ p 99) → (¬ p 107) → (¬ p 116) → False)
    : (¬ p 107) → (¬ p 99) → (p 97) → (p 89) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 116 := (fun u => d476 a3 a2 u)
  exact d83 a1 a0 v0

theorem c5123 (p : Nat → Prop)
    (d80 : (p 114) → (p 116) → (p 149) → False)
    (d83 : (¬ p 99) → (¬ p 107) → (¬ p 116) → False)
    : (¬ p 107) → (¬ p 99) → (p 114) → (p 149) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 116 := (fun u => d80 a2 u a3)
  exact d83 a1 a0 v0

theorem c5124 (p : Nat → Prop)
    (d216 : (p 39) → (p 47) → (p 116) → False)
    (d83 : (¬ p 99) → (¬ p 107) → (¬ p 116) → False)
    : (¬ p 107) → (¬ p 99) → (p 39) → (p 47) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 116 := (fun u => d216 a2 a3 u)
  exact d83 a1 a0 v0

theorem c5125 (p : Nat → Prop)
    (d551 : (p 66) → (p 74) → (p 116) → False)
    (d83 : (¬ p 99) → (¬ p 107) → (¬ p 116) → False)
    : (¬ p 107) → (¬ p 99) → (p 66) → (p 74) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 116 := (fun u => d551 a2 a3 u)
  exact d83 a1 a0 v0

theorem c5126 (p : Nat → Prop)
    (d318 : (p 78) → (p 86) → (p 116) → False)
    (d83 : (¬ p 99) → (¬ p 107) → (¬ p 116) → False)
    : (¬ p 107) → (¬ p 99) → (p 78) → (p 86) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 116 := (fun u => d318 a2 a3 u)
  exact d83 a1 a0 v0

theorem c5127 (p : Nat → Prop)
    (d4971 : (¬ p 39) → (¬ p 42) → (p 116) → (p 137) → False)
    (d83 : (¬ p 99) → (¬ p 107) → (¬ p 116) → False)
    : (¬ p 107) → (¬ p 99) → (¬ p 39) → (¬ p 42) → (p 137) → False := by
  intro a0 a1 a2 a3 a4
  have v0 : ¬ p 116 := (fun u => d4971 a2 a3 u a4)
  exact d83 a1 a0 v0

theorem c5128 (p : Nat → Prop)
    (d5060 : (¬ p 71) → (¬ p 66) → (p 116) → (p 146) → False)
    (d83 : (¬ p 99) → (¬ p 107) → (¬ p 116) → False)
    : (¬ p 107) → (¬ p 99) → (¬ p 71) → (¬ p 66) → (p 146) → False := by
  intro a0 a1 a2 a3 a4
  have v0 : ¬ p 116 := (fun u => d5060 a2 a3 u a4)
  exact d83 a1 a0 v0

theorem c5129 (p : Nat → Prop)
    (d5108 : (¬ p 24) → (¬ p 26) → (p 116) → (p 131) → False)
    (d83 : (¬ p 99) → (¬ p 107) → (¬ p 116) → False)
    : (¬ p 107) → (¬ p 99) → (¬ p 24) → (¬ p 26) → (p 131) → False := by
  intro a0 a1 a2 a3 a4
  have v0 : ¬ p 116 := (fun u => d5108 a2 a3 u a4)
  exact d83 a1 a0 v0

theorem c5130 (p : Nat → Prop)
    (d5100 : (¬ p 16) → (¬ p 15) → (¬ p 96) → (¬ p 89) → (p 116) → False)
    (d83 : (¬ p 99) → (¬ p 107) → (¬ p 116) → False)
    : (¬ p 107) → (¬ p 99) → (¬ p 16) → (¬ p 15) → (¬ p 96) → (¬ p 89) → False := by
  intro a0 a1 a2 a3 a4 a5
  have v0 : ¬ p 116 := (fun u => d5100 a2 a3 a4 a5 u)
  exact d83 a1 a0 v0

theorem c5131 (p : Nat → Prop)
    (d112 : (p 109) → (p 114) → (p 122) → False)
    (d323 : (¬ p 67) → (¬ p 72) → (¬ p 122) → False)
    : (¬ p 72) → (¬ p 67) → (p 114) → (p 109) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 122 := (fun u => d112 a3 a2 u)
  exact d323 a1 a0 v0

theorem c5132 (p : Nat → Prop)
    (d217 : (p 79) → (p 84) → (p 122) → False)
    (d323 : (¬ p 67) → (¬ p 72) → (¬ p 122) → False)
    : (¬ p 72) → (¬ p 67) → (p 79) → (p 84) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 122 := (fun u => d217 a2 a3 u)
  exact d323 a1 a0 v0

theorem c5133 (p : Nat → Prop)
    (d501 : (p 40) → (p 45) → (p 122) → False)
    (d323 : (¬ p 67) → (¬ p 72) → (¬ p 122) → False)
    : (¬ p 72) → (¬ p 67) → (p 45) → (p 40) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 122 := (fun u => d501 a3 a2 u)
  exact d323 a1 a0 v0

theorem c5134 (p : Nat → Prop)
    (d595 : (p 122) → (p 123) → (p 148) → False)
    (d323 : (¬ p 67) → (¬ p 72) → (¬ p 122) → False)
    : (¬ p 72) → (¬ p 67) → (p 123) → (p 148) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 122 := (fun u => d595 u a2 a3)
  exact d323 a1 a0 v0

theorem c5135 (p : Nat → Prop)
    (d454 : (p 25) → (p 30) → (p 122) → False)
    (d323 : (¬ p 67) → (¬ p 72) → (¬ p 122) → False)
    : (¬ p 72) → (¬ p 67) → (p 30) → (p 25) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 122 := (fun u => d454 a3 a2 u)
  exact d323 a1 a0 v0

theorem c5136 (p : Nat → Prop)
    (d331 : (p 100) → (p 105) → (p 122) → False)
    (d323 : (¬ p 67) → (¬ p 72) → (¬ p 122) → False)
    : (¬ p 72) → (¬ p 67) → (p 105) → (p 100) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 122 := (fun u => d331 a3 a2 u)
  exact d323 a1 a0 v0

theorem c5137 (p : Nat → Prop)
    (d64 : (p 119) → (p 122) → (p 135) → False)
    (d323 : (¬ p 67) → (¬ p 72) → (¬ p 122) → False)
    : (¬ p 72) → (¬ p 67) → (p 119) → (p 135) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 122 := (fun u => d64 a2 u a3)
  exact d323 a1 a0 v0

theorem c5138 (p : Nat → Prop)
    (d4953 : (¬ p 129) → (¬ p 55) → (p 122) → (p 54) → False)
    (d323 : (¬ p 67) → (¬ p 72) → (¬ p 122) → False)
    : (¬ p 72) → (¬ p 67) → (¬ p 129) → (¬ p 55) → (p 54) → False := by
  intro a0 a1 a2 a3 a4
  have v0 : ¬ p 122 := (fun u => d4953 a2 a3 u a4)
  exact d323 a1 a0 v0

theorem c5139 (p : Nat → Prop)
    (d5049 : (¬ p 105) → (¬ p 88) → (p 122) → (p 90) → False)
    (d323 : (¬ p 67) → (¬ p 72) → (¬ p 122) → False)
    : (¬ p 72) → (¬ p 67) → (¬ p 105) → (¬ p 88) → (p 90) → False := by
  intro a0 a1 a2 a3 a4
  have v0 : ¬ p 122 := (fun u => d5049 a2 a3 u a4)
  exact d323 a1 a0 v0

theorem c5140 (p : Nat → Prop)
    (d5071 : (¬ p 40) → (¬ p 43) → (p 140) → (p 122) → False)
    (d323 : (¬ p 67) → (¬ p 72) → (¬ p 122) → False)
    : (¬ p 72) → (¬ p 67) → (¬ p 40) → (¬ p 43) → (p 140) → False := by
  intro a0 a1 a2 a3 a4
  have v0 : ¬ p 122 := (fun u => d5071 a2 a3 a4 u)
  exact d323 a1 a0 v0

theorem c5141 (p : Nat → Prop)
    (d480 : (p 79) → (p 87) → (p 125) → False)
    (d54 : (¬ p 100) → (¬ p 108) → (¬ p 125) → False)
    : (¬ p 100) → (¬ p 108) → (p 87) → (p 79) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 125 := (fun u => d480 a3 a2 u)
  exact d54 a0 a1 v0

theorem c5142 (p : Nat → Prop)
    (d436 : (p 25) → (p 33) → (p 125) → False)
    (d54 : (¬ p 100) → (¬ p 108) → (¬ p 125) → False)
    : (¬ p 100) → (¬ p 108) → (p 25) → (p 33) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 125 := (fun u => d436 a2 a3 u)
  exact d54 a0 a1 v0

theorem c5143 (p : Nat → Prop)
    (d525 : (p 9) → (p 17) → (p 125) → False)
    (d54 : (¬ p 100) → (¬ p 108) → (¬ p 125) → False)
    : (¬ p 100) → (¬ p 108) → (p 17) → (p 9) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 125 := (fun u => d525 a3 a2 u)
  exact d54 a0 a1 v0

theorem c5144 (p : Nat → Prop)
    (d457 : (p 90) → (p 98) → (p 125) → False)
    (d54 : (¬ p 100) → (¬ p 108) → (¬ p 125) → False)
    : (¬ p 100) → (¬ p 108) → (p 98) → (p 90) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 125 := (fun u => d457 a3 a2 u)
  exact d54 a0 a1 v0

theorem c5145 (p : Nat → Prop)
    (d493 : (p 119) → (p 125) → (p 138) → False)
    (d54 : (¬ p 100) → (¬ p 108) → (¬ p 125) → False)
    : (¬ p 100) → (¬ p 108) → (p 119) → (p 138) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 125 := (fun u => d493 a2 u a3)
  exact d54 a0 a1 v0

theorem c5146 (p : Nat → Prop)
    (d415 : (p 118) → (p 125) → (p 132) → False)
    (d54 : (¬ p 100) → (¬ p 108) → (¬ p 125) → False)
    : (¬ p 100) → (¬ p 108) → (p 132) → (p 118) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 125 := (fun u => d415 a3 u a2)
  exact d54 a0 a1 v0

theorem c5147 (p : Nat → Prop)
    (d4919 : (¬ p 54) → (¬ p 58) → (p 147) → (p 125) → False)
    (d54 : (¬ p 100) → (¬ p 108) → (¬ p 125) → False)
    : (¬ p 100) → (¬ p 108) → (¬ p 54) → (¬ p 58) → (p 147) → False := by
  intro a0 a1 a2 a3 a4
  have v0 : ¬ p 125 := (fun u => d4919 a2 a3 a4 u)
  exact d54 a0 a1 v0

theorem c5148 (p : Nat → Prop)
    (d5013 : (¬ p 143) → (¬ p 70) → (p 67) → (p 125) → False)
    (d54 : (¬ p 100) → (¬ p 108) → (¬ p 125) → False)
    : (¬ p 100) → (¬ p 108) → (¬ p 143) → (¬ p 70) → (p 67) → False := by
  intro a0 a1 a2 a3 a4
  have v0 : ¬ p 125 := (fun u => d5013 a2 a3 a4 u)
  exact d54 a0 a1 v0

theorem c5149 (p : Nat → Prop)
    (d5067 : (¬ p 40) → (¬ p 43) → (p 143) → (p 125) → False)
    (d54 : (¬ p 100) → (¬ p 108) → (¬ p 125) → False)
    : (¬ p 100) → (¬ p 108) → (¬ p 40) → (¬ p 43) → (p 143) → False := by
  intro a0 a1 a2 a3 a4
  have v0 : ¬ p 125 := (fun u => d5067 a2 a3 a4 u)
  exact d54 a0 a1 v0

theorem c5150 (p : Nat → Prop)
    (d5082 : (¬ p 97) → (¬ p 90) → (¬ p 17) → (¬ p 16) → (p 125) → False)
    (d54 : (¬ p 100) → (¬ p 108) → (¬ p 125) → False)
    : (¬ p 100) → (¬ p 108) → (¬ p 97) → (¬ p 90) → (¬ p 17) → (¬ p 16) → False := by
  intro a0 a1 a2 a3 a4 a5
  have v0 : ¬ p 125 := (fun u => d5082 a2 a3 a4 a5 u)
  exact d54 a0 a1 v0

theorem c5151 (p : Nat → Prop)
    (d428 : (p 126) → (p 127) → (p 133) → False)
    (d492 : (¬ p 26) → (¬ p 28) → (¬ p 127) → False)
    : (¬ p 26) → (¬ p 28) → (p 133) → (p 126) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 127 := (fun u => d428 a3 u a2)
  exact d492 a0 a1 v0

theorem c5152 (p : Nat → Prop)
    (d196 : (p 127) → (p 132) → (p 143) → False)
    (d492 : (¬ p 26) → (¬ p 28) → (¬ p 127) → False)
    : (¬ p 26) → (¬ p 28) → (p 143) → (p 132) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 127 := (fun u => d196 u a3 a2)
  exact d492 a0 a1 v0

theorem c5153 (p : Nat → Prop)
    (d282 : (p 127) → (p 130) → (p 141) → False)
    (d492 : (¬ p 26) → (¬ p 28) → (¬ p 127) → False)
    : (¬ p 26) → (¬ p 28) → (p 141) → (p 130) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 127 := (fun u => d282 u a3 a2)
  exact d492 a0 a1 v0

theorem c5154 (p : Nat → Prop)
    (d586 : (p 127) → (p 131) → (p 142) → False)
    (d492 : (¬ p 26) → (¬ p 28) → (¬ p 127) → False)
    : (¬ p 26) → (¬ p 28) → (p 131) → (p 142) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 127 := (fun u => d586 u a2 a3)
  exact d492 a0 a1 v0

theorem c5155 (p : Nat → Prop)
    (d383 : (p 10) → (p 12) → (p 127) → False)
    (d492 : (¬ p 26) → (¬ p 28) → (¬ p 127) → False)
    : (¬ p 26) → (¬ p 28) → (p 12) → (p 10) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 127 := (fun u => d383 a3 a2 u)
  exact d492 a0 a1 v0

theorem c5156 (p : Nat → Prop)
    (d440 : (p 41) → (p 43) → (p 127) → False)
    (d492 : (¬ p 26) → (¬ p 28) → (¬ p 127) → False)
    : (¬ p 26) → (¬ p 28) → (p 43) → (p 41) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 127 := (fun u => d440 a3 a2 u)
  exact d492 a0 a1 v0

theorem c5157 (p : Nat → Prop)
    (d530 : (p 68) → (p 70) → (p 127) → False)
    (d492 : (¬ p 26) → (¬ p 28) → (¬ p 127) → False)
    : (¬ p 26) → (¬ p 28) → (p 70) → (p 68) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 127 := (fun u => d530 a3 a2 u)
  exact d492 a0 a1 v0

theorem c5158 (p : Nat → Prop)
    (d77 : (p 91) → (p 93) → (p 127) → False)
    (d492 : (¬ p 26) → (¬ p 28) → (¬ p 127) → False)
    : (¬ p 26) → (¬ p 28) → (p 93) → (p 91) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 127 := (fun u => d77 a3 a2 u)
  exact d492 a0 a1 v0

theorem c5159 (p : Nat → Prop)
    (d593 : (p 101) → (p 103) → (p 127) → False)
    (d492 : (¬ p 26) → (¬ p 28) → (¬ p 127) → False)
    : (¬ p 26) → (¬ p 28) → (p 103) → (p 101) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 127 := (fun u => d593 a3 a2 u)
  exact d492 a0 a1 v0

theorem c5160 (p : Nat → Prop)
    (d5087 : (¬ p 41) → (¬ p 44) → (p 139) → (p 127) → False)
    (d492 : (¬ p 26) → (¬ p 28) → (¬ p 127) → False)
    : (¬ p 26) → (¬ p 28) → (¬ p 41) → (¬ p 44) → (p 139) → False := by
  intro a0 a1 a2 a3 a4
  have v0 : ¬ p 127 := (fun u => d5087 a2 a3 a4 u)
  exact d492 a0 a1 v0

theorem c5161 (p : Nat → Prop)
    (d108 : (p 10) → (p 16) → (p 131) → False)
    (d378 : (¬ p 80) → (¬ p 86) → (¬ p 131) → False)
    : (¬ p 86) → (¬ p 80) → (p 16) → (p 10) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 131 := (fun u => d108 a3 a2 u)
  exact d378 a1 a0 v0

theorem c5162 (p : Nat → Prop)
    (d168 : (p 126) → (p 131) → (p 137) → False)
    (d378 : (¬ p 80) → (¬ p 86) → (¬ p 131) → False)
    : (¬ p 86) → (¬ p 80) → (p 137) → (p 126) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 131 := (fun u => d168 a3 u a2)
  exact d378 a1 a0 v0

theorem c5163 (p : Nat → Prop)
    (d446 : (p 129) → (p 131) → (p 149) → False)
    (d378 : (¬ p 80) → (¬ p 86) → (¬ p 131) → False)
    : (¬ p 86) → (¬ p 80) → (p 129) → (p 149) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 131 := (fun u => d446 a2 u a3)
  exact d378 a1 a0 v0

theorem c5164 (p : Nat → Prop)
    (d198 : (p 26) → (p 32) → (p 131) → False)
    (d378 : (¬ p 80) → (¬ p 86) → (¬ p 131) → False)
    : (¬ p 86) → (¬ p 80) → (p 26) → (p 32) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 131 := (fun u => d198 a2 a3 u)
  exact d378 a1 a0 v0

theorem c5165 (p : Nat → Prop)
    (d441 : (p 41) → (p 47) → (p 131) → False)
    (d378 : (¬ p 80) → (¬ p 86) → (¬ p 131) → False)
    : (¬ p 86) → (¬ p 80) → (p 41) → (p 47) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 131 := (fun u => d441 a2 a3 u)
  exact d378 a1 a0 v0

theorem c5166 (p : Nat → Prop)
    (d466 : (p 101) → (p 107) → (p 131) → False)
    (d378 : (¬ p 80) → (¬ p 86) → (¬ p 131) → False)
    : (¬ p 86) → (¬ p 80) → (p 107) → (p 101) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 131 := (fun u => d466 a3 a2 u)
  exact d378 a1 a0 v0

theorem c5167 (p : Nat → Prop)
    (d4931 : (¬ p 17) → (¬ p 16) → (p 131) → (p 132) → False)
    (d378 : (¬ p 80) → (¬ p 86) → (¬ p 131) → False)
    : (¬ p 86) → (¬ p 80) → (¬ p 17) → (¬ p 16) → (p 132) → False := by
  intro a0 a1 a2 a3 a4
  have v0 : ¬ p 131 := (fun u => d4931 a2 a3 u a4)
  exact d378 a1 a0 v0

theorem c5168 (p : Nat → Prop)
    (d5080 : (¬ p 97) → (¬ p 90) → (p 131) → (p 118) → False)
    (d378 : (¬ p 80) → (¬ p 86) → (¬ p 131) → False)
    : (¬ p 86) → (¬ p 80) → (¬ p 97) → (¬ p 90) → (p 118) → False := by
  intro a0 a1 a2 a3 a4
  have v0 : ¬ p 131 := (fun u => d5080 a2 a3 u a4)
  exact d378 a1 a0 v0

theorem c5169 (p : Nat → Prop)
    (d5154 : (¬ p 26) → (¬ p 28) → (p 131) → (p 142) → False)
    (d378 : (¬ p 80) → (¬ p 86) → (¬ p 131) → False)
    : (¬ p 86) → (¬ p 80) → (¬ p 26) → (¬ p 28) → (p 142) → False := by
  intro a0 a1 a2 a3 a4
  have v0 : ¬ p 131 := (fun u => d5154 a2 a3 u a4)
  exact d378 a1 a0 v0

theorem c5170 (p : Nat → Prop)
    (d5129 : (¬ p 107) → (¬ p 99) → (¬ p 24) → (¬ p 26) → (p 131) → False)
    (d378 : (¬ p 80) → (¬ p 86) → (¬ p 131) → False)
    : (¬ p 86) → (¬ p 80) → (¬ p 107) → (¬ p 99) → (¬ p 24) → (¬ p 26) → False := by
  intro a0 a1 a2 a3 a4 a5
  have v0 : ¬ p 131 := (fun u => d5129 a2 a3 a4 a5 u)
  exact d378 a1 a0 v0

theorem c5171 (p : Nat → Prop)
    (d393 : (p 11) → (p 13) → (p 134) → False)
    (d8 : (¬ p 27) → (¬ p 29) → (¬ p 134) → False)
    : (¬ p 27) → (¬ p 29) → (p 13) → (p 11) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 134 := (fun u => d393 a3 a2 u)
  exact d8 a0 a1 v0

theorem c5172 (p : Nat → Prop)
    (d274 : (p 133) → (p 134) → (p 139) → False)
    (d8 : (¬ p 27) → (¬ p 29) → (¬ p 134) → False)
    : (¬ p 27) → (¬ p 29) → (p 139) → (p 133) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 134 := (fun u => d274 a3 u a2)
  exact d8 a0 a1 v0

theorem c5173 (p : Nat → Prop)
    (d179 : (p 134) → (p 137) → (p 146) → False)
    (d8 : (¬ p 27) → (¬ p 29) → (¬ p 134) → False)
    : (¬ p 27) → (¬ p 29) → (p 146) → (p 137) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 134 := (fun u => d179 u a3 a2)
  exact d8 a0 a1 v0

theorem c5174 (p : Nat → Prop)
    (d420 : (p 56) → (p 58) → (p 134) → False)
    (d8 : (¬ p 27) → (¬ p 29) → (¬ p 134) → False)
    : (¬ p 27) → (¬ p 29) → (p 56) → (p 58) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 134 := (fun u => d420 a2 a3 u)
  exact d8 a0 a1 v0

theorem c5175 (p : Nat → Prop)
    (d73 : (p 69) → (p 71) → (p 134) → False)
    (d8 : (¬ p 27) → (¬ p 29) → (¬ p 134) → False)
    : (¬ p 27) → (¬ p 29) → (p 69) → (p 71) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 134 := (fun u => d73 a2 a3 u)
  exact d8 a0 a1 v0

theorem c5176 (p : Nat → Prop)
    (d4920 : (¬ p 54) → (¬ p 58) → (p 119) → (p 134) → False)
    (d8 : (¬ p 27) → (¬ p 29) → (¬ p 134) → False)
    : (¬ p 27) → (¬ p 29) → (¬ p 54) → (¬ p 58) → (p 119) → False := by
  intro a0 a1 a2 a3 a4
  have v0 : ¬ p 134 := (fun u => d4920 a2 a3 a4 u)
  exact d8 a0 a1 v0

theorem c5178 (p : Nat → Prop)
    (d4988 : (¬ p 14) → (¬ p 13) → (p 135) → (p 134) → False)
    (d8 : (¬ p 27) → (¬ p 29) → (¬ p 134) → False)
    : (¬ p 27) → (¬ p 29) → (¬ p 14) → (¬ p 13) → (p 135) → False := by
  intro a0 a1 a2 a3 a4
  have v0 : ¬ p 134 := (fun u => d4988 a2 a3 a4 u)
  exact d8 a0 a1 v0

theorem c5179 (p : Nat → Prop)
    (d5086 : (¬ p 41) → (¬ p 44) → (p 134) → (p 126) → False)
    (d8 : (¬ p 27) → (¬ p 29) → (¬ p 134) → False)
    : (¬ p 27) → (¬ p 29) → (¬ p 41) → (¬ p 44) → (p 126) → False := by
  intro a0 a1 a2 a3 a4
  have v0 : ¬ p 134 := (fun u => d5086 a2 a3 u a4)
  exact d8 a0 a1 v0

theorem c5180 (p : Nat → Prop)
    (d5063 : (¬ p 71) → (¬ p 66) → (¬ p 39) → (¬ p 42) → (p 134) → False)
    (d8 : (¬ p 27) → (¬ p 29) → (¬ p 134) → False)
    : (¬ p 27) → (¬ p 29) → (¬ p 71) → (¬ p 66) → (¬ p 39) → (¬ p 42) → False := by
  intro a0 a1 a2 a3 a4 a5
  have v0 : ¬ p 134 := (fun u => d5063 a2 a3 a4 a5 u)
  exact d8 a0 a1 v0

theorem c5181 (p : Nat → Prop)
    (d407 : (p 139) → (p 142) → (p 146) → False)
    (d92 : (¬ p 12) → (¬ p 13) → (¬ p 139) → False)
    : (¬ p 13) → (¬ p 12) → (p 146) → (p 142) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 139 := (fun u => d407 u a3 a2)
  exact d92 a1 a0 v0

theorem c5182 (p : Nat → Prop)
    (d260 : (p 139) → (p 143) → (p 147) → False)
    (d92 : (¬ p 12) → (¬ p 13) → (¬ p 139) → False)
    : (¬ p 13) → (¬ p 12) → (p 147) → (p 143) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 139 := (fun u => d260 u a3 a2)
  exact d92 a1 a0 v0

theorem c5183 (p : Nat → Prop)
    (d206 : (p 70) → (p 71) → (p 139) → False)
    (d92 : (¬ p 12) → (¬ p 13) → (¬ p 139) → False)
    : (¬ p 13) → (¬ p 12) → (p 70) → (p 71) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 139 := (fun u => d206 a2 a3 u)
  exact d92 a1 a0 v0

theorem c5184 (p : Nat → Prop)
    (d6 : (p 43) → (p 44) → (p 139) → False)
    (d92 : (¬ p 12) → (¬ p 13) → (¬ p 139) → False)
    : (¬ p 13) → (¬ p 12) → (p 44) → (p 43) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 139 := (fun u => d6 a3 a2 u)
  exact d92 a1 a0 v0

theorem c5185 (p : Nat → Prop)
    (d302 : (p 57) → (p 58) → (p 139) → False)
    (d92 : (¬ p 12) → (¬ p 13) → (¬ p 139) → False)
    : (¬ p 13) → (¬ p 12) → (p 57) → (p 58) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 139 := (fun u => d302 a2 a3 u)
  exact d92 a1 a0 v0

theorem c5186 (p : Nat → Prop)
    (d4927 : (¬ p 31) → (¬ p 29) → (p 141) → (p 139) → False)
    (d92 : (¬ p 12) → (¬ p 13) → (¬ p 139) → False)
    : (¬ p 13) → (¬ p 12) → (¬ p 31) → (¬ p 29) → (p 141) → False := by
  intro a0 a1 a2 a3 a4
  have v0 : ¬ p 139 := (fun u => d4927 a2 a3 a4 u)
  exact d92 a1 a0 v0

theorem c5187 (p : Nat → Prop)
    (d4990 : (¬ p 14) → (¬ p 13) → (p 140) → (p 139) → False)
    (d92 : (¬ p 12) → (¬ p 13) → (¬ p 139) → False)
    : (¬ p 13) → (¬ p 12) → (¬ p 14) → (p 140) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 139 := (fun u => d4990 a2 a0 a3 u)
  exact d92 a1 a0 v0

theorem c5188 (p : Nat → Prop)
    (d5172 : (¬ p 27) → (¬ p 29) → (p 139) → (p 133) → False)
    (d92 : (¬ p 12) → (¬ p 13) → (¬ p 139) → False)
    : (¬ p 13) → (¬ p 12) → (¬ p 27) → (¬ p 29) → (p 133) → False := by
  intro a0 a1 a2 a3 a4
  have v0 : ¬ p 139 := (fun u => d5172 a2 a3 u a4)
  exact d92 a1 a0 v0

theorem c5189 (p : Nat → Prop)
    (d5120 : (¬ p 57) → (¬ p 53) → (¬ p 71) → (¬ p 66) → (p 139) → False)
    (d92 : (¬ p 12) → (¬ p 13) → (¬ p 139) → False)
    : (¬ p 13) → (¬ p 12) → (¬ p 57) → (¬ p 53) → (¬ p 71) → (¬ p 66) → False := by
  intro a0 a1 a2 a3 a4 a5
  have v0 : ¬ p 139 := (fun u => d5120 a2 a3 a4 a5 u)
  exact d92 a1 a0 v0

theorem c5190 (p : Nat → Prop)
    (d5160 : (¬ p 26) → (¬ p 28) → (¬ p 41) → (¬ p 44) → (p 139) → False)
    (d92 : (¬ p 12) → (¬ p 13) → (¬ p 139) → False)
    : (¬ p 13) → (¬ p 12) → (¬ p 26) → (¬ p 28) → (¬ p 41) → (¬ p 44) → False := by
  intro a0 a1 a2 a3 a4 a5
  have v0 : ¬ p 139 := (fun u => d5160 a2 a3 a4 a5 u)
  exact d92 a1 a0 v0

theorem c5191 (p : Nat → Prop)
    (d504 : (p 140) → (p 143) → (p 150) → False)
    (d427 : (¬ p 28) → (¬ p 30) → (¬ p 140) → False)
    : (¬ p 30) → (¬ p 28) → (p 143) → (p 150) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 140 := (fun u => d504 u a2 a3)
  exact d427 a1 a0 v0

theorem c5192 (p : Nat → Prop)
    (d455 : (p 140) → (p 141) → (p 148) → False)
    (d427 : (¬ p 28) → (¬ p 30) → (¬ p 140) → False)
    : (¬ p 30) → (¬ p 28) → (p 141) → (p 148) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 140 := (fun u => d455 u a2 a3)
  exact d427 a1 a0 v0

theorem c5193 (p : Nat → Prop)
    (d568 : (p 140) → (p 142) → (p 149) → False)
    (d427 : (¬ p 28) → (¬ p 30) → (¬ p 140) → False)
    : (¬ p 30) → (¬ p 28) → (p 142) → (p 149) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 140 := (fun u => d568 u a2 a3)
  exact d427 a1 a0 v0

theorem c5194 (p : Nat → Prop)
    (d425 : (p 12) → (p 14) → (p 140) → False)
    (d427 : (¬ p 28) → (¬ p 30) → (¬ p 140) → False)
    : (¬ p 30) → (¬ p 28) → (p 12) → (p 14) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 140 := (fun u => d425 a2 a3 u)
  exact d427 a1 a0 v0

theorem c5195 (p : Nat → Prop)
    (d584 : (p 43) → (p 45) → (p 140) → False)
    (d427 : (¬ p 28) → (¬ p 30) → (¬ p 140) → False)
    : (¬ p 30) → (¬ p 28) → (p 43) → (p 45) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 140 := (fun u => d584 a2 a3 u)
  exact d427 a1 a0 v0

theorem c5196 (p : Nat → Prop)
    (d490 : (p 103) → (p 105) → (p 140) → False)
    (d427 : (¬ p 28) → (¬ p 30) → (¬ p 140) → False)
    : (¬ p 30) → (¬ p 28) → (p 105) → (p 103) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 140 := (fun u => d490 a3 a2 u)
  exact d427 a1 a0 v0

theorem c5197 (p : Nat → Prop)
    (d4959 : (¬ p 129) → (¬ p 55) → (p 140) → (p 57) → False)
    (d427 : (¬ p 28) → (¬ p 30) → (¬ p 140) → False)
    : (¬ p 30) → (¬ p 28) → (¬ p 129) → (¬ p 55) → (p 57) → False := by
  intro a0 a1 a2 a3 a4
  have v0 : ¬ p 140 := (fun u => d4959 a2 a3 u a4)
  exact d427 a1 a0 v0

theorem c5198 (p : Nat → Prop)
    (d5055 : (¬ p 105) → (¬ p 88) → (p 140) → (p 93) → False)
    (d427 : (¬ p 28) → (¬ p 30) → (¬ p 140) → False)
    : (¬ p 30) → (¬ p 28) → (¬ p 105) → (¬ p 88) → (p 93) → False := by
  intro a0 a1 a2 a3 a4
  have v0 : ¬ p 140 := (fun u => d5055 a2 a3 u a4)
  exact d427 a1 a0 v0

theorem c5199 (p : Nat → Prop)
    (d5187 : (¬ p 13) → (¬ p 12) → (¬ p 14) → (p 140) → False)
    (d427 : (¬ p 28) → (¬ p 30) → (¬ p 140) → False)
    : (¬ p 30) → (¬ p 28) → (¬ p 13) → (¬ p 12) → (¬ p 14) → False := by
  intro a0 a1 a2 a3 a4
  have v0 : ¬ p 140 := (fun u => d5187 a2 a3 a4 u)
  exact d427 a1 a0 v0

theorem c5200 (p : Nat → Prop)
    (d5140 : (¬ p 72) → (¬ p 67) → (¬ p 40) → (¬ p 43) → (p 140) → False)
    (d427 : (¬ p 28) → (¬ p 30) → (¬ p 140) → False)
    : (¬ p 30) → (¬ p 28) → (¬ p 72) → (¬ p 67) → (¬ p 40) → (¬ p 43) → False := by
  intro a0 a1 a2 a3 a4 a5
  have v0 : ¬ p 140 := (fun u => d5140 a2 a3 a4 a5 u)
  exact d427 a1 a0 v0

theorem c5201 (p : Nat → Prop)
    (d123 : (p 13) → (p 16) → (p 146) → False)
    (d463 : (¬ p 44) → (¬ p 47) → (¬ p 146) → False)
    : (¬ p 44) → (¬ p 47) → (p 16) → (p 13) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 146 := (fun u => d123 a3 a2 u)
  exact d463 a0 a1 v0

theorem c5202 (p : Nat → Prop)
    (d110 : (p 71) → (p 74) → (p 146) → False)
    (d463 : (¬ p 44) → (¬ p 47) → (¬ p 146) → False)
    : (¬ p 44) → (¬ p 47) → (p 74) → (p 71) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 146 := (fun u => d110 a3 a2 u)
  exact d463 a0 a1 v0

theorem c5203 (p : Nat → Prop)
    (d104 : (p 29) → (p 32) → (p 146) → False)
    (d463 : (¬ p 44) → (¬ p 47) → (¬ p 146) → False)
    : (¬ p 44) → (¬ p 47) → (p 32) → (p 29) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 146 := (fun u => d104 a3 a2 u)
  exact d463 a0 a1 v0

theorem c5204 (p : Nat → Prop)
    (d223 : (p 104) → (p 107) → (p 146) → False)
    (d463 : (¬ p 44) → (¬ p 47) → (¬ p 146) → False)
    : (¬ p 44) → (¬ p 47) → (p 107) → (p 104) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 146 := (fun u => d223 a3 a2 u)
  exact d463 a0 a1 v0

theorem c5205 (p : Nat → Prop)
    (d4897 : (¬ p 142) → (¬ p 57) → (p 146) → (p 58) → False)
    (d463 : (¬ p 44) → (¬ p 47) → (¬ p 146) → False)
    : (¬ p 44) → (¬ p 47) → (¬ p 142) → (¬ p 57) → (p 58) → False := by
  intro a0 a1 a2 a3 a4
  have v0 : ¬ p 146 := (fun u => d4897 a2 a3 u a4)
  exact d463 a0 a1 v0

theorem c5206 (p : Nat → Prop)
    (d4985 : (¬ p 14) → (¬ p 13) → (p 149) → (p 146) → False)
    (d463 : (¬ p 44) → (¬ p 47) → (¬ p 146) → False)
    : (¬ p 44) → (¬ p 47) → (¬ p 14) → (¬ p 13) → (p 149) → False := by
  intro a0 a1 a2 a3 a4
  have v0 : ¬ p 146 := (fun u => d4985 a2 a3 a4 u)
  exact d463 a0 a1 v0

theorem c5207 (p : Nat → Prop)
    (d5173 : (¬ p 27) → (¬ p 29) → (p 146) → (p 137) → False)
    (d463 : (¬ p 44) → (¬ p 47) → (¬ p 146) → False)
    : (¬ p 44) → (¬ p 47) → (¬ p 27) → (¬ p 29) → (p 137) → False := by
  intro a0 a1 a2 a3 a4
  have v0 : ¬ p 146 := (fun u => d5173 a2 a3 u a4)
  exact d463 a0 a1 v0

theorem c5208 (p : Nat → Prop)
    (d5181 : (¬ p 13) → (¬ p 12) → (p 146) → (p 142) → False)
    (d463 : (¬ p 44) → (¬ p 47) → (¬ p 146) → False)
    : (¬ p 44) → (¬ p 47) → (¬ p 13) → (¬ p 12) → (p 142) → False := by
  intro a0 a1 a2 a3 a4
  have v0 : ¬ p 146 := (fun u => d5181 a2 a3 u a4)
  exact d463 a0 a1 v0

theorem c5209 (p : Nat → Prop)
    (d5098 : (¬ p 16) → (¬ p 15) → (¬ p 31) → (¬ p 29) → (p 146) → False)
    (d463 : (¬ p 44) → (¬ p 47) → (¬ p 146) → False)
    : (¬ p 44) → (¬ p 47) → (¬ p 16) → (¬ p 15) → (¬ p 31) → (¬ p 29) → False := by
  intro a0 a1 a2 a3 a4 a5
  have v0 : ¬ p 146 := (fun u => d5098 a2 a3 a4 a5 u)
  exact d463 a0 a1 v0

theorem c5210 (p : Nat → Prop)
    (d5128 : (¬ p 107) → (¬ p 99) → (¬ p 71) → (¬ p 66) → (p 146) → False)
    (d463 : (¬ p 44) → (¬ p 47) → (¬ p 146) → False)
    : (¬ p 44) → (¬ p 47) → (¬ p 107) → (¬ p 99) → (¬ p 71) → (¬ p 66) → False := by
  intro a0 a1 a2 a3 a4 a5
  have v0 : ¬ p 146 := (fun u => d5128 a2 a3 a4 a5 u)
  exact d463 a0 a1 v0

theorem c5211 (p : Nat → Prop)
    (d229 : (p 148) → (p 150) → (p 152) → False)
    (d27 : (¬ p 14) → (¬ p 15) → (¬ p 148) → False)
    : (¬ p 14) → (¬ p 15) → (p 152) → (p 150) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 148 := (fun u => d229 u a3 a2)
  exact d27 a0 a1 v0

theorem c5212 (p : Nat → Prop)
    (d315 : (p 135) → (p 136) → (p 148) → False)
    (d27 : (¬ p 14) → (¬ p 15) → (¬ p 148) → False)
    : (¬ p 14) → (¬ p 15) → (p 136) → (p 135) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 148 := (fun u => d315 a3 a2 u)
  exact d27 a0 a1 v0

theorem c5213 (p : Nat → Prop)
    (d109 : (p 30) → (p 31) → (p 148) → False)
    (d27 : (¬ p 14) → (¬ p 15) → (¬ p 148) → False)
    : (¬ p 14) → (¬ p 15) → (p 30) → (p 31) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 148 := (fun u => d109 a2 a3 u)
  exact d27 a0 a1 v0

theorem c5214 (p : Nat → Prop)
    (d152 : (p 72) → (p 73) → (p 148) → False)
    (d27 : (¬ p 14) → (¬ p 15) → (¬ p 148) → False)
    : (¬ p 14) → (¬ p 15) → (p 72) → (p 73) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 148 := (fun u => d152 a2 a3 u)
  exact d27 a0 a1 v0

theorem c5215 (p : Nat → Prop)
    (d4981 : (¬ p 96) → (¬ p 89) → (p 114) → (p 148) → False)
    (d27 : (¬ p 14) → (¬ p 15) → (¬ p 148) → False)
    : (¬ p 14) → (¬ p 15) → (¬ p 96) → (¬ p 89) → (p 114) → False := by
  intro a0 a1 a2 a3 a4
  have v0 : ¬ p 148 := (fun u => d4981 a2 a3 a4 u)
  exact d27 a0 a1 v0

theorem c5216 (p : Nat → Prop)
    (d4998 : (¬ p 43) → (¬ p 141) → (p 45) → (p 148) → False)
    (d27 : (¬ p 14) → (¬ p 15) → (¬ p 148) → False)
    : (¬ p 14) → (¬ p 15) → (¬ p 43) → (¬ p 141) → (p 45) → False := by
  intro a0 a1 a2 a3 a4
  have v0 : ¬ p 148 := (fun u => d4998 a2 a3 a4 u)
  exact d27 a0 a1 v0

theorem c5217 (p : Nat → Prop)
    (d5034 : (¬ p 123) → (¬ p 79) → (p 84) → (p 148) → False)
    (d27 : (¬ p 14) → (¬ p 15) → (¬ p 148) → False)
    : (¬ p 14) → (¬ p 15) → (¬ p 123) → (¬ p 79) → (p 84) → False := by
  intro a0 a1 a2 a3 a4
  have v0 : ¬ p 148 := (fun u => d5034 a2 a3 a4 u)
  exact d27 a0 a1 v0

theorem c5219 (p : Nat → Prop)
    (d5134 : (¬ p 72) → (¬ p 67) → (p 123) → (p 148) → False)
    (d27 : (¬ p 14) → (¬ p 15) → (¬ p 148) → False)
    : (¬ p 14) → (¬ p 15) → (¬ p 72) → (¬ p 67) → (p 123) → False := by
  intro a0 a1 a2 a3 a4
  have v0 : ¬ p 148 := (fun u => d5134 a2 a3 a4 u)
  exact d27 a0 a1 v0

theorem c5220 (p : Nat → Prop)
    (d5192 : (¬ p 30) → (¬ p 28) → (p 141) → (p 148) → False)
    (d27 : (¬ p 14) → (¬ p 15) → (¬ p 148) → False)
    : (¬ p 14) → (¬ p 15) → (¬ p 30) → (¬ p 28) → (p 141) → False := by
  intro a0 a1 a2 a3 a4
  have v0 : ¬ p 148 := (fun u => d5192 a2 a3 a4 u)
  exact d27 a0 a1 v0

theorem c5221 (p : Nat → Prop)
    (d187 : (p 27) → (p 32) → (p 137) → False)
    (d145 : (¬ p 30) → (¬ p 32) → (¬ p 149) → False)
    : (¬ p 30) → (¬ p 149) → (p 137) → (p 27) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 32 := (fun u => d187 a3 u a2)
  exact d145 a0 v0 a1

theorem c5222 (p : Nat → Prop)
    (d344 : (p 1) → (p 16) → (p 32) → False)
    (d145 : (¬ p 30) → (¬ p 32) → (¬ p 149) → False)
    : (¬ p 30) → (¬ p 149) → (p 1) → (p 16) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 32 := (fun u => d344 a2 a3 u)
  exact d145 a0 v0 a1

theorem c5223 (p : Nat → Prop)
    (d303 : (p 22) → (p 32) → (p 97) → False)
    (d145 : (¬ p 30) → (¬ p 32) → (¬ p 149) → False)
    : (¬ p 30) → (¬ p 149) → (p 97) → (p 22) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 32 := (fun u => d303 a3 u a2)
  exact d145 a0 v0 a1

theorem c5224 (p : Nat → Prop)
    (d478 : (p 20) → (p 32) → (p 74) → False)
    (d145 : (¬ p 30) → (¬ p 32) → (¬ p 149) → False)
    : (¬ p 30) → (¬ p 149) → (p 20) → (p 74) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 32 := (fun u => d478 a2 u a3)
  exact d145 a0 v0 a1

theorem c5225 (p : Nat → Prop)
    (d470 : (p 18) → (p 32) → (p 47) → False)
    (d145 : (¬ p 30) → (¬ p 32) → (¬ p 149) → False)
    : (¬ p 30) → (¬ p 149) → (p 18) → (p 47) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 32 := (fun u => d470 a2 u a3)
  exact d145 a0 v0 a1

theorem c5226 (p : Nat → Prop)
    (d524 : (p 23) → (p 32) → (p 107) → False)
    (d145 : (¬ p 30) → (¬ p 32) → (¬ p 149) → False)
    : (¬ p 30) → (¬ p 149) → (p 107) → (p 23) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 32 := (fun u => d524 a3 u a2)
  exact d145 a0 v0 a1

theorem c5227 (p : Nat → Prop)
    (d309 : (p 21) → (p 32) → (p 86) → False)
    (d145 : (¬ p 30) → (¬ p 32) → (¬ p 149) → False)
    : (¬ p 30) → (¬ p 149) → (p 86) → (p 21) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 32 := (fun u => d309 a3 u a2)
  exact d145 a0 v0 a1

theorem c5228 (p : Nat → Prop)
    (d5077 : (¬ p 97) → (¬ p 90) → (p 25) → (p 32) → False)
    (d145 : (¬ p 30) → (¬ p 32) → (¬ p 149) → False)
    : (¬ p 30) → (¬ p 149) → (¬ p 97) → (¬ p 90) → (p 25) → False := by
  intro a0 a1 a2 a3 a4
  have v0 : ¬ p 32 := (fun u => d5077 a2 a3 a4 u)
  exact d145 a0 v0 a1

theorem c5229 (p : Nat → Prop)
    (d5097 : (¬ p 16) → (¬ p 15) → (p 32) → (p 31) → False)
    (d145 : (¬ p 30) → (¬ p 32) → (¬ p 149) → False)
    : (¬ p 30) → (¬ p 149) → (¬ p 16) → (¬ p 15) → (p 31) → False := by
  intro a0 a1 a2 a3 a4
  have v0 : ¬ p 32 := (fun u => d5097 a2 a3 u a4)
  exact d145 a0 v0 a1

theorem c5230 (p : Nat → Prop)
    (d5164 : (¬ p 86) → (¬ p 80) → (p 26) → (p 32) → False)
    (d145 : (¬ p 30) → (¬ p 32) → (¬ p 149) → False)
    : (¬ p 30) → (¬ p 149) → (¬ p 86) → (¬ p 80) → (p 26) → False := by
  intro a0 a1 a2 a3 a4
  have v0 : ¬ p 32 := (fun u => d5164 a2 a3 a4 u)
  exact d145 a0 v0 a1

theorem c5231 (p : Nat → Prop)
    (d5203 : (¬ p 44) → (¬ p 47) → (p 32) → (p 29) → False)
    (d145 : (¬ p 30) → (¬ p 32) → (¬ p 149) → False)
    : (¬ p 30) → (¬ p 149) → (¬ p 44) → (¬ p 47) → (p 29) → False := by
  intro a0 a1 a2 a3 a4
  have v0 : ¬ p 32 := (fun u => d5203 a2 a3 u a4)
  exact d145 a0 v0 a1

theorem c5232 (p : Nat → Prop)
    (d537 : (p 36) → (p 37) → (p 76) → False)
    (d58 : (¬ p 36) → (¬ p 39) → (¬ p 78) → False)
    : (¬ p 78) → (¬ p 39) → (p 37) → (p 76) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 36 := (fun u => d537 u a2 a3)
  exact d58 v0 a1 a0

theorem c5233 (p : Nat → Prop)
    (d283 : (p 2) → (p 5) → (p 36) → False)
    (d58 : (¬ p 36) → (¬ p 39) → (¬ p 78) → False)
    : (¬ p 78) → (¬ p 39) → (p 5) → (p 2) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 36 := (fun u => d283 a3 a2 u)
  exact d58 v0 a1 a0

theorem c5234 (p : Nat → Prop)
    (d156 : (p 18) → (p 21) → (p 36) → False)
    (d58 : (¬ p 36) → (¬ p 39) → (¬ p 78) → False)
    : (¬ p 78) → (¬ p 39) → (p 21) → (p 18) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 36 := (fun u => d156 a3 a2 u)
  exact d58 v0 a1 a0

theorem c5235 (p : Nat → Prop)
    (d360 : (p 36) → (p 41) → (p 80) → False)
    (d58 : (¬ p 36) → (¬ p 39) → (¬ p 78) → False)
    : (¬ p 78) → (¬ p 39) → (p 80) → (p 41) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 36 := (fun u => d360 u a3 a2)
  exact d58 v0 a1 a0

theorem c5236 (p : Nat → Prop)
    (d76 : (p 34) → (p 36) → (p 50) → False)
    (d58 : (¬ p 36) → (¬ p 39) → (¬ p 78) → False)
    : (¬ p 78) → (¬ p 39) → (p 50) → (p 34) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 36 := (fun u => d76 a3 u a2)
  exact d58 v0 a1 a0

theorem c5237 (p : Nat → Prop)
    (d280 : (p 36) → (p 45) → (p 84) → False)
    (d58 : (¬ p 36) → (¬ p 39) → (¬ p 78) → False)
    : (¬ p 78) → (¬ p 39) → (p 45) → (p 84) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 36 := (fun u => d280 u a2 a3)
  exact d58 v0 a1 a0

theorem c5238 (p : Nat → Prop)
    (d190 : (p 36) → (p 42) → (p 81) → False)
    (d58 : (¬ p 36) → (¬ p 39) → (¬ p 78) → False)
    : (¬ p 78) → (¬ p 39) → (p 81) → (p 42) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 36 := (fun u => d190 u a3 a2)
  exact d58 v0 a1 a0

theorem c5239 (p : Nat → Prop)
    (d69 : (p 36) → (p 47) → (p 86) → False)
    (d58 : (¬ p 36) → (¬ p 39) → (¬ p 78) → False)
    : (¬ p 78) → (¬ p 39) → (p 47) → (p 86) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 36 := (fun u => d69 u a2 a3)
  exact d58 v0 a1 a0

theorem c5240 (p : Nat → Prop)
    (d4915 : (¬ p 104) → (¬ p 77) → (p 44) → (p 36) → False)
    (d58 : (¬ p 36) → (¬ p 39) → (¬ p 78) → False)
    : (¬ p 78) → (¬ p 39) → (¬ p 104) → (¬ p 77) → (p 44) → False := by
  intro a0 a1 a2 a3 a4
  have v0 : ¬ p 36 := (fun u => d4915 a2 a3 a4 u)
  exact d58 v0 a1 a0

theorem c5241 (p : Nat → Prop)
    (d5002 : (¬ p 150) → (¬ p 45) → (p 87) → (p 36) → False)
    (d58 : (¬ p 36) → (¬ p 39) → (¬ p 78) → False)
    : (¬ p 78) → (¬ p 39) → (¬ p 150) → (¬ p 45) → (p 87) → False := by
  intro a0 a1 a2 a3 a4
  have v0 : ¬ p 36 := (fun u => d5002 a2 a3 a4 u)
  exact d58 v0 a1 a0

theorem c5242 (p : Nat → Prop)
    (d5025 : (¬ p 93) → (¬ p 76) → (p 43) → (p 36) → False)
    (d58 : (¬ p 36) → (¬ p 39) → (¬ p 78) → False)
    : (¬ p 78) → (¬ p 39) → (¬ p 93) → (¬ p 76) → (p 43) → False := by
  intro a0 a1 a2 a3 a4
  have v0 : ¬ p 36 := (fun u => d5025 a2 a3 a4 u)
  exact d58 v0 a1 a0

theorem c5243 (p : Nat → Prop)
    (d601 : (p 69) → (p 73) → (p 136) → False)
    (d138 : (¬ p 68) → (¬ p 73) → (¬ p 130) → False)
    : (¬ p 130) → (¬ p 68) → (p 136) → (p 69) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 73 := (fun u => d601 a3 u a2)
  exact d138 a1 v0 a0

theorem c5244 (p : Nat → Prop)
    (d339 : (p 67) → (p 73) → (p 123) → False)
    (d138 : (¬ p 68) → (¬ p 73) → (¬ p 130) → False)
    : (¬ p 130) → (¬ p 68) → (p 67) → (p 123) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 73 := (fun u => d339 a2 u a3)
  exact d138 a1 v0 a0

theorem c5245 (p : Nat → Prop)
    (d467 : (p 64) → (p 73) → (p 96) → False)
    (d138 : (¬ p 68) → (¬ p 73) → (¬ p 130) → False)
    : (¬ p 130) → (¬ p 68) → (p 64) → (p 96) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 73 := (fun u => d467 a2 u a3)
  exact d138 a1 v0 a0

theorem c5246 (p : Nat → Prop)
    (d574 : (p 4) → (p 15) → (p 73) → False)
    (d138 : (¬ p 68) → (¬ p 73) → (¬ p 130) → False)
    : (¬ p 130) → (¬ p 68) → (p 15) → (p 4) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 73 := (fun u => d574 a3 a2 u)
  exact d138 a1 v0 a0

theorem c5247 (p : Nat → Prop)
    (d397 : (p 20) → (p 31) → (p 73) → False)
    (d138 : (¬ p 68) → (¬ p 73) → (¬ p 130) → False)
    : (¬ p 130) → (¬ p 68) → (p 20) → (p 31) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 73 := (fun u => d397 a2 a3 u)
  exact d138 a1 v0 a0

theorem c5248 (p : Nat → Prop)
    (d4928 : (¬ p 31) → (¬ p 29) → (p 73) → (p 71) → False)
    (d138 : (¬ p 68) → (¬ p 73) → (¬ p 130) → False)
    : (¬ p 130) → (¬ p 68) → (¬ p 31) → (¬ p 29) → (p 71) → False := by
  intro a0 a1 a2 a3 a4
  have v0 : ¬ p 73 := (fun u => d4928 a2 a3 u a4)
  exact d138 a1 v0 a0

theorem c5249 (p : Nat → Prop)
    (d4964 : (¬ p 136) → (¬ p 56) → (p 73) → (p 49) → False)
    (d138 : (¬ p 68) → (¬ p 73) → (¬ p 130) → False)
    : (¬ p 130) → (¬ p 68) → (¬ p 136) → (¬ p 56) → (p 49) → False := by
  intro a0 a1 a2 a3 a4
  have v0 : ¬ p 73 := (fun u => d4964 a2 a3 u a4)
  exact d138 a1 v0 a0

theorem c5250 (p : Nat → Prop)
    (d5018 : (¬ p 143) → (¬ p 70) → (p 152) → (p 73) → False)
    (d138 : (¬ p 68) → (¬ p 73) → (¬ p 130) → False)
    : (¬ p 130) → (¬ p 68) → (¬ p 143) → (¬ p 70) → (p 152) → False := by
  intro a0 a1 a2 a3 a4
  have v0 : ¬ p 73 := (fun u => d5018 a2 a3 a4 u)
  exact d138 a1 v0 a0

theorem c5251 (p : Nat → Prop)
    (d5031 : (¬ p 123) → (¬ p 79) → (p 73) → (p 63) → False)
    (d138 : (¬ p 68) → (¬ p 73) → (¬ p 130) → False)
    : (¬ p 130) → (¬ p 68) → (¬ p 123) → (¬ p 79) → (p 63) → False := by
  intro a0 a1 a2 a3 a4
  have v0 : ¬ p 73 := (fun u => d5031 a2 a3 u a4)
  exact d138 a1 v0 a0

theorem c5252 (p : Nat → Prop)
    (d5096 : (¬ p 16) → (¬ p 15) → (p 73) → (p 74) → False)
    (d138 : (¬ p 68) → (¬ p 73) → (¬ p 130) → False)
    : (¬ p 130) → (¬ p 68) → (¬ p 16) → (¬ p 15) → (p 74) → False := by
  intro a0 a1 a2 a3 a4
  have v0 : ¬ p 73 := (fun u => d5096 a2 a3 u a4)
  exact d138 a1 v0 a0

theorem c5253 (p : Nat → Prop)
    (d5214 : (¬ p 14) → (¬ p 15) → (p 72) → (p 73) → False)
    (d138 : (¬ p 68) → (¬ p 73) → (¬ p 130) → False)
    : (¬ p 130) → (¬ p 68) → (¬ p 14) → (¬ p 15) → (p 72) → False := by
  intro a0 a1 a2 a3 a4
  have v0 : ¬ p 73 := (fun u => d5214 a2 a3 a4 u)
  exact d138 a1 v0 a0

theorem c5254 (p : Nat → Prop)
    (d326 : (p 5) → (p 14) → (p 84) → False)
    (d125 : (¬ p 78) → (¬ p 84) → (¬ p 114) → False)
    : (¬ p 114) → (¬ p 78) → (p 5) → (p 14) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 84 := (fun u => d326 a2 a3 u)
  exact d125 a1 v0 a0

theorem c5255 (p : Nat → Prop)
    (d379 : (p 80) → (p 84) → (p 129) → False)
    (d125 : (¬ p 78) → (¬ p 84) → (¬ p 114) → False)
    : (¬ p 114) → (¬ p 78) → (p 129) → (p 80) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 84 := (fun u => d379 a3 u a2)
  exact d125 a1 v0 a0

theorem c5256 (p : Nat → Prop)
    (d419 : (p 84) → (p 87) → (p 150) → False)
    (d125 : (¬ p 78) → (¬ p 84) → (¬ p 114) → False)
    : (¬ p 114) → (¬ p 78) → (p 150) → (p 87) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 84 := (fun u => d419 u a3 a2)
  exact d125 a1 v0 a0

theorem c5257 (p : Nat → Prop)
    (d161 : (p 63) → (p 72) → (p 84) → False)
    (d125 : (¬ p 78) → (¬ p 84) → (¬ p 114) → False)
    : (¬ p 114) → (¬ p 78) → (p 72) → (p 63) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 84 := (fun u => d161 a3 a2 u)
  exact d125 a1 v0 a0

theorem c5258 (p : Nat → Prop)
    (d89 : (p 21) → (p 30) → (p 84) → False)
    (d125 : (¬ p 78) → (¬ p 84) → (¬ p 114) → False)
    : (¬ p 114) → (¬ p 78) → (p 30) → (p 21) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 84 := (fun u => d89 a3 a2 u)
  exact d125 a1 v0 a0

theorem c5259 (p : Nat → Prop)
    (d347 : (p 84) → (p 86) → (p 149) → False)
    (d125 : (¬ p 78) → (¬ p 84) → (¬ p 114) → False)
    : (¬ p 114) → (¬ p 78) → (p 86) → (p 149) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 84 := (fun u => d347 u a2 a3)
  exact d125 a1 v0 a0

theorem c5260 (p : Nat → Prop)
    (d405 : (p 81) → (p 84) → (p 135) → False)
    (d125 : (¬ p 78) → (¬ p 84) → (¬ p 114) → False)
    : (¬ p 114) → (¬ p 78) → (p 81) → (p 135) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 84 := (fun u => d405 a2 u a3)
  exact d125 a1 v0 a0

theorem c5261 (p : Nat → Prop)
    (d4958 : (¬ p 129) → (¬ p 55) → (p 50) → (p 84) → False)
    (d125 : (¬ p 78) → (¬ p 84) → (¬ p 114) → False)
    : (¬ p 114) → (¬ p 78) → (¬ p 129) → (¬ p 55) → (p 50) → False := by
  intro a0 a1 a2 a3 a4
  have v0 : ¬ p 84 := (fun u => d4958 a2 a3 a4 u)
  exact d125 a1 v0 a0

theorem c5262 (p : Nat → Prop)
    (d5132 : (¬ p 72) → (¬ p 67) → (p 79) → (p 84) → False)
    (d125 : (¬ p 78) → (¬ p 84) → (¬ p 114) → False)
    : (¬ p 114) → (¬ p 78) → (¬ p 72) → (¬ p 67) → (p 79) → False := by
  intro a0 a1 a2 a3 a4
  have v0 : ¬ p 84 := (fun u => d5132 a2 a3 a4 u)
  exact d125 a1 v0 a0

theorem c5263 (p : Nat → Prop)
    (d5237 : (¬ p 78) → (¬ p 39) → (p 45) → (p 84) → False)
    (d125 : (¬ p 78) → (¬ p 84) → (¬ p 114) → False)
    : (¬ p 114) → (¬ p 78) → (¬ p 39) → (p 45) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 84 := (fun u => d5237 a1 a2 a3 u)
  exact d125 a1 v0 a0

theorem c5264 (p : Nat → Prop)
    (d5217 : (¬ p 14) → (¬ p 15) → (¬ p 123) → (¬ p 79) → (p 84) → False)
    (d125 : (¬ p 78) → (¬ p 84) → (¬ p 114) → False)
    : (¬ p 114) → (¬ p 78) → (¬ p 14) → (¬ p 15) → (¬ p 123) → (¬ p 79) → False := by
  intro a0 a1 a2 a3 a4 a5
  have v0 : ¬ p 84 := (fun u => d5217 a2 a3 a4 a5 u)
  exact d125 a1 v0 a0

theorem c5265 (p : Nat → Prop)
    (d56 : (p 76) → (p 87) → (p 98) → False)
    (d136 : (¬ p 91) → (¬ p 98) → (¬ p 132) → False)
    : (¬ p 132) → (¬ p 91) → (p 87) → (p 76) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 98 := (fun u => d56 a3 a2 u)
  exact d136 a1 v0 a0

theorem c5266 (p : Nat → Prop)
    (d121 : (p 93) → (p 98) → (p 143) → False)
    (d136 : (¬ p 91) → (¬ p 98) → (¬ p 132) → False)
    : (¬ p 132) → (¬ p 91) → (p 93) → (p 143) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 98 := (fun u => d121 a2 u a3)
  exact d136 a1 v0 a0

theorem c5267 (p : Nat → Prop)
    (d448 : (p 88) → (p 98) → (p 108) → False)
    (d136 : (¬ p 91) → (¬ p 98) → (¬ p 132) → False)
    : (¬ p 132) → (¬ p 91) → (p 108) → (p 88) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 98 := (fun u => d448 a3 u a2)
  exact d136 a1 v0 a0

theorem c5268 (p : Nat → Prop)
    (d591 : (p 22) → (p 33) → (p 98) → False)
    (d136 : (¬ p 91) → (¬ p 98) → (¬ p 132) → False)
    : (¬ p 132) → (¬ p 91) → (p 22) → (p 33) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 98 := (fun u => d591 a2 a3 u)
  exact d136 a1 v0 a0

theorem c5269 (p : Nat → Prop)
    (d362 : (p 96) → (p 98) → (p 152) → False)
    (d136 : (¬ p 91) → (¬ p 98) → (¬ p 132) → False)
    : (¬ p 132) → (¬ p 91) → (p 152) → (p 96) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 98 := (fun u => d362 a3 u a2)
  exact d136 a1 v0 a0

theorem c5270 (p : Nat → Prop)
    (d4905 : (¬ p 147) → (¬ p 58) → (p 98) → (p 51) → False)
    (d136 : (¬ p 91) → (¬ p 98) → (¬ p 132) → False)
    : (¬ p 132) → (¬ p 91) → (¬ p 147) → (¬ p 58) → (p 51) → False := by
  intro a0 a1 a2 a3 a4
  have v0 : ¬ p 98 := (fun u => d4905 a2 a3 u a4)
  exact d136 a1 v0 a0

theorem c5271 (p : Nat → Prop)
    (d5007 : (¬ p 150) → (¬ p 45) → (p 98) → (p 37) → False)
    (d136 : (¬ p 91) → (¬ p 98) → (¬ p 132) → False)
    : (¬ p 132) → (¬ p 91) → (¬ p 150) → (¬ p 45) → (p 37) → False := by
  intro a0 a1 a2 a3 a4
  have v0 : ¬ p 98 := (fun u => d5007 a2 a3 u a4)
  exact d136 a1 v0 a0

theorem c5272 (p : Nat → Prop)
    (d5015 : (¬ p 143) → (¬ p 70) → (p 64) → (p 98) → False)
    (d136 : (¬ p 91) → (¬ p 98) → (¬ p 132) → False)
    : (¬ p 132) → (¬ p 91) → (¬ p 143) → (¬ p 70) → (p 64) → False := by
  intro a0 a1 a2 a3 a4
  have v0 : ¬ p 98 := (fun u => d5015 a2 a3 a4 u)
  exact d136 a1 v0 a0

theorem c5273 (p : Nat → Prop)
    (d5046 : (¬ p 64) → (¬ p 69) → (p 98) → (p 138) → False)
    (d136 : (¬ p 91) → (¬ p 98) → (¬ p 132) → False)
    : (¬ p 132) → (¬ p 91) → (¬ p 64) → (¬ p 69) → (p 138) → False := by
  intro a0 a1 a2 a3 a4
  have v0 : ¬ p 98 := (fun u => d5046 a2 a3 u a4)
  exact d136 a1 v0 a0

theorem c5274 (p : Nat → Prop)
    (d5054 : (¬ p 105) → (¬ p 88) → (p 98) → (p 150) → False)
    (d136 : (¬ p 91) → (¬ p 98) → (¬ p 132) → False)
    : (¬ p 132) → (¬ p 91) → (¬ p 105) → (¬ p 88) → (p 150) → False := by
  intro a0 a1 a2 a3 a4
  have v0 : ¬ p 98 := (fun u => d5054 a2 a3 u a4)
  exact d136 a1 v0 a0

theorem c5275 (p : Nat → Prop)
    (d5144 : (¬ p 100) → (¬ p 108) → (p 98) → (p 90) → False)
    (d136 : (¬ p 91) → (¬ p 98) → (¬ p 132) → False)
    : (¬ p 132) → (¬ p 91) → (¬ p 100) → (¬ p 108) → (p 90) → False := by
  intro a0 a1 a2 a3 a4
  have v0 : ¬ p 98 := (fun u => d5144 a2 a3 u a4)
  exact d136 a1 v0 a0

theorem c5276 (p : Nat → Prop)
    (d221 : (p 65) → (p 68) → (p 101) → False)
    (d23 : (¬ p 38) → (¬ p 41) → (¬ p 101) → False)
    : (¬ p 41) → (¬ p 38) → (p 65) → (p 68) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 101 := (fun u => d221 a2 a3 u)
  exact d23 a1 a0 v0

theorem c5277 (p : Nat → Prop)
    (d484 : (p 88) → (p 91) → (p 101) → False)
    (d23 : (¬ p 38) → (¬ p 41) → (¬ p 101) → False)
    : (¬ p 41) → (¬ p 38) → (p 91) → (p 88) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 101 := (fun u => d484 a3 a2 u)
  exact d23 a1 a0 v0

theorem c5278 (p : Nat → Prop)
    (d279 : (p 7) → (p 10) → (p 101) → False)
    (d23 : (¬ p 38) → (¬ p 41) → (¬ p 101) → False)
    : (¬ p 41) → (¬ p 38) → (p 7) → (p 10) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 101 := (fun u => d279 a2 a3 u)
  exact d23 a1 a0 v0

theorem c5279 (p : Nat → Prop)
    (d205 : (p 101) → (p 102) → (p 126) → False)
    (d23 : (¬ p 38) → (¬ p 41) → (¬ p 101) → False)
    : (¬ p 41) → (¬ p 38) → (p 102) → (p 126) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 101 := (fun u => d205 u a2 a3)
  exact d23 a1 a0 v0

theorem c5280 (p : Nat → Prop)
    (d544 : (p 23) → (p 26) → (p 101) → False)
    (d23 : (¬ p 38) → (¬ p 41) → (¬ p 101) → False)
    : (¬ p 41) → (¬ p 38) → (p 26) → (p 23) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 101 := (fun u => d544 a3 a2 u)
  exact d23 a1 a0 v0

theorem c5281 (p : Nat → Prop)
    (d571 : (p 100) → (p 101) → (p 118) → False)
    (d23 : (¬ p 38) → (¬ p 41) → (¬ p 101) → False)
    : (¬ p 41) → (¬ p 38) → (p 100) → (p 118) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 101 := (fun u => d571 a2 u a3)
  exact d23 a1 a0 v0

theorem c5282 (p : Nat → Prop)
    (d204 : (p 101) → (p 108) → (p 132) → False)
    (d23 : (¬ p 38) → (¬ p 41) → (¬ p 101) → False)
    : (¬ p 41) → (¬ p 38) → (p 108) → (p 132) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 101 := (fun u => d204 u a2 a3)
  exact d23 a1 a0 v0

theorem c5283 (p : Nat → Prop)
    (d4947 : (¬ p 102) → (¬ p 56) → (p 55) → (p 101) → False)
    (d23 : (¬ p 38) → (¬ p 41) → (¬ p 101) → False)
    : (¬ p 41) → (¬ p 38) → (¬ p 102) → (¬ p 56) → (p 55) → False := by
  intro a0 a1 a2 a3 a4
  have v0 : ¬ p 101 := (fun u => d4947 a2 a3 a4 u)
  exact d23 a1 a0 v0

theorem c5284 (p : Nat → Prop)
    (d5107 : (¬ p 24) → (¬ p 26) → (p 101) → (p 99) → False)
    (d23 : (¬ p 38) → (¬ p 41) → (¬ p 101) → False)
    : (¬ p 41) → (¬ p 38) → (¬ p 24) → (¬ p 26) → (p 99) → False := by
  intro a0 a1 a2 a3 a4
  have v0 : ¬ p 101 := (fun u => d5107 a2 a3 u a4)
  exact d23 a1 a0 v0

theorem c5285 (p : Nat → Prop)
    (d5159 : (¬ p 26) → (¬ p 28) → (p 103) → (p 101) → False)
    (d23 : (¬ p 38) → (¬ p 41) → (¬ p 101) → False)
    : (¬ p 41) → (¬ p 38) → (¬ p 26) → (¬ p 28) → (p 103) → False := by
  intro a0 a1 a2 a3 a4
  have v0 : ¬ p 101 := (fun u => d5159 a2 a3 a4 u)
  exact d23 a1 a0 v0

theorem c5286 (p : Nat → Prop)
    (d5166 : (¬ p 86) → (¬ p 80) → (p 107) → (p 101) → False)
    (d23 : (¬ p 38) → (¬ p 41) → (¬ p 101) → False)
    : (¬ p 41) → (¬ p 38) → (¬ p 86) → (¬ p 80) → (p 107) → False := by
  intro a0 a1 a2 a3 a4
  have v0 : ¬ p 101 := (fun u => d5166 a2 a3 a4 u)
  exact d23 a1 a0 v0

theorem c5287 (p : Nat → Prop)
    (d570 : (p 102) → (p 103) → (p 133) → False)
    (d154 : (¬ p 65) → (¬ p 70) → (¬ p 103) → False)
    : (¬ p 70) → (¬ p 65) → (p 102) → (p 133) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 103 := (fun u => d570 a2 u a3)
  exact d154 a1 a0 v0

theorem c5288 (p : Nat → Prop)
    (d146 : (p 23) → (p 28) → (p 103) → False)
    (d154 : (¬ p 65) → (¬ p 70) → (¬ p 103) → False)
    : (¬ p 70) → (¬ p 65) → (p 28) → (p 23) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 103 := (fun u => d146 a3 a2 u)
  exact d154 a1 a0 v0

theorem c5289 (p : Nat → Prop)
    (d390 : (p 103) → (p 108) → (p 143) → False)
    (d154 : (¬ p 65) → (¬ p 70) → (¬ p 103) → False)
    : (¬ p 70) → (¬ p 65) → (p 143) → (p 108) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 103 := (fun u => d390 u a3 a2)
  exact d154 a1 a0 v0

theorem c5290 (p : Nat → Prop)
    (d406 : (p 103) → (p 107) → (p 142) → False)
    (d154 : (¬ p 65) → (¬ p 70) → (¬ p 103) → False)
    : (¬ p 70) → (¬ p 65) → (p 107) → (p 142) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 103 := (fun u => d406 u a2 a3)
  exact d154 a1 a0 v0

theorem c5291 (p : Nat → Prop)
    (d434 : (p 7) → (p 12) → (p 103) → False)
    (d154 : (¬ p 65) → (¬ p 70) → (¬ p 103) → False)
    : (¬ p 70) → (¬ p 65) → (p 12) → (p 7) → False := by
  intro a0 a1 a2 a3
  have v0 : ¬ p 103 := (fun u => d434 a3 a2 u)
  exact d154 a1 a0 v0

end JSP000746.RUP
