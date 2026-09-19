import Std
namespace DescendingWaves

def Descending : List Nat → Prop
  | a :: b :: c :: xs => a < b ∧ c + a ≤ b + b ∧ Descending (b :: c :: xs)
  | [a,b] => a < b
  | _ => True

def Monochromatic (color : Nat → Bool) (xs : List Nat) : Prop :=
  ∃ t, ∀ x ∈ xs, color x = t

def InInterval (n : Nat) (xs : List Nat) : Prop :=
  ∀ x ∈ xs, 1 ≤ x ∧ x ≤ n

structure Certificate (n bound : Nat) (color : Nat → Bool) (rank : Nat → Nat → Nat) : Prop where
  lower : ∀ a b, 1 ≤ a → a < b → b ≤ n → color a = color b → 2 ≤ rank a b
  upper : ∀ a b, 1 ≤ a → a < b → b ≤ n → color a = color b → rank a b ≤ bound
  step : ∀ a b c, 1 ≤ a → a < b → b < c → c ≤ n →
    c + a ≤ b + b → color a = color b → color b = color c →
    rank b c + 1 ≤ rank a b

theorem rank_bounds_length {n bound : Nat} {color : Nat → Bool} {rank : Nat → Nat → Nat}
    (cert : Certificate n bound color rank) (a b : Nat) (xs : List Nat)
    (hw : Descending (a::b::xs)) (hi : InInterval n (a::b::xs))
    (hm : Monochromatic color (a::b::xs)) :
    (a::b::xs).length ≤ rank a b := by
  induction xs generalizing a b with
  | nil =>
    obtain ⟨t, ht⟩ := hm
    have ha := hi a (by simp)
    have hb := hi b (by simp)
    have hab : color a = color b := (ht a (by simp)).trans (ht b (by simp)).symm
    exact cert.lower a b ha.1 hw hb.2 hab
  | cons c xs ih =>
    obtain ⟨hab, hgap, htail⟩ := hw
    have hbc : b < c := by
      cases xs with
      | nil => exact htail
      | cons d ys => exact htail.1
    have hi' : InInterval n (b::c::xs) := by
      intro x hx
      exact hi x (List.mem_cons_of_mem a hx)
    obtain ⟨t, ht⟩ := hm
    have hm' : Monochromatic color (b::c::xs) := by
      refine ⟨t, ?_⟩
      intro x hx
      exact ht x (List.mem_cons_of_mem a hx)
    have hlen := ih b c htail hi' hm'
    have ha := hi a (by simp)
    have hc := hi c (by simp)
    have habc : color a = color b := (ht a (by simp)).trans (ht b (by simp)).symm
    have hbcc : color b = color c := (ht b (by simp)).trans (ht c (by simp)).symm
    have hs := cert.step a b c ha.1 hab hbc hc.2 hgap habc hbcc
    simp only [List.length_cons] at *
    omega

theorem certificate_bounds_all {n bound : Nat} (hbound : 1 ≤ bound)
    {color : Nat → Bool} {rank : Nat → Nat → Nat}
    (cert : Certificate n bound color rank) (xs : List Nat)
    (hw : Descending xs) (hi : InInterval n xs) (hm : Monochromatic color xs) :
    xs.length ≤ bound := by
  cases xs with
  | nil => simp
  | cons a xs =>
    cases xs with
    | nil => simpa using hbound
    | cons b xs =>
      have hl := rank_bounds_length cert a b xs hw hi hm
      have hab : a < b := by
        cases xs with
        | nil => exact hw
        | cons c ys => exact hw.1
      obtain ⟨t,ht⟩ := hm
      have ha := hi a (by simp)
      have hb := hi b (by simp)
      have hc : color a = color b := (ht a (by simp)).trans (ht b (by simp)).symm
      exact Nat.le_trans hl (cert.upper a b ha.1 hab hb.2 hc)


set_option maxRecDepth 100000
set_option maxHeartbeats 0
def witnessColor (a : Nat) : Bool := (if a < 67 then (if a < 33 then (if a < 16 then (if a < 8 then false else (if a < 12 then false else (if a < 14 then (if a < 13 then true else false) else false))) else (if a < 24 then true else (if a < 28 then (if a < 26 then true else false) else false))) else (if a < 50 then (if a < 41 then (if a < 37 then (if a < 35 then false else true) else true) else (if a < 45 then (if a < 43 then true else (if a < 44 then true else false)) else false)) else (if a < 58 then (if a < 54 then (if a < 52 then false else (if a < 53 then false else true)) else true) else (if a < 62 then true else false)))) else (if a < 100 then (if a < 83 then (if a < 75 then (if a < 71 then (if a < 69 then false else (if a < 70 then false else true)) else true) else (if a < 79 then (if a < 77 then true else (if a < 78 then true else false)) else false)) else (if a < 91 then (if a < 87 then (if a < 85 then false else true) else true) else (if a < 95 then (if a < 93 then (if a < 92 then true else false) else false) else (if a < 97 then false else (if a < 98 then false else true))))) else (if a < 117 then (if a < 108 then (if a < 104 then true else false) else (if a < 112 then (if a < 110 then (if a < 109 then false else true) else true) else (if a < 114 then true else false))) else (if a < 125 then (if a < 121 then (if a < 119 then (if a < 118 then false else true) else true) else (if a < 123 then (if a < 122 then true else false) else false)) else (if a < 129 then (if a < 127 then true else (if a < 128 then true else false)) else (if a < 131 then (if a < 130 then false else true) else (if a < 132 then true else (if a < 133 then false else true))))))))
def witnessRank (a b : Nat) : Nat := (if b < 67 then (if b < 33 then (if b < 16 then (if b < 8 then (if b < 4 then (if b < 2 then (if b < 1 then 2 else (if a < 67 then (if a < 33 then (if a < 16 then (if a < 8 then (if a < 4 then (if a < 2 then (if a < 1 then 12 else 2) else 2) else 2) else 2) else 2) else 2) else 2)) else (if b < 3 then (if a < 67 then (if a < 33 then (if a < 16 then (if a < 8 then (if a < 4 then (if a < 2 then 11 else 2) else 2) else 2) else 2) else 2) else 2) else (if a < 67 then (if a < 33 then (if a < 16 then (if a < 8 then (if a < 4 then (if a < 2 then 10 else (if a < 3 then 10 else 2)) else 2) else 2) else 2) else 2) else 2))) else (if b < 6 then (if b < 5 then (if a < 67 then (if a < 33 then (if a < 16 then (if a < 8 then (if a < 4 then 9 else 2) else 2) else 2) else 2) else 2) else (if a < 67 then (if a < 33 then (if a < 16 then (if a < 8 then (if a < 4 then 8 else (if a < 6 then (if a < 5 then 8 else 2) else 2)) else 2) else 2) else 2) else 2)) else (if b < 7 then (if a < 67 then (if a < 33 then (if a < 16 then (if a < 8 then (if a < 4 then 7 else (if a < 6 then 7 else 2)) else 2) else 2) else 2) else 2) else (if a < 67 then (if a < 33 then (if a < 16 then (if a < 8 then (if a < 4 then 7 else (if a < 6 then 7 else (if a < 7 then 6 else 2))) else 2) else 2) else 2) else 2)))) else (if b < 12 then (if b < 10 then (if b < 9 then (if a < 67 then (if a < 33 then (if a < 16 then (if a < 8 then (if a < 4 then 6 else (if a < 6 then 6 else 5)) else 2) else 2) else 2) else 2) else (if a < 67 then (if a < 33 then (if a < 16 then (if a < 8 then 6 else (if a < 12 then (if a < 10 then (if a < 9 then 4 else 2) else 2) else 2)) else 2) else 2) else 2)) else (if b < 11 then (if a < 67 then (if a < 33 then (if a < 16 then (if a < 8 then 5 else (if a < 12 then (if a < 10 then 3 else 2) else 2)) else 2) else 2) else 2) else (if a < 67 then (if a < 33 then (if a < 16 then (if a < 8 then 5 else (if a < 12 then (if a < 10 then 5 else 2) else 2)) else 2) else 2) else 2))) else (if b < 14 then (if b < 13 then (if a < 67 then (if a < 33 then (if a < 16 then (if a < 8 then 12 else (if a < 12 then (if a < 10 then (if a < 9 then 12 else 2) else 2) else 2)) else 2) else 2) else 2) else (if a < 67 then (if a < 33 then (if a < 16 then (if a < 8 then (if a < 4 then (if a < 2 then (if a < 1 then 11 else 4) else 4) else 4) else (if a < 12 then 4 else (if a < 14 then (if a < 13 then 4 else 2) else 2))) else 2) else 2) else 2)) else (if b < 15 then (if a < 67 then (if a < 33 then (if a < 16 then (if a < 8 then (if a < 4 then (if a < 2 then 11 else (if a < 3 then 11 else 3)) else 3) else (if a < 12 then 3 else (if a < 14 then 3 else 2))) else 2) else 2) else 2) else (if a < 67 then (if a < 33 then (if a < 16 then (if a < 8 then (if a < 4 then (if a < 2 then (if a < 1 then 12 else 11) else 11) else (if a < 6 then (if a < 5 then 11 else 2) else 2)) else 2) else 2) else 2) else 2))))) else (if b < 24 then (if b < 20 then (if b < 18 then (if b < 17 then (if a < 67 then (if a < 33 then (if a < 16 then 11 else 2) else 2) else 2) else (if a < 67 then (if a < 33 then (if a < 16 then 10 else (if a < 24 then (if a < 20 then (if a < 18 then (if a < 17 then 10 else 2) else 2) else 2) else 2)) else 2) else 2)) else (if b < 19 then (if a < 67 then (if a < 33 then (if a < 16 then (if a < 8 then (if a < 4 then (if a < 2 then (if a < 1 then 12 else 11) else 9) else 9) else 9) else (if a < 24 then (if a < 20 then (if a < 18 then 9 else 2) else 2) else 2)) else 2) else 2) else (if a < 67 then (if a < 33 then (if a < 16 then (if a < 8 then (if a < 4 then (if a < 2 then 12 else (if a < 3 then 12 else 11)) else 8) else 8) else (if a < 24 then (if a < 20 then (if a < 18 then 8 else (if a < 19 then 8 else 2)) else 2) else 2)) else 2) else 2))) else (if b < 22 then (if b < 21 then (if a < 67 then (if a < 33 then (if a < 16 then (if a < 8 then (if a < 4 then 12 else (if a < 6 then 11 else 7)) else 7) else (if a < 24 then (if a < 20 then 7 else 2) else 2)) else 2) else 2) else (if a < 67 then (if a < 33 then (if a < 16 then (if a < 8 then (if a < 4 then 12 else (if a < 6 then 12 else 11)) else 6) else (if a < 24 then (if a < 20 then 6 else (if a < 22 then (if a < 21 then 6 else 2) else 2)) else 2)) else 2) else 2)) else (if b < 23 then (if a < 67 then (if a < 33 then (if a < 16 then (if a < 8 then (if a < 4 then 12 else (if a < 6 then 12 else (if a < 7 then 12 else 11))) else (if a < 12 then (if a < 10 then 11 else 5) else 5)) else (if a < 24 then (if a < 20 then 5 else (if a < 22 then 5 else 2)) else 2)) else 2) else 2) else (if a < 67 then (if a < 33 then (if a < 16 then (if a < 8 then 12 else (if a < 12 then (if a < 10 then (if a < 9 then 12 else 11) else 11) else 4)) else (if a < 24 then (if a < 20 then 4 else (if a < 22 then 4 else (if a < 23 then 4 else 2))) else 2)) else 2) else 2)))) else (if b < 28 then (if b < 26 then (if b < 25 then (if a < 67 then (if a < 33 then (if a < 16 then (if a < 8 then 12 else (if a < 12 then (if a < 10 then 12 else 11) else (if a < 14 then 11 else 3))) else (if a < 24 then 3 else 2)) else 2) else 2) else (if a < 67 then (if a < 33 then (if a < 16 then (if a < 8 then 12 else (if a < 12 then 12 else 11)) else 2) else 2) else 2)) else (if b < 27 then (if a < 67 then (if a < 33 then (if a < 16 then (if a < 8 then 11 else (if a < 12 then (if a < 10 then (if a < 9 then 11 else 10) else 10) else 10)) else (if a < 24 then 10 else (if a < 28 then (if a < 26 then 10 else 2) else 2))) else 2) else 2) else (if a < 67 then (if a < 33 then (if a < 16 then (if a < 8 then 11 else (if a < 12 then (if a < 10 then 11 else (if a < 11 then 11 else 9)) else 9)) else (if a < 24 then 9 else (if a < 28 then (if a < 26 then 9 else (if a < 27 then 9 else 2)) else 2))) else 2) else 2))) else (if b < 30 then (if b < 29 then (if a < 67 then (if a < 33 then (if a < 16 then (if a < 8 then 11 else (if a < 12 then 11 else (if a < 14 then (if a < 13 then 11 else 8) else 8))) else (if a < 24 then 8 else (if a < 28 then 8 else 2))) else 2) else 2) else (if a < 67 then (if a < 33 then (if a < 16 then (if a < 8 then 11 else (if a < 12 then 11 else (if a < 14 then 11 else (if a < 15 then 11 else 7)))) else (if a < 24 then 7 else (if a < 28 then 7 else (if a < 30 then (if a < 29 then 7 else 2) else 2)))) else 2) else 2)) else (if b < 31 then (if a < 67 then (if a < 33 then (if a < 16 then 11 else (if a < 24 then (if a < 20 then (if a < 18 then (if a < 17 then 11 else 6) else 6) else 6) else (if a < 28 then 6 else (if a < 30 then 6 else 2)))) else 2) else 2) else (if b < 32 then (if a < 67 then (if a < 33 then (if a < 16 then 11 else (if a < 24 then (if a < 20 then (if a < 18 then 11 else (if a < 19 then 11 else 5)) else 5) else (if a < 28 then 5 else (if a < 30 then 5 else (if a < 31 then 5 else 2))))) else 2) else 2) else (if a < 67 then (if a < 33 then (if a < 16 then 11 else (if a < 24 then (if a < 20 then 11 else (if a < 22 then (if a < 21 then 11 else 4) else 4)) else (if a < 28 then 4 else (if a < 30 then 4 else (if a < 31 then 4 else (if a < 32 then 4 else 2)))))) else 2) else 2))))))) else (if b < 50 then (if b < 41 then (if b < 37 then (if b < 35 then (if b < 34 then (if a < 67 then (if a < 33 then (if a < 16 then 11 else (if a < 24 then (if a < 20 then 11 else (if a < 22 then 11 else (if a < 23 then 11 else 3))) else 3)) else 2) else 2) else (if a < 67 then (if a < 33 then (if a < 16 then 11 else (if a < 24 then 11 else (if a < 28 then (if a < 26 then (if a < 25 then 11 else 2) else 2) else 2))) else 2) else 2)) else (if b < 36 then (if a < 67 then (if a < 33 then (if a < 16 then 11 else (if a < 24 then (if a < 20 then (if a < 18 then 11 else 10) else 10) else 10)) else (if a < 50 then (if a < 41 then (if a < 37 then (if a < 35 then 10 else 2) else 2) else 2) else 2)) else 2) else (if a < 67 then (if a < 33 then (if a < 16 then 11 else (if a < 24 then (if a < 20 then 11 else 9) else 9)) else (if a < 50 then (if a < 41 then (if a < 37 then (if a < 35 then 9 else (if a < 36 then 9 else 2)) else 2) else 2) else 2)) else 2))) else (if b < 39 then (if b < 38 then (if a < 67 then (if a < 33 then (if a < 16 then 11 else (if a < 24 then (if a < 20 then 11 else (if a < 22 then 11 else 8)) else 8)) else (if a < 50 then (if a < 41 then (if a < 37 then 8 else 2) else 2) else 2)) else 2) else (if a < 67 then (if a < 33 then (if a < 16 then 11 else (if a < 24 then 11 else 7)) else (if a < 50 then (if a < 41 then (if a < 37 then 7 else (if a < 39 then (if a < 38 then 7 else 2) else 2)) else 2) else 2)) else 2)) else (if b < 40 then (if a < 67 then (if a < 33 then (if a < 16 then 11 else (if a < 24 then 11 else (if a < 28 then (if a < 26 then 11 else 6) else 6))) else (if a < 50 then (if a < 41 then (if a < 37 then 6 else (if a < 39 then 6 else 2)) else 2) else 2)) else 2) else (if a < 67 then (if a < 33 then (if a < 16 then 11 else (if a < 24 then 11 else (if a < 28 then 11 else 5))) else (if a < 50 then (if a < 41 then (if a < 37 then 5 else (if a < 39 then 5 else (if a < 40 then 5 else 2))) else 2) else 2)) else 2)))) else (if b < 45 then (if b < 43 then (if b < 42 then (if a < 67 then (if a < 33 then (if a < 16 then 11 else (if a < 24 then 11 else (if a < 28 then 11 else (if a < 30 then 11 else 4)))) else (if a < 50 then (if a < 41 then 4 else 2) else 2)) else 2) else (if a < 67 then (if a < 33 then (if a < 16 then 11 else (if a < 24 then 11 else (if a < 28 then 11 else (if a < 30 then 11 else (if a < 31 then 11 else (if a < 32 then 11 else 3)))))) else (if a < 50 then (if a < 41 then 3 else (if a < 45 then (if a < 43 then (if a < 42 then 3 else 2) else 2) else 2)) else 2)) else 2)) else (if b < 44 then (if a < 67 then (if a < 33 then 11 else (if a < 50 then (if a < 41 then (if a < 37 then (if a < 35 then (if a < 34 then 11 else 2) else 2) else 2) else 2) else 2)) else 2) else (if a < 67 then (if a < 33 then 10 else (if a < 50 then (if a < 41 then 10 else (if a < 45 then (if a < 43 then 10 else (if a < 44 then 10 else 2)) else 2)) else 2)) else 2))) else (if b < 47 then (if b < 46 then (if a < 67 then (if a < 33 then (if a < 16 then 10 else (if a < 24 then 10 else (if a < 28 then 10 else (if a < 30 then (if a < 29 then 10 else 9) else 9)))) else (if a < 50 then (if a < 41 then 9 else (if a < 45 then 9 else 2)) else 2)) else 2) else (if a < 67 then (if a < 33 then (if a < 16 then 10 else (if a < 24 then 10 else (if a < 28 then 10 else (if a < 30 then 10 else (if a < 31 then 10 else 8))))) else (if a < 50 then (if a < 41 then 8 else (if a < 45 then 8 else (if a < 47 then (if a < 46 then 8 else 2) else 2))) else 2)) else 2)) else (if b < 48 then (if a < 67 then (if a < 33 then 10 else (if a < 50 then (if a < 41 then 7 else (if a < 45 then 7 else (if a < 47 then 7 else 2))) else 2)) else 2) else (if b < 49 then (if a < 67 then (if a < 33 then 10 else (if a < 50 then (if a < 41 then (if a < 37 then (if a < 35 then 10 else 6) else 6) else (if a < 45 then 6 else (if a < 47 then 6 else (if a < 48 then 6 else 2)))) else 2)) else 2) else (if a < 67 then (if a < 33 then 10 else (if a < 50 then (if a < 41 then (if a < 37 then 10 else 5) else (if a < 45 then 5 else (if a < 47 then 5 else (if a < 48 then 5 else (if a < 49 then 5 else 2))))) else 2)) else 2)))))) else (if b < 58 then (if b < 54 then (if b < 52 then (if b < 51 then (if a < 67 then (if a < 33 then 10 else (if a < 50 then (if a < 41 then (if a < 37 then 10 else (if a < 39 then 10 else 4)) else 4) else 2)) else 2) else (if a < 67 then (if a < 33 then 10 else (if a < 50 then (if a < 41 then 10 else 3) else (if a < 58 then (if a < 54 then (if a < 52 then (if a < 51 then 3 else 2) else 2) else 2) else 2))) else 2)) else (if b < 53 then (if a < 67 then (if a < 33 then 10 else (if a < 50 then (if a < 41 then 10 else (if a < 45 then (if a < 43 then 10 else 2) else 2)) else 2)) else 2) else (if a < 67 then (if a < 33 then 10 else (if a < 50 then 10 else (if a < 58 then (if a < 54 then (if a < 52 then 10 else (if a < 53 then 10 else 2)) else 2) else 2))) else 2))) else (if b < 56 then (if b < 55 then (if a < 67 then (if a < 33 then 10 else (if a < 50 then (if a < 41 then (if a < 37 then 10 else (if a < 39 then 10 else 9)) else 9) else (if a < 58 then (if a < 54 then 9 else 2) else 2))) else 2) else (if a < 67 then (if a < 33 then 10 else (if a < 50 then (if a < 41 then 10 else 8) else (if a < 58 then (if a < 54 then 8 else (if a < 56 then (if a < 55 then 8 else 2) else 2)) else 2))) else 2)) else (if b < 57 then (if a < 67 then (if a < 33 then 10 else (if a < 50 then (if a < 41 then 10 else (if a < 45 then (if a < 43 then 10 else 7) else 7)) else (if a < 58 then (if a < 54 then 7 else (if a < 56 then 7 else 2)) else 2))) else 2) else (if a < 67 then (if a < 33 then 10 else (if a < 50 then (if a < 41 then 10 else (if a < 45 then 10 else 6)) else (if a < 58 then (if a < 54 then 6 else (if a < 56 then 6 else (if a < 57 then 6 else 2))) else 2))) else 2)))) else (if b < 62 then (if b < 60 then (if b < 59 then (if a < 67 then (if a < 33 then 10 else (if a < 50 then (if a < 41 then 10 else (if a < 45 then 10 else (if a < 47 then 10 else 5))) else (if a < 58 then 5 else 2))) else 2) else (if a < 67 then (if a < 33 then 10 else (if a < 50 then (if a < 41 then 10 else (if a < 45 then 10 else (if a < 47 then 10 else (if a < 48 then 10 else (if a < 49 then 10 else 4))))) else (if a < 58 then 4 else (if a < 62 then (if a < 60 then (if a < 59 then 4 else 2) else 2) else 2)))) else 2)) else (if b < 61 then (if a < 67 then (if a < 33 then 10 else (if a < 50 then 10 else (if a < 58 then (if a < 54 then (if a < 52 then (if a < 51 then 10 else 3) else 3) else 3) else (if a < 62 then (if a < 60 then 3 else 2) else 2)))) else 2) else (if a < 67 then (if a < 33 then 10 else (if a < 50 then 10 else (if a < 58 then (if a < 54 then (if a < 52 then 10 else (if a < 53 then 10 else 2)) else 2) else 2))) else 2))) else (if b < 64 then (if b < 63 then (if a < 67 then (if a < 33 then 9 else (if a < 50 then 9 else (if a < 58 then 9 else (if a < 62 then 9 else 2)))) else 2) else (if a < 67 then (if a < 33 then 9 else (if a < 50 then (if a < 41 then 9 else (if a < 45 then 9 else (if a < 47 then 9 else (if a < 48 then 9 else (if a < 49 then 9 else 8))))) else (if a < 58 then 8 else (if a < 62 then 8 else (if a < 64 then (if a < 63 then 8 else 2) else 2))))) else 2)) else (if b < 65 then (if a < 67 then (if a < 33 then 9 else (if a < 50 then 9 else (if a < 58 then (if a < 54 then (if a < 52 then (if a < 51 then 9 else 7) else 7) else 7) else (if a < 62 then 7 else (if a < 64 then 7 else 2))))) else 2) else (if b < 66 then (if a < 67 then (if a < 33 then 9 else (if a < 50 then 9 else (if a < 58 then (if a < 54 then (if a < 52 then 9 else (if a < 53 then 9 else 6)) else 6) else (if a < 62 then 6 else (if a < 64 then 6 else (if a < 65 then 6 else 2)))))) else 2) else (if a < 67 then (if a < 33 then 9 else (if a < 50 then 9 else (if a < 58 then (if a < 54 then 9 else (if a < 56 then (if a < 55 then 9 else 5) else 5)) else (if a < 62 then 5 else (if a < 64 then 5 else (if a < 65 then 5 else (if a < 66 then 5 else 2))))))) else 2)))))))) else (if b < 100 then (if b < 83 then (if b < 75 then (if b < 71 then (if b < 69 then (if b < 68 then (if a < 67 then (if a < 33 then 9 else (if a < 50 then 9 else (if a < 58 then (if a < 54 then 9 else (if a < 56 then 9 else (if a < 57 then 9 else 4))) else 4))) else 2) else (if a < 67 then (if a < 33 then 9 else (if a < 50 then 9 else (if a < 58 then 9 else (if a < 62 then (if a < 60 then (if a < 59 then 9 else 3) else 3) else 3)))) else (if a < 100 then (if a < 83 then (if a < 75 then (if a < 71 then (if a < 69 then (if a < 68 then 3 else 2) else 2) else 2) else 2) else 2) else 2))) else (if b < 70 then (if a < 67 then (if a < 33 then 9 else (if a < 50 then 9 else (if a < 58 then 9 else (if a < 62 then (if a < 60 then 9 else (if a < 61 then 9 else 2)) else 2)))) else 2) else (if a < 67 then 9 else (if a < 100 then (if a < 83 then (if a < 75 then (if a < 71 then (if a < 69 then 9 else (if a < 70 then 9 else 2)) else 2) else 2) else 2) else 2)))) else (if b < 73 then (if b < 72 then (if a < 67 then (if a < 33 then 9 else (if a < 50 then 9 else (if a < 58 then 9 else 8))) else (if a < 100 then (if a < 83 then (if a < 75 then (if a < 71 then 8 else 2) else 2) else 2) else 2)) else (if a < 67 then (if a < 33 then 9 else (if a < 50 then 9 else (if a < 58 then 9 else (if a < 62 then (if a < 60 then 9 else 7) else 7)))) else (if a < 100 then (if a < 83 then (if a < 75 then (if a < 71 then 7 else (if a < 73 then (if a < 72 then 7 else 2) else 2)) else 2) else 2) else 2))) else (if b < 74 then (if a < 67 then (if a < 33 then 9 else (if a < 50 then 9 else (if a < 58 then 9 else (if a < 62 then 9 else 6)))) else (if a < 100 then (if a < 83 then (if a < 75 then (if a < 71 then 6 else (if a < 73 then 6 else 2)) else 2) else 2) else 2)) else (if a < 67 then (if a < 33 then 9 else (if a < 50 then 9 else (if a < 58 then 9 else (if a < 62 then 9 else (if a < 64 then 9 else 5))))) else (if a < 100 then (if a < 83 then (if a < 75 then (if a < 71 then 5 else (if a < 73 then 5 else (if a < 74 then 5 else 2))) else 2) else 2) else 2))))) else (if b < 79 then (if b < 77 then (if b < 76 then (if a < 67 then (if a < 33 then 9 else (if a < 50 then 9 else (if a < 58 then 9 else (if a < 62 then 9 else (if a < 64 then 9 else (if a < 65 then 9 else (if a < 66 then 9 else 4))))))) else (if a < 100 then (if a < 83 then (if a < 75 then 4 else 2) else 2) else 2)) else (if a < 67 then 9 else (if a < 100 then (if a < 83 then (if a < 75 then (if a < 71 then (if a < 69 then (if a < 68 then 9 else 3) else 3) else 3) else (if a < 79 then (if a < 77 then (if a < 76 then 3 else 2) else 2) else 2)) else 2) else 2))) else (if b < 78 then (if a < 67 then 9 else (if a < 100 then (if a < 83 then (if a < 75 then (if a < 71 then (if a < 69 then 9 else (if a < 70 then 9 else 2)) else 2) else 2) else 2) else 2)) else (if a < 67 then 8 else (if a < 100 then (if a < 83 then (if a < 75 then 8 else (if a < 79 then (if a < 77 then 8 else (if a < 78 then 8 else 2)) else 2)) else 2) else 2)))) else (if b < 81 then (if b < 80 then (if a < 67 then 8 else (if a < 100 then (if a < 83 then (if a < 75 then 7 else (if a < 79 then 7 else 2)) else 2) else 2)) else (if a < 67 then 8 else (if a < 100 then (if a < 83 then (if a < 75 then (if a < 71 then (if a < 69 then 8 else 6) else 6) else (if a < 79 then 6 else (if a < 81 then (if a < 80 then 6 else 2) else 2))) else 2) else 2))) else (if b < 82 then (if a < 67 then 8 else (if a < 100 then (if a < 83 then (if a < 75 then (if a < 71 then 8 else 5) else (if a < 79 then 5 else (if a < 81 then 5 else 2))) else 2) else 2)) else (if a < 67 then 8 else (if a < 100 then (if a < 83 then (if a < 75 then (if a < 71 then 8 else (if a < 73 then 8 else 4)) else (if a < 79 then 4 else (if a < 81 then 4 else (if a < 82 then 4 else 2)))) else 2) else 2)))))) else (if b < 91 then (if b < 87 then (if b < 85 then (if b < 84 then (if a < 67 then 8 else (if a < 100 then (if a < 83 then (if a < 75 then 8 else 3) else 2) else 2)) else (if a < 67 then 8 else (if a < 100 then (if a < 83 then (if a < 75 then 8 else (if a < 79 then (if a < 77 then 8 else 2) else 2)) else 2) else 2))) else (if b < 86 then (if a < 67 then 8 else (if a < 100 then (if a < 83 then 8 else (if a < 91 then (if a < 87 then (if a < 85 then 8 else 2) else 2) else 2)) else 2)) else (if a < 67 then 8 else (if a < 100 then (if a < 83 then (if a < 75 then 8 else 7) else (if a < 91 then (if a < 87 then (if a < 85 then 7 else (if a < 86 then 7 else 2)) else 2) else 2)) else 2)))) else (if b < 89 then (if b < 88 then (if a < 67 then 8 else (if a < 100 then (if a < 83 then (if a < 75 then 8 else (if a < 79 then (if a < 77 then 8 else 6) else 6)) else (if a < 91 then (if a < 87 then 6 else 2) else 2)) else 2)) else (if a < 67 then 8 else (if a < 100 then (if a < 83 then (if a < 75 then 8 else (if a < 79 then 8 else 5)) else (if a < 91 then (if a < 87 then 5 else (if a < 89 then (if a < 88 then 5 else 2) else 2)) else 2)) else 2))) else (if b < 90 then (if a < 67 then 8 else (if a < 100 then (if a < 83 then (if a < 75 then 8 else (if a < 79 then 8 else (if a < 81 then 8 else 4))) else (if a < 91 then (if a < 87 then 4 else (if a < 89 then 4 else 2)) else 2)) else 2)) else (if a < 67 then 8 else (if a < 100 then (if a < 83 then 8 else (if a < 91 then (if a < 87 then 3 else (if a < 89 then 3 else (if a < 90 then 3 else 2))) else 2)) else 2))))) else (if b < 95 then (if b < 93 then (if b < 92 then (if a < 67 then 8 else (if a < 100 then (if a < 83 then 8 else (if a < 91 then (if a < 87 then (if a < 85 then 8 else 2) else 2) else 2)) else 2)) else (if a < 67 then 7 else (if a < 100 then (if a < 83 then 7 else (if a < 91 then 7 else (if a < 95 then (if a < 93 then (if a < 92 then 7 else 2) else 2) else 2))) else 2))) else (if b < 94 then (if a < 67 then 7 else (if a < 100 then (if a < 83 then 7 else (if a < 91 then 6 else (if a < 95 then (if a < 93 then 6 else 2) else 2))) else 2)) else (if a < 67 then 7 else (if a < 100 then (if a < 83 then 7 else (if a < 91 then (if a < 87 then (if a < 85 then 7 else 5) else 5) else (if a < 95 then (if a < 93 then 5 else (if a < 94 then 5 else 2)) else 2))) else 2)))) else (if b < 97 then (if b < 96 then (if a < 67 then 7 else (if a < 100 then (if a < 83 then 7 else (if a < 91 then (if a < 87 then 7 else 4) else (if a < 95 then 4 else 2))) else 2)) else (if a < 67 then 7 else (if a < 100 then (if a < 83 then 7 else (if a < 91 then (if a < 87 then 7 else (if a < 89 then 7 else 3)) else (if a < 95 then 3 else (if a < 97 then (if a < 96 then 3 else 2) else 2)))) else 2))) else (if b < 98 then (if a < 67 then 7 else (if a < 100 then (if a < 83 then 7 else (if a < 91 then 7 else 2)) else 2)) else (if b < 99 then (if a < 67 then 7 else (if a < 100 then (if a < 83 then 7 else (if a < 91 then 7 else (if a < 95 then 7 else (if a < 97 then 7 else (if a < 98 then 7 else 2))))) else 2)) else (if a < 67 then 7 else (if a < 100 then (if a < 83 then 7 else (if a < 91 then (if a < 87 then 7 else (if a < 89 then 7 else (if a < 90 then 7 else 6))) else (if a < 95 then 6 else (if a < 97 then 6 else (if a < 98 then 6 else (if a < 99 then 6 else 2)))))) else 2)))))))) else (if b < 117 then (if b < 108 then (if b < 104 then (if b < 102 then (if b < 101 then (if a < 67 then 7 else (if a < 100 then (if a < 83 then 7 else (if a < 91 then 7 else (if a < 95 then (if a < 93 then (if a < 92 then 7 else 5) else 5) else 5))) else 2)) else (if a < 67 then 7 else (if a < 100 then (if a < 83 then 7 else (if a < 91 then 7 else (if a < 95 then (if a < 93 then 7 else (if a < 94 then 7 else 4)) else 4))) else (if a < 117 then (if a < 108 then (if a < 104 then (if a < 102 then (if a < 101 then 4 else 2) else 2) else 2) else 2) else 2)))) else (if b < 103 then (if a < 67 then 7 else (if a < 100 then (if a < 83 then 7 else (if a < 91 then 7 else (if a < 95 then 7 else (if a < 97 then (if a < 96 then 7 else 3) else 3)))) else (if a < 117 then (if a < 108 then (if a < 104 then (if a < 102 then 3 else 2) else 2) else 2) else 2))) else (if a < 67 then 7 else (if a < 100 then (if a < 83 then 7 else (if a < 91 then 7 else (if a < 95 then 7 else (if a < 97 then 7 else (if a < 98 then 7 else 2))))) else 2)))) else (if b < 106 then (if b < 105 then (if a < 67 then 6 else (if a < 100 then 6 else (if a < 117 then (if a < 108 then (if a < 104 then 6 else 2) else 2) else 2))) else (if a < 67 then 6 else (if a < 100 then (if a < 83 then 6 else (if a < 91 then 6 else (if a < 95 then 6 else (if a < 97 then 6 else 5)))) else (if a < 117 then (if a < 108 then (if a < 104 then 5 else (if a < 106 then (if a < 105 then 5 else 2) else 2)) else 2) else 2)))) else (if b < 107 then (if a < 67 then 6 else (if a < 100 then (if a < 83 then 6 else (if a < 91 then 6 else (if a < 95 then 6 else (if a < 97 then 6 else (if a < 98 then 6 else (if a < 99 then 6 else 4)))))) else (if a < 117 then (if a < 108 then (if a < 104 then 4 else (if a < 106 then 4 else 2)) else 2) else 2))) else (if a < 67 then 6 else (if a < 100 then 6 else (if a < 117 then (if a < 108 then (if a < 104 then (if a < 102 then (if a < 101 then 6 else 3) else 3) else (if a < 106 then 3 else (if a < 107 then 3 else 2))) else 2) else 2)))))) else (if b < 112 then (if b < 110 then (if b < 109 then (if a < 67 then 6 else (if a < 100 then 6 else (if a < 117 then (if a < 108 then (if a < 104 then (if a < 102 then 6 else (if a < 103 then 6 else 2)) else 2) else 2) else 2))) else (if a < 67 then 6 else (if a < 100 then 6 else (if a < 117 then (if a < 108 then 6 else (if a < 112 then (if a < 110 then (if a < 109 then 6 else 2) else 2) else 2)) else 2)))) else (if b < 111 then (if a < 67 then 6 else (if a < 100 then 6 else (if a < 117 then (if a < 108 then (if a < 104 then (if a < 102 then 6 else (if a < 103 then 6 else 5)) else 5) else (if a < 112 then (if a < 110 then 5 else 2) else 2)) else 2))) else (if a < 67 then 6 else (if a < 100 then 6 else (if a < 117 then (if a < 108 then (if a < 104 then 6 else (if a < 106 then (if a < 105 then 6 else 4) else 4)) else (if a < 112 then (if a < 110 then 4 else (if a < 111 then 4 else 2)) else 2)) else 2))))) else (if b < 114 then (if b < 113 then (if a < 67 then 6 else (if a < 100 then 6 else (if a < 117 then (if a < 108 then (if a < 104 then 6 else (if a < 106 then 6 else (if a < 107 then 6 else 3))) else (if a < 112 then 3 else 2)) else 2))) else (if a < 67 then 6 else (if a < 100 then 6 else (if a < 117 then (if a < 108 then 6 else (if a < 112 then (if a < 110 then (if a < 109 then 6 else 2) else 2) else 2)) else 2)))) else (if b < 115 then (if a < 67 then 5 else (if a < 100 then 5 else (if a < 117 then (if a < 108 then 5 else (if a < 112 then 5 else (if a < 114 then 5 else 2))) else 2))) else (if b < 116 then (if a < 67 then 5 else (if a < 100 then 5 else (if a < 117 then (if a < 108 then 5 else (if a < 112 then (if a < 110 then (if a < 109 then 5 else 4) else 4) else (if a < 114 then 4 else (if a < 115 then 4 else 2)))) else 2))) else (if a < 67 then 5 else (if a < 100 then 5 else (if a < 117 then (if a < 108 then 5 else (if a < 112 then (if a < 110 then 5 else (if a < 111 then 5 else 3)) else (if a < 114 then 3 else (if a < 115 then 3 else (if a < 116 then 3 else 2))))) else 2)))))))) else (if b < 125 then (if b < 121 then (if b < 119 then (if b < 118 then (if a < 67 then 5 else (if a < 100 then 5 else (if a < 117 then (if a < 108 then 5 else (if a < 112 then 5 else (if a < 114 then (if a < 113 then 5 else 2) else 2))) else 2))) else (if a < 67 then 5 else (if a < 100 then 5 else (if a < 117 then 5 else (if a < 125 then (if a < 121 then (if a < 119 then (if a < 118 then 5 else 2) else 2) else 2) else 2))))) else (if b < 120 then (if a < 67 then 5 else (if a < 100 then 5 else (if a < 117 then (if a < 108 then 5 else (if a < 112 then 5 else (if a < 114 then 5 else 4))) else (if a < 125 then (if a < 121 then (if a < 119 then 4 else 2) else 2) else 2)))) else (if a < 67 then 5 else (if a < 100 then 5 else (if a < 117 then (if a < 108 then 5 else (if a < 112 then 5 else (if a < 114 then 5 else (if a < 115 then 5 else (if a < 116 then 5 else 3))))) else (if a < 125 then (if a < 121 then (if a < 119 then 3 else (if a < 120 then 3 else 2)) else 2) else 2)))))) else (if b < 123 then (if b < 122 then (if a < 67 then 5 else (if a < 100 then 5 else (if a < 117 then 5 else (if a < 125 then (if a < 121 then (if a < 119 then (if a < 118 then 5 else 2) else 2) else 2) else 2)))) else (if a < 67 then 4 else (if a < 100 then 4 else (if a < 117 then 4 else (if a < 125 then (if a < 121 then 4 else (if a < 123 then (if a < 122 then 4 else 2) else 2)) else 2))))) else (if b < 124 then (if a < 67 then 4 else (if a < 100 then 4 else (if a < 117 then 4 else (if a < 125 then (if a < 121 then (if a < 119 then 4 else 3) else (if a < 123 then 3 else 2)) else 2)))) else (if a < 67 then 4 else (if a < 100 then 4 else (if a < 117 then 4 else (if a < 125 then (if a < 121 then 4 else 2) else 2))))))) else (if b < 129 then (if b < 127 then (if b < 126 then (if a < 67 then 4 else (if a < 100 then 4 else (if a < 117 then 4 else (if a < 125 then 4 else 2)))) else (if a < 67 then 4 else (if a < 100 then 4 else (if a < 117 then 4 else (if a < 125 then (if a < 121 then 4 else (if a < 123 then 4 else 3)) else (if a < 129 then (if a < 127 then (if a < 126 then 3 else 2) else 2) else 2)))))) else (if b < 128 then (if a < 67 then 4 else (if a < 100 then 4 else (if a < 117 then 4 else (if a < 125 then 4 else 2)))) else (if a < 67 then 3 else (if a < 100 then 3 else (if a < 117 then 3 else (if a < 125 then 3 else (if a < 129 then (if a < 127 then 3 else (if a < 128 then 3 else 2)) else 2))))))) else (if b < 131 then (if b < 130 then (if a < 67 then 3 else (if a < 100 then 3 else (if a < 117 then 3 else (if a < 125 then 3 else (if a < 129 then (if a < 127 then 3 else 2) else 2))))) else (if a < 67 then 3 else (if a < 100 then 3 else (if a < 117 then 3 else (if a < 125 then 3 else (if a < 129 then 3 else (if a < 131 then (if a < 130 then 3 else 2) else 2))))))) else (if b < 132 then (if a < 67 then 3 else (if a < 100 then 3 else (if a < 117 then 3 else (if a < 125 then 3 else (if a < 129 then 3 else (if a < 131 then (if a < 130 then 3 else 2) else 2)))))) else 2)))))))


def rowCheck (a : Nat) : Bool := (List.range 134).all fun b =>
  if 1 ≤ a ∧ a < b ∧ witnessColor a = witnessColor b then
    decide (2 ≤ witnessRank a b ∧ witnessRank a b ≤ 11) &&
    ((List.range' (b+1) (min 133 (b+b-a) - b)).all fun c =>
      if witnessColor b = witnessColor c then decide (witnessRank b c + 1 ≤ witnessRank a b)
      else true)
  else true

theorem checked_pair (a b : Nat) (hrow : rowCheck a = true)
    (ha : 1 ≤ a) (hab : a < b) (hb : b ≤ 133)
    (hc : witnessColor a = witnessColor b) :
    2 ≤ witnessRank a b ∧ witnessRank a b ≤ 11 := by
  have h := List.all_eq_true.mp hrow b (List.mem_range.mpr (by omega))
  rw [if_pos ⟨ha, hab, hc⟩] at h
  exact of_decide_eq_true (Bool.and_eq_true_iff.mp h).1

theorem checked_step (a b c : Nat) (hrow : rowCheck a = true)
    (ha : 1 ≤ a) (hab : a < b) (hbc : b < c) (hn : c ≤ 133)
    (hgap : c+a ≤ b+b) (hc1 : witnessColor a = witnessColor b)
    (hc2 : witnessColor b = witnessColor c) :
    witnessRank b c + 1 ≤ witnessRank a b := by
  have h := List.all_eq_true.mp hrow b (List.mem_range.mpr (by omega))
  rw [if_pos ⟨ha, hab, hc1⟩] at h
  have hm : c ∈ List.range' (b+1) (min 133 (b+b-a) - b) := by
    apply List.mem_range'.mpr
    refine ⟨c-b-1, ?_, ?_⟩ <;> omega
  have hs := List.all_eq_true.mp (Bool.and_eq_true_iff.mp h).2 c hm
  rw [if_pos hc2] at hs
  exact of_decide_eq_true hs


theorem row_0 : rowCheck 0 = true := by decide +kernel
#print axioms row_0
theorem row_1 : rowCheck 1 = true := by decide +kernel
theorem row_2 : rowCheck 2 = true := by decide +kernel
theorem row_3 : rowCheck 3 = true := by decide +kernel
theorem row_4 : rowCheck 4 = true := by decide +kernel
theorem row_5 : rowCheck 5 = true := by decide +kernel
theorem row_6 : rowCheck 6 = true := by decide +kernel
theorem row_7 : rowCheck 7 = true := by decide +kernel
theorem row_8 : rowCheck 8 = true := by decide +kernel
theorem row_9 : rowCheck 9 = true := by decide +kernel
theorem row_10 : rowCheck 10 = true := by decide +kernel
theorem row_11 : rowCheck 11 = true := by decide +kernel
theorem row_12 : rowCheck 12 = true := by decide +kernel
theorem row_13 : rowCheck 13 = true := by decide +kernel
theorem row_14 : rowCheck 14 = true := by decide +kernel
theorem row_15 : rowCheck 15 = true := by decide +kernel
theorem row_16 : rowCheck 16 = true := by decide +kernel
theorem row_17 : rowCheck 17 = true := by decide +kernel
theorem row_18 : rowCheck 18 = true := by decide +kernel
theorem row_19 : rowCheck 19 = true := by decide +kernel
theorem row_20 : rowCheck 20 = true := by decide +kernel
#print axioms row_20
theorem row_21 : rowCheck 21 = true := by decide +kernel
theorem row_22 : rowCheck 22 = true := by decide +kernel
theorem row_23 : rowCheck 23 = true := by decide +kernel
theorem row_24 : rowCheck 24 = true := by decide +kernel
theorem row_25 : rowCheck 25 = true := by decide +kernel
theorem row_26 : rowCheck 26 = true := by decide +kernel
theorem row_27 : rowCheck 27 = true := by decide +kernel
theorem row_28 : rowCheck 28 = true := by decide +kernel
theorem row_29 : rowCheck 29 = true := by decide +kernel
theorem row_30 : rowCheck 30 = true := by decide +kernel
theorem row_31 : rowCheck 31 = true := by decide +kernel
theorem row_32 : rowCheck 32 = true := by decide +kernel
theorem row_33 : rowCheck 33 = true := by decide +kernel
theorem row_34 : rowCheck 34 = true := by decide +kernel
theorem row_35 : rowCheck 35 = true := by decide +kernel
theorem row_36 : rowCheck 36 = true := by decide +kernel
theorem row_37 : rowCheck 37 = true := by decide +kernel
theorem row_38 : rowCheck 38 = true := by decide +kernel
theorem row_39 : rowCheck 39 = true := by decide +kernel
theorem row_40 : rowCheck 40 = true := by decide +kernel
#print axioms row_40
theorem row_41 : rowCheck 41 = true := by decide +kernel
theorem row_42 : rowCheck 42 = true := by decide +kernel
theorem row_43 : rowCheck 43 = true := by decide +kernel
theorem row_44 : rowCheck 44 = true := by decide +kernel
theorem row_45 : rowCheck 45 = true := by decide +kernel
theorem row_46 : rowCheck 46 = true := by decide +kernel
theorem row_47 : rowCheck 47 = true := by decide +kernel
theorem row_48 : rowCheck 48 = true := by decide +kernel
theorem row_49 : rowCheck 49 = true := by decide +kernel
theorem row_50 : rowCheck 50 = true := by decide +kernel
theorem row_51 : rowCheck 51 = true := by decide +kernel
theorem row_52 : rowCheck 52 = true := by decide +kernel
theorem row_53 : rowCheck 53 = true := by decide +kernel
theorem row_54 : rowCheck 54 = true := by decide +kernel
theorem row_55 : rowCheck 55 = true := by decide +kernel
theorem row_56 : rowCheck 56 = true := by decide +kernel
theorem row_57 : rowCheck 57 = true := by decide +kernel
theorem row_58 : rowCheck 58 = true := by decide +kernel
theorem row_59 : rowCheck 59 = true := by decide +kernel
theorem row_60 : rowCheck 60 = true := by decide +kernel
#print axioms row_60
theorem row_61 : rowCheck 61 = true := by decide +kernel
theorem row_62 : rowCheck 62 = true := by decide +kernel
theorem row_63 : rowCheck 63 = true := by decide +kernel
theorem row_64 : rowCheck 64 = true := by decide +kernel
theorem row_65 : rowCheck 65 = true := by decide +kernel
theorem row_66 : rowCheck 66 = true := by decide +kernel
theorem row_67 : rowCheck 67 = true := by decide +kernel
theorem row_68 : rowCheck 68 = true := by decide +kernel
theorem row_69 : rowCheck 69 = true := by decide +kernel
theorem row_70 : rowCheck 70 = true := by decide +kernel
theorem row_71 : rowCheck 71 = true := by decide +kernel
theorem row_72 : rowCheck 72 = true := by decide +kernel
theorem row_73 : rowCheck 73 = true := by decide +kernel
theorem row_74 : rowCheck 74 = true := by decide +kernel
theorem row_75 : rowCheck 75 = true := by decide +kernel
theorem row_76 : rowCheck 76 = true := by decide +kernel
theorem row_77 : rowCheck 77 = true := by decide +kernel
theorem row_78 : rowCheck 78 = true := by decide +kernel
theorem row_79 : rowCheck 79 = true := by decide +kernel
theorem row_80 : rowCheck 80 = true := by decide +kernel
#print axioms row_80
theorem row_81 : rowCheck 81 = true := by decide +kernel
theorem row_82 : rowCheck 82 = true := by decide +kernel
theorem row_83 : rowCheck 83 = true := by decide +kernel
theorem row_84 : rowCheck 84 = true := by decide +kernel
theorem row_85 : rowCheck 85 = true := by decide +kernel
theorem row_86 : rowCheck 86 = true := by decide +kernel
theorem row_87 : rowCheck 87 = true := by decide +kernel
theorem row_88 : rowCheck 88 = true := by decide +kernel
theorem row_89 : rowCheck 89 = true := by decide +kernel
theorem row_90 : rowCheck 90 = true := by decide +kernel
theorem row_91 : rowCheck 91 = true := by decide +kernel
theorem row_92 : rowCheck 92 = true := by decide +kernel
theorem row_93 : rowCheck 93 = true := by decide +kernel
theorem row_94 : rowCheck 94 = true := by decide +kernel
theorem row_95 : rowCheck 95 = true := by decide +kernel
theorem row_96 : rowCheck 96 = true := by decide +kernel
theorem row_97 : rowCheck 97 = true := by decide +kernel
theorem row_98 : rowCheck 98 = true := by decide +kernel
theorem row_99 : rowCheck 99 = true := by decide +kernel
theorem row_100 : rowCheck 100 = true := by decide +kernel
#print axioms row_100
theorem row_101 : rowCheck 101 = true := by decide +kernel
theorem row_102 : rowCheck 102 = true := by decide +kernel
theorem row_103 : rowCheck 103 = true := by decide +kernel
theorem row_104 : rowCheck 104 = true := by decide +kernel
theorem row_105 : rowCheck 105 = true := by decide +kernel
theorem row_106 : rowCheck 106 = true := by decide +kernel
theorem row_107 : rowCheck 107 = true := by decide +kernel
theorem row_108 : rowCheck 108 = true := by decide +kernel
theorem row_109 : rowCheck 109 = true := by decide +kernel
theorem row_110 : rowCheck 110 = true := by decide +kernel
theorem row_111 : rowCheck 111 = true := by decide +kernel
theorem row_112 : rowCheck 112 = true := by decide +kernel
theorem row_113 : rowCheck 113 = true := by decide +kernel
theorem row_114 : rowCheck 114 = true := by decide +kernel
theorem row_115 : rowCheck 115 = true := by decide +kernel
theorem row_116 : rowCheck 116 = true := by decide +kernel
theorem row_117 : rowCheck 117 = true := by decide +kernel
theorem row_118 : rowCheck 118 = true := by decide +kernel
theorem row_119 : rowCheck 119 = true := by decide +kernel
theorem row_120 : rowCheck 120 = true := by decide +kernel
#print axioms row_120
theorem row_121 : rowCheck 121 = true := by decide +kernel
theorem row_122 : rowCheck 122 = true := by decide +kernel
theorem row_123 : rowCheck 123 = true := by decide +kernel
theorem row_124 : rowCheck 124 = true := by decide +kernel
theorem row_125 : rowCheck 125 = true := by decide +kernel
theorem row_126 : rowCheck 126 = true := by decide +kernel
theorem row_127 : rowCheck 127 = true := by decide +kernel
theorem row_128 : rowCheck 128 = true := by decide +kernel
theorem row_129 : rowCheck 129 = true := by decide +kernel
theorem row_130 : rowCheck 130 = true := by decide +kernel
theorem row_131 : rowCheck 131 = true := by decide +kernel
theorem row_132 : rowCheck 132 = true := by decide +kernel
theorem row_133 : rowCheck 133 = true := by decide +kernel
theorem all_rows : ∀ a : Fin 134, rowCheck a.val = true := (Fin.cases row_0 (Fin.cases row_1 (Fin.cases row_2 (Fin.cases row_3 (Fin.cases row_4 (Fin.cases row_5 (Fin.cases row_6 (Fin.cases row_7 (Fin.cases row_8 (Fin.cases row_9 (Fin.cases row_10 (Fin.cases row_11 (Fin.cases row_12 (Fin.cases row_13 (Fin.cases row_14 (Fin.cases row_15 (Fin.cases row_16 (Fin.cases row_17 (Fin.cases row_18 (Fin.cases row_19 (Fin.cases row_20 (Fin.cases row_21 (Fin.cases row_22 (Fin.cases row_23 (Fin.cases row_24 (Fin.cases row_25 (Fin.cases row_26 (Fin.cases row_27 (Fin.cases row_28 (Fin.cases row_29 (Fin.cases row_30 (Fin.cases row_31 (Fin.cases row_32 (Fin.cases row_33 (Fin.cases row_34 (Fin.cases row_35 (Fin.cases row_36 (Fin.cases row_37 (Fin.cases row_38 (Fin.cases row_39 (Fin.cases row_40 (Fin.cases row_41 (Fin.cases row_42 (Fin.cases row_43 (Fin.cases row_44 (Fin.cases row_45 (Fin.cases row_46 (Fin.cases row_47 (Fin.cases row_48 (Fin.cases row_49 (Fin.cases row_50 (Fin.cases row_51 (Fin.cases row_52 (Fin.cases row_53 (Fin.cases row_54 (Fin.cases row_55 (Fin.cases row_56 (Fin.cases row_57 (Fin.cases row_58 (Fin.cases row_59 (Fin.cases row_60 (Fin.cases row_61 (Fin.cases row_62 (Fin.cases row_63 (Fin.cases row_64 (Fin.cases row_65 (Fin.cases row_66 (Fin.cases row_67 (Fin.cases row_68 (Fin.cases row_69 (Fin.cases row_70 (Fin.cases row_71 (Fin.cases row_72 (Fin.cases row_73 (Fin.cases row_74 (Fin.cases row_75 (Fin.cases row_76 (Fin.cases row_77 (Fin.cases row_78 (Fin.cases row_79 (Fin.cases row_80 (Fin.cases row_81 (Fin.cases row_82 (Fin.cases row_83 (Fin.cases row_84 (Fin.cases row_85 (Fin.cases row_86 (Fin.cases row_87 (Fin.cases row_88 (Fin.cases row_89 (Fin.cases row_90 (Fin.cases row_91 (Fin.cases row_92 (Fin.cases row_93 (Fin.cases row_94 (Fin.cases row_95 (Fin.cases row_96 (Fin.cases row_97 (Fin.cases row_98 (Fin.cases row_99 (Fin.cases row_100 (Fin.cases row_101 (Fin.cases row_102 (Fin.cases row_103 (Fin.cases row_104 (Fin.cases row_105 (Fin.cases row_106 (Fin.cases row_107 (Fin.cases row_108 (Fin.cases row_109 (Fin.cases row_110 (Fin.cases row_111 (Fin.cases row_112 (Fin.cases row_113 (Fin.cases row_114 (Fin.cases row_115 (Fin.cases row_116 (Fin.cases row_117 (Fin.cases row_118 (Fin.cases row_119 (Fin.cases row_120 (Fin.cases row_121 (Fin.cases row_122 (Fin.cases row_123 (Fin.cases row_124 (Fin.cases row_125 (Fin.cases row_126 (Fin.cases row_127 (Fin.cases row_128 (Fin.cases row_129 (Fin.cases row_130 (Fin.cases row_131 (Fin.cases row_132 (Fin.cases row_133 (fun i => Fin.elim0 i)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
theorem witness_certificate : Certificate 133 11 witnessColor witnessRank := by
  constructor
  · intro a b ha hab hb hc
    exact (checked_pair a b (all_rows ⟨a, by omega⟩) ha hab hb hc).1
  · intro a b ha hab hb hc
    exact (checked_pair a b (all_rows ⟨a, by omega⟩) ha hab hb hc).2
  · intro a b c ha hab hbc hn hgap hc1 hc2
    exact checked_step a b c (all_rows ⟨a, by omega⟩) ha hab hbc hn hgap hc1 hc2

theorem witness_no_twelve (xs : List Nat)
    (hw : Descending xs) (hi : InInterval 133 xs)
    (hm : Monochromatic witnessColor xs) : xs.length ≤ 11 :=
  certificate_bounds_all (by decide) witness_certificate xs hw hi hm

def ForcesWave (n k : Nat) : Prop :=
  ∀ color : Nat → Bool, ∃ xs : List Nat,
    xs.length = k ∧ Descending xs ∧ InInterval n xs ∧ Monochromatic color xs

theorem not_forces_133_12 : ¬ ForcesWave 133 12 := by
  intro h
  obtain ⟨xs,hlen,hw,hi,hm⟩ := h witnessColor
  have hb := witness_no_twelve xs hw hi hm
  omega

/-- The proposed exact quadratic threshold fails, without any assumption
about existence or a particular representation of the minimum threshold. -/
theorem quadratic_threshold_false : ¬ (∀ k : Nat, 1 ≤ k → ForcesWave (k*k-k+1) k) := by
  intro h
  exact not_forces_133_12 (h 12 (by decide))

#print axioms witness_no_twelve
#print axioms not_forces_133_12
#print axioms quadratic_threshold_false
end DescendingWaves
