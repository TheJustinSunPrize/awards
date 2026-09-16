import Std
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace JSP000301

/-- No proper divisor at least two: the usual elementary definition of prime. -/
def Prime (p : Nat) : Prop := 2 ≤ p ∧
  (List.range p).all (fun d => decide (2 ≤ d → p % d ≠ 0)) = true
instance (p : Nat) : Decidable (Prime p) := by unfold Prime; infer_instance

def Powerful (n : Nat) : Prop :=
  0 < n ∧ ∀ p : Nat, Prime p → p ∣ n → p * p ∣ n

def Square (n : Nat) : Prop := ∃ k : Nat, k * k = n

def Candidate (n : Nat) : Prop :=
  Powerful n ∧ Powerful (n+1) ∧ ¬ Square n ∧ ¬ Square (n+1)

theorem prime_iff (p : Nat) : Prime p ↔
    2 ≤ p ∧ ∀ d : Nat, 2 ≤ d → d < p → ¬ d ∣ p := by
  simp only [Prime, List.all_eq_true, List.mem_range, decide_eq_true_eq]
  constructor
  · rintro ⟨hp, hd⟩
    exact ⟨hp, fun d h2 hlt hdiv => hd d hlt h2 (Nat.dvd_iff_mod_eq_zero.mp hdiv)⟩
  · rintro ⟨hp, hd⟩
    exact ⟨hp, fun d hlt h2 hmod => hd d h2 hlt (Nat.dvd_iff_mod_eq_zero.mpr hmod)⟩

-- w/4 is a square root or prime witness; w%4 selects its interpretation.
def Certificate (n w : Nat) : Prop :=
  let k := w / 4
  match w % 4 with
  | 0 => k * k = n
  | 1 => k * k = n+1
  | 2 => Prime k ∧ n % k = 0 ∧ n % (k*k) ≠ 0
  | _ => Prime k ∧ (n+1) % k = 0 ∧ (n+1) % (k*k) ≠ 0
instance (n w : Nat) : Decidable (Certificate n w) := by
  unfold Certificate
  split <;> infer_instance

theorem certificate_sound {n w : Nat} (h : Certificate n w) : ¬ Candidate n := by
  intro ⟨hn, hn1, hs, hs1⟩
  unfold Certificate at h
  split at h
  · exact hs ⟨_, h⟩
  · exact hs1 ⟨_, h⟩
  · exact h.2.2 (Nat.dvd_iff_mod_eq_zero.mp (hn.2 _ h.1 (Nat.dvd_iff_mod_eq_zero.mpr h.2.1)))
  · exact h.2.2 (Nat.dvd_iff_mod_eq_zero.mp (hn1.2 _ h.1 (Nat.dvd_iff_mod_eq_zero.mpr h.2.1)))

def check (n : Nat) : List Nat → Bool
  | [] => true
  | w :: ws => decide (Certificate n w) && check (n+1) ws

theorem check_sound (ws : List Nat) (n m : Nat) (h : check n ws = true)
    (hlo : n ≤ m) (hhi : m < n+ws.length) : ¬ Candidate m := by
  induction ws generalizing n with
  | nil => simp at hhi; omega
  | cons w ws ih =>
    simp only [check, Bool.and_eq_true, decide_eq_true_eq] at h
    by_cases heq : n=m
    · subst m; exact certificate_sound h.1
    · apply ih (n+1) h.2 <;> simp_all <;> omega

def witnesses0 : List Nat := [
  4, 10, 9, 8, 11, 10, 30, 13, 12, 10, 15, 14, 11, 10, 17, 16, 11, 10, 23, 15, 11, 10, 15, 21, 20,
  10, 31, 30, 11, 10, 126, 15, 11, 10, 25, 24, 11, 10, 14, 22, 11, 10, 47, 23, 11, 10, 15, 29, 28, 10,
  14, 54, 11, 10, 22, 15, 11, 10, 15, 14, 11, 10, 33, 32, 11, 10, 71, 15, 11, 10, 286, 295, 11, 10, 14,
  31, 11, 10, 23, 37, 36, 10, 15, 14, 11, 10, 14, 46, 11, 10, 30, 15, 11, 10, 15, 14, 11, 10, 41, 40]

theorem verified0 : check 1 witnesses0 = true := by decide +kernel

theorem exclude0 (n : Nat) (lo : 1 ≤ n) (hi : n < 101) : ¬ Candidate n := by
  apply check_sound witnesses0 1 n verified0 lo
  exact hi

def witnesses1 : List Nat := [
  11, 10, 55, 15, 11, 10, 430, 439, 11, 10, 14, 30, 11, 10, 22, 55, 11, 10, 15, 45, 44, 10, 14, 126, 11,
  10, 510, 15, 11, 10, 15, 14, 11, 10, 22, 70, 11, 10, 23, 15, 11, 10, 49, 48, 11, 10, 14, 150, 11, 10,
  79, 71, 11, 10, 15, 14, 11, 10, 14, 22, 11, 10, 167, 15, 11, 10, 15, 53, 52, 10, 78, 174, 11, 10, 30,
  15, 11, 10, 23, 22, 11, 10, 14, 23, 11, 10, 46, 31, 11, 10, 15, 14, 11, 10, 57, 56, 11, 10, 798, 15]

theorem verified1 : check 101 witnesses1 = true := by decide +kernel

theorem exclude1 (n : Nat) (lo : 101 ≤ n) (hi : n < 201) : ¬ Candidate n := by
  apply check_sound witnesses1 101 n verified1 lo
  exact hi

def witnesses2 : List Nat := [
  11, 10, 15, 14, 11, 10, 55, 47, 11, 10, 215, 15, 11, 10, 22, 31, 11, 10, 14, 22, 11, 10, 31, 61, 60,
  10, 15, 14, 11, 10, 14, 118, 11, 10, 22, 15, 11, 10, 15, 14, 11, 10, 247, 23, 11, 10, 54, 15, 11, 10,
  31, 30, 11, 10, 65, 64, 11, 10, 23, 22, 11, 10, 15, 14, 11, 10, 14, 270, 11, 10, 71, 15, 11, 10, 15,
  14, 11, 10, 23, 22, 11, 10, 287, 15, 11, 10, 30, 69, 68, 10, 14, 294, 11, 10, 22, 47, 11, 10, 15, 14]

theorem verified2 : check 201 witnesses2 = true := by decide +kernel

theorem exclude2 (n : Nat) (lo : 201 ≤ n) (hi : n < 301) : ¬ Candidate n := by
  apply check_sound witnesses2 201 n verified2 lo
  exact hi

def witnesses3 : List Nat := [
  11, 10, 14, 23, 11, 10, 31, 15, 11, 10, 15, 14, 11, 10, 22, 318, 11, 10, 23, 15, 11, 10, 73, 72, 11,
  10, 14, 31, 11, 10, 335, 151, 11, 10, 15, 14, 11, 10, 14, 22, 11, 10, 175, 15, 11, 10, 15, 14, 11, 10,
  47, 46, 11, 10, 22, 15, 11, 10, 23, 77, 76, 10, 14, 23, 11, 10, 95, 94, 11, 10, 15, 14, 11, 10, 14,
  55, 11, 10, 23, 15, 11, 10, 15, 14, 11, 10, 174, 390, 11, 10, 70, 15, 11, 10, 22, 46, 11, 10, 81, 80]

theorem verified3 : check 301 witnesses3 = true := by decide +kernel

theorem exclude3 (n : Nat) (lo : 301 ≤ n) (hi : n < 401) : ¬ Candidate n := by
  apply check_sound witnesses3 301 n verified3 lo
  exact hi

def witnesses4 : List Nat := [
  11, 10, 54, 23, 11, 10, 15, 14, 11, 10, 14, 31, 11, 10, 22, 15, 11, 10, 15, 14, 11, 10, 190, 71, 11,
  10, 30, 15, 11, 10, 1726, 1735, 11, 10, 14, 79, 11, 10, 23, 85, 84, 10, 15, 14, 11, 10, 14, 30, 11, 10,
  46, 15, 11, 10, 15, 14, 11, 10, 23, 22, 11, 10, 119, 15, 11, 10, 55, 31, 11, 10, 14, 47, 11, 10, 31,
  30, 11, 10, 15, 14, 11, 10, 89, 88, 11, 10, 247, 15, 11, 10, 15, 14, 11, 10, 22, 31, 11, 10, 1998, 15]

theorem verified4 : check 401 witnesses4 = true := by decide +kernel

theorem exclude4 (n : Nat) (lo : 401 ≤ n) (hi : n < 501) : ¬ Candidate n := by
  apply check_sound witnesses4 401 n verified4 lo
  exact hi

def witnesses5 : List Nat := [
  11, 10, 31, 23, 11, 10, 14, 510, 11, 10, 30, 79, 11, 10, 15, 14, 11, 10, 14, 22, 11, 10, 527, 15, 11,
  10, 15, 93, 92, 10, 31, 30, 11, 10, 22, 15, 11, 10, 23, 22, 11, 10, 14, 23, 11, 10, 551, 247, 11, 10,
  15, 14, 11, 10, 14, 558, 11, 10, 23, 15, 11, 10, 15, 14, 11, 10, 30, 286, 11, 10, 47, 15, 11, 10, 97,
  96, 11, 10, 14, 22, 11, 10, 46, 23, 11, 10, 15, 14, 11, 10, 14, 150, 11, 10, 22, 15, 11, 10, 15, 14]

theorem verified5 : check 501 witnesses5 = true := by decide +kernel

theorem exclude5 (n : Nat) (lo : 501 ≤ n) (hi : n < 601) : ¬ Candidate n := by
  apply check_sound witnesses5 501 n verified5 lo
  exact hi

def witnesses6 : List Nat := [
  11, 10, 270, 23, 11, 10, 79, 15, 11, 10, 54, 70, 11, 10, 14, 30, 11, 10, 23, 22, 11, 10, 15, 101, 100,
  10, 14, 71, 11, 10, 319, 15, 11, 10, 15, 14, 11, 10, 23, 22, 11, 10, 31, 15, 11, 10, 2590, 47, 11, 10,
  14, 654, 11, 10, 22, 166, 11, 10, 15, 14, 11, 10, 14, 23, 11, 10, 94, 15, 11, 10, 15, 14, 11, 10, 105,
  104, 11, 10, 23, 15, 11, 10, 79, 23, 11, 10, 14, 55, 11, 10, 695, 31, 11, 10, 15, 14, 11, 10, 14, 30]

theorem verified6 : check 601 witnesses6 = true := by decide +kernel

theorem exclude6 (n : Nat) (lo : 601 ≤ n) (hi : n < 701) : ¬ Candidate n := by
  apply check_sound witnesses6 601 n verified6 lo
  exact hi

def witnesses7 : List Nat := [
  11, 10, 47, 15, 11, 10, 15, 14, 11, 10, 318, 95, 11, 10, 22, 15, 11, 10, 23, 22, 11, 10, 14, 119, 11,
  10, 31, 109, 108, 10, 15, 14, 11, 10, 14, 47, 11, 10, 23, 15, 11, 10, 15, 14, 11, 10, 47, 31, 11, 10,
  191, 15, 11, 10, 22, 30, 11, 10, 14, 22, 11, 10, 30, 23, 11, 10, 15, 14, 11, 10, 14, 774, 11, 10, 126,
  15, 11, 10, 15, 14, 11, 10, 113, 112, 11, 10, 791, 15, 11, 10, 30, 46, 11, 10, 14, 798, 11, 10, 70, 359]

theorem verified7 : check 701 witnesses7 = true := by decide +kernel

theorem exclude7 (n : Nat) (lo : 701 ≤ n) (hi : n < 801) : ¬ Candidate n := by
  apply check_sound witnesses7 701 n verified7 lo
  exact hi

def witnesses8 : List Nat := [
  11, 10, 15, 14, 11, 10, 14, 406, 11, 10, 31, 15, 11, 10, 15, 14, 11, 10, 23, 22, 11, 10, 415, 15, 11,
  10, 95, 94, 11, 10, 14, 54, 11, 10, 22, 46, 11, 10, 15, 117, 116, 10, 14, 23, 11, 10, 30, 15, 11, 10,
  15, 14, 11, 10, 22, 430, 11, 10, 23, 15, 11, 10, 3454, 23, 11, 10, 14, 30, 11, 10, 54, 391, 11, 10, 15,
  14, 11, 10, 14, 22, 11, 10, 55, 15, 11, 10, 15, 14, 11, 10, 46, 79, 11, 10, 22, 15, 11, 10, 121, 120]

theorem verified8 : check 801 witnesses8 = true := by decide +kernel

theorem exclude8 (n : Nat) (lo : 801 ≤ n) (hi : n < 901) : ¬ Candidate n := by
  apply check_sound witnesses8 801 n verified8 lo
  exact hi

def witnesses9 : List Nat := [
  11, 10, 14, 23, 11, 10, 911, 407, 11, 10, 15, 14, 11, 10, 14, 31, 11, 10, 23, 15, 11, 10, 15, 14, 11,
  10, 119, 118, 11, 10, 78, 15, 11, 10, 22, 54, 11, 10, 14, 22, 11, 10, 94, 23, 11, 10, 15, 14, 11, 10,
  14, 30, 11, 10, 22, 15, 11, 10, 15, 125, 124, 10, 430, 23, 11, 10, 3870, 15, 11, 10, 3886, 31, 11, 10, 14,
  246, 11, 10, 23, 22, 11, 10, 15, 14, 11, 10, 14, 54, 11, 10, 127, 15, 11, 10, 15, 14, 11, 10, 150, 31]

theorem verified9 : check 901 witnesses9 = true := by decide +kernel

theorem exclude9 (n : Nat) (lo : 901 ≤ n) (hi : n < 1001) : ¬ Candidate n := by
  apply check_sound witnesses9 901 n verified9 lo
  exact hi

def witnesses10 : List Nat := [
  11, 10, 70, 15, 11, 10, 31, 30, 11, 10, 14, 46, 11, 10, 22, 455, 11, 10, 15, 14, 11, 10, 129, 128, 11,
  10, 54, 15, 11, 10, 15, 14, 11, 10, 22, 30, 11, 10, 23, 15, 11, 10, 30, 23, 11, 10, 14, 526, 11, 10,
  1055, 55, 11, 10, 15, 14, 11, 10, 14, 22, 11, 10, 31, 15, 11, 10, 15, 14, 11, 10, 30, 119, 11, 10, 174,
  15, 11, 10, 23, 22, 11, 10, 14, 23, 11, 10, 71, 133, 132, 10, 15, 14, 11, 10, 14, 550, 11, 10, 30, 15]

theorem verified10 : check 1001 witnesses10 = true := by decide +kernel

theorem exclude10 (n : Nat) (lo : 1001 ≤ n) (hi : n < 1101) : ¬ Candidate n := by
  apply check_sound witnesses10 1001 n verified10 lo
  exact hi

def witnesses11 : List Nat := [
  11, 10, 15, 14, 11, 10, 166, 1110, 11, 10, 46, 15, 11, 10, 22, 126, 11, 10, 14, 22, 11, 10, 1127, 1126, 11,
  10, 15, 14, 11, 10, 14, 47, 11, 10, 22, 15, 11, 10, 15, 14, 11, 10, 47, 23, 11, 10, 31, 15, 11, 10,
  4606, 4615, 11, 10, 137, 136, 11, 10, 23, 22, 11, 10, 15, 14, 11, 10, 14, 31, 11, 10, 1175, 15, 11, 10, 15,
  14, 11, 10, 23, 22, 11, 10, 30, 15, 11, 10, 47, 46, 11, 10, 14, 598, 11, 10, 22, 31, 11, 10, 15, 14]

theorem verified11 : check 1101 witnesses11 = true := by decide +kernel

theorem exclude11 (n : Nat) (lo : 1101 ≤ n) (hi : n < 1201) : ¬ Candidate n := by
  apply check_sound witnesses11 1101 n verified11 lo
  exact hi

def witnesses12 : List Nat := [
  11, 10, 14, 23, 11, 10, 70, 15, 11, 10, 15, 14, 11, 10, 22, 78, 11, 10, 23, 15, 11, 10, 71, 141, 140,
  10, 14, 1230, 11, 10, 31, 30, 11, 10, 15, 14, 11, 10, 14, 22, 11, 10, 46, 15, 11, 10, 15, 14, 11, 10,
  558, 31, 11, 10, 22, 15, 11, 10, 23, 22, 11, 10, 14, 23, 11, 10, 30, 191, 11, 10, 15, 14, 11, 10, 14,
  46, 11, 10, 23, 15, 11, 10, 15, 14, 11, 10, 31, 30, 11, 10, 71, 15, 11, 10, 145, 144, 11, 10, 14, 54]

theorem verified12 : check 1201 witnesses12 = true := by decide +kernel

theorem exclude12 (n : Nat) (lo : 1201 ≤ n) (hi : n < 1301) : ¬ Candidate n := by
  apply check_sound witnesses12 1201 n verified12 lo
  exact hi

def witnesses13 : List Nat := [
  11, 10, 655, 23, 11, 10, 15, 14, 11, 10, 14, 55, 11, 10, 22, 15, 11, 10, 15, 14, 11, 10, 1327, 215, 11,
  10, 335, 15, 11, 10, 151, 127, 11, 10, 14, 31, 11, 10, 23, 22, 11, 10, 15, 14, 11, 10, 14, 79, 11, 10,
  30, 15, 11, 10, 15, 14, 11, 10, 23, 22, 11, 10, 47, 15, 11, 10, 79, 149, 148, 10, 14, 5495, 11, 10, 46,
  71, 11, 10, 15, 14, 11, 10, 14, 23, 11, 10, 78, 15, 11, 10, 15, 14, 11, 10, 22, 47, 11, 10, 31, 15]

theorem verified13 : check 1301 witnesses13 = true := by decide +kernel

theorem exclude13 (n : Nat) (lo : 1301 ≤ n) (hi : n < 1401) : ¬ Candidate n := by
  apply check_sound witnesses13 1301 n verified13 lo
  exact hi

def witnesses14 : List Nat := [
  11, 10, 55, 23, 11, 10, 14, 46, 11, 10, 70, 631, 11, 10, 15, 14, 11, 10, 14, 22, 11, 10, 359, 15, 11,
  10, 15, 14, 11, 10, 214, 718, 11, 10, 22, 15, 11, 10, 23, 22, 11, 10, 153, 152, 11, 10, 727, 31, 11, 10,
  15, 14, 11, 10, 14, 30, 11, 10, 23, 15, 11, 10, 15, 14, 11, 10, 654, 55, 11, 10, 95, 15, 11, 10, 167,
  31, 11, 10, 14, 22, 11, 10, 31, 23, 11, 10, 15, 14, 11, 10, 14, 1494, 11, 10, 22, 15, 11, 10, 15, 14]

theorem verified14 : check 1401 witnesses14 = true := by decide +kernel

theorem exclude14 (n : Nat) (lo : 1401 ≤ n) (hi : n < 1501) : ¬ Candidate n := by
  apply check_sound witnesses14 1401 n verified14 lo
  exact hi

def witnesses15 : List Nat := [
  11, 10, 191, 23, 11, 10, 46, 15, 11, 10, 31, 30, 11, 10, 14, 151, 11, 10, 23, 157, 156, 10, 15, 14, 11,
  10, 14, 47, 11, 10, 1535, 15, 11, 10, 15, 14, 11, 10, 23, 22, 11, 10, 775, 15, 11, 10, 30, 174, 11, 10,
  14, 390, 11, 10, 22, 695, 11, 10, 15, 14, 11, 10, 14, 23, 11, 10, 6270, 15, 11, 10, 15, 14, 11, 10, 30,
  79, 11, 10, 23, 15, 11, 10, 47, 23, 11, 10, 14, 31, 11, 10, 150, 239, 11, 10, 15, 14, 11, 10, 161, 160]

theorem verified15 : check 1501 witnesses15 = true := by decide +kernel

theorem exclude15 (n : Nat) (lo : 1501 ≤ n) (hi : n < 1601) : ¬ Candidate n := by
  apply check_sound witnesses15 1501 n verified15 lo
  exact hi

def witnesses16 : List Nat := [
  11, 10, 30, 15, 11, 10, 15, 14, 11, 10, 55, 54, 11, 10, 22, 15, 11, 10, 23, 22, 11, 10, 14, 30, 11,
  10, 47, 46, 11, 10, 15, 14, 11, 10, 14, 1638, 11, 10, 23, 15, 11, 10, 15, 14, 11, 10, 246, 71, 11, 10,
  31, 15, 11, 10, 22, 94, 11, 10, 14, 22, 11, 10, 55, 23, 11, 10, 15, 14, 11, 10, 14, 31, 11, 10, 270,
  15, 11, 10, 15, 165, 164, 10, 46, 23, 11, 10, 30, 15, 11, 10, 78, 190, 11, 10, 14, 214, 11, 10, 71, 31]

theorem verified16 : check 1601 witnesses16 = true := by decide +kernel

theorem exclude16 (n : Nat) (lo : 1601 ≤ n) (hi : n < 1701) : ¬ Candidate n := by
  apply check_sound witnesses16 1601 n verified16 lo
  exact hi

def witnesses17 : List Nat := [
  11, 10, 15, 14, 11, 10, 14, 30, 11, 10, 118, 15, 11, 10, 15, 14, 11, 10, 23, 22, 11, 10, 1727, 15, 11,
  10, 46, 31, 11, 10, 14, 1734, 11, 10, 22, 30, 11, 10, 15, 14, 11, 10, 14, 23, 11, 10, 79, 15, 11, 10,
  15, 14, 11, 10, 22, 31, 11, 10, 23, 15, 11, 10, 169, 168, 11, 10, 14, 54, 11, 10, 30, 791, 11, 10, 15,
  14, 11, 10, 14, 22, 11, 10, 895, 15, 11, 10, 15, 14, 11, 10, 31, 30, 11, 10, 22, 15, 11, 10, 30, 7207]

theorem verified17 : check 1701 witnesses17 = true := by decide +kernel

theorem exclude17 (n : Nat) (lo : 1701 ≤ n) (hi : n < 1801) : ¬ Candidate n := by
  apply check_sound witnesses17 1701 n verified17 lo
  exact hi

def witnesses18 : List Nat := [
  11, 10, 14, 23, 11, 10, 54, 271, 11, 10, 15, 14, 11, 10, 14, 95, 11, 10, 23, 15, 11, 10, 15, 14, 11,
  10, 30, 127, 11, 10, 919, 15, 11, 10, 22, 47, 11, 10, 14, 22, 11, 10, 78, 23, 11, 10, 15, 173, 172, 10,
  14, 71, 11, 10, 22, 15, 11, 10, 15, 14, 11, 10, 94, 23, 11, 10, 1871, 15, 11, 10, 55, 54, 11, 10, 14,
  30, 11, 10, 23, 22, 11, 10, 15, 14, 11, 10, 14, 238, 11, 10, 47, 15, 11, 10, 15, 14, 11, 10, 79, 78]

theorem verified18 : check 1801 witnesses18 = true := by decide +kernel

theorem exclude18 (n : Nat) (lo : 1801 ≤ n) (hi : n < 1901) : ¬ Candidate n := by
  apply check_sound witnesses18 1801 n verified18 lo
  exact hi

def witnesses19 : List Nat := [
  11, 10, 31, 15, 11, 10, 215, 95, 11, 10, 14, 958, 11, 10, 22, 287, 11, 10, 15, 14, 11, 10, 14, 31, 11,
  10, 166, 15, 11, 10, 15, 14, 11, 10, 177, 176, 11, 10, 23, 15, 11, 10, 118, 23, 11, 10, 14, 1950, 11, 10,
  247, 31, 11, 10, 15, 14, 11, 10, 14, 22, 11, 10, 54, 15, 11, 10, 15, 14, 11, 10, 71, 70, 11, 10, 55,
  15, 11, 10, 23, 22, 11, 10, 14, 23, 11, 10, 31, 30, 11, 10, 15, 14, 11, 10, 14, 1998, 11, 10, 7998, 15]

theorem verified19 : check 1901 witnesses19 = true := by decide +kernel

theorem exclude19 (n : Nat) (lo : 1901 ≤ n) (hi : n < 2001) : ¬ Candidate n := by
  apply check_sound witnesses19 1901 n verified19 lo
  exact hi

def witnesses20 : List Nat := [
  11, 10, 15, 14, 11, 10, 894, 167, 11, 10, 2015, 15, 11, 10, 22, 30, 11, 10, 14, 22, 11, 10, 30, 181, 180,
  10, 15, 14, 11, 10, 14, 79, 11, 10, 22, 15, 11, 10, 15, 14, 11, 10, 31, 23, 11, 10, 94, 15, 11, 10,
  30, 78, 11, 10, 14, 71, 11, 10, 23, 22, 11, 10, 15, 14, 11, 10, 14, 46, 11, 10, 31, 15, 11, 10, 15,
  14, 11, 10, 23, 22, 11, 10, 2087, 15, 11, 10, 119, 118, 11, 10, 14, 31, 11, 10, 22, 526, 11, 10, 15, 14]

theorem verified20 : check 2001 witnesses20 = true := by decide +kernel

theorem exclude20 (n : Nat) (lo : 2001 ≤ n) (hi : n < 2101) : ¬ Candidate n := by
  apply check_sound witnesses20 2001 n verified20 lo
  exact hi

def witnesses21 : List Nat := [
  11, 10, 14, 23, 11, 10, 71, 15, 11, 10, 15, 14, 11, 10, 185, 184, 11, 10, 23, 15, 11, 10, 46, 71, 11,
  10, 14, 30, 11, 10, 55, 54, 11, 10, 15, 14, 11, 10, 14, 22, 11, 10, 271, 15, 11, 10, 15, 14, 11, 10,
  958, 1078, 11, 10, 22, 15, 11, 10, 23, 22, 11, 10, 14, 23, 11, 10, 46, 967, 11, 10, 15, 14, 11, 10, 14,
  31, 11, 10, 23, 15, 11, 10, 15, 14, 11, 10, 2191, 47, 11, 10, 30, 15, 11, 10, 22, 246, 11, 10, 14, 46]

theorem verified21 : check 2101 witnesses21 = true := by decide +kernel

theorem exclude21 (n : Nat) (lo : 2101 ≤ n) (hi : n < 2201) : ¬ Candidate n := by
  apply check_sound witnesses21 2101 n verified21 lo
  exact hi

def witnesses22 : List Nat := [
  11, 10, 79, 23, 11, 10, 15, 189, 188, 10, 14, 30, 11, 10, 22, 15, 11, 10, 15, 14, 11, 10, 54, 359, 11,
  10, 70, 15, 11, 10, 94, 31, 11, 10, 14, 54, 11, 10, 23, 22, 11, 10, 15, 14, 11, 10, 14, 55, 11, 10,
  2255, 15, 11, 10, 15, 14, 11, 10, 23, 22, 11, 10, 126, 15, 11, 10, 31, 30, 11, 10, 14, 286, 11, 10, 30,
  47, 11, 10, 15, 14, 11, 10, 14, 23, 11, 10, 47, 15, 11, 10, 15, 14, 11, 10, 22, 30, 11, 10, 78, 15]

theorem verified22 : check 2201 witnesses22 = true := by decide +kernel

theorem exclude22 (n : Nat) (lo : 2201 ≤ n) (hi : n < 2301) : ¬ Candidate n := by
  apply check_sound witnesses22 2201 n verified22 lo
  exact hi

def witnesses23 : List Nat := [
  11, 10, 193, 192, 11, 10, 14, 2310, 11, 10, 9246, 1031, 11, 10, 15, 14, 11, 10, 14, 22, 11, 10, 31, 15, 11,
  10, 15, 14, 11, 10, 30, 46, 11, 10, 22, 15, 11, 10, 23, 22, 11, 10, 14, 23, 11, 10, 2351, 119, 11, 10,
  15, 14, 11, 10, 14, 78, 11, 10, 23, 15, 11, 10, 15, 14, 11, 10, 151, 95, 11, 10, 2375, 15, 11, 10, 47,
  46, 11, 10, 14, 22, 11, 10, 599, 23, 11, 10, 15, 14, 11, 10, 14, 54, 11, 10, 22, 15, 11, 10, 15, 197]

theorem verified23 : check 2301 witnesses23 = true := by decide +kernel

theorem exclude23 (n : Nat) (lo : 2301 ≤ n) (hi : n < 2401) : ¬ Candidate n := by
  apply check_sound witnesses23 2301 n verified23 lo
  exact hi

def witnesses24 : List Nat := [
  196, 10, 358, 23, 11, 10, 31, 15, 11, 10, 271, 79, 11, 10, 14, 606, 11, 10, 23, 22, 11, 10, 15, 14, 11,
  10, 14, 31, 11, 10, 46, 15, 11, 10, 15, 14, 11, 10, 23, 22, 11, 10, 30, 15, 11, 10, 71, 70, 11, 10,
  14, 47, 11, 10, 22, 31, 11, 10, 15, 14, 11, 10, 14, 23, 11, 10, 2471, 15, 11, 10, 15, 14, 11, 10, 46,
  2478, 11, 10, 23, 15, 11, 10, 54, 23, 11, 10, 14, 79, 11, 10, 31, 30, 11, 10, 15, 14, 11, 10, 201, 200]

theorem verified24 : check 2401 witnesses24 = true := by decide +kernel

theorem exclude24 (n : Nat) (lo : 2401 ≤ n) (hi : n < 2501) : ¬ Candidate n := by
  apply check_sound witnesses24 2401 n verified24 lo
  exact hi

def witnesses25 : List Nat := [
  11, 10, 1255, 15, 11, 10, 15, 14, 11, 10, 126, 31, 11, 10, 22, 15, 11, 10, 23, 22, 11, 10, 14, 407, 11,
  10, 30, 318, 11, 10, 15, 14, 11, 10, 14, 175, 11, 10, 23, 15, 11, 10, 15, 14, 11, 10, 55, 54, 11, 10,
  47, 15, 11, 10, 22, 286, 11, 10, 14, 22, 11, 10, 46, 23, 11, 10, 15, 14, 11, 10, 14, 127, 11, 10, 31,
  15, 11, 10, 15, 14, 11, 10, 30, 23, 11, 10, 54, 15, 11, 10, 10366, 10375, 11, 10, 14, 46, 11, 10, 55, 205]

theorem verified25 : check 2501 witnesses25 = true := by decide +kernel

theorem exclude25 (n : Nat) (lo : 2501 ≤ n) (hi : n < 2601) : ¬ Candidate n := by
  apply check_sound witnesses25 2501 n verified25 lo
  exact hi

def witnesses26 : List Nat := [
  204, 10, 15, 14, 11, 10, 14, 654, 11, 10, 30, 15, 11, 10, 15, 14, 11, 10, 23, 22, 11, 10, 167, 15, 11,
  10, 150, 47, 11, 10, 14, 30, 11, 10, 22, 1175, 11, 10, 15, 14, 11, 10, 14, 23, 11, 10, 1327, 15, 11, 10,
  15, 14, 11, 10, 22, 334, 11, 10, 23, 15, 11, 10, 151, 23, 11, 10, 14, 71, 11, 10, 671, 47, 11, 10, 15,
  14, 11, 10, 14, 22, 11, 10, 47, 15, 11, 10, 15, 14, 11, 10, 54, 2694, 11, 10, 22, 15, 11, 10, 10798, 151]

theorem verified26 : check 2601 witnesses26 = true := by decide +kernel

theorem exclude26 (n : Nat) (lo : 2601 ≤ n) (hi : n < 2701) : ¬ Candidate n := by
  apply check_sound witnesses26 2601 n verified26 lo
  exact hi

def witnesses27 : List Nat := [
  11, 10, 209, 208, 11, 10, 2711, 31, 11, 10, 15, 14, 11, 10, 14, 30, 11, 10, 23, 15, 11, 10, 15, 14, 11,
  10, 47, 46, 11, 10, 2735, 15, 11, 10, 22, 31, 11, 10, 14, 22, 11, 10, 54, 23, 11, 10, 15, 14, 11, 10,
  14, 174, 11, 10, 22, 15, 11, 10, 15, 14, 11, 10, 1230, 23, 11, 10, 695, 15, 11, 10, 31, 30, 11, 10, 14,
  1390, 11, 10, 23, 22, 11, 10, 15, 14, 11, 10, 14, 70, 11, 10, 1399, 15, 11, 10, 15, 14, 11, 10, 31, 30]

theorem verified27 : check 2701 witnesses27 = true := by decide +kernel

theorem exclude27 (n : Nat) (lo : 2701 ≤ n) (hi : n < 2801) : ¬ Candidate n := by
  apply check_sound witnesses27 2701 n verified27 lo
  exact hi

def witnesses28 : List Nat := [
  11, 10, 2807, 15, 11, 10, 30, 213, 212, 10, 14, 78, 11, 10, 22, 46, 11, 10, 15, 14, 11, 10, 14, 455, 11,
  10, 31, 15, 11, 10, 15, 14, 11, 10, 22, 2838, 11, 10, 23, 15, 11, 10, 319, 23, 11, 10, 14, 31, 11, 10,
  95, 94, 11, 10, 15, 14, 11, 10, 14, 22, 11, 10, 30, 15, 11, 10, 15, 14, 11, 10, 46, 71, 11, 10, 94,
  15, 11, 10, 23, 22, 11, 10, 14, 23, 11, 10, 11550, 431, 11, 10, 15, 14, 11, 10, 14, 726, 11, 10, 54, 15]

theorem verified28 : check 2801 witnesses28 = true := by decide +kernel

theorem exclude28 (n : Nat) (lo : 2801 ≤ n) (hi : n < 2901) : ¬ Candidate n := by
  apply check_sound witnesses28 2801 n verified28 lo
  exact hi

def witnesses29 : List Nat := [
  11, 10, 15, 14, 11, 10, 70, 2910, 11, 10, 31, 15, 11, 10, 217, 216, 11, 10, 14, 22, 11, 10, 71, 55, 11,
  10, 15, 14, 11, 10, 14, 31, 11, 10, 22, 15, 11, 10, 15, 14, 11, 10, 95, 23, 11, 10, 30, 15, 11, 10,
  54, 166, 11, 10, 14, 2958, 11, 10, 23, 22, 11, 10, 15, 14, 11, 10, 14, 30, 11, 10, 2975, 15, 11, 10, 15,
  14, 11, 10, 23, 22, 11, 10, 78, 15, 11, 10, 118, 247, 11, 10, 14, 46, 11, 10, 22, 30, 11, 10, 15, 14]

theorem verified29 : check 2901 witnesses29 = true := by decide +kernel

theorem exclude29 (n : Nat) (lo : 2901 ≤ n) (hi : n < 3001) : ¬ Candidate n := by
  apply check_sound witnesses29 2901 n verified29 lo
  exact hi

def witnesses30 : List Nat := [
  11, 10, 14, 23, 11, 10, 126, 15, 11, 10, 15, 14, 11, 10, 22, 31, 11, 10, 23, 15, 11, 10, 31, 221, 220,
  10, 14, 55, 11, 10, 30, 1351, 11, 10, 15, 14, 11, 10, 14, 22, 11, 10, 70, 15, 11, 10, 15, 14, 11, 10,
  31, 30, 11, 10, 22, 15, 11, 10, 23, 22, 11, 10, 14, 23, 11, 10, 55, 47, 11, 10, 15, 14, 11, 10, 14,
  71, 11, 10, 23, 15, 11, 10, 15, 14, 11, 10, 775, 774, 11, 10, 46, 15, 11, 10, 22, 79, 11, 10, 14, 31]

theorem verified30 : check 3001 witnesses30 = true := by decide +kernel

theorem exclude30 (n : Nat) (lo : 3001 ≤ n) (hi : n < 3101) : ¬ Candidate n := by
  apply check_sound witnesses30 3001 n verified30 lo
  exact hi

def witnesses31 : List Nat := [
  11, 10, 118, 23, 11, 10, 15, 14, 11, 10, 14, 47, 11, 10, 22, 15, 11, 10, 15, 14, 11, 10, 47, 46, 11,
  10, 71, 15, 11, 10, 119, 55, 11, 10, 225, 224, 11, 10, 23, 22, 11, 10, 15, 14, 11, 10, 14, 191, 11, 10,
  94, 15, 11, 10, 15, 14, 11, 10, 23, 22, 11, 10, 31, 15, 11, 10, 47, 46, 11, 10, 14, 54, 11, 10, 510,
  1415, 11, 10, 15, 14, 11, 10, 14, 23, 11, 10, 3191, 15, 11, 10, 15, 14, 11, 10, 22, 70, 11, 10, 30, 15]

theorem verified31 : check 3101 witnesses31 = true := by decide +kernel

theorem exclude31 (n : Nat) (lo : 3101 ≤ n) (hi : n < 3201) : ¬ Candidate n := by
  apply check_sound witnesses31 3101 n verified31 lo
  exact hi

def witnesses32 : List Nat := [
  11, 10, 359, 23, 11, 10, 14, 1606, 11, 10, 47, 31, 11, 10, 15, 14, 11, 10, 14, 22, 11, 10, 46, 15, 11,
  10, 15, 14, 11, 10, 407, 215, 11, 10, 22, 15, 11, 10, 23, 22, 11, 10, 14, 23, 11, 10, 31, 229, 228, 10,
  15, 14, 11, 10, 14, 46, 11, 10, 23, 15, 11, 10, 15, 14, 11, 10, 79, 31, 11, 10, 1639, 15, 11, 10, 31,
  30, 11, 10, 14, 22, 11, 10, 270, 23, 11, 10, 15, 14, 11, 10, 14, 151, 11, 10, 22, 15, 11, 10, 15, 14]

theorem verified32 : check 3201 witnesses32 = true := by decide +kernel

theorem exclude32 (n : Nat) (lo : 3201 ≤ n) (hi : n < 3301) : ¬ Candidate n := by
  apply check_sound witnesses32 3201 n verified32 lo
  exact hi

def witnesses33 : List Nat := [
  11, 10, 31, 23, 11, 10, 3311, 15, 11, 10, 30, 94, 11, 10, 14, 127, 11, 10, 23, 22, 11, 10, 15, 14, 11,
  10, 14, 54, 11, 10, 71, 15, 11, 10, 15, 14, 11, 10, 23, 22, 11, 10, 47, 15, 11, 10, 127, 71, 11, 10,
  14, 31, 11, 10, 22, 1495, 11, 10, 15, 14, 11, 10, 233, 232, 11, 10, 30, 15, 11, 10, 15, 14, 11, 10, 847,
  47, 11, 10, 23, 15, 11, 10, 70, 23, 11, 10, 14, 30, 11, 10, 215, 55, 11, 10, 15, 14, 11, 10, 14, 70]

theorem verified33 : check 3301 witnesses33 = true := by decide +kernel

theorem exclude33 (n : Nat) (lo : 3301 ≤ n) (hi : n < 3401) : ¬ Candidate n := by
  apply check_sound witnesses33 3301 n verified33 lo
  exact hi

def witnesses34 : List Nat := [
  11, 10, 95, 15, 11, 10, 15, 14, 11, 10, 1518, 3414, 11, 10, 22, 15, 11, 10, 23, 22, 11, 10, 14, 430, 11,
  10, 94, 511, 11, 10, 15, 14, 11, 10, 14, 31, 11, 10, 23, 15, 11, 10, 15, 14, 11, 10, 1534, 1726, 11, 10,
  30, 15, 11, 10, 22, 13831, 11, 10, 14, 22, 11, 10, 1735, 23, 11, 10, 15, 14, 11, 10, 14, 30, 11, 10, 47,
  15, 11, 10, 15, 237, 236, 10, 55, 23, 11, 10, 46, 15, 11, 10, 391, 31, 11, 10, 14, 55, 11, 10, 31, 30]

theorem verified34 : check 3401 witnesses34 = true := by decide +kernel

theorem exclude34 (n : Nat) (lo : 3401 ≤ n) (hi : n < 3501) : ¬ Candidate n := by
  apply check_sound witnesses34 3401 n verified34 lo
  exact hi

def witnesses35 : List Nat := [
  11, 10, 15, 14, 11, 10, 14, 119, 11, 10, 1759, 15, 11, 10, 15, 14, 11, 10, 23, 22, 11, 10, 54, 15, 11,
  10, 14110, 14119, 11, 10, 14, 3534, 11, 10, 22, 54, 11, 10, 15, 14, 11, 10, 14, 23, 11, 10, 3551, 15, 11, 10,
  15, 14, 11, 10, 22, 30, 11, 10, 23, 15, 11, 10, 30, 23, 11, 10, 14, 175, 11, 10, 79, 78, 11, 10, 15,
  14, 11, 10, 14, 22, 11, 10, 31, 15, 11, 10, 15, 14, 11, 10, 30, 1798, 11, 10, 22, 15, 11, 10, 241, 240]

theorem verified35 : check 3501 witnesses35 = true := by decide +kernel

theorem exclude35 (n : Nat) (lo : 3501 ≤ n) (hi : n < 3601) : ¬ Candidate n := by
  apply check_sound witnesses35 3501 n verified35 lo
  exact hi

def witnesses36 : List Nat := [
  11, 10, 14, 23, 11, 10, 47, 46, 11, 10, 15, 14, 11, 10, 14, 454, 11, 10, 23, 15, 11, 10, 15, 14, 11,
  10, 54, 79, 11, 10, 911, 15, 11, 10, 22, 406, 11, 10, 14, 22, 11, 10, 3647, 23, 11, 10, 15, 14, 11, 10,
  14, 46, 11, 10, 22, 15, 11, 10, 15, 14, 11, 10, 46, 23, 11, 10, 31, 15, 11, 10, 71, 70, 11, 10, 14,
  3678, 11, 10, 23, 22, 11, 10, 15, 14, 11, 10, 14, 31, 11, 10, 55, 15, 11, 10, 15, 14, 11, 10, 151, 150]

theorem verified36 : check 3601 witnesses36 = true := by decide +kernel

theorem exclude36 (n : Nat) (lo : 3601 ≤ n) (hi : n < 3701) : ¬ Candidate n := by
  apply check_sound witnesses36 3601 n verified36 lo
  exact hi

def witnesses37 : List Nat := [
  11, 10, 30, 15, 11, 10, 46, 414, 11, 10, 14, 118, 11, 10, 22, 31, 11, 10, 15, 245, 244, 10, 14, 78, 11,
  10, 935, 15, 11, 10, 15, 14, 11, 10, 22, 151, 11, 10, 23, 15, 11, 10, 55, 23, 11, 10, 14, 95, 11, 10,
  31, 30, 11, 10, 15, 14, 11, 10, 14, 22, 11, 10, 214, 15, 11, 10, 15, 14, 11, 10, 95, 47, 11, 10, 239,
  15, 11, 10, 23, 22, 11, 10, 14, 23, 11, 10, 30, 1687, 11, 10, 15, 14, 11, 10, 14, 54, 11, 10, 79, 15]

theorem verified37 : check 3701 witnesses37 = true := by decide +kernel

theorem exclude37 (n : Nat) (lo : 3701 ≤ n) (hi : n < 3801) : ¬ Candidate n := by
  apply check_sound witnesses37 3701 n verified37 lo
  exact hi

def witnesses38 : List Nat := [
  11, 10, 15, 14, 11, 10, 31, 30, 11, 10, 150, 15, 11, 10, 22, 47, 11, 10, 14, 22, 11, 10, 959, 71, 11,
  10, 15, 14, 11, 10, 14, 1918, 11, 10, 22, 15, 11, 10, 15, 14, 11, 10, 249, 248, 11, 10, 55, 15, 11, 10,
  431, 430, 11, 10, 14, 31, 11, 10, 23, 22, 11, 10, 15, 14, 11, 10, 14, 215, 11, 10, 318, 15, 11, 10, 15,
  14, 11, 10, 23, 22, 11, 10, 46, 15, 11, 10, 94, 15559, 11, 10, 14, 30, 11, 10, 22, 1735, 11, 10, 15, 14]

theorem verified38 : check 3801 witnesses38 = true := by decide +kernel

theorem exclude38 (n : Nat) (lo : 3801 ≤ n) (hi : n < 3901) : ¬ Candidate n := by
  apply check_sound witnesses38 3801 n verified38 lo
  exact hi

def witnesses39 : List Nat := [
  11, 10, 14, 23, 11, 10, 3911, 15, 11, 10, 15, 14, 11, 10, 22, 46, 11, 10, 23, 15, 11, 10, 439, 438, 11,
  10, 14, 1966, 11, 10, 3935, 79, 11, 10, 15, 14, 11, 10, 14, 22, 11, 10, 71, 15, 11, 10, 15, 14, 11, 10,
  55, 54, 11, 10, 22, 15, 11, 10, 23, 22, 11, 10, 14, 23, 11, 10, 127, 253, 252, 10, 15, 14, 11, 10, 14,
  30, 11, 10, 23, 15, 11, 10, 15, 14, 11, 10, 1774, 3990, 11, 10, 54, 15, 11, 10, 22, 31, 11, 10, 14, 16007]

theorem verified39 : check 3901 witnesses39 = true := by decide +kernel

theorem exclude39 (n : Nat) (lo : 3901 ≤ n) (hi : n < 4001) : ¬ Candidate n := by
  apply check_sound witnesses39 3901 n verified39 lo
  exact hi

def witnesses40 : List Nat := [
  11, 10, 31, 23, 11, 10, 15, 14, 11, 10, 14, 70, 11, 10, 22, 15, 11, 10, 15, 14, 11, 10, 598, 31, 11,
  10, 79, 15, 11, 10, 31, 30, 11, 10, 14, 47, 11, 10, 23, 22, 11, 10, 15, 14, 11, 10, 14, 46, 11, 10,
  4055, 15, 11, 10, 15, 14, 11, 10, 23, 22, 11, 10, 70, 15, 11, 10, 334, 55, 11, 10, 14, 2038, 11, 10, 654,
  607, 11, 10, 15, 14, 11, 10, 14, 23, 11, 10, 31, 15, 11, 10, 15, 14, 11, 10, 257, 256, 11, 10, 167, 15]

theorem verified40 : check 4001 witnesses40 = true := by decide +kernel

theorem exclude40 (n : Nat) (lo : 4001 ≤ n) (hi : n < 4101) : ¬ Candidate n := by
  apply check_sound witnesses40 4001 n verified40 lo
  exact hi

def witnesses41 : List Nat := [
  11, 10, 46, 23, 11, 10, 14, 31, 11, 10, 1031, 1030, 11, 10, 15, 14, 11, 10, 14, 22, 11, 10, 30, 15, 11,
  10, 15, 14, 11, 10, 70, 4134, 11, 10, 22, 15, 11, 10, 23, 22, 11, 10, 14, 23, 11, 10, 46, 70, 11, 10,
  15, 14, 11, 10, 14, 4158, 11, 10, 23, 15, 11, 10, 15, 14, 11, 10, 1854, 47, 11, 10, 31, 15, 11, 10, 119,
  118, 11, 10, 14, 22, 11, 10, 190, 23, 11, 10, 15, 14, 11, 10, 14, 31, 11, 10, 22, 15, 11, 10, 15, 14]

theorem verified41 : check 4101 witnesses41 = true := by decide +kernel

theorem exclude41 (n : Nat) (lo : 4101 ≤ n) (hi : n < 4201) : ¬ Candidate n := by
  apply check_sound witnesses41 4101 n verified41 lo
  exact hi

def witnesses42 : List Nat := [
  11, 10, 1870, 23, 11, 10, 30, 15, 11, 10, 55, 47, 11, 10, 14, 70, 11, 10, 23, 22, 11, 10, 15, 261, 260,
  10, 14, 30, 11, 10, 16926, 15, 11, 10, 15, 14, 11, 10, 23, 22, 11, 10, 4247, 15, 11, 10, 126, 31, 11, 10,
  14, 4254, 11, 10, 22, 30, 11, 10, 15, 14, 11, 10, 14, 23, 11, 10, 47, 15, 11, 10, 15, 14, 11, 10, 78,
  31, 11, 10, 23, 15, 11, 10, 31, 23, 11, 10, 14, 270, 11, 10, 30, 118, 11, 10, 15, 14, 11, 10, 14, 47]

theorem verified42 : check 4201 witnesses42 = true := by decide +kernel

theorem exclude42 (n : Nat) (lo : 4201 ≤ n) (hi : n < 4301) : ¬ Candidate n := by
  apply check_sound witnesses42 4201 n verified42 lo
  exact hi

def witnesses43 : List Nat := [
  11, 10, 54, 15, 11, 10, 15, 14, 11, 10, 47, 46, 11, 10, 22, 15, 11, 10, 23, 22, 11, 10, 14, 94, 11,
  10, 2167, 55, 11, 10, 15, 14, 11, 10, 14, 1086, 11, 10, 23, 15, 11, 10, 15, 14, 11, 10, 30, 4350, 11, 10,
  71, 15, 11, 10, 265, 264, 11, 10, 14, 22, 11, 10, 4367, 23, 11, 10, 15, 14, 11, 10, 14, 4374, 11, 10, 30,
  15, 11, 10, 15, 14, 11, 10, 551, 23, 11, 10, 166, 15, 11, 10, 247, 95, 11, 10, 14, 30, 11, 10, 47, 46]

theorem verified43 : check 4301 witnesses43 = true := by decide +kernel

theorem exclude43 (n : Nat) (lo : 4301 ≤ n) (hi : n < 4401) : ¬ Candidate n := by
  apply check_sound witnesses43 4301 n verified43 lo
  exact hi

def witnesses44 : List Nat := [
  11, 10, 15, 14, 11, 10, 14, 78, 11, 10, 46, 15, 11, 10, 15, 14, 11, 10, 23, 22, 11, 10, 31, 15, 11,
  10, 78, 166, 11, 10, 14, 47, 11, 10, 22, 71, 11, 10, 15, 14, 11, 10, 14, 23, 11, 10, 559, 15, 11, 10,
  15, 14, 11, 10, 22, 2230, 11, 10, 23, 15, 11, 10, 127, 23, 11, 10, 14, 167, 11, 10, 55, 31, 11, 10, 15,
  14, 11, 10, 14, 22, 11, 10, 79, 15, 11, 10, 15, 269, 268, 10, 1998, 4494, 11, 10, 22, 15, 11, 10, 46, 31]

theorem verified44 : check 4401 witnesses44 = true := by decide +kernel

theorem exclude44 (n : Nat) (lo : 4401 ≤ n) (hi : n < 4501) : ¬ Candidate n := by
  apply check_sound witnesses44 4401 n verified44 lo
  exact hi

def witnesses45 : List Nat := [
  11, 10, 14, 23, 11, 10, 95, 94, 11, 10, 15, 14, 11, 10, 14, 4518, 11, 10, 23, 15, 11, 10, 15, 14, 11,
  10, 1135, 31, 11, 10, 47, 15, 11, 10, 22, 30, 11, 10, 14, 22, 11, 10, 30, 23, 11, 10, 15, 14, 11, 10,
  14, 119, 11, 10, 22, 15, 11, 10, 15, 14, 11, 10, 31, 23, 11, 10, 2287, 15, 11, 10, 30, 71, 11, 10, 14,
  46, 11, 10, 23, 22, 11, 10, 15, 14, 11, 10, 14, 55, 11, 10, 31, 15, 11, 10, 15, 14, 11, 10, 30, 94]

theorem verified45 : check 4501 witnesses45 = true := by decide +kernel

theorem exclude45 (n : Nat) (lo : 4501 ≤ n) (hi : n < 4601) : ¬ Candidate n := by
  apply check_sound witnesses45 4501 n verified45 lo
  exact hi

def witnesses46 : List Nat := [
  11, 10, 4607, 15, 11, 10, 70, 47, 11, 10, 14, 31, 11, 10, 22, 79, 11, 10, 15, 14, 11, 10, 273, 272, 11,
  10, 30, 15, 11, 10, 15, 14, 11, 10, 22, 78, 11, 10, 23, 15, 11, 10, 175, 23, 11, 10, 14, 30, 11, 10,
  4655, 47, 11, 10, 15, 14, 11, 10, 14, 22, 11, 10, 47, 15, 11, 10, 15, 14, 11, 10, 295, 294, 11, 10, 31,
  15, 11, 10, 23, 22, 11, 10, 14, 23, 11, 10, 174, 1174, 11, 10, 15, 14, 11, 10, 14, 31, 11, 10, 150, 15]

theorem verified46 : check 4601 witnesses46 = true := by decide +kernel

theorem exclude46 (n : Nat) (lo : 4601 ≤ n) (hi : n < 4701) : ¬ Candidate n := by
  apply check_sound witnesses46 4601 n verified46 lo
  exact hi

def witnesses47 : List Nat := [
  11, 10, 15, 14, 11, 10, 47, 46, 11, 10, 30, 15, 11, 10, 22, 215, 11, 10, 14, 22, 11, 10, 4727, 31, 11,
  10, 15, 14, 11, 10, 14, 30, 11, 10, 22, 15, 11, 10, 15, 14, 11, 10, 70, 23, 11, 10, 190, 15, 11, 10,
  47, 46, 11, 10, 14, 118, 11, 10, 23, 277, 276, 10, 15, 14, 11, 10, 14, 79, 11, 10, 54, 15, 11, 10, 15,
  14, 11, 10, 23, 22, 11, 10, 55, 15, 11, 10, 31, 30, 11, 10, 14, 2398, 11, 10, 22, 46, 11, 10, 15, 14]

theorem verified47 : check 4701 witnesses47 = true := by decide +kernel

theorem exclude47 (n : Nat) (lo : 4701 ≤ n) (hi : n < 4801) : ¬ Candidate n := by
  apply check_sound witnesses47 4701 n verified47 lo
  exact hi

def witnesses48 : List Nat := [
  11, 10, 14, 23, 11, 10, 46, 15, 11, 10, 15, 14, 11, 10, 22, 30, 11, 10, 23, 15, 11, 10, 30, 270, 11,
  10, 14, 47, 11, 10, 607, 606, 11, 10, 15, 14, 11, 10, 14, 22, 11, 10, 31, 15, 11, 10, 15, 14, 11, 10,
  46, 95, 11, 10, 22, 15, 11, 10, 23, 22, 11, 10, 14, 23, 11, 10, 126, 2167, 11, 10, 15, 14, 11, 10, 14,
  94, 11, 10, 23, 15, 11, 10, 15, 14, 11, 10, 55, 54, 11, 10, 270, 15, 11, 10, 22, 70, 11, 10, 281, 280]

theorem verified48 : check 4801 witnesses48 = true := by decide +kernel

theorem exclude48 (n : Nat) (lo : 4801 ≤ n) (hi : n < 4901) : ¬ Candidate n := by
  apply check_sound witnesses48 4801 n verified48 lo
  exact hi

def witnesses49 : List Nat := [
  11, 10, 2455, 23, 11, 10, 15, 14, 11, 10, 14, 1230, 11, 10, 22, 15, 11, 10, 15, 14, 11, 10, 2190, 791, 11,
  10, 31, 15, 11, 10, 551, 550, 11, 10, 14, 2470, 11, 10, 23, 22, 11, 10, 15, 14, 11, 10, 14, 407, 11, 10,
  2479, 15, 11, 10, 15, 14, 11, 10, 23, 22, 11, 10, 30, 15, 11, 10, 95, 94, 11, 10, 14, 46, 11, 10, 798,
  31, 11, 10, 15, 14, 11, 10, 14, 23, 11, 10, 119, 15, 11, 10, 15, 14, 11, 10, 22, 79, 11, 10, 19998, 15]

theorem verified49 : check 4901 witnesses49 = true := by decide +kernel

theorem exclude49 (n : Nat) (lo : 4901 ≤ n) (hi : n < 5001) : ¬ Candidate n := by
  apply check_sound witnesses49 4901 n verified49 lo
  exact hi

def witnesses50 : List Nat := [
  11, 10, 559, 23, 11, 10, 14, 1254, 11, 10, 31, 30, 11, 10, 15, 14, 11, 10, 14, 22, 11, 10, 631, 15, 11,
  10, 15, 14, 11, 10, 54, 31, 11, 10, 22, 15, 11, 10, 23, 285, 284, 10, 14, 23, 11, 10, 414, 47, 11, 10,
  15, 14, 11, 10, 14, 55, 11, 10, 23, 15, 11, 10, 15, 14, 11, 10, 31, 30, 11, 10, 46, 15, 11, 10, 30,
  190, 11, 10, 14, 22, 11, 10, 54, 23, 11, 10, 15, 14, 11, 10, 14, 47, 11, 10, 22, 15, 11, 10, 15, 14]

theorem verified50 : check 5001 witnesses50 = true := by decide +kernel

theorem exclude50 (n : Nat) (lo : 5001 ≤ n) (hi : n < 5101) : ¬ Candidate n := by
  apply check_sound witnesses50 5001 n verified50 lo
  exact hi

def witnesses51 : List Nat := [
  11, 10, 30, 23, 11, 10, 5111, 15, 11, 10, 78, 286, 11, 10, 14, 31, 11, 10, 23, 22, 11, 10, 15, 14, 11,
  10, 14, 95, 11, 10, 30, 15, 11, 10, 15, 14, 11, 10, 23, 22, 11, 10, 150, 15, 11, 10, 47, 46, 11, 10,
  14, 30, 11, 10, 22, 767, 11, 10, 15, 14, 11, 10, 14, 23, 11, 10, 71, 15, 11, 10, 15, 14, 11, 10, 94,
  127, 11, 10, 23, 15, 11, 10, 289, 288, 11, 10, 14, 5190, 11, 10, 47, 46, 11, 10, 15, 14, 11, 10, 14, 31]

theorem verified51 : check 5101 witnesses51 = true := by decide +kernel

theorem exclude51 (n : Nat) (lo : 5101 ≤ n) (hi : n < 5201) : ¬ Candidate n := by
  apply check_sound witnesses51 5101 n verified51 lo
  exact hi

def witnesses52 : List Nat := [
  11, 10, 174, 15, 11, 10, 15, 14, 11, 10, 774, 55, 11, 10, 22, 15, 11, 10, 23, 22, 11, 10, 14, 47, 11,
  10, 5231, 31, 11, 10, 15, 14, 11, 10, 14, 30, 11, 10, 23, 15, 11, 10, 15, 14, 11, 10, 46, 119, 11, 10,
  55, 15, 11, 10, 22, 31, 11, 10, 14, 22, 11, 10, 31, 23, 11, 10, 15, 14, 11, 10, 14, 2638, 11, 10, 846,
  15, 11, 10, 15, 14, 11, 10, 2350, 23, 11, 10, 70, 15, 11, 10, 46, 271, 11, 10, 14, 1326, 11, 10, 30, 79]

theorem verified52 : check 5201 witnesses52 = true := by decide +kernel

theorem exclude52 (n : Nat) (lo : 5201 ≤ n) (hi : n < 5301) : ¬ Candidate n := by
  apply check_sound witnesses52 5201 n verified52 lo
  exact hi

def witnesses53 : List Nat := [
  11, 10, 15, 14, 11, 10, 14, 5310, 11, 10, 190, 15, 11, 10, 15, 14, 11, 10, 23, 22, 11, 10, 21294, 15, 11,
  10, 30, 293, 292, 10, 14, 126, 11, 10, 22, 94, 11, 10, 15, 14, 11, 10, 14, 23, 11, 10, 31, 15, 11, 10,
  15, 14, 11, 10, 22, 47, 11, 10, 23, 15, 11, 10, 126, 23, 11, 10, 14, 31, 11, 10, 71, 70, 11, 10, 15,
  14, 11, 10, 14, 22, 11, 10, 30, 15, 11, 10, 15, 14, 11, 10, 1351, 1350, 11, 10, 22, 15, 11, 10, 21598, 47]

theorem verified53 : check 5301 witnesses53 = true := by decide +kernel

theorem exclude53 (n : Nat) (lo : 5301 ≤ n) (hi : n < 5401) : ¬ Candidate n := by
  apply check_sound witnesses53 5301 n verified53 lo
  exact hi

def witnesses54 : List Nat := [
  11, 10, 14, 23, 11, 10, 21630, 2407, 11, 10, 15, 14, 11, 10, 14, 2710, 11, 10, 23, 15, 11, 10, 15, 14, 11,
  10, 95, 94, 11, 10, 31, 15, 11, 10, 22, 606, 11, 10, 14, 22, 11, 10, 5447, 23, 11, 10, 15, 14, 11, 10,
  14, 31, 11, 10, 22, 15, 11, 10, 15, 14, 11, 10, 2430, 23, 11, 10, 30, 15, 11, 10, 79, 55, 11, 10, 297,
  296, 11, 10, 23, 22, 11, 10, 15, 14, 11, 10, 14, 47, 11, 10, 78, 15, 11, 10, 15, 14, 11, 10, 47, 46]

theorem verified54 : check 5401 witnesses54 = true := by decide +kernel

theorem exclude54 (n : Nat) (lo : 5401 ≤ n) (hi : n < 5501) : ¬ Candidate n := by
  apply check_sound witnesses54 5401 n verified54 lo
  exact hi

def witnesses55 : List Nat := [
  11, 10, 175, 15, 11, 10, 71, 31, 11, 10, 14, 54, 11, 10, 22, 30, 11, 10, 15, 14, 11, 10, 14, 55, 11,
  10, 2767, 15, 11, 10, 15, 14, 11, 10, 22, 455, 11, 10, 23, 15, 11, 10, 31, 23, 11, 10, 14, 78, 11, 10,
  30, 1390, 11, 10, 15, 14, 11, 10, 14, 22, 11, 10, 55, 15, 11, 10, 15, 14, 11, 10, 31, 30, 11, 10, 71,
  15, 11, 10, 23, 22, 11, 10, 14, 23, 11, 10, 47, 46, 11, 10, 15, 14, 11, 10, 14, 119, 11, 10, 31, 15]

theorem verified55 : check 5501 witnesses55 = true := by decide +kernel

theorem exclude55 (n : Nat) (lo : 5501 ≤ n) (hi : n < 5601) : ¬ Candidate n := by
  apply check_sound witnesses55 5501 n verified55 lo
  exact hi

def witnesses56 : List Nat := [
  11, 10, 15, 14, 11, 10, 30, 287, 11, 10, 95, 15, 11, 10, 22, 54, 11, 10, 14, 22, 11, 10, 79, 301, 300,
  10, 15, 14, 11, 10, 14, 46, 11, 10, 22, 15, 11, 10, 15, 14, 11, 10, 46, 23, 11, 10, 1415, 15, 11, 10,
  631, 630, 11, 10, 14, 30, 11, 10, 23, 22, 11, 10, 15, 14, 11, 10, 14, 54, 11, 10, 214, 15, 11, 10, 15,
  14, 11, 10, 23, 22, 11, 10, 119, 15, 11, 10, 190, 318, 11, 10, 14, 5694, 11, 10, 22, 358, 11, 10, 15, 14]

theorem verified56 : check 5601 witnesses56 = true := by decide +kernel

theorem exclude56 (n : Nat) (lo : 5601 ≤ n) (hi : n < 5701) : ¬ Candidate n := by
  apply check_sound witnesses56 5601 n verified56 lo
  exact hi

def witnesses57 : List Nat := [
  11, 10, 14, 23, 11, 10, 54, 15, 11, 10, 15, 14, 11, 10, 22, 5718, 11, 10, 23, 15, 11, 10, 215, 214, 11,
  10, 14, 71, 11, 10, 46, 55, 11, 10, 15, 14, 11, 10, 14, 22, 11, 10, 1439, 15, 11, 10, 15, 14, 11, 10,
  286, 47, 11, 10, 22, 15, 11, 10, 23, 22, 11, 10, 14, 23, 11, 10, 31, 30, 11, 10, 15, 14, 11, 10, 305,
  304, 11, 10, 23, 15, 11, 10, 15, 14, 11, 10, 2574, 31, 11, 10, 727, 15, 11, 10, 22, 30, 11, 10, 14, 118]

theorem verified57 : check 5701 witnesses57 = true := by decide +kernel

theorem exclude57 (n : Nat) (lo : 5701 ≤ n) (hi : n < 5801) : ¬ Candidate n := by
  apply check_sound witnesses57 5701 n verified57 lo
  exact hi

def witnesses58 : List Nat := [
  11, 10, 30, 23, 11, 10, 15, 14, 11, 10, 14, 5814, 11, 10, 22, 15, 11, 10, 15, 14, 11, 10, 31, 30, 11,
  10, 127, 15, 11, 10, 70, 79, 11, 10, 14, 55, 11, 10, 23, 22, 11, 10, 15, 14, 11, 10, 14, 70, 11, 10,
  31, 15, 11, 10, 15, 14, 11, 10, 23, 22, 11, 10, 46, 15, 11, 10, 655, 654, 11, 10, 14, 31, 11, 10, 55,
  54, 11, 10, 15, 14, 11, 10, 14, 23, 11, 10, 30, 15, 11, 10, 15, 14, 11, 10, 22, 46, 11, 10, 70, 15]

theorem verified58 : check 5801 witnesses58 = true := by decide +kernel

theorem exclude58 (n : Nat) (lo : 5801 ≤ n) (hi : n < 5901) : ¬ Candidate n := by
  apply check_sound witnesses58 5801 n verified58 lo
  exact hi

def witnesses59 : List Nat := [
  11, 10, 167, 23, 11, 10, 14, 30, 11, 10, 94, 295, 11, 10, 15, 14, 11, 10, 14, 22, 11, 10, 5927, 15, 11,
  10, 15, 309, 308, 10, 2638, 71, 11, 10, 22, 15, 11, 10, 23, 22, 11, 10, 14, 23, 11, 10, 78, 2647, 11, 10,
  15, 14, 11, 10, 14, 31, 11, 10, 23, 15, 11, 10, 15, 14, 11, 10, 54, 191, 11, 10, 30, 15, 11, 10, 335,
  175, 11, 10, 14, 22, 11, 10, 47, 23, 11, 10, 15, 14, 11, 10, 14, 30, 11, 10, 22, 15, 11, 10, 15, 14]

theorem verified59 : check 5901 witnesses59 = true := by decide +kernel

theorem exclude59 (n : Nat) (lo : 5901 ≤ n) (hi : n < 6001) : ¬ Candidate n := by
  apply check_sound witnesses59 5901 n verified59 lo
  exact hi

def witnesses60 : List Nat := [
  11, 10, 79, 23, 11, 10, 3007, 15, 11, 10, 671, 31, 11, 10, 14, 47, 11, 10, 23, 22, 11, 10, 15, 14, 11,
  10, 14, 46, 11, 10, 55, 15, 11, 10, 15, 14, 11, 10, 23, 22, 11, 10, 6047, 15, 11, 10, 31, 30, 11, 10,
  14, 70, 11, 10, 22, 2695, 11, 10, 15, 14, 11, 10, 14, 23, 11, 10, 151, 15, 11, 10, 15, 14, 11, 10, 127,
  126, 11, 10, 23, 15, 11, 10, 313, 312, 11, 10, 14, 3046, 11, 10, 6095, 2711, 11, 10, 15, 14, 11, 10, 14, 246]

theorem verified60 : check 6001 witnesses60 = true := by decide +kernel

theorem exclude60 (n : Nat) (lo : 6001 ≤ n) (hi : n < 6101) : ¬ Candidate n := by
  apply check_sound witnesses60 6001 n verified60 lo
  exact hi

def witnesses61 : List Nat := [
  11, 10, 31, 15, 11, 10, 15, 14, 11, 10, 30, 766, 11, 10, 22, 15, 11, 10, 23, 22, 11, 10, 14, 6126, 11,
  10, 46, 911, 11, 10, 15, 14, 11, 10, 14, 54, 11, 10, 23, 15, 11, 10, 15, 14, 11, 10, 119, 47, 11, 10,
  3079, 15, 11, 10, 22, 78, 11, 10, 14, 22, 11, 10, 95, 23, 11, 10, 15, 14, 11, 10, 14, 6174, 11, 10, 54,
  15, 11, 10, 15, 14, 11, 10, 918, 23, 11, 10, 31, 15, 11, 10, 166, 47, 11, 10, 14, 6198, 11, 10, 127, 55]

theorem verified61 : check 6101 witnesses61 = true := by decide +kernel

theorem exclude61 (n : Nat) (lo : 6101 ≤ n) (hi : n < 6201) : ¬ Candidate n := by
  apply check_sound witnesses61 6101 n verified61 lo
  exact hi

def witnesses62 : List Nat := [
  11, 10, 15, 14, 11, 10, 14, 31, 11, 10, 6215, 15, 11, 10, 15, 14, 11, 10, 23, 22, 11, 10, 510, 15, 11,
  10, 54, 694, 11, 10, 14, 78, 11, 10, 22, 31, 11, 10, 15, 317, 316, 10, 14, 23, 11, 10, 47, 15, 11, 10,
  15, 14, 11, 10, 22, 70, 11, 10, 23, 15, 11, 10, 119, 23, 11, 10, 14, 6270, 11, 10, 25086, 71, 11, 10, 15,
  14, 11, 10, 14, 22, 11, 10, 246, 15, 11, 10, 15, 14, 11, 10, 55, 31, 11, 10, 22, 15, 11, 10, 31, 30]

theorem verified62 : check 6201 witnesses62 = true := by decide +kernel

theorem exclude62 (n : Nat) (lo : 6201 ≤ n) (hi : n < 6301) : ¬ Candidate n := by
  apply check_sound witnesses62 6201 n verified62 lo
  exact hi

def witnesses63 : List Nat := [
  11, 10, 14, 23, 11, 10, 30, 78, 11, 10, 15, 14, 11, 10, 14, 6318, 11, 10, 23, 15, 11, 10, 15, 14, 11,
  10, 31, 30, 11, 10, 54, 15, 11, 10, 22, 46, 11, 10, 14, 22, 11, 10, 55, 23, 11, 10, 15, 14, 11, 10,
  14, 1590, 11, 10, 22, 15, 11, 10, 15, 14, 11, 10, 30, 23, 11, 10, 799, 15, 11, 10, 94, 238, 11, 10, 14,
  31, 11, 10, 23, 22, 11, 10, 15, 14, 11, 10, 14, 6390, 11, 10, 30, 15, 11, 10, 15, 14, 11, 10, 321, 320]

theorem verified63 : check 6301 witnesses63 = true := by decide +kernel

theorem exclude63 (n : Nat) (lo : 6301 ≤ n) (hi : n < 6401) : ¬ Candidate n := by
  apply check_sound witnesses63 6301 n verified63 lo
  exact hi

def witnesses64 : List Nat := [
  11, 10, 78, 15, 11, 10, 174, 55, 11, 10, 14, 30, 11, 10, 22, 95, 11, 10, 15, 14, 11, 10, 14, 46, 11,
  10, 6431, 15, 11, 10, 15, 14, 11, 10, 22, 167, 11, 10, 23, 15, 11, 10, 70, 23, 11, 10, 14, 54, 11, 10,
  6455, 959, 11, 10, 15, 14, 11, 10, 14, 22, 11, 10, 94, 15, 11, 10, 15, 14, 11, 10, 2878, 3238, 11, 10, 30,
  15, 11, 10, 23, 22, 11, 10, 14, 23, 11, 10, 54, 31, 11, 10, 15, 14, 11, 10, 14, 30, 11, 10, 55, 15]

theorem verified64 : check 6401 witnesses64 = true := by decide +kernel

theorem exclude64 (n : Nat) (lo : 6401 ≤ n) (hi : n < 6501) : ¬ Candidate n := by
  apply check_sound witnesses64 6401 n verified64 lo
  exact hi

def witnesses65 : List Nat := [
  11, 10, 15, 14, 11, 10, 966, 95, 11, 10, 47, 15, 11, 10, 22, 79, 11, 10, 14, 22, 11, 10, 31, 30, 11,
  10, 15, 14, 11, 10, 14, 94, 11, 10, 22, 15, 11, 10, 15, 14, 11, 10, 1639, 23, 11, 10, 6551, 15, 11, 10,
  31, 30, 11, 10, 14, 46, 11, 10, 23, 325, 324, 10, 15, 14, 11, 10, 14, 3286, 11, 10, 127, 15, 11, 10, 15,
  14, 11, 10, 23, 22, 11, 10, 118, 15, 11, 10, 30, 47, 11, 10, 14, 79, 11, 10, 22, 70, 11, 10, 15, 14]

theorem verified65 : check 6501 witnesses65 = true := by decide +kernel

theorem exclude65 (n : Nat) (lo : 6501 ≤ n) (hi : n < 6601) : ¬ Candidate n := by
  apply check_sound witnesses65 6501 n verified65 lo
  exact hi

def witnesses66 : List Nat := [
  11, 10, 14, 23, 11, 10, 31, 15, 11, 10, 15, 14, 11, 10, 22, 55, 11, 10, 23, 15, 11, 10, 95, 94, 11,
  10, 14, 31, 11, 10, 78, 47, 11, 10, 15, 14, 11, 10, 14, 22, 11, 10, 30, 15, 11, 10, 15, 14, 11, 10,
  2958, 6654, 11, 10, 22, 15, 11, 10, 23, 22, 11, 10, 14, 23, 11, 10, 238, 55, 11, 10, 15, 14, 11, 10, 14,
  47, 11, 10, 23, 15, 11, 10, 15, 14, 11, 10, 47, 46, 11, 10, 31, 15, 11, 10, 22, 126, 11, 10, 14, 270]

theorem verified66 : check 6601 witnesses66 = true := by decide +kernel

theorem exclude66 (n : Nat) (lo : 6601 ≤ n) (hi : n < 6701) : ¬ Candidate n := by
  apply check_sound witnesses66 6601 n verified66 lo
  exact hi

def witnesses67 : List Nat := [
  11, 10, 1679, 23, 11, 10, 15, 14, 11, 10, 14, 551, 11, 10, 22, 15, 11, 10, 15, 14, 11, 10, 329, 328, 11,
  10, 30, 15, 11, 10, 47, 46, 11, 10, 14, 1686, 11, 10, 23, 22, 11, 10, 15, 14, 11, 10, 14, 30, 11, 10,
  174, 15, 11, 10, 15, 14, 11, 10, 23, 22, 11, 10, 79, 15, 11, 10, 191, 31, 11, 10, 14, 55, 11, 10, 31,
  30, 11, 10, 15, 14, 11, 10, 14, 23, 11, 10, 46, 15, 11, 10, 15, 14, 11, 10, 22, 31, 11, 10, 54, 15]

theorem verified67 : check 6701 witnesses67 = true := by decide +kernel

theorem exclude67 (n : Nat) (lo : 6701 ≤ n) (hi : n < 6801) : ¬ Candidate n := by
  apply check_sound witnesses67 6701 n verified67 lo
  exact hi

def witnesses68 : List Nat := [
  11, 10, 31, 23, 11, 10, 14, 47, 11, 10, 55, 54, 11, 10, 15, 14, 11, 10, 14, 22, 11, 10, 3415, 15, 11,
  10, 15, 14, 11, 10, 31, 30, 11, 10, 22, 15, 11, 10, 23, 22, 11, 10, 14, 23, 11, 10, 166, 430, 11, 10,
  15, 14, 11, 10, 14, 3430, 11, 10, 23, 15, 11, 10, 15, 14, 11, 10, 30, 70, 11, 10, 3439, 15, 11, 10, 46,
  55, 11, 10, 14, 22, 11, 10, 6887, 23, 11, 10, 15, 333, 332, 10, 14, 247, 11, 10, 22, 15, 11, 10, 15, 14]

theorem verified68 : check 6801 witnesses68 = true := by decide +kernel

theorem exclude68 (n : Nat) (lo : 6801 ≤ n) (hi : n < 6901) : ¬ Candidate n := by
  apply check_sound witnesses68 6801 n verified68 lo
  exact hi

def witnesses69 : List Nat := [
  11, 10, 54, 23, 11, 10, 47, 15, 11, 10, 27646, 127, 11, 10, 14, 30, 11, 10, 23, 22, 11, 10, 15, 14, 11,
  10, 14, 167, 11, 10, 118, 15, 11, 10, 15, 14, 11, 10, 23, 22, 11, 10, 31, 15, 11, 10, 775, 774, 11, 10,
  14, 46, 11, 10, 22, 150, 11, 10, 15, 14, 11, 10, 14, 23, 11, 10, 55, 15, 11, 10, 15, 14, 11, 10, 126,
  438, 11, 10, 23, 15, 11, 10, 391, 23, 11, 10, 14, 119, 11, 10, 79, 31, 11, 10, 15, 14, 11, 10, 14, 30]

theorem verified69 : check 6901 witnesses69 = true := by decide +kernel

theorem exclude69 (n : Nat) (lo : 6901 ≤ n) (hi : n < 7001) : ¬ Candidate n := by
  apply check_sound witnesses69 6901 n verified69 lo
  exact hi

def witnesses70 : List Nat := [
  11, 10, 71, 15, 11, 10, 15, 14, 11, 10, 78, 7014, 11, 10, 22, 15, 11, 10, 23, 22, 11, 10, 14, 1127, 11,
  10, 31, 30, 11, 10, 15, 14, 11, 10, 14, 127, 11, 10, 23, 15, 11, 10, 15, 14, 11, 10, 118, 31, 11, 10,
  46, 15, 11, 10, 337, 336, 11, 10, 14, 22, 11, 10, 30, 23, 11, 10, 15, 14, 11, 10, 14, 47, 11, 10, 119,
  15, 11, 10, 15, 14, 11, 10, 31, 23, 11, 10, 78, 15, 11, 10, 30, 167, 11, 10, 14, 191, 11, 10, 126, 286]

theorem verified70 : check 7001 witnesses70 = true := by decide +kernel

theorem exclude70 (n : Nat) (lo : 7001 ≤ n) (hi : n < 7101) : ¬ Candidate n := by
  apply check_sound witnesses70 7001 n verified70 lo
  exact hi

def witnesses71 : List Nat := [
  11, 10, 15, 14, 11, 10, 14, 7110, 11, 10, 31, 15, 11, 10, 15, 14, 11, 10, 23, 22, 11, 10, 55, 15, 11,
  10, 47, 46, 11, 10, 14, 31, 11, 10, 22, 55, 11, 10, 15, 14, 11, 10, 14, 23, 11, 10, 30, 15, 11, 10,
  15, 14, 11, 10, 22, 71, 11, 10, 23, 15, 11, 10, 54, 23, 11, 10, 14, 30, 11, 10, 47, 46, 11, 10, 15,
  14, 11, 10, 14, 22, 11, 10, 46, 15, 11, 10, 15, 14, 11, 10, 70, 118, 11, 10, 22, 15, 11, 10, 94, 79]

theorem verified71 : check 7101 witnesses71 = true := by decide +kernel

theorem exclude71 (n : Nat) (lo : 7101 ≤ n) (hi : n < 7201) : ¬ Candidate n := by
  apply check_sound witnesses71 7101 n verified71 lo
  exact hi

def witnesses72 : List Nat := [
  11, 10, 14, 23, 11, 10, 71, 70, 11, 10, 15, 14, 11, 10, 14, 31, 11, 10, 23, 15, 11, 10, 15, 341, 340,
  10, 46, 54, 11, 10, 30, 15, 11, 10, 22, 270, 11, 10, 14, 22, 11, 10, 7247, 23, 11, 10, 15, 14, 11, 10,
  14, 150, 11, 10, 22, 15, 11, 10, 15, 14, 11, 10, 911, 23, 11, 10, 95, 15, 11, 10, 46, 31, 11, 10, 14,
  70, 11, 10, 23, 22, 11, 10, 15, 14, 11, 10, 14, 151, 11, 10, 94, 15, 11, 10, 15, 14, 11, 10, 295, 294]

theorem verified72 : check 7201 witnesses72 = true := by decide +kernel

theorem exclude72 (n : Nat) (lo : 7201 ≤ n) (hi : n < 7301) : ¬ Candidate n := by
  apply check_sound witnesses72 7201 n verified72 lo
  exact hi

def witnesses73 : List Nat := [
  11, 10, 47, 15, 11, 10, 31, 30, 11, 10, 14, 287, 11, 10, 22, 126, 11, 10, 15, 14, 11, 10, 14, 1175, 11,
  10, 70, 15, 11, 10, 15, 14, 11, 10, 22, 30, 11, 10, 23, 15, 11, 10, 30, 23, 11, 10, 14, 46, 11, 10,
  3679, 79, 11, 10, 15, 14, 11, 10, 14, 22, 11, 10, 31, 15, 11, 10, 15, 14, 11, 10, 30, 78, 11, 10, 238,
  15, 11, 10, 23, 22, 11, 10, 14, 23, 11, 10, 334, 3287, 11, 10, 15, 14, 11, 10, 345, 344, 11, 10, 151, 15]

theorem verified73 : check 7301 witnesses73 = true := by decide +kernel

theorem exclude73 (n : Nat) (lo : 7301 ≤ n) (hi : n < 7401) : ¬ Candidate n := by
  apply check_sound witnesses73 7301 n verified73 lo
  exact hi

def witnesses74 : List Nat := [
  11, 10, 15, 14, 11, 10, 1855, 127, 11, 10, 71, 15, 11, 10, 22, 414, 11, 10, 14, 22, 11, 10, 54, 47, 11,
  10, 15, 14, 11, 10, 14, 3718, 11, 10, 22, 15, 11, 10, 15, 14, 11, 10, 3310, 23, 11, 10, 46, 15, 11, 10,
  95, 94, 11, 10, 14, 934, 11, 10, 23, 22, 11, 10, 15, 14, 11, 10, 14, 31, 11, 10, 126, 15, 11, 10, 15,
  14, 11, 10, 23, 22, 11, 10, 30, 15, 11, 10, 55, 54, 11, 10, 14, 239, 11, 10, 22, 71, 11, 10, 15, 14]

theorem verified74 : check 7401 witnesses74 = true := by decide +kernel

theorem exclude74 (n : Nat) (lo : 7401 ≤ n) (hi : n < 7501) : ¬ Candidate n := by
  apply check_sound witnesses74 7401 n verified74 lo
  exact hi

def witnesses75 : List Nat := [
  11, 10, 14, 23, 11, 10, 7511, 15, 11, 10, 15, 14, 11, 10, 22, 7518, 11, 10, 23, 15, 11, 10, 47, 31, 11,
  10, 14, 3766, 11, 10, 31, 30, 11, 10, 15, 14, 11, 10, 14, 22, 11, 10, 78, 15, 11, 10, 15, 14, 11, 10,
  239, 31, 11, 10, 22, 15, 11, 10, 23, 22, 11, 10, 14, 23, 11, 10, 30, 349, 348, 10, 15, 14, 11, 10, 14,
  3790, 11, 10, 23, 15, 11, 10, 15, 14, 11, 10, 31, 30, 11, 10, 55, 15, 11, 10, 22, 287, 11, 10, 14, 47]

theorem verified75 : check 7501 witnesses75 = true := by decide +kernel

theorem exclude75 (n : Nat) (lo : 7501 ≤ n) (hi : n < 7601) : ¬ Candidate n := by
  apply check_sound witnesses75 7501 n verified75 lo
  exact hi

def witnesses76 : List Nat := [
  11, 10, 7607, 23, 11, 10, 15, 14, 11, 10, 14, 46, 11, 10, 22, 15, 11, 10, 15, 14, 11, 10, 30, 247, 11,
  10, 118, 15, 11, 10, 54, 71, 11, 10, 14, 31, 11, 10, 23, 22, 11, 10, 15, 14, 11, 10, 14, 958, 11, 10,
  30, 15, 11, 10, 15, 14, 11, 10, 23, 22, 11, 10, 318, 15, 11, 10, 46, 286, 11, 10, 14, 30, 11, 10, 79,
  78, 11, 10, 15, 14, 11, 10, 14, 23, 11, 10, 30750, 15, 11, 10, 15, 14, 11, 10, 22, 54, 11, 10, 31, 15]

theorem verified76 : check 7601 witnesses76 = true := by decide +kernel

theorem exclude76 (n : Nat) (lo : 7601 ≤ n) (hi : n < 7701) : ¬ Candidate n := by
  apply check_sound witnesses76 7601 n verified76 lo
  exact hi

def witnesses77 : List Nat := [
  11, 10, 431, 23, 11, 10, 14, 55, 11, 10, 46, 966, 11, 10, 15, 14, 11, 10, 14, 22, 11, 10, 7727, 15, 11,
  10, 15, 14, 11, 10, 3438, 47, 11, 10, 22, 15, 11, 10, 23, 22, 11, 10, 353, 352, 11, 10, 55, 31, 11, 10,
  15, 14, 11, 10, 14, 30, 11, 10, 23, 15, 11, 10, 15, 14, 11, 10, 3454, 71, 11, 10, 78, 15, 11, 10, 1246,
  31, 11, 10, 14, 22, 11, 10, 31, 23, 11, 10, 15, 14, 11, 10, 14, 1950, 11, 10, 22, 15, 11, 10, 15, 14]

theorem verified77 : check 7701 witnesses77 = true := by decide +kernel

theorem exclude77 (n : Nat) (lo : 7701 ≤ n) (hi : n < 7801) : ¬ Candidate n := by
  apply check_sound witnesses77 7701 n verified77 lo
  exact hi

def witnesses78 : List Nat := [
  11, 10, 7807, 23, 11, 10, 150, 15, 11, 10, 31, 30, 11, 10, 14, 3910, 11, 10, 23, 22, 11, 10, 15, 14, 11,
  10, 14, 78, 11, 10, 47, 15, 11, 10, 15, 14, 11, 10, 23, 22, 11, 10, 46, 15, 11, 10, 30, 191, 11, 10,
  14, 54, 11, 10, 22, 391, 11, 10, 15, 14, 11, 10, 14, 23, 11, 10, 31, 15, 11, 10, 15, 14, 11, 10, 30,
  46, 11, 10, 23, 15, 11, 10, 295, 23, 11, 10, 14, 70, 11, 10, 54, 3511, 11, 10, 15, 14, 11, 10, 14, 318]

theorem verified78 : check 7801 witnesses78 = true := by decide +kernel

theorem exclude78 (n : Nat) (lo : 7801 ≤ n) (hi : n < 7901) : ¬ Candidate n := by
  apply check_sound witnesses78 7801 n verified78 lo
  exact hi

def witnesses79 : List Nat := [
  11, 10, 30, 15, 11, 10, 15, 14, 11, 10, 95, 94, 11, 10, 22, 15, 11, 10, 23, 357, 356, 10, 14, 30, 11,
  10, 3967, 3527, 11, 10, 15, 14, 11, 10, 14, 126, 11, 10, 23, 15, 11, 10, 15, 14, 11, 10, 3534, 7950, 11, 10,
  31, 15, 11, 10, 22, 54, 11, 10, 14, 22, 11, 10, 47, 23, 11, 10, 15, 14, 11, 10, 14, 31, 11, 10, 46,
  15, 11, 10, 15, 14, 11, 10, 1999, 23, 11, 10, 654, 15, 11, 10, 151, 150, 11, 10, 14, 47, 11, 10, 78, 31]

theorem verified79 : check 7901 witnesses79 = true := by decide +kernel

theorem exclude79 (n : Nat) (lo : 7901 ≤ n) (hi : n < 8001) : ¬ Candidate n := by
  apply check_sound witnesses79 7901 n verified79 lo
  exact hi

def witnesses80 : List Nat := [
  11, 10, 15, 14, 11, 10, 14, 30, 11, 10, 8015, 15, 11, 10, 15, 14, 11, 10, 23, 22, 11, 10, 71, 15, 11,
  10, 94, 31, 11, 10, 14, 119, 11, 10, 22, 79, 11, 10, 15, 14, 11, 10, 14, 23, 11, 10, 54, 15, 11, 10,
  15, 14, 11, 10, 22, 31, 11, 10, 23, 15, 11, 10, 31, 23, 11, 10, 14, 8070, 11, 10, 30, 55, 11, 10, 15,
  14, 11, 10, 14, 22, 11, 10, 175, 15, 11, 10, 15, 14, 11, 10, 31, 30, 11, 10, 22, 15, 11, 10, 361, 360]

theorem verified80 : check 8001 witnesses80 = true := by decide +kernel

theorem exclude80 (n : Nat) (lo : 8001 ≤ n) (hi : n < 8101) : ¬ Candidate n := by
  apply check_sound witnesses80 8001 n verified80 lo
  exact hi

def witnesses81 : List Nat := [
  11, 10, 14, 23, 11, 10, 270, 71, 11, 10, 15, 14, 11, 10, 14, 8118, 11, 10, 23, 15, 11, 10, 15, 14, 11,
  10, 30, 47, 11, 10, 79, 15, 11, 10, 22, 319, 11, 10, 14, 22, 11, 10, 70, 23, 11, 10, 15, 14, 11, 10,
  14, 127, 11, 10, 22, 15, 11, 10, 15, 14, 11, 10, 55, 23, 11, 10, 4087, 15, 11, 10, 911, 47, 11, 10, 14,
  30, 11, 10, 23, 22, 11, 10, 15, 14, 11, 10, 14, 79, 11, 10, 32766, 15, 11, 10, 15, 14, 11, 10, 167, 166]

theorem verified81 : check 8101 witnesses81 = true := by decide +kernel

theorem exclude81 (n : Nat) (lo : 8101 ≤ n) (hi : n < 8201) : ¬ Candidate n := by
  apply check_sound witnesses81 8101 n verified81 lo
  exact hi

def witnesses82 : List Nat := [
  11, 10, 31, 15, 11, 10, 79, 78, 11, 10, 14, 175, 11, 10, 22, 47, 11, 10, 15, 14, 11, 10, 14, 31, 11,
  10, 71, 15, 11, 10, 15, 14, 11, 10, 22, 118, 11, 10, 23, 15, 11, 10, 919, 23, 11, 10, 14, 295, 11, 10,
  150, 31, 11, 10, 15, 14, 11, 10, 14, 22, 11, 10, 4135, 15, 11, 10, 15, 14, 11, 10, 47, 46, 11, 10, 1326,
  15, 11, 10, 23, 365, 364, 10, 14, 23, 11, 10, 31, 30, 11, 10, 15, 14, 11, 10, 14, 70, 11, 10, 174, 15]

theorem verified82 : check 8201 witnesses82 = true := by decide +kernel

theorem exclude82 (n : Nat) (lo : 8201 ≤ n) (hi : n < 8301) : ¬ Candidate n := by
  apply check_sound witnesses82 8201 n verified82 lo
  exact hi

def witnesses83 : List Nat := [
  11, 10, 15, 14, 11, 10, 54, 31, 11, 10, 4159, 15, 11, 10, 22, 30, 11, 10, 14, 22, 11, 10, 30, 151, 11,
  10, 15, 14, 11, 10, 14, 55, 11, 10, 22, 15, 11, 10, 15, 14, 11, 10, 31, 23, 11, 10, 70, 15, 11, 10,
  30, 118, 11, 10, 14, 247, 11, 10, 23, 22, 11, 10, 15, 14, 11, 10, 14, 2094, 11, 10, 31, 15, 11, 10, 15,
  14, 11, 10, 23, 22, 11, 10, 334, 15, 11, 10, 935, 934, 11, 10, 14, 31, 11, 10, 22, 1247, 11, 10, 15, 14]

theorem verified83 : check 8301 witnesses83 = true := by decide +kernel

theorem exclude83 (n : Nat) (lo : 8301 ≤ n) (hi : n < 8401) : ¬ Candidate n := by
  apply check_sound witnesses83 8301 n verified83 lo
  exact hi

def witnesses84 : List Nat := [
  11, 10, 14, 23, 11, 10, 30, 15, 11, 10, 15, 14, 11, 10, 22, 79, 11, 10, 23, 15, 11, 10, 55, 54, 11,
  10, 14, 174, 11, 10, 71, 70, 11, 10, 15, 14, 11, 10, 14, 22, 11, 10, 8447, 15, 11, 10, 15, 14, 11, 10,
  1254, 319, 11, 10, 22, 15, 11, 10, 23, 22, 11, 10, 369, 368, 11, 10, 119, 118, 11, 10, 15, 14, 11, 10, 14,
  54, 11, 10, 23, 15, 11, 10, 15, 14, 11, 10, 94, 55, 11, 10, 30, 15, 11, 10, 22, 119, 11, 10, 14, 70]

theorem verified84 : check 8401 witnesses84 = true := by decide +kernel

theorem exclude84 (n : Nat) (lo : 8401 ≤ n) (hi : n < 8501) : ¬ Candidate n := by
  apply check_sound witnesses84 8401 n verified84 lo
  exact hi

def witnesses85 : List Nat := [
  11, 10, 46, 23, 11, 10, 15, 14, 11, 10, 14, 30, 11, 10, 22, 15, 11, 10, 15, 14, 11, 10, 3790, 47, 11,
  10, 55, 15, 11, 10, 78, 31, 11, 10, 14, 46, 11, 10, 23, 22, 11, 10, 15, 14, 11, 10, 14, 335, 11, 10,
  70, 15, 11, 10, 15, 14, 11, 10, 23, 22, 11, 10, 8567, 15, 11, 10, 31, 30, 11, 10, 14, 8574, 11, 10, 271,
  270, 11, 10, 15, 14, 11, 10, 14, 23, 11, 10, 79, 15, 11, 10, 15, 14, 11, 10, 22, 30, 11, 10, 175, 15]

theorem verified85 : check 8501 witnesses85 = true := by decide +kernel

theorem exclude85 (n : Nat) (lo : 8501 ≤ n) (hi : n < 8601) : ¬ Candidate n := by
  apply check_sound witnesses85 8501 n verified85 lo
  exact hi

def witnesses86 : List Nat := [
  11, 10, 30, 23, 11, 10, 14, 1078, 11, 10, 318, 47, 11, 10, 15, 14, 11, 10, 14, 22, 11, 10, 47, 15, 11,
  10, 15, 14, 11, 10, 30, 54, 11, 10, 22, 15, 11, 10, 23, 22, 11, 10, 14, 23, 11, 10, 95, 373, 372, 10,
  15, 14, 11, 10, 14, 47, 11, 10, 23, 15, 11, 10, 15, 14, 11, 10, 47, 46, 11, 10, 54, 15, 11, 10, 967,
  966, 11, 10, 14, 22, 11, 10, 55, 23, 11, 10, 15, 14, 11, 10, 14, 166, 11, 10, 22, 15, 11, 10, 15, 14]

theorem verified86 : check 8601 witnesses86 = true := by decide +kernel

theorem exclude86 (n : Nat) (lo : 8601 ≤ n) (hi : n < 8701) : ¬ Candidate n := by
  apply check_sound witnesses86 8601 n verified86 lo
  exact hi

def witnesses87 : List Nat := [
  11, 10, 71, 23, 11, 10, 31, 15, 11, 10, 126, 34855, 11, 10, 14, 95, 11, 10, 23, 22, 11, 10, 15, 14, 11,
  10, 14, 31, 11, 10, 151, 15, 11, 10, 15, 14, 11, 10, 23, 22, 11, 10, 30, 15, 11, 10, 34990, 55, 11, 10,
  14, 2190, 11, 10, 22, 31, 11, 10, 15, 14, 11, 10, 14, 23, 11, 10, 46, 15, 11, 10, 15, 14, 11, 10, 54,
  271, 11, 10, 23, 15, 11, 10, 247, 23, 11, 10, 14, 47, 11, 10, 31, 30, 11, 10, 15, 14, 11, 10, 14, 46]

theorem verified87 : check 8701 witnesses87 = true := by decide +kernel

theorem exclude87 (n : Nat) (lo : 8701 ≤ n) (hi : n < 8801) : ¬ Candidate n := by
  apply check_sound witnesses87 8701 n verified87 lo
  exact hi

def witnesses88 : List Nat := [
  11, 10, 127, 15, 11, 10, 15, 14, 11, 10, 46, 31, 11, 10, 22, 15, 11, 10, 23, 22, 11, 10, 14, 1415, 11,
  10, 30, 439, 11, 10, 15, 14, 11, 10, 377, 376, 11, 10, 23, 15, 11, 10, 15, 14, 11, 10, 31, 30, 11, 10,
  214, 15, 11, 10, 22, 71, 11, 10, 14, 22, 11, 10, 1111, 23, 11, 10, 15, 14, 11, 10, 14, 79, 11, 10, 31,
  15, 11, 10, 15, 14, 11, 10, 30, 23, 11, 10, 47, 15, 11, 10, 55, 54, 11, 10, 14, 31, 11, 10, 46, 95]

theorem verified88 : check 8801 witnesses88 = true := by decide +kernel

theorem exclude88 (n : Nat) (lo : 8801 ≤ n) (hi : n < 8901) : ¬ Candidate n := by
  apply check_sound witnesses88 8801 n verified88 lo
  exact hi

def witnesses89 : List Nat := [
  11, 10, 15, 14, 11, 10, 14, 70, 11, 10, 30, 15, 11, 10, 15, 14, 11, 10, 23, 22, 11, 10, 95, 15, 11,
  10, 127, 126, 11, 10, 14, 30, 11, 10, 22, 1327, 11, 10, 15, 14, 11, 10, 14, 23, 11, 10, 94, 15, 11, 10,
  15, 14, 11, 10, 22, 215, 11, 10, 23, 15, 11, 10, 335, 23, 11, 10, 14, 78, 11, 10, 8975, 3991, 11, 10, 15,
  14, 11, 10, 14, 22, 11, 10, 54, 15, 11, 10, 15, 14, 11, 10, 150, 71, 11, 10, 22, 15, 11, 10, 35998, 36007]

theorem verified89 : check 8901 witnesses89 = true := by decide +kernel

theorem exclude89 (n : Nat) (lo : 8901 ≤ n) (hi : n < 9001) : ¬ Candidate n := by
  apply check_sound witnesses89 8901 n verified89 lo
  exact hi

def witnesses90 : List Nat := [
  11, 10, 14, 23, 11, 10, 2255, 31, 11, 10, 15, 14, 11, 10, 14, 94, 11, 10, 23, 15, 11, 10, 15, 381, 380,
  10, 70, 150, 11, 10, 46, 15, 11, 10, 22, 31, 11, 10, 14, 22, 11, 10, 31, 23, 11, 10, 15, 14, 11, 10,
  14, 47, 11, 10, 22, 15, 11, 10, 15, 14, 11, 10, 47, 23, 11, 10, 9071, 15, 11, 10, 31, 30, 11, 10, 14,
  119, 11, 10, 23, 22, 11, 10, 15, 14, 11, 10, 14, 247, 11, 10, 9095, 15, 11, 10, 15, 14, 11, 10, 31, 30]

theorem verified90 : check 9001 witnesses90 = true := by decide +kernel

theorem exclude90 (n : Nat) (lo : 9001 ≤ n) (hi : n < 9101) : ¬ Candidate n := by
  apply check_sound witnesses90 9001 n verified90 lo
  exact hi

def witnesses91 : List Nat := [
  11, 10, 2279, 15, 11, 10, 30, 46, 11, 10, 14, 55, 11, 10, 22, 174, 11, 10, 15, 14, 11, 10, 14, 295, 11,
  10, 31, 15, 11, 10, 15, 14, 11, 10, 22, 2286, 11, 10, 23, 15, 11, 10, 166, 23, 11, 10, 14, 31, 11, 10,
  47, 46, 11, 10, 15, 14, 11, 10, 14, 22, 11, 10, 46, 15, 11, 10, 15, 14, 11, 10, 4078, 9174, 11, 10, 127,
  15, 11, 10, 23, 22, 11, 10, 14, 23, 11, 10, 9191, 4087, 11, 10, 15, 14, 11, 10, 14, 71, 11, 10, 95, 15]

theorem verified91 : check 9101 witnesses91 = true := by decide +kernel

theorem exclude91 (n : Nat) (lo : 9101 ≤ n) (hi : n < 9201) : ¬ Candidate n := by
  apply check_sound witnesses91 9101 n verified91 lo
  exact hi

def witnesses92 : List Nat := [
  11, 10, 15, 14, 11, 10, 46, 4606, 11, 10, 191, 15, 11, 10, 385, 384, 11, 10, 14, 22, 11, 10, 94, 167, 11,
  10, 15, 14, 11, 10, 14, 31, 11, 10, 22, 15, 11, 10, 15, 14, 11, 10, 54, 23, 11, 10, 30, 15, 11, 10,
  46, 79, 11, 10, 14, 54, 11, 10, 23, 22, 11, 10, 15, 14, 11, 10, 14, 30, 11, 10, 79, 15, 11, 10, 15,
  14, 11, 10, 23, 22, 11, 10, 47, 15, 11, 10, 150, 31, 11, 10, 14, 94, 11, 10, 22, 30, 11, 10, 15, 14]

theorem verified92 : check 9201 witnesses92 = true := by decide +kernel

theorem exclude92 (n : Nat) (lo : 9201 ≤ n) (hi : n < 9301) : ¬ Candidate n := by
  apply check_sound witnesses92 9201 n verified92 lo
  exact hi

def witnesses93 : List Nat := [
  11, 10, 14, 23, 11, 10, 55, 15, 11, 10, 15, 14, 11, 10, 22, 31, 11, 10, 23, 15, 11, 10, 31, 30, 11,
  10, 14, 46, 11, 10, 30, 71, 11, 10, 15, 14, 11, 10, 14, 22, 11, 10, 295, 15, 11, 10, 15, 14, 11, 10,
  31, 30, 11, 10, 22, 15, 11, 10, 23, 22, 11, 10, 14, 23, 11, 10, 70, 1391, 11, 10, 15, 14, 11, 10, 14,
  1174, 11, 10, 23, 15, 11, 10, 15, 14, 11, 10, 30, 167, 11, 10, 2351, 15, 11, 10, 22, 118, 11, 10, 14, 31]

theorem verified93 : check 9301 witnesses93 = true := by decide +kernel

theorem exclude93 (n : Nat) (lo : 9301 ≤ n) (hi : n < 9401) : ¬ Candidate n := by
  apply check_sound witnesses93 9301 n verified93 lo
  exact hi

def witnesses94 : List Nat := [
  11, 10, 9407, 23, 11, 10, 15, 389, 388, 10, 14, 54, 11, 10, 22, 15, 11, 10, 15, 14, 11, 10, 79, 55, 11,
  10, 46, 15, 11, 10, 527, 526, 11, 10, 14, 30, 11, 10, 23, 22, 11, 10, 15, 14, 11, 10, 14, 47, 11, 10,
  54, 15, 11, 10, 15, 14, 11, 10, 23, 22, 11, 10, 31, 15, 11, 10, 1055, 71, 11, 10, 14, 150, 11, 10, 95,
  55, 11, 10, 15, 14, 11, 10, 14, 23, 11, 10, 214, 15, 11, 10, 15, 14, 11, 10, 22, 4750, 11, 10, 30, 15]

theorem verified94 : check 9401 witnesses94 = true := by decide +kernel

theorem exclude94 (n : Nat) (lo : 9401 ≤ n) (hi : n < 9501) : ¬ Candidate n := by
  apply check_sound witnesses94 9401 n verified94 lo
  exact hi

def witnesses95 : List Nat := [
  11, 10, 47, 23, 11, 10, 14, 151, 11, 10, 119, 31, 11, 10, 15, 14, 11, 10, 14, 22, 11, 10, 358, 15, 11,
  10, 15, 14, 11, 10, 1414, 9534, 11, 10, 22, 15, 11, 10, 23, 22, 11, 10, 14, 23, 11, 10, 31, 30, 11, 10,
  15, 14, 11, 10, 14, 79, 11, 10, 23, 15, 11, 10, 15, 14, 11, 10, 55, 31, 11, 10, 70, 15, 11, 10, 31,
  30, 11, 10, 14, 22, 11, 10, 30, 23, 11, 10, 15, 14, 11, 10, 14, 46, 11, 10, 22, 15, 11, 10, 15, 14]

theorem verified95 : check 9501 witnesses95 = true := by decide +kernel

theorem exclude95 (n : Nat) (lo : 9501 ≤ n) (hi : n < 9601) : ¬ Candidate n := by
  apply check_sound witnesses95 9501 n verified95 lo
  exact hi

def witnesses96 : List Nat := [
  11, 10, 393, 392, 11, 10, 54, 15, 11, 10, 30, 358, 11, 10, 14, 239, 11, 10, 23, 22, 11, 10, 15, 14, 11,
  10, 14, 118, 11, 10, 31, 15, 11, 10, 15, 14, 11, 10, 23, 22, 11, 10, 9647, 15, 11, 10, 46, 270, 11, 10,
  14, 78, 11, 10, 22, 70, 11, 10, 15, 14, 11, 10, 14, 23, 11, 10, 30, 15, 11, 10, 15, 14, 11, 10, 167,
  166, 11, 10, 23, 15, 11, 10, 94, 23, 11, 10, 14, 30, 11, 10, 46, 1439, 11, 10, 15, 14, 11, 10, 14, 359]

theorem verified96 : check 9601 witnesses96 = true := by decide +kernel

theorem exclude96 (n : Nat) (lo : 9601 ≤ n) (hi : n < 9701) : ¬ Candidate n := by
  apply check_sound witnesses96 9601 n verified96 lo
  exact hi

def witnesses97 : List Nat := [
  11, 10, 126, 15, 11, 10, 15, 14, 11, 10, 54, 47, 11, 10, 22, 15, 11, 10, 23, 22, 11, 10, 14, 46, 11,
  10, 79, 78, 11, 10, 15, 14, 11, 10, 14, 31, 11, 10, 23, 15, 11, 10, 15, 14, 11, 10, 9751, 9750, 11, 10,
  95, 15, 11, 10, 22, 47, 11, 10, 14, 22, 11, 10, 54, 23, 11, 10, 15, 14, 11, 10, 14, 30, 11, 10, 55,
  15, 11, 10, 15, 14, 11, 10, 4350, 23, 11, 10, 9791, 15, 11, 10, 71, 31, 11, 10, 14, 126, 11, 10, 166, 397]

theorem verified97 : check 9701 witnesses97 = true := by decide +kernel

theorem exclude97 (n : Nat) (lo : 9701 ≤ n) (hi : n < 9801) : ¬ Candidate n := by
  apply check_sound witnesses97 9701 n verified97 lo
  exact hi

def witnesses98 : List Nat := [
  396, 10, 15, 14, 11, 10, 14, 71, 11, 10, 47, 15, 11, 10, 15, 14, 11, 10, 23, 22, 11, 10, 46, 15, 11,
  10, 31, 30, 11, 10, 14, 4918, 11, 10, 22, 4375, 11, 10, 15, 14, 11, 10, 14, 23, 11, 10, 174, 15, 11, 10,
  15, 14, 11, 10, 22, 30, 11, 10, 23, 15, 11, 10, 30, 23, 11, 10, 14, 287, 11, 10, 2471, 2470, 11, 10, 15,
  14, 11, 10, 14, 22, 11, 10, 31, 15, 11, 10, 15, 14, 11, 10, 30, 55, 11, 10, 22, 15, 11, 10, 47, 46]

theorem verified98 : check 9801 witnesses98 = true := by decide +kernel

theorem exclude98 (n : Nat) (lo : 9801 ≤ n) (hi : n < 9901) : ¬ Candidate n := by
  apply check_sound witnesses98 9801 n verified98 lo
  exact hi

def witnesses99 : List Nat := [
  11, 10, 14, 23, 11, 10, 9911, 1471, 11, 10, 15, 14, 11, 10, 14, 150, 11, 10, 23, 15, 11, 10, 15, 14, 11,
  10, 71, 70, 11, 10, 55, 15, 11, 10, 22, 79, 11, 10, 14, 22, 11, 10, 47, 23, 11, 10, 15, 14, 11, 10,
  14, 151, 11, 10, 22, 15, 11, 10, 15, 14, 11, 10, 166, 23, 11, 10, 31, 15, 11, 10, 238, 1110, 11, 10, 14,
  47, 11, 10, 23, 22, 11, 10, 15, 14, 11, 10, 14, 31, 11, 10, 390, 15, 11, 10, 15, 14, 11, 10, 401, 400]

theorem verified99 : check 9901 witnesses99 = true := by decide +kernel

theorem exclude99 (n : Nat) (lo : 9901 ≤ n) (hi : n < 10001) : ¬ Candidate n := by
  apply check_sound witnesses99 9901 n verified99 lo
  exact hi

def witnesses100 : List Nat := [
  11, 10, 30, 15, 11, 10, 559, 558, 11, 10, 14, 71, 11, 10, 22, 31, 11, 10, 15, 14, 11, 10, 14, 30, 11,
  10, 95, 15, 11, 10, 15, 14, 11, 10, 22, 54, 11, 10, 23, 15, 11, 10, 127, 23, 11, 10, 14, 55, 11, 10,
  31, 30, 11, 10, 15, 14, 11, 10, 14, 22, 11, 10, 71, 15, 11, 10, 15, 14, 11, 10, 1494, 31, 11, 10, 47,
  15, 11, 10, 23, 22, 11, 10, 14, 23, 11, 10, 30, 54, 11, 10, 15, 14, 11, 10, 14, 95, 11, 10, 407, 15]

theorem verified100 : check 10001 witnesses100 = true := by decide +kernel

theorem exclude100 (n : Nat) (lo : 10001 ≤ n) (hi : n < 10101) : ¬ Candidate n := by
  apply check_sound witnesses100 10001 n verified100 lo
  exact hi

def witnesses101 : List Nat := [
  11, 10, 15, 14, 11, 10, 31, 30, 11, 10, 319, 15, 11, 10, 22, 271, 11, 10, 14, 22, 11, 10, 214, 10126, 11,
  10, 15, 14, 11, 10, 14, 70, 11, 10, 22, 15, 11, 10, 15, 14, 11, 10, 94, 23, 11, 10, 175, 15, 11, 10,
  191, 47, 11, 10, 14, 31, 11, 10, 23, 22, 11, 10, 15, 14, 11, 10, 14, 126, 11, 10, 30, 15, 11, 10, 15,
  14, 11, 10, 23, 22, 11, 10, 70, 15, 11, 10, 246, 95, 11, 10, 14, 54, 11, 10, 22, 47, 11, 10, 15, 405]

theorem verified101 : check 10101 witnesses101 = true := by decide +kernel

theorem exclude101 (n : Nat) (lo : 10101 ≤ n) (hi : n < 10201) : ¬ Candidate n := by
  apply check_sound witnesses101 10101 n verified101 lo
  exact hi

def witnesses102 : List Nat := [
  404, 10, 14, 23, 11, 10, 47, 15, 11, 10, 15, 14, 11, 10, 22, 71, 11, 10, 23, 15, 11, 10, 287, 286, 11,
  10, 14, 215, 11, 10, 54, 1519, 11, 10, 15, 14, 11, 10, 14, 22, 11, 10, 55, 15, 11, 10, 15, 14, 11, 10,
  47, 46, 11, 10, 22, 15, 11, 10, 23, 22, 11, 10, 14, 23, 11, 10, 71, 31, 11, 10, 15, 14, 11, 10, 14,
  30, 11, 10, 23, 15, 11, 10, 15, 14, 11, 10, 510, 2574, 11, 10, 127, 15, 11, 10, 22, 31, 11, 10, 14, 414]

theorem verified102 : check 10201 witnesses102 = true := by decide +kernel

theorem exclude102 (n : Nat) (lo : 10201 ≤ n) (hi : n < 10301) : ¬ Candidate n := by
  apply check_sound witnesses102 10201 n verified102 lo
  exact hi

def witnesses103 : List Nat := [
  11, 10, 31, 23, 11, 10, 15, 14, 11, 10, 14, 5158, 11, 10, 22, 15, 11, 10, 15, 14, 11, 10, 119, 31, 11,
  10, 94, 15, 11, 10, 31, 30, 11, 10, 14, 70, 11, 10, 23, 22, 11, 10, 15, 14, 11, 10, 14, 54, 11, 10,
  46, 15, 11, 10, 15, 14, 11, 10, 23, 22, 11, 10, 174, 15, 11, 10, 30, 41479, 11, 10, 14, 47, 11, 10, 334,
  4615, 11, 10, 15, 14, 11, 10, 14, 23, 11, 10, 54, 15, 11, 10, 15, 14, 11, 10, 22, 94, 11, 10, 55, 15]

theorem verified103 : check 10301 witnesses103 = true := by decide +kernel

theorem exclude103 (n : Nat) (lo : 10301 ≤ n) (hi : n < 10401) : ¬ Candidate n := by
  apply check_sound witnesses103 10301 n verified103 lo
  exact hi

def witnesses104 : List Nat := [
  11, 10, 409, 408, 11, 10, 14, 31, 11, 10, 79, 55, 11, 10, 15, 14, 11, 10, 14, 22, 11, 10, 30, 15, 11,
  10, 15, 14, 11, 10, 78, 654, 11, 10, 22, 15, 11, 10, 23, 22, 11, 10, 14, 23, 11, 10, 126, 175, 11, 10,
  15, 14, 11, 10, 14, 5230, 11, 10, 23, 15, 11, 10, 15, 14, 11, 10, 4654, 119, 11, 10, 31, 15, 11, 10, 391,
  390, 11, 10, 14, 22, 11, 10, 46, 23, 11, 10, 15, 14, 11, 10, 14, 31, 11, 10, 22, 15, 11, 10, 15, 14]

theorem verified104 : check 10401 witnesses104 = true := by decide +kernel

theorem exclude104 (n : Nat) (lo : 10401 ≤ n) (hi : n < 10501) : ¬ Candidate n := by
  apply check_sound witnesses104 10401 n verified104 lo
  exact hi

def witnesses105 : List Nat := [
  11, 10, 55, 23, 11, 10, 30, 15, 11, 10, 94, 294, 11, 10, 14, 46, 11, 10, 23, 22, 11, 10, 15, 14, 11,
  10, 14, 30, 11, 10, 10535, 15, 11, 10, 15, 14, 11, 10, 23, 22, 11, 10, 54, 15, 11, 10, 214, 31, 11, 10,
  14, 247, 11, 10, 22, 30, 11, 10, 15, 14, 11, 10, 14, 23, 11, 10, 5287, 15, 11, 10, 15, 14, 11, 10, 190,
  31, 11, 10, 23, 15, 11, 10, 78, 23, 11, 10, 14, 10590, 11, 10, 30, 47, 11, 10, 15, 14, 11, 10, 14, 214]

theorem verified105 : check 10501 witnesses105 = true := by decide +kernel

theorem exclude105 (n : Nat) (lo : 10501 ≤ n) (hi : n < 10601) : ¬ Candidate n := by
  apply check_sound witnesses105 10501 n verified105 lo
  exact hi

def witnesses106 : List Nat := [
  11, 10, 47, 15, 11, 10, 15, 413, 412, 10, 31, 30, 11, 10, 22, 15, 11, 10, 23, 22, 11, 10, 14, 71, 11,
  10, 10631, 4727, 11, 10, 15, 14, 11, 10, 14, 47, 11, 10, 23, 15, 11, 10, 15, 14, 11, 10, 30, 95, 11, 10,
  10655, 15, 11, 10, 22, 150, 11, 10, 14, 22, 11, 10, 127, 23, 11, 10, 15, 14, 11, 10, 14, 55, 11, 10, 30,
  15, 11, 10, 15, 14, 11, 10, 4750, 23, 11, 10, 671, 15, 11, 10, 47, 46, 11, 10, 14, 30, 11, 10, 54, 119]

theorem verified106 : check 10601 witnesses106 = true := by decide +kernel

theorem exclude106 (n : Nat) (lo : 10601 ≤ n) (hi : n < 10701) : ¬ Candidate n := by
  apply check_sound witnesses106 10601 n verified106 lo
  exact hi

def witnesses107 : List Nat := [
  11, 10, 15, 14, 11, 10, 14, 10710, 11, 10, 55, 15, 11, 10, 15, 14, 11, 10, 23, 22, 11, 10, 31, 15, 11,
  10, 70, 598, 11, 10, 14, 10734, 11, 10, 22, 46, 11, 10, 15, 14, 11, 10, 14, 23, 11, 10, 46, 15, 11, 10,
  15, 14, 11, 10, 22, 127, 11, 10, 23, 15, 11, 10, 55, 23, 11, 10, 14, 359, 11, 10, 10775, 31, 11, 10, 15,
  14, 11, 10, 14, 22, 11, 10, 166, 15, 11, 10, 15, 14, 11, 10, 46, 78, 11, 10, 22, 15, 11, 10, 43198, 31]

theorem verified107 : check 10701 witnesses107 = true := by decide +kernel

theorem exclude107 (n : Nat) (lo : 10701 ≤ n) (hi : n < 10801) : ¬ Candidate n := by
  apply check_sound witnesses107 10701 n verified107 lo
  exact hi

def witnesses108 : List Nat := [
  11, 10, 14, 23, 11, 10, 31, 30, 11, 10, 15, 14, 11, 10, 417, 416, 11, 10, 23, 15, 11, 10, 15, 14, 11,
  10, 1606, 55, 11, 10, 2711, 15, 11, 10, 22, 30, 11, 10, 14, 22, 11, 10, 30, 23, 11, 10, 15, 14, 11, 10,
  14, 10854, 11, 10, 22, 15, 11, 10, 15, 14, 11, 10, 31, 23, 11, 10, 47, 15, 11, 10, 30, 335, 11, 10, 14,
  295, 11, 10, 23, 22, 11, 10, 15, 14, 11, 10, 14, 5446, 11, 10, 31, 15, 11, 10, 15, 14, 11, 10, 30, 47]

theorem verified108 : check 10801 witnesses108 = true := by decide +kernel

theorem exclude108 (n : Nat) (lo : 10801 ≤ n) (hi : n < 10901) : ¬ Candidate n := by
  apply check_sound witnesses108 10801 n verified108 lo
  exact hi

def witnesses109 : List Nat := [
  11, 10, 119, 15, 11, 10, 54, 406, 11, 10, 14, 31, 11, 10, 22, 4855, 11, 10, 15, 14, 11, 10, 14, 79, 11,
  10, 894, 15, 11, 10, 15, 14, 11, 10, 22, 5470, 11, 10, 23, 15, 11, 10, 79, 23, 11, 10, 14, 30, 11, 10,
  190, 4871, 11, 10, 15, 14, 11, 10, 14, 22, 11, 10, 78, 15, 11, 10, 15, 14, 11, 10, 55, 54, 11, 10, 1758,
  15, 11, 10, 23, 22, 11, 10, 14, 23, 11, 10, 167, 47, 11, 10, 15, 14, 11, 10, 14, 31, 11, 10, 47, 15]

theorem verified109 : check 10901 witnesses109 = true := by decide +kernel

theorem exclude109 (n : Nat) (lo : 10901 ≤ n) (hi : n < 11001) : ¬ Candidate n := by
  apply check_sound witnesses109 10901 n verified109 lo
  exact hi

def witnesses110 : List Nat := [
  11, 10, 15, 14, 11, 10, 175, 174, 11, 10, 30, 15, 11, 10, 22, 70, 11, 10, 14, 22, 11, 10, 55, 421, 420,
  10, 15, 14, 11, 10, 14, 30, 11, 10, 22, 15, 11, 10, 15, 14, 11, 10, 47, 23, 11, 10, 5527, 15, 11, 10,
  174, 31, 11, 10, 14, 2766, 11, 10, 23, 22, 11, 10, 15, 14, 11, 10, 14, 11070, 11, 10, 695, 15, 11, 10, 15,
  14, 11, 10, 23, 22, 11, 10, 71, 15, 11, 10, 31, 30, 11, 10, 14, 190, 11, 10, 22, 78, 11, 10, 15, 14]

theorem verified110 : check 11001 witnesses110 = true := by decide +kernel

theorem exclude110 (n : Nat) (lo : 11001 ≤ n) (hi : n < 11101) : ¬ Candidate n := by
  apply check_sound witnesses110 11001 n verified110 lo
  exact hi

def witnesses111 : List Nat := [
  11, 10, 14, 23, 11, 10, 118, 15, 11, 10, 15, 14, 11, 10, 22, 30, 11, 10, 23, 15, 11, 10, 415, 359, 11,
  10, 14, 54, 11, 10, 95, 94, 11, 10, 15, 14, 11, 10, 14, 22, 11, 10, 31, 15, 11, 10, 15, 14, 11, 10,
  30, 70, 11, 10, 22, 15, 11, 10, 23, 22, 11, 10, 14, 23, 11, 10, 54, 71, 11, 10, 15, 14, 11, 10, 14,
  46, 11, 10, 23, 15, 11, 10, 15, 14, 11, 10, 46, 271, 11, 10, 126, 15, 11, 10, 22, 1246, 11, 10, 14, 30]

theorem verified111 : check 11101 witnesses111 = true := by decide +kernel

theorem exclude111 (n : Nat) (lo : 11101 ≤ n) (hi : n < 11201) : ¬ Candidate n := by
  apply check_sound witnesses111 11101 n verified111 lo
  exact hi

def witnesses112 : List Nat := [
  11, 10, 70, 23, 11, 10, 15, 14, 11, 10, 14, 11214, 11, 10, 22, 15, 11, 10, 15, 14, 11, 10, 95, 94, 11,
  10, 31, 15, 11, 10, 46, 54, 11, 10, 425, 424, 11, 10, 23, 22, 11, 10, 15, 14, 11, 10, 14, 31, 11, 10,
  119, 15, 11, 10, 15, 14, 11, 10, 23, 22, 11, 10, 30, 15, 11, 10, 78, 239, 11, 10, 14, 5638, 11, 10, 46,
  31, 11, 10, 15, 14, 11, 10, 14, 23, 11, 10, 71, 15, 11, 10, 15, 14, 11, 10, 22, 47, 11, 10, 455, 15]

theorem verified112 : check 11201 witnesses112 = true := by decide +kernel

theorem exclude112 (n : Nat) (lo : 11201 ≤ n) (hi : n < 11301) : ¬ Candidate n := by
  apply check_sound witnesses112 11201 n verified112 lo
  exact hi

def witnesses113 : List Nat := [
  11, 10, 358, 23, 11, 10, 14, 46, 11, 10, 31, 30, 11, 10, 15, 14, 11, 10, 14, 22, 11, 10, 79, 15, 11,
  10, 15, 14, 11, 10, 5038, 31, 11, 10, 22, 15, 11, 10, 23, 22, 11, 10, 14, 23, 11, 10, 30, 55, 11, 10,
  15, 14, 11, 10, 14, 70, 11, 10, 23, 15, 11, 10, 15, 14, 11, 10, 119, 118, 11, 10, 334, 15, 11, 10, 30,
  127, 11, 10, 14, 22, 11, 10, 5695, 23, 11, 10, 15, 14, 11, 10, 14, 358, 11, 10, 22, 15, 11, 10, 15, 14]

theorem verified113 : check 11301 witnesses113 = true := by decide +kernel

theorem exclude113 (n : Nat) (lo : 11301 ≤ n) (hi : n < 11401) : ¬ Candidate n := by
  apply check_sound witnesses113 11301 n verified113 lo
  exact hi

def witnesses114 : List Nat := [
  11, 10, 30, 23, 11, 10, 46, 15, 11, 10, 1271, 407, 11, 10, 14, 935, 11, 10, 23, 22, 11, 10, 15, 14, 11,
  10, 14, 47, 11, 10, 30, 15, 11, 10, 15, 14, 11, 10, 23, 22, 11, 10, 11447, 15, 11, 10, 215, 429, 428, 10,
  14, 30, 11, 10, 22, 79, 11, 10, 15, 14, 11, 10, 14, 23, 11, 10, 191, 15, 11, 10, 15, 14, 11, 10, 70,
  78, 11, 10, 23, 15, 11, 10, 47, 23, 11, 10, 14, 1438, 11, 10, 71, 70, 11, 10, 15, 14, 11, 10, 14, 31]

theorem verified114 : check 11401 witnesses114 = true := by decide +kernel

theorem exclude114 (n : Nat) (lo : 11401 ≤ n) (hi : n < 11501) : ¬ Candidate n := by
  apply check_sound witnesses114 11401 n verified114 lo
  exact hi

def witnesses115 : List Nat := [
  11, 10, 2879, 15, 11, 10, 15, 14, 11, 10, 5118, 119, 11, 10, 22, 15, 11, 10, 23, 22, 11, 10, 14, 174, 11,
  10, 47, 31, 11, 10, 15, 14, 11, 10, 14, 30, 11, 10, 23, 15, 11, 10, 15, 14, 11, 10, 5134, 11550, 11, 10,
  46206, 15, 11, 10, 22, 31, 11, 10, 14, 22, 11, 10, 126, 23, 11, 10, 15, 14, 11, 10, 14, 46, 11, 10, 1854,
  15, 11, 10, 15, 14, 11, 10, 46, 23, 11, 10, 11591, 15, 11, 10, 31, 30, 11, 10, 14, 54, 11, 10, 30, 118]

theorem verified115 : check 11501 witnesses115 = true := by decide +kernel

theorem exclude115 (n : Nat) (lo : 11501 ≤ n) (hi : n < 11601) : ¬ Candidate n := by
  apply check_sound witnesses115 11501 n verified115 lo
  exact hi

def witnesses116 : List Nat := [
  11, 10, 15, 14, 11, 10, 14, 55, 11, 10, 70, 15, 11, 10, 15, 14, 11, 10, 23, 22, 11, 10, 238, 15, 11,
  10, 30, 70, 11, 10, 14, 2910, 11, 10, 22, 1727, 11, 10, 15, 14, 11, 10, 14, 23, 11, 10, 31, 15, 11, 10,
  15, 14, 11, 10, 22, 126, 11, 10, 23, 15, 11, 10, 433, 432, 11, 10, 14, 31, 11, 10, 46, 5191, 11, 10, 15,
  14, 11, 10, 14, 22, 11, 10, 30, 15, 11, 10, 15, 14, 11, 10, 151, 47, 11, 10, 22, 15, 11, 10, 55, 54]

theorem verified116 : check 11601 witnesses116 = true := by decide +kernel

theorem exclude116 (n : Nat) (lo : 11601 ≤ n) (hi : n < 11701) : ¬ Candidate n := by
  apply check_sound witnesses116 11601 n verified116 lo
  exact hi

def witnesses117 : List Nat := [
  11, 10, 14, 23, 11, 10, 94, 5207, 11, 10, 15, 14, 11, 10, 14, 118, 11, 10, 23, 15, 11, 10, 15, 14, 11,
  10, 2935, 151, 11, 10, 31, 15, 11, 10, 22, 391, 11, 10, 14, 22, 11, 10, 1471, 23, 11, 10, 15, 14, 11, 10,
  14, 31, 11, 10, 22, 15, 11, 10, 15, 14, 11, 10, 71, 23, 11, 10, 30, 15, 11, 10, 318, 247, 11, 10, 14,
  94, 11, 10, 23, 22, 11, 10, 15, 14, 11, 10, 14, 30, 11, 10, 47, 15, 11, 10, 15, 14, 11, 10, 78, 238]

theorem verified117 : check 11701 witnesses117 = true := by decide +kernel

theorem exclude117 (n : Nat) (lo : 11701 ≤ n) (hi : n < 11801) : ¬ Candidate n := by
  apply check_sound witnesses117 11701 n verified117 lo
  exact hi

def witnesses118 : List Nat := [
  11, 10, 46, 15, 11, 10, 167, 166, 11, 10, 14, 11814, 11, 10, 22, 30, 11, 10, 15, 14, 11, 10, 14, 47, 11,
  10, 11831, 15, 11, 10, 15, 14, 11, 10, 22, 31, 11, 10, 23, 15, 11, 10, 31, 23, 11, 10, 14, 167, 11, 10,
  30, 1759, 11, 10, 15, 14, 11, 10, 14, 22, 11, 10, 5935, 15, 11, 10, 15, 14, 11, 10, 31, 30, 11, 10, 78,
  15, 11, 10, 23, 437, 436, 10, 14, 23, 11, 10, 2975, 2974, 11, 10, 15, 14, 11, 10, 14, 5950, 11, 10, 31, 15]

theorem verified118 : check 11801 witnesses118 = true := by decide +kernel

theorem exclude118 (n : Nat) (lo : 11801 ≤ n) (hi : n < 11901) : ¬ Candidate n := by
  apply check_sound witnesses118 11801 n verified118 lo
  exact hi

def witnesses119 : List Nat := [
  11, 10, 15, 14, 11, 10, 55, 54, 11, 10, 174, 15, 11, 10, 22, 71, 11, 10, 14, 22, 11, 10, 47, 46, 11,
  10, 15, 14, 11, 10, 14, 78, 11, 10, 22, 15, 11, 10, 15, 14, 11, 10, 5310, 23, 11, 10, 54, 15, 11, 10,
  70, 334, 11, 10, 14, 47, 11, 10, 23, 22, 11, 10, 15, 14, 11, 10, 14, 46, 11, 10, 167, 15, 11, 10, 15,
  14, 11, 10, 23, 22, 11, 10, 31, 15, 11, 10, 151, 79, 11, 10, 14, 271, 11, 10, 22, 127, 11, 10, 15, 14]

theorem verified119 : check 11901 witnesses119 = true := by decide +kernel

theorem exclude119 (n : Nat) (lo : 11901 ≤ n) (hi : n < 12001) : ¬ Candidate n := by
  apply check_sound witnesses119 11901 n verified119 lo
  exact hi

def witnesses120 : List Nat := [
  11, 10, 14, 23, 11, 10, 79, 15, 11, 10, 15, 14, 11, 10, 22, 247, 11, 10, 23, 15, 11, 10, 46, 55, 11,
  10, 14, 95, 11, 10, 191, 31, 11, 10, 15, 14, 11, 10, 14, 22, 11, 10, 12047, 15, 11, 10, 15, 14, 11, 10,
  54, 71, 11, 10, 22, 15, 11, 10, 23, 22, 11, 10, 14, 23, 11, 10, 31, 30, 11, 10, 15, 14, 11, 10, 14,
  55, 11, 10, 23, 15, 11, 10, 15, 14, 11, 10, 70, 31, 11, 10, 430, 15, 11, 10, 22, 30, 11, 10, 441, 440]

theorem verified120 : check 12001 witnesses120 = true := by decide +kernel

theorem exclude120 (n : Nat) (lo : 12001 ≤ n) (hi : n < 12101) : ¬ Candidate n := by
  apply check_sound witnesses120 12001 n verified120 lo
  exact hi

def witnesses121 : List Nat := [
  11, 10, 54, 23, 11, 10, 15, 14, 11, 10, 14, 3030, 11, 10, 22, 15, 11, 10, 15, 14, 11, 10, 31, 30, 11,
  10, 270, 15, 11, 10, 30, 47, 11, 10, 14, 150, 11, 10, 23, 22, 11, 10, 15, 14, 11, 10, 14, 12150, 11, 10,
  118, 15, 11, 10, 15, 14, 11, 10, 23, 22, 11, 10, 12167, 15, 11, 10]

theorem verified121 : check 12101 witnesses121 = true := by decide +kernel

theorem exclude121 (n : Nat) (lo : 12101 ≤ n) (hi : n < 12167) : ¬ Candidate n := by
  apply check_sound witnesses121 12101 n verified121 lo
  exact hi

theorem minimality (n : Nat) (hn : 0 < n) (hlt : n < 12167) : ¬ Candidate n := by

  by_cases h0 : n < 101
  · exact exclude0 n (by omega) h0

  by_cases h1 : n < 201
  · exact exclude1 n (by omega) h1

  by_cases h2 : n < 301
  · exact exclude2 n (by omega) h2

  by_cases h3 : n < 401
  · exact exclude3 n (by omega) h3

  by_cases h4 : n < 501
  · exact exclude4 n (by omega) h4

  by_cases h5 : n < 601
  · exact exclude5 n (by omega) h5

  by_cases h6 : n < 701
  · exact exclude6 n (by omega) h6

  by_cases h7 : n < 801
  · exact exclude7 n (by omega) h7

  by_cases h8 : n < 901
  · exact exclude8 n (by omega) h8

  by_cases h9 : n < 1001
  · exact exclude9 n (by omega) h9

  by_cases h10 : n < 1101
  · exact exclude10 n (by omega) h10

  by_cases h11 : n < 1201
  · exact exclude11 n (by omega) h11

  by_cases h12 : n < 1301
  · exact exclude12 n (by omega) h12

  by_cases h13 : n < 1401
  · exact exclude13 n (by omega) h13

  by_cases h14 : n < 1501
  · exact exclude14 n (by omega) h14

  by_cases h15 : n < 1601
  · exact exclude15 n (by omega) h15

  by_cases h16 : n < 1701
  · exact exclude16 n (by omega) h16

  by_cases h17 : n < 1801
  · exact exclude17 n (by omega) h17

  by_cases h18 : n < 1901
  · exact exclude18 n (by omega) h18

  by_cases h19 : n < 2001
  · exact exclude19 n (by omega) h19

  by_cases h20 : n < 2101
  · exact exclude20 n (by omega) h20

  by_cases h21 : n < 2201
  · exact exclude21 n (by omega) h21

  by_cases h22 : n < 2301
  · exact exclude22 n (by omega) h22

  by_cases h23 : n < 2401
  · exact exclude23 n (by omega) h23

  by_cases h24 : n < 2501
  · exact exclude24 n (by omega) h24

  by_cases h25 : n < 2601
  · exact exclude25 n (by omega) h25

  by_cases h26 : n < 2701
  · exact exclude26 n (by omega) h26

  by_cases h27 : n < 2801
  · exact exclude27 n (by omega) h27

  by_cases h28 : n < 2901
  · exact exclude28 n (by omega) h28

  by_cases h29 : n < 3001
  · exact exclude29 n (by omega) h29

  by_cases h30 : n < 3101
  · exact exclude30 n (by omega) h30

  by_cases h31 : n < 3201
  · exact exclude31 n (by omega) h31

  by_cases h32 : n < 3301
  · exact exclude32 n (by omega) h32

  by_cases h33 : n < 3401
  · exact exclude33 n (by omega) h33

  by_cases h34 : n < 3501
  · exact exclude34 n (by omega) h34

  by_cases h35 : n < 3601
  · exact exclude35 n (by omega) h35

  by_cases h36 : n < 3701
  · exact exclude36 n (by omega) h36

  by_cases h37 : n < 3801
  · exact exclude37 n (by omega) h37

  by_cases h38 : n < 3901
  · exact exclude38 n (by omega) h38

  by_cases h39 : n < 4001
  · exact exclude39 n (by omega) h39

  by_cases h40 : n < 4101
  · exact exclude40 n (by omega) h40

  by_cases h41 : n < 4201
  · exact exclude41 n (by omega) h41

  by_cases h42 : n < 4301
  · exact exclude42 n (by omega) h42

  by_cases h43 : n < 4401
  · exact exclude43 n (by omega) h43

  by_cases h44 : n < 4501
  · exact exclude44 n (by omega) h44

  by_cases h45 : n < 4601
  · exact exclude45 n (by omega) h45

  by_cases h46 : n < 4701
  · exact exclude46 n (by omega) h46

  by_cases h47 : n < 4801
  · exact exclude47 n (by omega) h47

  by_cases h48 : n < 4901
  · exact exclude48 n (by omega) h48

  by_cases h49 : n < 5001
  · exact exclude49 n (by omega) h49

  by_cases h50 : n < 5101
  · exact exclude50 n (by omega) h50

  by_cases h51 : n < 5201
  · exact exclude51 n (by omega) h51

  by_cases h52 : n < 5301
  · exact exclude52 n (by omega) h52

  by_cases h53 : n < 5401
  · exact exclude53 n (by omega) h53

  by_cases h54 : n < 5501
  · exact exclude54 n (by omega) h54

  by_cases h55 : n < 5601
  · exact exclude55 n (by omega) h55

  by_cases h56 : n < 5701
  · exact exclude56 n (by omega) h56

  by_cases h57 : n < 5801
  · exact exclude57 n (by omega) h57

  by_cases h58 : n < 5901
  · exact exclude58 n (by omega) h58

  by_cases h59 : n < 6001
  · exact exclude59 n (by omega) h59

  by_cases h60 : n < 6101
  · exact exclude60 n (by omega) h60

  by_cases h61 : n < 6201
  · exact exclude61 n (by omega) h61

  by_cases h62 : n < 6301
  · exact exclude62 n (by omega) h62

  by_cases h63 : n < 6401
  · exact exclude63 n (by omega) h63

  by_cases h64 : n < 6501
  · exact exclude64 n (by omega) h64

  by_cases h65 : n < 6601
  · exact exclude65 n (by omega) h65

  by_cases h66 : n < 6701
  · exact exclude66 n (by omega) h66

  by_cases h67 : n < 6801
  · exact exclude67 n (by omega) h67

  by_cases h68 : n < 6901
  · exact exclude68 n (by omega) h68

  by_cases h69 : n < 7001
  · exact exclude69 n (by omega) h69

  by_cases h70 : n < 7101
  · exact exclude70 n (by omega) h70

  by_cases h71 : n < 7201
  · exact exclude71 n (by omega) h71

  by_cases h72 : n < 7301
  · exact exclude72 n (by omega) h72

  by_cases h73 : n < 7401
  · exact exclude73 n (by omega) h73

  by_cases h74 : n < 7501
  · exact exclude74 n (by omega) h74

  by_cases h75 : n < 7601
  · exact exclude75 n (by omega) h75

  by_cases h76 : n < 7701
  · exact exclude76 n (by omega) h76

  by_cases h77 : n < 7801
  · exact exclude77 n (by omega) h77

  by_cases h78 : n < 7901
  · exact exclude78 n (by omega) h78

  by_cases h79 : n < 8001
  · exact exclude79 n (by omega) h79

  by_cases h80 : n < 8101
  · exact exclude80 n (by omega) h80

  by_cases h81 : n < 8201
  · exact exclude81 n (by omega) h81

  by_cases h82 : n < 8301
  · exact exclude82 n (by omega) h82

  by_cases h83 : n < 8401
  · exact exclude83 n (by omega) h83

  by_cases h84 : n < 8501
  · exact exclude84 n (by omega) h84

  by_cases h85 : n < 8601
  · exact exclude85 n (by omega) h85

  by_cases h86 : n < 8701
  · exact exclude86 n (by omega) h86

  by_cases h87 : n < 8801
  · exact exclude87 n (by omega) h87

  by_cases h88 : n < 8901
  · exact exclude88 n (by omega) h88

  by_cases h89 : n < 9001
  · exact exclude89 n (by omega) h89

  by_cases h90 : n < 9101
  · exact exclude90 n (by omega) h90

  by_cases h91 : n < 9201
  · exact exclude91 n (by omega) h91

  by_cases h92 : n < 9301
  · exact exclude92 n (by omega) h92

  by_cases h93 : n < 9401
  · exact exclude93 n (by omega) h93

  by_cases h94 : n < 9501
  · exact exclude94 n (by omega) h94

  by_cases h95 : n < 9601
  · exact exclude95 n (by omega) h95

  by_cases h96 : n < 9701
  · exact exclude96 n (by omega) h96

  by_cases h97 : n < 9801
  · exact exclude97 n (by omega) h97

  by_cases h98 : n < 9901
  · exact exclude98 n (by omega) h98

  by_cases h99 : n < 10001
  · exact exclude99 n (by omega) h99

  by_cases h100 : n < 10101
  · exact exclude100 n (by omega) h100

  by_cases h101 : n < 10201
  · exact exclude101 n (by omega) h101

  by_cases h102 : n < 10301
  · exact exclude102 n (by omega) h102

  by_cases h103 : n < 10401
  · exact exclude103 n (by omega) h103

  by_cases h104 : n < 10501
  · exact exclude104 n (by omega) h104

  by_cases h105 : n < 10601
  · exact exclude105 n (by omega) h105

  by_cases h106 : n < 10701
  · exact exclude106 n (by omega) h106

  by_cases h107 : n < 10801
  · exact exclude107 n (by omega) h107

  by_cases h108 : n < 10901
  · exact exclude108 n (by omega) h108

  by_cases h109 : n < 11001
  · exact exclude109 n (by omega) h109

  by_cases h110 : n < 11101
  · exact exclude110 n (by omega) h110

  by_cases h111 : n < 11201
  · exact exclude111 n (by omega) h111

  by_cases h112 : n < 11301
  · exact exclude112 n (by omega) h112

  by_cases h113 : n < 11401
  · exact exclude113 n (by omega) h113

  by_cases h114 : n < 11501
  · exact exclude114 n (by omega) h114

  by_cases h115 : n < 11601
  · exact exclude115 n (by omega) h115

  by_cases h116 : n < 11701
  · exact exclude116 n (by omega) h116

  by_cases h117 : n < 11801
  · exact exclude117 n (by omega) h117

  by_cases h118 : n < 11901
  · exact exclude118 n (by omega) h118

  by_cases h119 : n < 12001
  · exact exclude119 n (by omega) h119

  by_cases h120 : n < 12101
  · exact exclude120 n (by omega) h120

  exact exclude121 n (by omega) hlt

theorem powerful_of_finite {n : Nat} (hn : 0<n)
    (h : (List.range (n+1)).all (fun p => decide (n % p = 0 → Prime p → n % (p*p)=0)) = true) : Powerful n := by
  refine ⟨hn, ?_⟩
  intro p hp hdiv
  have hle := Nat.le_of_dvd hn hdiv
  have hh := List.all_eq_true.mp h p (List.mem_range.mpr (by omega))
  have hh2 := of_decide_eq_true hh
  exact Nat.dvd_iff_mod_eq_zero.mpr (hh2 (Nat.dvd_iff_mod_eq_zero.mp hdiv) hp)

theorem left_powerful : Powerful 12167 := by
  apply powerful_of_finite (by decide)
  decide +kernel

theorem right_powerful : Powerful 12168 := by
  apply powerful_of_finite (by decide)
  decide +kernel

theorem not_square_between {n : Nat} (hl : 12100<n) (hu : n<12321) : ¬ Square n := by
  rintro ⟨k, hk⟩
  by_cases h : k≤110
  · have hm := Nat.mul_le_mul h h
    omega
  · have hh : 111≤k := by omega
    have hm := Nat.mul_le_mul hh hh
    omega

theorem counterexample : Candidate 12167 := by
  exact ⟨left_powerful, right_powerful,
    not_square_between (by decide) (by decide),
    not_square_between (by decide) (by decide)⟩

theorem smallest_counterexample : Candidate 12167 ∧
    ∀ n : Nat, Candidate n → 12167 ≤ n := by
  refine ⟨counterexample, ?_⟩
  intro n hn
  by_cases h : 12167 ≤ n
  · exact h
  · exact False.elim (minimality n hn.1.1 (by omega) hn)

theorem negative_answer : ¬ (∀ n : Nat,
    Powerful n → Powerful (n+1) → Square n ∨ Square (n+1)) := by
  intro h
  rcases h 12167 counterexample.1 counterexample.2.1 with hs | hs
  · exact counterexample.2.2.1 hs
  · exact counterexample.2.2.2 hs

#print axioms prime_iff
#print axioms negative_answer
#print axioms smallest_counterexample
end JSP000301
