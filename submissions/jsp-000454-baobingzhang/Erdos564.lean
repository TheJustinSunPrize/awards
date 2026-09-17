import Mathlib

/-!
# Erdős Problem 564: the Erdős–Hajnal–Rado lower bound `R₃(n) ≥ 2 ^ (c n²)`

Erdős Problem 564 asks whether the `2`-colour Ramsey number `R₃(n)` of the complete
`3`-uniform hypergraph on `n` vertices satisfies `R₃(n) ≥ 2 ^ 2 ^ (c n)` for some `c > 0`
(open). This file proves the known lower bound of Erdős, Hajnal and Rado (1965):
`R₃(n) > 2 ^ (c n²)` for some `c > 0`.

`hypergraphRamsey` is copied verbatim from Google DeepMind's formal-conjectures project
(`FormalConjecturesForMathlib/Combinatorics/Ramsey.lean`, Apache-2.0), placed here in the
namespace `Erdos564` instead of `Combinatorics`.

## Non-vacuity

`hypergraphRamsey r n` is the `sInf` of a set of natural numbers, and `sInf ∅ = 0`. So a lower
bound on it is only meaningful (indeed only true) once the set is nonempty. We prove this
(`hypergraphRamsey_set_nonempty`, for every `r` and `n`) via the finite hypergraph Ramsey
theorem `ramsey_exists`, shown by the usual induction on `r` with the off-diagonal step
`R_{r+1}(a+1, b+1) ≤ R_r(R_{r+1}(a, b+1), R_{r+1}(a+1, b)) + 1`.

## Lower bound (counting)

If `2 · C(m, n) < 2 ^ C(n, 3)` then some colouring `c : Finset (Fin m) → Bool` has no
monochromatic `n`-set: for each `n`-set `S` and colour, the colourings constant on the
`3`-subsets of `S` number `2 ^ (2 ^ m - C(n, 3))`, and the union bound over the `C(m, n)` sets
and `2` colours falls short of all `2 ^ 2 ^ m` colourings. Since `C(k, n)` is monotone in `k`,
no `k ≤ m` lies in the defining set, so `m < hypergraphRamsey 3 n`. With `m = 2 ^ t` and
`2 · C(2 ^ t, n) ≤ (2 ^ t) ^ n` this holds as soon as `t · n < C(n, 3)`.

## Main results

* `Erdos564.hypergraphRamsey_set_nonempty`: the set defining `hypergraphRamsey r n` is nonempty.
* `Erdos564.two_pow_lt_hypergraphRamsey_three`: `t * n < n.choose 3 → 2 ^ t < hypergraphRamsey 3 n`.
* `Erdos564.two_pow_sq_div_twelve_lt_hypergraphRamsey_three`:
  `6 ≤ n → 2 ^ (n ^ 2 / 12) < hypergraphRamsey 3 n`.
* `Erdos564.erdos_564_lower_bound`:
  `∃ c > 0, ∀ᶠ n in atTop, (2 : ℝ) ^ (c * n ^ 2) ≤ hypergraphRamsey 3 n` (with `c = 1/12`).
-/

open Filter

namespace Erdos564

/--
The `r`-uniform hypergraph Ramsey number `R_r(n)`.
The smallest natural number `m` such that every 2-coloring of the `r`-subsets of a set of size `m`
contains a monochromatic subset of size `n`.
-/
noncomputable def hypergraphRamsey (r n : ℕ) : ℕ :=
  sInf { m | ∀ (c : Finset (Fin m) → Bool),
    ∃ (S : Finset (Fin m)), S.card = n ∧
      ∃ (color : Bool), ∀ (e : Finset (Fin m)), e ⊆ S → e.card = r → c e = color }

/-! ### Existence: the finite hypergraph Ramsey theorem -/

/-- Finite off-diagonal hypergraph Ramsey theorem: for all `r a b` there is `N` such that for
every finset `X` with at least `N` elements and every `c : Finset α → Bool`, some `a`-subset of
`X` has all its `r`-subsets coloured `true`, or some `b`-subset has all its `r`-subsets coloured
`false`. -/
theorem ramsey_exists (r : ℕ) :
    ∀ a b : ℕ, ∃ N : ℕ, ∀ {α : Type} [DecidableEq α] (X : Finset α),
      N ≤ X.card → ∀ c : Finset α → Bool,
        (∃ S ⊆ X, S.card = a ∧ ∀ e ⊆ S, e.card = r → c e = true) ∨
        (∃ S ⊆ X, S.card = b ∧ ∀ e ⊆ S, e.card = r → c e = false) := by
  induction r with
  | zero =>
    intro a b
    refine ⟨a + b, fun X hX c => ?_⟩
    cases hc : c ∅ with
    | true =>
      obtain ⟨S, hS, hcard⟩ := Finset.exists_subset_card_eq (show a ≤ X.card by omega)
      exact Or.inl ⟨S, hS, hcard, fun e _ he => by rw [Finset.card_eq_zero.mp he]; exact hc⟩
    | false =>
      obtain ⟨S, hS, hcard⟩ := Finset.exists_subset_card_eq (show b ≤ X.card by omega)
      exact Or.inr ⟨S, hS, hcard, fun e _ he => by rw [Finset.card_eq_zero.mp he]; exact hc⟩
  | succ r ih =>
    intro a
    induction a with
    | zero =>
      intro b
      refine ⟨0, fun X _ c => Or.inl ⟨∅, Finset.empty_subset _, rfl, fun e he hcard => ?_⟩⟩
      simp [Finset.subset_empty.mp he] at hcard
    | succ a iha =>
      intro b
      induction b with
      | zero =>
        refine ⟨0, fun X _ c => Or.inr ⟨∅, Finset.empty_subset _, rfl, fun e he hcard => ?_⟩⟩
        simp [Finset.subset_empty.mp he] at hcard
      | succ b ihb =>
        obtain ⟨N₁, hN₁⟩ := iha (b + 1)
        obtain ⟨N₂, hN₂⟩ := ihb
        obtain ⟨M, hM⟩ := ih N₁ N₂
        refine ⟨M + 1, fun {α} _ X hX c => ?_⟩
        obtain ⟨v, hv⟩ : X.Nonempty := Finset.card_pos.mp (by omega)
        have hX' : M ≤ (X.erase v).card := by rw [Finset.card_erase_of_mem hv]; omega
        -- adding `v` to a set `Z` whose `r`-sets `T` all give `c (insert v T) = col`
        -- and whose `(r+1)`-sets all have colour `col` keeps it monochromatic
        have key : ∀ (col : Bool) (Z : Finset α), Z ⊆ X.erase v →
            (∀ T ⊆ Z, T.card = r → c (insert v T) = col) →
            (∀ e ⊆ Z, e.card = r + 1 → c e = col) →
            insert v Z ⊆ X ∧ (insert v Z).card = Z.card + 1 ∧
              ∀ e ⊆ insert v Z, e.card = r + 1 → c e = col := by
          intro col Z hZX hT hZ
          have hvZ : v ∉ Z := fun h => by simpa using hZX h
          refine ⟨Finset.insert_subset hv (hZX.trans (Finset.erase_subset v X)),
            Finset.card_insert_of_notMem hvZ, fun e he hcard => ?_⟩
          by_cases hve : v ∈ e
          · have h := hT (e.erase v) (fun x hx => ?_)
              (by rw [Finset.card_erase_of_mem hve, hcard]; rfl)
            · rwa [Finset.insert_erase hve] at h
            · obtain ⟨hxv, hxe⟩ := Finset.mem_erase.mp hx
              rcases Finset.mem_insert.mp (he hxe) with h | h
              · exact absurd h hxv
              · exact h
          · refine hZ e (fun x hx => ?_) hcard
            rcases Finset.mem_insert.mp (he hx) with h | h
            · exact absurd (h ▸ hx) hve
            · exact h
        rcases hM (X.erase v) hX' (fun T => c (insert v T)) with
          ⟨Y, hYX, hYcard, hY⟩ | ⟨Y, hYX, hYcard, hY⟩
        · rcases hN₁ Y hYcard.ge c with ⟨Z, hZY, hZcard, hZ⟩ | ⟨Z, hZY, hZcard, hZ⟩
          · obtain ⟨h1, h2, h3⟩ :=
              key true Z (hZY.trans hYX) (fun T hT => hY T (hT.trans hZY)) hZ
            exact Or.inl ⟨insert v Z, h1, by rw [h2, hZcard], h3⟩
          · exact Or.inr ⟨Z, (hZY.trans hYX).trans (Finset.erase_subset v X), hZcard, hZ⟩
        · rcases hN₂ Y hYcard.ge c with ⟨Z, hZY, hZcard, hZ⟩ | ⟨Z, hZY, hZcard, hZ⟩
          · exact Or.inl ⟨Z, (hZY.trans hYX).trans (Finset.erase_subset v X), hZcard, hZ⟩
          · obtain ⟨h1, h2, h3⟩ :=
              key false Z (hZY.trans hYX) (fun T hT => hY T (hT.trans hZY)) hZ
            exact Or.inr ⟨insert v Z, h1, by rw [h2, hZcard], h3⟩

/-- The set whose infimum defines `hypergraphRamsey r n` is nonempty, so `hypergraphRamsey r n`
is a genuine minimum (and not the junk value `sInf ∅ = 0`). -/
theorem hypergraphRamsey_set_nonempty (r n : ℕ) :
    { m | ∀ (c : Finset (Fin m) → Bool),
      ∃ (S : Finset (Fin m)), S.card = n ∧
        ∃ (color : Bool), ∀ (e : Finset (Fin m)), e ⊆ S → e.card = r → c e = color }.Nonempty := by
  obtain ⟨N, hN⟩ := ramsey_exists r n n
  refine ⟨N, fun c => ?_⟩
  rcases hN (Finset.univ : Finset (Fin N)) (by simp) c with ⟨S, -, hS, hc⟩ | ⟨S, -, hS, hc⟩
  · exact ⟨S, hS, true, hc⟩
  · exact ⟨S, hS, false, hc⟩

/-! ### Counting colourings -/

/-- The number of `Bool`-valued functions that are constantly `b` on a finset `A` is
`2 ^ (|β| - |A|)`. -/
theorem card_filter_forall_eq {β : Type*} [Fintype β] [DecidableEq β] (A : Finset β) (b : Bool) :
    (Finset.univ.filter (fun f : β → Bool => ∀ x ∈ A, f x = b)).card =
      2 ^ (Fintype.card β - A.card) := by
  rw [← Fintype.card_subtype]
  let e : {f : β → Bool // ∀ x ∈ A, f x = b} ≃ ({x // x ∉ A} → Bool) :=
    { toFun := fun f x => f.1 x.1
      invFun := fun g => ⟨fun x => if h : x ∈ A then b else g ⟨x, h⟩, fun x hx => by simp [hx]⟩
      left_inv := fun f => by
        ext x
        by_cases hx : x ∈ A
        · simp [hx, f.2 x hx]
        · simp [hx]
      right_inv := fun g => by
        ext x
        simp [x.2] }
  rw [Fintype.card_congr e, Fintype.card_fun, Fintype.card_bool, Fintype.card_subtype_compl,
    Fintype.card_coe]

/-- If `2 · C(m, n) < 2 ^ C(n, 3)`, some colouring of the finsets of `Fin m` has no
`n`-set whose `3`-subsets all receive the same colour. -/
theorem exists_coloring_without_monochromatic (m n : ℕ) (h : 2 * m.choose n < 2 ^ n.choose 3) :
    ∃ c : Finset (Fin m) → Bool, ∀ S : Finset (Fin m), S.card = n →
      ∀ color : Bool, ∃ e ⊆ S, e.card = 3 ∧ c e ≠ color := by
  classical
  by_contra hcon
  push Not at hcon
  set K := Fintype.card (Finset (Fin m)) with hK
  let bad : Finset (Fin m) → Bool → Finset (Finset (Fin m) → Bool) := fun S col =>
    Finset.univ.filter (fun f => ∀ e ∈ S.powersetCard 3, f e = col)
  have hsub : (Finset.univ : Finset (Finset (Fin m) → Bool)) ⊆
      ((Finset.univ : Finset (Fin m)).powersetCard n).biUnion
        (fun S => (Finset.univ : Finset Bool).biUnion (bad S)) := by
    intro f _
    obtain ⟨S, hS, col, hcol⟩ := hcon f
    simp only [Finset.mem_biUnion, Finset.mem_powersetCard, Finset.mem_univ, true_and]
    refine ⟨S, ⟨Finset.subset_univ S, hS⟩, col, ?_⟩
    simp only [bad, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_powersetCard]
    exact fun e he => hcol e he.1 he.2
  have hle := Finset.card_le_card hsub
  rw [Finset.card_univ, Fintype.card_fun, Fintype.card_bool, ← hK] at hle
  have hbad : ∀ S ∈ (Finset.univ : Finset (Fin m)).powersetCard n,
      ((Finset.univ : Finset Bool).biUnion (bad S)).card ≤ 2 * 2 ^ (K - n.choose 3) := by
    intro S hS
    have hScard := (Finset.mem_powersetCard.mp hS).2
    refine (Finset.card_biUnion_le).trans ?_
    simp only [bad, card_filter_forall_eq, Finset.card_powersetCard, hScard, ← hK,
      Finset.sum_const, Finset.card_univ, Fintype.card_bool, smul_eq_mul, le_refl]
  have hle2 := hle.trans ((Finset.card_biUnion_le).trans (Finset.sum_le_sum hbad))
  rw [Finset.sum_const, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin,
    smul_eq_mul] at hle2
  rcases Nat.lt_or_ge m n with hmn | hnm
  · rw [Nat.choose_eq_zero_of_lt hmn] at hle2
    simp at hle2
  · have h3 : n.choose 3 ≤ K := by
      rw [hK, Fintype.card_finset, Fintype.card_fin]
      exact (Nat.choose_le_two_pow n 3).trans (Nat.pow_le_pow_right (by norm_num) hnm)
    have : m.choose n * (2 * 2 ^ (K - n.choose 3)) < 2 ^ K := by
      calc m.choose n * (2 * 2 ^ (K - n.choose 3))
          = (2 * m.choose n) * 2 ^ (K - n.choose 3) := by ring
        _ < 2 ^ n.choose 3 * 2 ^ (K - n.choose 3) :=
          Nat.mul_lt_mul_of_pos_right h (by positivity)
        _ = 2 ^ K := by rw [← pow_add, Nat.add_sub_cancel' h3]
    omega

/-! ### Lower bounds for `hypergraphRamsey 3 n` -/

/-- If `2 · C(m, n) < 2 ^ C(n, 3)` then `m < R₃(n)`. -/
theorem lt_hypergraphRamsey_three_of_choose (m n : ℕ) (h : 2 * m.choose n < 2 ^ n.choose 3) :
    m < hypergraphRamsey 3 n := by
  have hmem := Nat.sInf_mem (hypergraphRamsey_set_nonempty 3 n)
  by_contra hle
  push Not at hle
  obtain ⟨c, hc⟩ := exists_coloring_without_monochromatic (hypergraphRamsey 3 n) n
    (lt_of_le_of_lt (Nat.mul_le_mul_left 2 (Nat.choose_le_choose n hle)) h)
  obtain ⟨S, hS, col, hcol⟩ := hmem c
  obtain ⟨e, he, he3, hne⟩ := hc S hS col
  exact hne (hcol e he he3)

/-- **Erdős–Hajnal–Rado**, general form: if `t · n < C(n, 3)` then `2 ^ t < R₃(n)`. -/
theorem two_pow_lt_hypergraphRamsey_three (t n : ℕ) (h : t * n < n.choose 3) :
    2 ^ t < hypergraphRamsey 3 n := by
  apply lt_hypergraphRamsey_three_of_choose
  have hn : 2 ≤ n := by
    by_contra hn
    push Not at hn
    rw [Nat.choose_eq_zero_of_lt (by omega)] at h
    omega
  calc 2 * (2 ^ t).choose n ≤ n.factorial * (2 ^ t).choose n :=
        Nat.mul_le_mul_right _ (hn.trans (Nat.self_le_factorial n))
    _ = (2 ^ t).descFactorial n := (Nat.descFactorial_eq_factorial_mul_choose _ _).symm
    _ ≤ (2 ^ t) ^ n := Nat.descFactorial_le_pow _ _
    _ = 2 ^ (t * n) := (pow_mul 2 t n).symm
    _ < 2 ^ n.choose 3 := Nat.pow_lt_pow_right (by norm_num) h

theorem six_mul_choose_three (k : ℕ) :
    6 * (k + 3).choose 3 = (k + 3) * (k + 2) * (k + 1) := by
  have := Nat.descFactorial_eq_factorial_mul_choose (k + 3) 3
  simp [Nat.descFactorial, Nat.factorial] at this
  linarith

/-- **Erdős–Hajnal–Rado**, explicit form: `2 ^ ⌊n² / 12⌋ < R₃(n)` for `n ≥ 6`. -/
theorem two_pow_sq_div_twelve_lt_hypergraphRamsey_three {n : ℕ} (hn : 6 ≤ n) :
    2 ^ (n ^ 2 / 12) < hypergraphRamsey 3 n := by
  apply two_pow_lt_hypergraphRamsey_three
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 6 := ⟨n - 6, by omega⟩
  have h6 := six_mul_choose_three (k + 3)
  have hq := Nat.div_mul_le_self ((k + 6) ^ 2) 12
  set q := (k + 6) ^ 2 / 12
  have h1 : q * 12 * (k + 6) ≤ (k + 6) ^ 2 * (k + 6) := Nat.mul_le_mul_right _ hq
  nlinarith

/-- **Erdős–Hajnal–Rado (1965)**, asymptotic form: `R₃(n) ≥ 2 ^ (c n²)` for some `c > 0` and all
large `n` (here `c = 1/12`, for `n ≥ 8`). -/
theorem erdos_564_lower_bound :
    ∃ c > (0 : ℝ), ∀ᶠ n : ℕ in atTop, (2 : ℝ) ^ (c * (n : ℝ) ^ 2) ≤ hypergraphRamsey 3 n := by
  refine ⟨1 / 12, by norm_num, eventually_atTop.mpr ⟨8, fun n hn => ?_⟩⟩
  have hlt : 2 ^ (n ^ 2 / 12 + 1) < hypergraphRamsey 3 n := by
    apply two_pow_lt_hypergraphRamsey_three
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 8 := ⟨n - 8, by omega⟩
    have h6 := six_mul_choose_three (k + 5)
    have hq := Nat.div_mul_le_self ((k + 8) ^ 2) 12
    set q := (k + 8) ^ 2 / 12
    have h1 : q * 12 * (k + 8) ≤ (k + 8) ^ 2 * (k + 8) := Nat.mul_le_mul_right _ hq
    nlinarith
  have hx : n ^ 2 < 12 * (n ^ 2 / 12 + 1) := by
    have := Nat.div_add_mod (n ^ 2) 12
    have := Nat.mod_lt (n ^ 2) (show 12 > 0 by norm_num)
    omega
  have hxR : ((n : ℝ) ^ 2) < 12 * ((n ^ 2 / 12 + 1 : ℕ) : ℝ) := by exact_mod_cast hx
  calc (2 : ℝ) ^ (1 / 12 * (n : ℝ) ^ 2)
      ≤ (2 : ℝ) ^ ((n ^ 2 / 12 + 1 : ℕ) : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    _ = ((2 ^ (n ^ 2 / 12 + 1) : ℕ) : ℝ) := by rw [Real.rpow_natCast]; push_cast; ring
    _ ≤ hypergraphRamsey 3 n := by exact_mod_cast hlt.le

end Erdos564
