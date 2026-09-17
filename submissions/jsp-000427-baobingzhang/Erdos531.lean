import Mathlib

/-!
# Erdős Problem 531: `F(k) ≥ 2^(2^(k-1)/k)` for the two-colour Folkman numbers

Erdős Problem 531 ([Er73], https://www.erdosproblems.com/531) reads:

> Let `F(k)` be the minimal `N` such that if we two-colour `{1, …, N}` there is a set `A` of size
> `k` such that all subset sums `∑_{a ∈ S} a` (for `∅ ≠ S ⊆ A`) are monochromatic. Estimate
> `F(k)`.

The existence of `F(k)` is Folkman's theorem. Erdős and Spencer [ErSp89] proved
`F(k) ≥ 2^(c k² / log k)`, and Balogh, Eberhard, Narayanan, Treglown and Wagner [BENTW17] improved
this to `F(k) ≥ 2^(2^(k-1)/k)`, the bound recorded on the problem page. This file proves the
[BENTW17] bound for every `k ≥ 2`, together with the two-colour case of Folkman's theorem, so that
`F k` is a genuine minimum. The problem itself (the growth rate of `F(k)`) remains open; [BENTW17]
notes that the upper bound known at the time was of tower type.

## Definitions and faithfulness

* `FolkmanProperty k N`: for every `c : ℕ → Fin 2` there are a `k`-element `A : Finset ℕ` and a
  colour such that every sum `∑ n ∈ S, n` over a nonempty `S ⊆ A` lies in `Finset.Icc 1 N` and
  has that colour. Colourings are functions on `ℕ`, but `c` is only ever evaluated at sums that
  are required to lie in `{1, …, N}`, so this is the same as quantifying over the 2-colourings of
  `{1, …, N}`. The requirement that the sums lie in `{1, …, N}` is explicit in [BENTW17]
  ("contained in `[n]` and have the same colour") and implicit on the problem page, where only
  `{1, …, N}` is coloured. Taking `S = {a}` shows `A ⊆ {1, …, N}`; `A` is a `Finset`, so its `k`
  elements are distinct.
* `F k := sInf {N | FolkmanProperty k N}`.

## Non-vacuity and the `sInf` convention

`sInf ∅ = 0` in `ℕ`, so a lower bound on `F k` is only meaningful once the defining set is
nonempty. `folkman` proves `∃ N, FolkmanProperty k N` for every `k`, and `folkmanProperty_iff`
shows `FolkmanProperty k N ↔ F k ≤ N`: `F k` is the least such `N`, and the property holds for
every larger `N`. The lower bound is also proved directly, without `F`, as
`not_folkmanProperty`: for `k ≥ 2` and `n = ⌊2^(2^(k-1)/k)⌋` some 2-colouring of `{1, …, n}` has
no `k`-set with monochromatic subset sums.

## The range of `k`

[BENTW17] states the bound "for all `k ∈ ℕ`", and the problem page gives no restriction, but it
fails for `k = 1`: `F 1 = 1 < 2 = 2^(2^0/1)` (`F_one`, `not_two_pow_le_F_one`). All main results
assume `k ≥ 2`, which is the range in which the proof of [BENTW17] works.

## Proof (following [BENTW17], with counting in place of probability)

* **Folkman's theorem** (`folkman`). Mathlib's Hindman theorem
  (`Hindman.exists_FS_of_finite_cover`), applied in `ℕ+`, gives for every colouring of `ℕ` a
  sequence of positive integers all of whose finite sums have one colour (`exists_pos_stream`).
  Taking a block of more than `M` initial terms as one element and recursing on the remaining
  sequence gives `k` distinct elements, all of whose nonempty subset sums are finite sums of the
  sequence (`exists_finset_fs`). A compactness argument in `ℕ → Fin 2` turns this into a finite
  `N`: if no `N` worked, the sets of colourings with no suitable `k`-set inside `{1, …, N}` would
  be closed, nonempty and decreasing, so some colouring would lie in all of them.
* **The colourings** (`col`). For `X ⊆ {0, …, n}` write `x = 2^v w` with `w` odd and give `x`
  colour `0` iff (`w ∈ X` ↔ `v` is even). So odd numbers are coloured freely by `X`, and `2x`
  always has the other colour from `x` (`col_two_mul_ne`), as in [BENTW17].
* **Repeated subset sums** (`card_mono_le`, first case). If two different subsets of `A` have the
  same sum, removing their intersection gives disjoint nonempty `D₁, D₂` with equal sum `x`; then
  `x` and `2x` are both subset sums, so no colouring `col X` makes all subset sums monochromatic.
* **Distinct subset sums** (`card_mono_le`, second case). Let `r ∈ A` have the least 2-adic
  valuation `s`. For each `C ⊆ A \ {r}` exactly one of `C`, `C ∪ {r}` (`blk r s C`) has sum
  `2^s · w` with `w` odd. These `2^(k-1)` odd numbers `w` are distinct, and a monochromatic
  colouring must put all of them in `X` or all outside `X`. Hence at most `2 · 2^(n+1-2^(k-1))`
  of the `2^(n+1)` sets `X` are bad for `A` (the paper's claim `P ≤ 2^(1-2^(k-1))`).
* **Union bound** (`not_folkmanProperty`). There are at most `C(n, k)` candidate sets `A`, and
  `2 · C(n, k) ≤ k! · C(n, k) = n (n-1) ⋯ (n-k+1) < n^k ≤ 2^(2^(k-1))` for `k ≥ 2`
  (`two_mul_choose_lt`, `floor_pow_le`). So some `X` is good for every `A`. (The paper uses
  `C(n, k) ≤ (en/k)^k` instead and checks `k ≤ 3` separately.)
* **Conclusion** (`two_pow_lt_F`). `FolkmanProperty k n` fails, so `n < F k`, hence
  `2^(2^(k-1)/k) < n + 1 ≤ F k`.

## Main results

* `Erdos531.folkman : ∃ N, FolkmanProperty k N` (Folkman's theorem, two colours).
* `Erdos531.folkmanProperty_iff : FolkmanProperty k N ↔ F k ≤ N`.
* `Erdos531.not_folkmanProperty :
    2 ≤ k → ¬ FolkmanProperty k ⌊(2 : ℝ) ^ ((2 : ℝ) ^ (k - 1) / k)⌋₊`.
* `Erdos531.two_pow_le_F : 2 ≤ k → (2 : ℝ) ^ ((2 : ℝ) ^ (k - 1) / k) ≤ F k` (the bound of
  [BENTW17] as stated on the problem page), and the strict version `Erdos531.two_pow_lt_F`.
* `Erdos531.F_one : F 1 = 1` and `Erdos531.not_two_pow_le_F_one`: the bound fails at `k = 1`.

In `(2 : ℝ) ^ ((2 : ℝ) ^ (k - 1) / k)` the outer power is the real power `Real.rpow`, the inner
one is a natural-number power, and `k - 1` is truncated subtraction, which is harmless for
`k ≥ 2`.

## References

* [BENTW17] Balogh, J., Eberhard, S., Narayanan, B., Treglown, A. and Wagner, A. Z.,
  _An improved lower bound for Folkman's theorem_. Bull. Lond. Math. Soc. 49 (2017), 745-747.
  arXiv:1703.02473.
* [Er73] Erdős, P., _Problems and results on combinatorial number theory_. A survey of
  combinatorial theory (1973), 117-138.
* [ErSp89] Erdős, P. and Spencer, J., _Monochromatic sumsets_. J. Combin. Theory Ser. A 50
  (1989), 162-163.
* [Hi74] Hindman, N., _Finite sums from sequences within cells of a partition of `ℕ`_.
  J. Combin. Theory Ser. A 17 (1974), 1-11.
* [erdosproblems.com/531](https://www.erdosproblems.com/531)
-/

open Finset

namespace Erdos531

/-- `FolkmanProperty k N`: for every 2-colouring `c` of `{1, …, N}` there is a `k`-element set
`A` such that all sums `∑ n ∈ S, n` over nonempty `S ⊆ A` lie in `{1, …, N}` and have the same
colour. -/
def FolkmanProperty (k N : ℕ) : Prop :=
  ∀ c : ℕ → Fin 2, ∃ A : Finset ℕ, A.card = k ∧ ∃ color : Fin 2,
    ∀ S : Finset ℕ, S.Nonempty → S ⊆ A →
      (∑ n ∈ S, n) ∈ Finset.Icc 1 N ∧ c (∑ n ∈ S, n) = color

/-- `F k`: the least `N` with `FolkmanProperty k N`. -/
noncomputable def F (k : ℕ) : ℕ := sInf {N | FolkmanProperty k N}

/-! ### Folkman's theorem: the set defining `F k` is nonempty -/

/-- `FolkmanProperty k N` is monotone in `N`. -/
theorem FolkmanProperty.mono {k N M : ℕ} (h : FolkmanProperty k N) (hNM : N ≤ M) :
    FolkmanProperty k M := by
  intro c
  obtain ⟨A, hA, color, hS⟩ := h c
  refine ⟨A, hA, color, fun S hS₁ hS₂ => ?_⟩
  obtain ⟨h1, h2⟩ := hS S hS₁ hS₂
  refine ⟨?_, h2⟩
  simp only [Finset.mem_Icc] at h1 ⊢
  omega

/-- A finite sum of the coerced sequence `a.map (↑)` is the coercion of a finite sum of `a`. -/
theorem fs_of_fs_map_coe {a : Stream' ℕ+} {m : ℕ}
    (h : Hindman.FS (a.map fun p : ℕ+ => (p : ℕ)) m) :
    ∃ p : ℕ+, Hindman.FS a p ∧ (p : ℕ) = m := by
  generalize hb : a.map (fun p : ℕ+ => (p : ℕ)) = b at h
  induction h generalizing a with
  | head b =>
    subst hb
    exact ⟨a.head, Hindman.FS.head a, by rw [Stream'.head_map]⟩
  | of_tail b m _ ih =>
    obtain ⟨p, hp, rfl⟩ := ih (a := a.tail) (by rw [← Stream'.tail_map, hb])
    exact ⟨p, Hindman.FS.of_tail a p hp, rfl⟩
  | cons b m _ ih =>
    obtain ⟨p, hp, rfl⟩ := ih (a := a.tail) (by rw [← Stream'.tail_map, hb])
    refine ⟨a.head + p, Hindman.FS.cons a p hp, ?_⟩
    rw [PNat.add_coe, ← hb, Stream'.head_map]

/-- Hindman's theorem for 2-colourings of `ℕ`, with a sequence of positive integers. -/
theorem exists_pos_stream (c : ℕ → Fin 2) :
    ∃ b : Stream' ℕ, (∀ i, 1 ≤ b.get i) ∧ ∃ color : Fin 2, ∀ m, Hindman.FS b m → c m = color := by
  obtain ⟨s, hs, a, ha⟩ := Hindman.exists_FS_of_finite_cover
    (Set.range fun color : Fin 2 => {p : ℕ+ | c p = color}) (Set.finite_range _)
    (fun p _ => Set.mem_sUnion.2 ⟨_, ⟨c p, rfl⟩, rfl⟩)
  obtain ⟨color, rfl⟩ := hs
  refine ⟨a.map fun p : ℕ+ => (p : ℕ), fun i => ?_, color, fun m hm => ?_⟩
  · rw [Stream'.get_map]
    exact (a.get i).pos
  · obtain ⟨p, hp, rfl⟩ := fs_of_fs_map_coe hm
    exact ha p hp

/-- The sum of the first `n` terms plus a finite sum of the remaining terms is a finite sum. -/
theorem fs_prefix_add (n : ℕ) : ∀ (b : Stream' ℕ) (m : ℕ), Hindman.FS (b.drop n) m →
    Hindman.FS b (∑ i ∈ range n, b.get i + m) := by
  induction n with
  | zero => intro b m h; simpa using h
  | succ n ih =>
    intro b m h
    rw [Stream'.drop_succ] at h
    have := Hindman.FS.cons b _ (ih b.tail m h)
    convert this using 1
    rw [Finset.sum_range_succ']
    simp only [Stream'.get_tail]
    rw [add_comm (∑ i ∈ range n, b.get (i + 1)), add_assoc]

/-- From a sequence of positive integers: `k` distinct elements, all larger than `M`, whose
nonempty subset sums are all finite sums of the sequence. -/
theorem exists_finset_fs (k : ℕ) : ∀ (M : ℕ) (b : Stream' ℕ), (∀ i, 1 ≤ b.get i) →
    ∃ A : Finset ℕ, A.card = k ∧ (∀ a ∈ A, M < a) ∧
      ∀ S : Finset ℕ, S.Nonempty → S ⊆ A → Hindman.FS b (∑ n ∈ S, n) := by
  induction k with
  | zero =>
    intro M b _
    refine ⟨∅, rfl, by simp, fun S hS hSA => ?_⟩
    rw [Finset.subset_empty] at hSA
    exact absurd hSA hS.ne_empty
  | succ k ih =>
    intro M b hb
    set x := ∑ i ∈ range (M + 1), b.get i with hx
    have hMx : M < x := by
      have := Finset.card_nsmul_le_sum (range (M + 1)) (fun i => b.get i) 1 (fun i _ => hb i)
      simp only [card_range, smul_eq_mul, mul_one] at this
      omega
    have hb' : ∀ i, 1 ≤ (b.drop (M + 1)).get i := fun i => by
      rw [Stream'.get_drop]; exact hb _
    obtain ⟨A, hAcard, hAgt, hAfs⟩ := ih x (b.drop (M + 1)) hb'
    have hxA : x ∉ A := fun h => lt_irrefl x (hAgt x h)
    refine ⟨insert x A, by rw [Finset.card_insert_of_notMem hxA, hAcard], ?_, ?_⟩
    · intro a ha
      rcases Finset.mem_insert.1 ha with rfl | ha
      · exact hMx
      · exact hMx.trans (hAgt a ha)
    · intro S hS hSA
      by_cases hxS : x ∈ S
      · rw [← Finset.insert_erase hxS, Finset.sum_insert (Finset.notMem_erase x S)]
        rcases (S.erase x).eq_empty_or_nonempty with he | he
        · rw [he, Finset.sum_empty, add_zero]
          exact Hindman.FS.finsetSum b _ ⟨0, Finset.mem_range.2 (Nat.succ_pos M)⟩
        · apply fs_prefix_add
          apply hAfs _ he
          intro y hy
          rcases Finset.mem_insert.1 (hSA (Finset.mem_of_mem_erase hy)) with rfl | h
          · exact absurd hy (Finset.notMem_erase _ _)
          · exact h
      · apply Hindman.FS_iter_tail_sub_FS b (M + 1)
        apply hAfs S hS
        intro y hy
        rcases Finset.mem_insert.1 (hSA hy) with rfl | h
        · exact absurd hy hxS
        · exact h

/-- **Folkman's theorem** (two colours): the set defining `F k` is nonempty. -/
theorem folkman (k : ℕ) : ∃ N, FolkmanProperty k N := by
  by_contra hcon
  push Not at hcon
  set t : ℕ → Set (ℕ → Fin 2) := fun N => {c | ¬ ∃ A : Finset ℕ, A.card = k ∧ ∃ color : Fin 2,
      ∀ S : Finset ℕ, S.Nonempty → S ⊆ A →
        (∑ n ∈ S, n) ∈ Finset.Icc 1 N ∧ c (∑ n ∈ S, n) = color} with ht
  have htn : ∀ N, (t N).Nonempty := fun N => not_forall.1 (hcon N)
  have htd : ∀ N, t (N + 1) ⊆ t N := by
    intro N c hc ⟨A, hA, color, hS⟩
    exact hc ⟨A, hA, color, fun S h1 h2 => by
      obtain ⟨h3, h4⟩ := hS S h1 h2
      exact ⟨by simp only [Finset.mem_Icc] at h3 ⊢; omega, h4⟩⟩
  have htcl : ∀ N, IsClosed (t N) := by
    intro N
    let r : (ℕ → Fin 2) → (Fin (N + 1) → Fin 2) := fun c i => c i
    have hr : Continuous r := continuous_pi fun i => continuous_apply _
    have : t N = r ⁻¹' (r '' t N) := by
      refine Set.Subset.antisymm (Set.subset_preimage_image r _) ?_
      rintro c ⟨c', hc', hcc'⟩ ⟨A, hA, color, hS⟩
      apply hc'
      refine ⟨A, hA, color, fun S h1 h2 => ?_⟩
      obtain ⟨h3, h4⟩ := hS S h1 h2
      refine ⟨h3, ?_⟩
      have h5 : (∑ n ∈ S, n) < N + 1 := by simp only [Finset.mem_Icc] at h3; omega
      exact (congrFun hcc' ⟨_, h5⟩).trans h4
    rw [this]
    exact (isClosed_discrete _).preimage hr
  obtain ⟨c, hc⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed t htd htn
    (htcl 0).isCompact htcl
  rw [Set.mem_iInter] at hc
  obtain ⟨b, hb, color, hcol⟩ := exists_pos_stream c
  obtain ⟨A, hA, hApos, hAfs⟩ := exists_finset_fs k 0 b hb
  apply hc (∑ n ∈ A, n)
  refine ⟨A, hA, color, fun S h1 h2 => ⟨?_, hcol _ (hAfs S h1 h2)⟩⟩
  rw [Finset.mem_Icc]
  obtain ⟨y, hy⟩ := h1
  exact ⟨(hApos y (h2 hy)).trans_le
      (Finset.single_le_sum (f := fun n => n) (fun _ _ => Nat.zero_le _) hy),
    Finset.sum_le_sum_of_subset h2⟩

/-- `F k` itself has the Folkman property. -/
theorem folkmanProperty_F (k : ℕ) : FolkmanProperty k (F k) := Nat.sInf_mem (folkman k)

/-- `F k` is the least `N` with `FolkmanProperty k N`, and the property holds above it. -/
theorem folkmanProperty_iff (k N : ℕ) : FolkmanProperty k N ↔ F k ≤ N :=
  ⟨fun h => Nat.sInf_le h, fun h => (folkmanProperty_F k).mono h⟩

/-! ### The colouring -/

/-- Write `x = 2 ^ v * w` with `w` odd. Then `x` gets colour `0` if and only if `w ∈ X ↔ v` is
even. -/
def col (X : Finset ℕ) (x : ℕ) : Fin 2 :=
  if (x / 2 ^ padicValNat 2 x ∈ X ↔ Even (padicValNat 2 x)) then 0 else 1

/-- The colour of `2 ^ s * w` for odd `w`. -/
theorem col_two_pow_mul (X : Finset ℕ) (s : ℕ) {w : ℕ} (hw : Odd w) :
    col X (2 ^ s * w) = if (w ∈ X ↔ Even s) then 0 else 1 := by
  have hw0 : w ≠ 0 := by rintro rfl; exact absurd hw (by decide)
  have hw2 : ¬ 2 ∣ w := by obtain ⟨j, rfl⟩ := hw; omega
  have hv : padicValNat 2 (2 ^ s * w) = s := by
    rw [padicValNat.mul (pow_ne_zero _ two_ne_zero) hw0, padicValNat.prime_pow,
      padicValNat.eq_zero_of_not_dvd hw2, add_zero]
  unfold col
  rw [hv, Nat.mul_div_cancel_left w (pow_pos two_pos s)]

/-- `x` and `2 x` always get different colours. -/
theorem col_two_mul_ne (X : Finset ℕ) {x : ℕ} (hx : x ≠ 0) : col X (2 * x) ≠ col X x := by
  obtain ⟨s, w, hw, rfl⟩ := Nat.exists_eq_two_pow_mul_odd hx
  rw [show 2 * (2 ^ s * w) = 2 ^ (s + 1) * w by ring, col_two_pow_mul X _ hw,
    col_two_pow_mul X _ hw]
  simp only [Nat.even_add_one]
  split_ifs <;> first | decide | tauto

/-! ### Counting -/

/-- Add `r` to `C` when needed to make the quotient of the sum by `2 ^ s` odd. -/
def blk (r s : ℕ) (C : Finset ℕ) : Finset ℕ :=
  if Odd ((∑ m ∈ C, m) / 2 ^ s) then C else insert r C

/-- If `2 ^ s` divides `r` and the sum of `C`, and `r / 2 ^ s` is odd, then the sum of `blk r s C`
is `2 ^ s` times an odd number. -/
theorem blk_spec {r s : ℕ} {C : Finset ℕ} (hrC : r ∉ C) (hC : 2 ^ s ∣ ∑ m ∈ C, m)
    (hr : 2 ^ s ∣ r) (hodd : Odd (r / 2 ^ s)) :
    ∑ m ∈ blk r s C, m = 2 ^ s * ((∑ m ∈ blk r s C, m) / 2 ^ s) ∧
      Odd ((∑ m ∈ blk r s C, m) / 2 ^ s) := by
  obtain ⟨u, hu⟩ := hC
  obtain ⟨v, rfl⟩ := hr
  have hp : 0 < 2 ^ s := pow_pos two_pos s
  rw [Nat.mul_div_cancel_left _ hp] at hodd
  unfold blk
  rw [hu, Nat.mul_div_cancel_left _ hp]
  split_ifs with h
  · rw [hu, Nat.mul_div_cancel_left _ hp]
    exact ⟨rfl, h⟩
  · rw [Finset.sum_insert hrC, hu, ← mul_add, Nat.mul_div_cancel_left _ hp]
    refine ⟨rfl, ?_⟩
    rw [Nat.not_odd_iff_even] at h
    exact hodd.add_even h

/-- `C` is recovered from `blk r s C`. -/
theorem blk_erase {r s : ℕ} {C : Finset ℕ} (hrC : r ∉ C) : (blk r s C).erase r = C := by
  unfold blk
  split_ifs
  · exact Finset.erase_eq_of_notMem hrC
  · exact Finset.erase_insert hrC

/-- At most `2 ^ |U \ T|` subsets of `U` contain all of `T` (or none of `T`). -/
theorem card_filter_iff_le (U T : Finset ℕ) (P : Prop) [Decidable P] :
    (U.powerset.filter fun X => ∀ m ∈ T, (m ∈ X ↔ P)).card ≤ 2 ^ (U \ T).card := by
  rw [← Finset.card_powerset]
  refine Finset.card_le_card_of_injOn (fun X => X \ T) ?_ ?_
  · intro X hX
    simp only [Finset.coe_filter, Finset.mem_powerset, Set.mem_ofPred_eq, Finset.coe_powerset,
      Set.mem_preimage] at hX ⊢
    exact Finset.sdiff_subset_sdiff hX.1 le_rfl
  · intro X hX Y hY hXY
    simp only [Finset.coe_filter, Finset.mem_powerset, Set.mem_ofPred_eq] at hX hY
    ext m
    by_cases hm : m ∈ T
    · rw [hX.2 m hm, hY.2 m hm]
    · have := congrArg (m ∈ ·) hXY
      simpa [hm] using this

/-- For a fixed `k`-set `A ⊆ {1, …, n}` with sum at most `n`, at most `2 · 2^(n+1) / 2^(2^(k-1))`
sets `X ⊆ {0, …, n}` make all nonempty subset sums of `A` monochromatic under `col X`. -/
theorem card_mono_le {n k : ℕ} (hk : 1 ≤ k) {A : Finset ℕ} (hAk : A.card = k)
    (hA : A ⊆ Icc 1 n) (hsum : ∑ a ∈ A, a ≤ n) :
    ((range (n + 1)).powerset.filter fun X =>
        ∃ color : Fin 2, ∀ S ∈ A.powerset, S.Nonempty → col X (∑ m ∈ S, m) = color).card *
      2 ^ 2 ^ (k - 1) ≤ 2 * 2 ^ (n + 1) := by
  set U := range (n + 1) with hU
  have hApos : ∀ a ∈ A, 0 < a := fun a ha => by
    have := hA ha
    simp only [Finset.mem_Icc] at this
    omega
  by_cases hinj : ∀ S₁ ⊆ A, ∀ S₂ ⊆ A, ∑ m ∈ S₁, m = ∑ m ∈ S₂, m → S₁ = S₂
  swap
  · push Not at hinj
    obtain ⟨S₁, h₁, S₂, h₂, hsum12, hne⟩ := hinj
    suffices h : ∀ X, ¬ ∃ color : Fin 2, ∀ S ∈ A.powerset, S.Nonempty →
        col X (∑ m ∈ S, m) = color by
      rw [Finset.filter_false_of_mem (fun X _ => h X), Finset.card_empty, zero_mul]
      positivity
    rintro X ⟨color, hcol⟩
    have e₁ := Finset.sum_inter_add_sum_sdiff S₁ S₂ (fun m => m)
    have e₂ := Finset.sum_inter_add_sum_sdiff S₂ S₁ (fun m => m)
    rw [Finset.inter_comm] at e₂
    have hD : ∑ m ∈ S₁ \ S₂, m = ∑ m ∈ S₂ \ S₁, m := by omega
    have hD₁A : S₁ \ S₂ ⊆ A := Finset.sdiff_subset.trans h₁
    have hD₂A : S₂ \ S₁ ⊆ A := Finset.sdiff_subset.trans h₂
    have hpos : 0 < ∑ m ∈ S₁ \ S₂, m := by
      rcases (S₁ \ S₂).eq_empty_or_nonempty with he | he
      · rcases (S₂ \ S₁).eq_empty_or_nonempty with he' | he'
        · rw [Finset.sdiff_eq_empty_iff_subset] at he he'
          exact absurd (Finset.Subset.antisymm he he') hne
        · rw [hD]
          exact Finset.sum_pos (fun a ha => hApos a (hD₂A ha)) he'
      · exact Finset.sum_pos (fun a ha => hApos a (hD₁A ha)) he
    have hne₁ : (S₁ \ S₂).Nonempty := Finset.nonempty_of_sum_ne_zero hpos.ne'
    have hunion : ∑ m ∈ (S₁ \ S₂) ∪ (S₂ \ S₁), m = 2 * ∑ m ∈ S₁ \ S₂, m := by
      rw [Finset.sum_union disjoint_sdiff_sdiff, ← hD]
      ring
    have h1 := hcol (S₁ \ S₂) (Finset.mem_powerset.2 hD₁A) hne₁
    have h2 := hcol ((S₁ \ S₂) ∪ (S₂ \ S₁))
      (Finset.mem_powerset.2 (Finset.union_subset hD₁A hD₂A))
      (hne₁.mono Finset.subset_union_left)
    rw [hunion] at h2
    exact col_two_mul_ne X hpos.ne' (h2.trans h1.symm)
  · have hAne : A.Nonempty := by rw [← Finset.card_pos, hAk]; omega
    obtain ⟨r, hrA, hrmin⟩ := A.exists_min_image (padicValNat 2) hAne
    set s := padicValNat 2 r with hs
    have hr0 : r ≠ 0 := (hApos r hrA).ne'
    have hdvd : ∀ a ∈ A, 2 ^ s ∣ a := fun a ha =>
      (pow_dvd_pow 2 (hrmin a ha)).trans pow_padicValNat_dvd
    have hrodd : Odd (r / 2 ^ s) := by
      have h1 := pow_succ_padicValNat_not_dvd (p := 2) hr0
      obtain ⟨v, hv⟩ := (pow_padicValNat_dvd : 2 ^ s ∣ r)
      rw [← hs] at h1
      rw [hv, Nat.mul_div_cancel_left _ (pow_pos two_pos _), Nat.odd_iff]
      by_contra hv2
      apply h1
      rw [hv, pow_succ]
      exact Nat.mul_dvd_mul_left _ (by omega)
    set P := (A.erase r).powerset with hP
    have hPB : ∀ C ∈ P, blk r s C ⊆ A ∧ (blk r s C).erase r = C ∧
        ∑ m ∈ blk r s C, m = 2 ^ s * ((∑ m ∈ blk r s C, m) / 2 ^ s) ∧
          Odd ((∑ m ∈ blk r s C, m) / 2 ^ s) := by
      intro C hC
      rw [hP, Finset.mem_powerset] at hC
      have hCA : C ⊆ A := hC.trans (Finset.erase_subset r A)
      have hrC : r ∉ C := fun h => Finset.notMem_erase r A (hC h)
      refine ⟨?_, blk_erase hrC,
        blk_spec hrC (Finset.dvd_sum fun a ha => hdvd a (hCA ha)) (hdvd r hrA) hrodd⟩
      unfold blk
      split_ifs
      · exact hCA
      · exact Finset.insert_subset hrA hCA
    set T := P.image fun C => (∑ m ∈ blk r s C, m) / 2 ^ s with hT
    have hTcard : T.card = 2 ^ (k - 1) := by
      rw [hT, Finset.card_image_of_injOn, hP, Finset.card_powerset, Finset.card_erase_of_mem hrA,
        hAk]
      intro C₁ hC₁ C₂ hC₂ heq
      obtain ⟨h1, h2, h3, -⟩ := hPB C₁ hC₁
      obtain ⟨h1', h2', h3', -⟩ := hPB C₂ hC₂
      have heq' : (∑ m ∈ blk r s C₁, m) / 2 ^ s = (∑ m ∈ blk r s C₂, m) / 2 ^ s := heq
      have : blk r s C₁ = blk r s C₂ := hinj _ h1 _ h1' (by rw [h3, h3', heq'])
      rw [← h2, ← h2', this]
    have hTU : T ⊆ U := by
      intro m hm
      obtain ⟨C, hC, rfl⟩ := Finset.mem_image.1 hm
      rw [hU, Finset.mem_range]
      have h1 := Finset.sum_le_sum_of_subset (f := fun m => m) (hPB C hC).1
      have h2 := Nat.div_le_self (∑ m ∈ blk r s C, m) (2 ^ s)
      omega
    have hsub : (U.powerset.filter fun X => ∃ color : Fin 2, ∀ S ∈ A.powerset, S.Nonempty →
          col X (∑ m ∈ S, m) = color) ⊆
        (U.powerset.filter fun X => ∀ m ∈ T, (m ∈ X ↔ Even s)) ∪
          (U.powerset.filter fun X => ∀ m ∈ T, (m ∈ X ↔ ¬ Even s)) := by
      intro X hX
      rw [Finset.mem_filter] at hX
      obtain ⟨hXU, color, hcol⟩ := hX
      have key : ∀ m ∈ T, col X (2 ^ s * m) = color ∧ Odd m := by
        intro m hm
        obtain ⟨C, hC, rfl⟩ := Finset.mem_image.1 hm
        obtain ⟨h1, -, h3, h4⟩ := hPB C hC
        refine ⟨?_, h4⟩
        rw [← h3]
        refine hcol _ (Finset.mem_powerset.2 h1)
          (Finset.nonempty_of_sum_ne_zero (f := fun m => m) ?_)
        rw [h3]
        exact (Nat.mul_pos (pow_pos two_pos s) h4.pos).ne'
      rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter]
      by_cases hc0 : color = 0
      · refine Or.inl ⟨hXU, fun m hm => ?_⟩
        obtain ⟨h1, h2⟩ := key m hm
        rw [col_two_pow_mul X s h2, hc0] at h1
        split_ifs at h1 with h
        · exact h
        · exact absurd h1 (by decide)
      · refine Or.inr ⟨hXU, fun m hm => ?_⟩
        obtain ⟨h1, h2⟩ := key m hm
        rw [col_two_pow_mul X s h2] at h1
        split_ifs at h1 with h
        · exact absurd h1.symm hc0
        · tauto
    calc _ ≤ ((U.powerset.filter fun X => ∀ m ∈ T, (m ∈ X ↔ Even s)).card +
          (U.powerset.filter fun X => ∀ m ∈ T, (m ∈ X ↔ ¬ Even s)).card) * 2 ^ 2 ^ (k - 1) :=
          Nat.mul_le_mul_right _ ((Finset.card_le_card hsub).trans (Finset.card_union_le _ _))
      _ ≤ (2 ^ (U \ T).card + 2 ^ (U \ T).card) * 2 ^ T.card := by
          rw [hTcard]
          gcongr
          · exact card_filter_iff_le U T _
          · exact card_filter_iff_le U T _
      _ = 2 * 2 ^ ((U \ T).card + T.card) := by ring
      _ = 2 * 2 ^ (n + 1) := by rw [Finset.card_sdiff_add_card_eq_card hTU, hU, Finset.card_range]

/-! ### Arithmetic -/

/-- `n^k ≤ 2^(2^(k-1))` for `n = ⌊2^(2^(k-1)/k)⌋`. -/
theorem floor_pow_le {k : ℕ} (hk : 1 ≤ k) :
    ⌊(2 : ℝ) ^ ((2 : ℝ) ^ (k - 1) / k)⌋₊ ^ k ≤ 2 ^ 2 ^ (k - 1) := by
  have hpos : (0 : ℝ) ≤ (2 : ℝ) ^ ((2 : ℝ) ^ (k - 1) / k) := by positivity
  have hk0 : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have h1 : ((⌊(2 : ℝ) ^ ((2 : ℝ) ^ (k - 1) / k)⌋₊ : ℕ) : ℝ) ^ k ≤
      ((2 : ℝ) ^ ((2 : ℝ) ^ (k - 1) / k)) ^ k :=
    pow_le_pow_left₀ (Nat.cast_nonneg _) (Nat.floor_le hpos) k
  have h2 : ((2 : ℝ) ^ ((2 : ℝ) ^ (k - 1) / k)) ^ k = ((2 ^ 2 ^ (k - 1) : ℕ) : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), div_mul_cancel₀ _ hk0]
    have : ((2 : ℝ) ^ (k - 1)) = ((2 ^ (k - 1) : ℕ) : ℝ) := by push_cast; ring
    rw [this, Real.rpow_natCast]
    push_cast
    ring
  exact_mod_cast h1.trans h2.le

/-- `2 · C(n, k) < 2^(2^(k-1))` whenever `k ≥ 2` and `n^k ≤ 2^(2^(k-1))`. -/
theorem two_mul_choose_lt {n k : ℕ} (hk : 2 ≤ k) (hn : n ^ k ≤ 2 ^ 2 ^ (k - 1)) :
    2 * n.choose k < 2 ^ 2 ^ (k - 1) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn0
  · rw [Nat.choose_eq_zero_of_lt (by omega)]
    positivity
  · have h1 : 2 ≤ k.factorial := Nat.factorial_le hk
    have h2 := Nat.descFactorial_lt_pow hn0.ne' hk
    rw [Nat.descFactorial_eq_factorial_mul_choose] at h2
    calc 2 * n.choose k ≤ k.factorial * n.choose k := Nat.mul_le_mul_right _ h1
      _ < n ^ k := h2
      _ ≤ _ := hn

/-! ### Main results -/

/-- **[BENTW17], colouring form.** For `k ≥ 2` and `n = ⌊2^(2^(k-1)/k)⌋` there is a 2-colouring
of `{1, …, n}` with no `k`-set whose nonempty subset sums all lie in `{1, …, n}` and have the same
colour. -/
theorem not_folkmanProperty {k : ℕ} (hk : 2 ≤ k) :
    ¬ FolkmanProperty k ⌊(2 : ℝ) ^ ((2 : ℝ) ^ (k - 1) / k)⌋₊ := by
  set n := ⌊(2 : ℝ) ^ ((2 : ℝ) ^ (k - 1) / k)⌋₊ with hn
  have hnum : 2 * n.choose k < 2 ^ 2 ^ (k - 1) := two_mul_choose_lt hk (floor_pow_le (by omega))
  set U := range (n + 1) with hU
  set 𝒜 := ((Icc 1 n).powersetCard k).filter fun A => ∑ a ∈ A, a ≤ n with h𝒜
  set bad := U.powerset.filter fun X => ∃ A ∈ 𝒜, ∃ color : Fin 2, ∀ S ∈ A.powerset,
    S.Nonempty → col X (∑ m ∈ S, m) = color with hbad_def
  have hbad : bad.card < U.powerset.card := by
    have h1 : bad ⊆ 𝒜.biUnion fun A => U.powerset.filter fun X => ∃ color : Fin 2,
        ∀ S ∈ A.powerset, S.Nonempty → col X (∑ m ∈ S, m) = color := by
      intro X hX
      rw [hbad_def, Finset.mem_filter] at hX
      obtain ⟨hXU, A, hA, hmono⟩ := hX
      exact Finset.mem_biUnion.2 ⟨A, hA, Finset.mem_filter.2 ⟨hXU, hmono⟩⟩
    have h2 := (Finset.card_le_card h1).trans Finset.card_biUnion_le
    have h3 : (∑ A ∈ 𝒜, (U.powerset.filter fun X => ∃ color : Fin 2,
        ∀ S ∈ A.powerset, S.Nonempty → col X (∑ m ∈ S, m) = color).card) * 2 ^ 2 ^ (k - 1) ≤
        𝒜.card * (2 * 2 ^ (n + 1)) := by
      rw [Finset.sum_mul, ← smul_eq_mul]
      refine Finset.sum_le_card_nsmul _ _ _ fun A hA => ?_
      rw [h𝒜, Finset.mem_filter, Finset.mem_powersetCard] at hA
      exact card_mono_le (by omega) hA.1.2 hA.1.1 hA.2
    have h4 : 𝒜.card ≤ n.choose k := by
      refine (Finset.card_filter_le _ _).trans ?_
      rw [Finset.card_powersetCard, Nat.card_Icc, Nat.add_sub_cancel]
    rw [Finset.card_powerset, hU, Finset.card_range]
    have : bad.card * 2 ^ 2 ^ (k - 1) < 2 ^ (n + 1) * 2 ^ 2 ^ (k - 1) := by
      calc bad.card * 2 ^ 2 ^ (k - 1) ≤ 𝒜.card * (2 * 2 ^ (n + 1)) :=
            (Nat.mul_le_mul_right _ h2).trans h3
        _ ≤ n.choose k * (2 * 2 ^ (n + 1)) := Nat.mul_le_mul_right _ h4
        _ = (2 * n.choose k) * 2 ^ (n + 1) := by ring
        _ < 2 ^ 2 ^ (k - 1) * 2 ^ (n + 1) := Nat.mul_lt_mul_of_pos_right hnum (by positivity)
        _ = _ := by ring
    exact Nat.lt_of_mul_lt_mul_right this
  obtain ⟨X, hXU, hXbad⟩ := Finset.exists_mem_notMem_of_card_lt_card hbad
  intro hF
  obtain ⟨A, hAk, color, hS⟩ := hF (col X)
  apply hXbad
  rw [hbad_def, Finset.mem_filter]
  refine ⟨hXU, A, ?_, color, fun S hS1 hS2 => (hS S hS2 (Finset.mem_powerset.1 hS1)).2⟩
  rw [h𝒜, Finset.mem_filter, Finset.mem_powersetCard]
  have hAne : A.Nonempty := by rw [← Finset.card_pos, hAk]; omega
  refine ⟨⟨fun a ha => ?_, hAk⟩, ?_⟩
  · have := (hS {a} (Finset.singleton_nonempty a) (Finset.singleton_subset_iff.2 ha)).1
    simpa using this
  · have := (hS A hAne subset_rfl).1
    rw [Finset.mem_Icc] at this
    exact this.2

/-- **[BENTW17]**, strict form: `2^(2^(k-1)/k) < F(k)` for `k ≥ 2`. -/
theorem two_pow_lt_F (k : ℕ) (hk : 2 ≤ k) : (2 : ℝ) ^ ((2 : ℝ) ^ (k - 1) / k) < F k := by
  have h := not_folkmanProperty hk
  rw [folkmanProperty_iff, not_le] at h
  calc _ < (⌊(2 : ℝ) ^ ((2 : ℝ) ^ (k - 1) / k)⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
    _ ≤ F k := by exact_mod_cast Nat.succ_le_of_lt h

/-- **[BENTW17]**: `F(k) ≥ 2^(2^(k-1)/k)` for `k ≥ 2`, as stated on the problem page. -/
theorem two_pow_le_F (k : ℕ) (hk : 2 ≤ k) : (2 : ℝ) ^ ((2 : ℝ) ^ (k - 1) / k) ≤ F k :=
  (two_pow_lt_F k hk).le

/-- `F(1) = 1`. -/
theorem F_one : F 1 = 1 := by
  apply le_antisymm
  · rw [← folkmanProperty_iff]
    intro c
    refine ⟨{1}, rfl, c 1, fun S hS hS1 => ?_⟩
    rw [hS.subset_singleton_iff.1 hS1]
    simp
  · by_contra h
    have h0 : F 1 = 0 := by omega
    obtain ⟨A, hA, color, hS⟩ := folkmanProperty_F 1 (fun _ => 0)
    rw [h0] at hS
    obtain ⟨a, rfl⟩ := Finset.card_eq_one.1 hA
    have := (hS {a} (Finset.singleton_nonempty a) subset_rfl).1
    simp at this

/-- The bound `F(k) ≥ 2^(2^(k-1)/k)` fails for `k = 1`, so the hypothesis `k ≥ 2` is needed. -/
theorem not_two_pow_le_F_one : ¬ (2 : ℝ) ^ ((2 : ℝ) ^ (1 - 1) / 1) ≤ F 1 := by
  rw [F_one]
  norm_num

end Erdos531
