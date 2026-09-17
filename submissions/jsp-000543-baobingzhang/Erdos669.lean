import Mathlib

/-!
# Erdős Problem 669: the orchard problem for `k = 3` (Burr–Grünbaum–Sloane)

Erdős Problem 669 ([Er97f], https://www.erdosproblems.com/669) reads:

> Let `F_k(n)` be minimal such that for any `n` points in `ℝ²` there exist at most `F_k(n)` many
> distinct lines passing through at least `k` of the points, and `f_k(n)` similarly but with lines
> passing through exactly `k` points.
>
> Estimate `f_k(n)` and `F_k(n)` - in particular, determine `lim F_k(n)/n²` and `lim f_k(n)/n²`.

The problem page records that `f_k(n) ≤ F_k(n)`, that `F_k(n) ≤ C(n,2)/C(k,2)`, and that Burr,
Grünbaum and Sloane [BGS74] proved `f₃(n) = n²/6 - O(n)` and `F₃(n) = n²/6 - O(n)`. This file
proves that result of [BGS74], and hence `lim F₃(n)/n² = lim f₃(n)/n² = 1/6`, together with the
trivial bound `F_k(n) ≤ C(n,2)/C(k,2)` for every `k ≥ 2`. The problem remains open for `k ≥ 4`;
nothing beyond the trivial upper bound is proved here for those `k`.

## Definitions and faithfulness

There is no formal-conjectures file for this problem. The conventions follow formal-conjectures:
`ℝ²` is `EuclideanSpace ℝ (Fin 2)`, and `IsLine` is copied from
`FormalConjectures/ErdosProblems/209.lean` (a line is an affine subspace whose direction has
dimension `1`).

* `richLines k S`: the lines `L` with at least `k` points of `S` on them, i.e.
  `k ≤ ((L : Set ℝ²) ∩ S).ncard`. `exactLines k S`: the lines with exactly `k` points of `S`.
  All lines of the plane are considered, not only lines spanned by two points of `S`.
* `F k n := sInf {N | ∀ S : Finset ℝ², S.card = n → (richLines k S).ncard ≤ N}` and `f k n` in
  the same way with `exactLines`. This is the page's "minimal `F_k(n)` such that any `n` points
  have at most `F_k(n)` such lines", with the `n` points being a `Finset` of `n` distinct points.

## The `ncard` and `sInf` conventions

`Set.ncard` is `0` on infinite sets and `sInf ∅ = 0` in `ℕ`. Neither convention is used by the
results below:

* `richLines_finite`: for `k ≥ 2` there are only finitely many lines through `k` points of `S`
  (each is spanned by two of the points), so the `ncard`s are genuine counts. For `k = 0`, and
  for `k = 1` with `S` nonempty, there are infinitely many such lines; all results below assume
  `k ≥ 2` or `k = 3`.
* `isGreatest_F`, `isGreatest_f`: for `k ≥ 2`, `F k n` and `f k n` are attained maxima of the
  number of such lines over all `n`-point sets.
* The main theorem `erdos_669.variants.three` would fail for a trivialised `F` or `f`, since the
  limits are `1/6 ≠ 0`.

## Proof

* **Upper bound** (`ncard_richLines_mul_le`). Two distinct points lie on exactly one line
  (`eq_line`). A line through at least `k` points of `S` contains at least `k(k-1)` ordered pairs
  of distinct points of `S`, and different lines share no such pair, so
  `#lines · k(k-1) ≤ n(n-1)`. For `k = 3` this is `F₃(n) ≤ n(n-1)/6`.
* **The curve.** Put `pt t = (t, 1/(1+t²))`, a point of the cubic `y(1+x²) = 1`. For distinct
  `s, t, u`, `pt u` lies on the line through `pt s` and `pt t` iff `st + su + tu = 1`
  (`mem_line_pt`). This follows from the identity
  `(u-s)(1/(1+t²) - 1/(1+s²)) - (t-s)(1/(1+u²) - 1/(1+s²))`
  `= (s-t)(u-s)(t-u)(1 - (st+su+tu)) / ((1+s²)(1+t²)(1+u²))`,
  used in the proof in polynomial form via `linear_combination`. Consequently a line meets the
  curve in at most three points (`card_filter_le_three`): if `pt u` and `pt v` both lie on the
  line through `pt s` and `pt t`, then `(s+t)(u-v) = 0`, and `s + t = 0` would give `st = 1`,
  i.e. `-s² = 1`.
* **The parameters.** Choose `m ∈ {n, n+1}` with `3 ∤ m` (`modulus`) and put
  `t_j = tan(π/6 + πj/m)` for `j < n` (`angle`). Then `cos(π/6 + πj/m) ≠ 0` because `3 ∤ m`
  (`cos_angle_ne_zero`), the `t_j` are distinct (`tan_angle_inj`), and the identity
  `cos(x+y+z) = cos x cos y cos z (1 - (tan x tan y + tan x tan z + tan y tan z))` shows that
  `m ∣ a + b + c` implies `t_a t_b + t_a t_c + t_b t_c = 1` (`e2_tan_angle`): the angle sum is
  `π/2 + π(a+b+c)/m`. So whenever `a, b, c < n` are distinct with `m ∣ a + b + c`, the three
  points are collinear, and their line contains exactly three points of `orchard n`.
* **Counting** (`card_good_aux`, `card_good_le`). Among the `n²` ordered pairs `(a, b)` with
  `a, b < n`, let `c < m` be the residue with `a + b + c ≡ 0 (mod m)` (`third`). At most `n` pairs
  have `a = b`, at most `n` have `c ≥ n` (then `c = n`), at most `n` have `c = a` and at most `n`
  have `c = b`, since in each case one coordinate determines the other. So at least `n² - 4n`
  pairs are good. Each good pair spans a line with exactly three points of `orchard n`, and such a
  line arises from at most `3 · 2 = 6` pairs. Hence `n² - 4n ≤ 6 f₃(n)` (`le_f_three`).
* **Conclusion.** `(n² - 4n)/6 ≤ f₃(n) ≤ F₃(n) ≤ n²/6` (`bounds_three`), which gives the `O(n)`
  statements and, by squeezing, both limits.

[BGS74] prove the sharper `f₃(n) ≥ 1 + ⌊n(n-3)/6⌋` (for `n ≥ 3`) with points `P(2ωk/n)` on a
nonsingular cubic `y² = 4x³ - g₂x - g₃` parametrised by the Weierstrass `℘`-function, where three
points are collinear iff their parameters sum to `0` modulo the real period. The construction
here uses the same idea on the singular (acnodal) cubic `y(1+x²) = 1`, whose parametrisation by
`tan` needs no elliptic functions; it gives a weaker lower-order term, which is enough for the
`O(n)` statement recorded on the problem page. The sharper bound of [BGS74] and their upper bounds
for `t₃(n)` beyond the trivial one are not formalised.

## Main results

* `Erdos669.erdos_669.variants.three`:
  `Tendsto (fun n => (F 3 n : ℝ) / n ^ 2) atTop (𝓝 (1 / 6)) ∧`
  `Tendsto (fun n => (f 3 n : ℝ) / n ^ 2) atTop (𝓝 (1 / 6))`.
* `Erdos669.erdos_669.variants.three_isBigO`: `f 3 n - n²/6 = O(n)` and `F 3 n - n²/6 = O(n)`.
* `Erdos669.bounds_three`: `(n² - 4n)/6 ≤ f 3 n ≤ F 3 n ≤ n²/6` for every `n`.
* `Erdos669.le_f_three : n * n ≤ 6 * f 3 n + 4 * n`.
* `Erdos669.erdos_669.variants.upper : 2 ≤ k → F k n * k.choose 2 ≤ n.choose 2`, and
  `Erdos669.F_mul_le : 2 ≤ k → F k n * (k * (k - 1)) ≤ n * (n - 1)`.
* `Erdos669.f_le_F : 2 ≤ k → f k n ≤ F k n`.
* `Erdos669.isGreatest_F`, `Erdos669.isGreatest_f`, `Erdos669.richLines_finite`.

## References

* [BGS74] Burr, S. A., Grünbaum, B. and Sloane, N. J. A., _The orchard problem_. Geom. Dedicata 2
  (1974), 397-424.
* [Er97f] Erdős, P., _Some unsolved problems_. Combinatorics, geometry and probability
  (Cambridge, 1993) (1997), 1-10.
* [erdosproblems.com/669](https://www.erdosproblems.com/669)
-/

namespace Erdos669

open Real Filter Topology Asymptotics

local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

/-! ## Definitions -/

/-- A line in the plane: an affine subspace whose direction is one-dimensional. -/
def IsLine (L : AffineSubspace ℝ ℝ²) : Prop :=
  Module.finrank ℝ L.direction = 1

/-- The lines of the plane containing at least `k` points of `S`. -/
def richLines (k : ℕ) (S : Finset ℝ²) : Set (AffineSubspace ℝ ℝ²) :=
  {L | IsLine L ∧ k ≤ ((L : Set ℝ²) ∩ S).ncard}

/-- The lines of the plane containing exactly `k` points of `S`. -/
def exactLines (k : ℕ) (S : Finset ℝ²) : Set (AffineSubspace ℝ ℝ²) :=
  {L | IsLine L ∧ ((L : Set ℝ²) ∩ S).ncard = k}

/-- `F k n`: the least `N` such that any `n` points of the plane have at most `N` lines through at
least `k` of them. -/
noncomputable def F (k n : ℕ) : ℕ :=
  sInf {N | ∀ S : Finset ℝ², S.card = n → (richLines k S).ncard ≤ N}

/-- `f k n`: the least `N` such that any `n` points of the plane have at most `N` lines through
exactly `k` of them. -/
noncomputable def f (k n : ℕ) : ℕ :=
  sInf {N | ∀ S : Finset ℝ², S.card = n → (exactLines k S).ncard ≤ N}

/-! ## Lines through two points -/

/-- The line through two distinct points is a line. -/
theorem isLine_pair {p q : ℝ²} (h : p ≠ q) : IsLine line[ℝ, p, q] := by
  unfold IsLine
  rw [direction_affineSpan, vectorSpan_pair]
  exact finrank_span_singleton (vsub_ne_zero.mpr h)

/-- A line through two distinct points `p`, `q` is `line[ℝ, p, q]`. -/
theorem eq_line {L : AffineSubspace ℝ ℝ²} (hL : IsLine L) {p q : ℝ²} (hp : p ∈ L) (hq : q ∈ L)
    (h : p ≠ q) : L = line[ℝ, p, q] := by
  have hle : line[ℝ, p, q] ≤ L := affineSpan_pair_le_of_mem_of_mem hp hq
  have hdir : (line[ℝ, p, q]).direction = L.direction :=
    Submodule.eq_of_le_of_finrank_eq (AffineSubspace.direction_le hle)
      (by rw [isLine_pair h]; exact hL.symm)
  exact (AffineSubspace.eq_of_direction_eq_of_nonempty_of_le hdir
    ⟨p, left_mem_affineSpan_pair ℝ p q⟩ hle).symm

theorem ncard_inter_eq (L : AffineSubspace ℝ ℝ²) (S : Finset ℝ²) [DecidablePred (· ∈ L)] :
    ((L : Set ℝ²) ∩ S).ncard = (S.filter (· ∈ L)).card := by
  rw [← Set.ncard_coe_finset, Finset.coe_filter]
  congr 1
  ext x
  simp [and_comm]

/-! ## Finiteness, and `F`, `f` as maxima -/

theorem exists_eq_line_of_mem_richLines {k : ℕ} (hk : 2 ≤ k) {S : Finset ℝ²}
    {L : AffineSubspace ℝ ℝ²} (hL : L ∈ richLines k S) :
    ∃ p ∈ S, ∃ q ∈ S, p ≠ q ∧ L = line[ℝ, p, q] := by
  classical
  obtain ⟨hl, hc⟩ := hL
  rw [ncard_inter_eq] at hc
  obtain ⟨p, hp, q, hq, hpq⟩ := Finset.one_lt_card.mp (by omega : 1 < (S.filter (· ∈ L)).card)
  simp only [Finset.mem_filter] at hp hq
  exact ⟨p, hp.1, q, hq.1, hpq, eq_line hl hp.2 hq.2 hpq⟩

theorem richLines_finite {k : ℕ} (hk : 2 ≤ k) (S : Finset ℝ²) : (richLines k S).Finite := by
  classical
  refine (S.offDiag.image fun pq => line[ℝ, pq.1, pq.2]).finite_toSet.subset ?_
  intro L hL
  obtain ⟨p, hp, q, hq, hpq, rfl⟩ := exists_eq_line_of_mem_richLines hk hL
  simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe, Finset.mem_offDiag]
  exact ⟨(p, q), ⟨hp, hq, hpq⟩, rfl⟩

theorem exactLines_subset (k : ℕ) (S : Finset ℝ²) : exactLines k S ⊆ richLines k S :=
  fun _ hL => ⟨hL.1, hL.2.ge⟩

theorem exactLines_finite {k : ℕ} (hk : 2 ≤ k) (S : Finset ℝ²) : (exactLines k S).Finite :=
  (richLines_finite hk S).subset (exactLines_subset k S)

/-- The counting bound: `ncard (richLines k S) · k(k-1) ≤ |S|(|S|-1)`, since a line through at
least `k` points of `S` contains at least `k(k-1)` ordered pairs of distinct points of `S`, and
two distinct points lie on only one line. -/
theorem ncard_richLines_mul_le {k : ℕ} (hk : 2 ≤ k) (S : Finset ℝ²) :
    (richLines k S).ncard * (k * (k - 1)) ≤ S.card * (S.card - 1) := by
  classical
  set Ls := (richLines_finite hk S).toFinset with hLs
  set s := S.offDiag.filter (fun pq => line[ℝ, pq.1, pq.2] ∈ richLines k S) with hs
  have h1 : k * (k - 1) * Ls.card ≤ s.card := by
    refine Finset.mul_card_image_le_card_of_maps_to
      (f := fun pq : ℝ² × ℝ² => line[ℝ, pq.1, pq.2]) ?_ _ ?_
    · intro pq hpq
      simp only [s, Finset.mem_filter] at hpq
      exact (Set.Finite.mem_toFinset _).mpr hpq.2
    · intro L hL
      rw [Set.Finite.mem_toFinset] at hL
      have hA := hL.2
      rw [ncard_inter_eq] at hA
      calc k * (k - 1) ≤ (S.filter (· ∈ L)).card * ((S.filter (· ∈ L)).card - 1) :=
            Nat.mul_le_mul hA (by omega)
        _ = (S.filter (· ∈ L)).offDiag.card := by rw [Finset.offDiag_card, Nat.mul_sub_one]
        _ ≤ _ := by
          apply Finset.card_le_card
          intro pq hpq
          simp only [Finset.mem_offDiag, Finset.mem_filter] at hpq
          have hl : L = line[ℝ, pq.1, pq.2] := eq_line hL.1 hpq.1.2 hpq.2.1.2 hpq.2.2
          simp only [s, Finset.mem_filter, Finset.mem_offDiag]
          exact ⟨⟨⟨hpq.1.1, hpq.2.1.1, hpq.2.2⟩, hl ▸ hL⟩, hl.symm⟩
  have h2 : s.card ≤ S.card * (S.card - 1) := by
    calc s.card ≤ S.offDiag.card := Finset.card_filter_le _ _
      _ = _ := by rw [Finset.offDiag_card, Nat.mul_sub_one]
  rw [Set.ncard_eq_toFinset_card _ (richLines_finite hk S), ← hLs, mul_comm]
  exact h1.trans h2

theorem isGreatest_sInf (v : Finset ℝ² → ℕ) (n B : ℕ)
    (hB : ∀ S : Finset ℝ², S.card = n → v S ≤ B) :
    IsGreatest {x | ∃ S : Finset ℝ², S.card = n ∧ v S = x}
      (sInf {N | ∀ S : Finset ℝ², S.card = n → v S ≤ N}) := by
  set V := {x | ∃ S : Finset ℝ², S.card = n ∧ v S = x} with hV
  have hne : V.Nonempty := by
    obtain ⟨S, hS⟩ := Infinite.exists_subset_card_eq ℝ² n
    exact ⟨_, S, hS, rfl⟩
  have hbdd : BddAbove V := ⟨B, by rintro _ ⟨S, hS, rfl⟩; exact hB S hS⟩
  obtain ⟨S₀, hS₀, hv⟩ := Nat.sSup_mem hne hbdd
  have hup : ∀ S : Finset ℝ², S.card = n → v S ≤ sSup V :=
    fun S hS => le_csSup hbdd ⟨S, hS, rfl⟩
  have heq : sInf {N | ∀ S : Finset ℝ², S.card = n → v S ≤ N} = sSup V := by
    refine le_antisymm (Nat.sInf_le ?_) (le_csInf ⟨_, hup⟩ fun N hN => hv ▸ hN S₀ hS₀)
    exact hup
  rw [heq]
  exact ⟨Nat.sSup_mem hne hbdd, fun x hx => le_csSup hbdd hx⟩

theorem ncard_richLines_le {k : ℕ} (hk : 2 ≤ k) (S : Finset ℝ²) :
    (richLines k S).ncard ≤ S.card * (S.card - 1) :=
  (Nat.le_mul_of_pos_right _ (Nat.mul_pos (by omega) (by omega))).trans
    (ncard_richLines_mul_le hk S)

/-- For `k ≥ 2`, `F k n` is the maximum, over all `n`-point sets, of the number of lines through
at least `k` of the points. -/
theorem isGreatest_F {k : ℕ} (hk : 2 ≤ k) (n : ℕ) :
    IsGreatest {x | ∃ S : Finset ℝ², S.card = n ∧ (richLines k S).ncard = x} (F k n) :=
  isGreatest_sInf _ n (n * (n - 1)) fun S hS => hS ▸ ncard_richLines_le hk S

/-- For `k ≥ 2`, `f k n` is the maximum, over all `n`-point sets, of the number of lines through
exactly `k` of the points. -/
theorem isGreatest_f {k : ℕ} (hk : 2 ≤ k) (n : ℕ) :
    IsGreatest {x | ∃ S : Finset ℝ², S.card = n ∧ (exactLines k S).ncard = x} (f k n) :=
  isGreatest_sInf _ n (n * (n - 1)) fun S hS => hS ▸
    (Set.ncard_le_ncard (exactLines_subset k S) (richLines_finite hk S)).trans
      (ncard_richLines_le hk S)

theorem f_le_F {k : ℕ} (hk : 2 ≤ k) (n : ℕ) : f k n ≤ F k n := by
  obtain ⟨S, hS, hv⟩ := (isGreatest_f hk n).1
  rw [← hv]
  exact (Set.ncard_le_ncard (exactLines_subset k S) (richLines_finite hk S)).trans
    ((isGreatest_F hk n).2 ⟨S, hS, rfl⟩)

/-- The trivial upper bound `F_k(n) · k(k-1) ≤ n(n-1)`. -/
theorem F_mul_le {k : ℕ} (hk : 2 ≤ k) (n : ℕ) : F k n * (k * (k - 1)) ≤ n * (n - 1) := by
  obtain ⟨S, hS, hv⟩ := (isGreatest_F hk n).1
  rw [← hv, ← hS]
  exact ncard_richLines_mul_le hk S

/-- The trivial upper bound `F_k(n) ≤ C(n,2)/C(k,2)` from the problem page, for `k ≥ 2`. -/
theorem erdos_669.variants.upper {k : ℕ} (hk : 2 ≤ k) (n : ℕ) :
    F k n * k.choose 2 ≤ n.choose 2 := by
  rw [Nat.choose_two_right, Nat.choose_two_right,
    ← Nat.mul_div_assoc _ (Nat.even_mul_pred_self k).two_dvd]
  exact Nat.div_le_div_right (F_mul_le hk n)

/-! ## The cubic curve `y (1 + x²) = 1` -/

/-- The point `(t, 1/(1+t²))`. -/
noncomputable def pt (t : ℝ) : ℝ² := !₂[t, 1 / (1 + t ^ 2)]

theorem pt_injective : Function.Injective pt := by
  intro s t h
  have := congrArg (fun x : ℝ² => x 0) h
  simpa [pt] using this

/-- Three points `pt s`, `pt t`, `pt u` with distinct parameters are collinear iff
`st + su + tu = 1`. -/
theorem mem_line_pt {s t u : ℝ} (hst : s ≠ t) (hsu : s ≠ u) (htu : t ≠ u) :
    pt u ∈ line[ℝ, pt s, pt t] ↔ s * t + s * u + t * u = 1 := by
  rw [← vsub_vadd (pt u) (pt s), vadd_left_mem_affineSpan_pair]
  have hs : (1 + s ^ 2) ≠ 0 := by positivity
  have ht : (1 + t ^ 2) ≠ 0 := by positivity
  have hu : (1 + u ^ 2) ≠ 0 := by positivity
  have hts : t - s ≠ 0 := sub_ne_zero.mpr hst.symm
  constructor
  · rintro ⟨r, hr⟩
    have h0 := congrArg (fun x : ℝ² => x 0) hr
    have h1 := congrArg (fun x : ℝ² => x 1) hr
    simp [pt] at h0 h1
    field_simp at h1
    have key : (u - s) * (u - t) * (1 - (s * t + s * u + t * u)) = 0 := by
      linear_combination h1 + (s + t) * (1 + u ^ 2) * h0
    have hus : u - s ≠ 0 := sub_ne_zero.mpr hsu.symm
    have hut : u - t ≠ 0 := sub_ne_zero.mpr htu.symm
    have := (mul_eq_zero.mp key).resolve_left (mul_ne_zero hus hut)
    linarith
  · intro he
    refine ⟨(u - s) / (t - s), ?_⟩
    ext i
    fin_cases i
    · simp [pt]; field_simp
    · simp [pt]; field_simp
      linear_combination (u - s) * (s - t) * (u - t) * he

/-- A line contains at most three points of the curve. -/
theorem card_filter_le_three {ι : Type*} (s : Finset ι) (τ : ι → ℝ) (hτ : Set.InjOn τ s)
    {L : AffineSubspace ℝ ℝ²} (hL : IsLine L) [DecidablePred fun j => pt (τ j) ∈ L] :
    (s.filter fun j => pt (τ j) ∈ L).card ≤ 3 := by
  classical
  by_cases h1 : (s.filter fun j => pt (τ j) ∈ L).card ≤ 1
  · omega
  obtain ⟨a, ha, b, hb, hab⟩ :=
    Finset.one_lt_card.mp (show 1 < (s.filter fun j => pt (τ j) ∈ L).card by omega)
  simp only [Finset.mem_filter] at ha hb
  have hτab : τ a ≠ τ b := fun h => hab (hτ ha.1 hb.1 h)
  have hLeq := eq_line hL ha.2 hb.2 fun h => hτab (pt_injective h)
  have hinj : Set.InjOn τ (s.filter fun j => pt (τ j) ∈ L : Finset ι) :=
    hτ.mono (Finset.coe_subset.mpr (Finset.filter_subset _ _))
  calc (s.filter fun j => pt (τ j) ∈ L).card
      = ((s.filter fun j => pt (τ j) ∈ L).image τ).card := (Finset.card_image_of_injOn hinj).symm
    _ ≤ ({τ a, τ b, (1 - τ a * τ b) / (τ a + τ b)} : Finset ℝ).card := by
        apply Finset.card_le_card
        intro x hx
        obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hx
        simp only [Finset.mem_filter] at hj
        simp only [Finset.mem_insert, Finset.mem_singleton]
        by_cases hja : τ j = τ a
        · exact Or.inl hja
        by_cases hjb : τ j = τ b
        · exact Or.inr (Or.inl hjb)
        right; right
        have he := (mem_line_pt hτab (Ne.symm hja) (Ne.symm hjb)).mp (hLeq ▸ hj.2)
        have hsum : τ a + τ b ≠ 0 := by
          intro h0
          have hb' : τ b = -τ a := by linarith
          rw [hb'] at he
          nlinarith [sq_nonneg (τ a)]
        field_simp
        linarith
    _ ≤ 3 := Finset.card_le_three

/-! ## Angles -/

/-- The angle `π/6 + π j/m`. -/
noncomputable def angle (m j : ℕ) : ℝ := π / 6 + π * j / m

theorem cast_ne_zero_of_not_three_dvd {m : ℕ} (hm : ¬ 3 ∣ m) : (m : ℝ) ≠ 0 := by
  have : m ≠ 0 := by rintro rfl; exact hm (dvd_zero 3)
  exact_mod_cast this

theorem cos_angle_ne_zero {m : ℕ} (hm : ¬ 3 ∣ m) (j : ℕ) : cos (angle m j) ≠ 0 := by
  intro h
  obtain ⟨k, hk⟩ := Real.cos_eq_zero_iff.mp h
  have hm0 := cast_ne_zero_of_not_three_dvd hm
  unfold angle at hk
  have hR : (m : ℝ) * (3 * k + 1) = 3 * j := by
    field_simp at hk
    linear_combination (-1 / 4 : ℝ) * hk
  have hZ : (m : ℤ) * (3 * k + 1) = 3 * j := by exact_mod_cast hR
  have h3 : (3 : ℤ) ∣ (m : ℤ) * (3 * k + 1) := ⟨j, hZ⟩
  rcases Int.prime_three.dvd_mul.mp h3 with h | h
  · exact hm (by exact_mod_cast h)
  · omega

theorem tan_angle_inj {m : ℕ} (hm : ¬ 3 ∣ m) {a b : ℕ} (ha : a < m) (hb : b < m)
    (h : tan (angle m a) = tan (angle m b)) : a = b := by
  have ca := cos_angle_ne_zero hm a
  have cb := cos_angle_ne_zero hm b
  have hm0 := cast_ne_zero_of_not_three_dvd hm
  rw [tan_eq_sin_div_cos, tan_eq_sin_div_cos, div_eq_div_iff ca cb] at h
  have hs : sin (angle m a - angle m b) = 0 := by rw [sin_sub]; linarith
  obtain ⟨k, hk⟩ := Real.sin_eq_zero_iff.mp hs
  unfold angle at hk
  have hR : (k : ℝ) * m = a - b := by
    field_simp at hk
    linear_combination hk / 6
  have hZ : k * (m : ℤ) = a - b := by exact_mod_cast hR
  have hk0 : k = 0 := by
    rcases lt_trichotomy k 0 with h | h | h
    · nlinarith
    · exact h
    · nlinarith
  subst hk0
  omega

/-- If `m ∣ a + b + c` then `t_a t_b + t_a t_c + t_b t_c = 1` for `t_j = tan (angle m j)`. -/
theorem e2_tan_angle {m : ℕ} (hm : ¬ 3 ∣ m) {a b c : ℕ} (h : m ∣ a + b + c) :
    tan (angle m a) * tan (angle m b) + tan (angle m a) * tan (angle m c) +
      tan (angle m b) * tan (angle m c) = 1 := by
  obtain ⟨q, hq⟩ := h
  have hm0 := cast_ne_zero_of_not_three_dvd hm
  have ca := cos_angle_ne_zero hm a
  have cb := cos_angle_ne_zero hm b
  have cc := cos_angle_ne_zero hm c
  have hcos : cos (angle m a + angle m b + angle m c) = 0 := by
    rw [Real.cos_eq_zero_iff]
    refine ⟨q, ?_⟩
    have hR : ((a : ℝ) + b + c) = m * q := by exact_mod_cast hq
    unfold angle
    field_simp
    push_cast
    linear_combination 12 * hR
  have iden : ∀ x y z : ℝ, cos x ≠ 0 → cos y ≠ 0 → cos z ≠ 0 →
      cos (x + y + z) =
        cos x * cos y * cos z * (1 - (tan x * tan y + tan x * tan z + tan y * tan z)) := by
    intro x y z hx hy hz
    rw [tan_eq_sin_div_cos, tan_eq_sin_div_cos, tan_eq_sin_div_cos, cos_add, cos_add, sin_add]
    field_simp
    ring
  rw [iden _ _ _ ca cb cc] at hcos
  have := (mul_eq_zero.mp hcos).resolve_left (mul_ne_zero (mul_ne_zero ca cb) cc)
  linarith

/-! ## The construction -/

/-- The modulus: `n` if `3 ∤ n`, otherwise `n + 1`. -/
def modulus (n : ℕ) : ℕ := if 3 ∣ n then n + 1 else n

theorem modulus_spec (n : ℕ) : ¬ 3 ∣ modulus n ∧ n ≤ modulus n ∧ modulus n ≤ n + 1 := by
  unfold modulus
  split_ifs with h <;> omega

theorem modulus_pos (n : ℕ) : 0 < modulus n := by
  have := (modulus_spec n).1
  rcases Nat.eq_zero_or_pos (modulus n) with h | h
  · rw [h] at this; exact absurd (dvd_zero 3) this
  · exact h

/-- The residue `c < m` with `a + b + c ≡ 0 (mod m)`. -/
def third (m a b : ℕ) : ℕ := (m - (a + b) % m) % m

theorem third_modEq {m : ℕ} (hm : 0 < m) (a b : ℕ) : a + b + third m a b ≡ 0 [MOD m] := by
  have h1 : a + b ≡ (a + b) % m [MOD m] := (Nat.mod_modEq _ _).symm
  have h2 : third m a b ≡ m - (a + b) % m [MOD m] := Nat.mod_modEq _ _
  have h3 := h1.add h2
  rw [Nat.add_sub_cancel' (Nat.mod_lt _ hm).le] at h3
  exact h3.trans (Nat.modEq_zero_iff_dvd.mpr dvd_rfl)

theorem eq_of_add_modEq {m x y z : ℕ} (hy : y < m) (hz : z < m) (h1 : x + y ≡ 0 [MOD m])
    (h2 : x + z ≡ 0 [MOD m]) : y = z :=
  Nat.ModEq.eq_of_lt_of_lt (Nat.ModEq.add_left_cancel' x (h1.trans h2.symm)) hy hz

/-- The `j`-th point of the construction for `n` points. -/
noncomputable def P (n j : ℕ) : ℝ² := pt (tan (angle (modulus n) j))

/-- The `n`-point set. -/
noncomputable def orchard (n : ℕ) : Finset ℝ² := (Finset.range n).image (P n)

theorem tan_injOn (n : ℕ) :
    Set.InjOn (fun j => tan (angle (modulus n) j)) (Finset.range n : Set ℕ) := by
  intro a ha b hb h
  simp only [Finset.coe_range, Set.mem_Iio] at ha hb
  have := modulus_spec n
  exact tan_angle_inj this.1 (by omega) (by omega) h

theorem P_injOn (n : ℕ) : Set.InjOn (P n) (Finset.range n : Set ℕ) :=
  fun _ ha _ hb h => tan_injOn n ha hb (pt_injective h)

theorem card_orchard (n : ℕ) : (orchard n).card = n := by
  rw [orchard, Finset.card_image_of_injOn (P_injOn n), Finset.card_range]

theorem third_lt {m : ℕ} (hm : 0 < m) (a b : ℕ) : third m a b < m := Nat.mod_lt _ hm

/-- At least `n² - 4n` ordered pairs `(a, b)` of indices below `n` have `a ≠ b` and a third index
`c < n`, different from `a` and `b`, with `a + b + c ≡ 0 (mod m)`. -/
theorem card_good_aux (n m : ℕ) (hm : 0 < m) (hnm : n ≤ m) (hmn : m ≤ n + 1) :
    n * n ≤ ((Finset.range n ×ˢ Finset.range n).filter fun ab =>
      ab.1 ≠ ab.2 ∧ third m ab.1 ab.2 < n ∧ third m ab.1 ab.2 ≠ ab.1 ∧
        third m ab.1 ab.2 ≠ ab.2).card + 4 * n := by
  classical
  set R := Finset.range n ×ˢ Finset.range n with hRdef
  have hR : R.card = n * n := by simp [R]
  have hbad : ∀ (p : ℕ × ℕ → Prop) [DecidablePred p] (g : ℕ × ℕ → ℕ),
      (∀ ab ∈ R, g ab < n) →
      (∀ ab ∈ R, ∀ ab' ∈ R, p ab → p ab' → g ab = g ab' → ab = ab') →
      (R.filter p).card ≤ n := by
    intro p _ g hg hinj
    calc (R.filter p).card ≤ (Finset.range n).card := by
          apply Finset.card_le_card_of_injOn g
          · intro ab hab
            simp only [Finset.coe_filter] at hab
            simpa using hg ab hab.1
          · intro ab hab ab' hab' h
            simp only [Finset.coe_filter] at hab hab'
            exact hinj ab hab.1 ab' hab'.1 hab.2 hab'.2 h
      _ = n := Finset.card_range n
  have hmem : ∀ ab ∈ R, ab.1 < n ∧ ab.2 < n := by
    intro ab hab
    simpa [R] using hab
  have hB1 : (R.filter fun ab => ab.1 = ab.2).card ≤ n :=
    hbad _ Prod.fst (fun ab h => (hmem ab h).1) fun ab _ ab' _ h h' e =>
      Prod.ext e (by rw [← h, ← h', e])
  have hB2 : (R.filter fun ab => n ≤ third m ab.1 ab.2).card ≤ n := by
    refine hbad _ Prod.fst (fun ab h => (hmem ab h).1) fun ab hab ab' hab' h h' e => ?_
    obtain ⟨a, b⟩ := ab
    obtain ⟨a', b'⟩ := ab'
    have hb := (hmem _ hab).2
    have hb' := (hmem _ hab').2
    simp only at h h' e hb hb'
    subst e
    have h1 : third m a b = n := by have := third_lt hm a b; omega
    have h2 : third m a b' = n := by have := third_lt hm a b'; omega
    have k1 := third_modEq hm a b
    have k2 := third_modEq hm a b'
    rw [h1, add_right_comm] at k1
    rw [h2, add_right_comm] at k2
    rw [eq_of_add_modEq (by omega) (by omega) k1 k2]
  have hB3 : (R.filter fun ab => third m ab.1 ab.2 = ab.1).card ≤ n := by
    refine hbad _ Prod.fst (fun ab h => (hmem ab h).1) fun ab hab ab' hab' h h' e => ?_
    obtain ⟨a, b⟩ := ab
    obtain ⟨a', b'⟩ := ab'
    have hb := (hmem _ hab).2
    have hb' := (hmem _ hab').2
    simp only at h h' e hb hb'
    subst e
    have k1 := third_modEq hm a b
    have k2 := third_modEq hm a b'
    rw [h, add_right_comm] at k1
    rw [h', add_right_comm] at k2
    rw [eq_of_add_modEq (by omega) (by omega) k1 k2]
  have hB4 : (R.filter fun ab => third m ab.1 ab.2 = ab.2).card ≤ n := by
    refine hbad _ Prod.snd (fun ab h => (hmem ab h).2) fun ab hab ab' hab' h h' e => ?_
    obtain ⟨a, b⟩ := ab
    obtain ⟨a', b'⟩ := ab'
    have ha := (hmem _ hab).1
    have ha' := (hmem _ hab').1
    simp only at h h' e ha ha'
    subst e
    have k1 := third_modEq hm a b
    have k2 := third_modEq hm a' b
    rw [h, add_assoc, add_comm] at k1
    rw [h', add_assoc, add_comm] at k2
    rw [eq_of_add_modEq (by omega) (by omega) k1 k2]
  have hsplit := Finset.card_filter_add_card_filter_not (s := R) fun ab =>
    ab.1 ≠ ab.2 ∧ third m ab.1 ab.2 < n ∧ third m ab.1 ab.2 ≠ ab.1 ∧ third m ab.1 ab.2 ≠ ab.2
  have hsub : (R.filter fun ab => ¬ (ab.1 ≠ ab.2 ∧ third m ab.1 ab.2 < n ∧
      third m ab.1 ab.2 ≠ ab.1 ∧ third m ab.1 ab.2 ≠ ab.2)) ⊆
      (R.filter fun ab => ab.1 = ab.2) ∪ (R.filter fun ab => n ≤ third m ab.1 ab.2) ∪
        (R.filter fun ab => third m ab.1 ab.2 = ab.1) ∪
        (R.filter fun ab => third m ab.1 ab.2 = ab.2) := by
    intro ab hab
    simp only [Finset.mem_filter, Finset.mem_union] at hab ⊢
    obtain ⟨hR, hn⟩ := hab
    by_cases c1 : ab.1 = ab.2
    · exact Or.inl (Or.inl (Or.inl ⟨hR, c1⟩))
    by_cases c2 : n ≤ third m ab.1 ab.2
    · exact Or.inl (Or.inl (Or.inr ⟨hR, c2⟩))
    by_cases c3 : third m ab.1 ab.2 = ab.1
    · exact Or.inl (Or.inr ⟨hR, c3⟩)
    by_cases c4 : third m ab.1 ab.2 = ab.2
    · exact Or.inr ⟨hR, c4⟩
    exact absurd ⟨c1, by omega, c3, c4⟩ hn
  have hc := Finset.card_le_card hsub
  have hu1 := Finset.card_union_le ((R.filter fun ab => ab.1 = ab.2) ∪
    (R.filter fun ab => n ≤ third m ab.1 ab.2) ∪
    (R.filter fun ab => third m ab.1 ab.2 = ab.1)) (R.filter fun ab => third m ab.1 ab.2 = ab.2)
  have hu2 := Finset.card_union_le ((R.filter fun ab => ab.1 = ab.2) ∪
    (R.filter fun ab => n ≤ third m ab.1 ab.2)) (R.filter fun ab => third m ab.1 ab.2 = ab.1)
  have hu3 := Finset.card_union_le (R.filter fun ab => ab.1 = ab.2)
    (R.filter fun ab => n ≤ third m ab.1 ab.2)
  omega

/-- The ordered pairs `(a, b)` of distinct indices below `n` whose third index is a new index
below `n`. -/
def good (n : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.range n ×ˢ Finset.range n).filter fun ab =>
    ab.1 ≠ ab.2 ∧ third (modulus n) ab.1 ab.2 < n ∧ third (modulus n) ab.1 ab.2 ≠ ab.1 ∧
      third (modulus n) ab.1 ab.2 ≠ ab.2

theorem card_good (n : ℕ) : n * n ≤ (good n).card + 4 * n :=
  card_good_aux n (modulus n) (modulus_pos n) (modulus_spec n).2.1 (modulus_spec n).2.2

/-- Each good pair spans a line with exactly three points of `orchard n`, and each such line comes
from at most six good pairs. -/
theorem card_good_le (n : ℕ) : (good n).card ≤ 6 * (exactLines 3 (orchard n)).ncard := by
  classical
  obtain ⟨hm3, -, -⟩ := modulus_spec n
  have hm := modulus_pos n
  have hfin := exactLines_finite (by norm_num : 2 ≤ 3) (orchard n)
  rw [Set.ncard_eq_toFinset_card _ hfin]
  have hA : ∀ L : AffineSubspace ℝ ℝ², IsLine L →
      ((Finset.range n).filter fun j => P n j ∈ L).card ≤ 3 := fun L hL =>
    card_filter_le_three (Finset.range n) (fun j => tan (angle (modulus n) j)) (tan_injOn n) hL
  have hinter : ∀ L : AffineSubspace ℝ ℝ², ((L : Set ℝ²) ∩ (orchard n)).ncard =
      ((Finset.range n).filter fun j => P n j ∈ L).card := by
    intro L
    rw [ncard_inter_eq, orchard, Finset.filter_image, Finset.card_image_of_injOn]
    exact (P_injOn n).mono (Finset.coe_subset.mpr (Finset.filter_subset _ _))
  refine Finset.card_le_mul_card_image_of_maps_to
    (f := fun ab : ℕ × ℕ => line[ℝ, P n ab.1, P n ab.2]) ?_ 6 ?_
  · rintro ⟨a, b⟩ hab
    simp only [good, Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hab
    obtain ⟨⟨ha, hb⟩, hne, hc, hca, hcb⟩ := hab
    have hPab : P n a ≠ P n b := fun h => hne (P_injOn n (by simpa) (by simpa) h)
    rw [Set.Finite.mem_toFinset]
    refine ⟨isLine_pair hPab, ?_⟩
    rw [hinter]
    apply le_antisymm (hA _ (isLine_pair hPab))
    have hne' : ∀ x y, x < n → y < n → x ≠ y →
        tan (angle (modulus n) x) ≠ tan (angle (modulus n) y) :=
      fun x y hx hy hxy h => hxy (tan_injOn n (by simpa) (by simpa) h)
    have hsub : ({a, b, third (modulus n) a b} : Finset ℕ) ⊆
        (Finset.range n).filter fun j => P n j ∈ line[ℝ, P n a, P n b] := by
      intro j hj
      simp only [Finset.mem_insert, Finset.mem_singleton] at hj
      simp only [Finset.mem_filter, Finset.mem_range]
      rcases hj with rfl | rfl | rfl
      · exact ⟨ha, left_mem_affineSpan_pair _ _ _⟩
      · exact ⟨hb, right_mem_affineSpan_pair _ _ _⟩
      · refine ⟨hc, ?_⟩
        exact (mem_line_pt (hne' a b ha hb hne) (hne' _ _ ha hc (Ne.symm hca))
          (hne' _ _ hb hc (Ne.symm hcb))).mpr
          (e2_tan_angle hm3 (Nat.modEq_zero_iff_dvd.mp (third_modEq hm a b)))
    calc 3 = ({a, b, third (modulus n) a b} : Finset ℕ).card :=
          (Finset.card_eq_three.mpr ⟨a, b, _, hne, Ne.symm hca, Ne.symm hcb, rfl⟩).symm
      _ ≤ _ := Finset.card_le_card hsub
  · intro L hL
    rw [Set.Finite.mem_toFinset] at hL
    calc (Finset.filter (fun ab : ℕ × ℕ => line[ℝ, P n ab.1, P n ab.2] = L) (good n)).card
        ≤ ((Finset.range n).filter fun j => P n j ∈ L).offDiag.card := by
          apply Finset.card_le_card
          rintro ⟨a, b⟩ hab
          simp only [good, Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hab
          simp only [Finset.mem_offDiag, Finset.mem_filter, Finset.mem_range]
          obtain ⟨⟨⟨ha, hb⟩, hne, -⟩, rfl⟩ := hab
          exact ⟨⟨ha, left_mem_affineSpan_pair _ _ _⟩, ⟨hb, right_mem_affineSpan_pair _ _ _⟩, hne⟩
      _ ≤ 6 := by
          rw [Finset.offDiag_card]
          have := hA L hL.1
          generalize ((Finset.range n).filter fun j => P n j ∈ L).card = c at this ⊢
          interval_cases c <;> simp

/-! ## Main results for `k = 3` -/

/-- The lower bound `f₃(n) ≥ (n² - 4n)/6`. -/
theorem le_f_three (n : ℕ) : n * n ≤ 6 * f 3 n + 4 * n := by
  have h1 := card_good n
  have h2 := card_good_le n
  have h3 : (exactLines 3 (orchard n)).ncard ≤ f 3 n :=
    (isGreatest_f (by norm_num) n).2 ⟨orchard n, card_orchard n, rfl⟩
  omega

theorem bounds_three (n : ℕ) :
    ((n : ℝ) ^ 2 - 4 * n) / 6 ≤ f 3 n ∧ (f 3 n : ℝ) ≤ F 3 n ∧ (F 3 n : ℝ) ≤ (n : ℝ) ^ 2 / 6 := by
  have h1 : ((n * n : ℕ) : ℝ) ≤ ((6 * f 3 n + 4 * n : ℕ) : ℝ) := by exact_mod_cast le_f_three n
  have h2 : ((f 3 n : ℕ) : ℝ) ≤ ((F 3 n : ℕ) : ℝ) := by exact_mod_cast f_le_F (by norm_num) n
  have h3 : ((F 3 n * 6 : ℕ) : ℝ) ≤ ((n * n : ℕ) : ℝ) := by
    have := F_mul_le (by norm_num : 2 ≤ 3) n
    exact_mod_cast this.trans (Nat.mul_le_mul_left _ (Nat.sub_le _ _))
  push_cast at h1 h3
  refine ⟨by nlinarith, h2, by nlinarith⟩

/-- **Burr–Grünbaum–Sloane** (`k = 3`): `lim F₃(n)/n² = lim f₃(n)/n² = 1/6`. -/
theorem erdos_669.variants.three :
    Tendsto (fun n => (F 3 n : ℝ) / n ^ 2) atTop (𝓝 (1 / 6)) ∧
      Tendsto (fun n => (f 3 n : ℝ) / n ^ 2) atTop (𝓝 (1 / 6)) := by
  have hlow : Tendsto (fun n : ℕ => (1 / 6 : ℝ) - (2 / 3) / n) atTop (𝓝 (1 / 6)) := by
    simpa using tendsto_const_nhds.sub (tendsto_const_div_atTop_nhds_zero_nat (2 / 3 : ℝ))
  have hlo : ∀ᶠ n : ℕ in atTop, (1 / 6 : ℝ) - (2 / 3) / n ≤ (f 3 n : ℝ) / n ^ 2 := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    have h1 := (bounds_three n).1
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    rw [le_div_iff₀ (by positivity)]
    have : ((1 / 6 : ℝ) - (2 / 3) / n) * n ^ 2 = ((n : ℝ) ^ 2 - 4 * n) / 6 := by
      field_simp
      ring
    linarith
  have hmid : ∀ n : ℕ, (f 3 n : ℝ) / n ^ 2 ≤ (F 3 n : ℝ) / n ^ 2 := fun n =>
    div_le_div_of_nonneg_right (bounds_three n).2.1 (by positivity)
  have hup : ∀ n : ℕ, (F 3 n : ℝ) / n ^ 2 ≤ 1 / 6 := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · have hn' : (0 : ℝ) < n := by exact_mod_cast hn
      rw [div_le_iff₀ (by positivity)]
      linarith [(bounds_three n).2.2]
  refine ⟨tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds ?_
      (Eventually.of_forall hup),
    tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds hlo
      (Eventually.of_forall fun n => (hmid n).trans (hup n))⟩
  filter_upwards [hlo] with n hn using hn.trans (hmid n)

/-- **Burr–Grünbaum–Sloane** (`k = 3`), in the form of the problem page:
`f₃(n) = n²/6 - O(n)` and `F₃(n) = n²/6 - O(n)`. -/
theorem erdos_669.variants.three_isBigO :
    (fun n => (f 3 n : ℝ) - n ^ 2 / 6) =O[atTop] (fun n => (n : ℝ)) ∧
      (fun n => (F 3 n : ℝ) - n ^ 2 / 6) =O[atTop] (fun n => (n : ℝ)) := by
  constructor
  all_goals
    refine IsBigO.of_bound 1 (Eventually.of_forall fun n => ?_)
    obtain ⟨h1, h2, h3⟩ := bounds_three n
    have hn : (0 : ℝ) ≤ n := n.cast_nonneg
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hn, one_mul, abs_le]
    constructor <;> linarith

end Erdos669
