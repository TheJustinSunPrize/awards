import Mathlib

/-!
# Erdős Problem 188: `k ≥ 6` (Tsaturian's theorem)

Erdős Problem 188 ([erdosproblems.com/188](https://www.erdosproblems.com/188)) asks for the
smallest `k` such that `ℝ²` can be red/blue coloured with no two red points at distance `1` and no
`k`-term arithmetic progression of blue points with distance `1`. Erdős, Graham, Montgomery,
Rothschild, Spencer and Straus [EGMRSS75] proved `k ≥ 5`. Tsaturian [Ts17] improved this to
`k ≥ 6`: every such colouring contains five blue points on a line with consecutive distances `1`
(a blue `ℓ₅`). The problem itself is open. This file formalizes Tsaturian's theorem and the lower
bound `k ≥ 6`.

## Statements

The definitions `Set.IsAPOfLengthWith` and `Erdos188.s` are copied verbatim from Google DeepMind's
formal-conjectures project (Apache-2.0), files
`FormalConjecturesForMathlib/Combinatorics/AP/Basic.lean` and
`FormalConjectures/ErdosProblems/188.lean`. `Erdos188.s` is the set of `k` for which a colouring as
in the problem exists (red points are `Set.univ \ blue`); the problem asks for its least element.

* `Erdos188.tsaturian` ([Ts17, Theorem 1.1]): for every `blue : Set ℂ` with
  `(Set.univ \ blue).Pairwise (fun c₁ c₂ => dist c₁ c₂ ≠ 1)` there are `z d : ℂ` with `‖d‖ = 1`
  and `z + n • d ∈ blue` for all `n < 5`.
* `Erdos188.tsaturian_euclidean`: the same statement in `EuclideanSpace ℝ (Fin 2)`.
* `Erdos188.erdos_188.variants.six_le : ∀ k, k ∈ s → 6 ≤ k`. For `k ≤ 5`, the first `k` of the five
  blue points form a set `bs ⊆ blue` with `bs.IsAPOfLengthWith k z d` and `‖d‖ = 1`.
* `Erdos188.erdos_188.variants.isLeast_six_le`: `IsLeast s m → 6 ≤ m`, i.e. the answer to
  formal-conjectures' `erdos_188` is at least `6`.
* `Erdos188.erdos_188.variants.estimate_left : ∀ k, k ∈ s → 5 ≤ k`, the first conjunct of
  formal-conjectures' `erdos_188.variants.estimate`.

Not covered: that `s` is nonempty (some finite `k` works) and any upper bound.

## Proof

The proof follows [Ts17]. Points of the plane are complex numbers and `ω = e^{iπ/3}`. Assume there
is no red unit pair (`NoRedPair`) and no blue `ℓ₅` (`NoBlueℓ5`).

* Lemma 2.1 (`no_blue_triangle`, Figure 1a): no blue equilateral triangle of side `3` with a red
  centre.
* Lemma 2.2 (`no_red_triangle`): no red equilateral triangle of side `3` with a red centre. [Ts17]
  writes side `√3`, a typo (noted on the erdosproblems forum); the proof is for side `3`. Rotating
  the triangle about its centre by `θ` with `cos θ = 5/6` moves each vertex by exactly `1`.
* Lemma 2.3 (`no_red_T7`, Figure 3): no red `T₇`. As in [Ts17], only the five points
  `A, B, C, D, F` are used, with rotations by `θ` about `B` and `C`.
* For a red `A` and a unit vector `u`, the colouring of the lattice `A + (ℤ + ℤ ω) u` is
  `f : ℤ × ℤ → Prop`. `Good f` records the conditions above for lattice configurations
  (`good_of`). `frame f q k` recentres the lattice at `q` and rotates it by `k · 60°`. `Good` is
  invariant under this (`Good.frame`), so each figure is treated in one position, and all
  coordinates are checked by `decide`.
* Lemma 2.4 (Figures 4–6): `T3_to_T4`, `T4_to_T5`, `T5_to_T6`, and `T3_to_T6`, which lists the four
  `T₆` that can contain a given red `T₃`.
* Lemma 2.5 (Figures 7 and 8): `T6_step` (a red `T₆` forces its translate by `5`), the two other
  directions by the `120°` symmetry of `T₆` (`T6_step₂`, `T6_step₃`), all translates by `5ℤ²`
  (`T6_periodic`), and `T6_cover`: every other lattice point is adjacent to one of these red
  points. So in this case the lattice colouring is invariant under `5ℤ²`.
* Lemma 2.6 (Figures 9 and 10): if the lattice has no red `T₃`, then `T3free_step` (Figure 10) is
  applied three times to reach the red point at distance `5`. The full description of Figure 9 is
  not needed.
* `lattice_main`: in both cases, if the lattice point `(0, 0)` is red then so is `(5, 0)`. Hence
  `red_shift`: if `A` is red then `A + 5u` is red for every unit vector `u`.
* Theorem 1.1 (`exists_blue_ℓ5`): take a red `A`, `B = A + 5` and `C = A + 5v` with
  `v = (49 + i√99)/50`, so that `|BC| = 1`. Both `B` and `C` are red, a contradiction.

Small typos in [Ts17] are read in the evident way: in the proof of Lemma 2.1, `XADEB` would be a
blue `ℓ₅`; in the proof of Lemma 2.2, `A, B, C` are red; in the proof of Lemma 2.5, `A′JNMR` would
be a blue `ℓ₅` and `A′, …, F′` are red.

## Credits

The mathematics is due to Tsaturian [Ts17]. The Lean formalization was written with AI assistance
(Claude, Anthropic).

## References

* [Ts17] S. Tsaturian, _A Euclidean Ramsey result in the plane_, Electron. J. Combin. 24 (2017),
  no. 4, Paper 4.35; arXiv:1703.10723.
* [EGMRSS75] P. Erdős, R. L. Graham, P. Montgomery, B. L. Rothschild, J. Spencer and E. G. Straus,
  _Euclidean Ramsey theorems II_, Infinite and finite sets (Colloq., Keszthely, 1973), Vol. I,
  Colloq. Math. Soc. János Bolyai 10, North-Holland, 1975, 529–557.
* [erdosproblems.com/188](https://www.erdosproblems.com/188)
-/

set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

section APDefs

-- Copied verbatim from formal-conjectures,
-- `FormalConjecturesForMathlib/Combinatorics/AP/Basic.lean` (Apache-2.0).

variable {α : Type*} [AddCommMonoid α]

/--
A set $S$ is an arithmetic progression of length $l$ with first term $a$ and difference $d$
if $S = \{a, a + d, ..., a + (l - 1)d\}$, if $l$ if finite, else $S = \{a, a + d, a + 2d, ...\}.
This can be written as `s.IsAPOfLengthWith l a d`, where `l : ℕ∞` may take the infinite
value `⊤`.
-/
def Set.IsAPOfLengthWith (s : Set α) (l : ℕ∞) (a d : α) : Prop :=
  ENat.card s = l ∧ s = {a + n • d | (n : ℕ) (_ : n < l)}

end APDefs

namespace Erdos188

-- Copied verbatim from formal-conjectures, `FormalConjectures/ErdosProblems/188.lean`
-- (Apache-2.0).

/--
The set of numbers $k$ such that $\mathbb{R}^2$ can be red/blue coloured with no pair of red
points unit distance apart, and no $k$-term arithmetic progression of blue points with distance 1.
-/
def s := { k : ℕ | ∃ blue : Set ℂ,
  (Set.univ \ blue).Pairwise (fun c₁ c₂ => dist c₁ c₂ ≠ 1) ∧
    ¬ (∃ᵉ (bs ⊆ blue) (z) (d), ‖d‖ = 1 ∧ bs.IsAPOfLengthWith k z d) }

/-! ### Plane geometry: Lemmas 2.1–2.3 of Tsaturian -/

/-- `ω = e^{iπ/3}`. -/
noncomputable def ω : ℂ := ⟨1/2, Real.sqrt 3 / 2⟩

/-- `θ = e^{iα}` with `cos α = 5/6`, so that `|1 - θ| = 1/√3`. -/
noncomputable def θ : ℂ := ⟨5/6, Real.sqrt 11 / 6⟩

lemma sqrt3_sq : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num)
lemma sqrt11_sq : Real.sqrt 11 * Real.sqrt 11 = 11 := Real.mul_self_sqrt (by norm_num)

lemma ω_sq : ω ^ 2 = ω - 1 := by
  apply Complex.ext <;> simp [ω, sq] <;> nlinarith [sqrt3_sq]

lemma normSq_ω : Complex.normSq ω = 1 := by
  simp [ω, Complex.normSq_apply]; nlinarith [sqrt3_sq]

lemma normSq_ω_sub_one : Complex.normSq (ω - 1) = 1 := by
  simp [ω, Complex.normSq_apply]; nlinarith [sqrt3_sq]

lemma normSq_θ : Complex.normSq θ = 1 := by
  simp [θ, Complex.normSq_apply]; nlinarith [sqrt11_sq]

lemma normSq_one_sub_θ : Complex.normSq (1 - θ) = 1 / 3 := by
  simp [θ, Complex.normSq_apply]; nlinarith [sqrt11_sq]

lemma norm_eq_one_of_normSq {z : ℂ} (h : Complex.normSq z = 1) : ‖z‖ = 1 := by
  have h2 : ‖z‖ ^ 2 = 1 := by rw [← Complex.normSq_eq_norm_sq]; exact h
  have := norm_nonneg z
  nlinarith

lemma normSq_one_sub_ω : Complex.normSq (1 - ω) = 1 := by
  simp [ω, Complex.normSq_apply]; nlinarith [sqrt3_sq]

lemma normSq_two_ω_sub_one : Complex.normSq (2 * ω - 1) = 3 := by
  simp [ω, Complex.normSq_apply]; nlinarith [sqrt3_sq]

section Geometry

/-- No two red points are at distance `1`. -/
def NoRedPair (R : ℂ → Prop) : Prop := ∀ x y, R x → R y → ‖x - y‖ ≠ 1

/-- Every `ℓ₅` (five points `z, z + d, …, z + 4d` with `‖d‖ = 1`) contains a red point. -/
def NoBlueℓ5 (R : ℂ → Prop) : Prop :=
  ∀ z d : ℂ, ‖d‖ = 1 → R z ∨ R (z + d) ∨ R (z + 2 * d) ∨ R (z + 3 * d) ∨ R (z + 4 * d)

variable {R : ℂ → Prop}

lemma blue_of_adj (hadj : NoRedPair R) {x y : ℂ} (hx : R x)
    (e : ‖x - y‖ = 1) : ¬ R y := fun hy => hadj x y hx hy e

lemma red_of_l5 (h5 : NoBlueℓ5 R)
    {z d p1 p2 p3 p4 : ℂ} (hd : ‖d‖ = 1) (e1 : z + d = p1) (e2 : z + 2 * d = p2)
    (e3 : z + 3 * d = p3) (e4 : z + 4 * d = p4) (h1 : ¬R p1) (h2 : ¬R p2) (h3 : ¬R p3)
    (h4 : ¬R p4) : R z := by
  subst e1 e2 e3 e4
  rcases h5 z d hd with h | h | h | h | h
  · exact h
  · exact absurd h h1
  · exact absurd h h2
  · exact absurd h h3
  · exact absurd h h4

lemma norm_mul_one {c u : ℂ} (hc : Complex.normSq c = 1) (hu : ‖u‖ = 1) : ‖c * u‖ = 1 := by
  rw [norm_mul, hu, norm_eq_one_of_normSq hc, one_mul]

/-- Lemma 2.1 of Tsaturian, in the frame of a unit vector `u`. -/
lemma no_blue_triangle_frame (hadj : NoRedPair R) (h5 : NoBlueℓ5 R)
    {O u : ℂ} (hu : ‖u‖ = 1) (hO : R O) (hA : ¬R (O + (1 - 2 * ω) * u))
    (hC : ¬R (O + (1 + ω) * u)) (hB : ¬R (O + (ω - 2) * u)) : False := by
  have nω : ‖ω * u‖ = 1 := norm_mul_one normSq_ω hu
  have nω1 : ‖(ω - 1) * u‖ = 1 := norm_mul_one normSq_ω_sub_one hu
  have hD : ¬R (O - ω * u) :=
    blue_of_adj hadj hO (by rw [show O - (O - ω * u) = ω * u by ring]; exact nω)
  have hE : ¬R (O - u) := blue_of_adj hadj hO (by rw [show O - (O - u) = u by ring]; exact hu)
  have hF : ¬R (O + (1 - ω) * u) :=
    blue_of_adj hadj hO (by rw [show O - (O + (1 - ω) * u) = (ω - 1) * u by ring]; exact nω1)
  have hG : ¬R (O + u) :=
    blue_of_adj hadj hO (by rw [show O - (O + u) = -u by ring, norm_neg]; exact hu)
  have hX : R (O + (2 - 3 * ω) * u) :=
    red_of_l5 h5 nω1 (by ring) (by ring) (by ring) (by ring) hA hD hE hB
  have hY : R (O + (1 - 3 * ω) * u) :=
    red_of_l5 h5 nω (by ring) (by ring) (by ring) (by ring) hA hF hG hC
  exact hadj _ _ hX hY
    (by rw [show O + (2 - 3 * ω) * u - (O + (1 - 3 * ω) * u) = u by ring]; exact hu)

/-- Lemma 2.1 of Tsaturian: no blue equilateral triangle of side `3` with a red centre. -/
lemma no_blue_triangle (hadj : NoRedPair R) (h5 : NoBlueℓ5 R)
    {O t : ℂ} (ht : Complex.normSq t = 3) (hO : R O) (h1 : ¬R (O + t))
    (h2 : ¬R (O + t * ω ^ 2)) (h3 : ¬R (O + t * ω ^ 4)) : False := by
  have hu : ‖t * (2 * ω - 1) / 3‖ = 1 := by
    apply norm_eq_one_of_normSq
    rw [Complex.normSq_div, Complex.normSq_mul, ht, normSq_two_ω_sub_one]
    norm_num [Complex.normSq_apply]
  refine no_blue_triangle_frame hadj h5 hu hO ?_ ?_ ?_
  · rwa [show O + (1 - 2 * ω) * (t * (2 * ω - 1) / 3) = O + t by
      linear_combination (-4*t/3) * ω_sq]
  · rwa [show O + (1 + ω) * (t * (2 * ω - 1) / 3) = O + t * ω ^ 2 by
      linear_combination (-t/3) * ω_sq]
  · rwa [show O + (ω - 2) * (t * (2 * ω - 1) / 3) = O + t * ω ^ 4 by
      linear_combination (-t*ω^2 - t*ω + 2*t/3) * ω_sq]

/-- Lemma 2.2 of Tsaturian (with side length `3`): no red equilateral triangle of side `3` with a
red centre. -/
lemma no_red_triangle (hadj : NoRedPair R) (h5 : NoBlueℓ5 R)
    {O t : ℂ} (ht : Complex.normSq t = 3) (hO : R O) (h1 : R (O + t))
    (h2 : R (O + t * ω ^ 2)) (h3 : R (O + t * ω ^ 4)) : False := by
  have n2 : Complex.normSq (ω ^ 2) = 1 := by rw [map_pow, normSq_ω, one_pow]
  have n4 : Complex.normSq (ω ^ 4) = 1 := by rw [map_pow, normSq_ω, one_pow]
  refine no_blue_triangle hadj h5 (t := t * θ)
    (by rw [Complex.normSq_mul, ht, normSq_θ, mul_one]) hO ?_ ?_ ?_
  · refine blue_of_adj hadj h1 (norm_eq_one_of_normSq ?_)
    rw [show O + t - (O + t * θ) = t * (1 - θ) by ring, Complex.normSq_mul, ht, normSq_one_sub_θ]
    norm_num
  · refine blue_of_adj hadj h2 (norm_eq_one_of_normSq ?_)
    rw [show O + t * ω ^ 2 - (O + t * θ * ω ^ 2) = t * ω ^ 2 * (1 - θ) by ring,
      Complex.normSq_mul, Complex.normSq_mul, ht, n2, normSq_one_sub_θ]
    norm_num
  · refine blue_of_adj hadj h3 (norm_eq_one_of_normSq ?_)
    rw [show O + t * ω ^ 4 - (O + t * θ * ω ^ 4) = t * ω ^ 4 * (1 - θ) by ring,
      Complex.normSq_mul, Complex.normSq_mul, ht, n4, normSq_one_sub_θ]
    norm_num

/-- Lemma 2.3 of Tsaturian (the five points of a `T₇` that its proof uses): there are no red
points `A, B, C, D, F` with `A, B, C, D` on a line at spacing `√3` and `F` at distance `√3` from
both `B` and `C`. -/
lemma no_red_T7 (hadj : NoRedPair R) (h5 : NoBlueℓ5 R)
    {p s : ℂ} (hs : Complex.normSq s = 3) (hA : R p) (hB : R (p + s)) (hC : R (p + 2 * s))
    (hD : R (p + 3 * s)) (hF : R (p + 2 * s - s * ω)) : False := by
  have n1θ : Complex.normSq (s * (1 - θ)) = 1 := by
    rw [Complex.normSq_mul, hs, normSq_one_sub_θ]; norm_num
  have hX' : R (p + s + θ * s * ω) := by
    by_contra hX'
    refine no_blue_triangle hadj h5 (O := p + s) (t := θ * s * ω)
      (by rw [Complex.normSq_mul, Complex.normSq_mul, hs, normSq_θ, normSq_ω]; norm_num)
      hB hX' ?_ ?_
    · refine blue_of_adj hadj hA (norm_eq_one_of_normSq ?_)
      rw [show p - (p + s + θ * s * ω * ω ^ 2) = -(s * (1 - θ)) by
        linear_combination (-s*θ*ω - s*θ) * ω_sq, Complex.normSq_neg]
      exact n1θ
    · refine blue_of_adj hadj hF (norm_eq_one_of_normSq ?_)
      rw [show p + 2 * s - s * ω - (p + s + θ * s * ω * ω ^ 4) = s * (1 - θ) * (1 - ω) by
        linear_combination (-s*θ*ω^3 - s*θ*ω^2 + s*θ) * ω_sq,
        Complex.normSq_mul, n1θ, normSq_one_sub_ω, one_mul]
  have hX'' : R (p + 2 * s + θ * s * ω ^ 2) := by
    by_contra hX''
    refine no_blue_triangle hadj h5 (O := p + 2 * s) (t := θ * s)
      (by rw [Complex.normSq_mul, hs, normSq_θ]; norm_num) hC ?_ ?_ ?_
    · refine blue_of_adj hadj hD (norm_eq_one_of_normSq ?_)
      rw [show p + 3 * s - (p + 2 * s + θ * s) = s * (1 - θ) by ring]
      exact n1θ
    · exact hX''
    · refine blue_of_adj hadj hF (norm_eq_one_of_normSq ?_)
      rw [show p + 2 * s - s * ω - (p + 2 * s + θ * s * ω ^ 4) = -(s * (1 - θ) * ω) by
        linear_combination (-s*θ*ω^2 - s*θ*ω) * ω_sq,
        Complex.normSq_neg, Complex.normSq_mul, n1θ, normSq_ω, one_mul]
  refine hadj _ _ hX' hX'' (norm_eq_one_of_normSq ?_)
  rw [show p + s + θ * s * ω - (p + 2 * s + θ * s * ω ^ 2) = -(s * (1 - θ)) by
    linear_combination (-s*θ) * ω_sq, Complex.normSq_neg]
  exact n1θ

end Geometry

/-! ### Lattice combinatorics -/

/-- Multiplication by `ω = e^{iπ/3}` in the coordinates `(a, b) ↦ a + b ω`. -/
def rot (v : ℤ × ℤ) : ℤ × ℤ := (-v.2, v.1 + v.2)

/-- The norm form: `|a + b ω|² = a² + ab + b²`. -/
def N (v : ℤ × ℤ) : ℤ := v.1 * v.1 + v.1 * v.2 + v.2 * v.2

lemma rot_add (a b : ℤ × ℤ) : rot (a + b) = rot a + rot b := by
  ext <;> simp [rot] <;> ring

lemma rot_sub (a b : ℤ × ℤ) : rot (a - b) = rot a - rot b := by
  ext <;> simp [rot] <;> ring

lemma N_rot (a : ℤ × ℤ) : N (rot a) = N a := by
  simp [N, rot]; ring

/-- The conditions on a colouring of a unit triangular lattice (`f v` means "`v` is red") that the
proof uses: no red unit pair, no blue `ℓ₅`, and Lemmas 2.1, 2.2 and 2.3 of Tsaturian. -/
structure Good (f : ℤ × ℤ → Prop) : Prop where
  adj : ∀ p e, N e = 1 → f p → f (p + e) → False
  l5 : ∀ p e, N e = 1 → ¬f p → ¬f (p + e) → ¬f (p + e + e) → ¬f (p + e + e + e) →
    ¬f (p + e + e + e + e) → False
  l21 : ∀ p t, N t = 3 → f p → ¬f (p + t) → ¬f (p + rot (rot t)) →
    ¬f (p + rot (rot (rot (rot t)))) → False
  l22 : ∀ p t, N t = 3 → f p → f (p + t) → f (p + rot (rot t)) →
    f (p + rot (rot (rot (rot t)))) → False
  l23 : ∀ p s, N s = 3 → f p → f (p + s) → f (p + s + s) → f (p + s + s + s) →
    f (p + s + s - rot s) → False

variable {f : ℤ × ℤ → Prop}

lemma Good.trans (hf : Good f) (q : ℤ × ℤ) : Good (fun x => f (q + x)) where
  adj p e he h1 h2 := hf.adj (q + p) e he h1 (by simpa [add_assoc] using h2)
  l5 p e he h1 h2 h3 h4 h5 := hf.l5 (q + p) e he h1 (by simpa [add_assoc] using h2)
    (by simpa [add_assoc] using h3) (by simpa [add_assoc] using h4) (by simpa [add_assoc] using h5)
  l21 p t ht h1 h2 h3 h4 := hf.l21 (q + p) t ht h1 (by simpa [add_assoc] using h2)
    (by simpa [add_assoc] using h3) (by simpa [add_assoc] using h4)
  l22 p t ht h1 h2 h3 h4 := hf.l22 (q + p) t ht h1 (by simpa [add_assoc] using h2)
    (by simpa [add_assoc] using h3) (by simpa [add_assoc] using h4)
  l23 p s hs h1 h2 h3 h4 h5 := hf.l23 (q + p) s hs h1 (by simpa [add_assoc] using h2)
    (by simpa [add_assoc] using h3) (by simpa [add_assoc] using h4)
    (by simpa [add_assoc, add_sub_assoc] using h5)

lemma Good.rotate (hf : Good f) : Good (fun x => f (rot x)) where
  adj p e he h1 h2 := hf.adj (rot p) (rot e) (by rwa [N_rot]) h1 (by rwa [← rot_add])
  l5 p e he h1 h2 h3 h4 h5 := hf.l5 (rot p) (rot e) (by rwa [N_rot]) h1 (by rwa [← rot_add])
    (by rwa [← rot_add, ← rot_add]) (by rwa [← rot_add, ← rot_add, ← rot_add])
    (by rwa [← rot_add, ← rot_add, ← rot_add, ← rot_add])
  l21 p t ht h1 h2 h3 h4 := hf.l21 (rot p) (rot t) (by rwa [N_rot]) h1 (by rwa [← rot_add])
    (by rwa [← rot_add]) (by rwa [← rot_add])
  l22 p t ht h1 h2 h3 h4 := hf.l22 (rot p) (rot t) (by rwa [N_rot]) h1 (by rwa [← rot_add])
    (by rwa [← rot_add]) (by rwa [← rot_add])
  l23 p s hs h1 h2 h3 h4 h5 := hf.l23 (rot p) (rot s) (by rwa [N_rot]) h1 (by rwa [← rot_add])
    (by rwa [← rot_add, ← rot_add]) (by rwa [← rot_add, ← rot_add, ← rot_add])
    (by rwa [← rot_add, ← rot_add, ← rot_sub])

/-- The lattice seen from the point `q`, rotated by `k · 60°`. -/
def frame (f : ℤ × ℤ → Prop) (q : ℤ × ℤ) (k : ℕ) : ℤ × ℤ → Prop := fun x => f (q + rot^[k] x)

lemma Good.frame (hf : Good f) (q : ℤ × ℤ) (k : ℕ) : Good (Erdos188.frame f q k) := by
  induction k with
  | zero => exact hf.trans q
  | succ k ih => exact ih.rotate

lemma frame_iff {q : ℤ × ℤ} {k : ℕ} {v w : ℤ × ℤ} (h : q + rot^[k] v = w) :
    Erdos188.frame f q k v ↔ f w := by
  subst h; rfl

lemma Good.adj' (hf : Good f) {p q : ℤ × ℤ} (h : N (q - p) = 1) (hp : f p) (hq : f q) : False :=
  hf.adj p (q - p) h hp (by rwa [add_sub_cancel])

lemma Good.l5' (hf : Good f) {p0 p1 p2 p3 p4 : ℤ × ℤ}
    (h : N (p1 - p0) = 1 ∧ p2 = p1 + (p1 - p0) ∧ p3 = p2 + (p1 - p0) ∧ p4 = p3 + (p1 - p0))
    (h0 : ¬f p0) (h1 : ¬f p1) (h2 : ¬f p2) (h3 : ¬f p3) (h4 : ¬f p4) : False := by
  obtain ⟨hN, rfl, rfl, rfl⟩ := h
  exact hf.l5 p0 (p1 - p0) hN h0 (by rwa [add_sub_cancel]) (by rwa [add_sub_cancel])
    (by rwa [add_sub_cancel]) (by rwa [add_sub_cancel])

lemma Good.l21' (hf : Good f) {c x y z : ℤ × ℤ}
    (h : N (x - c) = 3 ∧ y = c + rot (rot (x - c)) ∧ z = c + rot (rot (rot (rot (x - c)))))
    (hc : f c) (hx : ¬f x) (hy : ¬f y) (hz : ¬f z) : False := by
  obtain ⟨hN, rfl, rfl⟩ := h
  exact hf.l21 c (x - c) hN hc (by rwa [add_sub_cancel]) hy hz

lemma Good.l22' (hf : Good f) {c x y z : ℤ × ℤ}
    (h : N (x - c) = 3 ∧ y = c + rot (rot (x - c)) ∧ z = c + rot (rot (rot (rot (x - c)))))
    (hc : f c) (hx : f x) (hy : f y) (hz : f z) : False := by
  obtain ⟨hN, rfl, rfl⟩ := h
  exact hf.l22 c (x - c) hN hc (by rwa [add_sub_cancel]) hy hz

lemma Good.l23' (hf : Good f) {p0 p1 p2 p3 p4 : ℤ × ℤ}
    (h : N (p1 - p0) = 3 ∧ p2 = p1 + (p1 - p0) ∧ p3 = p2 + (p1 - p0) ∧
      p4 = p2 - rot (p1 - p0))
    (h0 : f p0) (h1 : f p1) (h2 : f p2) (h3 : f p3) (h4 : f p4) : False := by
  obtain ⟨hN, rfl, rfl, rfl⟩ := h
  exact hf.l23 p0 (p1 - p0) hN h0 (by rwa [add_sub_cancel]) (by rwa [add_sub_cancel])
    (by rwa [add_sub_cancel]) (by rwa [add_sub_cancel])

/-- Lemma 2.4 of Tsaturian, first step (Figure 4): a red `T₃` extends to a red `T₄`. -/
lemma T3_to_T4 (hf : Good f) (hA : f (0, 0)) (hB : f (1, 1)) (hC : f (2, -1)) :
    f (3, 0) ∨ f (1, -2) ∨ f (-1, 2) := by
  by_contra hno
  simp only [not_or] at hno
  obtain ⟨hX, hY, hZ⟩ := hno
  have hE : ¬f (2, 1) := fun h => hf.adj' (by decide) hB h
  have hF : ¬f (1, 2) := fun h => hf.adj' (by decide) hB h
  have hG : ¬f (2, -2) := fun h => hf.adj' (by decide) hC h
  have hH : ¬f (3, -2) := fun h => hf.adj' (by decide) hC h
  have hI : ¬f (-1, 1) := fun h => hf.adj' (by decide) hA h
  have hJ : ¬f (-1, 0) := fun h => hf.adj' (by decide) hA h
  have hK : ¬f (-1, -1) := by
    intro hK
    have hL : ¬f (-1, -2) := fun h => hf.adj' (by decide) hK h
    have hM : ¬f (0, -2) := fun h => hf.adj' (by decide) hK h
    exact hf.l5' (by decide) hL hM hY hG hH
  have hN : f (-1, 3) := by
    by_contra hN
    exact hf.l5' (by decide) hK hJ hI hZ hN
  have hP : ¬f (-1, 4) := fun h => hf.adj' (by decide) hN h
  have hQ : ¬f (0, 3) := fun h => hf.adj' (by decide) hN h
  exact hf.l5' (by decide) hP hQ hF hE hX

/-- Lemma 2.4 of Tsaturian, second step (Figure 5): a red `T₄` extends to a red `T₅`. -/
lemma T4_to_T5 (hf : Good f) (_hA : f (0, 0)) (_hB : f (1, 1)) (hC : f (2, -1)) (hD : f (3, 0)) :
    f (2, 2) ∨ f (1, -2) ∨ f (4, -2) := by
  by_contra hno
  simp only [not_or] at hno
  obtain ⟨hX, hF, hG⟩ := hno
  have hH : ¬f (2, -2) := fun h => hf.adj' (by decide) hC h
  have hI : ¬f (3, -2) := fun h => hf.adj' (by decide) hC h
  have hM : ¬f (4, 0) := fun h => hf.adj' (by decide) hD h
  have hN : ¬f (3, 1) := fun h => hf.adj' (by decide) hD h
  have hP : f (5, -2) := by
    by_contra hP
    exact hf.l5' (by decide) hF hH hI hG hP
  have hQ : ¬f (5, -1) := fun h => hf.adj' (by decide) hP h
  have hR : ¬f (6, -2) := fun h => hf.adj' (by decide) hP h
  exact hf.l5' (by decide) hX hN hM hQ hR

/-- Lemma 2.4 of Tsaturian, third step (Figure 6): a red `T₅` extends to a red `T₆`. -/
lemma T5_to_T6 (hf : Good f) (hA : f (0, 0)) (hB : f (1, 1)) (hC : f (2, -1)) (hD : f (3, 0))
    (hE : f (2, 2)) : f (4, -2) := by
  by_contra hF
  have hX : ¬f (-1, 2) := fun h => hf.l22' (by decide) hB h hC hE
  have hY : ¬f (0, 3) := fun h => hf.l22' (by decide) hB h hA hD
  have hG : ¬f (-1, 0) := fun h => hf.adj' (by decide) hA h
  have hH : ¬f (-1, 1) := fun h => hf.adj' (by decide) hA h
  have hI : ¬f (1, 3) := fun h => hf.adj' (by decide) hE h
  have hJ : ¬f (2, 3) := fun h => hf.adj' (by decide) hE h
  have hK : ¬f (2, -2) := fun h => hf.adj' (by decide) hC h
  have hL : ¬f (3, -2) := fun h => hf.adj' (by decide) hC h
  have hM : ¬f (4, -1) := fun h => hf.adj' (by decide) hD h
  have hN : ¬f (4, 0) := fun h => hf.adj' (by decide) hD h
  have hP : f (1, -2) := by
    by_contra hP
    have hQ : f (0, -2) := by
      by_contra hQ
      exact hf.l5' (by decide) hQ hP hK hL hF
    have hU : ¬f (-1, -1) := fun h => hf.adj' (by decide) hQ h
    have hT : ¬f (-1, -2) := fun h => hf.adj' (by decide) hQ h
    exact hf.l5' (by decide) hT hU hG hH hX
  have hR : f (4, 1) := by
    by_contra hR
    have hS : f (4, 2) := by
      by_contra hS
      exact hf.l5' (by decide) hS hR hN hM hF
    have hV : ¬f (4, 3) := fun h => hf.adj' (by decide) hS h
    have hW : ¬f (3, 3) := fun h => hf.adj' (by decide) hS h
    exact hf.l5' (by decide) hV hW hJ hI hY
  exact hf.l23' (by decide) hR hD hC hP hB

lemma T4_to_T6 (hf : Good f) (hA : f (0, 0)) (hB : f (1, 1)) (hC : f (2, -1)) (hD : f (3, 0)) :
    (f (2, 2) ∧ f (4, -2)) ∨ (f (1, -2) ∧ f (-1, 2)) := by
  rcases T4_to_T5 hf hA hB hC hD with h | h | h
  · exact Or.inl ⟨h, T5_to_T6 hf hA hB hC hD h⟩
  · refine Or.inr ⟨h, (frame_iff (by decide)).1 (T5_to_T6 (hf.frame (3, 0) 3)
      ((frame_iff (by decide)).2 hD) ((frame_iff (by decide)).2 hC)
      ((frame_iff (by decide)).2 hB) ((frame_iff (by decide)).2 hA)
      ((frame_iff (by decide)).2 h))⟩
  · refine Or.inl ⟨(frame_iff (by decide)).1 (T5_to_T6 (hf.frame (4, -2) 2)
      ((frame_iff (by decide)).2 h) ((frame_iff (by decide)).2 hC)
      ((frame_iff (by decide)).2 hD) ((frame_iff (by decide)).2 hB)
      ((frame_iff (by decide)).2 hA)), h⟩

/-- Lemma 2.4 of Tsaturian: a red `T₃` lies in a red `T₆`; the four possible `T₆`. -/
lemma T3_to_T6 (hf : Good f) (hA : f (0, 0)) (hB : f (1, 1)) (hC : f (2, -1)) :
    (f (2, 2) ∧ f (4, -2) ∧ f (3, 0)) ∨ (f (-1, -1) ∧ f (3, -3) ∧ f (1, -2)) ∨
      (f (-2, 1) ∧ f (0, 3) ∧ f (-1, 2)) ∨ (f (3, 0) ∧ f (1, -2) ∧ f (-1, 2)) := by
  rcases T3_to_T4 hf hA hB hC with hX | hY | hZ
  · rcases T4_to_T6 hf hA hB hC hX with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨h1, h2, hX⟩
    · exact Or.inr (Or.inr (Or.inr ⟨hX, h1, h2⟩))
  · rcases T4_to_T6 (hf.frame (1, 1) 4) ((frame_iff (by decide)).2 hB)
      ((frame_iff (by decide)).2 hC) ((frame_iff (by decide)).2 hA)
      ((frame_iff (by decide)).2 hY) with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inr (Or.inl ⟨(frame_iff (by decide)).1 h2, (frame_iff (by decide)).1 h1, hY⟩)
    · exact Or.inr (Or.inr (Or.inr ⟨(frame_iff (by decide)).1 h2, hY,
        (frame_iff (by decide)).1 h1⟩))
  · rcases T4_to_T6 (hf.frame (2, -1) 2) ((frame_iff (by decide)).2 hC)
      ((frame_iff (by decide)).2 hA) ((frame_iff (by decide)).2 hB)
      ((frame_iff (by decide)).2 hZ) with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inr (Or.inr (Or.inl ⟨(frame_iff (by decide)).1 h1, (frame_iff (by decide)).1 h2,
        hZ⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨(frame_iff (by decide)).1 h1, (frame_iff (by decide)).1 h2,
        hZ⟩))

/-- The six points of a `T₆` (a triangle of side `2√3` with its edge midpoints). -/
def T6 (g : ℤ × ℤ → Prop) : Prop :=
  g (0, 0) ∧ g (1, 1) ∧ g (2, 2) ∧ g (2, -1) ∧ g (4, -2) ∧ g (3, 0)

/-- Lemma 2.5 of Tsaturian, main step (Figure 8): a red `T₆` forces its translate by `5`. -/
lemma T6_step (hf : Good f) (h : T6 f) : T6 (frame f (5, 0) 0) := by
  obtain ⟨hA, hB, hC, hF, hE, hD⟩ := h
  have hI : ¬f (3, -3) := fun h => hf.l22' (by decide) hF hA h hD
  have hJ : ¬f (5, -1) := fun h => hf.l22' (by decide) hD hC hF h
  have hK : ¬f (1, -1) := fun h => hf.adj' (by decide) hA h
  have hL : ¬f (2, -2) := fun h => hf.adj' (by decide) hF h
  have hM : ¬f (5, -3) := fun h => hf.adj' (by decide) hE h
  have hN : ¬f (5, -2) := fun h => hf.adj' (by decide) hE h
  have hR : ¬f (5, -4) := by
    intro hR
    have hP : ¬f (5, -5) := fun h => hf.adj' (by decide) hR h
    have hQ : ¬f (4, -4) := fun h => hf.adj' (by decide) hR h
    exact hf.l5' (by decide) hK hL hI hQ hP
  have hA' : f (5, 0) := by
    by_contra hA'
    exact hf.l5' (by decide) hA' hJ hN hM hR
  have hS1 : ¬f (2, 1) := fun h => hf.adj' (by decide) hD h
  have hS2 : ¬f (3, 1) := fun h => hf.adj' (by decide) hD h
  have hS3 : ¬f (4, 1) := fun h => hf.adj' (by decide) hA' h
  have hS4 : ¬f (5, 1) := fun h => hf.adj' (by decide) hA' h
  have hB' : f (6, 1) := by
    by_contra hB'
    exact hf.l5' (by decide) hS1 hS2 hS3 hS4 hB'
  have hT1 : ¬f (3, -1) := fun h => hf.adj' (by decide) hD h
  have hT2 : ¬f (4, -1) := fun h => hf.adj' (by decide) hD h
  have hT4 : ¬f (6, -1) := fun h => hf.adj' (by decide) hA' h
  have hF' : f (7, -1) := by
    by_contra hF'
    exact hf.l5' (by decide) hT1 hT2 hJ hT4 hF'
  have hV : ¬f (1, 3) := fun h => hf.adj' (by decide) hC h
  have hW : ¬f (2, 3) := fun h => hf.adj' (by decide) hC h
  have hU : ¬f (0, 3) := fun h => hf.l22' (by decide) hB hA hD h
  have hX : ¬f (4, 2) := by
    intro hX
    have hX1 : ¬f (3, 3) := fun h => hf.adj' (by decide) hX h
    have hX2 : ¬f (4, 3) := fun h => hf.adj' (by decide) hX h
    exact hf.l5' (by decide) hU hV hW hX1 hX2
  have hV' : ¬f (4, -3) := fun h => hf.adj' (by decide) hE h
  have hY : ¬f (6, -2) := by
    intro hY
    have hY1 : ¬f (6, -3) := fun h => hf.adj' (by decide) hY h
    have hY2 : ¬f (7, -3) := fun h => hf.adj' (by decide) hY h
    exact hf.l5' (by decide) hI hV' hM hY1 hY2
  have hA'' : frame f (5, 0) 0 (0, 0) := (frame_iff (by decide)).2 hA'
  have hB'' : frame f (5, 0) 0 (1, 1) := (frame_iff (by decide)).2 hB'
  have hF'' : frame f (5, 0) 0 (2, -1) := (frame_iff (by decide)).2 hF'
  rcases T3_to_T6 (hf.frame (5, 0) 0) hA'' hB'' hF'' with ⟨h1, h2, h3⟩ | ⟨_, _, h⟩ | ⟨_, _, h⟩ |
      ⟨_, h, _⟩
  · exact ⟨hA'', hB'', h1, hF'', h2, h3⟩
  · exact absurd ((frame_iff (by decide)).1 h) hY
  · exact absurd ((frame_iff (by decide)).1 h) hX
  · exact absurd ((frame_iff (by decide)).1 h) hY

lemma frame_eq₂ {q q₂ q₃ : ℤ × ℤ} {k k₂ k₃ : ℕ} {v v' : ℤ × ℤ}
    (h : q + rot^[k] v = q₂ + rot^[k₂] (q₃ + rot^[k₃] v')) :
    Erdos188.frame f q k v ↔ Erdos188.frame (Erdos188.frame f q₂ k₂) q₃ k₃ v' := by
  show f _ ↔ f _
  rw [h]

lemma rotk_add (k : ℕ) (a b : ℤ × ℤ) : rot^[k] (a + b) = rot^[k] a + rot^[k] b := by
  induction k generalizing a b with
  | zero => rfl
  | succ k ih => simp only [Function.iterate_succ_apply, rot_add, ih]

lemma rotk_rot (k : ℕ) (v : ℤ × ℤ) : rot^[k] (rot v) = rot (rot^[k] v) := by
  rw [← Function.iterate_succ_apply, Function.iterate_succ_apply']

lemma rotk_zero (k : ℕ) : rot^[k] (0, 0) = (0, 0) := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply]; exact ih

lemma frame_frame (q q' : ℤ × ℤ) (k k' : ℕ) :
    Erdos188.frame (Erdos188.frame f q k) q' k' = Erdos188.frame f (q + rot^[k] q') (k + k') := by
  funext v
  simp only [frame, rotk_add, Function.iterate_add_apply, add_assoc]

/-- Lemma 2.5 of Tsaturian: translate of a red `T₆` in the direction `EB`. -/
lemma T6_step₂ (hf : Good f) (h : T6 f) : T6 (frame f (-5, 5) 0) := by
  obtain ⟨hA, hB, hC, hF, hE, hD⟩ := h
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := T6_step (hf.frame (4, -2) 2)
    ⟨(frame_iff (by decide)).2 hE, (frame_iff (by decide)).2 hF, (frame_iff (by decide)).2 hA,
      (frame_iff (by decide)).2 hD, (frame_iff (by decide)).2 hC, (frame_iff (by decide)).2 hB⟩
  exact ⟨(frame_eq₂ (by decide)).2 (h3),
    (frame_eq₂ (by decide)).2 (h6),
    (frame_eq₂ (by decide)).2 (h5),
    (frame_eq₂ (by decide)).2 (h2),
    (frame_eq₂ (by decide)).2 (h1),
    (frame_eq₂ (by decide)).2 (h4)⟩

/-- Lemma 2.5 of Tsaturian: translate of a red `T₆` in the direction `CF`. -/
lemma T6_step₃ (hf : Good f) (h : T6 f) : T6 (frame f (0, -5) 0) := by
  obtain ⟨hA, hB, hC, hF, hE, hD⟩ := h
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := T6_step (hf.frame (2, 2) 4)
    ⟨(frame_iff (by decide)).2 hC, (frame_iff (by decide)).2 hD, (frame_iff (by decide)).2 hE,
      (frame_iff (by decide)).2 hB, (frame_iff (by decide)).2 hA, (frame_iff (by decide)).2 hF⟩
  exact ⟨(frame_eq₂ (by decide)).2 (h5),
    (frame_eq₂ (by decide)).2 (h4),
    (frame_eq₂ (by decide)).2 (h1),
    (frame_eq₂ (by decide)).2 (h6),
    (frame_eq₂ (by decide)).2 (h3),
    (frame_eq₂ (by decide)).2 (h2)⟩

lemma frame_frame₀ (q q' : ℤ × ℤ) :
    Erdos188.frame (Erdos188.frame f q 0) q' 0 = Erdos188.frame f (q + q') 0 := by
  funext v
  simp only [frame, Function.iterate_zero_apply, add_assoc]

lemma T6_trans (hf : Good f) {q : ℤ × ℤ} (h : T6 (frame f q 0)) :
    T6 (frame f (q + (5, 0)) 0) ∧ T6 (frame f (q - (5, 0)) 0) ∧
      T6 (frame f (q + (0, 5)) 0) ∧ T6 (frame f (q - (0, 5)) 0) := by
  have t1 : ∀ q, T6 (frame f q 0) → T6 (frame f (q + (5, 0)) 0) := fun q h => by
    have := T6_step (hf.frame q 0) h; rwa [frame_frame₀] at this
  have t2 : ∀ q, T6 (frame f q 0) → T6 (frame f (q + (-5, 5)) 0) := fun q h => by
    have := T6_step₂ (hf.frame q 0) h; rwa [frame_frame₀] at this
  have t3 : ∀ q, T6 (frame f q 0) → T6 (frame f (q + (0, -5)) 0) := fun q h => by
    have := T6_step₃ (hf.frame q 0) h; rwa [frame_frame₀] at this
  refine ⟨t1 q h, ?_, ?_, ?_⟩
  · have := t3 _ (t2 q h)
    rwa [show q + (-5, 5) + (0, -5) = q - (5, 0) by ext <;> simp <;> ring] at this
  · have := t2 _ (t1 q h)
    rwa [show q + (5, 0) + (-5, 5) = q + (0, 5) by ext <;> simp <;> ring] at this
  · have := t3 q h
    rwa [show q + (0, -5) = q - (0, 5) by ext <;> simp <;> ring] at this

/-- Lemma 2.5 of Tsaturian: all translates of a red `T₆` by `5ℤ²` are red. -/
lemma T6_periodic (hf : Good f) (h : T6 f) : ∀ m n : ℤ, T6 (frame f (5 * m, 5 * n) 0) := by
  have base : T6 (frame f (5 * 0, 5 * 0) 0) := by
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
    exact ⟨(frame_iff (by decide)).2 h1, (frame_iff (by decide)).2 h2,
      (frame_iff (by decide)).2 h3, (frame_iff (by decide)).2 h4,
      (frame_iff (by decide)).2 h5, (frame_iff (by decide)).2 h6⟩
  have row : ∀ m : ℤ, T6 (frame f (5 * m, 5 * 0) 0) := by
    intro m
    induction m using Int.induction_on with
    | zero => exact base
    | succ i ih =>
      have := (T6_trans hf ih).1
      rwa [show ((5 * (i : ℤ), 5 * 0) : ℤ × ℤ) + (5, 0) = (5 * ((i : ℤ) + 1), 5 * 0) by
        ext <;> simp <;> ring] at this
    | pred i ih =>
      have := (T6_trans hf ih).2.1
      rwa [show ((5 * -(i : ℤ), 5 * 0) : ℤ × ℤ) - (5, 0) = (5 * (-(i : ℤ) - 1), 5 * 0) by
        ext <;> simp <;> ring] at this
  intro m n
  induction n using Int.induction_on with
  | zero => exact row m
  | succ i ih =>
    have := (T6_trans hf ih).2.2.1
    rwa [show ((5 * m, 5 * (i : ℤ)) : ℤ × ℤ) + (0, 5) = (5 * m, 5 * ((i : ℤ) + 1)) by
      ext <;> simp <;> ring] at this
  | pred i ih =>
    have := (T6_trans hf ih).2.2.2
    rwa [show ((5 * m, 5 * -(i : ℤ)) : ℤ × ℤ) - (0, 5) = (5 * m, 5 * (-(i : ℤ) - 1)) by
      ext <;> simp <;> ring] at this

/-- End of the proof of Lemma 2.5 (Figure 7): if all translates of a red `T₆` by `5ℤ²` are red,
then every red point lies in one of them (every other point is adjacent to one), so the colouring
of the lattice is invariant under translation by `5ℤ²`. -/
lemma T6_cover (hf : Good f) (hper : ∀ m n : ℤ, T6 (frame f (5 * m, 5 * n) 0)) (x y a b : ℤ)
    (hq : f (x, y)) : f ((x, y) + (5 * a, 5 * b)) := by
  have hx : x % 5 = 0 ∨ x % 5 = 1 ∨ x % 5 = 2 ∨ x % 5 = 3 ∨ x % 5 = 4 := by omega
  have hy : y % 5 = 0 ∨ y % 5 = 1 ∨ y % 5 = 2 ∨ y % 5 = 3 ∨ y % 5 = 4 := by omega
  rcases hx with hx | hx | hx | hx | hx <;> rcases hy with hy | hy | hy | hy | hy
  · have h : f ((5 * (x / 5 + a), 5 * (y / 5 + b)) + (0, 0)) :=
      (hper (x / 5 + a) (y / 5 + b)).1
    have e : (x, y) + (5 * a, 5 * b) = (5 * (x / 5 + a), 5 * (y / 5 + b)) + (0, 0) := by
      ext <;> simp <;> omega
    rw [e]; exact h
  · exfalso
    have h : f ((5 * (x / 5), 5 * ((y - 1) / 5)) + (1, 1)) := (hper (x / 5) ((y - 1) / 5)).2.1
    have e : (5 * (x / 5), 5 * ((y - 1) / 5)) + (1, 1) = (x, y) + (1, 0) := by
      ext <;> simp <;> omega
    exact hf.adj (x, y) (1, 0) (by decide) hq (e ▸ h)
  · exfalso
    have h : f ((5 * ((x - 5) / 5), 5 * ((y + 3) / 5)) + (4, -2)) :=
      (hper ((x - 5) / 5) ((y + 3) / 5)).2.2.2.2.1
    have e : (5 * ((x - 5) / 5), 5 * ((y + 3) / 5)) + (4, -2) = (x, y) + (-1, 1) := by
      ext <;> simp <;> omega
    exact hf.adj (x, y) (-1, 1) (by decide) hq (e ▸ h)
  · exfalso
    have h : f ((5 * ((x - 5) / 5), 5 * ((y + 2) / 5)) + (4, -2)) :=
      (hper ((x - 5) / 5) ((y + 2) / 5)).2.2.2.2.1
    have e : (5 * ((x - 5) / 5), 5 * ((y + 2) / 5)) + (4, -2) = (x, y) + (-1, 0) := by
      ext <;> simp <;> omega
    exact hf.adj (x, y) (-1, 0) (by decide) hq (e ▸ h)
  · exfalso
    have h : f ((5 * (x / 5), 5 * ((y + 1) / 5)) + (0, 0)) := (hper (x / 5) ((y + 1) / 5)).1
    have e : (5 * (x / 5), 5 * ((y + 1) / 5)) + (0, 0) = (x, y) + (0, 1) := by
      ext <;> simp <;> omega
    exact hf.adj (x, y) (0, 1) (by decide) hq (e ▸ h)
  · exfalso
    have h : f ((5 * ((x - 1) / 5), 5 * (y / 5)) + (1, 1)) := (hper ((x - 1) / 5) (y / 5)).2.1
    have e : (5 * ((x - 1) / 5), 5 * (y / 5)) + (1, 1) = (x, y) + (0, 1) := by
      ext <;> simp <;> omega
    exact hf.adj (x, y) (0, 1) (by decide) hq (e ▸ h)
  · have h : f ((5 * ((x - 1) / 5 + a), 5 * ((y - 1) / 5 + b)) + (1, 1)) :=
      (hper ((x - 1) / 5 + a) ((y - 1) / 5 + b)).2.1
    have e : (x, y) + (5 * a, 5 * b) = (5 * ((x - 1) / 5 + a), 5 * ((y - 1) / 5 + b)) + (1, 1) := by
      ext <;> simp <;> omega
    rw [e]; exact h
  · exfalso
    have h : f ((5 * ((x - 1) / 5), 5 * ((y - 2) / 5)) + (2, 2)) :=
      (hper ((x - 1) / 5) ((y - 2) / 5)).2.2.1
    have e : (5 * ((x - 1) / 5), 5 * ((y - 2) / 5)) + (2, 2) = (x, y) + (1, 0) := by
      ext <;> simp <;> omega
    exact hf.adj (x, y) (1, 0) (by decide) hq (e ▸ h)
  · exfalso
    have h : f ((5 * ((x - 1) / 5), 5 * ((y - 3) / 5)) + (2, 2)) :=
      (hper ((x - 1) / 5) ((y - 3) / 5)).2.2.1
    have e : (5 * ((x - 1) / 5), 5 * ((y - 3) / 5)) + (2, 2) = (x, y) + (1, -1) := by
      ext <;> simp <;> omega
    exact hf.adj (x, y) (1, -1) (by decide) hq (e ▸ h)
  · exfalso
    have h : f ((5 * ((x - 1) / 5), 5 * ((y + 1) / 5)) + (2, -1)) :=
      (hper ((x - 1) / 5) ((y + 1) / 5)).2.2.2.1
    have e : (5 * ((x - 1) / 5), 5 * ((y + 1) / 5)) + (2, -1) = (x, y) + (1, 0) := by
      ext <;> simp <;> omega
    exact hf.adj (x, y) (1, 0) (by decide) hq (e ▸ h)
  · exfalso
    have h : f ((5 * ((x - 2) / 5), 5 * (y / 5)) + (3, 0)) := (hper ((x - 2) / 5) (y / 5)).2.2.2.2.2
    have e : (5 * ((x - 2) / 5), 5 * (y / 5)) + (3, 0) = (x, y) + (1, 0) := by
      ext <;> simp <;> omega
    exact hf.adj (x, y) (1, 0) (by decide) hq (e ▸ h)
  · exfalso
    have h : f ((5 * ((x - 2) / 5), 5 * ((y - 1) / 5)) + (2, 2)) :=
      (hper ((x - 2) / 5) ((y - 1) / 5)).2.2.1
    have e : (5 * ((x - 2) / 5), 5 * ((y - 1) / 5)) + (2, 2) = (x, y) + (0, 1) := by
      ext <;> simp <;> omega
    exact hf.adj (x, y) (0, 1) (by decide) hq (e ▸ h)
  · have h : f ((5 * ((x - 2) / 5 + a), 5 * ((y - 2) / 5 + b)) + (2, 2)) :=
      (hper ((x - 2) / 5 + a) ((y - 2) / 5 + b)).2.2.1
    have e : (x, y) + (5 * a, 5 * b) = (5 * ((x - 2) / 5 + a), 5 * ((y - 2) / 5 + b)) + (2, 2) := by
      ext <;> simp <;> omega
    rw [e]; exact h
  · exfalso
    have h : f ((5 * ((x - 2) / 5), 5 * ((y + 2) / 5)) + (2, -1)) :=
      (hper ((x - 2) / 5) ((y + 2) / 5)).2.2.2.1
    have e : (5 * ((x - 2) / 5), 5 * ((y + 2) / 5)) + (2, -1) = (x, y) + (0, 1) := by
      ext <;> simp <;> omega
    exact hf.adj (x, y) (0, 1) (by decide) hq (e ▸ h)
  · have h : f ((5 * ((x - 2) / 5 + a), 5 * ((y + 1) / 5 + b)) + (2, -1)) :=
      (hper ((x - 2) / 5 + a) ((y + 1) / 5 + b)).2.2.2.1
    have e : (x, y) + (5 * a, 5 * b)
        = (5 * ((x - 2) / 5 + a), 5 * ((y + 1) / 5 + b)) + (2, -1) := by
      ext <;> simp <;> omega
    rw [e]; exact h
  · have h : f ((5 * ((x - 3) / 5 + a), 5 * (y / 5 + b)) + (3, 0)) :=
      (hper ((x - 3) / 5 + a) (y / 5 + b)).2.2.2.2.2
    have e : (x, y) + (5 * a, 5 * b) = (5 * ((x - 3) / 5 + a), 5 * (y / 5 + b)) + (3, 0) := by
      ext <;> simp <;> omega
    rw [e]; exact h
  · exfalso
    have h : f ((5 * ((x - 3) / 5), 5 * ((y - 1) / 5)) + (2, 2)) :=
      (hper ((x - 3) / 5) ((y - 1) / 5)).2.2.1
    have e : (5 * ((x - 3) / 5), 5 * ((y - 1) / 5)) + (2, 2) = (x, y) + (-1, 1) := by
      ext <;> simp <;> omega
    exact hf.adj (x, y) (-1, 1) (by decide) hq (e ▸ h)
  · exfalso
    have h : f ((5 * ((x - 3) / 5), 5 * ((y - 2) / 5)) + (2, 2)) :=
      (hper ((x - 3) / 5) ((y - 2) / 5)).2.2.1
    have e : (5 * ((x - 3) / 5), 5 * ((y - 2) / 5)) + (2, 2) = (x, y) + (-1, 0) := by
      ext <;> simp <;> omega
    exact hf.adj (x, y) (-1, 0) (by decide) hq (e ▸ h)
  · exfalso
    have h : f ((5 * ((x - 3) / 5), 5 * ((y + 2) / 5)) + (4, -2)) :=
      (hper ((x - 3) / 5) ((y + 2) / 5)).2.2.2.2.1
    have e : (5 * ((x - 3) / 5), 5 * ((y + 2) / 5)) + (4, -2) = (x, y) + (1, 0) := by
      ext <;> simp <;> omega
    exact hf.adj (x, y) (1, 0) (by decide) hq (e ▸ h)
  · exfalso
    have h : f ((5 * ((x - 3) / 5), 5 * ((y + 1) / 5)) + (3, 0)) :=
      (hper ((x - 3) / 5) ((y + 1) / 5)).2.2.2.2.2
    have e : (5 * ((x - 3) / 5), 5 * ((y + 1) / 5)) + (3, 0) = (x, y) + (0, 1) := by
      ext <;> simp <;> omega
    exact hf.adj (x, y) (0, 1) (by decide) hq (e ▸ h)
  · exfalso
    have h : f ((5 * ((x + 1) / 5), 5 * (y / 5)) + (0, 0)) := (hper ((x + 1) / 5) (y / 5)).1
    have e : (5 * ((x + 1) / 5), 5 * (y / 5)) + (0, 0) = (x, y) + (1, 0) := by
      ext <;> simp <;> omega
    exact hf.adj (x, y) (1, 0) (by decide) hq (e ▸ h)
  · exfalso
    have h : f ((5 * ((x + 1) / 5), 5 * ((y - 1) / 5)) + (0, 0)) :=
      (hper ((x + 1) / 5) ((y - 1) / 5)).1
    have e : (5 * ((x + 1) / 5), 5 * ((y - 1) / 5)) + (0, 0) = (x, y) + (1, -1) := by
      ext <;> simp <;> omega
    exact hf.adj (x, y) (1, -1) (by decide) hq (e ▸ h)
  · exfalso
    have h : f ((5 * ((x - 4) / 5), 5 * ((y + 3) / 5)) + (4, -2)) :=
      (hper ((x - 4) / 5) ((y + 3) / 5)).2.2.2.2.1
    have e : (5 * ((x - 4) / 5), 5 * ((y + 3) / 5)) + (4, -2) = (x, y) + (0, 1) := by
      ext <;> simp <;> omega
    exact hf.adj (x, y) (0, 1) (by decide) hq (e ▸ h)
  · have h : f ((5 * ((x - 4) / 5 + a), 5 * ((y + 2) / 5 + b)) + (4, -2)) :=
      (hper ((x - 4) / 5 + a) ((y + 2) / 5 + b)).2.2.2.2.1
    have e : (x, y) + (5 * a, 5 * b)
        = (5 * ((x - 4) / 5 + a), 5 * ((y + 2) / 5 + b)) + (4, -2) := by
      ext <;> simp <;> omega
    rw [e]; exact h
  · exfalso
    have h : f ((5 * ((x - 4) / 5), 5 * ((y + 1) / 5)) + (3, 0)) :=
      (hper ((x - 4) / 5) ((y + 1) / 5)).2.2.2.2.2
    have e : (5 * ((x - 4) / 5), 5 * ((y + 1) / 5)) + (3, 0) = (x, y) + (-1, 1) := by
      ext <;> simp <;> omega
    exact hf.adj (x, y) (-1, 1) (by decide) hq (e ▸ h)

lemma rotk_surj (k : ℕ) (w : ℤ × ℤ) : ∃ y, rot^[k] y = w := by
  induction k generalizing w with
  | zero => exact ⟨w, rfl⟩
  | succ k ih =>
    obtain ⟨y, hy⟩ := ih w
    refine ⟨(y.1 + y.2, -y.1), ?_⟩
    rw [Function.iterate_succ_apply, ← hy]
    congr 1
    ext <;> simp [rot]

lemma rotk_surj₅ (k : ℕ) (c d : ℤ) : ∃ a b : ℤ, rot^[k] (5 * a, 5 * b) = (5 * c, 5 * d) := by
  induction k generalizing c d with
  | zero => exact ⟨c, d, rfl⟩
  | succ k ih =>
    obtain ⟨a, b, hab⟩ := ih c d
    refine ⟨a + b, -a, ?_⟩
    rw [Function.iterate_succ_apply, ← hab]
    congr 1
    ext <;> simp [rot] <;> ring

/-- A red `T₆` anywhere in the lattice forces the colouring of Figure 7, in which a point and its
translate by `5` (in the direction of the first coordinate) have the same colour. -/
lemma T6_shift (hf : Good f) {P : ℤ × ℤ} {K : ℕ} (h : T6 (frame f P K)) (x : ℤ × ℤ)
    (hx : f x) : f (x + (5, 0)) := by
  have hg := hf.frame P K
  have hper := T6_periodic hg h
  obtain ⟨⟨y1, y2⟩, hy⟩ := rotk_surj K (x - P)
  obtain ⟨a, b, hab⟩ := rotk_surj₅ K 1 0
  have h1 : frame f P K (y1, y2) := by
    show f (P + rot^[K] (y1, y2))
    rwa [hy, add_sub_cancel]
  have h2 := T6_cover hg hper y1 y2 a b h1
  change f (P + rot^[K] ((y1, y2) + (5 * a, 5 * b))) at h2
  rwa [rotk_add, hy, hab, ← add_assoc, add_sub_cancel] at h2

/-- No three red lattice points form a `T₃` (an equilateral triangle of side `√3`). -/
def NoT3 (f : ℤ × ℤ → Prop) : Prop := ∀ p b, N b = 3 → f p → f (p + rot b) → f (p + b) → False

lemma NoT3.frame (hT : NoT3 f) (q : ℤ × ℤ) (k : ℕ) : NoT3 (Erdos188.frame f q k) := by
  induction k with
  | zero =>
    intro p b hb h1 h2 h3
    exact hT (q + p) b hb h1 (by simpa [Erdos188.frame, add_assoc] using h2)
      (by simpa [Erdos188.frame, add_assoc] using h3)
  | succ k ih =>
    intro p b hb h1 h2 h3
    refine ih (rot p) (rot b) (by rwa [N_rot]) h1 ?_ ?_
    · change Erdos188.frame f q k (rot (p + rot b)) at h2
      rwa [rot_add] at h2
    · change Erdos188.frame f q k (rot (p + b)) at h3
      rwa [rot_add] at h3

lemma NoT3.expl (hT : NoT3 f) {p x y : ℤ × ℤ} (h : N (y - p) = 3 ∧ x = p + rot (y - p))
    (hp : f p) (hx : f x) (hy : f y) : False := by
  obtain ⟨hN, rfl⟩ := h
  exact hT p (y - p) hN hp hx (by rwa [add_sub_cancel])

/-- Lemma 2.6 of Tsaturian, main step (Figure 10): in a lattice without red `T₃`, two red points
at distance `√3` force further red points. -/
lemma T3free_step (hf : Good f) (hT : NoT3 f) (hA : f (0, 0)) (hB : f (-1, 2)) :
    f (-2, 4) ∧ f (3, -1) ∧ f (2, 1) := by
  have hD : ¬f (-2, 1) := fun h => hT.expl (by decide) hA h hB
  have hG : ¬f (1, 1) := fun h => hT.expl (by decide) hA hB h
  have hE : ¬f (-1, 1) := fun h => hf.adj' (by decide) hA h
  have hF : ¬f (0, 1) := fun h => hf.adj' (by decide) hA h
  have hH : ¬f (-1, 3) := fun h => hf.adj' (by decide) hB h
  have hI : ¬f (0, 2) := fun h => hf.adj' (by decide) hB h
  have hB' : f (2, 1) := by
    by_contra hB'
    exact hf.l5' (by decide) hD hE hF hG hB'
  have hN : ¬f (2, 0) := fun h => hf.adj' (by decide) hB' h
  have hA' : f (3, -1) := by
    by_contra hA'
    exact hf.l5' (by decide) hH hI hG hN hA'
  have hC : f (-2, 4) := by
    by_contra hC
    exact hf.l5' (by decide) hC hH hI hG hN
  exact ⟨hC, hA', hB'⟩

lemma N3_cases {b : ℤ × ℤ} (hb : N b = 3) : ∃ k : ℕ, rot^[k] (2, -1) = b := by
  obtain ⟨b1, b2⟩ := b
  simp only [N] at hb
  have h1 : -2 ≤ b1 := by nlinarith [sq_nonneg (b1 + 2 * b2)]
  have h2 : b1 ≤ 2 := by nlinarith [sq_nonneg (b1 + 2 * b2)]
  have h3 : -2 ≤ b2 := by nlinarith [sq_nonneg (2 * b1 + b2)]
  have h4 : b2 ≤ 2 := by nlinarith [sq_nonneg (2 * b1 + b2)]
  interval_cases b1 <;> interval_cases b2 <;> norm_num at hb <;>
    first
    | exact ⟨0, by decide⟩ | exact ⟨1, by decide⟩ | exact ⟨2, by decide⟩
    | exact ⟨3, by decide⟩ | exact ⟨4, by decide⟩ | exact ⟨5, by decide⟩

/-- The lattice form of the main step of Tsaturian's theorem: in a unit triangular lattice, if
the origin is red then so is the point at distance `5` along a lattice direction. -/
theorem lattice_main (hf : Good f) (hA : f (0, 0)) : f (5, 0) := by
  by_cases hT : NoT3 f
  · -- Lemma 2.6: the colouring of Figure 9.
    have hB : f (1, -2) ∨ f (1, 1) ∨ f (-2, 1) := by
      by_contra h
      simp only [not_or] at h
      obtain ⟨h1, h2, h3⟩ := h
      exact hf.l21' (by decide) hA h1 h2 h3
    rcases hB with hB | hB | hB
    · obtain ⟨-, a2, a3⟩ := T3free_step (hf.frame (1, -2) 0) (hT.frame (1, -2) 0)
        ((frame_iff (by decide)).2 hB) ((frame_iff (by decide)).2 hA)
      have p1 : f (4, -3) := (frame_iff (by decide)).1 a2
      have p2 : f (3, -1) := (frame_iff (by decide)).1 a3
      obtain ⟨b1, -, -⟩ := T3free_step (hf.frame (4, -3) 0) (hT.frame (4, -3) 0)
        ((frame_iff (by decide)).2 p1) ((frame_iff (by decide)).2 p2)
      have p3 : f (2, 1) := (frame_iff (by decide)).1 b1
      obtain ⟨-, -, c3⟩ := T3free_step (hf.frame (3, -1) 0) (hT.frame (3, -1) 0)
        ((frame_iff (by decide)).2 p2) ((frame_iff (by decide)).2 p3)
      exact (frame_iff (by decide)).1 c3
    · obtain ⟨-, a2, a3⟩ := T3free_step (hf.frame (0, 0) 5) (hT.frame (0, 0) 5)
        ((frame_iff (by decide)).2 hA) ((frame_iff (by decide)).2 hB)
      have p1 : f (2, -3) := (frame_iff (by decide)).1 a2
      have p2 : f (3, -2) := (frame_iff (by decide)).1 a3
      obtain ⟨b1, -, -⟩ := T3free_step (hf.frame (2, -3) 5) (hT.frame (2, -3) 5)
        ((frame_iff (by decide)).2 p1) ((frame_iff (by decide)).2 p2)
      have p3 : f (4, -1) := (frame_iff (by decide)).1 b1
      obtain ⟨c1, -, -⟩ := T3free_step (hf.frame (3, -2) 5) (hT.frame (3, -2) 5)
        ((frame_iff (by decide)).2 p2) ((frame_iff (by decide)).2 p3)
      exact (frame_iff (by decide)).1 c1
    · obtain ⟨a1, -, -⟩ := T3free_step (hf.frame (-2, 1) 4) (hT.frame (-2, 1) 4)
        ((frame_iff (by decide)).2 hB) ((frame_iff (by decide)).2 hA)
      have p1 : f (2, -1) := (frame_iff (by decide)).1 a1
      obtain ⟨-, b2, b3⟩ := T3free_step (hf.frame (2, -1) 1) (hT.frame (2, -1) 1)
        ((frame_iff (by decide)).2 p1) ((frame_iff (by decide)).2 hA)
      have p2 : f (3, 1) := (frame_iff (by decide)).1 b2
      have p3 : f (1, 2) := (frame_iff (by decide)).1 b3
      obtain ⟨c1, -, -⟩ := T3free_step (hf.frame (1, 2) 4) (hT.frame (1, 2) 4)
        ((frame_iff (by decide)).2 p3) ((frame_iff (by decide)).2 p2)
      exact (frame_iff (by decide)).1 c1
  · -- Lemmas 2.4 and 2.5: the colouring of Figure 7.
    simp only [NoT3, not_forall, imp_false, not_not] at hT
    obtain ⟨p, b, hb, hp, hpr, hpb⟩ := hT
    obtain ⟨k, rfl⟩ := N3_cases hb
    have g0 : frame f p k (0, 0) := by
      show f (p + rot^[k] (0, 0))
      rw [rotk_zero, show p + ((0 : ℤ), (0 : ℤ)) = p by ext <;> simp]
      exact hp
    have g1 : frame f p k (1, 1) := by
      show f (p + rot^[k] (rot (2, -1)))
      rwa [rotk_rot]
    have g2 : frame f p k (2, -1) := hpb
    have key : ∀ (P : ℤ × ℤ) (K : ℕ), T6 (frame (frame f p k) P K) → f (5, 0) := by
      intro P K h
      rw [frame_frame] at h
      simpa using T6_shift hf h (0, 0) hA
    rcases T3_to_T6 (hf.frame p k) g0 g1 g2 with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ |
        ⟨h1, h2, h3⟩
    · exact key (0, 0) 0 ⟨(frame_iff (by decide)).2 g0, (frame_iff (by decide)).2 g1,
        (frame_iff (by decide)).2 h1, (frame_iff (by decide)).2 g2,
        (frame_iff (by decide)).2 h2, (frame_iff (by decide)).2 h3⟩
    · exact key (1, 1) 4 ⟨(frame_iff (by decide)).2 g1, (frame_iff (by decide)).2 g2,
        (frame_iff (by decide)).2 h2, (frame_iff (by decide)).2 g0,
        (frame_iff (by decide)).2 h1, (frame_iff (by decide)).2 h3⟩
    · exact key (2, -1) 2 ⟨(frame_iff (by decide)).2 g2, (frame_iff (by decide)).2 g0,
        (frame_iff (by decide)).2 h1, (frame_iff (by decide)).2 g1,
        (frame_iff (by decide)).2 h2, (frame_iff (by decide)).2 h3⟩
    · exact key (3, 0) 3 ⟨(frame_iff (by decide)).2 h1, (frame_iff (by decide)).2 g2,
        (frame_iff (by decide)).2 h2, (frame_iff (by decide)).2 g1,
        (frame_iff (by decide)).2 h3, (frame_iff (by decide)).2 g0⟩

/-! ### From the plane to a unit triangular lattice -/

/-- The lattice point with coordinates `(a, b)` is `a + b ω`. -/
noncomputable def φ (v : ℤ × ℤ) : ℂ := (v.1 : ℂ) + (v.2 : ℂ) * ω

lemma φ_add (a b : ℤ × ℤ) : φ (a + b) = φ a + φ b := by
  simp only [φ, Prod.fst_add, Prod.snd_add, Int.cast_add]; ring

lemma φ_sub (a b : ℤ × ℤ) : φ (a - b) = φ a - φ b := by
  simp only [φ, Prod.fst_sub, Prod.snd_sub, Int.cast_sub]; ring

lemma φ_rot (a : ℤ × ℤ) : φ (rot a) = ω * φ a := by
  simp only [φ, rot, Int.cast_neg, Int.cast_add]
  linear_combination (-(a.2 : ℂ)) * ω_sq

lemma normSq_φ (a : ℤ × ℤ) : Complex.normSq (φ a) = (N a : ℝ) := by
  simp only [φ, ω, N, Complex.normSq_apply, Complex.add_re, Complex.intCast_re, Complex.mul_re,
    Complex.intCast_im, Complex.add_im, Complex.mul_im, Int.cast_add, Int.cast_mul]
  linear_combination ((a.2 : ℝ) ^ 2 / 4) * sqrt3_sq

lemma φ_zero : φ (0, 0) = 0 := by simp [φ]

lemma φ_five : φ (5, 0) = 5 := by simp [φ]

section Transfer

variable {R : ℂ → Prop}

lemma red_congr {x y : ℂ} (h : R x) (e : x = y) : R y := e ▸ h

/-- The colouring restricted to the unit triangular lattice `A + (ℤ + ℤ ω) u` satisfies all the
conditions of `Good`. -/
lemma good_of (hadj : NoRedPair R) (h5 : NoBlueℓ5 R)
    {A u : ℂ} (hu : ‖u‖ = 1) : Good (fun v => R (A + φ v * u)) := by
  have hu2 : Complex.normSq u = 1 := by rw [Complex.normSq_eq_norm_sq, hu]; norm_num
  have unit : ∀ e : ℤ × ℤ, N e = 1 → ‖φ e * u‖ = 1 := fun e he =>
    norm_mul_one (by rw [normSq_φ, he]; norm_num) hu
  have n3 : ∀ t : ℤ × ℤ, N t = 3 → Complex.normSq (φ t * u) = 3 := fun t ht => by
    rw [Complex.normSq_mul, normSq_φ, ht, hu2]; norm_num
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro p e he h1 h2
    refine hadj _ _ h2 h1 ?_
    rw [show A + φ (p + e) * u - (A + φ p * u) = φ e * u by rw [φ_add]; ring]
    exact unit e he
  · intro p e he h1 h2 h3 h4 h6
    rcases h5 (A + φ p * u) (φ e * u) (unit e he) with h | h | h | h | h
    · exact h1 h
    · exact h2 (red_congr h (by rw [φ_add]; ring))
    · exact h3 (red_congr h (by rw [φ_add, φ_add]; ring))
    · exact h4 (red_congr h (by rw [φ_add, φ_add, φ_add]; ring))
    · exact h6 (red_congr h (by rw [φ_add, φ_add, φ_add, φ_add]; ring))
  · intro p t ht h1 h2 h3 h4
    refine no_blue_triangle hadj h5 (O := A + φ p * u) (t := φ t * u) (n3 t ht) h1 ?_ ?_ ?_
    · exact fun h => h2 (red_congr h (by rw [φ_add]; ring))
    · exact fun h => h3 (red_congr h (by rw [φ_add, φ_rot, φ_rot]; ring))
    · exact fun h => h4 (red_congr h (by rw [φ_add, φ_rot, φ_rot, φ_rot, φ_rot]; ring))
  · intro p t ht h1 h2 h3 h4
    exact no_red_triangle hadj h5 (O := A + φ p * u) (t := φ t * u) (n3 t ht) h1
      (red_congr h2 (by rw [φ_add]; ring)) (red_congr h3 (by rw [φ_add, φ_rot, φ_rot]; ring))
      (red_congr h4 (by rw [φ_add, φ_rot, φ_rot, φ_rot, φ_rot]; ring))
  · intro p s hs h1 h2 h3 h4 h6
    exact no_red_T7 hadj h5 (p := A + φ p * u) (s := φ s * u) (n3 s hs) h1
      (red_congr h2 (by rw [φ_add]; ring)) (red_congr h3 (by rw [φ_add, φ_add]; ring))
      (red_congr h4 (by rw [φ_add, φ_add, φ_add]; ring))
      (red_congr h6 (by rw [φ_sub, φ_add, φ_add, φ_rot]; ring))

/-- The key consequence of Lemmas 2.5 and 2.6 of Tsaturian: if there is no red unit pair and no
blue `ℓ₅`, then every red point `A` has red translates `A + 5u` for all unit vectors `u`. -/
theorem red_shift (hadj : NoRedPair R) (h5 : NoBlueℓ5 R)
    {A u : ℂ} (hu : ‖u‖ = 1) (hA : R A) : R (A + 5 * u) := by
  have h := lattice_main (good_of hadj h5 (A := A) hu) (red_congr hA (by rw [φ_zero]; ring))
  exact red_congr h (by rw [φ_five])

/-- **Tsaturian's theorem** [Ts17, Theorem 1.1], in terms of the set `R` of red points: if no two
red points are at distance `1`, then there are five blue points `z, z + d, …, z + 4d` with
`‖d‖ = 1`. -/
theorem exists_blue_ℓ5 (hadj : NoRedPair R) :
    ∃ z d : ℂ, ‖d‖ = 1 ∧ ¬R z ∧ ¬R (z + d) ∧ ¬R (z + 2 * d) ∧ ¬R (z + 3 * d) ∧
      ¬R (z + 4 * d) := by
  by_contra hno
  have h5 : ∀ z d : ℂ, ‖d‖ = 1 →
      R z ∨ R (z + d) ∨ R (z + 2 * d) ∨ R (z + 3 * d) ∨ R (z + 4 * d) := by
    intro z d hd
    by_contra h
    simp only [not_or] at h
    exact hno ⟨z, d, hd, h⟩
  obtain ⟨A, hA⟩ : ∃ A, R A := by
    rcases h5 0 1 (by simp) with h | h | h | h | h <;> exact ⟨_, h⟩
  have s99 : Real.sqrt 99 * Real.sqrt 99 = 99 := Real.mul_self_sqrt (by norm_num)
  have hv : ‖(⟨49 / 50, Real.sqrt 99 / 50⟩ : ℂ)‖ = 1 := by
    apply norm_eq_one_of_normSq
    simp only [Complex.normSq_apply]
    nlinarith
  have hB := red_shift hadj h5 (u := 1) (by simp) hA
  have hC := red_shift hadj h5 hv hA
  refine hadj _ _ hB hC (norm_eq_one_of_normSq ?_)
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.add_re, Complex.mul_re,
    Complex.sub_im, Complex.add_im, Complex.mul_im, Complex.one_re, Complex.one_im]
  norm_num
  nlinarith

end Transfer

/-! ### The statements -/

/-- **Tsaturian's theorem** [Ts17, Theorem 1.1]: in every red/blue colouring of the plane
`ℝ² ≅ ℂ` with no two red points at distance `1` (the red points are `Set.univ \ blue`), there are
five blue points `z, z + d, z + 2d, z + 3d, z + 4d` on a line with `‖d‖ = 1`. -/
theorem tsaturian (blue : Set ℂ)
    (hred : (Set.univ \ blue).Pairwise (fun c₁ c₂ => dist c₁ c₂ ≠ 1)) :
    ∃ z d : ℂ, ‖d‖ = 1 ∧ ∀ n : ℕ, n < 5 → z + n • d ∈ blue := by
  obtain ⟨z, d, hd, h0, h1, h2, h3, h4⟩ := exists_blue_ℓ5 (R := fun x => x ∉ blue) (by
    intro x y hx hy hxy
    have hne : x ≠ y := by
      rintro rfl
      simp at hxy
    exact hred ⟨trivial, hx⟩ ⟨trivial, hy⟩ hne (by rw [Complex.dist_eq]; exact hxy))
  refine ⟨z, d, hd, fun n hn => ?_⟩
  simp only [not_not] at h0 h1 h2 h3 h4
  interval_cases n
  · simpa using h0
  · simpa using h1
  · simpa [nsmul_eq_mul] using h2
  · simpa [nsmul_eq_mul] using h3
  · simpa [nsmul_eq_mul] using h4

/-- The same theorem in `EuclideanSpace ℝ (Fin 2)`. -/
theorem tsaturian_euclidean (blue : Set (EuclideanSpace ℝ (Fin 2)))
    (hred : (Set.univ \ blue).Pairwise (fun x y => dist x y ≠ 1)) :
    ∃ z d : EuclideanSpace ℝ (Fin 2), ‖d‖ = 1 ∧ ∀ n : ℕ, n < 5 → z + n • d ∈ blue := by
  let e := Complex.orthonormalBasisOneI.repr
  obtain ⟨z, d, hd, h⟩ := tsaturian (e ⁻¹' blue) (by
    intro x hx y hy hxy hdist
    exact hred ⟨trivial, hx.2⟩ ⟨trivial, hy.2⟩ (e.injective.ne hxy)
      (by rw [LinearIsometryEquiv.dist_map]; exact hdist))
  refine ⟨e z, e d, by rw [LinearIsometryEquiv.norm_map, hd], fun n hn => ?_⟩
  rw [← map_nsmul, ← map_add]
  exact h n hn

/-- **Erdős Problem 188, lower bound `k ≥ 6`** (Tsaturian [Ts17]): every `k` in `Erdos188.s` is at
least `6`. -/
theorem erdos_188.variants.six_le : ∀ k, k ∈ s → 6 ≤ k := by
  rintro k ⟨blue, hred, hno⟩
  by_contra hk
  rw [not_le] at hk
  obtain ⟨z, d, hd, hblue⟩ := tsaturian blue hred
  have hd0 : d ≠ 0 := by
    rintro rfl
    simp at hd
  apply hno
  refine ⟨{z + n • d | (n : ℕ) (_ : (n : ℕ∞) < (k : ℕ∞))}, ?_, z, d, hd, ?_, rfl⟩
  · rintro _ ⟨n, hn, rfl⟩
    exact hblue n (by norm_cast at hn; omega)
  · have himage : {z + n • d | (n : ℕ) (_ : (n : ℕ∞) < (k : ℕ∞))} =
        (fun n : ℕ => z + n • d) '' (Finset.range k : Set ℕ) := by
      ext x
      simp
    change Set.encard _ = _
    rw [himage, Set.InjOn.encard_image, Set.encard_coe_eq_coe_finsetCard, Finset.card_range]
    intro a _ b _ hab
    simpa [nsmul_eq_mul, hd0] using hab

/-- The first half of `erdos_188.variants.estimate` of formal-conjectures (`k ≥ 5`, [EGMRSS75]),
as a consequence. -/
theorem erdos_188.variants.estimate_left : ∀ k, k ∈ s → 5 ≤ k :=
  fun k hk => (erdos_188.variants.six_le k hk).trans' (by norm_num)

/-- Any answer to `erdos_188` (the least element of `s`) is at least `6`. -/
theorem erdos_188.variants.isLeast_six_le (m : ℕ) (hm : IsLeast s m) : 6 ≤ m :=
  erdos_188.variants.six_le m hm.1

end Erdos188
