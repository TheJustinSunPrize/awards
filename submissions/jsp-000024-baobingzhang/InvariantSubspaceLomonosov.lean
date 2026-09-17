import Mathlib

/-!
# Lomonosov's invariant subspace theorem (Hilden's proof) and corollaries

Partial progress on the invariant subspace problem (JSP-000024). The problem itself, for every
bounded operator on a separable infinite-dimensional complex Hilbert space, is open and is not
proved here.

## Main results

Let `X` be a complex Banach space.

* `exists_hyperinvariant_of_isCompactOperator` (**Lomonosov**, 1973): if `X` is
  infinite-dimensional, every nonzero compact operator `K` on `X` has a nontrivial closed
  hyperinvariant subspace, i.e. a closed subspace `M ≠ 0, X` with `A M ⊆ M` for every bounded
  `A` commuting with `K`.
* `lomonosov` (**Lomonosov**, 1973): if `dim X ≥ 2` and a bounded operator `T` commutes with a
  nonzero compact operator, then `T` has a nontrivial closed invariant subspace.
* `aronszajn_smith` (**Aronszajn–Smith**, 1954; von Neumann for Hilbert spaces): every compact
  operator on `X` with `dim X ≥ 2` has a nontrivial closed invariant subspace.
* `bernstein_robinson` (**Bernstein–Robinson** 1966, Halmos 1966): the same holds for every
  polynomially compact operator, i.e. when `p(T)` is compact for some nonzero polynomial `p`.
* Hilbert-space forms with exactly the binders of `Invariant_subspace_problem` from
  formal-conjectures (`Invariant_subspace_problem_of_isCompactOperator`,
  `Invariant_subspace_problem_of_commute_isCompactOperator`).
* The formal-conjectures variants `Invariant_subspace_problem_finite_dimensional` and
  `Invariant_subspace_problem_normal_operator` (both tagged "research solved" there), under their
  original names and with their original statements.

The structure `ClosedInvariantSubspace` and the statements of the two formal-conjectures variants
are copied verbatim from Google DeepMind's formal-conjectures project,
`FormalConjectures/Wikipedia/InvariantSubspaceProblem.lean` (Apache-2.0); only the
`@[category ..., AMS 47]` attributes, which need that project's utilities, are omitted.
Here `2 ≤ Module.rank ℂ X` is the hypothesis `dim X ≥ 2` used there (for `dim X ≤ 1` every
subspace is `0` or `X`).

## Proof

* **Eigenvectors.** If `T v = μ v` with `v ≠ 0`, then `ℂ v` is closed (finite-dimensional),
  `T`-invariant and proper since `dim X ≥ 2` (`nonempty_of_apply_eq_smul`). In finite dimension
  `T` has an eigenvector because `ℂ` is algebraically closed; this gives the finite-dimensional
  variant.
* **Nonzero eigenvalue of `K`.** If `K v = λ v` with `λ ≠ 0`, `v ≠ 0`, the eigenspace
  `ker (K - λ)` is closed, nonzero and invariant under every `A` commuting with `K`. It is proper
  when `X` is infinite-dimensional: otherwise `K = λ • 1`, so the identity is compact and `X` is
  finite-dimensional (Riesz).
* **Quasinilpotent `K`** (Hilden's argument, `exists_hyperinvariant_of_spectralRadius_eq_zero`).
  If `K` has no nonzero eigenvalue, the Fredholm alternative (Mathlib,
  `IsCompactOperator.hasEigenvalue_iff_mem_spectrum`) gives `spectrum K ⊆ {0}`, so the spectral
  radius is `0` and Gelfand's formula gives `‖K ^ n‖ ^ (1 / n) → 0`. Suppose no nontrivial
  closed subspace is invariant under the commutant `{K}'`. For `y ≠ 0`, the closure of the orbit
  `{A y | A ∈ {K}'}` is such a subspace containing `y`, hence equals `X`. Choose `x₀` with
  `‖K x₀‖ = 2‖K‖` (so `‖x₀‖ ≥ 2`) and put `B = ball x₀ 1`. The set `C = closure (K B)` is
  compact and lies in `closedBall (K x₀) ‖K‖`, so `0 ∉ C`. The open sets `A⁻¹ B`, `A ∈ {K}'`,
  cover `C`; take a finite subcover `A_1, …, A_m` and `c = 1 + Σ ‖A_i‖`. By induction there are
  `W_n ∈ {K}'` with `‖W_n‖ ≤ c ^ n` and `W_n (K ^ n x₀) ∈ B`: given `W_n`, the point
  `K (W_n (K ^ n x₀)) = W_n (K ^ (n + 1) x₀)` lies in `C`, so some `A_i` moves it into `B`, and
  `W_(n+1) = A_i W_n`. Hence `1 ≤ ‖x₀‖ - 1 < c ^ n ‖K ^ n‖ ‖x₀‖`, i.e.
  `1 / 2 < c ^ n ‖K ^ n‖` for all `n`, contradicting `‖K ^ n‖ ^ (1 / n) → 0`.
* **Corollaries.** For compact `T`: `T = 0` has every line invariant, otherwise take `K = T`.
  For polynomially compact `T`: if `p(T) ≠ 0` take `K = p(T)`, which commutes with `T`; if
  `p(T) = 0`, a root `μ` of the minimal polynomial `(X - μ) q` gives an eigenvector `q(T) v`.
* **Normal operators** on a Hilbert space (continuous functional calculus). If the spectrum is a
  single point `a` then `T = a • 1` and every line is invariant. Otherwise pick `a ≠ b` in the
  spectrum and continuous bumps `f`, `g` supported in disjoint discs around `a` and `b`. Then
  `f(T) g(T) = 0`, `f(T) ≠ 0 ≠ g(T)`, and `ker f(T)` is closed, `T`-invariant, proper and
  contains the nonzero range of `g(T)`.

## References

* V. I. Lomonosov, *Invariant subspaces of the family of operators that commute with a completely
  continuous operator*, Funct. Anal. Appl. 7 (1973), 213–214.
* A. J. Michaels, *Hilden's simple proof of Lomonosov's invariant subspace theorem*,
  Adv. Math. 25 (1977), 56–58.
* N. Aronszajn, K. T. Smith, *Invariant subspaces of completely continuous operators*,
  Ann. of Math. 60 (1954), 345–350.
* A. R. Bernstein, A. Robinson, *Solution of an invariant subspace problem of K. T. Smith and
  P. R. Halmos*, Pacific J. Math. 16 (1966), 421–431; P. R. Halmos, *Invariant subspaces of
  polynomially compact operators*, Pacific J. Math. 16 (1966), 433–437.
* H. Radjavi, P. Rosenthal, *Invariant Subspaces*, 2nd ed., Dover, 2003.
-/

open Filter Topology Module

namespace InvariantSubspaceProblem

variable {H : Type*} [NormedAddCommGroup H]

/-- `ClosedInvariantSubspace T` is the type of non-trivial (different from `H` and `{0}`) closed
subspaces of a complex vector space `H` that are invariant under the action of linear map `T`. -/
structure ClosedInvariantSubspace [Module ℂ H] (T : H →L[ℂ] H) where
  toSubspace : Submodule ℂ H
  ne_bot : toSubspace ≠ ⊥
  ne_top : toSubspace ≠ ⊤
  is_closed : IsClosed (toSubspace : Set H)
  is_fixed : toSubspace.map T.toLinearMap ≤ toSubspace

section Banach

/-! ### Complex Banach spaces -/

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]

/-- The line spanned by an eigenvector is a nontrivial closed invariant subspace once
`dim X ≥ 2`. -/
theorem nonempty_of_apply_eq_smul (hdim : 2 ≤ Module.rank ℂ X) (T : X →L[ℂ] X) {v : X} {μ : ℂ}
    (hv : v ≠ 0) (hTv : T v = μ • v) : Nonempty (ClosedInvariantSubspace T) := by
  refine ⟨⟨ℂ ∙ v, ?_, ?_, ?_, ?_⟩⟩
  · exact Submodule.span_singleton_eq_bot.not.mpr hv
  · intro h
    have h1 := rank_span_le (R := ℂ) ({v} : Set X)
    rw [h, rank_top, Cardinal.mk_singleton] at h1
    have := hdim.trans h1
    norm_num at this
  · exact Submodule.closed_of_finiteDimensional _
  · rw [Submodule.map_span_le]
    rintro _ rfl
    simp only [ContinuousLinearMap.coe_coe, hTv]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)

/-- A space of dimension at least `2` has a nonzero vector. -/
theorem nontrivial_of_two_le_rank (hdim : 2 ≤ Module.rank ℂ X) : Nontrivial X :=
  rank_pos_iff_nontrivial.mp (lt_of_lt_of_le (by norm_num) hdim)

/-- The orbit `{A y | A K = K A}` of `y` under the commutant of `K`, as a subspace. -/
def orbit (K : X →L[ℂ] X) (y : X) : Submodule ℂ X where
  carrier := {x | ∃ A : X →L[ℂ] X, A * K = K * A ∧ A y = x}
  add_mem' := by
    rintro _ _ ⟨A, hA, rfl⟩ ⟨B, hB, rfl⟩
    exact ⟨A + B, by rw [add_mul, mul_add, hA, hB], rfl⟩
  zero_mem' := ⟨0, by simp, rfl⟩
  smul_mem' := by
    rintro c _ ⟨A, hA, rfl⟩
    exact ⟨c • A, by rw [smul_mul_assoc, mul_smul_comm, hA], rfl⟩

/-- `y` lies in its own orbit (take `A = 1`). -/
theorem mem_orbit_self (K : X →L[ℂ] X) (y : X) : y ∈ orbit K y :=
  ⟨1, by rw [one_mul, mul_one], rfl⟩

/-- The orbit is invariant under every operator commuting with `K`. -/
theorem map_orbit_le {K B : X →L[ℂ] X} (hB : B * K = K * B) (y : X) :
    (orbit K y).map B.toLinearMap ≤ orbit K y := by
  rintro _ ⟨_, ⟨A, hA, rfl⟩, rfl⟩
  exact ⟨B * A, by rw [mul_assoc, hA, ← mul_assoc, hB, mul_assoc], rfl⟩

/-- **Hilden's argument.** A nonzero compact operator `K` with spectral radius `0` on a complex
Banach space has a nontrivial closed subspace invariant under every operator commuting with `K`. -/
theorem exists_hyperinvariant_of_spectralRadius_eq_zero [CompleteSpace X] {K : X →L[ℂ] X}
    (hK : IsCompactOperator K) (hK0 : K ≠ 0) (hρ : spectralRadius ℂ K = 0) :
    ∃ M : Submodule ℂ X, M ≠ ⊥ ∧ M ≠ ⊤ ∧ IsClosed (M : Set X) ∧
      ∀ A : X →L[ℂ] X, A * K = K * A → M.map A.toLinearMap ≤ M := by
  by_contra! hcon
  -- every nonzero vector has a dense orbit under the commutant of `K`
  have hdense : ∀ y : X, y ≠ 0 → Dense (orbit K y : Set X) := by
    intro y hy
    rw [Submodule.dense_iff_topologicalClosure_eq_top]
    by_contra htop
    obtain ⟨A, hA, hAM⟩ := hcon (orbit K y).topologicalClosure
      (fun h => hy (by
        have := (orbit K y).le_topologicalClosure (mem_orbit_self K y)
        rwa [h, Submodule.mem_bot] at this))
      htop (Submodule.isClosed_topologicalClosure _)
    apply hAM
    calc (orbit K y).topologicalClosure.map A.toLinearMap
        ≤ ((orbit K y).map A.toLinearMap).topologicalClosure :=
          Submodule.topologicalClosure_map A _
      _ ≤ (orbit K y).topologicalClosure :=
          Submodule.topologicalClosure_mono (map_orbit_le hA y)
  -- choose `x₀` with `‖K x₀‖ = 2 ‖K‖`, so that `‖x₀‖ ≥ 2`
  obtain ⟨x₁, hx₁⟩ : ∃ x₁, K x₁ ≠ 0 := by
    by_contra! h
    exact hK0 (ContinuousLinearMap.ext h)
  have hKpos : 0 < ‖K‖ := norm_pos_iff.mpr hK0
  have hKx₁ : 0 < ‖K x₁‖ := norm_pos_iff.mpr hx₁
  set x₀ : X := ((2 * ‖K‖ / ‖K x₁‖ : ℝ) : ℂ) • x₁ with hx₀
  have hKx₀ : ‖K x₀‖ = 2 * ‖K‖ := by
    rw [hx₀, map_smul, norm_smul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    field_simp
  have hx₀2 : 2 ≤ ‖x₀‖ := by
    have h := K.le_opNorm x₀
    rw [hKx₀] at h
    nlinarith
  set B := Metric.ball x₀ 1 with hB
  set C := closure (K '' B) with hC
  have hCc : IsCompact C := hK.isCompact_closure_image_of_bounded Metric.isBounded_ball
  have hC0 : ∀ y ∈ C, y ≠ 0 := by
    have hsub : C ⊆ Metric.closedBall (K x₀) ‖K‖ := by
      refine closure_minimal ?_ Metric.isClosed_closedBall
      rintro _ ⟨z, hz, rfl⟩
      rw [Metric.mem_closedBall, dist_eq_norm, ← map_sub]
      refine (K.le_opNorm _).trans ?_
      rw [Metric.mem_ball, dist_eq_norm] at hz
      nlinarith [norm_nonneg (z - x₀)]
    rintro y hy rfl
    have := hsub hy
    rw [Metric.mem_closedBall, dist_zero_left, hKx₀] at this
    linarith
  -- finitely many commuting operators move every point of `C` into `B`
  let ι := {A : X →L[ℂ] X // A * K = K * A}
  have hcover : C ⊆ ⋃ A : ι, (A : X →L[ℂ] X) ⁻¹' B := by
    intro y hy
    obtain ⟨_, ⟨A, hA, rfl⟩, hAy⟩ :=
      (hdense y (hC0 y hy)).exists_mem_open Metric.isOpen_ball ⟨x₀, Metric.mem_ball_self one_pos⟩
    exact Set.mem_iUnion.mpr ⟨⟨A, hA⟩, hAy⟩
  obtain ⟨t, ht⟩ := hCc.elim_finite_subcover (fun A : ι => (A : X →L[ℂ] X) ⁻¹' B)
    (fun A => Metric.isOpen_ball.preimage A.1.continuous) hcover
  set c : ℝ := 1 + ∑ A ∈ t, ‖(A : X →L[ℂ] X)‖ with hc
  have hc1 : 1 ≤ c := by
    have : 0 ≤ ∑ A ∈ t, ‖(A : X →L[ℂ] X)‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
    linarith
  have hct : ∀ A ∈ t, ‖(A : X →L[ℂ] X)‖ ≤ c := by
    intro A hA
    have := Finset.single_le_sum (f := fun A : ι => ‖(A : X →L[ℂ] X)‖)
      (fun _ _ => norm_nonneg _) hA
    linarith
  -- iterating: for every `n` some product `W` of such operators has `W (K ^ n x₀) ∈ B`
  have hiter : ∀ n : ℕ, ∃ W : X →L[ℂ] X, W * K = K * W ∧ ‖W‖ ≤ c ^ n ∧ W ((K ^ n) x₀) ∈ B := by
    intro n
    induction n with
    | zero =>
      refine ⟨1, by rw [one_mul, mul_one], ?_, ?_⟩
      · rw [pow_zero]
        exact ContinuousLinearMap.norm_id_le
      · rw [pow_zero]
        exact Metric.mem_ball_self one_pos
    | succ n ih =>
      obtain ⟨W, hW, hWn, hWB⟩ := ih
      have hy : K (W ((K ^ n) x₀)) ∈ C := subset_closure ⟨_, hWB, rfl⟩
      obtain ⟨A, hAt, hA⟩ := Set.mem_iUnion₂.mp (ht hy)
      refine ⟨A.1 * W, ?_, ?_, ?_⟩
      · rw [mul_assoc, hW, ← mul_assoc, A.2, mul_assoc]
      · rw [pow_succ']
        exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
          (mul_le_mul (hct A hAt) hWn (norm_nonneg _) (by linarith))
      · have : K (W ((K ^ n) x₀)) = W ((K ^ (n + 1)) x₀) := by
          rw [pow_succ']
          exact (congrArg (fun F : X →L[ℂ] X => F ((K ^ n) x₀)) hW).symm
        rw [this] at hA
        exact hA
  -- hence `1 / 2 < c ^ n ‖K ^ n‖` for all `n`
  have hlow : ∀ n : ℕ, 1 / 2 < c ^ n * ‖K ^ n‖ := by
    intro n
    obtain ⟨W, -, hWn, hWB⟩ := hiter n
    rw [Metric.mem_ball, dist_eq_norm] at hWB
    have h1 : ‖x₀‖ - 1 < ‖W ((K ^ n) x₀)‖ := by
      have := norm_sub_norm_le x₀ (W ((K ^ n) x₀))
      rw [norm_sub_rev] at this
      linarith
    have h2 : ‖W ((K ^ n) x₀)‖ ≤ c ^ n * ‖K ^ n‖ * ‖x₀‖ := by
      calc ‖W ((K ^ n) x₀)‖ ≤ ‖W‖ * ‖(K ^ n) x₀‖ := W.le_opNorm _
        _ ≤ c ^ n * (‖K ^ n‖ * ‖x₀‖) :=
          mul_le_mul hWn ((K ^ n).le_opNorm _) (norm_nonneg _) (by positivity)
        _ = c ^ n * ‖K ^ n‖ * ‖x₀‖ := by ring
    by_contra! hn
    have : c ^ n * ‖K ^ n‖ * ‖x₀‖ ≤ 1 / 2 * ‖x₀‖ :=
      mul_le_mul_of_nonneg_right hn (norm_nonneg _)
    linarith
  -- but Gelfand's formula gives `‖K ^ n‖ ^ (1 / n) → 0`
  have hG := spectrum.pow_norm_pow_one_div_tendsto_nhds_spectralRadius K
  rw [hρ] at hG
  have hG' : Tendsto (fun n : ℕ => ‖K ^ n‖ ^ (1 / n : ℝ)) atTop (𝓝 0) := by
    have := (ENNReal.continuousAt_toReal ENNReal.zero_ne_top).tendsto.comp hG
    simp only [ENNReal.toReal_zero] at this
    refine this.congr fun n => ?_
    simp only [Function.comp_apply]
    exact ENNReal.toReal_ofReal (by positivity)
  have hε : (0 : ℝ) < 1 / (2 * c) := by positivity
  obtain ⟨n, hn⟩ := ((hG'.eventually (gt_mem_nhds hε)).and (eventually_ge_atTop 1)).exists
  have hn0 : n ≠ 0 := by omega
  have hKn : ‖K ^ n‖ < (1 / (2 * c)) ^ n := by
    have := pow_lt_pow_left₀ hn.1 (by positivity) hn0
    rwa [one_div (n : ℝ), Real.rpow_inv_natCast_pow (norm_nonneg _) hn0] at this
  have : c ^ n * ‖K ^ n‖ < 1 / 2 := by
    calc c ^ n * ‖K ^ n‖ < c ^ n * (1 / (2 * c)) ^ n :=
          mul_lt_mul_of_pos_left hKn (by positivity)
      _ = (1 / 2) ^ n := by
          rw [← mul_pow]
          congr 1
          field_simp
      _ ≤ 1 / 2 := pow_le_of_le_one (by norm_num) (by norm_num) hn0
  linarith [hlow n]

/-- **Lomonosov's theorem** (hyperinvariant form). A nonzero compact operator `K` on an
infinite-dimensional complex Banach space has a nontrivial closed hyperinvariant subspace: a closed
subspace `M ≠ ⊥, ⊤` that is invariant under every bounded operator commuting with `K`. -/
theorem exists_hyperinvariant_of_isCompactOperator [CompleteSpace X]
    (hX : ¬ FiniteDimensional ℂ X) {K : X →L[ℂ] X} (hK : IsCompactOperator K) (hK0 : K ≠ 0) :
    ∃ M : Submodule ℂ X, M ≠ ⊥ ∧ M ≠ ⊤ ∧ IsClosed (M : Set X) ∧
      ∀ A : X →L[ℂ] X, A * K = K * A → M.map A.toLinearMap ≤ M := by
  by_cases hμ : ∃ μ : ℂ, μ ≠ 0 ∧ Module.End.HasEigenvalue (K : End ℂ X) μ
  · obtain ⟨μ, hμ0, hμ⟩ := hμ
    refine ⟨Module.End.eigenspace (K : End ℂ X) μ, hμ, ?_, ?_, ?_⟩
    · intro htop
      apply hX
      have hKf : (K : X → X) = μ • id := by
        funext x
        have hx : x ∈ Module.End.eigenspace (K : End ℂ X) μ := htop ▸ Submodule.mem_top
        simpa using Module.End.mem_eigenspace_iff.mp hx
      have h := hK
      rw [hKf, IsCompactOperator.smul_iff₀ hμ0] at h
      exact FiniteDimensional.of_isCompactOperator_id h
    · have : (Module.End.eigenspace (K : End ℂ X) μ : Set X) = {x | K x = μ • x} := by
        ext x
        exact Module.End.mem_eigenspace_iff
      rw [this]
      exact isClosed_eq K.continuous (continuous_const_smul μ)
    · rintro A hA _ ⟨x, hx, rfl⟩
      rw [SetLike.mem_coe, Module.End.mem_eigenspace_iff] at hx
      rw [Module.End.mem_eigenspace_iff]
      change K (A x) = μ • A x
      have hx' : K x = μ • x := hx
      calc K (A x) = A (K x) := (congrArg (fun F : X →L[ℂ] X => F x) hA).symm
        _ = μ • A x := by rw [hx', map_smul]
  · push Not at hμ
    refine exists_hyperinvariant_of_spectralRadius_eq_zero hK hK0 ?_
    rw [spectralRadius_eq_of_unital]
    refine nonpos_iff_eq_zero.mp (iSup₂_le fun k hk => ?_)
    by_cases hk0 : k = 0
    · simp [hk0]
    · exact absurd ((hK.hasEigenvalue_iff_mem_spectrum hk0).mpr hk) (hμ k hk0)

/--
Every (bounded) linear operator `T : H → H` on a finite-dimensional normed space `H` of dimension
at least 2 has a non-trivial (closed) `T`-invariant subspace. This can be solved using the Jordan
normal form, which is
[not yet in mathlib](https://leanprover-community.github.io/undergrad_todo.html).

`H` is a complex normed space: with a bare `Module ℂ H` unrelated to the norm, finite-dimensional
subspaces need not be closed, and the statement fails already in complex dimension `2`.

(Statement and docstring from formal-conjectures. Proved here with an eigenvector of `T`.) -/
theorem Invariant_subspace_problem_finite_dimensional [NormedSpace ℂ H] (h : FiniteDimensional ℂ H)
    (hdim : 2 ≤ Module.rank ℂ H) (T : H →L[ℂ] H) : Nonempty (ClosedInvariantSubspace T) := by
  have := nontrivial_of_two_le_rank hdim
  obtain ⟨μ, hμ⟩ := Module.End.exists_eigenvalue (T : End ℂ H)
  obtain ⟨v, hv⟩ := hμ.exists_hasEigenvector
  exact nonempty_of_apply_eq_smul hdim T hv.2 hv.apply_eq_smul

/-- **Lomonosov's theorem.** On a complex Banach space of dimension at least `2`, a bounded
operator `T` commuting with a nonzero compact operator `K` has a non-trivial closed invariant
subspace. -/
theorem lomonosov [CompleteSpace X] (hdim : 2 ≤ Module.rank ℂ X) (T K : X →L[ℂ] X)
    (hK : IsCompactOperator K) (hK0 : K ≠ 0) (hTK : T * K = K * T) :
    Nonempty (ClosedInvariantSubspace T) := by
  by_cases hX : FiniteDimensional ℂ X
  · exact Invariant_subspace_problem_finite_dimensional hX hdim T
  · obtain ⟨M, hM0, hM1, hMc, hMA⟩ := exists_hyperinvariant_of_isCompactOperator hX hK hK0
    exact ⟨⟨M, hM0, hM1, hMc, hMA T hTK⟩⟩

/-- **Aronszajn–Smith theorem.** Every compact operator on a complex Banach space of dimension at
least `2` has a non-trivial closed invariant subspace. -/
theorem aronszajn_smith [CompleteSpace X] (hdim : 2 ≤ Module.rank ℂ X) (T : X →L[ℂ] X)
    (hT : IsCompactOperator T) : Nonempty (ClosedInvariantSubspace T) := by
  by_cases hT0 : T = 0
  · have := nontrivial_of_two_le_rank hdim
    obtain ⟨v, hv⟩ := exists_ne (0 : X)
    exact nonempty_of_apply_eq_smul hdim T (μ := 0) hv (by simp [hT0])
  · exact lomonosov hdim T T hT hT0 rfl

/-- An operator annihilated by a nonzero polynomial has an eigenvector. -/
theorem exists_apply_eq_smul_of_aeval_eq_zero [Nontrivial X] (T : X →L[ℂ] X)
    {p : Polynomial ℂ} (hp : p ≠ 0) (h : Polynomial.aeval T p = 0) :
    ∃ v : X, v ≠ 0 ∧ ∃ μ : ℂ, T v = μ • v := by
  have hint : IsIntegral ℂ T := isAlgebraic_iff_isIntegral.mp ⟨p, hp, h⟩
  obtain ⟨μ, hμ⟩ := IsAlgClosed.exists_root (minpoly ℂ T) (minpoly.degree_pos hint).ne'
  obtain ⟨q, hq⟩ := Polynomial.dvd_iff_isRoot.mpr hμ
  obtain ⟨v, hv⟩ : ∃ v : X, Polynomial.aeval T q v ≠ 0 := by
    by_contra! hc
    have hmon : q.Monic :=
      (Polynomial.monic_X_sub_C μ).of_mul_monic_left (hq ▸ minpoly.monic hint)
    have hle := minpoly.min ℂ T hmon (ContinuousLinearMap.ext hc)
    rw [hq, Polynomial.degree_mul, Polynomial.degree_X_sub_C,
      Polynomial.degree_eq_natDegree hmon.ne_zero] at hle
    norm_cast at hle
    omega
  refine ⟨Polynomial.aeval T q v, hv, μ, ?_⟩
  have := congrArg (fun F : X →L[ℂ] X => F v) (minpoly.aeval ℂ T)
  simpa [hq, sub_eq_zero] using this

/-- **Bernstein–Robinson theorem** (Halmos' form). Every polynomially compact operator on a
complex Banach space of dimension at least `2`, i.e. one with `p(T)` compact for some nonzero
polynomial `p`, has a non-trivial closed invariant subspace. -/
theorem bernstein_robinson [CompleteSpace X] (hdim : 2 ≤ Module.rank ℂ X) (T : X →L[ℂ] X)
    {p : Polynomial ℂ} (hp : p ≠ 0) (hpT : IsCompactOperator (Polynomial.aeval T p)) :
    Nonempty (ClosedInvariantSubspace T) := by
  by_cases h0 : Polynomial.aeval T p = 0
  · have := nontrivial_of_two_le_rank hdim
    obtain ⟨v, hv, μ, hTv⟩ := exists_apply_eq_smul_of_aeval_eq_zero T hp h0
    exact nonempty_of_apply_eq_smul hdim T hv hTv
  · have hc := (Polynomial.commute_X p).map (Polynomial.aeval T)
    rw [Polynomial.aeval_X] at hc
    exact lomonosov hdim T _ hpT h0 hc.eq

end Banach

/-! ### Hilbert spaces, with the binders of formal-conjectures' `Invariant_subspace_problem` -/

/-- The invariant subspace problem, with the hypotheses of formal-conjectures'
`Invariant_subspace_problem`, holds for compact operators (von Neumann; Aronszajn–Smith). -/
theorem Invariant_subspace_problem_of_isCompactOperator [InnerProductSpace ℂ H]
    [TopologicalSpace.SeparableSpace H] [CompleteSpace H] (hdim : 2 ≤ Module.rank ℂ H)
    (T : H →L[ℂ] H) (hT : IsCompactOperator T) : Nonempty (ClosedInvariantSubspace T) :=
  aronszajn_smith hdim T hT

/-- The invariant subspace problem, with the hypotheses of formal-conjectures'
`Invariant_subspace_problem`, holds for operators commuting with a nonzero compact operator
(Lomonosov). -/
theorem Invariant_subspace_problem_of_commute_isCompactOperator [InnerProductSpace ℂ H]
    [TopologicalSpace.SeparableSpace H] [CompleteSpace H] (hdim : 2 ≤ Module.rank ℂ H)
    (T K : H →L[ℂ] H) (hK : IsCompactOperator K) (hK0 : K ≠ 0) (hTK : T * K = K * T) :
    Nonempty (ClosedInvariantSubspace T) :=
  lomonosov hdim T K hK hK0 hTK

/--
Every normal linear operator `T : H → H` on a Hilbert space `H` of dimension at least 2 has a
non-trivial closed `T`-invariant subspace. If `T` is a multiple of the identity, one can tafrake any
non-trivial subspace . If not, one can take any nontrivial spectral subspace of `T`.

(Statement and docstring from formal-conjectures. Proved here with the continuous functional
calculus: the kernel of `f(T)` for a bump function `f` around one point of the spectrum.) -/
theorem Invariant_subspace_problem_normal_operator [InnerProductSpace ℂ H] [CompleteSpace H]
    (hdim : 2 ≤ Module.rank ℂ H) (T : H →L[ℂ] H) [IsStarNormal T]:
    Nonempty (ClosedInvariantSubspace T) := by
  have := nontrivial_of_two_le_rank hdim
  by_cases hsub : ∃ a ∈ spectrum ℂ T, ∃ b ∈ spectrum ℂ T, a ≠ b
  · obtain ⟨a, ha, b, hb, hab⟩ := hsub
    set r : ℝ := ‖a - b‖ / 2 with hr
    have hr0 : 0 < r := by
      have := norm_pos_iff.mpr (sub_ne_zero.mpr hab)
      positivity
    set f : ℂ → ℂ := fun z => ((max 0 (r - ‖z - a‖) : ℝ) : ℂ) with hf
    set g : ℂ → ℂ := fun z => ((max 0 (r - ‖z - b‖) : ℝ) : ℂ) with hg
    have hfc : Continuous f := by rw [hf]; fun_prop
    have hgc : Continuous g := by rw [hg]; fun_prop
    have hfg : (fun z => f z * g z) = 0 := by
      funext z
      simp only [Pi.zero_apply, hf, hg]
      by_cases h1 : r - ‖z - a‖ ≤ 0
      · simp [max_eq_left h1]
      · have h2 : r - ‖z - b‖ ≤ 0 := by
          have := norm_add_le (z - b) (a - z)
          rw [show z - b + (a - z) = a - b by ring, norm_sub_rev a z] at this
          linarith
        simp [max_eq_left h2]
    have hfa : f a ≠ 0 := by simp [hf, hr0.le, hr0.ne']
    have hgb : g b ≠ 0 := by simp [hg, hr0.le, hr0.ne']
    set F := cfc f T with hF
    set G := cfc g T with hG
    have hFG : F * G = 0 := by
      rw [hF, hG, ← cfc_mul f g T hfc.continuousOn hgc.continuousOn, hfg, cfc_zero]
    have hG0 : G ≠ 0 := by
      intro h
      have := eqOn_of_cfc_eq_cfc (h.trans (cfc_zero ℂ T).symm) hgc.continuousOn continuousOn_const
      exact hgb (this hb)
    have hF0 : F ≠ 0 := by
      intro h
      have := eqOn_of_cfc_eq_cfc (h.trans (cfc_zero ℂ T).symm) hfc.continuousOn continuousOn_const
      exact hfa (this ha)
    have hTF : T * F = F * T := by
      have := cfc_commute_cfc id f T
      rwa [cfc_id ℂ T] at this
    refine ⟨⟨LinearMap.ker (F : H →ₗ[ℂ] H), ?_, ?_, F.isClosed_ker, ?_⟩⟩
    · obtain ⟨x, hx⟩ : ∃ x, G x ≠ 0 := by
        by_contra! h
        exact hG0 (ContinuousLinearMap.ext h)
      refine (Submodule.ne_bot_iff _).mpr ⟨G x, ?_, hx⟩
      exact congrArg (fun E : H →L[ℂ] H => E x) hFG
    · intro htop
      apply hF0
      ext x
      have : x ∈ LinearMap.ker (F : H →ₗ[ℂ] H) := htop ▸ Submodule.mem_top
      exact this
    · rintro _ ⟨x, hx, rfl⟩
      change F (T x) = 0
      have hx' : F x = 0 := hx
      calc F (T x) = T (F x) := (congrArg (fun E : H →L[ℂ] H => E x) hTF).symm
        _ = 0 := by rw [hx', map_zero]
  · push Not at hsub
    obtain ⟨a, ha⟩ := spectrum.nonempty T
    have hT := CFC.eq_algebraMap_of_spectrum_subset_singleton T a
      (fun b hb => Set.mem_singleton_iff.mpr (hsub b hb a ha))
    obtain ⟨v, hv⟩ := exists_ne (0 : H)
    refine nonempty_of_apply_eq_smul hdim T (μ := a) hv ?_
    rw [hT]
    simp [Algebra.algebraMap_eq_smul_one]

end InvariantSubspaceProblem
