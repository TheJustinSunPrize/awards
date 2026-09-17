# JSP-000024: Invariant subspace problem, Lomonosov's theorem (Hilden's proof): operators commuting with a nonzero compact operator, plus Aronszajn–Smith, Bernstein–Robinson and the normal/finite-dimensional variants

Catalog entry: [JSP-000024](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0001-0100.md#JSP-000024)

## Problem

Invariant subspace problem (formal-conjectures `Invariant_subspace_problem`; catalog JSP-000024): does every bounded linear operator on a separable infinite-dimensional complex Hilbert space have a nonzero proper closed invariant subspace?

## Scope

Partial progress: classical positive results for special classes of operators — Lomonosov's theorem (1973; hyperinvariant subspaces for nonzero compact operators on infinite-dimensional complex Banach spaces, and invariant subspaces for every operator commuting with a nonzero compact operator), Aronszajn–Smith (compact operators), Bernstein–Robinson/Halmos (polynomially compact operators), and the formal-conjectures variants for normal operators and finite-dimensional spaces. The invariant subspace problem for general bounded operators on separable Hilbert space remains open and is not addressed. Lomonosov's stronger statement that a non-scalar operator commuting with a nonzero compact operator has a hyperinvariant subspace (for T itself) is not formalized.

## Formal statements

All results are in `InvariantSubspaceLomonosov.lean`. `ClosedInvariantSubspace` and the statements of `Invariant_subspace_problem_finite_dimensional` and `Invariant_subspace_problem_normal_operator` are copied verbatim (docstrings included) from Google DeepMind's formal-conjectures `FormalConjectures/Wikipedia/InvariantSubspaceProblem.lean` (Apache-2.0), omitting only the `@[category …]` attributes. `2 ≤ Module.rank ℂ X` is FC's dimension hypothesis; separability is kept in the Hilbert-space forms only to match FC's binders and is not used.

```lean
theorem exists_hyperinvariant_of_isCompactOperator [CompleteSpace X]
    (hX : ¬ FiniteDimensional ℂ X) {K : X →L[ℂ] X} (hK : IsCompactOperator K) (hK0 : K ≠ 0) :
    ∃ M : Submodule ℂ X, M ≠ ⊥ ∧ M ≠ ⊤ ∧ IsClosed (M : Set X) ∧
      ∀ A : X →L[ℂ] X, A * K = K * A → M.map A.toLinearMap ≤ M

theorem exists_hyperinvariant_of_spectralRadius_eq_zero [CompleteSpace X] {K : X →L[ℂ] X}
    (hK : IsCompactOperator K) (hK0 : K ≠ 0) (hρ : spectralRadius ℂ K = 0) :
    ∃ M : Submodule ℂ X, M ≠ ⊥ ∧ M ≠ ⊤ ∧ IsClosed (M : Set X) ∧
      ∀ A : X →L[ℂ] X, A * K = K * A → M.map A.toLinearMap ≤ M

theorem lomonosov [CompleteSpace X] (hdim : 2 ≤ Module.rank ℂ X) (T K : X →L[ℂ] X)
    (hK : IsCompactOperator K) (hK0 : K ≠ 0) (hTK : T * K = K * T) :
    Nonempty (ClosedInvariantSubspace T)

theorem aronszajn_smith [CompleteSpace X] (hdim : 2 ≤ Module.rank ℂ X) (T : X →L[ℂ] X)
    (hT : IsCompactOperator T) : Nonempty (ClosedInvariantSubspace T)

theorem bernstein_robinson [CompleteSpace X] (hdim : 2 ≤ Module.rank ℂ X) (T : X →L[ℂ] X)
    {p : Polynomial ℂ} (hp : p ≠ 0) (hpT : IsCompactOperator (Polynomial.aeval T p)) :
    Nonempty (ClosedInvariantSubspace T)

theorem Invariant_subspace_problem_finite_dimensional [NormedSpace ℂ H] (h : FiniteDimensional ℂ H)
    (hdim : 2 ≤ Module.rank ℂ H) (T : H →L[ℂ] H) : Nonempty (ClosedInvariantSubspace T)

theorem Invariant_subspace_problem_of_isCompactOperator [InnerProductSpace ℂ H]
    [TopologicalSpace.SeparableSpace H] [CompleteSpace H] (hdim : 2 ≤ Module.rank ℂ H)
    (T : H →L[ℂ] H) (hT : IsCompactOperator T) : Nonempty (ClosedInvariantSubspace T)

theorem Invariant_subspace_problem_of_commute_isCompactOperator [InnerProductSpace ℂ H]
    [TopologicalSpace.SeparableSpace H] [CompleteSpace H] (hdim : 2 ≤ Module.rank ℂ H)
    (T K : H →L[ℂ] H) (hK : IsCompactOperator K) (hK0 : K ≠ 0) (hTK : T * K = K * T) :
    Nonempty (ClosedInvariantSubspace T)

theorem Invariant_subspace_problem_normal_operator [InnerProductSpace ℂ H] [CompleteSpace H]
    (hdim : 2 ≤ Module.rank ℂ H) (T : H →L[ℂ] H) [IsStarNormal T]:
    Nonempty (ClosedInvariantSubspace T)
```

With `ClosedInvariantSubspace` copied verbatim from formal-conjectures, for a complex Banach space `X`: `exists_hyperinvariant_of_isCompactOperator` (X infinite-dimensional, K compact, K ≠ 0 ⇒ ∃ closed M ≠ ⊥, ⊤ with A M ⊆ M for every A commuting with K), `exists_hyperinvariant_of_spectralRadius_eq_zero` (Hilden's core step, any X), `lomonosov` (2 ≤ rank X, K compact nonzero, TK = KT ⇒ Nonempty (ClosedInvariantSubspace T)), `aronszajn_smith` (T compact), `bernstein_robinson` (p ≠ 0, p(T) compact); Hilbert-space forms with exactly the binders of FC's open `Invariant_subspace_problem` plus one hypothesis (`Invariant_subspace_problem_of_isCompactOperator`, `..._of_commute_isCompactOperator`); and FC's research-solved variants `Invariant_subspace_problem_finite_dimensional` and `Invariant_subspace_problem_normal_operator` under their original names and statements.

## Proof outline

Eigenvector lines give invariant subspaces (dim ≥ 2). If K has a nonzero eigenvalue λ, ker(K − λ) is hyperinvariant and proper in infinite dimension (else the identity would be compact). Otherwise the Fredholm alternative gives spectral radius 0 and Hilden's argument applies: if the commutant has no invariant subspace, every nonzero orbit is dense; pick x₀ with ‖Kx₀‖ = 2‖K‖, B = ball(x₀,1), cover the compact closure of K(B) (which avoids 0) by finitely many A_i⁻¹(B), and build W_n in the commutant with ‖W_n‖ ≤ cⁿ and W_n Kⁿ x₀ ∈ B, so 1/2 < cⁿ‖Kⁿ‖ for all n, contradicting Gelfand's formula. Corollaries: compact T (take K = T), polynomially compact T (K = p(T), or an eigenvector if p(T) = 0). Normal operators: continuous functional calculus with disjoint bump functions around two spectral points; ker f(T) is invariant, closed and proper.

## Build and verification

- Lean `v4.34.0` (`leanprover/lean4:v4.34.0`)
- Mathlib tag `v4.34.0`, commit `5ed2965256430c3649e86755f9576b54eca72435`; all dependencies are pinned in `lake-manifest.json`

```sh
lake exe cache get
lake build
```

`#print axioms` (see `verification/axioms.txt`):

```
'InvariantSubspaceProblem.exists_hyperinvariant_of_isCompactOperator' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'InvariantSubspaceProblem.exists_hyperinvariant_of_spectralRadius_eq_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'InvariantSubspaceProblem.lomonosov' depends on axioms: [propext, Classical.choice, Quot.sound]
'InvariantSubspaceProblem.aronszajn_smith' depends on axioms: [propext, Classical.choice, Quot.sound]
'InvariantSubspaceProblem.bernstein_robinson' depends on axioms: [propext, Classical.choice, Quot.sound]
'InvariantSubspaceProblem.Invariant_subspace_problem_finite_dimensional' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'InvariantSubspaceProblem.Invariant_subspace_problem_of_isCompactOperator' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'InvariantSubspaceProblem.Invariant_subspace_problem_of_commute_isCompactOperator' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'InvariantSubspaceProblem.Invariant_subspace_problem_normal_operator' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

The file contains no `sorry`, no `axiom` declarations and no `native_decide`. The build log and the SHA-256 of
`InvariantSubspaceLomonosov.lean` (`195e4dacf0dd5b91e01f76d54f513ae68a42809fd812a67b6e84730711d57a67`) are in `verification/`.

## Attribution

- Mathematics: V. I. Lomonosov, Funct. Anal. Appl. 7 (1973) 213–214; H. M. Hilden's proof as written by A. J. Michaels, Adv. Math. 25 (1977) 56–58; N. Aronszajn and K. T. Smith, Ann. of Math. 60 (1954) 345–350 (von Neumann for Hilbert spaces); A. R. Bernstein and A. Robinson, Pacific J. Math. 16 (1966) 421–431; P. R. Halmos, Pacific J. Math. 16 (1966) 433–437; standard spectral-theorem argument for normal operators (Radjavi–Rosenthal, Invariant Subspaces). Lean formalization written with AI assistance (Anthropic Claude), using Mathlib's Fredholm alternative, Gelfand formula and continuous functional calculus.
- Lean formalization: GitHub user `baobingzhang`, developed with AI assistance (Anthropic Claude).


No priority for the mathematics is claimed; the contribution is the Lean formalization.
