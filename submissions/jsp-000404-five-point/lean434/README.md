# JSP-000404: exact cases N=5 through N=8

**Partial formalization. The arbitrary-N Sendov classification is not proved.**

This Lean 4.34 integration proves, in one dependency environment:

- `JSP404.alpha_five_eq_three_pi_div_five`: `alpha 5 = 3*pi/5` (108 degrees).
- `JSP404.alpha_eq_two_pi_div_three`: `alpha N = 2*pi/3` for every `6 <= N <= 8` (120 degrees).
- `JSP404.small_cases_exact`: the conjunction of both statements.
- `SendovSixPointPlane.finite_set_large_angle`: every finite set of at least six distinct Euclidean-plane points contains a pairwise-distinct triple with angle at least `2*pi/3`.

`alpha`, `Guaranteed`, and `HasLargeAngle` are the actual planar definitions in the pinned upstream project. `Point` is `EuclideanSpace Real (Fin 2)`; angles are Mathlib's `EuclideanGeometry.angle`. No general-position or convexity assumption is added. Equality is an extremal threshold and does not assert that its infimum is attained.

## Attribution and scope

The upper bounds and extremal definitions are by superpilot69 and the credited contributors in [PR #42](https://github.com/TheJustinSunPrize/awards/pull/42), fixed at commit `722cb3caa86710c788296ca0ec954a79e9a0adcc`. They are imported as a pinned Git dependency, preserving the upstream license and attribution. This integration does not claim authorship of those constructions. The mathematics is historical: Sendov, *A minimax problem for point configurations*, Acta Mathematica Hungarica 69 (1995), 27-46, [DOI](https://doi.org/10.1007/BF01874605).

The added contribution, prepared by zilan520 with Codex assistance, consists of the five- and six-point lower bounds, their geometric transfers, and the equalities combining those bounds with the attributed upper constructions. The original five-point package remains available in the parent directory on Lean 4.19. This directory ports that proof to the same Lean 4.34 version as the upper-bound project and extends the small cases.

For six points, 15 direction variables and 20 triangle constraints imply `3 <= t`. The generated proof has 2,961 case splits and 2,962 linear-arithmetic leaves. Every leaf is a Lean proof. Z3 only generated the tree; it is neither required nor trusted for verification. A generic projection and ordering derive the constraints from actual angles, and a finite maximum gives the 120-degree conclusion. Selecting six points extends the lower bound to larger finite sets.

`SendovDirectionModel.card_bound_transfer` is explicitly conditional on a general combinatorial inequality. That inequality remains unproved; this conditional helper is not presented as a general solution. Neither global priority nor award entitlement is asserted. Please assess the added formalization under the partial-progress/contribution rules.

## Reproduction

Use Lean 4.34.0 and the committed dependency manifest. Mathlib is fixed at `5ed2965256430c3649e86755f9576b54eca72435`.

```sh
lake exe cache get
python verify.py
```

`verify.py` checks pinned clean dependency source trees, builds the package, rechecks every local module using `lean --trust=0`, audits all printed axiom closures, and records source/log hashes in `verification/result.json`. Only `propext`, `Classical.choice`, and `Quot.sound` are permitted. The local run uses compiled Mathlib caches, not a network-isolated rebuild.

See [INDEPENDENT.md](INDEPENDENT.md) for separate implementation checks and deliberate invalid-proof controls. Official isolated verification, independent reviewer sign-off, statement-fidelity/attribution review, and award assessment remain outstanding.
