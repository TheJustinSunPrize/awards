# Scope of JSP-000926 / Erdős 1115

**Classification: Partial Progress. Verification status: pending.**

This document describes the statements in the proposed source. It does not certify that the source has compiled or passed kernel replay.

## Quantifiers of the proposed terminal theorem

`Erdos1115.not_erdos_1115_continuousOn` states that for every `phi : R -> R` with `phi(r) -> +infinity`, there exists `f : C -> C` satisfying all of the following:

1. `f` is nonconstant and its range is unbounded.
2. `f` is complex differentiable everywhere, and there exist `A >= 0` and `rho >= 0` such that `|f(z)| <= A * exp(|z|^rho)` for every complex `z`. This is the upstream predicate `EntireOfFiniteOrder`.
3. There exists `C >= 0` such that, for all sufficiently large real `r`, `log M(r,f) <= C * phi(r) * (log r)^2`. Here `M(r,f)` is the upstream maximum modulus on the circle `|z| = r`. The estimate is one-sided; no lower growth bound is asserted.
4. `f` has the explicit geometric escaping-barrier certificate `HasGeometricEscapingBarriers`.
5. For every map `gamma : R -> C` continuous on `[0,infinity)`, if `|f(gamma(t))| -> +infinity` as `t -> +infinity`, then `HasLinearGeometricLength gamma` is false.

The function `f` is chosen before the universal quantifier over curves. The growth constant may depend on `phi` and the constructed function. A putative linear-length constant could depend on the curve: the conclusion excludes every such constant for every eligible curve.

There is no separate escape hypothesis in the terminal target. `curve_escapes_of_composition_escapes` derives `|gamma(t)| -> +infinity` from continuity of `f` and divergence of `|f(gamma(t))|`, using boundedness of the continuous image of a compact closed disk. Continuity of `gamma` is required only on the nonnegative half-line; a constant extension supplies the globally continuous representative used internally.

## Meaning of geometric disk length

For a finite index set `Fin n`, admissible intervals `[a_i,b_i]` satisfy:

- `0 <= a_i <= b_i`;
- `|gamma(t)| < r` for every `t` in the entire closed interval `[a_i,b_i]`;
- `b_i <= a_j` whenever `i < j`.

`geometricLengthInDisc gamma r` is the supremum, in the extended nonnegative reals, of the sums `sum_i eVariationOn gamma [a_i,b_i]` over all such finite families. Mathlib's `eVariationOn` is the supremum of finite polygonal chord sums on each interval. This gives arc length with multiplicity along the parameterized curve. It is not occupation time or the Hausdorff measure of the image with repeated visits erased.

The intervals can share endpoints but cannot overlap in their interiors. Degenerate intervals contribute zero. Requiring their whole images to lie in the open disk prevents charging the connection between two visits when the curve leaves the disk in between. In particular, this definition is not `eVariationOn` on the possibly disconnected set of all in-disk parameter times.

`HasLinearGeometricLength gamma` means that there exists a real `C >= 0` with

`geometricLengthInDisc gamma r <= ENNReal.ofReal (C*r)`

for all sufficiently large real `r`. This is an eventual bound, not a bound demanded at every positive radius. Infinite length cannot satisfy it.

The supporting targets are:

- `Erdos1115.geometricLengthInDisc_mono`: disk length is monotone in the radius.
- `Erdos1115.sum_ordered_subarc_variation_le`: ordered subarc sums are bounded by variation on a containing compact parameter interval.
- `Erdos1115.geometricLengthInDisc_le_variation_of_time_bound`: a bound on all in-disk times uniformly bounds the supremum defining length.
- `Erdos1115.geometricLengthInDisc_ne_top_of_locallyBoundedVariationOn`: local bounded variation on `[0,infinity)` and escape imply finite length in every disk.
- `Erdos1115.geometricLengthInDisc_eq_of_eqOn_nonneg`: changing negative-parameter values leaves every disk length unchanged.

For continuous locally rectifiable paths, interval variation is the usual polygonal arc length, and finite compact-subarc families localize it to the open disk. The terminal theorem quantifies over all continuous half-line curves, so it includes these paths. No theorem identifying this definition with a separately constructed arc-length measure, no general arc-length reparameterization construction, and no comparison with image Hausdorff measure is claimed as part of this package.

## What is added to the existing formalization

The [pinned plby source](https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos1115.lean) defines its path condition as `LipschitzWith 1` and its disk length as the measure of nonnegative parameter times in the disk. A parameter speed at most one does not equate these times with geometric arc length.

`Erdos1115.labyrinth_isGeometricLengthBarrier` adapts the existing first-hitting and alternating-gate argument. The new step bounds total variation below by the sum of distances between successive gate crossings. A single compact subarc contains these crossings and lies strictly inside the required open disk. Consequently the lower bound holds for continuous curves without a speed assumption. The existing entire-function construction and growth estimates then give `not_erdos_1115_geometric`, followed by the half-line interface in `not_erdos_1115_continuousOn`.

This is an incremental formal extension of mathematics due to A. A. Gol'dberg and Alexandre Eremenko and of the plby formalization credited to Codex / GPT-5.6 Sol. The upstream construction and adapted proof retain their attribution and Apache-2.0 notices. No claim of first discovery or first formalization is made.

## Limits of the Partial Progress claim

The target supplies the geometric counterexample to the particular question of an `O(r)` asymptotic curve, including arbitrary divergent loss above the `(log r)^2` threshold. It supplies **some finite order** for the constructed function.

It does not prove existence of such counterexamples at every prescribed finite order in `[0,infinity)`, prove Hayman's positive threshold result, or answer the general optimal-growth question for `ell(r)` in terms of `M(r)`. These are reasons to retain the Partial Progress classification for the broader problem.

The contributor-run public helper completed all five compilations, all five exact-module kernel replays, and all six target-axiom checks. See `evidence/verification.json` and `source-manifest.json`. Designated organizer statement review and acceptance remain pending. `RECIPIENT-JSP-000926-A` is an unconfirmed placeholder, not a confirmed recipient or an official signature.
