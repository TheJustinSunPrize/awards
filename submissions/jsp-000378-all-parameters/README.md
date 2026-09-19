# JSP-000378 / Erdős 466 — full separation-parameter classification

This package formalizes a parameter extension of Graham's planar construction, including the non-strict endpoint obstruction. It is a contribution for review, not a new solution of an open problem or an award announcement.

For every positive real `δ`, the largest admissible number `N(X,δ)` of points in a Euclidean disk of radius `X`, with each mutual distance at least `δ` from the nearest integer, tends to infinity as `X` tends to infinity **if and only if `δ < 1/2`**.

The canonical proof is [Erdos466.lean](Erdos466.lean). Its main declarations are:

- `Erdos466General.erdos_466_parameter_classification`: the full equivalence for all `δ > 0`;
- `Erdos466General.erdos_466`: the original existence question;
- `Erdos466General.infinite_configuration`: an infinite explicit construction for every `0 ≤ δ < 1/2`;
- `Erdos466General.N_le_three_at_or_above_half`: the endpoint and above it admit at most three points.

The source uses the standard Euclidean metric and nearest-integer rounding. For positive separation it proves that its natural-number supremum is an attained finite maximum. The condition `δ > 0` is essential to that definition; no maximum-cardinality assertion at `δ = 0` is made.

## Mathematical argument

For `0 ≤ δ < 1/2`, choose a natural number `q ≥ 4` such that `(1−2δ)q > 4`, and put `P_m = (q^m,q^(2m))`. For indices `i < j`, write `u = q^i`, `v = q^j`, and `a = v²−u²`. Here `a` is an integer, `u ≥ 1`, and `v ≥ qu`.

The distance `D` between the points satisfies `D² = a² + (v−u)²`. Direct factorization gives

```
D² − (a+δ)² = (v−u)((1−2δ)v−(1+2δ)u) − δ² > 0,
(a+1/2)² − D² = 2u(v−u) + 1/4 > 0.
```

Thus `a+δ < D < a+1/2 < a+1−δ`, so `D` is more than `δ` from every integer. For `0 < δ < 1/2`, each finite prefix fits in a disk, and radius monotonicity gives the full limit. Compactness and a finite cover by balls of radius `δ/3` ensure the maximum-cardinality definition is well founded.

Conversely, a real number at least `1/2` from the integers must be a half-integer. Four admissible points at separation `δ ≥ 1/2` would therefore give, after scaling by two, four planar points whose six mutual distances are odd integers. Their squared distances are all `1` modulo `8`. The determinant of twice the Gram matrix of the three displacement vectors is then `4` modulo `8`, whereas three planar vectors have zero Gram determinant. This contradiction bounds every such configuration by three points.

## Prior work and contribution

Graham solved the original existence problem long ago. The public [plby proof](https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos466.lean) already formalizes that full existence question for `δ = 1/10`, and is credited in the source and [ATTRIBUTION.md](ATTRIBUTION.md). This package extends that inspected scope to every parameter below one half and adds the non-strict endpoint classification. The odd-distance obstruction is classical work of Graham, Rothschild and Straus. No new mathematical discovery, global first-formalization priority, or improvement of Sárközy's quantitative growth bounds is claimed.

The six development components are retained in `source-components/`. `assemble.py` only collects external imports at the top and concatenates their bodies; `assembly.json` records their hashes and the canonical-source hash. Formal verification targets the canonical file itself.

## Reproduction

The toolchain is Lean **4.34.0**, pinned by `lean-toolchain`; Mathlib is pinned to **5ed2965256430c3649e86755f9576b54eca72435**, with all transitive revisions in `lake-manifest.json`.

With this Lean toolchain installed, obtain the pinned dependencies and their caches, then run:

```sh
lake exe cache get
lake build
```

For proof replay and the independent Nanoda kernel check, follow [verification-tools/VERIFY.md](verification-tools/VERIFY.md). It specifies the exporter and checker source revisions, permitted axioms, exact theorem targets, and actual network restriction. All four verification stages passed on 2026-09-16. Nanoda checked 27,805 declarations with no errors. The results and limitations are recorded in [verification/verification.public.json](verification/verification.public.json) and the accompanying logs.

Reproduction evidence is distinct from official statement review or an award decision. No official curator or verifier signature is asserted. The process uses cached dependencies and rechecks the exported theorem dependency closure; it does not claim a complete rebuild of Mathlib from source or filesystem isolation.

## References

- [Official JSP-000378 catalog entry](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0301-0400.md#JSP-000378).
- [Erdős Problem 466](https://www.erdosproblems.com/466).
- [Prior proof registration, Issue #16](https://github.com/TheJustinSunPrize/awards/issues/16), and [source register, PR #40](https://github.com/TheJustinSunPrize/awards/pull/40).
- R. L. Graham, B. L. Rothschild, E. G. Straus, [Are There n+2 Points in E^n with Odd Integral Distances?](https://doi.org/10.2307/2318906), *American Mathematical Monthly* 81 (1974), 21–25.

See [LICENSE](LICENSE) and [ATTRIBUTION.md](ATTRIBUTION.md).
