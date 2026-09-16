# JSP-000378: request for review of an all-parameter formalization and endpoint obstruction

**Status:** Locally verified proof package for contribution review. Official acceptance and any award decision remain pending.

**Prize problem:** JSP-000378 — [Can arbitrarily large planar point sets have all pairwise distances uniformly bounded away from the nearest integer?](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0301-0400.md#JSP-000378)

**Original problem:** [Erdős Problem 466](https://www.erdosproblems.com/466).

## Request

Please assess the incremental formalization described below, including its correspondence to the original problem, overlap with prior public Lean work, and whether the additional contribution is eligible for recognition under JSP-000378. Please attribute only the additional work supported by the submitted evidence. The original mathematical solution and an existing complete Lean solution of the original existence question belong to the prior work identified below.

This package was prepared with Codex assistance for the submitting GitHub account `jinkaizhang236-sketch`. The additional formalization described below is the only contribution submitted for review. No recipient record, priority, contribution share, or award decision is created or asserted. Existing relevant prize discussions are identified below.

## Exact result submitted

Let

\[
\|t\|_{\mathbb Z}=\min_{z\in\mathbb Z}|t-z|.
\]

For \(\delta>0\) and \(X\ge0\), let \(N(X,\delta)\) be the maximum size of a finite set in a closed Euclidean disk of radius \(X\) such that

\[
\|\operatorname{dist}(P_i,P_j)\|_{\mathbb Z}\ge\delta
\quad\text{whenever }i\ne j.
\]

The principal statement is

\[
\forall\delta>0,\qquad
\lim_{X\to+\infty}N(X,\delta)=+\infty
\quad\Longleftrightarrow\quad
\delta<\tfrac12.
\]

Its Lean declaration is `Erdos466General.erdos_466_parameter_classification` in the canonical `Erdos466.lean` (assembled from `source-components/Erdos466General.lean` and the other attributed components):

```lean
theorem erdos_466_parameter_classification {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun X : ℝ ↦ N X δ) atTop atTop ↔ δ < 1 / 2
```

The package also supplies:

- `infinite_configuration`: for every \(0\le\delta<1/2\), an injective sequence of planar points with all mutual distances strictly more than \(\delta\) from the nearest integer;
- `N_realizable`: for \(\delta>0\), the natural-number supremum defining \(N(X,\delta)\) is an attained maximum;
- `N_tendsto_infinity`: convergence for every \(0<\delta<1/2\), with the original non-strict pairwise distance condition;
- `no_four_at_or_above_half` and `N_le_three_at_or_above_half`: at \(\delta\ge1/2\), no four-point configuration is possible and \(N(X,\delta)\le3\);
- `erdos_466`: the original existence question as a corollary, using \(\delta=1/10\).

The positivity assumption on the maximum-cardinality limit is intentional. The infinite construction also works at \(\delta=0\), but every disk of positive radius then admits arbitrarily large finite sets, so a natural-number supremum cannot be used as their maximum.

## Prior work and the increment being reviewed

Ronald Graham's mathematical solution is recorded on the [Erdős 466 page](https://www.erdosproblems.com/466). The problem is already solved. The page also records Sárközy's stronger quantitative growth results; this submission does not improve those growth bounds.

A prior complete Lean formalization is publicly available in [plby/lean-proofs at commit `8822f7ddef30fadbd92e1c6ab4ed897af356af5e`](https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos466.lean). It proves the original existence question with \(\delta=1/10\) using \(P_m=(2^m,4^m)\). The source credits Ronald Graham for the mathematics; Codex and GPT-5.6 Sol for the formalization; and The Formal Conjectures Authors in its copyright notice. Its nearest-integer interval argument and compactness argument are reused or adapted with attribution. A catalogue's “Lean No” field must not be treated as evidence that this earlier proof does not exist.

The existing proof evidence is already discussed in [Issue #16](https://github.com/TheJustinSunPrize/awards/issues/16) and the source register in [PR #40](https://github.com/TheJustinSunPrize/awards/pull/40). This request should be cross-linked to those records and assessed for its additional formalized statements; it does not replace or appropriate their prior evidence work.

Relative to that inspected fixed-parameter source, the additional package formalizes the following stronger scope:

1. **All parameters below one half.** Choose an integer \(q\ge4\) with \((1-2\delta)q>4\) and use \(P_m=(q^m,q^{2m})\). The proof handles every pair of indices and establishes the required uniform distance bound without discarding a finite prefix.
2. **The non-strict endpoint.** At distance at least \(1/2\) from the integers, all pairwise distances are half-integers. Scaling by two gives odd integral distances, and a Gram-determinant congruence modulo eight excludes four planar points.
3. **The original maximum and limit.** A compactness bound makes the natural-number supremum an attained maximum. Finite prefixes and monotonicity in the radius then give the stated limit and its converse.

The endpoint obstruction is a classical consequence of R. L. Graham, B. L. Rothschild, and E. G. Straus, [*Are There n+2 Points in E^n with Odd Integral Distances?*](https://doi.org/10.2307/2318906), *American Mathematical Monthly* 81(1) (1974), 21–25. The package gives a direct coordinate and congruence proof of the planar case. It does not claim a new mathematical theorem or a first proof of that obstruction.

This comparison establishes additional scope relative to the named inspected implementation. It does not establish worldwide priority or guarantee that no equivalent formalization exists elsewhere. The requested review concerns that incremental contribution, not ownership of the original solution or all prior formal work. Details of reused material and credits are in `ATTRIBUTION.md`.

## Proof outline

For \(i<j\), put \(u=q^i\), \(v=q^j\), and \(a=v^2-u^2\in\mathbb Z\). The distance \(D\) between the corresponding parabola points satisfies

\[
D^2=a^2+(v-u)^2.
\]

The choice of \(q\) implies

\[
a+\delta<D<a+\tfrac12<a+1-\delta.
\]

Hence every integer is more than \(\delta\) from \(D\). For the converse, the squares of six odd integral distances are all one modulo eight. The determinant of twice the Gram matrix of the three displacement vectors is then four modulo eight. In the plane that determinant is zero, a contradiction.

`README.md` gives the mathematical argument; a Chinese companion is included in the separately delivered archive. The Lean files connect these calculations to the standard Euclidean metric, nearest-integer rounding, finite point configurations, and the limit definition.

## Source and verification evidence

All local verification stages completed on 2026-09-16. The accompanying intake submission links this directory at an immutable public commit; it does not rely on a mutable branch as the proof identity.

| Evidence | Observed status |
| --- | --- |
| Canonical source digest | SHA-256 `1e4c3c35392b21578cf3f620b56dc3dee6f0db3c3040d9b1afca92a2d0c2a20a` |
| Locked environment | Lean 4.34.0; Mathlib `5ed2965256430c3649e86755f9576b54eca72435`; all revisions in `lake-manifest.json` |
| Complete canonical-source compilation | Exit 0; 73.463 seconds; only non-error import/style warnings |
| Lean kernel replay including imports | `leanchecker --fresh Erdos466`: exit 0; 708.752 seconds |
| Theorem-closure export | Exit 0; 127.344 seconds; 145,728,907 bytes |
| Independent kernel | Nanoda 0.4.17: exit 0; 7.221 seconds; 27,805 declarations checked with no errors |
| Both theorem axiom reports | Exactly `propext`, `Classical.choice`, `Quot.sound` |
| Statement and contribution comparison | Submitter-side AI-assisted review in `STATEMENT_REVIEW.md`; no official signature asserted |
| Public contributor account | `jinkaizhang236-sketch`; Codex assistance disclosed; no recipient record or identity attestation created |
| Official verification, eligibility and award | Pending organizer assessment |

Full commands, exit codes, actual tool identities, locked dependencies, source/export hashes, and network-denial control results are in `verification/verification.public.json`. Complete checker logs and the log-publication hash map accompany that record. The export SHA-256 is `35fc58ff0e23fa84afd99f6086b39a096879d3affdcc85116b6f58faedec8ec4`. The large generated export is retained locally and can be reproduced with the pinned exporter; it is not committed. Reproduction instructions and tool provenance are in `verification-tools/`.

Compilation, replay, export and independent checking ran with network access denied under a tested macOS policy. Filesystem isolation and a complete rebuild of cached dependencies from source are **not** claimed. Leanchecker is Lean's own kernel; Nanoda is the separate Rust implementation. Official verifier/curator signatures are **not** asserted.

The package was initially developed with Lean 4.33.1 and finally verified with the pinned Lean 4.34.0 release. The source was frozen and hash-checked throughout the final run. Machine-check success concerns the exact formal theorem statements and does not establish global priority, novelty, prize eligibility, or acceptance.
