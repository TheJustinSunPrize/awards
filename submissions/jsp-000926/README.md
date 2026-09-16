# JSP-000926 / Erdős 1115: geometric length of continuous asymptotic curves

**Proposed classification: Partial Progress. Contributor-run compilation, axiom checks, and kernel replay passed; official review remains pending.**

This supplement extends an existing Lean formalization of the Gol'dberg–Eremenko counterexample to the linear-length question in [Erdős Problem 1115](https://www.erdosproblems.com/1115). The submitted target uses geometric arc length for every curve continuous on the nonnegative half-line. It requires only that the absolute value of the entire function along the curve tends to infinity; escape of the curve itself is derived.

The contribution is a formal geometric-scope completion of the existing construction. It does not claim a new mathematical counterexample, a first formalization, the prescribed-order variants, or a solution to the broader question of optimal length in terms of maximum modulus. See [SCOPE.md](SCOPE.md) for exact quantifiers and limitations.

## Proposed main statement

Target: `Erdos1115.not_erdos_1115_continuousOn`, in module `JSP000926.CurveStatement`.

For every real function `phi` tending to positive infinity, the target constructs a nonconstant entire function `f` of some finite order, with unbounded range and an eventual growth estimate

`log M(r,f) <= C * phi(r) * (log r)^2`.

For every `gamma : R -> C` continuous on `[0,infinity)`, if `|f(gamma(t))|` tends to infinity, its geometric length in the open disk `|z| < r` has no eventual linear upper bound. No speed, differentiability, or unit-speed parameter assumption is imposed. Locally rectifiable continuous curves are included.

The length counts repeated traversal with multiplicity. It is the supremum of finite sums of total variations over ordered, interior-disjoint compact parameter intervals whose entire images lie in the open disk. Infinite values remain infinite. Values of the curve at negative parameters do not affect the definition or conclusion.

## Existing work and the added proof

The mathematical counterexample is due to A. A. Gol'dberg and Alexandre Eremenko. The analytic construction and alternating-gate argument are reused from [plby/lean-proofs at commit 8822f7ddef30fadbd92e1c6ab4ed897af356af5e](https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos1115.lean). That file credits Codex and GPT-5.6 Sol as formal authors and carries an Apache-2.0 notice. Its attribution and applicable license notices must accompany the reused source and adapted argument.

The existing path definition is globally `LipschitzWith 1`, while its disk-length expression measures parameter time spent in the disk. Such a speed bound allows slow movement and pauses. The added proof obtains a geometric lower bound directly from the same alternating gates: consecutive gate crossings have a large chord distance, and their finite chord sum is bounded by total variation on a subarc wholly inside the disk. It does not infer geometric length from occupation time.

The new modules provide:

- `JSP000926.GeometricLength`: localized variation length, the geometric labyrinth barrier, and the counterexample for continuous escaping curves.
- `JSP000926.LengthProperties`: radius monotonicity, a bound for finite ordered subarc sums, and finite disk length for locally bounded-variation curves that escape.
- `JSP000926.CurveStatement`: independence from negative parameters, derivation of curve escape from function-value escape, and the half-line target above.

The supplement was prepared with OpenAI Codex assistance. Attribution to existing authors records provenance; it is not a signature, recipient nomination, or endorsement by those authors.

## Reproduction and verification

The public helper was actually run from this package on Windows using Lean 4.33.0
(commit `d8b18978322de05a8f3dba51ef03cf5461676c17`) and Mathlib
`db584cd6d46c92f209a44c0f1c829460d327499d`. It bootstrapped the exact upstream
bytes, compiled all five package modules into a fresh output directory, audited
six named targets, and explicitly replayed each of the five modules. All ten
process steps passed. Every target uses only `propext`, `Classical.choice`, and
`Quot.sound`. Exact source hashes, tool hashes, timestamps, durations and replay
module lists are in [evidence/verification.json](evidence/verification.json);
the frozen source/helper manifest is [source-manifest.json](source-manifest.json).

Use an existing checkout and compiled cache of the exact Mathlib pin, with its
pinned package caches, and the stated Lean toolchain. From this package run:

```text
python reproduce.py --lean-bin /path/to/lean-4.33.0/bin --mathlib-dir /path/to/mathlib
```

On Windows, quote paths containing spaces. The helper never modifies the supplied
Mathlib or toolchain directories. It fixes `LEAN_SYSROOT` and `LEAN_NUM_THREADS=1`,
checks the Lean commit and Mathlib manifest, fetches the prerequisite by hash,
and rebuilds every custom module in a new `.reproduction/` directory. On a shared
machine, coordinate concurrent Lean jobs outside this helper; it acquires no lock.
Its complete results are saved under `.reproduction/`.

The usual Lake route is also configured (the tested end-to-end route above used
the existing pinned cache):

```text
python bootstrap_upstream.py
lake exe cache get
lake build JSP000926
lake env leanchecker --verbose JSP000926.Upstream
lake env leanchecker --verbose JSP000926.GeometricLength
lake env leanchecker --verbose JSP000926.LengthProperties
lake env leanchecker --verbose JSP000926.CurveStatement
lake env leanchecker --verbose JSP000926.Audit
```

Existing Mathlib/dependency binaries were imported; a full dependency rebuild,
network-disabled isolation, and an independently implemented checker are not
claimed. `leanchecker` replays with the same Lean kernel. Separate AI source and
scope reviews are summarized in [evidence/semantic-review.md](evidence/semantic-review.md);
they are not organizer-appointed or human attestations. Attribution and bounded
public duplicate searches are documented in [PROVENANCE.md](PROVENANCE.md).

## Intake status

Recipient placeholder: `RECIPIENT-JSP-000926-A`; confirmation pending.

This is a proposed Partial Progress intake package. It does not assert official acceptance, eligibility, a prize award, a curator or verifier signature, or an entitlement to payment. The mathematical scope and verification status should be reviewed separately.
