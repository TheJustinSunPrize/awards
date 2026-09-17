# JSP-000242: certified optimization and uniform bounds for unit fractions

This package provides a complete fixed-cardinality decision procedure, a proved
optimizer for every number of terms at least three, uniform analytic upper
bounds, and exact modular prime obstructions. It is a scoped Lean formalization
submission, with AI assistance disclosed. It does not prove the lower-bound
construction in Croot's short-interval theorem or claim new mathematics.

## Statements and their correspondence

For a finite set `A` of distinct positive integers with reciprocal sum one,
let `B(k)` be the largest achievable value of `min A` among sets with exactly
`k` elements. Positivity, exact cardinality, rational sum, membership of the
minimum, and the lower-bound condition all occur in
`UnitFractionBounds.AttainableMinimum` in [UnitFractionBounds.lean](UnitFractionBounds.lean).
There is no imposed maximum denominator in this optimization problem.

### A complete decision procedure and optimizer

For every natural cardinality `k`, positive lower denominator bound `m`, and
rational target `r`, `possible_iff_finset` proves:

```lean
possible k m r = true ↔
  ∃ A : Finset ℕ, A.card = k ∧
    (∀ a ∈ A, m ≤ a) ∧ (∑ a ∈ A, (1 : ℚ) / a) = r
```

The finite recursion derives the next denominator bound `floor(k/r)` from the
remaining positive sum, and decreases `k`. A consecutive-denominator reciprocal
envelope prunes impossible branches. Both positive and negative answers are
proved correct for the actual finite-set problem, including arbitrarily large
individual denominators. This is a termination and correctness result, not an
efficient-complexity claim.

[UnitFractionOptimum.lean](UnitFractionOptimum.lean) defines the computable
`optimalMinimum`. The bound `m ≤ k` on a feasible lower denominator threshold is
proved before it is used to form the finite candidate set. For every `k ≥ 3`:

```lean
IsGreatest {m | AttainableMinimum k m} (optimalMinimum k)
```

Thus the returned value is attained and globally optimal. The module also proves
`possible k m 1 = true ↔ m ≤ optimalMinimum k` for every positive `m`, and
monotonicity of `B(k)` on `k ≥ 3`. The extension step replaces a largest denominator
`a ≥ 2` by `a+1` and `a(a+1)`, preserving distinctness and the lower denominator
bound. The exceptional outputs are `B(1)=1`, while zero is a sentinel for the
infeasible cardinalities zero and two; no attained minimum is asserted there.

### Uniform analytic upper bounds

[UnitFractionAsymptotic.lean](UnitFractionAsymptotic.lean) proves, for every finite
representation of a positive rational `r` with `k` distinct denominators at
least `m > 0`,

```text
m < k / (exp(r) - 1) + 1/2.
```

In particular, for every `k ≥ 3`,

```text
B(k) < k / (e - 1) + 1/2,
B(k)/k < 1/(e - 1) + 1/(2k).
```

The quantified eventual upper estimate holds for every positive epsilon. The
proof bounds each reciprocal strictly by the logarithmic increment across its
midpoint interval and telescopes the resulting sum. It uses the proved optimizer
and actual finite-set representations. It does not assume Croot's construction.
It does not prove convergence of `B(k)/k` or a matching asymptotic lower bound.

### Exact finite optima

The ten `IsGreatest` certificates in the initial module remain unchanged:

| `k` | `B(k)` | One attaining set |
| --- | --- | --- |
| 3 | 2 | 2, 3, 6 |
| 4 | 2 | 2, 3, 7, 42 |
| 5 | 3 | 3, 4, 5, 6, 20 |
| 6 | 3 | 3, 4, 5, 6, 30, 60 |
| 7 | 3 | 3, 4, 5, 7, 30, 42, 60 |
| 8 | 4 | 4, 5, 6, 7, 8, 15, 40, 42 |
| 9 | 4 | 4, 5, 6, 7, 8, 20, 40, 42, 60 |
| 10 | 5 | 5, 6, 7, 8, 9, 10, 12, 40, 42, 45 |
| 11 | 6 | 6, 7, 8, 9, 10, 12, 14, 15, 18, 24, 28 |
| 12 | 6 | 6, 7, 8, 9, 10, 11, 12, 18, 22, 33, 40, 42 |

These upper bounds cover unbounded denominators. The displayed witness sets do
not limit their quantifiers. For example, the recursive certificate rules out
minimum at least four for seven terms, although the simple harmonic envelope
does not rule it out.

### Modular obstructions and sharp thresholds

[UnitFractionPrimes.lean](UnitFractionPrimes.lean) concerns a related problem
where a maximum denominator is explicitly bounded. Partition a representation
according to divisibility by a prime `p`. Clearing denominators forces `p` to
divide the weighted numerator of the divisible part. For a common multiple `L`
of `1,...,T`, an exact Boolean certificate checks every nonempty subset `C` of
that range for nondivisibility of `sum(L/j, j in C)` by `p`.

`prime_exclusion_by_certificate` proves that a successful certificate excludes
**every multiple of `p`** in any representation whose denominators are all
strictly less than `p(T+1)`. It does not require `p` itself to be the minimum or
maximum. The coarse harmonic-weight criterion is also proved separately.

Let `AdmitsPrimeDivisor p N` mean that a finite set of distinct positive
denominators at most `N`, summing reciprocally to one, contains a multiple of `p`.
The general `first_prime_threshold_of_certificate` rule combines the universal
exclusion with an attaining witness. Two unconditional `IsLeast` theorems prove:

| Prime | Least admissible maximum bound | Attaining set |
| --- | --- | --- |
| 7 | 28 | 2, 4, 7, 14, 28 |
| 17 | 85 | 2, 3, 15, 17, 34, 85 |

Consequently no such representation bounded by 27 can contain a multiple of 7,
and none bounded by 84 can contain a multiple of 17. Both thresholds are attained.
The modular certificates succeed below the respective coarse harmonic weights
11 and 25. These bounded-denominator results support the unit-fraction proof
library; they do not replace the uncapped optimizer or the missing asymptotic
construction.

## Attribution and review request

Source catalog entry:
[JSP-000242 at the reviewed revision](https://github.com/TheJustinSunPrize/awards/blob/f4e7173d89dfe91022a185427d63452c8ffbf6ae/problems/catalog-0201-0300.md#JSP-000242).
The problem family is due to Erdős and Graham. The catalog cites E. S. Croot III,
*On unit fractions with denominators in short intervals*, Acta Arithmetica 99
(2001), 99–114, [DOI](https://doi.org/10.4064/aa99-2-1),
[author's preprint](https://arxiv.org/abs/math/9904181).
The cited paper's constructive short-interval theorem is outside this package's
proved scope. Classical optimization, splitting, logarithmic estimates, and
prime-denominator arguments retain their mathematical attribution.

The prime obstruction overlaps in method with earlier formalizations, especially
[PR #303](https://github.com/TheJustinSunPrize/awards/pull/303) and
[PR #354](https://github.com/TheJustinSunPrize/awards/pull/354).
[Duplicate screening](DUPLICATE-SEARCH.md) distinguishes their predicates and
bounds, and records exact inspected revisions. No global first-formalization
priority or mathematical novelty is asserted.

Public submitter: `procaross`. Proposed formalizer recipient placeholder:
`RECIPIENT-JSP-000242-PROCAROSS-A`; confirmation is pending. This implementation
and documentation were prepared with OpenAI ChatGPT/Codex assistance.

Please assess correspondence, usefulness, attribution, overlap, and eligibility
of this scoped formalization, including whether the added general results qualify
as partial progress under the [published rules](https://www.hejustinsun.com/zh/prize/rules).
No candidate, catalog, decision, recipient-confirmation, or payment record is
created or changed. This is a submission for review, not a tier assignment or an
assertion of payment entitlement.

## Reproduction and evidence

The package pins Lean 4.34.0, Mathlib, and all transitive Git dependencies.
The four default Lake targets are the four proof modules. Python 3.10 or later,
Git, and the pinned Lean toolchain are required.

From this directory, with Elan installed:

```sh
export MATHLIB_NO_CACHE_ON_UPDATE=1
export LEAN_NUM_THREADS=1
lake exe cache get Mathlib.Data.Finset.Sort Mathlib.Data.Rat.Floor \
  Mathlib.Algebra.BigOperators.Group.List.Basic \
  Mathlib.Algebra.BigOperators.Group.Finset.Basic \
  Mathlib.Order.Interval.Finset.Nat Mathlib.Tactic.NormNum Mathlib.Tactic.Linarith \
  Mathlib.Data.Finset.Max Mathlib.Analysis.SpecialFunctions.Log.Deriv \
  Mathlib.Data.Nat.Prime.Basic Mathlib.Data.Nat.Cast.Field \
  Mathlib.Algebra.BigOperators.Group.Finset.Piecewise \
  Mathlib.Algebra.BigOperators.Ring.Finset \
  Mathlib.Algebra.Order.BigOperators.Group.Finset Mathlib.Data.Finset.Powerset
lake build
python3 verify.py
```

`verify.py` checks proof and configuration hashes, compiles with
`autoImplicit=false` and warnings treated as errors, audits 39 selected theorem
axiom dependencies, and replays all four modules with bundled `leanchecker`.
It checks four valid imported certificates and requires two deliberately false
certificates to fail in the same environment. This default run does not invoke
Nanoda; see [EXTERNAL-VERIFICATION.md](EXTERNAL-VERIFICATION.md) for the optional
independent implementation and its pinned build instructions.

[ARTIFACTS.json](ARTIFACTS.json) lists the checksum and size of every other
public package file. The [recorded local report](verification/local/verification.json) and its compact
logs bind the source, objects, tools, exports, and positive/negative controls.
The recorded local environment used exact-revision archive dependencies, rather
than claiming a fresh network bootstrap. No GitHub Actions proof job is added.
Repository CI validates records and references; it does not run these proofs.

Bundled `leanchecker` uses Lean's own kernel and trusts imported declarations.
The separately implemented Rust checker rechecks the exported dependency closure,
including the reached Lean and Mathlib declarations, while retaining the three
foundational axioms. It still depends on the exporter, compilers, hardware, and
axioms. These are contributor-run checks on one host, not independent human review,
network-isolated organizer verification, or a prize decision.

Source licensing: [Apache 2.0](LICENSE). Dependencies retain their original
licenses and attribution. Generated objects, caches, and full exports are not
committed to this source package.
