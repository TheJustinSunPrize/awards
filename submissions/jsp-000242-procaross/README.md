# JSP-000242: complete optimal-minimum asymptotic for unit fractions

This package proves the asymptotic answer to the **uncapped-denominator**
optimization problem in JSP-000242:

```text
B(k)/k → 1/(e - 1) as k → infinity.
```

Here `B(k)` is proved to be the attained, globally greatest possible minimum
denominator in a representation of one by exactly `k` distinct positive unit
fractions, for every `k ≥ 3`. The matching lower bound and full convergence are
proved in [UnitFractionLimit.lean](UnitFractionLimit.lean). No conjecture or
short-interval construction is assumed. This is a formalization of classical
mathematics, with AI assistance disclosed; no new mathematical theorem or global
first-formalization priority is claimed.

The proof uses a harmonic prefix, the classical factorial remainder method,
Chebyshev's bound on the least common multiple, and a proved padding operation.
It does **not** prove the stronger assertion that every denominator can be kept
in the same short interval, nor the shortest-span problem JSP-000243.

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

### Complete convergence theorem

The exact Lean conclusion is:

```lean
Filter.Tendsto (fun k : ℕ => (optimalMinimum k : ℝ) / k) Filter.atTop
  (nhds (1 / (Real.exp 1 - 1)))
```

`optimalMinimum_eventual_lower` and `optimalMinimum_eventual_upper` separately
provide both quantified epsilon inequalities for **all** sufficiently large `k`.
The definition and attained optimality theorem above connect this limit to the
original extremal problem. There is no maximum-denominator cutoff.

The new construction is organized into three independently compiled modules:

1. [UnitFractionRemainder.lean](UnitFractionRemainder.lean) proves duplicate
   removal without increasing length, then a factorial expansion bound: for
   `0 ≤ a < b ≤ n!`, the fraction `a/b` has a representation by at most `2n`
   distinct positive unit fractions. The duplicate-removal proof uses
   well-founded shortlex descent; it does not rely on a heuristic termination
   claim or a search cutoff.
2. [UnitFractionCompletion.lean](UnitFractionCompletion.lean) completes a
   harmonic prefix with such a short tail. Each denominator of a positive
   representation is bounded below by the reciprocal of its total sum, so the
   small remainder forces every added denominator beyond the prefix. Denominator
   divisibility is tracked through every subtraction. Chebyshev's bound, already
   proved in pinned Mathlib, and an elementary factorial bound show that for
   every fixed `D`, `lcm(1,...,D*t) ≤ t!` for all sufficiently large `t`.
3. [UnitFractionLimit.lean](UnitFractionLimit.lean) proves that, for positive `q`
   and `(e-1)q < p`, `B((p+2)t) ≥ qt` for all sufficiently large `t`. Monotonic
   padding covers the intervening cardinalities, with an explicit `q/k`
   rounding error. Taking arbitrarily large `q` and `p = floor((e-1)q)+1`
   gives the matching lower constant; the proved upper bound finishes the limit.

[MATHEMATICAL-PROOF.md](MATHEMATICAL-PROOF.md) gives a review-oriented derivation
and maps each step to its formal declaration. This construction allows very
large tail denominators. It establishes the minimum-denominator asymptotic,
not Croot's stronger short-interval theorem.

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
The matching lower bound is supplied separately by the construction above.

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
library; they are ancillary to the uncapped optimizer and complete asymptotic proof.

## Attribution and review request

Source catalog entry:
[JSP-000242 at the reviewed revision](https://github.com/TheJustinSunPrize/awards/blob/f4e7173d89dfe91022a185427d63452c8ffbf6ae/problems/catalog-0201-0300.md#JSP-000242).
The problem family is due to Erdős and Graham. The catalog cites E. S. Croot III,
*On unit fractions with denominators in short intervals*, Acta Arithmetica 99
(2001), 99–114, [DOI](https://doi.org/10.4064/aa99-2-1),
[author's preprint](https://arxiv.org/abs/math/9904181).
The paper's stronger short-interval theorem is outside this package's proved
scope. The minimum-denominator asymptotic is proved here by a different classical
route. The factorial method is attributed to P. Erdős, *Az 1/x₁ + 1/x₂ + … +
1/xₙ = a/b egyenlet egész számú megoldásairól*, Mat. Lapok 1 (1950), 192–210
([original article](https://www.renyi.hu/~p_erdos/1950-02.pdf), Theorem 1 and its
factorial construction). Duplicate elimination follows the classical
Takenouchi-style idea; the implementation gives a direct shortlex proof.
Optimization, splitting, logarithmic estimates, and prime-denominator arguments
retain their classical attribution.

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
of the complete minimum-denominator asymptotic formalization under the [published rules](https://www.hejustinsun.com/zh/prize/rules).
No candidate, catalog, decision, recipient-confirmation, or payment record is
created or changed. This is a submission for review, not a tier assignment or an
assertion of payment entitlement.

## Reproduction and evidence

The package pins Lean 4.34.0, Mathlib, and all transitive Git dependencies.
The seven default Lake targets are the seven proof modules. Python 3.10 or later,
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
  Mathlib.Algebra.Order.BigOperators.Group.Finset Mathlib.Data.Finset.Powerset \
  Mathlib.Data.List.Shortlex Mathlib.Data.Nat.Factorial.Basic Mathlib.NumberTheory.Chebyshev
lake build
python3 verify.py
```

`verify.py` checks proof and configuration hashes, compiles with
`autoImplicit=false` and warnings treated as errors, audits 51 selected theorem
axiom dependencies, and replays all seven modules with bundled `leanchecker`.
It checks the limit theorem through a separate import and four valid finite
certificates, and requires two deliberately false certificates to fail in the same environment. This default run does not invoke
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
