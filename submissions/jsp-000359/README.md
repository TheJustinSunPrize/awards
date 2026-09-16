# JSP-000359 / Erdős 440: an independent Lean 4.19 proof

This AI-assisted package formalizes both questions in the original problem:
the square-root order bound and the greatest attainable normalized lower limit.
It includes the real-threshold counting bridge and standard `Filter.liminf`.
The mathematics is historical work of Erdős and Szemerédi (1980).
No mathematical discovery, first-formalization priority, or prize eligibility
is asserted.

## Exact scope

Let `a : ℕ → ℕ` be strictly increasing with `0 < a i` for every index.
This represents the original enumeration of an infinite set of positive
integers; using index zero instead of index one does not add a zero-valued term.
For real `x ≥ 0`, let `A(x)` count **all** indices `i` such that
`lcm(a(i), a(i+1)) ≤ x`.

`JSP000359.original_problem` proves the conjunction:

1. For every such sequence and every real `x ≥ 0`, `A(x) ≤ 2 * sqrt(x)`.
   This explicit global bound implies the requested `A(x) = O(sqrt(x))`.
2. The set of attainable values of `liminf_(x→∞) A(x)/sqrt(x)` has greatest
   element exactly **1**. The sequence `a(i)=i+1` attains 1; in fact its
   normalized count converges to 1.

The finite counting implementation is not a truncation of the mathematical
problem: `mem_goodIndices_iff` proves that every qualifying index is included,
and `mem_real_count_iff` verifies the real-floor threshold conversion.
`normalized_count_bounded` proves that each normalized counting function takes
values in `[0,2]`; the real-valued liminf does not rely on an empty or unbounded
conditional infimum. Division at zero is immaterial to the limit at infinity.

The sharper pointwise limsup constant (about 1.86) and its extremal construction
appear in the historical discussion but are not among the two questions in the
original displayed statement. They are not proved by this package. The existing
formalization linked below includes them.

## Proof outline

For positive integers `u < v` with `lcm(u,v) ≤ x`, integer quotients satisfy
`floor(x/v) < floor(x/u)`. Split qualifying indices according to `a(i) ≤ t`.
There are at most `t` in the first part. In the second, the distinct positive
quotients lie in `[1, floor(x/(t+1))]`. Thus
`A(x) ≤ t + floor(x/(t+1))`; choose `t = floor(sqrt(x))`.

For the lower limit, write `L_i=lcm(a(i),a(i+1))`. Since the gcd divides the
positive difference, `1/L_i ≤ 1/a(i) - 1/a(i+1)`. For any finite set `S` of
indices at least `n`, telescoping gives `sum_(i in S) 1/L_i ≤ 1/(n+1)`.

Suppose `A(k^2)>k` for all sufficiently large integers `k`. Choose a positive
`n` above that cutoff. Greedily select `m` distinct indices at least `n`, the
`j`th with `L_i ≤ (n+j)^2`: at each step the counting assumption supplies more
indices than the initial `n` indices and the `j` previously selected ones.
Their reciprocal sum is at least
`sum_(0≤j<m) 1/(n+j)^2 ≥ 1/n - 1/(n+m)`.
Taking `m=n^2+1` contradicts the upper bound `1/(n+1)`. Hence arbitrarily large
square thresholds have `A(k^2) ≤ k`, and every normalized liminf is at most 1.

For `a(i)=i+1`, coprimality gives `L_i=(i+1)(i+2)`. Its natural-threshold count
lies between `Nat.sqrt x - 1` and `Nat.sqrt x`. The real-threshold bridge gives
`sqrt(x)-2 ≤ A(x) ≤ sqrt(x)`, so the normalized count converges to 1.

## Sources, prior work and attribution

- [Official catalog at the review base](https://github.com/TheJustinSunPrize/awards/blob/f4e7173d89dfe91022a185427d63452c8ffbf6ae/problems/catalog-0301-0400.md#JSP-000359).
- [Original displayed questions and historical results](https://www.erdosproblems.com/440).
- [Discussion, including Tao's elementary order-bound argument](https://www.erdosproblems.com/forum/thread/440).
- [Existing-proof registration, Issue #22, Supplement 2](https://github.com/TheJustinSunPrize/awards/issues/22).
- [Pinned prior Lean theorem by plby/lean-proofs](https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos440.lean).

The final priority check found Issue #22's supplement and the pinned prior
formalization, whose main theorem includes five natural-threshold conclusions,
including the sharp limsup. Therefore this is explicitly an **additional,
independent reproduction**, with a real-threshold bridge; it is not a first-proof
registration or a stronger mathematical result. The earlier limited search did
not establish absence of other work. No global novelty is claimed for the bridge.

The source files here were written with Codex assistance. The prior main file
was inspected to compare scope after these proofs had passed local checking;
it was not copied into this package. Its attribution includes Erdős, Szemerédi,
Tao, van Doorn, and Codex / GPT-5.6 Sol for the formalization. The independent
mathematical routes described here are not asserted to be new.
Code in this submission follows the parent repository's MIT license. Mathlib
dependencies retain their own licenses.

## Reproduction and verification limits

Install `leanprover/lean4:v4.19.0`. The committed manifest pins mathlib to
`c44e0c8ee63ca166450922a373c7409c5d26b00b` and pins transitive dependencies.
From this directory:

```sh
lake exe cache get Mathlib/Data/Nat/GCD/Basic.lean Mathlib/Data/Nat/Sqrt.lean Mathlib/Data/Finset/Card.lean Mathlib/Order/Interval/Finset/Nat.lean Mathlib/Tactic/Linarith.lean
lake exe cache get Mathlib/Data/Real/Sqrt.lean Mathlib/Algebra/BigOperators/Intervals.lean Mathlib/Tactic/FieldSimp.lean Mathlib/Tactic/Positivity.lean Mathlib/Topology/Algebra/Order/LiminfLimsup.lean Mathlib/Analysis/SpecificLimits/Basic.lean
python verify.py
```

Python 3.10 or later is required. The verifier runs `lake build`, rechecks both
source modules using `lake env lean --trust=0`, audits the final theorem reports,
and writes SHA-256 evidence. `.gitattributes` preserves LF line endings.

All audited theorem footprints contain only `propext`, `Classical.choice`, and
`Quot.sound`. No placeholder proof, custom axiom, `native_decide`, or unsafe
proof code is used. The verification record lists actual commands and outcomes.
The local run reused pinned dependency checkouts and compiled caches. It was
not network isolated, and the same Lean implementation is not an independently
implemented checker. Official statement-fidelity review and independent
verification remain pending.

This package changes no catalog eligibility, recipient, candidate, or award
record. Whether an additional reproduction is useful for intake or eligible for
any recognition is for the maintainers and prize reviewers to decide.
