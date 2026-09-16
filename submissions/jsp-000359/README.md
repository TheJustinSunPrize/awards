# JSP-000359 / Erdős 440: the square-root counting bound only

This is an AI-assisted Lean formalization of a known bound, submitted as
**partial coverage of the original problem**. It proves the first question,
not the sharp liminf statement or the optimal pointwise constant. It makes
no claim of a new mathematical solution, first formalization, or prize eligibility.

## Statement and scope

Let `a : ℕ → ℕ` be any strictly increasing sequence of positive integers.
For a natural threshold `x`, let `A(x)` count indices `i` for which
`Nat.lcm (a i) (a (i + 1)) ≤ x`. The file proves

```
A(x) ≤ t + x / (t + 1)       for every natural t
A(x) ≤ 2 * Nat.sqrt x       for every natural x
```

Here `/` is natural-number division and `Nat.sqrt` is the integer square root.
There is no eventual-size assumption and the bound also holds at zero.
`mem_goodIndices_iff` proves that the finite definition counts **all** qualifying
indices, so the theorem is not just a bound for an arbitrary truncated prefix.

The original question uses a real threshold. Since LCM values are integers,
its count at a nonnegative real `x` equals its count at `floor x`. Thus the
natural-threshold theorem yields the mathematical `O(sqrt x)` assertion.
The real-floor conversion and big-O notation are not separately encoded here;
the machine-checked statement is the exact natural-number inequality above.

**Not established by this file:** the optimal value of
`liminf A(x) / sqrt(x)` (known to be 1), its attainment, and the optimal
pointwise asymptotic constant (about 1.86). Reviewers should not mark the
whole JSP entry as fully formalized on the basis of this file.

## Argument

For positive integers `a < b` with `lcm(a,b) ≤ x`, one has
`floor(x/b) < floor(x/a)`. To see this, put `d = gcd(a,b)` and
`q = floor(x/b)`. Since `lcm(a,b)/b = a/d`, one has `dq ≥ a`.
Also `d` divides the positive difference `b-a`, so `d ≤ b-a`. Consequently
`bq ≥ a(q+1)` and `bq ≤ x`, proving the quotient drop.

Along the sequence, the quotients are nonincreasing, and each qualifying
index gives a strict drop. Split those indices according to `a(i) ≤ t`.
There are at most `t` indices in this part by strict increase. In the other
part, the distinct positive quotients `floor(x/a(i))` all lie between 1 and
`floor(x/(t+1))`. Add the bounds and choose `t = floor(sqrt(x))`.

## Provenance

- [Official JSP-000359 catalog](https://github.com/TheJustinSunPrize/awards/blob/f4e7173d89dfe91022a185427d63452c8ffbf6ae/problems/catalog-0301-0400.md#JSP-000359).
- [Erdős problem 440, complete statement and historical results](https://www.erdosproblems.com/440).
- [Discussion and Tao's 2025 elementary upper-bound argument](https://www.erdosproblems.com/forum/thread/440).

The upper bound is historical mathematical work. The source attributes the
stronger results to Erdős and Szemerédi (1980); Tao's comment gives an elementary
dyadic proof of the order bound. This file uses the integer-quotient counting
argument described above. Its novelty relative to all literature is not asserted.
The Lean source was written with Codex assistance, rather than copied from a
prior problem-specific Lean file. Mathlib dependencies retain their own licenses.
Code in this submission follows the parent repository's MIT license.

On 2026-09-16, a scan of all 33 then-visible official issues/PRs, the original
discussion, web searches and two GitHub code-name searches did not identify a
submission for JSP-000359. This limited search cannot certify global priority.

## Reproduction

Install the toolchain specified by `lean-toolchain`. From this directory:

```sh
lake exe cache get Mathlib/Data/Nat/GCD/Basic.lean Mathlib/Data/Nat/Sqrt.lean Mathlib/Data/Finset/Card.lean Mathlib/Order/Interval/Finset/Nat.lean Mathlib/Tactic/Linarith.lean
lake build
lake env lean --trust=0 LcmCounting.lean
```

`python verify.py` reruns these build/kernel checks and verifies the axiom reports,
then writes SHA-256 records under `verification/`. Python 3.10 or later is required.
The directory's `.gitattributes` preserves LF line endings so checkout does not
invalidate the recorded file hashes.

The committed manifest pins mathlib to
`c44e0c8ee63ca166450922a373c7409c5d26b00b` and pins transitive dependencies.
The local validation reused those pinned dependency checkouts and their compiled
cache; it was not a clean network-isolated build.

The final theorem axiom reports contain only `propext`, `Classical.choice`,
and `Quot.sound`. No `sorry`, `admit`, custom axioms, or `native_decide` are used.
`--trust=0` uses the same Lean implementation; it is not an independent checker.
Official statement-fidelity review, independent checking and any prize decision
remain pending. No candidate, award or eligibility record is changed by this submission.
