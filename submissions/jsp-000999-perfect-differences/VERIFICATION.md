# Verification record

Environment: Lean 4.34.0, Mathlib `5ed2965256430c3649e86755f9576b54eca72435`. The environment checker verified all nine dependency revisions against the lockfile and confirmed their tracked sources were unmodified. Compiled dependency caches were used; the whole dependency tree was not rebuilt from source.

The main module has **554 lines and 36 named theorems**. Its initial build completed without warnings, followed by the reproducible verification run. Every named theorem's axiom closure was inspected and contains only `propext`, `Classical.choice`, and `Quot.sound`. The source has no unfinished declarations, problem-specific axioms, `native_decide`, `Lean.ofReduceBool`, or unsafe proof escapes. Concrete finite controls in `Evaluation.lean` use `decide +kernel`.

`lake env leanchecker --fresh --verbose PerfectDifference` completed successfully in **65.465 seconds**, replaying imported declarations and the target module through Lean's official kernel. This is not an independently implemented kernel or organizer-designated verification.

Supplemental exact checks:

- All **512** subsets of `{1,...,9}`: sum-based Sidon tests agree with independently enumerated positive-difference multiplicities; **140** are Sidon seeds.
- Those 140 seeds and five additional seed chains: **1,305** finite stages verified for positivity, seed retention, nesting, cardinality, uniqueness of all positive differences, coverage and both explicit growth bounds. Additional cases include `{1,2,4,8}`, a translated seed and a large singleton.
- **9,949** nonforbidden prescribed-pair insertions verified directly by sum and difference enumeration.
- Negative controls reject `{1,2,3}`, an already-present prescribed difference, and a forbidden insertion.
- Four Lean executable outputs exactly match the Python construction: seven empty-seed stages with their next missing differences, and six `{1,2,4,8}` stages with their next missing differences.
- Formal finite controls include the exact difference set of `{1,2,4,8}`, its missing difference 5, its Sidon property, rejection of `{1,2,3}`, and a theorem instance completing `{1,2,4,8}` to a perfect set.

These finite computations check the executable definitions and statement interpretation, not the universally quantified proofs. The Python program is not formally verified. The deliberately loose bound is checked as stated and must not be described as a sharp exponent result.

Commands, elapsed times, input hashes and full logs are in `verification/verification.json` and the adjacent files. `SHA256SUMS` covers all public package files except itself. Repository-level checks are separately recorded in `verification/repository-checks.json`; they verify repository policy and data consistency, not mathematical truth or award eligibility.
