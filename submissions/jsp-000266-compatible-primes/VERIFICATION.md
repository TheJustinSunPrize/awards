# Verification record

Environment: Lean 4.34.0, Mathlib `5ed2965256430c3649e86755f9576b54eca72435`. The environment script checked all nine manifest dependency revisions and confirmed their tracked sources were unmodified. Dependency compiled caches were used; a full from-source rebuild of all dependencies was not performed.

The main module has 396 lines and 26 named theorems. A clean initial build completed without warnings. The reproducible verification script subsequently rebuilt it, audited all 26 theorem closures and checked the executable outputs. All closures contain only `propext`, `Classical.choice`, `Quot.sound`. There are no unfinished declarations, problem-specific axioms, `native_decide`, `Lean.ofReduceBool`, or unsafe proof escapes in this module. Concrete finite proof terms use `decide +kernel`.

`lake env leanchecker --fresh --verbose ReciprocalDoubling` completed with exit code 0 in **72.512 seconds**. It replays imported declarations and the target module through Lean's official kernel. This is not a separately implemented kernel such as Nanoda, nor verification designated by the organizers.

Exact supplementary checks:

- Rational set dynamic programming and independently implemented LCM-scaled integer bitsets agree for every `S(N)`, `0≤N≤16`.
- Signed-sum enumeration agrees with pairwise differences of subset sums for `0≤m≤8`.
- Exact doubling is equivalent to the signed obstruction for `1≤m≤12`; the finite counting lower bound is checked over that range.
- 51 compatible-prime/exponent cases whose final index is at most 16 satisfy exact doubling.
- The four Lean outputs (11 counts, 10 irreducibility tests, 8 numerator cutoffs and an 8-by-11 compatibility matrix) exactly match Python's rational computations.
- Formal positive controls `(4,2)` and `(4,23)` support arbitrary-exponent theorem instances. The formal negative control `(4,3)` is incompatible; the Python check additionally confirms that index 12 does not double.

Finite computations are checks on statements and executable definitions, not substitutes for the universally quantified proof. Python is not formally verified. The finite tests are exponentially expensive and should not be represented as a scalable solver.

The package's input hashes and commands are in `verification/verification.json`; complete logs are retained. `SHA256SUMS` covers public package files except itself. Repository-level checks are separately recorded in `verification/repository-checks.json`; they validate repository data and policy, not mathematical truth or award eligibility.
