# JSP-000641 / Erdős #781: a finite disproof of the exact quadratic threshold

This AI-assisted submission supplies a concrete two-coloring of **[1,133]** with no monochromatic descending wave of length **12**. Since 12² − 12 + 1 = 133, it disproves the proposed universal exact threshold f(k) = k² − k + 1. Equivalently, the least forcing threshold, if denoted f, satisfies f(12) ≥ 134. It does not claim f(12) = 134 or a minimum counterexample parameter.

The failure of the quadratic formula was already established by Alon and Spencer's stronger cubic lower bound. This package is a finite, independently checkable witness to that known negative conclusion, with no claim of new discovery or first formalization. It does **not** formalize the full asymptotic result f(k) = Θ(k³).

Related submission: [Issue #29](https://github.com/TheJustinSunPrize/awards/issues/29) registers an existing cubic-bound formalization by plby, with upstream attribution to Codex / GPT-5.6 Sol and the Formal Conjectures Authors. Its [pinned source](https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos781.lean) derives the quadratic contradiction at k = 2^50. This submission supplies a separate explicit certificate at k = 12, using only Std. It is supplemental finite evidence, not a competing first-proof claim or a replacement for that stronger asymptotic result. The linked third-party source is not incorporated into this package or reverified here.

## Explicit coloring

Start with color 0, then alternate colors across consecutive blocks with lengths

```text
11, 1, 3, 10, 9, 9, 9, 9, 8, 8, 7, 7,
6, 6, 5, 5, 4, 4, 3, 3, 2, 2, 1, 1
```

These lengths sum to 133. [coloring.json](coloring.json) records all 133 bits; bit i−1 is the color of integer i. No value outside [1,133] is relevant.

A descending wave is a strictly increasing list x₁,…,xₘ whose successive gaps do not increase. In the Lean definition this is expressed without division or truncated subtraction: for every three adjacent entries a,b,c, we require a < b and c+a ≤ b+b, together with the recursive condition on the tail; a two-entry list requires a < b. Monochromatic means every entry has the same Boolean color. Interval membership is stated explicitly for every entry.

## Formal proof

[DescendingWaves.lean](DescendingWaves.lean) is standalone, importing only Lean's bundled `Std`. Its main declarations in namespace `DescendingWaves` are:

- `rank_bounds_length` and `certificate_bounds_all`: the general certificate soundness proof.
- `witness_certificate`: the complete finite certificate for this coloring.
- `witness_no_twelve`: every monochromatic descending wave in [1,133] has length at most 11.
- `not_forces_133_12`: the interval [1,133] does not force a 12-term monochromatic descending wave.
- `quadratic_threshold_false`: the proposed quadratic interval does not force a k-term wave for every positive k.

The certificate assigns a natural-number rank R(a,b) to each relevant same-colored increasing pair. Lean verifies 2 ≤ R(a,b) ≤ 11 and

```text
R(b,c) + 1 ≤ R(a,b)
```

whenever a < b < c, c+a ≤ 2b, and all three colors agree. A list-induction theorem then bounds every possible monochromatic descending wave by the rank of its first pair. This covers arbitrary lists, not merely waves enumerated by a search script.

The rank lookup is generated arithmetic data. A Boolean checker enumerates same-colored pairs and only the allowable interval of third entries; `checked_pair` and `checked_step` prove its soundness. Every row is checked with `decide +kernel`; the generic theorem connects those checks to the mathematical statement. Search results, external solvers, and the Python script are not trusted proof oracles. No `native_decide`, `sorry`, admitted proof, or new mathematical axiom is used.

`ForcesWave n k` universally quantifies over Boolean colorings and asks for an in-range monochromatic descending wave with exactly k entries. Refuting `ForcesWave 133 12` suffices to refute the conjectured exact formula, without defining the minimum threshold or assuming an existence theorem for it. No mathlib adapter is needed to express this discrete integer statement; it uses a bespoke list representation documented above.

## Reproduce

Use **Lean 4.24.0**, as pinned in [lean-toolchain](lean-toolchain):

```sh
./verify.sh
python3 independent_check.py
```

An explicit binary can be selected with `LEAN_BIN=/absolute/path/to/lean ./verify.sh`. The complete local kernel check took about 54 seconds on the development machine; time and memory usage vary. It uses more memory than the independent Python check.

[verification.log](verification.log) contains the local compiler result and main theorem axiom reports. [independent_check.py](independent_check.py) uses a forward dynamic program, distinct from the backward certificate construction, and reports maximum length 11 in [finite-checks.json](finite-checks.json). The list 1,…,11 itself witnesses that length. This script is supplementary; the universal no-wave conclusion comes from Lean.

[SHA256SUMS](SHA256SUMS) and [artifact-manifest.json](artifact-manifest.json) supply file hashes and byte counts. Public GitHub commit pinning is not asserted to be an independent archival service or independent mathematical review.

## Sources, attribution, and scope of submission

- [Erdős problem 781](https://www.erdosproblems.com/781), whose exact quadratic conjecture is the target of this counterexample.
- [JSP-000641 catalog entry at the submission base](https://github.com/TheJustinSunPrize/awards/blob/f4e7173d89dfe91022a185427d63452c8ffbf6ae/problems/catalog-0601-0700.md#JSP-000641).
- T. C. Brown, P. Erdős, and A. R. Freedman, *Quasi-progressions and descending waves*, J. Combin. Theory Ser. A 53 (1990), 81–95, for the question and earlier bounds, as cited by the catalog.
- N. Alon and J. Spencer, [Ascending waves](https://doi.org/10.1016/0097-3165(89)90033-2), J. Combin. Theory Ser. A 52 (1989), 275–287, for the known asymptotic resolution. Reflection exchanges ascending and descending waves.

The submitter is the GitHub account opening the PR. Codex assisted with selecting the problem, heuristic witness search, formal proof, and validation. This is a self-submission for review. Neither discovery priority nor sole manual authorship is asserted. No award, recipient identity confirmation, eligibility change, or independent-review status is asserted; the catalog's status fields are unchanged. The proposed submission directory is subject to maintainer guidance.

Code follows the repository's Apache-2.0 license; documentation and data follow its LICENSE-CONTENT.
