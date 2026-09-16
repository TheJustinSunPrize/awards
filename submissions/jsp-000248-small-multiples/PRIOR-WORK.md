# Prior formalizations and the scope of this extension

Checked **2026-09-16 23:25:49–23:26:34 UTC** using the live GitHub API for
`TheJustinSunPrize/awards`. The review fetched both PR metadata and complete
changed-file lists, then read every changed Lean file at its fixed head commit.
The heads were checked again after reading the files. Both PRs were open and
unmerged; no Lean execution was performed for this comparison.

## PR93: finite certificates

[PR93](https://github.com/TheJustinSunPrize/awards/pull/93), submitted by `vsex7`,
had head **`e3f5144b41c0c41fbc9783d0dcdf54d28045a7bd`** in `vsex7/awards`.
Its only Lean file is
[`submissions/jsp-000248/LargestDenominator.lean`](https://github.com/vsex7/awards/blob/e3f5144b41c0c41fbc9783d0dcdf54d28045a7bd/submissions/jsp-000248/LargestDenominator.lean).
The declarations certify five explicit lists with maxima 6, 12, 18, 20 and 24,
and evaluate the 15 nonempty subsets of `{2,3,4,5}` against common denominator
60. Its list predicate requires denominators at least 2. These are finite
Boolean certificates; the file contains no universally quantified prime-power
or small-multiple obstruction theorem. This comparison uses the actual
declarations, not broader statements in the PR prose.

## PR114: the prime-power obstruction is already public

[PR114](https://github.com/TheJustinSunPrize/awards/pull/114), submitted by
`vibemathing`, had head **`a308b3de8a4cce8eeea492023c52b207b753716e`** in
`vibemathing/awards`. Its two Lean files are
[`candidates/observation/jsp-000248-f03-prime-power-v1/Statement.lean`](https://github.com/vibemathing/awards/blob/a308b3de8a4cce8eeea492023c52b207b753716e/candidates/observation/jsp-000248-f03-prime-power-v1/Statement.lean)
and [`Proof.lean`](https://github.com/vibemathing/awards/blob/a308b3de8a4cce8eeea492023c52b207b753716e/candidates/observation/jsp-000248-f03-prime-power-v1/Proof.lean).
The public theorem `JSP000248.prime_power_not_largest` quantifies over every
prime `p` and positive exponent `a`. Its definition excludes a finite set of
distinct positive denominators whose reciprocal sum is one, which contains
`p^a` and has all members at most `p^a`.

This is mathematically the same prime-power endpoint as the supporting theorem
in our package. We acknowledge that overlap and claim no priority for it.
PR114's held-review description does not remove the public source theorem.
Its other proof declarations are two private valuation helpers; neither Lean
file contains a theorem about arbitrary `m * p^k` or a factorial cutoff. Its
published citation credits AI-assisted formalization by “JSP formalizer f03”.

## The contribution proposed here

`JSP248.small_multiple_prime_power_not_largestDenominator` uniformly excludes
`m * p^k` whenever `0 < m`, `p.Prime`, `m * m.factorial < p`, and `0 < k`.
The case `m = 1` overlaps PR114; the additional scope is the uniform family of
small multiples, including the non-prime-power family `2 * 5^(k+1)`. The proof
handles several denominators divisible by `p^k` by bounding their scaled
integer sum. It is not a renaming or replay of either prior submission.

The predicate allows denominator 1 and requires an attained maximum. The
factorial cutoff is sufficient, with no optimality claim. Mathematical credit
for the elementary prime-power/small-multiple obstruction context remains with
Erdős and Graham, as discussed by Greg Martin in
[*Denser Egyptian fractions*](https://arxiv.org/abs/math/9811112). This is a
partial formalization contribution, not a classification, a proof of density
one, or a formalization of Martin's quantitative exceptional-count theorem.

Repository-wide PR searches across all states for `"JSP-000248"`, and a
supplementary search for `"Erdos292" OR "Erdős 292" OR "largest denominator"`,
returned no additional matching PRs at the check time. This is a dated
source-scope comparison, not a claim of exhaustive global priority, official
verification of the other PRs, or an eligibility/award determination.
