# Scope and prior work

Scope checked on 2026-09-17. The deliverable is a complete formalization of
Cohn's known all-noncube strengthening, with all three entries positive,
all three pairs coprime, all three entries 3-powerful, and `a+b=c`.
It does not solve the other higher-power variants of Erdős 939.
Positivity is explicit because the powerful predicate alone can hold at zero.

## Fixed upstream sources

[PR #65](https://github.com/TheJustinSunPrize/awards/pull/65), fixed at
`b5b70857b2d77d6a060e00956beb8e19918b48f9`, proves base infinitude and
explicitly excludes the all-noncube strengthening. At the recorded check
it was open and non-draft, without comments or reviews. These are dated
observations, not promises about its present state.

- [Prize939.lean](https://github.com/inoader/awards/blob/b5b70857b2d77d6a060e00956beb8e19918b48f9/submissions/jsp-000780/Prize939.lean)
- [NOTICE](https://github.com/inoader/awards/blob/b5b70857b2d77d6a060e00956beb8e19918b48f9/submissions/jsp-000780/NOTICE)
- [LICENSE](https://github.com/inoader/awards/blob/b5b70857b2d77d6a060e00956beb8e19918b48f9/submissions/jsp-000780/LICENSE)
- [Formal Conjectures statement](https://github.com/google-deepmind/formal-conjectures/blob/40e7c98697de6f66b8cbdbf641749ab39ed9c152/FormalConjectures/ErdosProblems/939.lean)

All 22 upstream files were read and their downloaded bytes checked against
Git blob hashes. The original proof SHA-256 was
`f556e09410ff1ea3da2d8d38b84a91e068465181ecc42ebe97ce98a8eb4727fc`.
Its toolchain was Lean 4.28.0 and mathlib
`8f9d9cff6bd728b17a24e163c9402775d9e6a365`.
That original toolchain was not independently rebuilt. The local port uses
Lean 4.33.1 and the separately pinned dependencies in this package.

Apache-2.0 attribution to 2026 inoader and the 2025 Formal Conjectures Authors
is preserved. Existing base infinitude is not counted as new work here.
The port adds `norm_num` to one original seed conversion goal; its initial
failed build and subsequent warning records remain in `development/`.

## Seed and new proof

The seed is from Cohn (1998), page 439; the original scan was obtained from
the Leiden mathematics mirror linked in the README after the AMS endpoint
returned 403. The coordinates are:

```text
X = 9712247684771506604963490444281
Y = 32295800804958334401937923416351
Z = 27474621855216870941749052236511
a = 32 * X^3
b = 49 * Y^3
c = 81 * Z^3
```

Exact auxiliary checks covered positivity, the sum, all pairwise gcds,
`3 | abc`, `7 | Y`, and valuations `v2(a)=5`, `v7(b)=5`, `v3(c)=4`.
Their recorded results are in `evidence/source-seed-checks.json`; the
auxiliary script itself is retained locally. Lean does not assume these
results. It uses `a=2^5 X^3`, `b=7^5 (Y/7)^3`, `c=3^4 Z^3`, and excludes
cube coefficients using `3^3<32,49<4^3` and `4^3<81<5^3`.

For `x>y>0`, the upstream recurrence constructs
`A=x(x+2y)^3`, `B=y(2x+y)^3`, `C=(x+y)(x-y)^3`, with `B+C=A` and
`x+y<A`. Its invariant `3 | xy(x+y)` prevents a shared factor 3 in
the relevant linear factors. The new seed satisfies this invariant, so
no unproved normalization step is needed. Each new coordinate is an old
coordinate times a positive cube. `GoodNoncube` preserves the three
noncube conditions, and the finite-maximum contradiction proves infinitude.

## Search scope and limitations

Recorded official issue/PR searches, including closed items, for `939`,
`780`, `JSP-000780`, `Cohn`, `noncube`, and `non-cube` returned respectively
1, 0, 2, 1, 1, and 0 results, all with `incomplete_results=false` and no
missing result pages. Relevant items were base PR #65 and documentation PR #7.

GitHub code searches returned 67 results for `Erdos939 extension:lean`,
47 for `noncube extension:lean`, 6 for `Cohn 939 extension:lean`, and 2
for `noncube powerful extension:lean`; these responses were fully retrieved.
The broader `Cohn extension:lean` query returned 240, of which only the
first 100 were read. Keyword and indexing limits apply even to full responses.

Thirteen directly relevant fixed-source files were inspected, plus one
unrelated importer. No equivalent complete all-noncube infinitude theorem
was found in the inspected sources:

- [lean-genius 939](https://github.com/rjwalters/lean-genius/blob/dc62f771ed5010abfdb04247dff6143e0e69d3e7/proofs/Proofs/Erdos939Problem.lean) defines the triples and mentions Nitaj; other subquestions include axiom placeholders.
- [alphaproof-nexus 939](https://github.com/daedalus/alphaproof-nexus/blob/4e65a6ca81655f090a3c8dcf9f56e4a38c984f4c/problems/erdos/939/Erdos939.lean) and its initial population files are incomplete.
- [Aristotle archive](https://github.com/kavanaghpatrick/aristotle-math-problems/blob/2425339a625bf9e9edef22efee04471db6562bcb/archive/old-submissions/batch_dec14_precise/erdos939_precise.lean) and related files retain placeholders for the triples theorem.
- Other `noncube powerful` matches concerned Erdős 364, not this target.

These are static source checks, not independent compilation of those projects.
Detailed responses and source/blob associations remain in the local research
workspace; `evidence/search-summary.json` gives the shared summary.
No global priority, organizer eligibility, or payment entitlement is claimed.
No new PR, comment, or award application has been published for this work.
