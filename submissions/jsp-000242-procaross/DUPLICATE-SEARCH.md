# Duplicate screening and attribution boundaries

Snapshot: `2026-09-17T07:20:31.202155+00:00`. All recorded GitHub searches completed successfully.
The machine-readable query counts and public result links are in
[dedup-summary.json](dedup-summary.json).

## Searches

GitHub issue/PR searches covered all states in `TheJustinSunPrize/awards`, with
up to 100 results per query. Queries were `JSP-000242`, `"smallest denominator"`,
`"unit fractions"`, `"Croot"`, and `"Egyptian"`. The first query returned no
matching issue or PR at this snapshot. The phrase query returned PR #354,
which concerns a different parameter.

Global GitHub code searches with `language:Lean` for `JSP-000242` and
`"smallest denominator"` returned no results. `Egyptian` returned eight indexed
files, including several nonmathematical uses of the word. The broad `Croot`
code query hit the 100-result limit, largely through identifier matches; it
does not support an absence claim.

The pinned Mathlib number-theory and combinatorics directories were also searched
for `Egyptian`, `unit fractions`, and `unitFraction`, with no matching source text.
This is a text search of those directories, not a semantic inventory of Mathlib.

## Nearby submissions reviewed

| Source | Scope relevant to overlap screening |
| --- | --- |
| [PR #93](https://github.com/TheJustinSunPrize/awards/pull/93) | JSP-000248: possible largest denominators, impossibility with largest denominator at most 5, and individual witnesses. It includes the classical set `{2,3,6}`, which is also our three-term witness. |
| [PR #354](https://github.com/TheJustinSunPrize/awards/pull/354) | JSP-000250: the least unobtainable smallest denominator when every denominator is bounded by `N`, with an asymptotic `O(N/log N)` upper bound. |
| [Issue #213](https://github.com/TheJustinSunPrize/awards/issues/213) | JSP-000241: representations involving polynomial values and unit-fraction denominators. |
| [PR #303](https://github.com/TheJustinSunPrize/awards/pull/303) | JSP-000248: small-multiple obstructions for the largest denominator. |
| [PR #271](https://github.com/TheJustinSunPrize/awards/pull/271) | JSP-000251: a lower bound on the number of terms needed to pass a specified denominator threshold. |
| [PR #206](https://github.com/TheJustinSunPrize/awards/pull/206) | JSP-000257: one rational-target instance of a different statement. |

The proposed package contributes the general fixed-cardinality decision
procedure and exact optima for `3 <= k <= 12`. Individual classical witness
identities, including `{2,3,6}`, are not claimed as novel or previously unformalized.

## Public Lean files inspected

The [Egyptian121 exercise](https://github.com/math-market/practice-problems/blob/8990a84ee67f25f4847a8895119229eed6f0fa57/lean/Egyptian121.lean)
states a three-term representation of `5/121` and has a placeholder proof in the
inspected revision. It provides a concrete witness predicate, rather than the
fixed-cardinality equivalence and optimal-minimum results submitted here.

Two files in `beetree/math_erdos_289` were read at revision
`7a520bded78b26629850cbfc152c4c832437702f`:
[PrimePowerLCMTelescope.lean](https://github.com/beetree/math_erdos_289/blob/7a520bded78b26629850cbfc152c4c832437702f/SolveMath/Corpus/NumberTheory/ReciprocalSumLiuSawhneySupport/PrimePowerLCMTelescope.lean)
and [SmoothPrimePowerFactorization.lean](https://github.com/beetree/math_erdos_289/blob/7a520bded78b26629850cbfc152c4c832437702f/SolveMath/Corpus/NumberTheory/ReciprocalSumLiuSawhneySupport/SmoothPrimePowerFactorization.lean).
Their headers and declarations concern prime-power denominator elimination,
LCM estimates, and reciprocal sums. No matching fixed-cardinality decision
procedure or this finite-optimum table was identified in that inspection.
Their full dependency tree was not rebuilt or exhaustively audited.

## Conclusion and limitations

No submission matching the proposed combination of decision procedure and ten
exact finite optima was identified in the recorded searches. This supports
requesting overlap review; it does not establish global first-formalization
priority or new mathematics. GitHub indexing can miss recent commits, forks,
alternative names, comments, and unindexed or private repositories. A proof can
exist without any of the searched words. The catalog's `Lean proof: No` field
was not treated as proof that the topic was unformalized.
