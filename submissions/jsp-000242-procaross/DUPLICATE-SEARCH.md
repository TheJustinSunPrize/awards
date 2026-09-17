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

The initial package contributed the general fixed-cardinality decision
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

## Expanded package review, 2026-09-17

The expanded package adds an attained optimizer for every `k ≥ 3`, monotonicity,
a uniform midpoint-logarithm upper bound for all positive rational targets, and
finite modular prime certificates. The latter give exact first admissible
maximum bounds 28 and 85 for occurrences of multiples of 7 and 17. These are
formalization claims; mathematical novelty and global first priority are not
claimed.

The [repeat query record](dedup-update.json) returned only this PR (#607) for `JSP-000242`. A quoted prime /
denominator query returned #354 but missed known relevant #303, illustrating why
indexed query results are not evidence of absence. A `primePartFree` query had no
hits. The retained earlier search snapshot is not being rewritten as a claim
about the expanded scope.

### Direct source comparisons

- PR #303 was inspected at `fcb2edfac6c478815b4fe78d6614250302744504`, including
  [SmallMultipleObstruction.lean](https://github.com/zifanersuotang/awards/blob/fcb2edfac6c478815b4fe78d6614250302744504/submissions/jsp-000248-small-multiples/SmallMultipleObstruction.lean).
  It proves that `m*p^k` cannot be an attained largest denominator when
  `p > m*m!`. Its prime-power scope is stronger in that direction than our
  first-power partition. Both use the classical small integer numerator / prime
  divisibility contradiction. That shared idea is not an original contribution
  claimed here. Our modular certificates address any divisible denominator under
  a cap, without requiring the divisible denominator to attain that cap.
- PR #354 was inspected at `b583ad8173e9a6eac6de5238077d4d76e27a09ce`, including
  [JSP000250.lean](https://github.com/ketianzhang1-lang/awards/blob/b583ad8173e9a6eac6de5238077d4d76e27a09ce/docs/submissions/jsp-000250-kz/JSP000250.lean).
  `prime_obstruction_split` and `prime_not_representable` use a common multiple
  and a bound `m*lcmUpto(m) < p`, with the prime present as a minimum in the
  application. The source also establishes `t(N) = O(N/log N)` for a different
  extremal function. The denominator-clearing method substantially overlaps.
  Our contribution proposes the reusable exact subset divisibility certificate,
  the stronger next-multiple cap, and the two proved sharp thresholds, alongside
  the fixed-cardinality optimizer. No asymptotic improvement on #354 is claimed.

The complete repository tree of `beetree/math_erdos_289` at the previously pinned
revision was retrieved without truncation to locate potentially related files.
In addition to the earlier two files, declaration-name scans of
`UnitFractionSubsumResults/PruningLemmas.lean` and `UnitFractionDensities.lean`
were used to locate relevant density / subsum machinery. This was not a full
semantic review, compilation, or independence check of that development.

No third-party proof source was copied into the submitted modules. These
comparisons support explicit overlap review; they do not establish first priority,
novel mathematical results, or satisfaction of the prize's assessment criteria.

## Complete asymptotic proof, 2026-09-17

The current package now proves `B(k)/k → 1/(e-1)` for the attained extremum
at every sufficiently large cardinality. The construction uses classical
factorial expansions and duplicate removal, not Croot's short-interval theorem
as a hypothesis. Mathematical novelty is not claimed.

[Updated search record](dedup-limit.json) retains fresh all-state PR queries for
`JSP-000242`, factorial/fraction terms, and the smallest-denominator phrase.
The exact catalog query returns only this PR. This is an indexed search result,
not proof of first-formalization priority.

[PR #271](https://github.com/TheJustinSunPrize/awards/pull/271), at
`ea6deab95a19f29705cba2bb9bcec34194e4ece3`, was rechecked via its PR description
and file inventory. It explicitly claims only the Erdős–Straus lower bound on
the number of terms, and excludes the constructive upper bound and closure of
the second-order question JSP-000251. Our harmonic upper-bound argument overlaps
with that classical inequality in the reciprocal optimization formulation.
The new construction supplies the matching first-order lower bound for B(k).
It does not answer whether the second-order difference for JSP-000251 diverges.
No source from #271 was copied, and its complete proof was not rebuilt here.

The factorial route is attributed to Erdős (1950); the duplicate-removal
principle and padding identities are classical. The new Lean source was written
for this submission using pinned Mathlib lemmas. The absence of a matching
result in the bounded searches does not establish originality or award priority.
