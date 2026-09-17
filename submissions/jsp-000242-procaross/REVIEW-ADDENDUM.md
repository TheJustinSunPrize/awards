# Statement correspondence, prior work and submission chronology

Review snapshot: 2026-09-17. This supplements the earlier bounded
[overlap review](DUPLICATE-SEARCH.md). It records contributor analysis rather than
designated verification or an award-priority decision.

## Original statement

Croot, *On unit fractions with denominators in short intervals*, Acta Arithmetica
99 (2001), 99–114, explicitly asks on page 99, question 1, whether the greatest
smallest denominator of a k-term representation of 1 is asymptotic to k/(e−1).
The set of representations uses distinct positive integer denominators.
[Published paper](https://www.impan.pl/shop/en/publication/transaction/download/product/83061).

The submitted definitions and conclusions correspond as follows:

| Mathematical requirement | Formal declaration or clause |
| --- | --- |
| Distinct positive denominators, exactly k terms, sum 1 | `AttainableMinimum`: `Finset ℕ`, positivity, `A.card = k`, and rational reciprocal sum 1 |
| The actual minimum of a representation | `M ∈ A` and `∀ a ∈ A, M ≤ a` |
| Attained greatest minimum among all representations | `optimalMinimum_isGreatest`, for every k ≥ 3 |
| The asymptotic in question 1 | `optimalMinimum_tendsto`: B(k)/k → 1/(e−1) |

There is no upper cutoff on denominators in the feasible set. Question 2 on
page 99 concerns the shortest interval; the stronger main theorem on page 100
also bounds the largest denominator. Those statements are outside this package,
but are not additional hypotheses in question 1. The
[proof outline](MATHEMATICAL-PROOF.md) explains the separate factorial route.

## Additional prior-work checks

All 440 PRs returned by the official repository's all-state pagination at
2026-09-17T11:52:00Z were screened by title and body. Terms included unit
fractions, Egyptian fractions, smallest/minimum denominators, Croot and the
related JSP identifiers. This was not a semantic review of every PR's source.
Related PRs and targeted external sources were then inspected. No earlier
complete matching proof was identified in this bounded review.

The directly related
[Erdos284Problem.lean](https://github.com/rjwalters/lean-genius/blob/dc62f771ed5010abfdb04247dff6143e0e69d3e7/proofs/Proofs/Erdos284Problem.lean)
declares `f`, `f_upper_bound`, and `f_lower_bound` as axioms at lines 75, 99 and
121. Its final theorem combines the two assumed bounds. Thus that inspected
file does not prove the matching extremal-limit result without additional
assumptions. Other files in that repository do prove finite examples and a
splitting step; those elementary contributions are not claimed as firsts here.

[PR #309](https://github.com/TheJustinSunPrize/awards/pull/309), at
`6fa0832648ddc3f2b61536403446e66705c3433b`, concerns the classical bound on the
number of divisors needed to represent integers below a factorial. It is
related to the construction tools, not a proof of this package's main limit.
The previously reviewed PRs #271, #303 and #354 retain the overlap qualifications
recorded in `DUPLICATE-SEARCH.md`.

The [Bloom–Mehta project](https://github.com/b-mehta/unit-fractions/tree/10ef71a300cf29e5f19beb2bbc723a035a0678de)
formalizes reciprocal-sum representations in sets of positive density. Its
README and principal result files were inspected; they did not supply the
fixed-cardinality optimal-minimum conclusion reviewed here. Its full dependency
tree was not rebuilt for this comparison.

The [Erdős problem database](https://github.com/teorth/erdosproblems/blob/3c68e941162f81d650fc886eed34e58bed3a6a01/data/problems.yaml)
still marks problem 284 unformalized, but its entry is older than this submission.
Global indexed code queries missed the existing Erdos284 file above as well as
this submission. Database flags and search absence therefore cannot establish
global first-formalization priority. No such priority is asserted.

## Public chronology

| Event | UTC timestamp | Evidence and limit |
| --- | --- | --- |
| PR #607 created with partial finite results | 2026-09-17 08:27:26 | PR creation does not establish that the later complete proof existed then. |
| Complete proof commit `85f2a9b...` | 2026-09-17 11:18:20 | Git committer timestamp; supplied by the committer. |
| Complete source release published | 2026-09-17 11:20:37 | GitHub release `published_at`, with the pinned source asset and checksum. |

The [source release](https://github.com/procaross/awards/releases/tag/jsp-000242-full-asymptotic-v1)
is public timestamp evidence for the complete package, not an organizer-approved
priority ruling. The original PR time is not claimed as the completion time.

## Applicant confirmation and remaining decisions

The [applicant confirmation](CONTRIBUTOR-CONFIRMATION.md) now has an authorized
public attestation. The [published rules](https://www.hejustinsun.com/zh/prize/rules)
recognize a formalizer role, but designated verification, applicability of the
achievement-date condition to a new formalization of classical mathematics,
and any award allocation remain for the organizer to determine. This addendum
does not change official eligibility flags or announce an award.
