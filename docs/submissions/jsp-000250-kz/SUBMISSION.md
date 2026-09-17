# JSP-000250: upper-bound formalization for review

## English

Please review the formalization of the upper-bound part of JSP-000250 and
its eligibility for formalization credit. The requested scope is
`t(N) = O(N/log N)`, where `t(N)` is the first impossible initial denominator
in a distinct-unit-fraction representation of one with all denominators at
most `N`. This submission includes a general prime obstruction and a
fully quantified asymptotic bound. The lower-bound part is not submitted.

## Exact correspondence

The source is Liu and Sawhney, *On further questions regarding unit
fractions*, [arXiv:2404.07113v1, Theorem 1.6 and Section 4](https://arxiv.org/html/2404.07113v1#S4).
The upper-bound argument is credited there to Erdős and Graham (1980),
page 35. The catalog entry is [JSP-000250](../../../problems/catalog-0201-0300.md#JSP-000250).

| Mathematical object or claim | Lean declaration and scope |
| --- | --- |
| Distinct positive denominators from `t` through `N`, including `t`, whose reciprocal sum is one | `Representable N t`; a `Finset` ensures distinctness; `0 < t` and the interval conditions ensure positivity |
| Least positive initial denominator that fails | `firstException N`, constructed using `Nat.find`; `firstException_spec` proves it fails and `smaller_denominators_representable` proves minimality |
| Prime obstruction | `prime_not_representable`: `N <= p*m` and `m*lcm(1,...,m) < p` imply that a prime `p` is not representable |
| Explicit bound | `firstException_upper_bound`: for positive `N` with `log N >= 128`, `t(N) <= 128*N/log N` |
| Upper-bound order | `firstException_isBigO`, with no additional hypotheses, along natural `N` tending to infinity |

The equality is evaluated in the rationals, so zero-denominator conventions
cannot introduce witnesses: every member of a witnessing set is positive.
Finite rational sums embed faithfully in the reals. A finite set with a
specified least member is the set formulation of the ordered distinct
denominators in the source question. No equivalence to an unrelated definition
of Egyptian fractions is assumed.

The constant 128 and the explicit threshold replace the source's sharper
numerical choices. The upper-bound asymptotic order is proved in full. The
near-matching lower bound, an exact formula for every finite `t(N)`, and a
complete classification of impossible denominators remain outside this package.

## Evidence and reproduction

- [Pinned source project](https://github.com/ketianzhang1-lang/jsp-000301-lean/tree/567770d9977669a0846c491d0822fda8dddf9011/projects/jsp-000250).
- [Proof, explanation, attribution and reproduction instructions](README.md).
- [Verification receipt](VERIFICATION.md).
- [Checksums of the copied source files](SOURCE_SHA256SUMS).

The copied Lean source, lockfile, toolchain and scripts match that source
commit byte for byte. Checks validate the exact pinned project and its
exported dependency closure; they do not certify award eligibility.

## Attribution and requested handling

Mathematical credit remains with the cited authors. This new Lean
implementation uses Mathlib and was prepared with OpenAI ChatGPT assistance
under the submitting account's direction. No global first-formalization
priority is asserted. A search of the official repository's public submissions
for `JSP-000250` returned no matching pull requests on 2026-09-17; this is only
a limited duplication check.

Use the unconfirmed recipient placeholder `RECIPIENT-JSP-000250-KZ-A` pending
the organizers' identity and contribution review. The submitting account has
an interest in the eligibility decision. There is no independent human
verification signature or recipient confirmation in this submission.

Please assess statement correspondence, attribution, overlap, and whether
the fully formalized upper-bound component is eligible for separate credit.
This intake package makes no changes to the catalog flags, candidate records,
award records, or generated indexes.
