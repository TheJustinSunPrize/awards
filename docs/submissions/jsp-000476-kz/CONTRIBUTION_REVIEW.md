# Contribution comparison for JSP-000476

## English

This contributor-side review, prepared on 2026-09-17, narrows the claim in
[PR #372](https://github.com/TheJustinSunPrize/awards/pull/372) against specific
prior public source files. It requests assessment of a scoped formalization
increment. It does not establish novelty, independent approval, or eligibility.

## Sources and inspection boundary

The primary proof is pinned at
[`4ab28a44e7c89d814699c70f79a0e138f72162e7`](https://github.com/ketianzhang1-lang/jsp-000301-lean/blob/4ab28a44e7c89d814699c70f79a0e138f72162e7/projects/jsp-000476/JSP000476.lean).
Its proof code and verification evidence are unchanged by this review.

For comparison, the following files were read at external commit
`8822f7ddef30fadbd92e1c6ab4ed897af356af5e`:

- [LowerBound.lean](https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos587/LowerBound.lean): the prime-multiple construction and a real-valued cube-root lower bound.
- [LowerBoundMax.lean](https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos587/LowerBoundMax.lean): transfer of that bound to the extremal quantity.
- [Erdos587.lean](https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos587.lean): the entry file, declarations, documentation, and imports for the broader development.

The external project's full dependency closure was neither rebuilt nor audited
in this comparison. Its entry file declares a complete asymptotic result and
stronger upper bounds; that is a description of the inspected source, not an
independent certification. Absence from the two inspected lower-bound files
does not establish absence from the repository or the mathematical literature.

## Statement comparison

Both constructions use the set {p,2p,...,mp}. The external file represents its
indices by the closed interval from 1 to m; our file uses i+1 for 0 <= i < m.
Both quantify over nonempty subsets with distinct summands. The external
square condition uses `IsSquare` on natural numbers; ours excludes every
natural x squared. These are the same square-avoidance condition.

| Claim | Inspected external declaration | Primary submission | Assessment |
| --- | --- | --- | --- |
| Classical prime construction | `prime_multiples_square_sum_free`, sufficient hypothesis m^2 < p | `multiples_power_free`, sufficient hypothesis m(m+1)/2 < p | Substantial mathematical overlap; a sharper finite sufficient condition and stronger avoided family are explicitly formalized here. |
| Exact prime threshold | Not stated in the inspected lower-bound files | `exact_criterion` and `multiples_square_witness` give both directions and a failure witness | A concrete difference from those files; no global priority claim. |
| Uniform lower bound | `exists_cube_root_square_sum_free`: cardinality at least N^(1/3)/4 for N >= 64 | `exists_power_free_in_interval`: cardinality m whenever m^2(m+1) <= N | Both have cube-root scale; our finite construction budget is no larger than the inspected proof's 2m^3 budget, and is strictly smaller for m >= 2. This does not improve the exponent or establish a new extremal asymptotic result. |
| Squarefree steps | Prime hypothesis in the inspected lower-bound construction | `squarefree_exact_criterion`: exact threshold for squares and all perfect powers | The squarefree construction is already noted in Nguyen–Vu Remark 1.3; mathematical novelty is not claimed. |
| Every positive step d | Not stated in the inspected lower-bound files | `all_positive_steps_classified`: d=b^2*a, with a squarefree, and exact square threshold m(m+1)<2a | Complete only for the family {d,2d,...,md}. General d does not yield all-power avoidance. |
| Upper bound for arbitrary admissible sets | Entry file declares `nguyenVuBound` and further upper-bound variants | No corresponding theorem | The principal missing part of a complete solution in our submission. |
| Full extremal growth | Entry file declares `erdos_587`, eventual N^(1/3-epsilon) and N^(1/3+epsilon) bounds for every positive epsilon | No corresponding theorem | Our submission is partial relative to the original problem. |

A small arithmetic example makes the threshold difference concrete: p=7,
m=3 satisfies m(m+1)/2=6<7 while m^2=9<7 is false. Our criterion applies to
{7,14,21}; the sufficient hypothesis of the inspected external lemma does
not. This does not contradict that lemma or exclude deriving the same
example elsewhere in the external project.

## Attribution and verification boundaries

The classical construction is attributed to Erdős in Example 1.2 of
Nguyen–Vu, [Squares in sumsets](https://arxiv.org/abs/0811.1311); their
Remark 1.3 supplies the squarefree context. The external entry file credits
Nguyen and Vu for the informal result, Formal Conjectures authors for the
statements, and Codex / GPT-5.6 Sol for formalization.

Our proof was written before this expanded source comparison. No external
proof code has been copied or imported in this update. OpenAI ChatGPT
assistance remains disclosed. The same-contributor implementation described
in [SUPPLEMENTARY_PROOF.md](SUPPLEMENTARY_PROOF.md) overlaps this submission;
it is neither a separate award claim nor independent human review.

The primary proof's successful Lean and NaNoda checks remain documented in
[VERIFICATION.md](VERIFICATION.md). They do not certify the external project,
the supplementary implementation, mathematical originality, statement fidelity
to the full original problem, or award eligibility.

## Questions still requiring a review decision

1. Does this narrower formalization increment qualify for consideration given
   the classical result and prior external formalization?
2. Are the definitions, exact finite criteria, attribution, and comparison
   adequate, including overlap beyond the inspected files?
3. Which independent reviewers and archival evidence are required before
   this material could enter a public candidate record?

The [catalog entry](https://github.com/TheJustinSunPrize/awards/blob/f4e7173d89dfe91022a185427d63452c8ffbf6ae/problems/catalog-0401-0500.md#JSP-000476)
currently records `Lean proof: No` and `Eligible to claim: No`. The existence
of external source code does not itself update those markers. This PR proposes
evidence for review and changes neither marker nor candidate or award records.
Under the [record guide](https://github.com/TheJustinSunPrize/awards/blob/f4e7173d89dfe91022a185427d63452c8ffbf6ae/docs/records.md),
catalog flags, a submitted PR, and successful checks are not a public nomination
or award. No monetary amount or likelihood of an award can be inferred from
the evidence in this package.

Unresolved items remain organizer intake and eligibility assessment, independent
statement and attribution review, written recipient confirmation, and permanent
independent preservation of the large verification artifact. The recorded
artifact expires on 2026-12-16; pinned source and textual evidence alone do not
establish permanent preservation of that complete artifact.
