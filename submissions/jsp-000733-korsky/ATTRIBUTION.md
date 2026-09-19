# Attribution and formalization scope

The mathematical results in this package are credited to Samuel Korsky and
the earlier authors identified below. The contribution is a Lean formalization
and an original-problem bridge prepared with Codex assistance. It claims neither
a new mathematical discovery nor established global formalization priority.

## Samuel Korsky's manuscript

Source: **Samuel Korsky**, *Near-Exact Bounds for Primitive Subset Sums*,
July 26, 2026.

- [Author's manuscript](https://drive.google.com/file/d/1G1kNGljoP7qn32niEu87fCWcGKjQvWk4/view).
- [Erdős Problem 882 proof-claims thread](https://www.erdosproblems.com/forum/thread/882/proof-claims), where the author linked the manuscript on July 27, 2026. The listing is not a certification by the moderators.
- Recorded PDF size: 227,158 bytes.
- Recorded SHA-256: `0115a7326cf7b3df8b64d8403055047e9c77e921f83c12c0c19454bbf5c43c84`.

The precise correspondence is:

| Formal statement | Mathematical source |
|---|---|
| `korsky_sum_bound` | Theorem 1.1 (1.6); Proposition 2.2 (2.6). |
| `original_upper_bound` | The upper inequality (3.6) in the proof of Corollary 1.2. |
| `korsky_deficit_bound` | Theorem 1.1 (1.7); Proposition 3.2 (3.3), rearranged without truncated subtraction. |
| `korsky_finite_bound`, `original_finite_bound` | Theorem 1.1 (1.8), expressed without a ceiling by multiplying through by the positive cardinality. |
| `original_threshold_bound` | The upper-bound implication used in Corollary 1.3, in a strict, ceiling-free threshold form. |

The manuscript acknowledges GPT-5.6 Pro assistance with refinements involving
translated coefficient families and balanced differences. Korsky states that
he verified the mathematics and computations and takes responsibility for the
paper. That disclosure is preserved; those mathematical refinements are not
claimed as discoveries of this submitter.

The Lean presentation retains the ordered ternary family and coefficient
cancellation. For the sum bound it uses an injection into residues modulo the
total sum. For the finite strengthening it directly packs balanced words into
an integer interval. The even-support count is implemented by recursive
Boolean encoding; reversed coordinate ranks provide the upper endpoint.
These are formal proof presentations of Korsky's argument, with no separate
mathematical priority claimed. In particular, the author's intermediate
quantity `R` and all of its individual lemmas are not exported as such.

This package contains the upper inequalities and their finite threshold
consequences. It does not contain the classical lower construction, all of
Corollary 1.2, or the equality conclusion of Corollary 1.3. The file
`KorskyBalancedLower.lean` bounds a weighted-word interval from below; it does
not establish a lower bound for the extremal function.

## Earlier mathematics and formal work

The [original problem](https://www.erdosproblems.com/882) is attributed to Erdős
and Sárközy. The classical lower construction is credited to Paul Erdős,
Vsevolod F. Lev, Gérard Rauzy, Csaba Sándor, and András Sárközy, *Greedy
algorithm, arithmetic progressions, subset sums and divisibility*, Discrete
Mathematics 200 (1999), 119–135. It is cited as background, not as a formalized
part of this submission.

An existing lower-construction formalization is published in `plby/lean-proofs`
at [revision 8822f7ddef30fadbd92e1c6ab4ed897af356af5e](https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos882.lean).
Its header credits Codex and GPT-5.6 Sol as formal authors. No source code or
lower-construction proof from that work is incorporated here. The original
subset-sum definitions and finite-maximum implementation were independently
written from the mathematical statement. No license grant is inferred for
that separate source.

[PR #31](https://github.com/TheJustinSunPrize/awards/pull/31), reviewed at
`83f20bbe58d116a9a290c86821fa4ee1a29dd3eb`, establishes the leading asymptotic.
Its [pinned scope statement](https://github.com/zifanersuotang/awards/blob/83f20bbe58d116a9a290c86821fa4ee1a29dd3eb/submissions/jsp-000733/SCOPE.md)
excludes the stronger additive-error results.

[PR #264](https://github.com/TheJustinSunPrize/awards/pull/264), reviewed at
`1db509ec5ad2c410d9b13232685c343c008f0b1f`, proves
`F(n) ≤ log₂ n + (1/2)log₂(log₂ n) + 3` for `n ≥ 32`, and an eventual version.
Its original-condition and maximum-attainment bridges are proved. These
contributions remain acknowledged. The current constant-error and strengthened
finite upper endpoints have different scope. No source code from either PR
is incorporated. This comparison does not challenge those proofs or establish
worldwide first-formalization priority.

Lean, Mathlib, and verification dependencies retain their upstream licenses
and attribution. Mathematical citations do not relicense third-party text or
code. The existing third-party notices continue to apply to this extension.

## Contribution and review roles

The contribution is the formalization of known human-readable mathematics,
including the new finite strengthening and its attained-maximum threshold
interface. Mathematical solver credit and formalizer credit remain distinct.
Any attribution, eligibility, award allocation, or payment depends on the
organizer's review under the [official rules](https://www.hejustinsun.com/prize/rules).
No author endorsement, official verifier signature, or award decision is
asserted by this document. Verification evidence and archival status are separate from authorship.
The six-theorem verification passed; permanent external archival remains
**PENDING**. The actual verification receipt is recorded in the
[expanded-package verification record](verification/finite-v2/VERIFICATION.md).
The earlier `verification/` records remain intact and concern their original
source snapshot and theorem scope.
