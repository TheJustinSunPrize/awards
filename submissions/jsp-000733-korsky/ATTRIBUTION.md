# Attribution and formalization scope

This package formalizes published mathematics about Erdős Problem 882. It
claims neither a new mathematical discovery nor established global priority
for its formalization.

## Samuel Korsky's upper bound

The mathematical source is Samuel Korsky, *Near-Exact Bounds for Primitive
Subset Sums*, dated July 26, 2026. The author linked the manuscript in the
[Erdős Problem 882 proof-claims thread](https://www.erdosproblems.com/forum/thread/882/proof-claims)
on July 27, 2026. The listing expressly does not certify correctness or imply
moderator review.

- [Author's manuscript](https://drive.google.com/file/d/1G1kNGljoP7qn32niEu87fCWcGKjQvWk4/view).
- Recorded PDF size: 227,158 bytes.
- Recorded PDF SHA-256: `0115a7326cf7b3df8b64d8403055047e9c77e921f83c12c0c19454bbf5c43c84`.
- The sum bound is Proposition 2.2, equation (2.6), identical to the inequality
  (1.6) within Theorem 1.1.
- The original extremal upper bound follows by bounding the total by `k*n`;
  this is inequality (3.6) in the proof of Corollary 1.2.

The manuscript acknowledges GPT-5.6 Pro assistance in refining translated
coefficient-family and balanced-difference arguments. Korsky states that he
checked the mathematics and computations and takes responsibility for the
paper. This disclosure is preserved; the current submitter does not claim those
mathematical refinements as their own.

The formal proof uses the paper's ordered ternary family and coefficient
cancellation. It presents the packing as a finite injection into residues
modulo the total sum, rather than counting arbitrarily many translates and
taking a limit. The new Lean proof, finite presentation, and original-problem
bridge were prepared with Codex assistance. No separate mathematical priority
is claimed for this rearrangement.

The formalized sum bound assumes positive natural weights and excludes only a
ratio of 2 between nonempty subset sums. The original primitivity condition
implies this hypothesis. Only the sum inequality and resulting upper bound are
submitted. The rest of Theorem 1.1, the lower construction, a two-value theorem,
and the manuscript's stronger intervals of exact values are not claimed as
formalized results of this package.

## Earlier mathematics and formal work

The underlying [original problem](https://www.erdosproblems.com/882) is attributed
to Erdős and Sárközy. The classical lower construction is credited to Paul
Erdős, Vsevolod F. Lev, Gérard Rauzy, Csaba Sándor, and András Sárközy,
*Greedy algorithm, arithmetic progressions, subset sums and divisibility*,
Discrete Mathematics 200 (1999), 119–135.

An existing lower-construction formalization is published in `plby/lean-proofs`
at [revision 8822f7ddef30fadbd92e1c6ab4ed897af356af5e](https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos882.lean).
Its header credits Codex and GPT-5.6 Sol as formal authors. It is acknowledged
as prior work; **none of its source code or lower-construction proof is
incorporated in this submission**. The original-problem definitions and maximum
attainment used here were independently implemented from the mathematical
statement.

[PR #31](https://github.com/TheJustinSunPrize/awards/pull/31), reviewed at
`83f20bbe58d116a9a290c86821fa4ee1a29dd3eb`, establishes the leading asymptotic. Its
[pinned scope statement](https://github.com/zifanersuotang/awards/blob/83f20bbe58d116a9a290c86821fa4ee1a29dd3eb/submissions/jsp-000733/SCOPE.md)
excludes the stronger error-term results.

[PR #264](https://github.com/TheJustinSunPrize/awards/pull/264), reviewed at
`1db509ec5ad2c410d9b13232685c343c008f0b1f`, proves
`F(n) ≤ log₂ n + (1/2)log₂(log₂ n) + 3` for `n ≥ 32`, and an eventual version.
Its source includes complete original-condition and maximum-attainment
bridges. The present constant additive-error upper bound is a distinct,
stronger endpoint. No source code from either PR is incorporated here. This
scope comparison does not dispute the validity of those contributions or
establish worldwide priority.

## Authorship and review roles

The submission seeks recognition for formalizing Korsky's known mathematical
result. Solver attribution and formalization attribution remain distinct. The
[official rules](https://www.hejustinsun.com/prize/rules), sections 1 and 5,
recognize formalization of human-readable proofs and distinguish a formalizer
role; section 2.5 permits qualifying achievements completed in 2026. These
provisions allow review of the proposed contribution but do not guarantee its
eligibility determination, tier, or payment.

The 30% formalizer share described in section 5 is a share of an allocation only
if an award is made and attribution confirmed. No recipient nomination,
committee signature, proof-author endorsement, or award decision is implied
by these citations. Verification outcomes and archival status are recorded
separately from authorship.
