# Statement fidelity and attribution

## Target

[Erdős Problem 757](https://www.erdosproblems.com/757), indexed as
[JSP-000621](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0601-0700.md#JSP-000621),
asks for the best universal Sidon-subset proportion for finite real sets
whose every four-element subset has at least eleven signed differences.
The original optimal-constant question is still open.

This package formalizes the known **upper bound `c ≤ 4/7`**, not the
optimal value and not the separate lower bound `9/17`.

## Definitions checked

| Original concept | Definition here |
| --- | --- |
| Finite real set | `Finset ℝ`; no restriction to rational or integer inputs in `Admissible` |
| Difference set, including zero | `differences t = (t ×ˢ t).image (fun p => p.1 - p.2)` |
| Local `(4,5)` condition | `AlmostSidon a`: every four-element subset `t` has `(differences t).card ≥ 11` |
| Sidon subset | Equality of two pair sums forces equality of the unordered pairs, including repeated summands |
| Universal proportion | `Admissible c`: for every finite real `a` satisfying the local condition, some Sidon subset has cardinality at least `c * a.card` |
| Claimed theorem | `admissible_le_four_sevenths : Admissible c → c ≤ 4 / 7` over `ℝ` |

`Finset` quantifies over all finite sets. It does not allow duplicate elements.
The certificate's integers are cast into `ℝ` through an injective map.
Theorems `realImage_card`, `differences_realImage` and `sidon_realImage_iff`
prove the necessary preservation facts. The example lies in the domain
of the original real-set problem.

The proof is not conditional on the existence of the construction, on
a Python check, on an unproved extremal result or on a claimed asymptotic
limit. It proves the concrete example and then applies the universal
guarantee to that example. No separate assertion about the limiting
extremal ratio is made.

## Construction and proof obligations

The integer base is

`{0,136,200,243,246,249,272,286,298,323,400,528,596,1056}`.

The checked obligations are:

1. The set has fourteen elements.
2. Every four-element subset has at least eleven signed differences.
3. Every nine-element subset contains an explicitly certified nonconstant
   three-term arithmetic progression, and hence is not Sidon.
4. Any larger subset contains a nine-element subset, so its Sidon property
   would contradict item 3.
5. The subset `{0,136,200,243,246,298,323,528}` is Sidon and has eight elements.
6. All the preceding properties hold for the corresponding real sets.
7. A universal guarantee applied to the base implies `14 * c ≤ 8`, so `c ≤ 4/7`.

## Credit and priority

The mathematical construction and upper bound are credited to **Jie Ma
and Quanyu Tang**, [arXiv:2602.23282](https://arxiv.org/abs/2602.23282),
version 1, Lemma 5.1, Section 5.1 and Appendix A. The first version was
submitted on 2026-02-26; the current abstract retains the same upper bound.

The submitted work is a new implementation of a formal proof of that
known result. OpenAI Codex assisted the formalization, local verification
and preparation of the package. The public proposal
[awards#49](https://github.com/TheJustinSunPrize/awards/issues/49) was
reviewed during selection and is acknowledged here. The LeanGenius
`Erdos757Problem.lean` definitions and elementary results were inspected,
but its code was not imported and it did not provide this upper-bound proof.

The bounded prior-art check found no complete proof of this precise bound
in the inspected official submissions and selected public source searches.
That does not establish worldwide novelty, first-formalization priority,
exclusive reservation or prize entitlement. Those determinations remain
with the organizers and reviewers.

The applicant seeks consideration for a formalization contribution only.
No mathematical solver credit or award is claimed. Recipient identity
confirmation and any payout arrangements are outside this public package.
