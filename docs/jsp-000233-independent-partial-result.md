# JSP-000233 / Erdős Problem 272 — independent partial result (draft)

**Author:** Peihan Wu (GitHub: [killtoki123456](https://github.com/killtoki123456))  
**Status:** Work in progress; a partial mathematical result, not a complete solution or prize claim.  
**Record date:** 2 November 2026.

This note records the scope, evidence, and attribution of the author's public manuscript. **Please keep the associated pull request in draft status.** Neither acceptance nor merging is requested at this stage. Its mathematical claims have not been independently verified by the award organizers.

## 1. Mathematical statement and claimed contribution

Let \(t(N)\) be the maximum size of a family of **distinct** subsets of \([N]=\{1,\dots,N\}\) such that the intersection of any two distinct members is a **nonempty arithmetic progression**. Singletons and pairs count as arithmetic progressions. The members of the family need not themselves be arithmetic progressions, and no common point of the entire family is assumed.

The manuscript **claims** that, for every integer **\(N\ge 4000\)** (including \(N=4000\)),

\[
t(N)=\binom{N}{2}+1+\left\lfloor\frac{N-1}{4}\right\rfloor.
\]

The claimed independent contribution is a large-order **upper-bound argument** with the explicit threshold \(N\ge 4000\). Combined with Tibor Szabó's previously known matching lower-bound construction, this yields the claimed exact value in that range. **The lower-bound construction is not claimed as a new contribution by Peihan Wu.** Nor does this manuscript claim to classify all extremal families.

For context, [Li Xiang's separate Draft PR #5513](https://github.com/TheJustinSunPrize/awards/pull/5513) reports an exact-value result for \(N\ge642498\). The present manuscript claims the same value for the larger range \(N\ge4000\), including **\(4000\le N<642498\)**. This is a comparison of reported scopes, not a claim that this proof is based on Li Xiang's work, and not an adjudication of priority or correctness.

**What remains incomplete:** This manuscript does not prove the full original problem for all smaller parameters \(N<4000\). This does not mean all smaller cases are unknown: already-established small-parameter results retain their proper citations. The author's preliminary investigations near 3800–4000 are excluded from this submission, and no threshold of 3800 is claimed.

## 2. Public manuscript and version-locked evidence

- Original problem: [Erdős Problem 272](https://www.erdosproblems.com/272).
- Prize record: [JSP-000233](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0201-0300.md#jsp-000233).
- Author's research repository: [Erdos-Problem-272-An-Independent-Proof-with-an-Explicit-Threshold](https://github.com/killtoki123456/Erdos-Problem-272-An-Independent-Proof-with-an-Explicit-Threshold).
- Selected repository branch: **main**.
- Fixed version: [commit 5677c4f71e1aff67062a141adc75a318878bb1f8](https://github.com/killtoki123456/Erdos-Problem-272-An-Independent-Proof-with-an-Explicit-Threshold/commit/5677c4f71e1aff67062a141adc75a318878bb1f8).
- [English manuscript (PDF), fixed version](https://github.com/killtoki123456/Erdos-Problem-272-An-Independent-Proof-with-an-Explicit-Threshold/blob/5677c4f71e1aff67062a141adc75a318878bb1f8/erdos272_arxiv_en.pdf).
- [English README, fixed version](https://github.com/killtoki123456/Erdos-Problem-272-An-Independent-Proof-with-an-Explicit-Threshold/blob/5677c4f71e1aff67062a141adc75a318878bb1f8/README.md).
- [Chinese README, fixed version](https://github.com/killtoki123456/Erdos-Problem-272-An-Independent-Proof-with-an-Explicit-Threshold/blob/5677c4f71e1aff67062a141adc75a318878bb1f8/README.zh-CN.md).

These fixed links identify the materials provided with this draft. They do **not** certify validity, independent reproducibility, or an earlier discovery date.

## 3. Independence and attribution

The author's English README expressly declares:

> I declare that I conducted and completed this research independently, without research dependence on Li Xiang's draft. That draft was not the source of my arguments or threshold improvements, and this research is not a continuation, adaptation or joint development of it.

This is the author's declaration, **not a finding by the prize organizers**. The independence statement concerns Li Xiang's draft, not the prior mathematical literature or the absence of AI assistance.

The author claims independent development of the present large-order threshold argument. Earlier results and sources cited in the manuscript, including **Szabó's matching lower construction**, **Zhanfu Yang's work on the common-point case, private pairs, and staircase methods**, and the reported work of **Jensen Kohlmeyer and Liam Kruer**, retain their original attribution. Li Xiang's PR is cited to distinguish independent, overlapping research scopes.

The author's public README also reports **GPT-assisted** mathematical exploration, proof reconstruction and gap repair, implementation, manuscript preparation, and review. That disclosure is retained here; AI-assisted checking does not amount to independent human peer review.

### Author-reported research timeline

The author's README records these intermediate thresholds. **These are dates in the author's research records, not independently verified initial-publication or formal-verification dates.**

| Date | Recorded threshold |
| --- | --- |
| 2026-10-24 | \(N\ge2^{252}\) |
| 2026-10-25 | \(N\ge2^{90}\) |
| 2026-10-29 | \(N\ge75000\) |
| 2026-10-30 | \(N\ge49000\) |
| 2026-11-01 | \(N\ge4000\) |

No priority determination is claimed from these dates or from the PR creation date.

## 4. Evidence limits and formalization status

The selected public repository version contains the paper PDF and two READMEs. As the author explicitly acknowledges, the mathematical paper still relies on electronic supplements and computational certificates that have **not been publicly released** in this repository. Code, certificates, technical source notes, and Lean files are **not** included in the published version. Thus the public materials do **not yet permit independent reproduction of all computations or verification of the full chain of dependencies**.

Some Lean formalization has been undertaken, but the author's README describes it as unfinished and unpublished. This submission therefore does **not** provide or claim a public Lean proof, a reproducible Lean build, or an axiom audit. No independent human verification or organizer acceptance is claimed.

## 5. Collaboration, authorship, and potential future prize claims

If a subsequent complete solution or award submission **materially relies on this manuscript**, the author asks that the specific results and fixed version be cited, and that their actual contribution be identified alongside prior authors and other contributors. The author can be contacted through an issue in the [independent research repository](https://github.com/killtoki123456/Erdos-Problem-272-An-Independent-Proof-with-an-Explicit-Threshold/issues).

The author wishes to discuss participation in any qualifying future joint application that materially draws on this work. Joint application roles, authorship, and any proposed distribution of prize funds should be discussed explicitly in advance, according to actual contributions and the applicable prize rules. This statement **does not establish a prize entitlement, automatic share, or joint authorship**.

## 6. Scope of this draft PR

This draft adds **only this standalone documentation file**. It does **not** alter the existing JSP-000233 catalog entry, problem status, Lean status, award eligibility, candidate records, award records, or any other existing file. The mathematical manuscript remains in the author's separate repository.

The organizer's [contribution guidelines](https://github.com/TheJustinSunPrize/awards/blob/main/CONTRIBUTING.md) require complete solutions for formal acceptance and describe catalog-based changes. **This partial submission does not meet those requirements yet**, and using a standalone documentation file is a preparatory choice, not an approved alternative format. Maintainers may ask for a different format or decline to retain the draft.

**No complete-solution claim, accepted review, priority decision, candidate status, public review, or award entitlement is asserted.**
