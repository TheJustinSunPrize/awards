# Update on subsequent work

The subsequent inverse-factorial improvement in PR #457 is credited in [the new comparison](second-order/PRIOR_ART.md). The newly added package proves a positive cube-root second-order term under natural density one. The comparison below records the original submission's inspected source versions and should not be read as the latest unconditional error bound.

---

# Sources, scope comparison, and attribution

## Source versions consulted

1. Kyle Pratt, *A “Digested” Proof of Erdős Problem #421*, [author's paper](https://www.erdosproblems.com/static/421-Pratt.pdf). Downloaded 2026-09-17; PDF SHA-256 `7d3852fd9b0eeb2ab9dbecbe9cf2a145b89c060f2e491d8064a823a49d55f8ba`, 442749 bytes. Proposition 7.1, printed pp. 17–18, is the comparison baseline. The paper is linked, not redistributed. Its density-one existence proof credits earlier AI-assisted work by Chojecki, Sneiderman, Sharma and others; this submission claims none of that construction work.
2. [PR #457](https://github.com/TheJustinSunPrize/awards/pull/457), by `KunHcz`, public creation time 2026-09-17T04:16:41Z, head `3a5901f7dc4ccd6805a597d04319035808b16bf8`. It states an unconditional coefficient 1/2 with a finite error term, using disjoint triples. Its source and verification were not rerun here; the comparison refers to its public stated result.
3. [Animish Sharma's existing Erdős 421 work](https://github.com/Animish-Sharma/Erdos/tree/5c55362d54cf1f4af2ef2d1110a4c513cba54afd/421), fixed commit `5c55362d54cf1f4af2ef2d1110a4c513cba54afd`. The paper and Lean sources were consulted for scope. This package uses no code or mathematical assumptions from them and does not claim to reproduce their full existence theorem.
4. [Robby Sneiderman's audit and reconstruction](https://github.com/Robby955/erdos-421-audit/tree/318c112c7a70879d98d86d8c3d9a280d77dadb35), fixed commit `318c112c7a70879d98d86d8c3d9a280d77dadb35`. The paper source was consulted for scope; no code or text is included here.
5. [Google DeepMind formal-conjectures, Erdős 421](https://github.com/google-deepmind/formal-conjectures/blob/40e7c98697de6f66b8cbdbf641749ab39ed9c152/FormalConjectures/ErdosProblems/421.lean), fixed commit `40e7c98697de6f66b8cbdbf641749ab39ed9c152`; file SHA-256 `42eb253f0c6d5fb024e9e4c7083405dd0c9a6e59b44f1e18280ac37cb4acf4cf`. Used to cross-check quantifiers and interval conventions. This is a formalized statement with a placeholder proof, not evidence that the theorem has been proved there. No source file is vendored.

## Precise comparison

Pratt's displayed unconditional omission lower bound has coefficient 1/3. His density-one case has coefficient one. PR #457 raises the unconditional coefficient to 1/2. Our finite theorem gives

`E(N) >= floor(sqrt(N)) - floor(sqrt(floor(sqrt(N)))) - 1`

with no density hypothesis. Thus it gives the same leading coefficient one as Pratt's density-one estimate for a wider class, together with a uniform error bound. It does not improve the leading coefficient in the already-known density-one case.

The essential refinement is to count products of adjacent **set members**, not only consecutive integers, and to keep the produced omissions strictly above the cutoff used to count existing omissions. The finite proof and Lean implementation were developed for this contribution. The general observation that block-product collisions force omissions is credited to the existing work.

The submission is not copied from PR #457. Its result is acknowledged because it was found during the final duplicate check. A preliminary 449-item official issue/PR snapshot had no direct same-topic match; a subsequent live search found #457. This illustrates why the preliminary search is not evidence of first priority.

## Limitations of the prior-art search

The official repository, the referenced papers, and public code searches were checked. Search results can be incomplete, and we have not audited all literature or unpublished work. No worldwide novelty or first-formalization claim is made. Human review of the improvement relative to the fixed source versions and of the contribution's eligibility is requested.

## Software attribution and licensing

This package's code and prose were developed with GPT assistance by the submitting account `green3sf`. They are released under the accompanying MIT license. This account label is source attribution, not a confirmed prize recipient designation.

Lean 4.34.0 and Mathlib (commit `5ed2965256430c3649e86755f9576b54eca72435`) supply the foundational library and tactics. They and the other pinned dependencies retain their respective upstream licenses. They are downloaded dependencies, not vendored sources. No proof code from the first JSP-000099 submission or from its upstream author is used in this package.
