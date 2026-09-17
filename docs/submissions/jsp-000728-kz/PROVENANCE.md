# Provenance and contribution scope

This submission covers the Cameron–Erdős lower bound only. The mathematical result and odd-pair construction are classical. Their account is reproduced in Section 1, page 2 of Balogh, Liu, Sharifzadeh and Treglown, *The number of maximal sum-free subsets of integers*, arXiv:1409.5661, published in Proceedings of the AMS 143 (2015), 4713–4721, DOI 10.1090/S0002-9939-2015-12615-9.

Original lower-bound credit: Peter J. Cameron and Paul Erdős. The later upper bounds and precise asymptotics belong to their respective cited authors and are outside this package. This submission claims no new informal mathematics, no solution of the full JSP-000728 catalog question, and no global first-formalization priority.

The Lean implementation in this package was written with OpenAI ChatGPT assistance under the submitting account's direction. Mathlib supplies standard finite-set, counting, order and tactic infrastructure. No imported research theorem supplies the claimed counting bound. The general construction and maximal-extension injection are proved in the included source.

Proposed formalization-contributor identifier: RECIPIENT-JSP-000728-KZ-A; confirmation pending. The account's parallel or alternative implementations of this same lower bound belong to the same contribution and must not be counted as separate reward applications. In particular, an unpublished alternative interval construction was identified during preparation.

The official issue and pull-request inventory was checked for JSP-000728 on September 17, 2026; no existing entry was found at the initial check. This is a bounded search, not a guarantee of worldwide novelty or priority.

A subsequent external-source review found public upper-bound formalization source for the same counting problem in `plby/lean-proofs`, predating this submission. See [OVERLAP_REVIEW.md](OVERLAP_REVIEW.md) for the pinned source, exact statement comparison, upstream attribution and limits of verification. This discovery does not expand the scope or priority claims of the present lower-bound implementation.

Reproduction scripts adapt same-account tooling used for earlier proof submissions. Mathematical source text is linked and paraphrased, not reproduced as a paper. Repository code and documentation licenses apply; dependency and external tool licenses remain with their authors.
