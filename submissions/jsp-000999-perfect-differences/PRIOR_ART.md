# Mathematical attribution and comparison

## Established mathematics

This package independently implements a classical finite-obstruction greedy construction. It claims a checked Lean artifact with explicit constants, not new mathematics.

1. Javier Cilleruelo and Melvyn B. Nathanson, **Perfect difference sets constructed from Sidon sets**, [arXiv:math/0609244v1](https://arxiv.org/html/math/0609244v1), 8 September 2006; published in Combinatorica 28 (2008), 401–414, [DOI](https://doi.org/10.1007/s00493-008-2339-4). The introduction records the known greedy cube-root counting bound and cites Lev. Section 4.1 explicitly records the corresponding cubic representation-endpoint bound. The paper's stronger density results are not formalized here.
2. Vsevolod F. Lev, **Reconstructing integer sets from their representation functions**, Electronic Journal of Combinatorics 11 (2004), Research Paper 78, [DOI](https://doi.org/10.37236/1831). This is the greedy-construction reference identified by Cilleruelo–Nathanson. Attribution here relies on that explicit citation; this package is not presented as a line-by-line formalization of all of Lev's paper.
3. Boris Alexeev and Dustin G. Mixon, **Forbidden Sidon subsets of perfect difference sets, featuring a human-assisted proof**, [arXiv:2510.19804v1](https://arxiv.org/html/2510.19804v1), Claim 10. That claim states that a finite Sidon set extends to an infinite perfect difference set and credits Hall, Theorem 3.1, explaining the finite-obstruction greedy argument. Their finite modular counterexamples concern a different extension question. This submission independently formalizes the positive-integer infinite extension with explicit cubic bounds; it does not assert a new finite-seed extension theorem.

## Same-problem Lean project

The public project [lechmazur/erdos_1194](https://github.com/lechmazur/erdos_1194/tree/ea9819d2d7027d04481aa27fb7f7bf6322155ceb), inspected at commit `ea9819d2d7027d04481aa27fb7f7bf6322155ceb` on 2026-09-17, already formalizes a lower growth obstruction for the same problem. Its [Challenge.lean](https://github.com/lechmazur/erdos_1194/blob/ea9819d2d7027d04481aa27fb7f7bf6322155ceb/Challenge.lean) defines a positive set with unique positive differences and a top endpoint indexed by the difference. Its principal claims are `floor_saving_lower_bound` and `endpoint_limsup`.

The present package instead constructs a set and proves an upper endpoint bound `u(d)≤2*(2*d+1)^3`, with arbitrary finite positive Sidon seeds and explicit counting witnesses. These do not imply or replace the sharper lower-bound results. No code from that project is copied or imported. The comparison is limited to the pinned project inspected; no global claim of absence of equivalent Lean proofs or first-formalization priority is made.

## Official scope

The record [JSP-000999](https://github.com/TheJustinSunPrize/awards/blob/f4e7173d89dfe91022a185427d63452c8ffbf6ae/problems/catalog-0901-1000.md#JSP-000999) concerns growth of perfect difference sets and cites the older constructions. [Erdős 1194](https://www.erdosproblems.com/1194) is the corresponding external problem. The official record at the pinned revision does not establish eligibility or a completed solution. This package supplies reviewable evidence for a scoped contribution and leaves those determinations to the maintainers.

The dated formal artifact is from 2026; the underlying mathematical results predate 2026. The date of formalization must not be confused with the date of mathematical discovery. Passing local verification does not resolve any prize cutoff, originality, acceptance or eligibility requirement.
