# JSP-000883: a verified improved upper bound

## English

This package proves the `Erdos1063.erdos_1063.better_upper` target, with the
explicit choice **upper(k) = exp((3/4) log(2) k) = 2^(3k/4)**. In fact the proof
establishes `n_k ≤ upper(k)` for all sufficiently large k. It also proves
`upper = o(k * lcm(1,...,k-1))`.

The main theorem is in [Submission.lean](Submission.lean). Its `n` is the least
natural number n ≥ 2k for which exactly one of n,n-1,...,n-k+1 does not divide
`choose(n,k)`. A witness is constructed before the infimum bound is used; the
result does not exploit an empty set. The LCM is computed in **natural numbers**
before casting to reals.

This completes that improved-upper-bound target. It does not determine the exact
value or sharp asymptotic order of n_k, nor claim to resolve every formulation of
the original request to estimate n_k. The official catalog's broader problem
and its eligibility status remain for the operator to review.

## Reproduction

Install Lean v4.34.0 through the usual Lean toolchain manager, then run:

```sh
sh verify.sh
```

The [toolchain](lean-toolchain), [Lake configuration](lakefile.toml), and
[dependency lock](lake-manifest.json) pin the environment. Mathlib is pinned to
`5ed2965256430c3649e86755f9576b54eca72435` (v4.34.0). Initial execution needs
network access for pinned dependencies and Mathlib caches.

The script builds all seven source modules, prints the final theorem's axiom
dependencies, and replays each submitted module with the bundled `leanchecker`.
See [verification details](VERIFICATION.md), [the reproduction log](reproduction.log),
and [source hashes](SHA256SUMS). No compiled binary is required in the submission.

## Attribution and relationship to existing work

This is a formalization contribution based on already public mathematical
research. No priority for discovering an improved upper bound is claimed.

- Patrick White's [erdos1063-upper-bound repository](https://github.com/pw/erdos1063-upper-bound),
  inspected at [a28481f5b4bda374086533397269c5b550c759b8](https://github.com/pw/erdos1063-upper-bound/tree/a28481f5b4bda374086533397269c5b550c759b8),
  gives the low-carry covering argument, small-prime anchors, exceptional-prime
  handling, simultaneous approximation, and a stronger subexponential bound.
  Its README records the author's stated GPT-5.6 Sol / Claude collaboration and
  explicitly says the written result lacks a Lean formalization.
- Ricky Cipollini's manuscript, linked from the
  [Erdős 1063 proof-claims page](https://www.erdosproblems.com/forum/thread/1063/proof-claims)
  and available on [Overleaf](https://www.overleaf.com/read/hrpsqsnqktky), supplies
  related carry/stabilization arguments and a sharper claimed upper bound.
  The public claim identifies Cipollini and GPT-5.6 Sol. Those mathematical
  attributions are retained; this package does not adjudicate solver priority.
- The target and definition follow the
  [Formal Conjectures Erdős 1063 statement](https://github.com/google-deepmind/formal-conjectures/blob/cb20d7eb22b6f9866001d53fdf1ea4bb93fb34c0/FormalConjectures/ErdosProblems/1063.lean)
  (Apache-2.0, copyright 2026 The Formal Conjectures Authors), including its
  correction that the LCM is a natural-number LCM.
- Related official submissions are [PR 56](https://github.com/TheJustinSunPrize/awards/pull/56),
  [PR 154](https://github.com/TheJustinSunPrize/awards/pull/154),
  [PR 406](https://github.com/TheJustinSunPrize/awards/pull/406), and
  [PR 498](https://github.com/TheJustinSunPrize/awards/pull/498).

The Lean implementation and the coarse parameter/counting estimates in this
package were prepared in this Codex-assisted workflow. The weaker explicit
exponential estimate is chosen to complete the target with elementary
Chebyshev bounds; it is not presented as an improvement over the stronger
written 2026 results. See the [proof outline](PROOF_OUTLINE.md).

## Requested operator review

Please review statement fidelity, attribution, machine verification, and
eligibility of this formalization of the improved-upper-bound target.
`submissions/jsp-000883` is an intake location proposed by this PR and can be
moved to the operator's preferred location.

Proposed formalization contributor: **RECIPIENT-jsp-000883-A**, confirmation
pending. This is a self-submission with Codex AI assistance; its local checks
are not independent third-party attestations. Mathematical solver attribution
remains with the cited prior work, subject to public priority review.

No candidate or award decision, recipient confirmation, paid status, curator
signature, or official priority timestamp is asserted. Existing catalog and
award records are unchanged. Repository CI validates records and links; it
does not itself run this Lean proof or decide an award.

Lean source: Apache-2.0, see [LICENSE](LICENSE). First-party documentation is
offered under [CC BY 4.0](https://creativecommons.org/licenses/by/4.0/).
