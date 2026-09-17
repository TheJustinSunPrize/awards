# JSP-000738: five divisors near the square root, infinitely often

## English

**Draft observation candidate.** This record requests review of a Lean
formalization of an existing partial result. It does not announce an award
or assert that the full problem has been solved.

### Result and original source

For infinitely many positive integers n, at least five distinct positive
divisors d satisfy the strict inequalities

`sqrt(n) < d < sqrt(n) + 31 * n^(1/4)`.

The ordinary proof is **M. Czech**, *Five divisors near √n, infinitely often:
a Pell-tuned refinement of the Erdős–Rosenfeld construction (Erdős problem #887)*,
July 2026, Theorem 1: [author's proof note](https://czechu.blog/erdos/problems/887/note887.pdf).
The downloaded paper has SHA-256
`0a20ebeffa5e48201875cbdc62526224a17a54e55ae10e3755364bb334fcf77a`.
The paper is linked, not redistributed.

The Lean proof uses the Pell orbit `z^2 = 56*x^2 + 65` and
`n = (x^2-1)*(x^2-4)*(x^2-16)*(x^2-49)`, starting at `(1109,8299)`.
Its uniform estimates assume `x >= 50`. This tail proves the full infinite-family
conclusion with C=31; the initial point `(37,277)` and the paper's full pointwise
statement starting at x=37 are not separately formalized.

Three final roots are exposed in the 268-line source:

- `FiveDivisors.infinitely_many_five_divisors`: the direct positive-natural-number
  statement with five distinct divisors in the strict real interval.
- `FiveDivisors.five_divisor_lower_bound`: an existential positive C, with
  witness 31, for the floor/ceiling finite divisor-count convention.
- `FiveDivisors.four_not_greatest`: the negation of the `IsGreatest ... 4`
  proposition in [Formal Conjectures #887 at c252a410](https://github.com/google-deepmind/formal-conjectures/blob/c252a41054125b5fd9c8356e2137cd9b55337657/FormalConjectures/ErdosProblems/887.lean).

The latter two use the same `Infinite` subtype convention as that source.
The project imports Mathlib only. It does not assume any of the unproved
conjectures or introduce a problem-specific axiom. The universal upper-bound
question in JSP-000738 remains outside the proved result. Neither optimality
of C=31 nor exactly five total divisors is asserted.

### Fixed source and externally hosted evidence

- [Source repository at fixed commit](https://github.com/Rogerhu12/erdos887-five-divisors/tree/e26c3fdba882e230839046c95ca3af9a6050a030):
  `e26c3fdba882e230839046c95ca3af9a6050a030`.
- [Lean source](https://github.com/Rogerhu12/erdos887-five-divisors/blob/e26c3fdba882e230839046c95ca3af9a6050a030/FiveDivisors.lean),
  SHA-256 `63cd854393898b7da42f25cc9a7052f67faccd4d3c4e4fcd3e087da6c01e953c`,
  **10,918 bytes**.
- [Release v0.1.0](https://github.com/Rogerhu12/erdos887-five-divisors/releases/tag/v0.1.0),
  release ID `390443205`.
- [Source and evidence archive](https://github.com/Rogerhu12/erdos887-five-divisors/releases/download/v0.1.0/Erdos887FiveDivisors-v0.1.0.zip),
  asset ID `569490258`, **18,531 bytes**, SHA-256
  `d638b142f630721f9f7e7be4aed0d5c02e754e9c09890109932d0eba7d7055a6`.
- [Reproduction instructions](https://github.com/Rogerhu12/erdos887-five-divisors/blob/e26c3fdba882e230839046c95ca3af9a6050a030/README.md),
  [verification record](https://github.com/Rogerhu12/erdos887-five-divisors/blob/e26c3fdba882e230839046c95ca3af9a6050a030/verification.json),
  [axiom log](https://github.com/Rogerhu12/erdos887-five-divisors/blob/e26c3fdba882e230839046c95ca3af9a6050a030/verification.log),
  and [hosted reproduction run](https://github.com/Rogerhu12/erdos887-five-divisors/actions/runs/35183894524).

The archive contains all 14 tracked files from the fixed commit. It is hosted
on GitHub; an immutable-release setting, DOI or independent permanent archive
is not asserted. The hash and byte count identify the submitted artifact.
The published asset was downloaded again and its size, SHA-256 and embedded
Lean source hash were checked against the local archive and source.

The source uses Lean `leanprover/lean4:v4.33.0` and Mathlib
`db584cd6d46c92f209a44c0f1c829460d327499d`; all dependencies are locked.
The submitted local evidence records compiler exit code 0, no warnings, and
transitive axiom lists for all three roots containing only `propext`,
`Classical.choice` and `Quot.sound`. The proof has no `sorry`, `admit`, custom
axioms or `native_decide`. Local source elaboration used compiled dependency
caches after checking their source revisions. No fresh dependency rebuild,
separate checker implementation or independent human review is claimed.
The hosted Ubuntu workflow separately built the project and repeated fresh
elaboration and the three axiom checks successfully on 17 September 2026
(run 35183894524, completed at 05:00:00 UTC). It used the Mathlib dependency
cache and is a reproducibility check, not independent mathematical review.

### Duplicate and priority review

The [dated prior-work audit](https://github.com/Rogerhu12/erdos887-five-divisors/blob/e26c3fdba882e230839046c95ca3af9a6050a030/PRIOR_WORK.md)
records the searches and inspected sources. Before this submission, award-repository
searches for JSP-000738, 887 and the five-divisor phrase found no matching record.

- [Award PR 450](https://github.com/TheJustinSunPrize/awards/pull/450) concerns
  JSP-000737 / Erdős 886 and an upper bound depending on C, not this five-divisor
  infinite-family lower bound.
- [Formal Conjectures PR 3631](https://github.com/google-deepmind/formal-conjectures/pull/3631)
  fixes statements. [PR 3232](https://github.com/google-deepmind/formal-conjectures/pull/3232)
  and [PR 2710](https://github.com/google-deepmind/formal-conjectures/pull/2710)
  change annotations but leave the claimed proof as `sorry`.
- [jarekkoch-hub/erdos887-lean at 230bf2c](https://github.com/jarekkoch-hub/erdos887-lean/blob/230bf2cd0bc15f971ad9d0e36f36f2056dd9d8b7/Erdos887/Formalization.lean)
  contains a four-divisor infinite-family endpoint with C=64. Its upper and
  sharpness endpoints take an `ExternalReconstructionSource` parameter.
- The audit also records axiom-based files, statement copies and benchmark
  wrappers, as well as another ordinary five-divisor construction report.

No complete unconditional Lean implementation of the same five-divisor conclusion
was located among the inspected public sources. This is a limited search result,
not proof of global priority; the related projects were not independently rebuilt.

### Review status and conflicts

This is a self-submission of an AI-assisted formalization produced with Codex.
Ordinary mathematical discovery credit remains with the cited author.
Recipient identity stays `RECIPIENT-JSP-000738-LEAN-A` pending confirmation.
No registered curator, verifier or independent-reviewer role is asserted.

The candidate remains `draft`, with problem resolution, decision, batch and
official verification fields null. A formal-channel statement, authorized
attestations, recipient confirmation, priority and eligibility remain for the
repository's review process. Repository validation checks record structure;
it does not certify mathematics or authorize an award.
