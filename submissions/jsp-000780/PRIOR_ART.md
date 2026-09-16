# Prior-art screening and attribution

Screening date: 2026-09-16. This is a bounded public search, not a proof of
global priority or an award decision.

## Mathematical credit

Nitaj proved the infinitude of coprime 3-powerful triples in 1995. Cohn's
1998 paper supplies a transformation and proves the stronger noncube
result. The present Lean proof uses Nitaj's seed and specializes Cohn's
transformation. Both retain mathematical credit. This application concerns
only the new formalization of the triples subquestion.

## Inspected formal sources

- [Formal Conjectures 939](https://github.com/google-deepmind/formal-conjectures/blob/40e7c98697de6f66b8cbdbf641749ab39ed9c152/FormalConjectures/ErdosProblems/939.lean): `erdos_939.variants.triples` ends in `sorry`.
- [lean-genius 939](https://github.com/rjwalters/lean-genius/blob/dc62f771ed5010abfdb04247dff6143e0e69d3e7/proofs/Proofs/Erdos939Problem.lean): defines the triples set and comments on Nitaj's result, but does not prove its infinitude.
- [erdos-ai 939](https://github.com/ryantuck/erdos-ai/blob/f32b2886f8f005d481533036d0af4fe36e8e48f7/conjectures/939.lean): describes the solved triples question in a comment; its higher-exponent theorem has a placeholder.
- [Archived Aristotle problem statement](https://github.com/kavanaghpatrick/aristotle-math-problems/blob/2425339a625bf9e9edef22efee04471db6562bcb/archive/old-submissions/batch_dec14_precise/erdos939_precise.lean): incomplete problem material, not a complete triples infinitude proof.
- The `plby/lean-proofs` tree at `8822f7ddef30fadbd92e1c6ab4ed897af356af5e` was screened for a corresponding Erdős 939 module; none was found.
- Public GitHub code searches for `erdos_939`, `erdos_939.variants.triples`, `939 triples`, and `Nitaj` were reviewed. Other returned hits were statements, adjacent problems, or incomplete developments.

## Important separate prior proof

The [original discussion](https://www.erdosproblems.com/forum/thread/939?order=oldest)
contains Liam Price's 2026-05-24 Lean playground link for the GPT-5.5 Pro
construction, formalized by Aristotle. Its declarations
`infinite_rpowerful_sums` and `infinite_rpowerful_sum_tuples` cover `r ≥ 6`.
That existing formalization is why this submission does **not** claim the
higher-exponent construction as a new contribution. It does not establish
the `r=3` triples result proved here.

## Official intake screening

The pre-submission public API snapshot contains all 59 issues/PRs through
number 59, including closed records. The only explicit mention of
JSP-000780 / Erdős 939 is [PR 7](https://github.com/TheJustinSunPrize/awards/pull/7),
which corrects a bibliography identifier, not a proof submission.
No competing triples proof submission was found in that snapshot.
The pinned official catalogue still lists Lean proof `No` and Eligible to
claim `No`; neither field is changed or treated as a guarantee of payment.

The applicant requests only the formal verifier role. Priority, whether a
2026 formalization of this previously solved subquestion qualifies, recipient
confirmation, tier, and amount remain for the designated reviewers.
