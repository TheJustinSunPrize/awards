# Attribution and bounded prior-art screening

Screened on 2026-09-16. This is evidence for review, not proof of global priority.

## Contribution attribution

- **Mathematics:** Monier (1985), the factorial upper bound. No solver-role
  credit is requested. Erdős and Selfridge posed the problem. Cambie's stronger
  bound is acknowledged but not proved in this package.
- **Statement definition:** The Formal Conjectures Authors, copyright 2026,
  Apache-2.0; see [NOTICE](NOTICE) and [LICENSE](LICENSE).
- **Lean implementation:** Newly written for this submission by the applicant
  with ChatGPT assistance. No existing proof implementation was copied.

## Inspected public sources

| Source | Observed scope at the pinned revision |
| --- | --- |
| [Formal Conjectures](https://github.com/google-deepmind/formal-conjectures/blob/40e7c98697de6f66b8cbdbf641749ab39ed9c152/FormalConjectures/ErdosProblems/1063.lean) | `monier_upper_bound` remains `by sorry`; small threshold values are proved. |
| [lean-genius](https://github.com/rjwalters/lean-genius/blob/dc62f771ed5010abfdb04247dff6143e0e69d3e7/proofs/Proofs/Erdos1063Problem.lean) | `monier_factorial_bound` is a custom axiom; its existence/summary theorems depend on that axiom. |
| [fc100](https://github.com/Paul-Lez/fc100/blob/4b48458754b42299b09af16590db56abe9ace268/FC100Solved/ErdosProblems/1063.lean) | The Monier bound is still `by sorry`, despite the directory name. |
| [FormalConjectures-Bench target](https://github.com/AllenGrahamHart/FormalConjectures-Bench/blob/0d031f7212150df788f4fa38c26cfc3fc729f3d0/tasks-v2/erdosproblems-1063-monier-upper-bound/tests/golden_env/FormalConjecturesBench/Target.lean) | The target is still `by sorry`; it is a task statement, not an existing completed proof. |
| [Erdős problem discussion](https://www.erdosproblems.com/forum/thread/1063) | Identifies Monier's bound and Cambie's stronger bound; a formalized statement is not itself a proof. |

The recursive tree of `plby/lean-proofs` at
`8822f7ddef30fadbd92e1c6ab4ed897af356af5e` had no Erdos1063 module.
GitHub code searches for `monier_upper_bound`, `monier_factorial_bound`, and
additional `1063` Lean files did not identify a complete prior proof of this
bound in the inspected results. Benchmark declarations alone do not establish
complete proofs; search indexing may be incomplete. No claim is made that all
public or unpublished work has been exhausted.

The initial official repository snapshot contained 54 issues/PRs. The final
pre-submission snapshot contained 55 records (fewer than the 100-item page size). Searches of their titles and bodies found no `JSP-000883`,
`1063`, or `Monier` submission; see [the timestamped screening record](evidence/submission-screen.json).
The catalogue records Lean `No` and eligible to
claim `No`; neither field independently establishes eligibility or priority.

Because the main mathematical problem remains open and the bound is old,
eligibility of this newly completed partial-result formalization is explicitly
requested for adjudication rather than assumed. No tier or payment is promised.
