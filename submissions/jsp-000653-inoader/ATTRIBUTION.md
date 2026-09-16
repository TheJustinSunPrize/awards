# Attribution and prior evidence

## Mathematical sources

1. Paul Erdős, *A survey of problems in combinatorial number theory* (1980),
   the source identified in the remarks to
   [Problem 795](https://www.erdosproblems.com/795) for the stronger exact formula.
2. Rushil Raghavan, *Sharp Bounds for Sets with Distinct Subset Products*,
   [arXiv:2501.02695v2](https://arxiv.org/abs/2501.02695v2), 26 February 2026.
   Section 1 describes the prime-power exact-formula speculation and states a
   stronger asymptotic lower construction that disproves it. The falsity of
   the formula must be credited to this earlier work, not to this submission.

The explicit 48-bounded witness was found during this submission's integer
search. We make no claim that this particular witness, or an equivalent one,
has never appeared before. The Lean development was written for this submission
using the bundled Lean/Std library; no prior Erdős proof code was copied.

## Existing formal work disclosed

The public file
[plby/lean-proofs, Erdos795.lean, pinned revision 8822f7d](https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos795.lean)
contains a 6,678-line development of the asymptotic upper-bound result. Its
public final theorem `Erdos795.erdos_795` states that result. Its header attributes
the mathematics to Erdős and Raghavan and the formalization to Codex/GPT-5.6 Sol.
This submission does not contest or appropriate that work or its priority.

We also inspected
[rjwalters/lean-genius, Erdos795Problem.lean](https://github.com/rjwalters/lean-genius/blob/main/proofs/Proofs/Erdos795Problem.lean),
which contains incomplete statements of several related results.

The search included all 29 official award PRs returned on 16 September 2026,
earlier official issue records, the above prior sources, and GitHub code searches
for `Erdos795`, `erdos_795`, and `795 counterexample`. We did not identify a prior
formal proof of this exact-formula counterexample in the inspected material.
Search coverage is bounded: this is not a guarantee of novelty or priority, and
is not an independent validation of the other repositories' proofs.

## Present contribution

Human-AI collaborative formalization submitted through GitHub account `inoader`.
The code, witness search, and explanatory documents were produced with OpenAI
Codex. The applicant's formal recipient identity is left as
`RECIPIENT-JSP-000653-A` until the organizer confirms it.

No fixed award tier, allocation percentage, competing claimant's invalidity,
or first-solver status is asserted. The requested assessment concerns only this
new formal evidence for the explicitly delimited secondary conjecture.
