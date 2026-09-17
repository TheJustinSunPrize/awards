# JSP-000254: verified five-eighths bound for the unit-fraction problem

## Request and scope

Please review a new Lean proof development of the known five-eighths construction
and the resulting negative answer to the one-half-density subquestion of
[JSP-000254](../../../problems/catalog-0201-0300.md#JSP-000254), corresponding to
[Erdős Problem 302](https://www.erdosproblems.com/302).

This is a **partial-scope contribution to the catalog problem**. It proves, for every
N, the lower bound f(N) >= 5 floor(N/8), where f(N) is the largest size of a subset
of {1,...,N} containing no three distinct a,b,c with 1/a = 1/b + 1/c. It then proves
the asymptotic five-eighths lower bound and that f(N)/N cannot converge to 1/2.
It does not determine the optimal density, prove existence of the limit, or prove
the recorded nine-tenths upper bound. No change to the full problem's status,
Lean flag, eligibility, candidates, awards, or payment records is requested.

## Attribution

The mathematical construction is due to **Stijn Cambie**, as credited in the
[fixed upstream statement](https://github.com/google-deepmind/formal-conjectures/blob/40e7c98697de6f66b8cbdbf641749ab39ed9c152/FormalConjectures/ErdosProblems/302.lean).
The definitions follow the Formal Conjectures Authors' Apache-2.0 source; attribution
and the license are retained. This submission claims the new formal proof scripts
and verification package for `RECIPIENT-JSP-000254-KZ-A`, submitting GitHub account
`ketianzhang1-lang`, prepared with OpenAI Codex assistance. It makes no original
mathematical discovery claim and no globally first formalization claim.

The submitter has an interest in assessment of this contribution. No recipient
identity confirmation or authorized prize-verifier signature is asserted.

## Fixed source and verification

- [Proof project at commit 54a0d8edb05945100ff151f70e8dc28870a45962](https://github.com/ketianzhang1-lang/jsp-000301-lean/tree/54a0d8edb05945100ff151f70e8dc28870a45962/projects/jsp-000254).
- [Lean source](https://github.com/ketianzhang1-lang/jsp-000301-lean/blob/54a0d8edb05945100ff151f70e8dc28870a45962/projects/jsp-000254/JSP000254.lean).
- [Pinned CI run](https://github.com/ketianzhang1-lang/jsp-000301-lean/actions/runs/35173758386).
- [Statement map](statement-map.md) and [machine-readable evidence](evidence.json).

Lean and Mathlib are pinned to v4.34.0, with exact package revisions in the lockfile.
Local compilation with warnings treated as errors, Lean kernel replay, and all
12 target axiom audits succeeded. The only reported axioms are `propext`,
`Classical.choice`, and `Quot.sound`. Cloud and independent-checker execution
results are recorded in the evidence file. Successful proof checking does not
constitute independent human statement review or an award decision.

To reproduce, check out the fixed source commit, enter `projects/jsp-000254`, and run:

```sh
lake exe cache get
bash scripts/verify.sh
bash scripts/verify_nanoda.sh
```

## Duplicate screening

On 2026-09-17, searches of the public awards issues and pull requests for the exact
catalog number and for `302` returned no matching submissions. Both claimed
upstream theorem bodies remain admitted in formal-conjectures commit
`40e7c98697de6f66b8cbdbf641749ab39ed9c152`. The reviewed plby/lean-proofs snapshot,
`8822f7ddef30fadbd92e1c6ab4ed897af356af5e`, has no `Erdos302.lean` file. These checks
are bounded evidence, not a guarantee of priority or the absence of proofs elsewhere.

The repository changes are documentation and evidence only. No live candidate or
award record is created, and there is no assertion of claim eligibility or payment.
