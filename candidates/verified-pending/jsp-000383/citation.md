# Candidate citation: JSP-000383

## English

Starting from a set of primes, can repeatedly adjoining prime sums of three
distinct existing primes generate infinitely many primes? (Erdős problem,
catalog JSP-000383; solved by Rudi Mrazović and Vjekoslav Kovač, independently
Noga Alon.)

Status of this candidate record:

- Mathematical status: solved (constructive closure argument).
- Lean formalization: available (formalization contributor: Shiqiang Chen,
  independent researcher) in the public repository
  `github.com/shunfeng8421/jsp301-lean` at commit
  `885fd813dc8f2e1e779a537095679cf2a4b2cb02`, file `Jsp383.lean`.
- Eligible to claim: yes, subject to independent verification and review.

Scoped constructive component (2026-09-18):

1. The 30-term adjoin chain `[19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,83,89,97,101,103,107,109,113,127,131,137,139,149,151,157]` is given.
2. `Jsp383.chain_is_legal_run` establishes the chain is 30 long, distinct, and every entry is prime.
3. Each adjoined value is the sum of three distinct already-present primes (e.g. 19=3+5+11, 23=5+7+11, 29=3+7+19), verified by `decide`.
4. Axiom audit reports exactly `[propext, Classical.choice, Quot.sound]`; no `sorry`/`admit`/`axiom`.

This component exhibits the constructive growth mechanism (5→35 primes) behind
the result. See `verification/record.yaml`, `verification/statement.yaml`, and
`verification/build-current-release.log`.