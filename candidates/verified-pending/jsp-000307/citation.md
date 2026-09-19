# Candidate citation: JSP-000307

## English

Do there exist consecutive integers with strictly decreasing largest prime factors? (Erdős problem, catalog JSP-000307.)

Status of this candidate record:

- Mathematical status: solved by explicit witness n=13 (P(13)=13, P(14)=7, P(15)=5 — strictly decreasing).
- Lean formalization: available (formalization contributor: Shiqiang Chen, independent researcher) in the public repository `github.com/shunfeng8421/jsp301-lean` at commit `37c490428c5892e9c9d53de54049cf500fa70bfb`, file `Jsp307.lean`.
- Eligible to claim: yes, subject to independent verification and review.

Witness-based proof (first public release 2026-09-17 04:35 UTC):

1. `Jsp307.lpf_13`, `lpf_14`, `lpf_15` establish the largest prime factors via the `IsLPF` predicate.
2. `Jsp307.JSP_307` assembles the decreasing chain P(13)=13 > P(14)=7 > P(15)=5 for consecutive integers 13,14,15.
3. Axiom audit reports exactly `[propext, Classical.choice, Quot.sound]`; no `sorry`/`admit`/`axiom`.

See `verification/record.yaml`, `verification/statement.yaml`, and `verification/build-current-release.log`.