# Verification report

Verified locally on 2026-09-17 UTC, macOS arm64, Lean 4.33.1.
This is local evidence, not an organizer decision or an independent implementation audit.

## Result and scope

The submitted theorem proves the exact known Formal Conjectures variant for every
natural length from 3 through 10. It uses the published 93-digit starting prime
and common difference 210. All ten terms are prime; every other integer in the
closed interval from the first to the last term is composite. Consecutiveness is
proved against `Nat.nth Nat.Prime`, with cardinality exactly the requested length.
No eleven-term, unbounded-length, or infinitude result is claimed.

## Successful checks

1. `lake --wfail build Erdos141FirstCases Erdos141FirstCases.Audit` completed
   successfully (1953 jobs) with the standard pinned manifest. `build.log`
   preserves the final successful output.
2. `lake env lean -E warning Erdos141FirstCases/Audit.lean` succeeded. The audit
   independently expands the two reference definitions, checks definitional
   equality, proves the exact expanded statement and exact closed interval,
   and reports all seven audited declarations in `statement-and-axioms.log`.
3. All seven transitive axiom sets contain only `propext`, `Classical.choice`,
   and `Quot.sound`. The submitted sources contain no proof placeholders,
   custom axioms, or native-evaluation proof shortcuts.
4. `lake env leanchecker --fresh -v Erdos141FirstCases.Audit` succeeded with
   exit code 0 in approximately 210 seconds. This replays the full imported
   environment through the bundled Lean kernel implementation. See
   `kernel-result.json` and `kernel-replay.log`.
5. All nine dependency Git revisions match the lockfile, with clean tracked
   worktrees (`dependency-pins.json`). Shared local build caches were used;
   no local overrides or filesystem links are part of the package.
6. Repository validation, local links, data generation, generated-data checks,
   all 22 unit tests, and the history check against official base
   `f4e7173d89dfe91022a185427d63452c8ffbf6ae` succeeded. The history result here
   is the pre-commit check; the final publication history is also checked
   before pushing. Repository checks do not certify mathematics.
7. The ten submitted Lean source files are byte-for-byte copies of the locally
   built and replayed sources. The package was checked for accidental private
   paths, credentials, personal contact information, and symlinks.

## Numerical certificate accounting

There are 372 distinct primality lemmas: 222 explicit-factor Lucas certificates
and 150 small-prime proofs. For the 1881 non-term offsets, 1838 have small proper
divisors and 43 have failed Fermat congruences. All these numerical claims are
checked by the submitted Lean proofs. External factorization hints are untrusted.

## Limits

The original mathematical construction is attributed in the README and NOTICE.
The prior-art search is bounded and does not establish priority or eligibility.
A successful build and kernel replay do not decide whether the contribution
meets the prize organizers' criteria. No award or payment is recorded.

`SHA256SUMS` covers every package file except itself.
