# Verification receipt

Proof repository: `ketianzhang1-lang/jsp-000301-lean`.

Pinned source: `a197ebc6cc3ea878c60db0f2456465cef1e8e09b`, directory
`projects/jsp-000725`.

[Exact source](https://github.com/ketianzhang1-lang/jsp-000301-lean/tree/a197ebc6cc3ea878c60db0f2456465cef1e8e09b/projects/jsp-000725)

[Verification workflow](https://github.com/ketianzhang1-lang/jsp-000301-lean/actions/runs/35169441697)

Toolchain: Lean 4.34.0; Mathlib revision
`5ed2965256430c3649e86755f9576b54eca72435`.
The complete transitive dependency manifest is included.

## Actual public CI result

Run `35169441697`, job `105037686870`, completed successfully on
2026-09-17 at 01:11 UTC against the exact pinned source above.

- `lake build --wfail`: passed (3093 jobs, including cached dependencies).
- `leanchecker --verbose JSP000725`: passed; reported `replaying JSP000725`.
- All ten declaration audits: exactly `propext`, `Classical.choice`, `Quot.sound`.
- The Python standard-axiom allowlist: passed.
- The deliberately false arithmetic statement was rejected as required.
- The dependency manifest remained unchanged.

Unmodified compact CI outputs are under `evidence/ci/`. The negative-control
log contains the expected error; it is not a proof failure. Source digest:
`a3c0add755c8df4967e688693e7024610965b623d803127abbf72b287f6b1e2a`.

GitHub artifact `10475622589` contains these six files. The downloaded ZIP was
checked to be 1218 bytes with SHA-256
`05bcad81ccce1d058b5fbc3ec81e5c9c8ad6697a3074b3cfbb5881969b7ab3d5`.
Its advertised expiry is 2026-12-16. The extracted text files are also committed
here so the compact evidence is not available only through that expiring ZIP.

An earlier workflow attempted a full empty-environment dependency replay.
That broader attempt is not evidence claimed by this receipt. The final
workflow deliberately uses the documented target-module replay above.

## Scope and limits

The included source and setup files are byte-for-byte copies of the pinned
project. `SOURCE_MANIFEST.json` records their SHA-256 hashes and byte counts.
The standalone `finite_check.py` checks the documented interpretation by a
different implementation for N=0,...,40 and the boundary witnesses for t=2,...,30.
The diagnostic is not the universal proof and is not used by Lean.

The developer environment used cached Mathlib objects and a compatibility
wrapper for Lean's executable-path lookup. The public workflow uses the normal
official toolchain on GitHub's Ubuntu runner. Independent review should rely
on the pinned source and reproduce the public workflow.

Kernel replay checks the target module against the imported pinned Mathlib
environment using Lean's own implementation. The dependency library is not
replayed from an empty environment. No independent checker such as
NaNoda, isolated rebuild of every dependency, independent human sign-off,
organizer approval, or archival certification is asserted.

GitHub artifacts have finite retention. Permanent proof-source links and
compact evidence are provided in the repository, but are not represented as
independent permanent archival.

## Repository checks

The official repository's 22 unit tests and its validate, links, build, check,
and history commands passed against base
`f4e7173d89dfe91022a185427d63452c8ffbf6ae`. These validate the public record
infrastructure; they do not prove the theorem or establish award eligibility.

All proposed changes are new files under `docs/submissions/jsp-000725-kz/`.
No catalog flags, candidates, awards, recipient records, schemas, tests or
verification requirements are changed. The submission directory is proposed
evidence intake, consistent with prior submissions; placement remains subject
to maintainer review.

The repository-command transcript has only its terminal blank line removed.
The six extracted CI artifact files are unmodified.
