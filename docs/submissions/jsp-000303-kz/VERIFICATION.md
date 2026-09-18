# Actual verification evidence

Verified proof commit: `8828e97f231afdd50556350b87660c16f5068a03` in
`ketianzhang1-lang/jsp-000301-lean`, project `projects/jsp-000303`.

[Successful contributor-run proof CI](https://github.com/ketianzhang1-lang/jsp-000301-lean/actions/runs/35171950685),
job `105045299333`, completed 2026-09-17 UTC on Ubuntu 24.04.

| Check | Actual result |
| --- | --- |
| Pinned Lean 4.34.0 / locked Mathlib 4.34.0 | Passed |
| `lake build --wfail` | Passed; 3094 build jobs |
| Bundled kernel replay of JSP000303 and Statement | Both passed |
| Eleven theorem axiom audits | Passed; each uses only a subset of propext, Classical.choice, Quot.sound |
| False arithmetic control | Rejected as required |
| Strict-allowlist NaNoda | Passed; 18,034 declarations checked with no errors |
| Published proof/configuration/workflow sources | All 15 Git blob hashes match local source bytes |
| Official repository validation, links, build and check | Passed locally |
| Official validator tests | All 22 passed locally |

The independent checker implementation is NaNoda, commit
`4c544ed4099c8227f07d5de77ad1e69fb0740a27`. The exporter is lean4export,
commit `6cea97789dc088ea47fcea15692db85685aedac5`. Both pins, exact commands,
all eleven roots and the strict axiom policy are in `scripts/verify_nanoda.sh`.
The proof run builds these tools from the pinned sources.

## External evidence artifact

[GitHub Actions artifact 10477740179](https://github.com/ketianzhang1-lang/jsp-000301-lean/actions/runs/35171950685/artifacts/10477740179)

- Name: `jsp-000303-evidence`.
- Size: **12,837,117 bytes**.
- SHA-256: `c7fb9de17f51bde804571eaf9977f3cdba7caa77561937d9d61941f6d293cf75`.
- Advertised expiry: **2026-12-16T01:48:10Z**.

The archive contains source, build/kernel/axiom/negative-control logs,
exported proof data, checker output and hashes. The ID, size, digest and
expiry above were returned by GitHub; the digest also appears in the
successful upload log. A local download attempt was denied with HTTP 403,
so independent local hashing or extraction of the ZIP is **not claimed**.
Source fidelity was checked separately against the pinned Git tree.

Compact evidence retained in this submission:

- `verification/ci-summary.log`: verbatim selected lines from the retrieved
  successful job log, retaining timestamps. The selection contains build,
  kernel, axiom, checker and artifact-upload results; it is not the full log.
- `verification/artifact-metadata.json`: actual GitHub artifact metadata.
- `verification/local-axioms.log`: complete local axiom/type output.
- `verification/source-comparison.log`: Git-blob source comparison result.
- `verification/repository-checks.log`: actual repository checks and 22 tests.

## Limits and required official review

These are contributor-run checks. NaNoda is an independently implemented
checker, not an independently administered or organizer-designated review.
The Lean replay uses the bundled kernel. Cached upstream dependencies and
network access were used; no full offline rebuild of all dependencies or
approved minimum-safe-version determination is claimed. The local runner
needed a host executable-location compatibility shim; remote Ubuntu CI
checked the published project without that shim.

The artifact has finite retention. This is not a permanent independently
administered archive. Compact logs remain in this contribution. Designated
statement review, contribution/overlap assessment, recipient confirmation,
eligibility and any award remain pending. Repository CI validates records
and is not itself mathematical verification or a payment authorization.
