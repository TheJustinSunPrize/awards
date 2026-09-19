# Verification record for review

Proof source: [95a9bf8f203ce4dae381dd5db81bf8a1a1f6d54b](https://github.com/ketianzhang1-lang/jsp-000301-lean/tree/95a9bf8f203ce4dae381dd5db81bf8a1a1f6d54b/projects/jsp-000392).

Proof CI: [run 35168627081](https://github.com/ketianzhang1-lang/jsp-000301-lean/actions/runs/35168627081).

## Local checks observed

The exact proof source compiled successfully with Lean 4.34.0. Its SHA-256 is
`ef3bb79ad86ca9df5293b53438726e5e01934e7bf9cdc59f6632551aa5ff675c`.
All twelve target axiom audits passed: eleven depend only on `propext` and
`Quot.sound`; `colorable_not_forces` depends on no axioms.

The official awards repository's validate, links, build, check, history checks
and all 22 unit tests passed against base
`f4e7173d89dfe91022a185427d63452c8ffbf6ae`. Only this submission directory is
added. The eleven copied project files match the pinned proof project exactly.

## Cloud checks

All cloud steps passed on 2026-09-17 UTC: `lake build --wfail` (3,093 jobs),
bundled Lean kernel replay, all twelve target axiom audits, actual dependency
revision checks, and rejection of the false statement `1=0`. Strict-allowlist
NaNoda checked **1,840 declarations with no errors**, including the complete
seed, construction, quantified family and Ramsey reduction dependency closures.

Artifact ID: `10476226174`, 996,130 bytes. ZIP SHA-256:
`3d4a02bc763d7da794503e6d890f59b145a12b704e6bc6ae751fd3e37b18be97`.
Its reported expiration is 2026-12-16T00:57:22Z.
[Download through the successful CI run](https://github.com/ketianzhang1-lang/jsp-000301-lean/actions/runs/35168627081/artifacts/10476226174).
The downloaded ZIP hash and inner source-archive hash were verified, and all
project files were compared byte-for-byte with that actually tested archive.
Compact actual logs and checker configuration are included in `evidence/`;
AXIOM_AUDIT.txt is the actual cloud transcript. Full exporter data and the
source tarball remain in the external artifact; the checksum files identify
those external files, which are not duplicated in this submission directory.

## Reproduction and limitations

Lean 4.34.0; Mathlib commit
`5ed2965256430c3649e86755f9576b54eca72435`; all transitive dependencies are fixed
in lake-manifest.json and their checked-out revisions are asserted by verify.sh.
The independent checker uses lean4export
`6cea97789dc088ea47fcea15692db85685aedac5` and NaNoda
`4c544ed4099c8227f07d5de77ad1e69fb0740a27`.

An earlier CI run, [35168535500](https://github.com/ketianzhang1-lang/jsp-000301-lean/actions/runs/35168535500),
successfully built and replayed the proof but its audit parser failed to
recognize Lean's axiom-free output wording. The final source changes only that
parser to explicitly recognize the axiom-free case; the mathematical source
is unchanged. No error is silently ignored.

The environment uses network access and precompiled Mathlib caches. These are
contributor-operated checks, not independent human certification, organizer
approval, a full dependency rebuild, or an isolated offline validation.
Safe-version approval, scope and attribution review, priority, recipient
confirmation, contribution eligibility and any award decision remain pending.
GitHub Actions artifacts have finite retention; pinned source and compact
verification evidence are committed, with artifact details recorded below.
