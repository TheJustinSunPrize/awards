# Finite-v2 verification record

Run ID: `06568604-a3fd-4fa2-a3d4-831c21267533`. Started at `2026-09-16T21:39:02.823349+00:00`.
Module: `Erdos882KorskyFinite`. Receipt phase: `complete`;
`local_checks_passed: true`.

This records actual local tool results for the expanded source snapshot.
It is not a designated organizer signature or an award determination.

## Checks and theorem scope

All **14 production modules** in the local import closure were freshly
compiled in this run. The fresh Lean kernel check (`leanchecker --fresh`),
theorem-closure export, and Nanoda run all exited **0**. Nanoda reports
**9,132 declarations checked with no errors**, prints all six
named theorem statements, and reports exactly the three standard axioms
`propext`, `Classical.choice`, and `Quot.sound`.

| Exported theorem | Actual Lean axiom dependencies |
|---|---|
| `Erdos882Korsky.korsky_sum_bound` | `propext, Classical.choice, Quot.sound` |
| `Erdos882Korsky.original_upper_bound` | `propext, Classical.choice, Quot.sound` |
| `Erdos882Korsky.korsky_deficit_bound` | `propext, Classical.choice, Quot.sound` |
| `Erdos882Korsky.korsky_finite_bound` | `propext, Classical.choice, Quot.sound` |
| `Erdos882Korsky.original_finite_bound` | `propext, Classical.choice, Quot.sound` |
| `Erdos882Korsky.original_threshold_bound` | `propext, Classical.choice, Quot.sound` |

Nanoda rejects unpermitted axioms and unknown requested declarations;
`unsafe_permit_all_axioms` is false. The portable configuration
[nanoda.json](nanoda.json) uses `verification/finite-v2/proof.ndjson`, relative
to the package root. It differs from the run configuration only in that path.

| Command | Exit code | Seconds |
|---|---|---|
| `compile-KorskyDefs` | 0 | 71.564 |
| `compile-KorskyCount` | 0 | 58.366 |
| `compile-KorskyInject` | 0 | 56.827 |
| `compile-KorskyModular` | 0 | 43.004 |
| `compile-Erdos882Original` | 0 | 31.552 |
| `compile-KorskyEndpoint` | 0 | 30.694 |
| `compile-Erdos882Korsky` | 0 | 59.698 |
| `compile-KorskyBalancedDefs` | 0 | 43.697 |
| `compile-KorskyBalancedCount` | 0 | 34.734 |
| `compile-KorskyBalancedLower` | 0 | 34.249 |
| `compile-KorskyBalancedUpper` | 0 | 26.039 |
| `compile-KorskyBalancedPacking` | 0 | 26.603 |
| `compile-KorskyFiniteEndpoint` | 0 | 26.635 |
| `compile-Erdos882KorskyFinite` | 0 | 31.319 |
| `leanchecker` | 0 | 257.995 |
| `export` | 0 | 27.626 |
| `nanoda` | 0 | 2.302 |

The [public receipt](verification.json) records all source and tool identities.
[Combined logs](check-logs.txt) retain every nonempty stdout/stderr stream,
redact local paths, and mark empty streams. Export stdout is the separate
`proof.ndjson` artifact, not repeated in the text log. The log manifest records
the original stream sizes and hashes before path redaction.

## Source and artifact identities

- Final module SHA-256: `6178662e8f02d47f047acd686db77f4bc172ad1262ed70fd6fada3f5dc54497c`.
- Final module bytes: 2,649.
- Export filename: `proof.ndjson`.
- Export SHA-256: `5a710a3e4fa610606afdbc2fd2171ed1315860d2ae43116010b3da4efdd83bf9`.
- Export bytes: 39,724,522.
- Dependency manifest SHA-256: `2a4ac093ff9e6f16d731b27021cbfcc6623a3da0a4ffb1777eab435de1f84d66`.
- Toolchain: `Lean (version 4.34.0, arm64-apple-darwin24.6.0, commit 293d5d0c0c3f3dded4688b3ccd6a33939ac5102b, Release)`.

Every packaged production source was checked against its hash in this
completed receipt before assembly. The source manifest covers the packaged
proof and environment files. The earlier evidence in the parent `verification/`
directory is preserved; it concerns the earlier theorem scope and run.

## Isolation and limitations

Each proof-check command used the macOS network-denial profile
`(version 1)(allow default)(deny network*)`. The unsandboxed control returned
`NETWORK_ACCESSIBLE`, exit **0**; the same probe under denial returned
`NETWORK_DENIED 1`, exit **73**. This establishes the applied network policy
for this run, rather than relying on an untested isolation claim.

**Filesystem access was not isolated.** Mathlib and other pinned dependencies
used existing compiled objects; they were **not rebuilt from source** in this
run. The local 14-module closure was freshly compiled. The independent Nanoda
check covers the exported declaration closure, not unrelated library content.

The earlier [baseline negative-control receipt](../negative-controls.json)
is preserved with its original scope. Both `NegativeControls.lean` and
`ExtensionNegativeControls.lean` passed a separate network-denied Lean run
(exit 0, no warnings). The [expanded control receipt](negative-controls-expanded.json)
records source hashes, actual commands, times, and outputs. The controls use
kernel-checked `decide`, without `native_decide`. The source-scope review is
automated and is distinct from independent kernel checking.

## Publication and archival status

`proof.ndjson` is included in the prepared local verification package. The
public PR contains the source, reproduction tool, small logs and receipts,
and exact export identity. Public availability of the large binary attachment
has not been confirmed. Permanent external archival remains **PENDING**;
`permanent_external_archive_confirmed` is **false**. Artifact identity is
evidence of content, not an archive receipt.

## Repository checks

The expanded submission passed `manage.py validate`, `links`, `build`,
`check`, and `history --base f4e7173d89dfe91022a185427d63452c8ffbf6ae`,
and all 22 repository validator tests. See [the actual receipt](repository-checks.json).
These checks concern repository records and structure, not mathematical
acceptance or prize payment.
