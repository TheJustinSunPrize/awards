# Verification receipt: full bound and sharp stars

These are contributor-run machine checks, including an independent checker
implementation. They are not organizer approval or independent human review.
The original receipt remains in [INITIAL_VERIFICATION.md](INITIAL_VERIFICATION.md).

## Pinned source and successful execution

- [Proof commit 5f94d026ec88696bb5047506c433ad401e5f02ef](https://github.com/ketianzhang1-lang/jsp-000301-lean/tree/5f94d026ec88696bb5047506c433ad401e5f02ef/projects/jsp-000438).
- Proof Git tree: `dd661f4f29977c7944f20747b892fcf4991e82b0`.
- [Exact workflow](https://github.com/ketianzhang1-lang/jsp-000301-lean/blob/5f94d026ec88696bb5047506c433ad401e5f02ef/.github/workflows/jsp-000438.yml).
- [Successful run 35177382098](https://github.com/ketianzhang1-lang/jsp-000301-lean/actions/runs/35177382098).
- [Successful job 105061961050](https://github.com/ketianzhang1-lang/jsp-000301-lean/actions/runs/35177382098/job/105061961050).
- Checks completed 2026-09-17 UTC, with Lean 4.34.0 and Mathlib
  `5ed2965256430c3649e86755f9576b54eca72435`.

The 20 project files listed in [PROOF_SHA256SUMS](PROOF_SHA256SUMS) match the
checked proof commit byte-for-byte. The uploaded proof Git tree was compared
with the locally prepared tree and matched. The exact workflow is copied as
[PROOF_WORKFLOW.yml](PROOF_WORKFLOW.yml). Submission receipts, historical files
and the separate multicolor supplement are not part of that 20-file snapshot.

| Check | Observed result |
| --- | --- |
| Build with warnings treated as errors | Success; 3,139 build jobs |
| Bundled Lean checker replay | All four proof modules passed |
| Ten named axiom closures | Only `propext`, `Classical.choice`, `Quot.sound` |
| Actual dependency Git revisions against lockfile | All matched |
| Invalid arithmetic negative control (`1 = 0`) | Rejected as required |
| NaNoda strict-allowlist check | 11,276 declarations checked with no errors |
| Tested-source archive and evidence upload | Success |
| Full universal upper-bound target | Original statement and definitions retained |
| Exact sharpness target | Every natural k; star order 2k+2; Ramsey number 4k+2 |

The replayed modules are `Upstream548`, `RamseyDefinitions`, `JSP000438` and
`StarSharpness`. The original five audited targets are retained. The five new
targets are `sharpGraph_degree_le`, `sharpGraph_compl_degree_le`,
`sharpGraph_avoids_star`, `star_ramsey_even_order` and
`tree_ramsey_bound_is_sharp`, all in namespace `JSP000438`.
The original source modules and credited upstream proof are unchanged.

NaNoda is pinned at `4c544ed4099c8227f07d5de77ad1e69fb0740a27`, with
lean4export at `6cea97789dc088ea47fcea15692db85685aedac5`. All ten targets and
their dependency closures are exported. Every axiom outside the three-item
allowlist is rejected, including `sorryAx`. The run used an Ubuntu 24.04
hosted runner, network access and dependency caches.

Observed results are preserved in the [public log excerpt](evidence/sharp-log-excerpt.txt)
and [run status](evidence/sharp-run-status.json). The excerpt contains selected
lines, not the complete job log. Full logs are available through the linked run.

## External evidence artifact

[GitHub Actions artifact 10479581072](https://github.com/ketianzhang1-lang/jsp-000301-lean/actions/runs/35177382098/artifacts/10479581072)
contains tested source, the lockfile, build/checker/audit logs, negative-control
output, compressed dependency export, checker configuration and checksums.

| Field | Recorded service value |
| --- | --- |
| Name | `jsp-000438-sharp-evidence` |
| ZIP bytes | `8419347` |
| ZIP SHA-256 | `2d6482c1e9ac669bf7d1549ed7cfe559e102ca202a39ea82643eb7eba76afb65` |
| Created | `2026-09-17T03:17:14Z` |
| Reported expiry | `2026-12-16T03:13:52Z` |

The API metadata and upload log agree on the ID, byte count and digest
([metadata snapshot](evidence/sharp-artifact-metadata.json)). These are
service-reported values; the artifact ZIP digest has not been separately
recomputed locally. The external artifact has finite retention. Pinned source
and compact receipts remain in Git, and the committed scripts can reproduce
the checks independently of the artifact.

## Submission history and repository preflight

This is an update to existing organizer PR #408. Original receipts, source
hashes, workflow and review request remain in the `INITIAL_` files, and the
original logs remain in `evidence/`. The independently added
[finite-color supplement](supplements/multicolor/README.md) and its separate
verification receipt are preserved byte-for-byte from PR head
`6fd24e484966821113a2ad7c3c7cabaf63bb8ab4`. The 11,276-declaration check above
covers the full bound and sharp-star project, not a combined multicolor project.

Against official base `f4e7173d89dfe91022a185427d63452c8ffbf6ae`, the updated
submission passed record validation, Markdown links, deterministic data
generation, generated-data consistency, history preservation and all 22
repository tests. The change is confined to this submission directory.
These checks concern repository structure, not award eligibility or payment.
