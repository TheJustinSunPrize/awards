> Historical receipt for the initial package at commit `546e5b052fef4a87a0853501c46ed36df2eed402`. Source-identity statements below refer to that historical snapshot, not the current supplemented package.

# Verification receipt: JSP-000212

## Tested source

- Proof commit: `5a44bae1b7d4a8a70d1f8594e26688f251f0b9e0`.
- [Source project at that commit](https://github.com/ketianzhang1-lang/jsp-000301-lean/tree/5a44bae1b7d4a8a70d1f8594e26688f251f0b9e0/projects/jsp-000212).
- [Workflow at that commit](https://github.com/ketianzhang1-lang/jsp-000301-lean/blob/5a44bae1b7d4a8a70d1f8594e26688f251f0b9e0/.github/workflows/jsp-000212.yml).
- [Successful run 35176592120](https://github.com/ketianzhang1-lang/jsp-000301-lean/actions/runs/35176592120), job `105059546166`, completed 2026-09-17 UTC.
- The Lean sources, build configuration, lockfile, license and verification scripts in this submission are byte-identical to the tested project. Its README is retained here as PROOF.md. The submission README, this receipt and evidence copies were added afterwards.

## Observed results

| Check | Observed result |
| --- | --- |
| Lean 4.34.0 / pinned Mathlib | Installed; all locked dependency revisions matched |
| Build with warnings as errors | Passed, including BoseChowla and Audit |
| Bundled Lean checker replay | Both BoseChowla and Audit passed |
| Five theorem axiom closures | Each used only propext, Classical.choice, Quot.sound |
| False arithmetic negative control | The attempted proof of 1 = 0 was rejected |
| Independent NaNoda replay | Checked 23881 declarations with no errors |
| Evidence upload | 15 files uploaded successfully |

The five axiom targets are `product_injective`, `sub_ne_zero`,
`exists_exponent_family`, `exists_bose_chowla` and `jsp000212`, all in the
`BoseChowla` namespace. The final two theorems and their complete exported
dependency closure were replayed by NaNoda with unpermitted axioms treated
as hard errors. Its output was:

```text
2026-09-17T03:03:57.4260951Z Checked 23881 declarations with no errors
```

The decoded public GitHub job log was retrieved and preserved verbatim,
apart from removal of its leading Unicode byte-order mark, in
[evidence/github-job.log](evidence/github-job.log). The response of the
GitHub artifact-list API is preserved in
[evidence/artifacts.json](evidence/artifacts.json).

## Artifact receipt

- Artifact: [jsp-000212-evidence](https://github.com/ketianzhang1-lang/jsp-000301-lean/actions/runs/35176592120/artifacts/10479116479).
- ID: `10479116479`.
- Size reported by GitHub: `20915410` bytes.
- ZIP SHA-256 reported by GitHub: `6d0ba1e301e8d48af1073c78a298c3aac4ac19363d54c024c6e3170a0cca2272`.
- Expiration reported by GitHub: `2026-12-16T03:01:21Z`.

The workflow includes the tested source archive, lockfile, axiom log,
kernel replay logs, negative-control log, NaNoda output and statements,
compressed exported proof, configuration and checksums. The ZIP digest
above is API-reported; it was not independently recomputed on a downloaded
ZIP in this session. GitHub Actions artifacts have finite retention and
this receipt does not assert permanent archival of the binary export.
The pinned source and scripts support regeneration.

## Limits and outstanding review

This is contributor-run verification. Mathlib compiled caches were used;
a complete Mathlib source rebuild is not asserted. Independent software
replay is not independent human verification. The intended theorem and
its relation to the open extremal problem still require reviewer judgment.

The submission establishes the finite construction for prime cardinalities.
It does not establish a new mathematical bound, a complete solution of
JSP-000212, all-prime-power or modular scope, global priority, designated
prize-verifier acceptance, recipient confirmation or prize entitlement.
