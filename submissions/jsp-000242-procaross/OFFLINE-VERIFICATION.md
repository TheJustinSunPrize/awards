# Offline review package

The complete export can be checked without Lean, Mathlib caches, compilation,
or network access once the pinned Nanoda binary is available. The proof sources
remain exactly those in commit `85f2a9b753f17697e3acc15c8f14a6b65b9b440c`.

## Archive

[Download release](https://github.com/procaross/awards/releases/tag/jsp-000242-offline-review-v1)

- Asset: `jsp-000242-85f2a9b753f1-offline-review.tar.gz`
- Size: 26,651,036 bytes
- SHA-256: `70c7a65c9c0691cd2f52f04ca76781d12035c1959d9ded4c4ecc3b847621e795`
- Internal manifest SHA-256: `1013f1be01e2668edc937276a81e676e1dc5869196697b9b7282c3d7d35bab74`

The deterministic archive contains 19 files: the full checked NDJSON export,
true/false control exports, the original 51-file source-package archive,
[offline_check.py](offline_check.py), a README, a self-excluding checksum
manifest, and license texts for the submission, Lean and the pinned dependencies.
It contains no checker executable, private paths, credentials, or build cache.
The main export retains SHA-256
`01fc575a9e19a3e3c7856f68d5eea40c6d2560e5e2977224a10ba4f1f3a15b1c`.

Build the unmodified checker from the source revision and lockfile specified in
[external-toolchain.json](external-toolchain.json) before going offline.
Python 3.10 or later is required for the wrapper. After unpacking, on macOS:

```sh
sandbox-exec -p '(version 1) (allow default) (deny network*)' \
  python3 offline_check.py --checker /absolute/path/to/nanoda_bin
```

Use an equivalent OS/container network policy on other platforms. The wrapper
does not itself establish isolation or certify the provenance of a supplied
checker binary. It records that binary's checksum for comparison with a trusted
build. The manifest checks occur before checker invocation. Results default to
`offline-results/`; use `--results` to choose a separate output directory.

## Recorded check

The exact archive was extracted into a new directory and checked under the OS
policy above. A loopback connection succeeded without the policy and failed
with `PermissionError` under it. The policy applied to the wrapper and its
child processes throughout checking.

- The main proof passed: **29,437 declarations**.
- The positive control passed.
- The deliberately false-type control was rejected by the definitional-equality
  assertion, exit 101. This file is an explicit negative test, not a proof claim.
- A separately altered artifact was rejected by the manifest check before any
  checker was invoked.

The first fresh-extraction attempt exposed the checker's requirement that its
pretty-printer output file already exist. The wrapper now creates that file;
the rebuilt archive passed the full fresh-extraction check. Failed-attempt
artifacts were retained locally. The mathematical source was not changed.

[Isolation evidence](verification/offline/isolation-evidence.json) binds the
archive, command, network probe and [actual checker report](verification/offline/offline-report.json).
The checker hash matches the previously recorded local Nanoda binary. The
axiom policy remains limited to `propext`, `Classical.choice`, and `Quot.sound`.

This strengthens reproducibility of the submitted proof. It remains a
contributor-run check on the same host, not an independently administered
organizer check, independent human review, a merge or an award decision.
