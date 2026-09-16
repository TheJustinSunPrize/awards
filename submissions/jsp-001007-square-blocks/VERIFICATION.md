# Verification evidence

## Executed by the submitter

On 2026-09-16 the unmodified repair-v2 Lean sources passed `bash run_checks.sh` on arm64 macOS 26.5.1 using Lean 4.33.1 and Mathlib commit `0df444a360eaa60ab8c11dca51a86af692955474`. The initial invocation supplied `--full`; this version's script has a single full-check mode and does not branch on that argument.

The run cloned pinned dependencies into a fresh project directory, used Mathlib's downloaded dependency cache, built the three local modules, directly compiled them for axiom reports, then compiled the standalone source with only a Mathlib import. Every compiler stage and audit returned success. The submitter reran the existing audit/gate tests on the public source copy.

## Evidence files

- [Native status](verification/native-status.json).
- [Verified source hashes](verification/verified-source-hashes.json).
- [Lean version](verification/lean-version.txt).
- [Module build log](verification/native-build.log).
- [Main compiler log](verification/lean-compile.log) and [main axiom reports](verification/lean-axioms.json).
- [PrimeBlocks compiler log](verification/prime-blocks-compile.log) and [axiom reports](verification/prime-blocks-axioms.json).
- [Arithmetic compiler log](verification/core-native-compile.log) and [axiom reports](verification/core-native-axioms.json).
- [Standalone compiler log](verification/standalone-compile.log) and [all 14 axiom reports](verification/standalone-axioms.json).
- [Finite witness check](verification/finite-witness.json), which is not Lean verification.
- [Audit and failure-path unit tests](verification/submission-tests.log), which do not prove the mathematics.

The two small files in `verification/wasm/` are historical fixtures required by existing audit tests. They are not used as current full-proof verification evidence. The test suite's fake compiler fixtures exercise rejection paths only; they are not passed off as Lean outputs.

## Limits of this evidence

All 14 reported dependencies are subsets of `{propext, Classical.choice, Quot.sound}`. There are no `sorryAx` dependencies. Style/deprecation warnings remain. Source hashes bind these claims to the exact submitted Lean files.

This is one submitter-operated native Lean toolchain, not two independent proof checkers. We have not run nanoda or another independent checker for this package. The run was not network-isolated, did not use an immutable container image, and used prebuilt Mathlib dependency artifacts. It does not assert the repository's completed formal-verification record requirements or a current minimum-safe-version review.

There are no curator statement signatures, independent human correspondence review, recipient confirmation, or award decision. The package is offered through a separate contribution intake PR. It does not create a record in `candidates/verified-pending`, announce an award, or assert a right to payment. The repository's formal candidate templates require evidence and attestations that cannot be supplied by relabeling these local build results.

The provenance record lists the received archive digest and the source-preservation checks. Source comments that refer to the repair author's earlier unverified environment are historical; the native logs above describe the subsequent actual reproduction.

## Published evidence archive

The [source and native evidence archive](https://github.com/randyxian08/awards/releases/download/jsp001007-square-blocks-v2/JSP001007_square_blocks_submission_v2.zip) contains the checked Lean sources and native logs. Proof source bytes match [commit a646fcebecd47b2030417b17952bab9693d590ee](https://github.com/randyxian08/awards/tree/a646fcebecd47b2030417b17952bab9693d590ee/submissions/jsp-001007-square-blocks). Archive-coordinate metadata is omitted inside the ZIP to avoid a self-hash dependency. Its SHA-256 is `b1a10f42600a15d19a54aac24cf2fcc170c8220a151312c0d56db45bb2cd1ea4` and size is 51284 bytes. See [artifact.json](verification/artifact.json) for coordinates. Hashes detect later asset changes; GitHub hosting is not a DOI archive or a prize verification decision.
