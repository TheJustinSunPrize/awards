# Verification evidence

## English

- Lean v4.34.0, commit `293d5d0c0c3f3dded4688b3ccd6a33939ac5102b`.
- Mathlib v4.34.0, commit `5ed2965256430c3649e86755f9576b54eca72435`.
- All transitive package revisions are fixed in `lake-manifest.json`.
- Main result: `Erdos1063.erdos_1063.better_upper` in `Submission.lean`.
- Axiom dependencies: `[propext, Classical.choice, Quot.sound]`.
- No `sorryAx`, custom axioms, `native_decide`, or external oracle in the
  final theorem's dependency chain.

The supplied script builds every module in this package, re-elaborates the
main statement for its axiom report, and replays all seven modules with
Lean's bundled `leanchecker`. The evidence is in `reproduction.log`.

Local environment: macOS arm64. Submitted modules were built in a separate
Lake project with new local build artifacts. Pinned dependency checkouts and
official Mathlib caches were reused from the research environment. This was
not a network-isolated clean-room run. No machine-local symlink, compiled
olean, cached dependency, credential, or private contact is included in the
source package.

`leanchecker` rechecks submitted declarations against imported Mathlib. It
uses Lean's own kernel and is not an independent implementation or an
independent person's verification. This is a self-submission; local checks
must not be represented as organizer approval or third-party attestation.

The theorem completes the explicitly displayed improved-upper target, with
the natural LCM and a real witness before taking the infimum. It does not
resolve the broader sharp-asymptotic problem. The original catalog remains
unchanged pending operator review.
