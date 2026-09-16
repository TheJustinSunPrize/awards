# Verification evidence

Verification date: 2026-09-17 (Asia/Shanghai).

- Lean 4.34.0; Linux aarch64.
- Mathlib commit: `5ed2965256430c3649e86755f9576b54eca72435`.
- `lake build -KwarningAsError=true`: all 999 build jobs passed.
- `lake env lean Audit.lean`: six audited theorems use only
  `propext`, `Classical.choice`, and `Quot.sound`.
- `SHA256SUMS` fixes all first-party Lean sources, the toolchain, and manifests.
- The triangle and single-edge semantic checks are included in the normal build.

Development reused pre-fetched dependencies at the pinned revisions. The
independent reproduction starts from a fresh project directory with no project
build products and uses the same pre-fetched dependency directory. It verifies
that every first-party module rebuilds; it is not a fresh network download or an
independent third-party verification. The reproduction script and output are
included here.

These are local verification records. They do not establish award eligibility,
priority, or acceptance. Official repository CI checks record structure rather
than running external Lean proof projects.
