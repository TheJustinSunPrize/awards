# Verification evidence

Verified 2026-09-17 on Linux aarch64 with Lean 4.34.0
(commit `293d5d0c0c3f3dded4688b3ccd6a33939ac5102b`) and Lake 5.0.0.
Mathlib is pinned to `5ed2965256430c3649e86755f9576b54eca72435`;
all transitive dependencies are pinned in `lake-manifest.json`.

## Local checks

```sh
lake build -KwarningAsError=true
lake env lean -DwarningAsError=true Audit.lean
sha256sum -c evidence/SHA256SUMS
```

The project build and audit passed. The four audited declarations are
`sphere_grid`, `configuration_every_size`, `eventually_many_pairs`, and
`erdos605`. Each depends only on `propext`, `Classical.choice`, and `Quot.sound`.
See [axioms.txt](axioms.txt), [build.log](build.log), and [SHA256SUMS](SHA256SUMS).
The hashes cover every first-party Lean file and the toolchain/Lake manifests.

First-party source scanning found no `sorry`, `admit`, `unsafe`, `native_decide`,
or custom axiom declarations. Source and documentation were also scanned for
local home-directory paths, credentials, and private contact information.

## Clean-project reproduction

A separate directory was populated without `.lake` or `.git`. Lake cloned the
pinned dependencies afresh, then restored upstream compiled Mathlib caches.
No development-directory symlink was used in this reproduction. All first-party
modules were rebuilt and the same axiom audit was run. See
[clean-build.log](clean-build.log) and [clean-axioms.txt](clean-axioms.txt).

This is a clean-project check on the same machine and toolchain. It uses the
upstream binary dependency cache and is not an independent checker, full
from-source reconstruction of Mathlib, or independent human verification.

## Host repository checks

The evidence package was also tested in a separate worktree of
`TheJustinSunPrize/awards` based on `f4e7173d89dfe91022a185427d63452c8ffbf6ae`:

```sh
python scripts/manage.py validate
python scripts/manage.py links
python scripts/manage.py build
python scripts/manage.py check
python -m unittest discover -s tests -v
```

All four commands and all 22 unit tests passed. No existing catalog or generated
data file changed. These checks validate repository records, not Lean mathematics.

## Review and limitations

A separate Codex agent read the six proof modules and found no definition or
scope issues; this remains AI-assisted review within the same task. No human
review or organizer verification has been completed.

The earlier complete proof and official Issue 16 are disclosed in
[STATEMENT.md](../STATEMENT.md). This package does not establish first
formalization, priority, eligibility, payment, or an award.
