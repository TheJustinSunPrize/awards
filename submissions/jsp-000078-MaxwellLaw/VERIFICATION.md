# Verification record

## Statement checked

The compiled export is `Jsp000078.erdos_58`. The actual type printed by
Lean is recorded in [axioms.log](evidence/axioms.log): its vertex type is
arbitrary `Type u_1`, with no `Finite`, `Fintype`, countability, or
nonemptiness assumption. It has the standard odd-cycle-length finiteness
and cardinality hypotheses, the chromatic upper bound, and both directions
of the complete-subgraph equality characterization.

`Jsp000078.oddCycleLengths_eq` checks that the finite proof's cycle definition
equals the unchanged Formal Conjectures definition. The final statement,
including the case `k=0`, matches the pinned source in [REFERENCES.md](REFERENCES.md).

## Observed checks

The final end-to-end verification completed at 2026-09-16T15:44:25.900237+00:00 (UTC).

- Lean `4.33.0`, release commit `d8b18978322de05a8f3dba51ef03cf5461676c17`.
- Mathlib `db584cd6d46c92f209a44c0f1c829460d327499d`; all transitive dependencies
  are pinned in [lake-manifest.json](lake-manifest.json).
- All 35 finite-proof modules compiled from the unchanged source files.
  The complete package, including the new general theorem, built successfully.
- The 36 attributed source files passed byte-count and SHA-256 checks.
  The standard-definition copy also matched the original Git blob
  `08b5da1a82f2e4ad251b18d4c94def8fc715f694`.
- [Audit.lean](Audit.lean) compiled successfully. The transitive axiom sets for
  the finite theorem, compactness theorem, extended-cardinality theorem, and
  final general theorem are exactly
  `propext`, `Classical.choice`, and `Quot.sound`.
  The definition bridge uses only `propext` and `Quot.sound`.
- No custom mathematical axioms, `sorryAx`, or compiler-trust reduction axioms
  occur in these axiom reports. No `sorry`, `admit`, or `native_decide`
  occurs in the submitted mathematical modules.
- Batch kernel replay passed for **3,197 declarations from all 39 mathematical modules**.
  The initial environment contained Mathlib only, with no project theorem preloaded.
  Every collected declaration passed the unsafe/partial, custom-axiom, and name-overlap guards.
- Upstream repository validation, Markdown links, immutable-history check,
  deterministic data generation/check, and all **22** unit tests passed.

## Evidence and reproduction

Run `lake exe cache get` and then `python3 verify.py` from this package.
The script checks source identity, builds, checks the axiom allowlist, and replays
the declarations from all 39 mathematical modules into a Mathlib-only environment. It saves actual command exits, timings, source hashes,
and outputs under the ignored `logs/` directory.

Public evidence copies (artifact IDs, SHA-256 hashes, and byte counts are in
[artifacts.json](evidence/artifacts.json)):

- [Toolchain](evidence/toolchain.log) and [source identity](evidence/sources.log).
- [Initial source-build log](evidence/initial-build.log). This records the
  successful finite-module compilations and an initial arithmetic-simplification
  elaboration error in the new general module.
- [Subsequent successful complete build](evidence/successful-build.log), after
  adding the required `one_add_one_eq_two` rewrite. The finite source stayed unchanged.
- [Final verification build](evidence/build.log) and [axiom/type audit](evidence/axioms.log).
- [Full kernel replay](evidence/replay.log), [actual command records](evidence/commands.json),
  and [verification summary with source hashes](evidence/verification-summary.json).
- [Repository validation](evidence/awards-validate.log), [Markdown links](evidence/awards-links.log),
  [immutable history](evidence/awards-history.log), [data build](evidence/awards-build.log),
  [data consistency](evidence/awards-check.log), and [22 unit tests](evidence/awards-tests.log).

The published build-log copies replace only the local absolute workspace prefix
with `<WORKSPACE>`; unredacted originals are retained locally. No successful
exit or axiom result is inferred from an unsuccessful command. Lake's
“Replayed” build messages mean reuse of cached build logs; they are distinct
from the separate kernel replay performed by [ReplayBatch.lean](ReplayBatch.lean).

## Verification scope

Official dependency caches were used for Mathlib and its dependencies. All
vendored and new mathematical source modules were compiled locally. The final
verification build reuses these local outputs when their hashes are unchanged.

[ReplayBatch.lean](ReplayBatch.lean) adapts the official Lean 4.33.0 module-data
loading logic to collect the exported, server, and private declarations of all
39 modules. It invokes the unchanged `Lean.Environment.replay` API once, against
an environment importing Mathlib only. This avoids reloading common dependencies;
none of the project's own theorems is accepted as a trusted imported premise.
The kernel checks declarations in dependency order and checks constructors and
recursors against the regenerated inductive definitions.

The driver rejects unsafe or partial declarations (which the underlying API
would otherwise skip), new axioms, and any overlapping declaration names.
The verification script also checks the exact list of collected modules and the
successful declaration/module counts.

[Replay.lean](Replay.lean) additionally retains the original single-module
`replayFromImports` routine unchanged as an optional per-module tool. Selected
modules were checked with it during development; the complete published replay
record is the batch run.

Both methods use the **same Lean kernel**. This is not a fresh replay of all
Mathlib declarations, a separately implemented verifier, an independent human
referee report, or an official prize verification decision.

The utility itself uses Lean's `unsafe` environment API, as the official
checker does. It is not imported by any mathematical module and creates no
mathematical assumptions. Its original authors and adaptation are credited in
[REFERENCES.md](REFERENCES.md).
