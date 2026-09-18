# Verification protocol

Environment: Lean `v4.34.0`; Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`.

Run `python3 scripts/verify.py` from an environment with `lake` on `PATH`.
It builds the delivered source, scans for proof placeholders and computation
shortcuts, checks the dependency pin, and audits the axiom closure of all four
main declarations. Only `propext`, `Classical.choice`, and `Quot.sound` are
allowed. The outputs are `build.log`, `axioms.log`, and `SHA256SUMS` here.

`core.cnf` and `core.lrat` are discovery evidence, not trusted proof inputs to
Lean. `schur_core.json` records the meaning of each of the 602 initial clauses.
The generated resolution proof uses explicit applications and classical
contradiction. Its correctness does not rely on believing the solver's UNSAT
exit code, the Python generator, or a native evaluator.

The initial development environment reused a prefetched, commit-locked
Mathlib dependency directory from another local proof project. This is not a
claim of recompiling all of Mathlib from source. The dependency directory and
all compiled outputs are excluded from the public repository. The manifest
and toolchain provide the portable dependency specification.

## Completed checks (2026-09-17)

- `lake build`: successful, 1,109 build jobs reported. Dependency jobs were
  reused from the pinned prefetched Mathlib cache; all delivered first-party
  modules were compiled during this run of development and final verification.
- The 39 generated proof fragments and their 9,697-lemma composition compiled.
- `resolution`, `independent_schur_triple_le_eighteen`, `erdos_895`, and
  `erdos_895_finite_interval` all have exactly the three allowed standard axioms.
- Source scan: no proof placeholders, declared axioms, unsafe code, native
  evaluation proof tactics, or generated computation axioms.
- Toolchain executable: Lean 4.34.0, commit
  `293d5d0c0c3f3dded4688b3ccd6a33939ac5102b`, Linux aarch64.
- Actual local Mathlib checkout matches the manifest's exact revision.
- Independent statement review: all 153 edge labels and 602 input-clause
  mappings were checked against their mathematical meanings; positivity,
  distinctness and the finite-interval transfer were reviewed.
- Local Markdown links checked; no missing targets.

These checks establish a complete formal proof of the stated mathematical
claim. They do not establish prize acceptance or adjudicate priority.
