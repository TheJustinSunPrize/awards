# JSP-000360 / Erdos #441: unbounded additive improvement

This Lean project proves that Erdos's standard lcm-bounded construction can be
extended by **any prescribed number of elements**, at arbitrarily large bounds.
It formalizes a qualitative consequence of Chen and Dai's known result; it does
not claim a new mathematical discovery or the full sharp asymptotic formula.

The final theorem `JSP000360.unbounded_extension` states, for every r,M in the
natural numbers, that some N>=M admits a finite admissible set containing the
standard construction with exactly r additional elements.

## Reproduce

Install Lean through elan, Git, and a working HTTPS connection. In this directory:

```sh
lake exe cache get Mathlib.Data.Nat.Factorial.Basic Mathlib.Data.Nat.GCD.Basic Mathlib.Data.Finset.Card Mathlib.Tactic
lake build
lake env lean Audit.lean
```

The included `lake-manifest.json` locks every dependency. `lake update` is not
needed when reproducing this manifest. If regenerating it, the direct Mathlib
dependency is still pinned to the exact commit in `lakefile.toml`.

- Lean: 4.19.0, release commit 6caaee842e94.
- Lake: the version bundled with that Lean release.
- Mathlib: c44e0c8ee63ca166450922a373c7409c5d26b00b (v4.19.0).
- Local validation: Windows x86_64, 2026-09-17.
- `lake build`: passed.
- Final axioms: `propext`, `Classical.choice`, `Quot.sound`.

These are the standard logical axioms in the checked theorem. There is no
`sorryAx`, custom placeholder axiom, or compiled-evaluation axiom in its axiom
list. The project proof does not use `sorry`, `admit`, or `native_decide`.

Windows note: an ASCII directory path is recommended for this Lean release's
auxiliary tools. The local run used ASCII junction paths to this project and its
dependencies. Official Mathlib cache files were reused; this was not a full
rebuild of Mathlib from source. No independent-machine reproduction is claimed.

## Files

- [Proof.lean](Proof.lean): complete formal proof.
- [Audit.lean](Audit.lean): final statement and axiom inspection.
- [PROOF.md](PROOF.md): mathematical construction and proof.
- [STATEMENT.md](STATEMENT.md): exact correspondence and scope.
- [SOURCES.md](SOURCES.md): original result and earlier formalization.
- [verification/build-log.txt](verification/build-log.txt): project build output.
- [verification/lean-check.txt](verification/lean-check.txt): direct source check.
- [verification/axioms.txt](verification/axioms.txt): audit of the built theorem.
- [verification/checksums.txt](verification/checksums.txt): SHA-256 file checksums.

## Contribution and submission status

The inspected earlier proof gives an infinite family with one extra element.
This project proves an unbounded number of extra elements using a factorial
recurrence. The mathematical source remains Chen and Dai (2007); AI assistance
was used to prepare this formalization and accompanying documents.

This is prepared submission evidence, not an accepted prize claim. No confirmed
recipient, award decision, eligibility change, independent review, or first
public timestamp is asserted. The official submission route and recognition of
this incremental formalization scope remain unconfirmed.
