# Actual verification and its limits

Version 0.2.1 includes the locally repaired, compiled proof. Its incoming archive
was not compiled. The supplied arithmetic repairs passed; two residue-hypothesis
normalizations and two real-type annotations were then needed. The precise
additional changes are in [LOCAL_REPAIRS.patch](lean/LOCAL_REPAIRS.patch).
No theorem statement, mathematical assumption or dependency pin was weakened.

## Successful final run

[Machine-readable result](lean/evidence/result.json) records all four completed
stages: arithmetic, finite construction, growth, and full asymptotics.
[The final audit](lean/evidence/audit-full.log) prints the inline original target
and the transitive axiom dependencies of all required results, including the
external `chebyshev_asymptotic` input.

- Lean 4.33.0; Mathlib `db584cd6d46c92f209a44c0f1c829460d327499d`.
- All nine package Git revisions match the committed manifest.
- All four original propositions are inhabited by actual typed proof terms.
- All audited theorems depend only on `propext`, `Classical.choice`, `Quot.sound`.
  No `sorryAx` or additional mathematical axiom appears.
- All nine pinned PNT source modules were downloaded, checked against Git blob
  identities, and compiled. The source bytes and original notices are retained.
- [Native leanchecker record](lean/evidence/leanchecker.actual.json) and
  [log](lean/evidence/leanchecker.actual.log): all 16 local/PNT modules replayed
  against their imported environments, exit code 0.
- [70 Python tests](lean/evidence/repaired-python-tests.actual.log) passed.
- The publication copy's 16 mathematical source files are byte-identical to the
  verified files; [hashes](lean/evidence/verified-source-files.json) are included.

The local run reused pinned Mathlib caches. It did not rebuild or replay all
Mathlib from source. The replay uses the same Lean kernel, not an independent
implementation. An additional combined-batch utility was attempted but stopped
on duplicate generated declarations before completion; the claimed successful
replay is the native per-module command above, not that batch attempt.

Public logs normalize local filesystem prefixes to `$PROJECT`,
`$DEPENDENCY_CACHE`, `$ELAN_HOME`, and `$LOCAL_HOME`. Log hashes in result.json
were recalculated after this path-only normalization; process outcomes and
mathematical output are preserved. These are self-produced local verification
receipts, not external verifier attestations.

## Historical numerical evidence

The original v0.1 [Python log](evidence/python-tests.log) and
[finite-check log](evidence/finite-checks.log) cover 18 tests and 1,454 eligible
pairs up to k=300. Those are historical finite experiments, not the reason the
universal theorem is now considered locally Lean-verified.

Official review, statement acceptance, novelty/priority and award eligibility
remain with the reviewers and organizer. PR #601 and its stronger-bound sources
are explicitly acknowledged. No official catalog or award record is changed.
