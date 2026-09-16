# Verification review

The submitted proof was repaired from a supplied Lean candidate and checked
with official Lean 4.19.0 on macOS arm64 on 2026-09-16.

## Repairs

Two elaboration failures in the original candidate were fixed:

1. In `colorable_mono`, the ambiguous `congrArg Fin.val hxy` was replaced by
   `congrArg (fun z : Fin k => z.val) hxy`.
2. A local `set_option synthInstance.maxSize 1024 in` was added immediately
   before `binary_obstruction` so instance synthesis can handle the nested
   finite quantifiers and conjunctions.

These repairs preserve the mathematical definitions, statements, edge list,
and coloring certificates. The publication copy also changes a comment's
review filename from the original Chinese report to this English report;
its proof is recompiled and its current source hash is recorded in the receipt.

## Actual checks

The reproduction script runs the 11 auxiliary positive/negative audit tests,
checks all 512 binary colorings, the explicit three-coloring, all 22 edge
removal certificates, all 9 vertex removal certificates, degrees, simplicity,
and correspondence between source literals and the finite data.
It then runs `lake clean`, `lake build`, and `lake env lean JSP690.lean`.

The axiom reports for the two main declarations are:

- `JSP690.JSP_000690`: `propext`, `Quot.sound`.
- `JSP690.JSP_000690_full`: `propext`, `Classical.choice`, `Quot.sound`.

The edge representation and non-monochromatic equivalence lemmas are also
audited. No admitted proofs, new mathematical axioms, or native-computation
axioms are used. The Python checks are supplementary and do not replace the
Lean proof. The source-bound receipt and compiler output are in
[verification/status.json](verification/status.json) and
[verification/lean-check.log](verification/lean-check.log).

## Limits

These are local, submitter-produced checks using the official Lean compiler.
No independently implemented second checker, independent human reviewer,
organizer verification, award decision, or formalization priority is claimed.
