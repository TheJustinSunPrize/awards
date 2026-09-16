# Local verification evidence

These files record the final local check performed on 2026-09-16. They are
reproducibility aids, not independent verification and not an award decision.

Environment:

- Lean 4.34.0, commit `293d5d0c0c3f3dded4688b3ccd6a33939ac5102b`
- Lake 5.0.0
- mathlib commit `5ed2965256430c3649e86755f9576b54eca72435`
- Linux `aarch64`

Commands:

```sh
lake build -KwarningAsError=true
lake env lean Audit.lean
```

The build completed successfully (1,214 jobs). The axiom output is preserved
in `axioms.txt`; hashes of the checked first-party Lean files are in
`SHA256SUMS`.
