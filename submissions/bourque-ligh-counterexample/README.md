# Bourque–Ligh conjecture: formal verification of the published counterexample

This Lean development verifies the nine-element counterexample of
Pentti Haukkanen, Jun Wang and Juha Sillanpää to the Bourque–Ligh conjecture.
The mathematical result belongs to those authors. This submission contributes
its formal verification.

The conjecture asks whether the LCM matrix of every finite GCD-closed set of
distinct positive integers is nonsingular. The published counterexample is

```text
S = {1, 2, 3, 4, 5, 6, 10, 45, 180}.
```

The proof checks every hypothesis and constructs a nonzero vector annihilated
by the LCM matrix. It then derives a zero determinant and negates the original
universal conjecture. Both integer and real matrix formulations are included.

## Files

- [BourqueLigh.lean](BourqueLigh.lean): definitions and complete proof.
- [PROOF.md](PROOF.md): certificate and correspondence with the conjecture.
- [ATTRIBUTION.md](ATTRIBUTION.md): original sources and contribution attribution.
- [verification.json](verification.json): toolchain, check results and source digest.
- [dedup.json](dedup.json): submission and prior-formalization search record.
- [verify.py](verify.py): reproducible build, replay and axiom audit.

## Reproduce

Install Elan, then run in this directory:

```sh
lake exe cache get
python3 verify.py
```

The project pins Lean `v4.19.0` and Mathlib commit
`c44e0c8ee63ca166450922a373c7409c5d26b00b`.
The lockfile pins the transitive dependencies.
`verify.py` runs `lake build`, rechecks the source with `lake env lean`,
and checks the reported axiom dependencies. Logs are written to
`verification/local/`.

The final declarations use only `propext`, `Classical.choice`, and `Quot.sound`.
All finite computations use ordinary `decide`, which produces terms checked
by the Lean kernel.

## Submission

Recommended as a new problem for the Justin Sun Prize, with the existing
mathematical solution credited to Haukkanen, Wang and Sillanpää and this
formalization submitted for review. The proposed formalization recipient is
`RECIPIENT-BOURQUE-LIGH-A`, pending confirmation.

## License

The original Lean source and verification script are MIT licensed; the original
explanatory documentation is CC BY 4.0. See [LICENSE](LICENSE).
The cited papers retain their respective copyrights.
