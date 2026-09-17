# Erdos 1063: a locally verified lcm-scale upper bound

Version 0.2.1 (local repairs), 17 September 2026. This continues PR #498 with a
complete Lean proof of the eventual bound `n_k <= 3*L_k`, where
`L_k = lcm(1,...,k-1)`, and the resulting `better_upper` Big-O/little-o target.
All four former proposition-only obligations now have compiled theorem proofs.

**Local verification passed:** Lean 4.33.0 compiled all project and pinned PNT
modules; exact-type checks and transitive axiom audits passed. The final axiom
set is `[propext, Classical.choice, Quot.sound]`. Lean's own checker replayed
all 16 local/PNT modules against their imports, with exit code 0.
This is not independent verifier attestation, a fresh replay of Mathlib, or
an award/priority determination.

## Review the proof and evidence

- [Lean project and reproduction commands](lean/README.md).
- [Exact final theorem](lean/JSP000883/Asymptotics.lean).
- [Verification scope and receipts](VERIFICATION.md).
- [Attribution](lean/docs/ATTRIBUTION.md) and [identified prior work](lean/docs/PRIOR_ART.md).
- [Versioned source/evidence release](https://github.com/randyxian08/awards/releases/tag/jsp000883-lean-v0.2.1).
- [Original v0.1 manuscript](MANUSCRIPT.md); the Lean proof uses an equivalent
  integer-product/coprimality route, with details in the Lean module comments.

## Scope and credit

The result provides actual witnesses for all sufficiently large k before
bounding the natural infimum. The LCM is computed in naturals before casting
to reals. It does not establish the sharp growth rate or fully settle the
original open-ended estimation question.

Related PR #601 submits a stronger bound and attributes earlier public research;
this submission does not claim first mathematical discovery or first verified
formalization of the broad target. Monier, Cambie, pcycho's formalization, the
PNT project, the plby port, and Mathlib retain their credited contributions.
The publishing account is `randyxian08`; work and verification were assisted by
ChatGPT/Codex. No legal recipient identity or award entitlement is asserted.

## Reproduce

From `lean/`, with Python 3.10+, Git and elan/Lake:

```sh
python3 scripts/check_integrity.py
python3 scripts/verify.py --prepare
lake env leanchecker --verbose JSP000883 PrimeNumberTheoremAnd
python3 -m unittest discover -s tests -v
```

All 70 Python tests passed. These tests are separate from the Lean proof checks.
The original finite experiment code remains in `src/`, `tests/`, and `scripts/`.

## Version history

The [v0.1 release](https://github.com/randyxian08/awards/releases/tag/jsp000883-research-v0.1) and its PDF remain unchanged as the historical
unrefereed, Lean-incomplete research note. The present source release adds the
compiled proof and evidence; it does not retroactively label v0.1 as verified.
`artifacts.json` retains both releases' asset hashes and sizes. See
[CHANGELOG.md](CHANGELOG.md), [NOTICE](NOTICE), and [LICENSE](LICENSE).
