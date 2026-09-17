# Complete locally verified Lean proof

The theorem endpoints are `JSP000883.finiteConstruction`,
`JSP000883.eventualPrimeInterval`, `JSP000883.eventualUpper`,
`JSP000883.betterUpper`, and the inline original target
`JSP000883.erdos_1063_better_upper`.

All compiled successfully with Lean 4.33.0 and the pinned dependencies.
The final transitive axiom set is `[propext, Classical.choice, Quot.sound]`.
See [the actual final record](evidence/result.json) and
[the final type/axiom output](evidence/audit-full.log).

```sh
python3 scripts/check_integrity.py
python3 scripts/verify.py --prepare
lake env leanchecker --verbose JSP000883 PrimeNumberTheoremAnd
python3 -m unittest discover -s tests -v
```

The supplied PNT closure is retained byte-for-byte and identified by the
[source manifest](evidence/pnt-source-manifest.json). Mathlib and its dependency
sources/caches are fetched separately. All mathematical source bytes match the
verified local run; source comments describing the original uncompiled packaging
environment are historical, superseded by the actual logs and current README.

The original `FiniteConstructionClaim`, `EventualPrimeIntervalClaim`,
`EventualUpperClaim`, and `BetterUpperClaim` remain definitions of propositions;
the companion theorem files now prove them. Compilation of definitions alone
is not the verification claim.

[Attribution](docs/ATTRIBUTION.md), [prior art](docs/PRIOR_ART.md),
[local repair diff](LOCAL_REPAIRS.patch), and [verification scope](../VERIFICATION.md).
