# JSP-000404: eleven-point lower bound

This package proves that every set of at least eleven distinct points in the Euclidean plane contains three distinct points forming an angle of at least `3*pi/4` (135 degrees). Combined with attributed existing upper constructions, it proves `alpha N = 3*pi/4` for `11 <= N <= 16`.

Prepared by [hit1190100321](https://github.com/hit1190100321) with Codex assistance. The added formalization is the eleven-point direction lower bound and its geometric transfer, yielding the previously uncovered exact cases N=11 through N=15 in the inspected submissions. N=16 is already covered by prior dyadic formalizations. The mathematics is historical; this is a partial formalization of JSP-000404 / Erdos problem 504.

## Statements

- `SunPrize.eleven_point_direction_bound`: every eleven-point direction model satisfies `4 <= t`.
- `SunPrize.eleven_point_angle`: any finite set of at least eleven distinct points in `EuclideanSpace Real (Fin 2)` has three distinct points with `EuclideanGeometry.angle >= 3*pi/4`.
- `SunPrize.alpha_eleven_to_sixteen`: `11 <= N -> N <= 16 -> JSP404.alpha N = 3*pi/4`.

`alpha N` is the supremum of angle thresholds guaranteed in every N-point configuration. The angle is Mathlib's actual unoriented Euclidean angle. No convexity or general-position assumption is imposed. The bound is non-strict.

## Reproduction

Install Lean 4.34.0 using `lean-toolchain`, and Python 3.10 or later. Mathlib is pinned to `5ed2965256430c3649e86755f9576b54eca72435`; all dependencies are locked in `lake-manifest.json`. From this directory, run:

```sh
lake exe cache get
python -X utf8 scripts/verify_project.py
```

The verifier builds the geometric dependencies, recompiles all certificate modules, then runs `lake env lean -j 1 --trust=0 Audit.lean` and checks the public declarations' axiom lists. The supplied Lean proof sources are sufficient; Z3 and CaDiCaL are not needed for verification. Those solvers were used for certificate discovery.

The recorded run checked the modules by stages and separately ran the final audit, all successfully. The consolidated wrapper was syntax-checked after assembly but has not additionally been run end to end from a fresh environment. The final audit dependencies are exactly `propext`, `Classical.choice`, and `Quot.sound`. These are submitter-run local checks; official isolated verification and award assessment remain pending.

## Evidence and attribution

- [Proof explanation](docs/证明说明.md)
- [Verification report](docs/核验报告.md), [machine-readable result](verification/result.json)
- [Source hashes](verification/source-sha256.json), [module results](verification/module-results.json), [final audit log](verification/audit.log)
- [Prior-art review](docs/选题核查.md), [contribution](docs/贡献署名.md)
- [Pinned third-party sources and licenses](vendor/来源说明.md)

The complete arbitrary-N classification remains outside the proved scope. Eligibility, priority, and any award amount require organizer review.
