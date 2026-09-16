# JSP-000733 / Erdos 882: leading asymptotic

The target is `Erdos882.maximumSize_asymptotic`: `f(n) / log₂(n) → 1`,
where `f(n)` is the maximum size of a subset of `{1, …, n}` whose distinct
nonempty subset-sum values never divide each other. The three added Lean
modules and this target are unchanged by the dependency-packaging repair.

## Files and attribution

- `Erdos882Upper.lean`: primitivity implies distinct subset sums; then
  `2 ^ f(n) ≤ n * f(n) + 1`.
- `AsymptoticCore.lean`: analytic consequence of the counting and lower bounds.
- `Erdos882Asymptotic.lean`: unconditional assembly for the actual maximum.
- `Erdos882Existing.lean` is **not bundled**. `verify.py` downloads the prior
  definitions and lower-bound proof from the fixed upstream URL in
  `provenance.json`, verifies its SHA-256, and retains its exact author header.

The lower construction is attributed to Erdős, Lev, Rauzy, Sándor and Sárközy.
The upstream header credits Codex and GPT-5.6 Sol as formal authors. Our added
sources were produced with Codex. We do not claim authorship of the prior
proof, mathematical discovery, or globally first formalization.

The copyright and license applicable to that specific upstream source have
not been determined by this submission. Its general upstream license notice
does not establish permission for this file. Our Apache license covers only
our added files. See `NOTICE`. Earlier PR commits bundled the source; this
follow-up preserves history and does not clear historical license uncertainty.

## Reproduce through the public helper

Install Lean `v4.33.0` (release commit
`d8b18978322de05a8f3dba51ef03cf5461676c17`) and Mathlib commit
`db584cd6d46c92f209a44c0f1c829460d327499d` with its matching compiled cache.
Then run this package's actual public entry, using a **new** output directory:

```text
python verify.py --lean-bin PATH_TO_LEAN_BIN --mathlib PATH_TO_MATHLIB --output reproduced-verification
```

Network access is required to fetch the pinned dependency. The helper rejects
a hash mismatch, creates a fresh build, clears inherited Lean/Lake search
settings, compiles the downloaded dependency and three added modules in order,
then runs `leanchecker --verbose` on each of those four local modules. It
checks principal theorem axioms and records actual command exit codes,
source/helper/runtime/output hashes and timestamps. The supplied runtime and
Mathlib trees are not modified. Serialize this pipeline on a shared computer.

`verification/` retains the original pre-repair compilation/replay record;
it does not demonstrate this revised helper's end-to-end operation.
`verification-helper-20260917/` records the separate fresh Windows run of
this public download/build/check entry. Only its completed `result: pass`
record establishes that run's outcome; neither record is repository CI.

The bundled checker uses the same Lean kernel and the pinned imported
Mathlib cache. This is checking of the local declarations, not an independent
kernel implementation or a full replay of Mathlib. The run is not network
isolated. No official reviewer signature, eligibility, acceptance, exemption,
or award determination is asserted.

## Scope

This is a leading asymptotic result. It does not prove an exact formula, the
half-log-log upper error, or a bounded additive error. `PROOF.md` and `SCOPE.md`
record attribution and the checked prior formal and informal work.
