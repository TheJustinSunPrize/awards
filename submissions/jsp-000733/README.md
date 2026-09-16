# JSP-000733 / Erdős 882: leading asymptotic

This package formalizes `f(n) / log₂(n) → 1`, where `f(n)` is the maximum
size of a subset of `{1, …, n}` whose distinct nonempty subset-sum values
never divide each other. The source uses the definitions and existing lower
construction from `plby/lean-proofs` without changing their meaning.

## Files and attribution

- `Erdos882Existing.lean` is the exact Git blob from the upstream source
  listed in `provenance.json`, retaining its author header.
- `Erdos882Upper.lean` proves that primitive subset sums are all distinct,
  then `2 ^ f(n) ≤ n * f(n) + 1`.
- `AsymptoticCore.lean` proves the analytic consequence of these counting
  and construction bounds for an arbitrary sequence.
- `Erdos882Asymptotic.lean` applies it to the actual extremal function and
  prints the three principal theorem axiom reports.
- `PROOF.md` explains the argument and the scope of the contribution.

The informal lower construction is due to Erdős, Lev, Rauzy, Sándor and
Sárközy. The retained upstream header identifies its formal authors as
Codex and GPT-5.6 Sol. The added sources were produced with Codex for this
submission. The submitter does not claim authorship of the copied lower
proof, mathematical discovery, or globally first formalization.

## Reproduce

Use Lean `v4.33.0` and Mathlib commit
`db584cd6d46c92f209a44c0f1c829460d327499d`. The `lakefile.toml` pins that
dependency; prepare its matching compiled cache using the normal Mathlib
installation process. Then run:

```text
python verify.py --lean-bin PATH_TO_LEAN_BIN --mathlib PATH_TO_MATHLIB --output reproduced-verification
```

The script writes a fresh isolated build directory, compiles all four
modules in dependency order, runs `leanchecker --verbose` separately on
each local module, checks the final theorem axioms, and records hashes and
exit codes under the chosen output directory. The recorded submission run
used `verification/`; the command above preserves that evidence. It does not modify the supplied runtime
or Mathlib tree. On a shared computer, run only one such pipeline at a time.

The replay uses the bundled Lean kernel and trusts the pinned imported
Mathlib cache. It is additional checking of local declarations, not a
second independent implementation of Lean or a replay of all Mathlib
declarations. The run is not network-isolated. Actual results are reported
only by a successfully completed `verification/verification.json`.

## Scope

The target is the leading asymptotic, not an exact formula or a bounded
additive error. Prior conditional counting formalizations and a July 2026
unreviewed mathematical refinement claim are documented in `PROOF.md` and
`SCOPE.md`. No recipient identity, independent
checker signature, operator acceptance, or award decision is asserted.
