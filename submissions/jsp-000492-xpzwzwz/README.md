# JSP-000492 / Erdős Problem 605

A standalone Lean 4 proof of spherical configurations with superlinearly many
equal-distance pairs. The main theorem is `JSP000492.erdos605`. The sphere
has radius one in Euclidean three-space; the common distance is `Real.sqrt 2`.

**A complete earlier formalization is already registered in [official Issue 16](https://github.com/TheJustinSunPrize/awards/issues/16).**
This is an additional formalization of known mathematics. We do not claim
first formalization, priority, or established prize eligibility. The earlier
[pinned proof](https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos605.lean)
already uses the same mathematical grid construction. This package offers a
modular standalone proof, explicit quantitative threshold, and reproducible
evidence for review.

The mathematical result is due to Paul Erdős, Dean Hickerson, and János Pach.
This package was written with OpenAI Codex assistance for GitHub account
`xpzwzwz`. Its Lean source was developed separately; no source from the earlier
formalization was copied. Additional Codex-agent review is not independent
human verification. Final attribution remains subject to review; the recipient
placeholder is `RECIPIENT-JSP-000492-A`.

## Checked statements

* `sphere_grid m`: exactly `3*m^3` distinct unit-sphere points and `m^4`
  selected equal-distance pairs, with no reversed duplicates.
* `configuration_every_size n`: exactly `n` unit-sphere points and at least
  `gridSize n ^ 4` unordered pairs at distance √2.
* `eventually_many_pairs K n`: for `n ≥ 3*(24*K+1)^3`, a configuration with
  at least `K*n` unordered pairs.
* `erdos605`: a real-valued function tending to infinity witnesses the original
  lower bound for every `n`, including zero.

`pairCount` uses `Sym2`, excludes diagonal pairs, and counts each unordered
pair once. This is a Euclidean distance statement, not just an incidence count.
See [STATEMENT.md](STATEMENT.md) for scope and prior art.

## Build

Lean 4.34.0; Mathlib commit `5ed2965256430c3649e86755f9576b54eca72435`.

```sh
lake exe cache get
lake build -KwarningAsError=true
lake env lean -DwarningAsError=true Audit.lean
sha256sum -c evidence/SHA256SUMS
```

Modules: `Geometry` normalizes points and line normals; `Construction` counts
the grid; `Pairs` handles unordered pairs; `Padding` supplies every cardinality;
`Scale` proves growth estimates; `Main` connects the final theorem.

See [evidence/README.md](evidence/README.md) for verification and limitations.
Organizer acceptance and independent human review remain pending.

## Sources

* [Erdős Problem 605](https://www.erdosproblems.com/605).
* P. Erdős, D. Hickerson, J. Pach, *A Problem of Leo Moser About Repeated
  Distances on the Sphere*, American Mathematical Monthly 96 (1989), 569–575,
  [DOI](https://doi.org/10.1080/00029890.1989.11972243).
* [Earlier formalization registration, Issue 16](https://github.com/TheJustinSunPrize/awards/issues/16).

Immutable standalone source: [xpzwzwz/jsp-000492-lean@a891a6b](https://github.com/xpzwzwz/jsp-000492-lean/tree/a891a6bcb44df6f8e8ddaadd0f1a53ba7cac3869).
