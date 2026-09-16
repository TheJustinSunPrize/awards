# JSP-000500 / Erdős 617: the fixed r=7 theorem

This project proves in Lean that **every seven-coloring of the edges of K50
has an eight-vertex subset whose induced edges omit at least one color**.

The final declarations are `JSP500.main_proven : JSP500.Main` and
`JSP500.upstream_proven : JSP500.Upstream`. The latter allows any finite
vertex type with exactly fifty elements. The project root imports the complete
proof in `JSP500/Main.lean`.

## Evidence for review

- [Statement and definition correspondence](STATEMENT.md)
- [Complete proof outline and key bounds](PROOF.md)
- [Direct weighted light-edge argument](WEIGHTED_PROOF.md)
- [Verification record](verification/record.json) and [axiom audit](verification/axioms.log)
- [Sources and licenses](THIRD_PARTY_NOTICES.md)

All 26 audited exports, including both final declarations, use only Lean's
standard foundational axioms: `propext`, `Classical.choice`, and `Quot.sound`.
The final proofs have no dependency on `sorryAx`, native-evaluation axioms, or
project-specific unproved axioms. Finite exhaustive computation is not a proof
premise. Verification includes a clean build and a fresh `leanchecker` replay;
the latter uses Lean's kernel, not an independently implemented kernel.

## Reproduce

Install Lean 4.34.0 as specified in `lean-toolchain`, with `lake` on PATH.
Mathlib is pinned to commit `5ed2965256430c3649e86755f9576b54eca72435`.
Python 3 uses only its standard library.

On first setup, fetch dependencies and the cache for the imported modules:

```sh
MATHLIB_NO_CACHE_ON_UPDATE=1 lake --no-cache update
lake --no-cache exe cache get Mathlib.Combinatorics.SimpleGraph.Extremal.Turan Mathlib.Combinatorics.SimpleGraph.FiveWheelLike Mathlib.Combinatorics.SimpleGraph.DegreeSum Mathlib.Tactic.NormNum Mathlib.Tactic.Linarith Mathlib.Tactic.Ring Mathlib.Tactic.IntervalCases Mathlib.Tactic.Push
python3 scripts/verify.py
```

The script cleans and builds this project's modules, audits all listed exports,
replays the imported environment with `leanchecker --fresh`, and writes logs and
source hashes to `verification/`. Dependency cache artifacts may be used in the
build; fresh kernel replay checks the imported declarations as well.

## Submission scope

Formal-evidence and prize evaluation are requested for the **fixed r=7 case**
of [Erdős Problem 617](https://www.erdosproblems.com/617), catalogued as
[JSP-000500](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0401-0500.md#JSP-000500).
This establishes the seven-color case completely. The general conjecture
quantifies over every integer r >= 3; that broader statement is outside this
proof's scope. The requested contribution is the Lean formalization and its
direct counting and vertex-deletion proofs. Award classification and attribution
are submitted for the committee's review.

Public applicant account: `inoader`. Recipient placeholder:
`RECIPIENT-JSP-000500-A`, pending confirmation. Work was prepared with
OpenAI Codex assistance. Source attribution and licensing are preserved in the
linked notices. Private identity and payment information are not part of this package.
