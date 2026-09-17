# JSP-000651 / Erdős 792: the classical one-third bound

Lean 4.34.0 formalization of the classical sum-free subset lower bound.
For every finite integer set `A` with at least two elements, the proof
constructs existentially a sum-free subset `B` with `|A| ≤ 3|B|`.
For nonempty sets excluding zero it proves the stronger strict inequality
`|A| < 3|B|`. The exceptional singleton `{0}` is explicitly excluded and
proved to be an exception.

This is a known result attributed to **Paul Erdős (1965)** on the
[Erdős Problem 792 page](https://www.erdosproblems.com/792).
The original optimal-bound problem and its stronger known bounds are
outside this submission. Only consideration for a formalization
contribution is requested; mathematical discovery, priority, eligibility,
and an award are not claimed.

## Statement and proof

The main theorems in [SumFreeBound.lean](SumFreeBound.lean) are:

- `SumFreeBound.middle_third_nonzero`: the strict bound for any nonempty
  finite set of nonzero integers, allowing positive and negative elements.
- `SumFreeBound.erdos_lower_bound`: the weak bound for every finite integer
  set of size at least two, including sets containing zero.
- `SumFreeBound.singleton_zero_exception`: the literal weak bound fails
  for `{0}`.

`SumFree B` excludes every equation `a + b = c` with all three terms in `B`,
including repeated summands. See [STATEMENT.md](STATEMENT.md) for the exact
scope, proof correspondence and attribution.

The proof selects a sufficiently large prime `p = 3k + 2`, uses the
sum-free interval `{k+1, ..., 2k+1}` in `ZMod p`, and counts preimages under
all multipliers. Dirichlet's theorem is an existing **proved Mathlib
dependency**, not an assumption introduced by this package or a new
contribution. The counting, pullback, zero handling and final bounds are
proved here.

## Reproduce

Use Python 3.10+, Git and the official Lean 4.34.0 toolchain, with `lean`
and `lake` on PATH. All package revisions are pinned in the manifest.
From this directory:

```sh
MATHLIB_NO_CACHE_ON_UPDATE=1 lake update
lake exe cache get --cache-from=master Mathlib.NumberTheory.LSeries.PrimesInAP Mathlib.Combinatorics.Enumerative.DoubleCounting Mathlib.Tactic.NormNum Mathlib.Tactic.Linarith Mathlib.Tactic.Push
python3 -O verify.py
python3 -m unittest discover -s tests -v
```

The verifier builds the proof, compiles [Audit.lean](Audit.lean) with
warnings as errors, audits the named theorems' axiom dependencies, runs
negative controls, and replays the imported environment in a fresh Lean
kernel. Its outputs are [verification.json](evidence/verification.json)
and [axioms.txt](evidence/axioms.txt). Each invocation invalidates previous
generated evidence before checking and publishes the success receipt last, by atomic replacement. The regression
tests seed stale passing evidence and verify that failures remove it, including
under Python optimization; they are separate from real Lean verification.

The audited theorems depend only on the standard `propext`,
`Classical.choice` and `Quot.sound` axioms. The proof uses no placeholders,
custom axioms, native-evaluation shortcut or external-solver assumptions.
`python3 verify.py --skip-replay` is available for a shorter rerun and
explicitly records that replay was omitted.

`leanchecker --fresh` uses the bundled Lean kernel, not a separately
implemented checker. Upstream cache artifacts were used; this is not a
complete source rebuild of every imported library. Local checks and
repository CI do not constitute organizer verification or an award.

Code is MIT licensed. Dependencies retain their own licenses; repository
documentation and record data follow the host repository's
`LICENSE-CONTENT` when included there.

## Documentation attribution

Catalog context is credited to **The Justin Sun Prize contributors**,
[source revision `f4e7173d89dfe91022a185427d63452c8ffbf6ae`](https://github.com/TheJustinSunPrize/awards/blob/f4e7173d89dfe91022a185427d63452c8ffbf6ae/problems/catalog-0601-0700.md#JSP-000651),
under [CC BY 4.0](https://creativecommons.org/licenses/by/4.0/).
Changes: new formalization documentation, explicit theorem scope, proof
correspondence and reproducibility instructions; the catalog is unchanged.
Mathematical attribution and third-party rights remain as stated above.
