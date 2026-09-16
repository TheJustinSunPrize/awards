# Closed polynomial lemniscates: JSP-000410

This module extends an existing open-sublevel construction to the closed set
`{z : ℂ | ‖p.eval z‖ ≤ 1}`. For every natural number `N`, it constructs a
monic complex polynomial with at least `N` distinct connected components of this closed
set whose diameters are strictly greater than `6/5`. Consequently this refutes
the proposed assertion that every threshold `d > 1` admits a component-count
bound independent of the polynomial degree.

The threshold is fixed at `6/5`; the statement does not give the stronger
family of results for every `d < 4`, a bound linear in the degree, or the
number of components for an arbitrary specified polynomial.

## Sources and contribution

- [Catalog JSP-000410, reviewed revision](https://github.com/TheJustinSunPrize/awards/blob/f4e7173d89dfe91022a185427d63452c8ffbf6ae/problems/catalog-0401-0500.md#JSP-000410)
- [Erdős problem 511 and its source discussion](https://www.erdosproblems.com/511)
- [Existing open-sublevel formalization](https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos511.lean)

The original problem page's main display uses an open sublevel set. The
catalog entry explicitly uses the closed set, which is the target here;
the two statements must not be silently identified.

The underlying construction and analytic approximation estimates belong to
that existing formalization, whose source credits the mathematical literature
and its formal authors. The new contribution is a closed-sublevel assembly:
a continuous barrier keeps each closed connected component inside its own box,
and the original core segment supplies a diameter lower bound.

A review of the checked public sources found a complete open-set proof and
other incomplete or axiomatic variants, but no complete closed-set proof.
This bounded prior-art search is not a universal first-publication claim.
Prepared with OpenAI Codex assistance; no award, recipient, or priority
determination is made.

The two unchanged upstream dependency files are external references in
[upstream.json](upstream.json). They are not vendored in this contribution.
Their source headers do not establish a license we can infer, so this package
contains only the new bridge, references, verification metadata and helper.
The helper retrieves exact hash-pinned bytes into the reproducer's dedicated
checkout. Source attribution remains intact.

## Exact Lean statements

- `JSP410Closed.arbitrarily_many_large_closed_components`
- `JSP410Closed.not_uniformly_bounded_closed_components`

`HasLargeClosedComponents` uses an injective family of actual connected
components, with each component's ordinary metric diameter above the
threshold. The diameter argument first proves boundedness; it does not rely
on the convention for an unbounded set's diameter.

The source construction exposes its analytic lemmas as private declarations.
A safe syntax macro names those existing constants using Lean's actual
numeric private-name component. No axiom, evaluator shortcut, or custom
kernel rule is introduced. This is a version-pinned interface, not a stable
public upstream API: changing the source module name or commit requires a
new review and build.

## Reproduction

Requires Python 3, Git, and Lean's `elan`/`lake` toolchain management.
Use a fresh, dedicated Mathlib checkout; the helper rejects existing source
files whose bytes differ.

```sh
git clone https://github.com/leanprover-community/mathlib4.git mathlib4-jsp410
cd mathlib4-jsp410
git checkout db584cd6d46c92f209a44c0f1c829460d327499d
lake exe cache get
cd ..
python /path/to/this/package/verify.py --mathlib mathlib4-jsp410
```

The script checks the Mathlib revision and toolchain, checks the dependency
hashes, compiles Erdős229, Erdős511, then the bridge, and replays only the
bridge module with `leanchecker`. Logs and their byte hashes are written to
`verification/<UTC timestamp>/` in this package. The bridge source prints
both final theorem axiom reports. Inspect the actual report and exit codes;
a script existing or an unchecked source file is not verification.

This is Lean's target-module kernel replay against the imported environment,
not a fresh replay of all Mathlib, an independently implemented checker, or
an independent human referee report.

## Verification status

The exact LF source committed here compiled successfully with Lean 4.33.0 and
the pinned Mathlib revision; target-module `leanchecker` replay exited 0.
Both final theorem reports contain only `propext`, `Classical.choice`, and
`Quot.sound`. The unchanged upstream dependencies compiled successfully.

Bridge SHA-256: `926bc1f3128bd1704b8a92bf67c444d88e8e213073abc5de0eb04ad35e73c2ae` (6440 bytes).

See [verification.json](verification.json), the
[final compiler and replay output](validation-logs/bridge-final-lf.log), and
the [original dependency-build log](validation-logs/dependency-build-first-attempt.log).
The latter also records an early bridge import-order error, fixed before the
final successful run; it is retained unedited.

Local verification used an isolated output directory and a pinned read-only
Mathlib cache. The portable fresh-checkout helper above has been statically
reviewed; a separate end-to-end run of that helper is not claimed.
This evidence is submitted for maintainer review and does not determine
priority, candidate status, eligibility, or an award.
