# JSP-000733: Korsky's finite upper bounds for primitive subset sums

This package formalizes upper bounds from Samuel Korsky's *Near-Exact Bounds
for Primitive Subset Sums* (July 26, 2026) for **Erdős Problem 882**. Let `F(n)`
be the maximum size of a subset of `{1,...,n}` whose distinct nonempty
subset-sum values never divide one another.

The principal addition is the finite estimate in Theorem 1.1, (1.7)–(1.8).
For any nonempty admissible set of size `k`, it proves

```text
(k+1) * 2^(k-1) + (k-1)^2 / 4 ≤ k*n + 1.
```

Here every quantity is a natural number and `/` is natural-number division,
so `(k-1)^2 / 4` means `floor((k-1)^2/4)`. The displayed statement is the
ceiling-free form of (1.8). The previous sum bound and constant additive-error
endpoint `F(n) ≤ Nat.log 2 n + 1` are retained.

The new original-problem threshold theorem gives, for all natural `n,m`,

```text
(m+1)*n + 1 < (m+2)*2^m + m^2/4  →  F(n) ≤ m.
```

This is an upper-bound contribution. The package does not supply a lower-bound
construction, a two-value theorem, an exact-value theorem, or a proof of the
remaining conjecture `F(n) = floor(log₂(n+1))`.

## Exported statements

All theorem names below are in namespace `Erdos882Korsky`.

| Theorem | Statement and hypotheses |
|---|---|
| `korsky_sum_bound` | For positive natural weights and `k > 0`, `NoDouble a` implies `k * 2^(k-1) ≤ total a`. Retained. |
| `original_upper_bound` | For every natural `n`, `Erdos882.maximumSize n ≤ Nat.log 2 n + 1`. Retained. |
| `korsky_deficit_bound` | For `k > 0`, strictly increasing positive natural weights bounded by `n`, and `NoDouble a`, `total a + 2^(k-1) + (k-1)^2/4 ≤ k*n+1`. New; corresponds to (1.7). |
| `korsky_finite_bound` | Under the same hypotheses, `(k+1)*2^(k-1) + (k-1)^2/4 ≤ k*n+1`. New; corresponds to (1.8). |
| `original_finite_bound` | The finite bound for every nonempty `Erdos882.Admissible n A`, with `k = A.card`. New. |
| `original_threshold_bound` | The displayed strict threshold implies `Erdos882.maximumSize n ≤ m`. New. |

`NoDouble a` forbids a ratio of 2 between any two nonempty index-subset sums;
the subsets may overlap. It is weaker than the original primitivity condition.
The original extremal function is the attained maximum of a finite set of
admissible cardinalities. It is unchanged by this extension. The final exported
theorems have no unproved counting, packing, or maximum-attainment parameters.

## Proof structure

The original seven production source files are retained byte for byte. They
implement the original definitions and attained
maximum, ordered ternary words, coefficient cancellation, modular packing,
the sum bound, and the original constant-error upper bound. The extension adds
seven production modules:

| Module | Contribution |
|---|---|
| `KorskyBalancedDefs.lean` | `Balanced w`: an ordered ternary word with coordinate sum `k`. |
| `KorskyBalancedCount.lean` | A bijection with even Boolean supports gives exactly `2^(k-1)` balanced words for positive `k`. |
| `KorskyBalancedLower.lean` | For monotone weights, every balanced word has weighted value at least `total a`. The filename refers to an interval endpoint, not a lower bound for `F(n)`. |
| `KorskyBalancedUpper.lean` | Strictly increasing weights and reversed coordinate ranks give `value a w + floor((k-1)^2/4) ≤ k*n`. |
| `KorskyBalancedPacking.lean` | The existing collision lemma injects balanced words into a closed integer interval. Its cardinality supplies the deficit bound. |
| `KorskyFiniteEndpoint.lean` | Sorted enumeration, preservation of admissibility under subsets, and a bridge to the original finite maximum. |
| `Erdos882KorskyFinite.lean` | Assembles the four new theorems and reports their axiom dependencies. |

The all-ones word is retained and has value `total a`. Integer-interval packing
preserves the final `+1`. The threshold argument takes an admissible subset of
exactly `m+1` elements; it needs no unproved monotonicity assertion about a
threshold function. See [SCOPE_AUDIT.md](SCOPE_AUDIT.md).

## Mathematical provenance and related work

The mathematical strengthening belongs to **Samuel Korsky**. The source is
[the author's manuscript](https://drive.google.com/file/d/1G1kNGljoP7qn32niEu87fCWcGKjQvWk4/view),
Theorem 1.1 (1.6)–(1.8), Proposition 2.2, and Section 3. This formalization uses
a finite modular presentation for (1.6) and direct balanced-word interval
packing for (1.7)–(1.8). It does not reproduce every intermediate paper lemma.
Korsky's disclosed GPT-5.6 Pro assistance and the present Codex assistance are
recorded in [ATTRIBUTION.md](ATTRIBUTION.md).

[PR #31](https://github.com/TheJustinSunPrize/awards/pull/31) covers the leading
asymptotic. [PR #264](https://github.com/TheJustinSunPrize/awards/pull/264), at
reviewed head `1db509ec5ad2c410d9b13232685c343c008f0b1f`, proves the half-log-log
upper bound for `n ≥ 32`, with original-condition and maximum-attainment
bridges. Those contributions are acknowledged. No source code from those PRs
or the separately published lower-construction formalization is incorporated.
This bounded comparison does not establish global first-formalization priority.

## Reproduction and evidence

Use Lean **4.34.0**, Mathlib revision
`5ed2965256430c3649e86755f9576b54eca72435`, and the transitive pins in
`lake-manifest.json`. Package version **2.0.0** sets the default build target to
`Erdos882KorskyFinite`.

```sh
lake exe cache get
lake build Erdos882KorskyFinite
```

The full verification record must identify the exact source snapshot and cover
all six exported statements, compilation of the local import closure, the fresh
Lean kernel check, the independent checker, actual axiom dependencies, negative
controls, tool identities, isolation arrangements, and artifact hashes. Cached
dependency objects and any other verification limitations must be stated.
Prior verification of the smaller package does not verify this extension.

The expanded-package evidence belongs in `verification/finite-v2/`:
[verification summary](verification/finite-v2/VERIFICATION.md),
[run receipt](verification/finite-v2/verification.json),
[independent-checker record](verification/finite-v2/nanoda.json), and
[check logs](verification/finite-v2/check-logs.txt). The original records under
`verification/` are retained as evidence of the earlier scope.

- Final verification: **passed**, run `06568604-a3fd-4fa2-a3d4-831c21267533`; 14 fresh module builds, fresh Lean kernel, and Nanoda (9,132 declarations).
- Proof export: `39,724,522` bytes; SHA-256 `5a710a3e4fa610606afdbc2fd2171ed1315860d2ae43116010b3da4efdd83bf9`.
- Both negative-control modules passed a separate network-denied Lean run; see [the receipt](verification/finite-v2/negative-controls-expanded.json).
- Permanent external archival receipt: **PENDING**.

A local ZIP or ordinary repository upload is not represented as permanent
external archival. Permanent external archival still requires its own receipt. Submission requests
review of the formalization; technical checks alone confer no award entitlement.
