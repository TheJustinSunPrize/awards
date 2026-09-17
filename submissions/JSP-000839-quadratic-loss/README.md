# A quadratic loss obstruction for Erdős 1009

This Lean 4 project verifies a generalized Sauer construction for edge-disjoint
triangle packings. It formalizes a lower bound related to
[Erdős problem 1009](https://www.erdosproblems.com/1009) /
[JSP-000839](https://github.com/TheJustinSunPrize/awards/blob/f4e7173d89dfe91022a185427d63452c8ffbf6ae/problems/catalog-0801-0900.md#JSP-000839).

For every integer `t >= 1` and every `r >= 0`, the graph consists of two
independent classes of size `r` and a complete core of size `12*t`, with all
edges between different classes. It has

```text
n = 2*r + 12*t
m = r^2 + 24*r*t + 72*t^2 - 6*t
k = m - floor(n^2/4) = 12*r*t + 36*t^2 - 6*t < (6*t)*n.
```

Every edge-disjoint triangle packing has at most
`12*r*t + 24*t^2 - 4*t` members. Thus it loses at least **`12*t^2 - 2*t`**
triangles relative to the excess `k`. The order `n` is unbounded with `t` fixed.
Consequently, even a guarantee restricted to sufficiently large graphs needs
`f(6*t) >= 12*t^2 - 2*t`. The project also proves the lower bound for every real
parameter `c >= 6*t`, and that one constant error cannot work for all `c > 0`.

## Mathematical scope and attribution

Sauer's four-vertex-core example is recorded on the original problem page.
This project formalizes the general-core construction, weighted counting, and
the strengthening obtained because an even core gives each core vertex odd
degree. A triangle packing leaves an unused edge at each such vertex.

Győri proved the original existence theorem with an error of order `c^2`.
This project does not reprove that upper bound or claim a new solution of the
original problem. It does not claim that the stated packing upper bound is
attained. It makes no claim of a new mathematical discovery, global first
formalization, prize eligibility, or an award.

The Lean source was written in this AI-assisted session using OpenAI Codex
and collaborating agents. The submitting GitHub account operates the session;
the original mathematical contributions remain attributed to their sources.
No source code from a previous Erdős 1009 proof was incorporated.

## Main declarations

| Declaration | Verified claim |
| --- | --- |
| `IsPacking.bound_even_core` | For every positive even `s`, `6*card P <= 6*r*s + s*(s-2)`. |
| `edge_count_excess` | Exact graph edge count above `floor(n^2/4)`. |
| `arbitrarily_large_obstructions` | The exact construction and loss bound at every required order threshold. |
| `error_lower_bound` | Any eventual error guarantee at `c=6*t` needs `f >= 12*t^2-2*t`. |
| `error_lower_bound_of_le` | The same necessary error whenever the real parameter is at least `6*t`. |
| `no_uniform_error` | There is no error constant working for all positive real parameters. |

All names are in namespace `TrianglePacking`. `IsPacking` uses Mathlib's
three-vertex cliques and pairwise disjoint sets of oriented edges. Sharing an
unordered edge necessarily shares both orientations, so this is ordinary
edge-disjoint packing, with shared vertices allowed.

## Reproduction

- Lean: `leanprover/lean4:v4.33.1`.
- Mathlib: `0df444a360eaa60ab8c11dca51a86af692955474`.
- Other dependencies: pinned by `lake-manifest.json`.

With the specified toolchain available:

```sh
lake exe cache get Mathlib.Combinatorics.SimpleGraph.Clique Mathlib.Combinatorics.SimpleGraph.DegreeSum Mathlib.Algebra.BigOperators.Group.Finset.Piecewise Mathlib.Data.Real.Basic Mathlib.Tactic.NormNum Mathlib.Tactic.Linarith Mathlib.Tactic.Ring Mathlib.Tactic.FinCases
lake --wfail build TrianglePacking
lake env lean -DwarningAsError=true Audit.lean
LEAN_NUM_THREADS=1 lake env leanchecker --verbose TrianglePacking
```

On Windows, `verify.ps1 -LeanBin <path-to-lean-bin>` runs these checks after
dependency setup, checks the exact replayed module list, and records logs,
source hashes, and versions in `verification/`. Passing logs are evidence of
the stated local checks, not an organizer's verification record.

The kernel replay uses Lean's own kernel. It checks all local proof modules
against imported Mathlib/package artifacts; it is not an independent checker
implementation, a fresh replay of all imports, or a network-isolated review.

## Prior-art check

The check covered the official catalog, available Issues/PRs and the fixed
`plby/lean-proofs` commit `8822f7ddef30fadbd92e1c6ab4ed897af356af5e`.
The eight-module project import closure of its `Erdos1009.lean` contains 5101
lines and proves an upper bound with `f=210000*C^2`, for an integer `C>c`.
The generalized Sauer lower-bound family was not found in those checked files.
This limited search does not establish global priority. A source-level
statement review is in `statement-review.md`; it is not an independent kernel
validation.

Code license: Apache-2.0. Sources and prior mathematical attribution are retained
in this README and the proof exposition.
