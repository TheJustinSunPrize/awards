# JSP-000689 / Erdős Problem #833

A complete Lean 4 proof of the affirmative exponential-degree assertion:
**every finite `r`-uniform hypergraph, `r ≥ 2`, that is not two-colourable
has a vertex of degree at least `(9/8)^r`.** Thus the absolute constant
`c = 1/8` answers the question for three-chromatic hypergraphs.

**Prior formalization exists.** Before publication, a full issue-body check found
[official issue #19](https://github.com/TheJustinSunPrize/awards/issues/19), which
registers an [earlier complete Lean proof](https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos833.lean).
This repository is an independent alternative proof, not a first-formalization
or priority claim. It is offered for review as an alternative formalization;
see [comparison with the prior proof](COMPARISON.md).

Main declarations:

- `JSP000689.erdos833`: arbitrary finite vertex types, explicit real bound;
- `JSP000689.prize_statement`: one positive constant quantified before all
  finite vertex counts and edge sizes;
- `JSP000689.colorable`: a more general counting criterion.

This is a formalization of known mathematics, not a claim of a new solution.
Erdős and Lovász established the exponential-degree result in 1975. Their
stronger numerical bound `2^(r-1)/(4r)` is not claimed here. We establish the
original existential-constant assertion with a self-contained counting proof.
Determining the exact extremal function for every rank is outside this claim.

The formalization was developed with OpenAI Codex assistance for the GitHub
applicant `xpzwzwz`. The project is submitted for consideration as an independent alternative
formalization, with no assertion of eligibility or priority. The catalog still lists
`Lean proof: No`, but issue #19 provides evidence that this flag is stale.

## Reproduce

Pinned environment: Lean `v4.34.0`, Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`. Transitive revisions are fixed in
`lake-manifest.json`.

```sh
lake exe cache get
lake build -KwarningAsError=true
lake env lean Audit.lean
sha256sum -c evidence/SHA256SUMS
```

All project proofs are checked by Lean's kernel. They use no proof placeholders,
custom axioms, `unsafe` declarations, or native-evaluation proof shortcuts.
The audited declarations use only `propext`, `Classical.choice`, and `Quot.sound`.
See [verification evidence](evidence/README.md) and [statement alignment](STATEMENT.md).

## Counting proof

Let `C(S)` count proper two-colourings of the induced hypergraph on a vertex set
`S`. For a real or rational parameter `β ≥ 1`, we prove

`C(S) ≥ β C(S \ {v})`

whenever every vertex degree is at most `(2-β) β^(r-2)`.
There are exactly `2 C(S \ {v})` extensions. A failed extension has an incident
monochromatic edge. Keep one vertex of that edge and erase the other `r-1`
vertices: the erased colours can be recovered from the retained vertex.
Induction bounds the number of such failed extensions for each edge by
`C(S \ {v}) / β^(r-2)`. A union bound closes the induction, and `C(∅) ≥ 1`
ensures the existence of a colouring.

Contraposition at `β = 3/2` gives a vertex degree greater than
`(1/2)(3/2)^(r-2)`. For `r ≥ 6`, this dominates `(9/8)^r`.
For `2 ≤ r ≤ 5`, the same criterion at `β = 1` gives a vertex of degree at
least two, which is enough.

## Files

| Module | Responsibility |
| --- | --- |
| `Counting.lean` | Ordinary monochromatic edges, proper colourings, exact extension count, compression injection, union cover |
| `Growth.lean` | Iteration of multiplicative growth and the counting recurrence |
| `Colorable.lean` | Strong induction proving the counting criterion |
| `Main.lean` | Explicit constant, all ranks, and real-valued prize statement |
| `Sanity.lean` | Non-vacuity via a triangle; a single edge remains two-colourable |

## Sources and attribution

- [Official JSP-000689 entry](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0601-0700.md#JSP-000689).
- [Erdős Problem #833](https://www.erdosproblems.com/833), and its
  [LaTeX statement and bibliography](https://www.erdosproblems.com/latex/833).
- P. Erdős and L. Lovász, *Problems and results on 3-chromatic hypergraphs and
  some related questions*, 1975, pp. 609–627.

The Lean source was written for this project; the implementation depends on
Mathlib and its separately licensed dependencies. First-party code is MIT licensed.

## Immutable source snapshot

[Public source at `d7cc774fb5259bfa9625b23b3a61f865a41e558e`](https://github.com/xpzwzwz/jsp-000689-lean/tree/d7cc774fb5259bfa9625b23b3a61f865a41e558e).
