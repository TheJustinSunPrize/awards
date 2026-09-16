# JSP-000443: Boza's uniform Ramsey inequalities in Lean

This package gives complete Lean proofs of Theorem 6 and Corollary 8 of
Luis Boza, [Exact values and bounds for Ramsey numbers of C4 versus a star graph,
arXiv:2409.12770v2](https://arxiv.org/abs/2409.12770v2).
It concerns [JSP-000443](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0401-0500.md#jsp-000443)
and [Erdős problem 552](https://www.erdosproblems.com/552).

## Exact scope

Let `f(n) = SimpleGraph.graphRamsey (SimpleGraph.cycleGraph 4)
(completeBipartiteGraph (Fin 1) (Fin n))`.

- `JSP443.boza_theorem6`: for all positive natural numbers `a,b`,
  `a+b ≤ f(a) ∨ f(a+b) ≤ a+2*b`.
- `JSP443.boza_corollary8`: for every positive natural number `n`,
  `f(f(n)+1) ≤ 2*f(n)-n+2`.

These are known mathematical results, attributed to Boza. This contribution
is their formalization. It does not determine all values of `f`, settle the
asymptotic question in Erdős 552, or claim that the entire prize problem is solved.

## Proof and definitions

[Proof.lean](Proof.lean) contains the full proof. Ordinary subgraph containment
uses Mathlib's injective homomorphisms `Copy` / `IsContained`, allowing extra
edges. The star has exactly `n` leaves.

The proof establishes: distinct vertices of a C4-free graph have at most one
common neighbor; a star copy is equivalent to a sufficiently large vertex
degree; a deletion lemma preserving the required degree bound; and the two
Ramsey inequalities. The elementary bound `f(n) ≤ 2*n+2` proves nonemptiness
of the set defining the Ramsey minimum. Monotone transfer to arbitrary finite
vertex types is proved, not assumed.

The two vendored modules under `FormalConjecturesForMathlib/` are unchanged
from Google DeepMind [formal-conjectures commit
40e7c98697de6f66b8cbdbf641749ab39ed9c152](https://github.com/google-deepmind/formal-conjectures/tree/40e7c98697de6f66b8cbdbf641749ab39ed9c152/FormalConjecturesForMathlib/Combinatorics/SimpleGraph).
Their original Apache 2.0 attribution is preserved. In particular, the proof
imports the original `SimpleGraph.graphRamsey` definition.

## Reproduce

Lean: `leanprover/lean4:v4.33.1`.
Mathlib: `0df444a360eaa60ab8c11dca51a86af692955474`.
All transitive dependencies are pinned in [lake-manifest.json](lake-manifest.json).

With the Lean toolchain installed, run from this directory:

```sh
lake exe cache get
lake build
```

The proof source prints both final theorem types and their axiom dependencies.
Actual local Lean compilation returned exit code 0 and printed only
`propext`, `Classical.choice`, and `Quot.sound` for both final theorems;
see [the local log](verification/local-lean.log).
There is no `sorry`, custom axiom, `native_decide`, or external oracle in the proof.
Local validation reused the pinned Mathlib compiled cache; it is not an
independent rebuild of Mathlib or an official prize verification.

## Attribution and submission

The mathematical statements are Boza's. The formalization was developed
with Codex and ChatGPT Pro assistance. Recipient placeholder:
`RECIPIENT-JSP-000443-A`; recipient confirmation is pending.
This package is submitted for review as a partial-scope formalization
contribution. No award decision or official priority determination is asserted.

Code is distributed under [Apache 2.0](LICENSE), retaining third-party notices.
