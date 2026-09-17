# JSP-000884: Euler totient comparison

This package supplies a source-faithful Lean formalization of the three
statements recorded for Erdős Problem 1064: the density-one strict inequality,
the infinitely-often reverse inequality, and the natural-valued `o(n)`
strengthening.  It is a candidate artifact under verification, not an award,
eligibility, or independent-review decision.

The JSP catalogue wording is:

> How does an integer's totient compare with the totient of the integer minus
> its totient?

The canonical wrapper is `JSP000884.solution` in `JSP000884.lean`.  Its target
is the conjunction

```lean
{n | φ n > φ (n - φ n)}.HasDensity 1 ∧
  {n | φ n < φ (n - φ n)}.Infinite ∧
    ∀ f : ℕ → ℕ,
      (fun n => (f n : ℝ)) =o[atTop] (fun n => (n : ℝ)) →
        {n | φ (n - φ n) + f n < φ n}.HasDensity 1
```

## Provenance

- Catalogue entry: [JSP-000884](https://github.com/TheJustinSunPrize/awards/blob/aea6bf0c1b85e9ba4efe5b5b74231988d5e966a9/problems/catalog-0801-0900.md#JSP-000884).
- Original mathematical source: [Erdős Problem 1064](https://www.erdosproblems.com/1064), with the references recorded by the catalogue.
- Frozen formal statement: [Formal Conjectures commit
  `40e7c98697de6f66b8cbdbf641749ab39ed9c152`](https://github.com/google-deepmind/formal-conjectures/blob/40e7c98697de6f66b8cbdbf641749ab39ed9c152/FormalConjectures/ErdosProblems/1064.lean).
- Proof source: [plby/lean-proofs commit
  `8822f7ddef30fadbd92e1c6ab4ed897af356af5e`](https://github.com/plby/lean-proofs/tree/8822f7ddef30fadbd92e1c6ab4ed897af356af5e), especially `ErdosProblems/Erdos1064.lean`.

The source file and its project-local transitive dependencies are copied with
their public headers and license notices.  `JSP000884.lean` only states the
JSP wrapper and applies the three imported source theorems; it introduces no
axiom, oracle, finite approximation, or weakened target.

## Reproduction

From this directory, with network access available for the pinned dependency
checkout on a fresh clone:

```sh
lake update
./verify.sh
```

The package pins Lean `v4.33.0` and Mathlib revision
`db584cd6d46c92f209a44c0f1c829460d327499d`; transitive dependency revisions are
recorded in `lake-manifest.json`.  The verification script scans every copied
Lean source for proof escapes, builds the package, and checks the wrapper.
Generated `.lake/` files are build products and are not part of the submission.

A successful local kernel build is evidence of elaboration only.  It is not an
independent mathematical review, an official JSP verification decision, an
award decision, or recipient confirmation.
