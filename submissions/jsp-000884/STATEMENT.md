# Statement correspondence

## Catalogue identity

The repository catalogue identifies JSP-000884 as a solved number-theory
problem, while recording that no Lean proof is present and that the result is
not eligible to claim.  The catalogue question is deliberately short; this
package therefore makes its formal correspondence explicit instead of
silently treating one subcase as the whole question.

Catalogue snapshot: [awards commit
`aea6bf0c1b85e9ba4efe5b5b74231988d5e966a9`](https://github.com/TheJustinSunPrize/awards/blob/aea6bf0c1b85e9ba4efe5b5b74231988d5e966a9/problems/catalog-0801-0900.md#JSP-000884).

## Frozen formal target

The public Formal Conjectures file for Erdős Problem 1064 contains these three
propositions:

1. `{n | φ n > φ (n - φ n)}.HasDensity 1`;
2. `{n | φ n < φ (n - φ n)}.Infinite`;
3. for every `f : ℕ → ℕ` with `f = o(n)`,
   `{n | φ (n - φ n) + f n < φ n}.HasDensity 1`.

`JSP000884.target` is exactly their conjunction, using the same natural
numbers, subtraction, Euler totient, real coercion, little-o filter, and
natural-density definitions.  `JSP000884.solution` is a direct conjunction of
`Erdos1064.erdos_1064`,
`Erdos1064.erdos_1064.variants.k2`, and
`Erdos1064.erdos_1064.variants.general_function`.

The third proposition is the source's robust form of the first: it says that
an arbitrary natural-valued sublinear error can be added to the smaller side
while density-one strict inequality remains.  It is not replaced by a finite
sample or by an assertion of the desired proposition.

## Statement source and mathematics

- Formal statement source: [Formal Conjectures Problem 1064 at commit
  `40e7c98697de6f66b8cbdbf641749ab39ed9c152`](https://github.com/google-deepmind/formal-conjectures/blob/40e7c98697de6f66b8cbdbf641749ab39ed9c152/FormalConjectures/ErdosProblems/1064.lean).
- Mathematical references listed by the JSP catalogue include Grytczuk--Luca--Wójtowicz (2001) and Luca--Pomerance (2002); the source file retains its Erdős Problem 1064 reference and attribution header.
- The proof is reproduced from the immutable public [plby/lean-proofs
  commit `8822f7ddef30fadbd92e1c6ab4ed897af356af5e`](https://github.com/plby/lean-proofs/tree/8822f7ddef30fadbd92e1c6ab4ed897af356af5e).

This document records statement correspondence only.  It does not assert an
official JSP decision or independent mathematical review.
