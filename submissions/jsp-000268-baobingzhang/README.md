# JSP-000268 / Erdős Problem 322: the case k = 3 (Mahler 1936), formalized in Lean 4

Catalog entry: [JSP-000268](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0201-0300.md#JSP-000268) ·
Problem source: [erdosproblems.com/322](https://www.erdosproblems.com/322)

## Problem

Let `k ≥ 3` and let `r_k(n)` be the number of representations of `n` as a sum of `k` many `k`-th powers.
Does there exist `c > 0` such that `r_k(n) > n^c` for infinitely many `n`?
(Hardy and Littlewood's Hypothesis K would say `r_k(n) ≤ n^{o(1)}`.)

The catalog status is **Progress**: the case `k = 3` was settled by Mahler [Ma36], while `k ≥ 4` is open.
This package formalizes Mahler's result, i.e. the complete `k = 3` case. It does not address `k ≥ 4`.

## Formal statements

All results are in `Erdos322.lean`, namespace `Erdos322`.

`representationCount` is copied verbatim from Google DeepMind's
[formal-conjectures](https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/322.lean)
statement of Erdős Problem 322 (Apache-2.0). It counts **ordered** `k`-tuples of **positive** integers.

```lean
def representationCount (k n : ℕ) : ℕ :=
  ((Finset.univ : Finset (Fin k → Fin (n + 1))).filter
    (fun a ↦ (∀ i, 0 < (a i : ℕ)) ∧ ∑ i, (a i : ℕ) ^ k = n)).card

/-- Erdős Problem 322 for k = 3 (Mahler 1936). -/
theorem erdos_322_k_three :
    ∃ c > (0 : ℝ), {n : ℕ | (n : ℝ) ^ c < representationCount 3 n}.Infinite

/-- Quantitative form: q^12 has at least ⌊q/4⌋ representations, i.e. r₃(n) ≫ n^(1/12) along n = q^12. -/
theorem le_representationCount_three (q : ℕ) : q / 4 ≤ representationCount 3 (q ^ 12)

/-- Mahler's identity. -/
theorem mahler_identity (p q : ℤ) :
    (9 * p ^ 4) ^ 3 + (3 * p * q ^ 3 - 9 * p ^ 4) ^ 3 + (q ^ 4 - 9 * p ^ 3 * q) ^ 3 = q ^ 12
```

`erdos_322_k_three` is exactly the `k = 3` instance of the right-hand side of the formal-conjectures statement
`∀ k : ℕ, 3 ≤ k → ∃ c > (0 : ℝ), {n : ℕ | (n : ℝ) ^ c < representationCount k n}.Infinite`.
Mahler's triples are strictly increasing positive integers, so the lower bound also holds for unordered
representations and for conventions that allow zero.

## Proof outline

1. For `1 ≤ p` and `4p ≤ q`, the three terms `9p⁴`, `3pq³ − 9p⁴` and `q⁴ − 9p³q` are positive,
   and their cubes sum to `q¹²` (Mahler's identity).
2. `p ↦ (9p⁴, 3pq³ − 9p⁴, q⁴ − 9p³q)` is injective on `1 ≤ p ≤ q/4`, which gives `q/4 ≤ r₃(q¹²)`.
3. For `t ≥ 3` and `n = (4t²)¹²` we get `n^(1/24) = 2t < t² ≤ r₃(n)`, and these `n` are unbounded.

## Build and verification

- Lean `v4.34.0` (`leanprover/lean4:v4.34.0`, commit `293d5d0c0c3f3dded4688b3ccd6a33939ac5102b`)
- Mathlib tag `v4.34.0`, commit `5ed2965256430c3649e86755f9576b54eca72435`; all dependencies are pinned in `lake-manifest.json`

```sh
lake exe cache get
lake build
```

`#print axioms` (see `verification/axioms.txt`):

```
'Erdos322.erdos_322_k_three' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos322.le_representationCount_three' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos322.mahler_identity' depends on axioms: [propext, Quot.sound]
```

The file contains no `sorry`, no `axiom` declarations and no `native_decide`.
The build log and the SHA-256 of `Erdos322.lean` are in `verification/`.

## Attribution

- Mathematics: K. Mahler, *Note on Hypothesis K of Hardy and Littlewood*, J. London Math. Soc. 11 (1936), 136–138.
- Formal statement of `representationCount`: The Formal Conjectures Authors (Apache-2.0).
- Lean formalization: GitHub user `baobingzhang`, developed with AI assistance (Anthropic Claude).

No priority for the mathematics is claimed. The contribution is the Lean formalization.
