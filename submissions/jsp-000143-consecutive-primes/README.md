# Erdős 141: the known cases through ten consecutive primes

This package formalizes the known finite-length result for JSP-000143 / Erdős 141:
for every natural number `3 ≤ k ≤ 10`, a set of `k` consecutive primes is an
arithmetic progression. It does not resolve the question for arbitrary lengths,
the eleven-term case, or infinitude for any fixed length. It does not establish
an award, eligibility, or priority.

## Mathematics and attribution

The construction is published in H. Dubner, T. Forbes, N. Lygeros, M. Mizony,
H. Nelson, and P. Zimmermann, *Ten consecutive primes in arithmetic progression*,
Mathematics of Computation 71 (2002), 1323–1328,
[DOI 10.1090/S0025-5718-01-01374-6](https://doi.org/10.1090/S0025-5718-01-01374-6).
The authors credit Manfred Toplic with finding the ten-prime progression on
March 2, 1998. Table 3 gives the starting prime and common difference 210.
[Author-hosted paper](https://lygeros.org/wp-content/uploads/2019/12/S0025-5718-01-01374-6.pdf).

The formalization was developed by the submitting public GitHub account
`James-16` with substantial OpenAI Codex assistance. Mathematical discovery is
not claimed. Definitions are adapted from the Apache-2.0 Formal Conjectures
project; see `NOTICE`. No worldwide first-formalization claim is made.

The start is:

```text
100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229719
```

The ten terms are `start + 210*i`, for `0 ≤ i < 10`. The proof establishes both
the primality of these terms and the compositeness of all 1,881 other integers
in the closed interval `[start, start + 1890]`.

## Exact statement

`Erdos141.erdos_141.variants.first_cases` has the name and statement of the known
variant in [Formal Conjectures, pinned revision 40e7c986](https://github.com/google-deepmind/formal-conjectures/blob/40e7c98697de6f66b8cbdbf641749ab39ed9c152/FormalConjectures/ErdosProblems/141.lean):

```lean
theorem erdos_141.variants.first_cases :
    (∀ k ≥ 3, k ≤ 10 → ∃ (s : Set ℕ), s.IsAPAndPrimeProgressionOfLength k)
```

The predicate uses `Nat.nth Nat.Prime`, so “consecutive” refers to the full
prime sequence. An ordinary progression of primes without consecutiveness
would not satisfy the target. The arithmetic-progression definition also
requires cardinality exactly `k`; a constant progression cannot witness it.

`Audit.lean` independently expands both reference definitions, checks their
definitional equality, proves the expanded target, and proves that the closed
interval contains exactly the ten listed primes. The prime index is handled
symbolically using `Nat.count Nat.Prime start`; the proof does not enumerate
all primes below the starting value.

## Proof structure

- `Pratt.lean` derives an explicit-factor Lucas criterion from Mathlib.
- `Primes.lean` proves 372 primality lemmas: 222 Lucas certificates and 150 small
  primes checked by Mathlib's proof-producing `norm_num`. Modular powers are
  checked by `reduce_mod_char`; numeric comparisons use kernel reduction.
- `Fermat.lean` proves that a failed Fermat congruence implies compositeness.
  `Composites.lean` verifies base-2 witnesses for 43 offsets.
- `Block.lean` and `Blocks.lean` verify small proper divisors for the remaining
  1,838 offsets and prove exhaustive interval coverage. The table is divided
  into small blocks to keep kernel verification memory use manageable.
- `Bridge.lean` proves the general connection from prime endpoints and prime-free
  gaps to the exact `Nat.nth` statement. The main file applies it to each prefix.

FactorDB supplied untrusted factorization hints for some predecessor integers.
`data/pratt-hints.json` preserves the hints used. The proof validates complete
products, smaller-prime dependencies, and modular order conditions. No external
factorization database, probable-prime assertion, or downloaded executable is
trusted for a theorem. Rebuilding the package makes no FactorDB queries.

## Reproduction

Requires Lean `v4.33.1`; the manifest pins Mathlib to
`0df444a360eaa60ab8c11dca51a86af692955474` and all transitive dependencies.

```sh
lake exe cache get
bash tools/verify.sh
```

The verification script builds both the proof and its audit with warnings as
errors, repeats the exact-statement/axiom audit, then replays the entire imported
environment using the bundled Lean `leanchecker --fresh`. This is a fresh replay
through the same Lean kernel implementation, not an independent verifier.

The seven audited declarations depend only on `propext`, `Classical.choice`,
and `Quot.sound`. There are no proof placeholders, custom axioms, or native
evaluation shortcuts in the submitted Lean sources. See the verification logs,
report, prior-art notes, and SHA-256 manifest under `verification/`.

## Review request

Please assess statement fidelity, mathematical attribution, overlap, and the
formalization contribution under the prize rules. The catalogue's overall
problem status is unchanged. No recipient identity, candidate record, award
record, or payment instruction is created by this package.
