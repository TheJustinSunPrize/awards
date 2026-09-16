# Statement correspondence submitted for review

This is a submitter's comparison, not a curator-issued statement or an independent review attestation.

## Sources

- [JSP-001007 catalog entry](https://github.com/TheJustinSunPrize/awards/blob/f4e7173d89dfe91022a185427d63452c8ffbf6ae/problems/catalog-1001-1022.md#JSP-001007).
- Erdős, *A survey of problems in combinatorial number theory* (1980), page 107, Section 6, Problem 3: [original paper](https://www.renyi.hu/~p_erdos/1980-03.pdf).
- [Erdős Problem #1202](https://www.erdosproblems.com/1202), consulted 2026-09-16.
- [Green Problem 44](https://people.maths.ox.ac.uk/greenbj/papers/open-problems.pdf).
- [Pinned Formal Conjectures statement](https://github.com/google-deepmind/formal-conjectures/blob/c252a41054125b5fd9c8356e2137cd9b55337657/FormalConjectures/GreensOpenProblems/44.lean), under its original Apache-2.0 license. This reference is not imported or used as a proof dependency.

## Definitions and quantifiers

`remaining N p A` is exactly the finite set `(Finset.Icc 1 N).filter (fun x => ∀ i, (x : ZMod (p i)) ∉ A i)`. The interval starts at 1 and includes N. All quantified residue sets use Mathlib's `ZMod`, and their cardinalities use `Finset.card`.

`counterexamples k N0` has no unproved prime-cluster hypothesis. It quantifies over every `k : ℕ` and `N0 : ℕ`, and produces an existential `N ≥ N0`. Each chosen modulus is a prime greater than 2; `StrictMono p` ensures that they are distinct and increasing. Forbidden residues are the first `floor(p/2)` residues. For these odd primes this is `(p-1)/2`.

The conclusion `N < 10 * (remaining N p A).card` is strictly stronger than the failure of the proposed `10 * remaining.card ≤ N` bound. The power inequality `p_i^10 < N^9` is exact natural-number arithmetic; `real_cutoff` also proves the corresponding real bound `p_i < N^(1 - 1/10)`.

`fixed_1000_counterexample` gives witnesses with exactly the prime ordering, residue cardinalities, and maximum-prime power bound of the pinned Formal Conjectures `green_44` formula. Its survivor inequality contradicts that formula's universal upper bound. The reference's `answer(sorry)` wrapper and unproved declaration are not imported.

`not_erdos_uniform_sieve` and `not_erdos_eventual_uniform_sieve` refute the package's explicitly defined uniform propositions. Both use epsilon = eta = 1/10. The latter also allows a threshold `N0` before the universal quantifier over `N`; the arbitrarily-large counterexamples still refute it. No claim of the stronger quantitative bounds reported for the original Price–GPT construction is made here.

The public #1202 transcription introduces both epsilon and eta but currently displays epsilon in its concluding bound. Fixing both to 1/10 makes this distinction immaterial for the submitted counterexample. The original wording and formal correspondence still require the prize's independent substantive review.
