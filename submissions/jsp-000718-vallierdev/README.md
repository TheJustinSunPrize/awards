# JSP-000718 / Erdős Problem 866 — lower-bound formalization in Lean 4

A Lean 4 + Mathlib formalization contribution for
[The Justin Sun Prize](https://github.com/TheJustinSunPrize/awards), entry
[JSP-000718](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0701-0800.md#JSP-000718)
("How far above one half must density be to force all pairwise sums of a large
set?"), corresponding to [Erdős Problem 866](https://www.erdosproblems.com/866).

## The problem

Choi, Erdős and Szemerédi [CES75] define `g_k(N)` as the minimal number such
that every `A ⊆ {1, ..., 2N}` with `|A| ≥ N + g_k(N)` contains all `C(k,2)`
pairwise sums of some `k` distinct positive integers (the integers themselves
need not lie in `A`). They proved `g_3(N) = 2`, i.e. `N + 1` elements do not
suffice but `N + 2` elements always do.

## What is proved here

This package formalizes the **sharp lower-bound examples** for `k = 3`:

```lean
/-- Three integers cannot have all three pairwise sums odd. -/
theorem not_pairwise_sums_all_odd {x y z : ℕ}
    (hxy : Odd (x + y)) (hxz : Odd (x + z)) (hyz : Odd (y + z)) : False

/-- The odd numbers in [1, 2N] contain no such triple. -/
theorem oddsIn_avoid (N : ℕ) : ¬ HasTripleSumConfig (oddsIn N)

/-- The odd numbers in [1, 2N] together with 2 still contain no such triple. -/
theorem insert_two_oddsIn_avoid (N : ℕ) : ¬ HasTripleSumConfig (insert 2 (oddsIn N))

/-- g₃(N) ≥ 1: an avoiding set of size N. -/
theorem g3_lower (N : ℕ) :
    ∃ A : Finset ℕ, A ⊆ Finset.Icc 1 (2 * N) ∧ A.card = N ∧ ¬ HasTripleSumConfig A

/-- g₃(N) ≥ 2: an avoiding set of size N + 1, so density 1/2 + 1/(2N)
    does not force the configuration. -/
theorem g3_lower' (N : ℕ) (hN : 1 ≤ N) :
    ∃ A : Finset ℕ, A ⊆ Finset.Icc 1 (2 * N) ∧ A.card = N + 1 ∧ ¬ HasTripleSumConfig A
```

where

```lean
/-- Three distinct positive integers whose pairwise sums all lie in `A`. -/
def HasTripleSumConfig (A : Finset ℕ) : Prop :=
  ∃ x y z : ℕ, 1 ≤ x ∧ x < y ∧ y < z ∧ x + y ∈ A ∧ x + z ∈ A ∧ y + z ∈ A
```

### Proof outline

* **Parity obstruction** (`not_pairwise_sums_all_odd`): among any three
  integers, two share a parity, so one pairwise sum is even; three pairwise
  sums cannot all be odd.
* **Odd numbers avoid the configuration** (`oddsIn_avoid`): every member of
  `oddsIn N` is odd, so the parity obstruction applies directly.
* **Adding `2` does not help** (`insert_two_oddsIn_avoid`): a pairwise sum
  equal to `2` would be a sum of two distinct positive integers, hence at
  least `1 + 2 = 3`; so every pairwise sum must be odd, and the parity
  obstruction applies again.
* **Counting** (`card_oddsIn`): the odd numbers in `[1, 2N]` are the image of
  `range N` under `i ↦ 2i + 1`, so `|oddsIn N| = N`, and
  `|insert 2 (oddsIn N)| = N + 1` since `2` is not odd.

## Scope

Partial progress only. The matching upper bound `g_3(N) ≤ 2` (every
`A ⊆ {1, ..., 2N}` with `|A| ≥ N + 2` admits such a triple) is the theorem of
Choi, Erdős and Szemerédi [CES75] and is **not** claimed here. No statement
about `g_k` for `k ≠ 3`, and no award eligibility, is claimed or implied.

## References

* [CES75] S. L. G. Choi, P. Erdős and E. Szemerédi, *Some additive and
  multiplicative problems in number theory*, Acta Arith. (1975), 37–50.
* [erdosproblems.com/866](https://www.erdosproblems.com/866) — problem
  statement and known results (`g_3(N) = 2`, `g_4(N) ≤ 2338` by Wouter van
  Doorn).
* [JSP-000718](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0701-0800.md#JSP-000718) — the corresponding entry in The Justin Sun Prize problem bank.

## Verification

* Lean toolchain: `leanprover/lean4:v4.34.0`
* Mathlib: `v4.34.0` (commit
  `5ed2965256430c3649e86755f9576b54eca72435`), pinned in
  `lake-manifest.json`.
* `lake build` passes; the full log is in `verification/lake-build.log`.
* `#print axioms` for every main theorem reports exactly
  `[propext, Classical.choice, Quot.sound]` (`verification/axioms.txt`).
* No `sorry`, no `axiom` declarations, no `native_decide`.
* `Erdos866.lean` SHA-256 is recorded in `verification/sha256.txt`.

This is local verification only; it is not presented as official independent
verification by the prize.

## Authorship

The formalization was developed with AI assistance. The mathematics is the
classical parity argument recorded at erdosproblems.com/866 ("It is clear
that `g_k(N) ≥ 0` always", and the sharp `g_3(N) ≥ 2` example implicit in the
statement `g_3(N) = 2` attributed to Choi–Erdős–Szemerédi); no mathematical
priority is claimed.

## License

Apache-2.0 (see [LICENSE](LICENSE)).
