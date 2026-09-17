# JSP-000171: Erdős 176, Spencer's exact value N(k,1) = 2^t(k−1)+1 for k = 2^t·m (m odd), and N(k,2) = N(k,1) for even k

Catalog entry: [JSP-000171](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0101-0200.md#JSP-000171) · Problem source: [erdosproblems.com/176](https://www.erdosproblems.com/176)

## Problem

Let `N(k,ℓ)` be the minimal `N` such that for any `f : {1,…,N} → {−1,1}` there is a `k`-term arithmetic progression `P` with `|∑_{n∈P} f(n)| ≥ ℓ`. Find good upper bounds for `N(k,ℓ)`. Is it true that for any `c > 0` there is `C > 1` with `N(k,ck) ≤ C^k`? What about `N(k,2) ≤ C^k` or `N(k,√k) ≤ C^k`?

## Scope

Partial progress: Spencer's exact formula `N(k,1) = 2^t(k−1)+1` for `k = 2^t·m` with `m` odd [Sp73], recorded on erdosproblems.com/176 and credited in the catalog record JSP-000171, together with the parity consequence `N(k,2) = N(k,1)` for even `k` (observed on the erdosproblems forum). The questions `N(k,ck) ≤ C^k`, `N(k,2) ≤ C^k` for odd `k` and `N(k,√k) ≤ C^k` are not addressed here; note that KitaKen1 (github.com/KitaKen1/erdos176-nk2-polynomial-bound-lean and …-nksqrtk-polynomial-bound-lean, June 2026) has Lean formalizations of polynomial upper bounds for `N(k,2)` and `N(k,√k)`, which are separate work and not claimed here.

## Formal statements

All results are in `Erdos176.lean`. `Set.IsAPOfLengthWith` and `Set.IsAPOfLength` are copied verbatim from Google DeepMind's formal-conjectures (`FormalConjecturesForMathlib/Combinatorics/AP/Basic.lean`, Apache-2.0); `ForcesDiscrepancy` and `discrepancyAPNumber` are copied verbatim from the open statement-only formal-conjectures PR #4693 (by arex1337); `forcesDiscrepancy_iff` shows equivalence with an elementary formulation in case the PR's definitions change.

```lean
theorem discrepancyAPNumber_one {k t m : ℕ} (hm : Odd m) (hk : k = 2 ^ t * m) :
    discrepancyAPNumber k 1 = (2 ^ t * (k - 1) + 1 : ℕ)

theorem discrepancyAPNumber_one_padicValNat {k : ℕ} (hk : k ≠ 0) :
    discrepancyAPNumber k 1 = (2 ^ padicValNat 2 k * (k - 1) + 1 : ℕ)

theorem discrepancyAPNumber_two_eq_one {k : ℕ} (hk : Even k) (hk0 : k ≠ 0) :
    discrepancyAPNumber k 2 = discrepancyAPNumber k 1

theorem discrepancyAPNumber_two {k t m : ℕ} (ht : 1 ≤ t) (hm : Odd m) (hk : k = 2 ^ t * m) :
    discrepancyAPNumber k 2 = (2 ^ t * (k - 1) + 1 : ℕ)

theorem forcesDiscrepancy_one_iff {k t m : ℕ} (hm : Odd m) (hk : k = 2 ^ t * m) (N : ℕ) :
    ForcesDiscrepancy N k 1 ↔ 2 ^ t * (k - 1) + 1 ≤ N

theorem isLeast_forcesDiscrepancy_one {k t m : ℕ} (hm : Odd m) (hk : k = 2 ^ t * m) :
    IsLeast {N | ForcesDiscrepancy N k 1} (2 ^ t * (k - 1) + 1)

theorem exists_balanced_colouring {k t m : ℕ} (hm : Odd m) (hk : k = 2 ^ t * m) :
    ∃ f : ℕ → ℤ, (∀ n, f n = 1 ∨ f n = -1) ∧
      ∀ a d : ℕ, 1 ≤ a → 1 ≤ d → a + (k - 1) * d ≤ 2 ^ t * (k - 1) →
        ∑ i ∈ range k, f (a + i * d) = 0

theorem forcesDiscrepancy_iff {N k : ℕ} (hk : 1 ≤ k) (ℓ : ℝ) :
    ForcesDiscrepancy N k ℓ ↔ ForcesDiscrepancyAP N k ℓ
```

With `Set.IsAPOfLengthWith`, `Set.IsAPOfLength` (formal-conjectures, verbatim) and `ForcesDiscrepancy`, `discrepancyAPNumber` (verbatim from the statement-only formal-conjectures PR #4693; `N(k,ℓ)` as an `sInf` in `ℕ∞`, so `⊤` rather than a junk value if no `N` works): `discrepancyAPNumber_one : Odd m → k = 2^t·m → N(k,1) = 2^t(k−1)+1`, `discrepancyAPNumber_one_padicValNat`, `discrepancyAPNumber_two_eq_one : Even k → k ≠ 0 → N(k,2) = N(k,1)`, `discrepancyAPNumber_two`, and both directions explicitly: `forcesDiscrepancy_one_iff : ForcesDiscrepancy N k 1 ↔ 2^t(k−1)+1 ≤ N`, `isLeast_forcesDiscrepancy_one`, `exists_balanced_colouring` (an explicit colouring of `{1,…,2^t(k−1)}` in which every `k`-term AP sums to 0), and `forcesDiscrepancy_iff` (equivalence with an elementary AP formulation).

## Proof outline

Upper bound: if every `k`-term AP sums to 0, comparing overlapping runs of `k` consecutive integers gives `f(a+k) = f(a)`; then the AP `1, 1+2^t, …, 1+(k−1)2^t` splits into `2^t` equal blocks of `m` signs, so its sum is `2^t` times an odd number, contradiction. Lower bound (`t ≥ 1`): colour `n` by `(−1)^⌊n/h⌋` with `h = k/2`; any fitting AP has difference `d < 2^t`, and writing `d = 2^u·e` (`e` odd), shifting the index by `2^{t−1−u}·m` flips every sign while the sum is `k`-periodic, so the sum equals its negative and is 0. Parity: for even `k` a sum of `k` signs is even, so `|s| ≥ 1 ⇔ |s| ≥ 2`.

## Build and verification

- Lean `v4.34.0` (`leanprover/lean4:v4.34.0`)
- Mathlib tag `v4.34.0`, commit `5ed2965256430c3649e86755f9576b54eca72435`; all dependencies are pinned in `lake-manifest.json`

```sh
lake exe cache get
lake build
```

`#print axioms` (see `verification/axioms.txt`):

```
'Erdos176.discrepancyAPNumber_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos176.discrepancyAPNumber_one_padicValNat' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos176.discrepancyAPNumber_two_eq_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos176.discrepancyAPNumber_two' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos176.forcesDiscrepancy_one_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos176.isLeast_forcesDiscrepancy_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos176.exists_balanced_colouring' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos176.forcesDiscrepancy_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The file contains no `sorry`, no `axiom` declarations and no `native_decide`. The build log and the SHA-256 of
`Erdos176.lean` (`e2c4b80b07124711f7a7d2a8cb63f71bb5013dca0c096e67e5cd1e6e4f184564`) are in `verification/`.

## Attribution

- Mathematics: J. Spencer, solution to Problem P.185, Canad. Math. Bull. (1973) [Sp73], cited by the catalog record JSP-000171 and erdosproblems.com/176; parity observation from the erdosproblems.com/176 forum; problem of Erdős [Er63d] and Erdős–Graham. The Lean proof reconstructs the argument (Spencer's note was not consulted), written with AI assistance.
- Lean formalization: GitHub user `baobingzhang`, developed with AI assistance (Anthropic Claude).


No priority for the mathematics is claimed; the contribution is the Lean formalization.
