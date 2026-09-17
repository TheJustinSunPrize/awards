# JSP-000368: Erdős 454, Pomerance's bound limsup (f(n) − 2pₙ) ≥ 2

Catalog entry: [JSP-000368](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0301-0400.md#JSP-000368) · Problem source: [erdosproblems.com/454](https://www.erdosproblems.com/454)

## Problem

Let `f(n) = min_{0<i<n} (p_{n+i} + p_{n−i})`, where `p_k` is the `k`-th prime. Is it true that `limsup_n (f(n) − 2p_n) = ∞`?

## Scope

Partial progress: Pomerance's theorem `limsup (f(n) − 2p_n) ≥ 2`, i.e. infinitely many `n` with `p_{n+i} + p_{n−i} ≥ 2p_n + 2` for all `0 < i < n`. Whether the limsup is infinite is open and not claimed.

## Formal statements

All results are in `Erdos454.lean`. The definition `f` and the statement `erdos_454.variants.two_le_limsup` are copied verbatim from Google DeepMind's formal-conjectures project (`FormalConjectures/ErdosProblems/454.lean`, Apache-2.0), including its 0-indexed `Nat.nth Prime` convention.

```lean
theorem erdos_454.variants.two_le_limsup :
    2 ≤ limsup (fun n => (f n - 2 * n.nth Prime : ℕ∞)) atTop

theorem exists_gt_forall_nth_prime_add_nth_prime (N : ℕ) :
    ∃ n > N, ∀ i, 0 < i → i < n →
      2 * n.nth Prime + 2 ≤ (n + i).nth Prime + (n - i).nth Prime

theorem frequently_two_mul_nth_prime_add_two_le_f :
    ∃ᶠ n in atTop, 2 * n.nth Prime + 2 ≤ f n
```

`erdos_454.variants.two_le_limsup` has the exact name and statement of the formal-conjectures theorem (category "research solved"), which is stated with `sorry` upstream; it is proved here, together with the elementary form `∀ N, ∃ n > N, ∀ 0 < i < n, 2p_n + 2 ≤ p_{n+i} + p_{n−i}`.

## Proof outline

(a) From `primorial x ≤ 4^x`, `c·m ≤ c·4^c + p_m` for all `c, m`, so `p_m − s·m → ∞` for every `s`. (b) Take `s = p_{N+1} + 1` and let `n` be the largest minimiser of `m ↦ p_m − s·m`; then `p_{n−i} − s(n−i) ≥ p_n − sn` and `p_{n+i} − s(n+i) > p_n − sn`, so `p_{n+i} + p_{n−i} > 2p_n`, and the choice of `s` forces `n > N`. (c) Both indices `n ± i` are at least 1, so both primes are odd and the sum is even, which upgrades `> 2p_n` to `≥ 2p_n + 2`.

## Build and verification

- Lean `v4.34.0` (`leanprover/lean4:v4.34.0`)
- Mathlib tag `v4.34.0`, commit `5ed2965256430c3649e86755f9576b54eca72435`; all dependencies are pinned in `lake-manifest.json`

```sh
lake exe cache get
lake build
```

`#print axioms` (see `verification/axioms.txt`):

```
'Erdos454.erdos_454.variants.two_le_limsup' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos454.exists_gt_forall_nth_prime_add_nth_prime' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos454.frequently_two_mul_nth_prime_add_two_le_f' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The file contains no `sorry`, no `axiom` declarations and no `native_decide`. The build log and the SHA-256 of
`Erdos454.lean` (`417a563b0fd2d62ab7a6f860afef2152b99dd0f2664c1d4351928874992b0b61`) are in `verification/`.

## Attribution

- Mathematics: C. Pomerance, *The prime number graph*, Math. Comp. 33 (1979), 399–408 [Po79].
- Lean formalization: GitHub user `baobingzhang`, developed with AI assistance (Anthropic Claude).


No priority for the mathematics is claimed; the contribution is the Lean formalization.
