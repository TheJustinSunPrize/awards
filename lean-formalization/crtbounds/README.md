# CRT Lower Bound — Lean 4 Formalization

## Main Theorem

```
theorem crt_lower_bound (n : ℕ) (hn : 4 ≤ n) :
    3 ^ windowSize n ≤ lcmUpTo n
```

where `windowPrimes n = {p ∈ (n/2, n] : Prime}` and `windowSize n = |windowPrimes n| = π(n) - π(n/2)`.

This proves `3^(π(n)-π(n/2)) ≤ lcm(1,...,n)` for all n ≥ 4.

## Proof Architecture

1. **p-adic obstruction** (`padic_obstruction_core`): For prime p > n/2, every signed subsum numerator m(ε) satisfies m(ε) ≡ ε_p · c_p (mod p) where c_p = (L/p) mod p ≠ 0.

2. **Injectivity** (`proj_inj`): The p-adic projection is injective: if m(ε₁) ≡ m(ε₂) (mod p) and |δ_p| ≤ 1, then ε₁_p = ε₂_p.

3. **Counting**: Window primes are pairwise coprime, their product divides L, and each is ≥ 3, so 3^|W| ≤ ∏p ≤ L.

## Verification

- Lean 4 version: 4.35.0-rc2
- Mathlib commit: f61f3ed7633ff99ecaae4a086395b501652a76ee
- Zero `sorry`, standard axioms only
- `lake build` passes
