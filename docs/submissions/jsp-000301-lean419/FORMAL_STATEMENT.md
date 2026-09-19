# Formal statement and correspondence

## English

The target is the scoped yes/no question in [JSP-000301](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0301-0400.md#JSP-000301).
The formal result refutes the implication that a pair of consecutive positive
powerful integers must contain a square.

## Definitions

```lean
def JSP301.Powerful (n : ℕ) : Prop :=
  0 < n ∧ ∀ p : ℕ, Nat.Prime p → p ∣ n → p ^ 2 ∣ n
```

This document displays the fully qualified name for clarity; the source declares
`Powerful` inside `namespace JSP301`.

Positivity is explicit. The prime-divisor quantifier ranges over every natural
prime, not a list restricted to the example's factors. `Nat.Prime`, divisibility,
and `IsSquare` come from the pinned Lean/Mathlib environment, with no replacement
of their meanings. The source uses `IsSquare` over `ℕ`; there is no restriction on
the potential natural square root.

## Exact exported statements

```lean
JSP301.known_counterexample :
  ∃ n : ℕ, JSP301.Powerful n ∧ JSP301.Powerful (n + 1) ∧
    ¬ IsSquare n ∧ ¬ IsSquare (n + 1)

JSP301.catalog_statement_false :
  ¬ (∀ n : ℕ, JSP301.Powerful n → JSP301.Powerful (n + 1) →
    IsSquare n ∨ IsSquare (n + 1))
```

These are displayed types. The executable declarations, including their proofs,
are in `JSP301.lean`.

## Proof argument

The witness is `n = 12167`. Exact arithmetic verifies
`12167 = 23^3` and `12168 = 2^3 * 3^2 * 13^2`.
For an arbitrary prime divisor of the first integer, primality forces that divisor
to be 23. For an arbitrary prime divisor of the second, the prime-divisor-of-a-product
and prime-divisor-of-a-power facts reduce the possibilities to 2, 3, or 13.
The square of each possible prime divides the relevant integer.

For either integer `m`, the exact bounds `12100 < m < 12321` rule out a square.
For any proposed natural root `k`, either `k ≤ 110`, implying `k*k ≤ 12100`,
or `111 ≤ k`, implying `12321 ≤ k*k`. Both cases contradict the bounds.

The existential witness then directly contradicts the universally quantified
square implication. There are no extra hypotheses about the integers, primes,
or possible roots. `autoImplicit` is disabled.

## Scope and review status

This is not a density or asymptotic counting theorem and does not settle Erdős #365.
The scope comparison above is supplied by the preparing assistant, not signed by
an independent reviewer. Maintainers should review the definitions and correspondence
before recording official verification. The catalog already supplies the mathematical
counterexample; original mathematical discovery is not claimed.
