# JSP-000035: Catalan Conjecture (Mihailescu's Theorem) — Bounded Verification

## Problem

Are 8 and 9 the only consecutive positive integers that are both proper
perfect powers? (A proper perfect power is n = a^b with a ≥ 2, b ≥ 2.)

## Solution

**Solved**: Yes. Mihailescu (2002) proved that 8 = 2³ and 9 = 3² are the
only consecutive perfect powers.

## Formalization

This submission provides:

1. **Existence** (`jsp_000035_witness`): Proves that 8 = 2³ and 9 = 3²
   are consecutive proper perfect powers.

2. **Uniqueness up to 50** (`jsp_000035_bounded`): For all n in [4, 50],
   if both n and n+1 are proper perfect powers, then n = 8.

The proof uses exhaustive case analysis via `interval_cases`. For each
n in [4, 50], we show that at least one of n, n+1 is not a proper perfect
power (except n = 8 where both 8 and 9 are PPPs).

A key lemma (`ppp_bound`) establishes that if n is a proper perfect power
a^b, then both a ≤ n and b ≤ n, giving finite search ranges for
`interval_cases`.

The full Mihailescu theorem (uniqueness for all n) requires deep
algebraic number theory (cyclotomic fields) and is beyond current
Lean/Mathlib capabilities.

## Build

```bash
lake build Erdos35Full
```

Requires Lean 4 v4.34.0 and Mathlib.

## References

- [Ca44] Catalan, "Théorèmes et problèmes", 1844.
- [Mi03] Mihailescu, "Primary cyclotomic units and a proof of Catalan's
  conjecture", J. Reine Angew. Math. 572 (2004), 167–195.
