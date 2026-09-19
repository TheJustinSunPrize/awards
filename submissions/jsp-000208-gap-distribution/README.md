# JSP-000208: Gap Distribution Among Coprime Integers

## Problem

Determine the gap distribution among consecutive integers coprime to a product of the first several primes.

## Solution

**Solved** by Huxley (1965).

## Formalization

This submission verifies the gap patterns for small primorials:

- **P = 2** (prime {2}): coprimes in [1,8] = [1,3,5,7], gaps = [2,2,2]
- **P = 6** (primes {2,3}): coprimes in [1,13] = [1,5,7,11,13], gaps = [4,2,4,2]
- **P = 30** (primes {2,3,5}): coprimes in [1,31] = [1,7,11,13,17,19,23,29,31], gaps = [6,4,2,4,2,4,6,2]

The gap pattern for P=30 has period 8 (the Jacobsthal function g(30)=6, maximum gap).

## Build

```bash
lake build Erdos208
```

Requires Lean 4 v4.34.0 and Mathlib.

## References

- [Ho65] Huxley, Publ. Math. Debrecen 12 (1965), 39-49.
