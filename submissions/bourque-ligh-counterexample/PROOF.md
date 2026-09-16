# Statement and proof certificate

For a finite set `S` of positive natural numbers, let `L(S)` be the square
matrix whose entry in row `a` and column `b` is `Nat.lcm a b`.
The set is GCD-closed if `Nat.gcd a b` belongs to `S` for every `a,b` in `S`.
The Bourque–Ligh conjecture states that `det L(S) != 0` for every such set.

## Formal statement correspondence

`GCDClosed` quantifies over all pairs of members, including equal members.
`lcmMatrix` is indexed by the subtype of elements of `S`; every element indexes
exactly one row and one column. Thus distinctness is part of the finite-set
representation. Positivity is a separate checked hypothesis.
The matrix entries use Mathlib's `Nat.lcm`, and singularity uses Mathlib's
`Matrix.det` and matrix-vector multiplication.

The main counterexample is the entire published set

```text
S = {1, 2, 3, 4, 5, 6, 10, 45, 180}.
```

Its cardinality, positivity and closure are proved by finite decision
procedures. With coordinates in the displayed order, the certificate is

```text
v = (-180, 180, 60, -45, 36, -30, -18, -4, 1).
```

The proof verifies the exact identity `L(S) v = 0`. The coordinate at `180`
is `1`, so `v` is nonzero. A matrix with nonzero determinant has trivial
kernel; consequently `det L(S) = 0`. Substituting `S` into the universal
conjecture gives its negation.

The real matrix is obtained by entrywise casting the integer matrix. The
determinant commutes with this ring homomorphism, so its determinant is also
zero over the real numbers. This explicitly connects the integer certificate
to ordinary nonsingularity over a field.

## Mathematical scope

The result formalized here is the disproof of the original universal
nonsingularity conjecture by its published nine-element counterexample.
The later classification of small cardinalities is a separate result.
