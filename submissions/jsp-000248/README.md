# JSP-000248: Formal verification of largest denominators in Egyptian fraction representations of 1

This package provides a formal Lean 4 verification of finite witnesses and bounds for **JSP-000248** (Erdős & Graham 1980, solved by Greg Martin 2000):

> **Problem**: Which positive integers can be the largest denominator in a representation of one by distinct unit fractions?

## Mathematical scope

A unit fraction representation of 1 is a decomposition
$$\sum_{i=1}^k \frac{1}{d_i} = 1$$
with integers $2 \le d_1 < d_2 < \dots < d_k = N$.

Greg Martin (2000, *Acta Arithmetica*) proved that every sufficiently large integer (and in fact all integers except a small finite set of exceptions) can be the largest denominator.

This submission provides standalone, machine-checked Lean 4 certificates for the initial boundary and constructive witnesses:
1. **Exhaustive impossibility for $N \le 5$**:
   All nonempty subsets of $\{2, 3, 4, 5\}$ are evaluated against common multiple $M = 60$. No subset sums to 1. Hence, no integer $N \le 5$ can be the largest denominator.
2. **Minimal witness $N = 6$**:
   The decomposition $1 = \frac{1}{2} + \frac{1}{3} + \frac{1}{6}$ certifies that $N = 6$ is the smallest possible largest denominator.
3. **Explicit constructive witnesses**:
   Formal certificates are verified for $N \in \{6, 12, 18, 20, 24\}$:
   - $N=6$: `[2, 3, 6]`
   - $N=12$: `[2, 4, 6, 12]`
   - $N=18$: `[2, 3, 9, 18]`
   - $N=20$: `[2, 4, 5, 20]`
   - $N=24$: `[2, 3, 8, 24]`

## Verification details

- **File**: `LargestDenominator.lean`
- **Toolchain**: Lean 4 (compatible with Lean 4.x standard kernel `decide`)
- **Axioms**: Standard kernel evaluation, no `sorry`, no `unsafe`, no external solver oracle.
- **Scope note**: This is AI-assisted supplemental finite evidence and constructive certificates for JSP-000248. Mathematical credit belongs to Erdős, Graham, and Greg Martin. No catalog status or award claim is modified.
