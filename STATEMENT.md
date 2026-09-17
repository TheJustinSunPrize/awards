# Statement and scope

For a natural number N, let B(N) contain the positive integers a <= N such that
2a^2 <= N, or a is even and a^2 <= 2N. This is the usual Erdos construction,
expressed without real square roots.

The target theorem is:

For all natural numbers r and M, there exist N >= M and a finite set A such that
B(N) is a subset of A, every element of A lies in [1,N], every pair of elements
of A has least common multiple at most N, and |A| = |B(N)| + r.

The quantifiers have no finite search cutoff. Zero values of r and M are included.
In particular, the excess of the extremal cardinality over |B(N)| is unbounded
along a sequence of arbitrarily large N.

This does not prove the sharp asymptotic formula for the extremal cardinality,
nor the stronger quantitative iterated-logarithm bound in Chen and Dai (2007).
It is a formalization contribution to a known mathematical result.

## Definitions in Proof.lean

- `standard`: B(N), using the inequalities above.
- `Admissible`: subset of [1,N] and the actual `Nat.lcm` bound for every pair.
- `base`: [1,K] union twice [1,K]. `base_eq_standard` identifies it with B(2K^2).
- `extend_base`: the finite construction lemma with explicit assumptions.
- `unbounded_extension`: the unconditional target theorem.

No claim of prize eligibility, acceptance, independent reproduction, or a new
mathematical discovery is made.
