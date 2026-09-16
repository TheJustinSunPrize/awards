# Statement correspondence

## English

Original problem: can there exist `k > 2` and a colouring of all `k`-subsets of a
`2k`-element set with `k+1` colours such that every `(k+1)`-subset contains subsets
of all `k+1` colours?

Sources:

- [Erdős problem 835](https://www.erdosproblems.com/835).
- [Ma–Tang, On Problem 835](https://github.com/QuanyuTang/erdos-problem-835/blob/7f131832bab5abfc903014ddb61efff21d56ae01/On_Problem_835.pdf).
- [Formal Conjectures definition](https://github.com/google-deepmind/formal-conjectures/blob/40e7c98697de6f66b8cbdbf641749ab39ed9c152/FormalConjectures/ErdosProblems/835.lean).

The submitted theorem is the following necessary condition, with the original
finite-set definition reproduced verbatim:

```lean
theorem Erdos835.property_successor_prime {k : ℕ}
    (hk : 1 ≤ k) (h : Erdos835.Property k) : (k + 1).Prime
```

Its direct corollary is:

```lean
theorem Erdos835.not_property_of_composite {k : ℕ}
    (hk : 1 ≤ k) (hc : ¬ (k + 1).Prime) : ¬ Erdos835.Property k
```

The bound `k ≥ 1` includes the entire range `k > 2` in the original question.
There is no bounded search, finite cutoff, assumed colouring, or custom axiom
standing in for a mathematical step. The prime-successor cases are deliberately
not claimed. No chromatic-number equivalence from an unproved upstream theorem
is used.

## Proof

1. A `(k+1)`-set has exactly `k+1` subsets of size `k`. Its rainbow colouring is
   therefore injective.
2. The `k+1` extensions of a fixed `(k−1)`-set lie pairwise in top cliques.
   Consequently every colour occurs exactly once among these extensions.
3. Fix a set `L` of size `k−t`, where `1 ≤ t ≤ k`, and a colour. Double count
   incidences between `(k−1)`-sets containing `L` and colour-matching `k`-sets
   containing `L`. Every smaller set has one extension; every larger set contains
   exactly `t` such smaller sets. Thus `t` divides `choose (k+t) (t−1)`.
4. If `k+1` is composite, take its least prime divisor `p ≤ k`. Lucas's theorem
   gives `choose (k+p) (p−1) ≡ 1 (mod p)`, contradicting step 3 at `t=p`.

The internal total colouring is used only on sets of size `k`. The final theorem
derives it from the dependent colouring in `Erdos835.Property`, so arbitrary
values outside that size do not weaken the submitted conclusion.
