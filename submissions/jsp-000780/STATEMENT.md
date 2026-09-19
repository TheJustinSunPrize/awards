# Statement correspondence

## Sources and scope

- [Official JSP-000780 record](https://github.com/TheJustinSunPrize/awards/blob/f4e7173d89dfe91022a185427d63452c8ffbf6ae/problems/catalog-0701-0800.md#JSP-000780).
- [Erdős Problem 939](https://www.erdosproblems.com/939).
- [Pinned Formal Conjectures statement](https://github.com/google-deepmind/formal-conjectures/blob/40e7c98697de6f66b8cbdbf641749ab39ed9c152/FormalConjectures/ErdosProblems/939.lean).
- A. Nitaj, [On a Conjecture of Erdős on 3-Powerful Numbers](https://doi.org/10.1112/blms/27.4.317), Bull. London Math. Soc. 27 (1995), 317–318.
- J. H. E. Cohn, [A conjecture of Erdős on 3-powerful numbers](https://doi.org/10.1090/S0025-5718-98-00881-3), Math. Comp. 67 (1998), 439–440; [paper](https://pub.math.leidenuniv.nl/~smitbde/edu/bachsem/3-powerful_abc-triple.pdf).

The target is the complete positive-answer **triples subquestion**, not all
questions grouped under Erdős 939 or the catalogue's broad title. No new
mathematical discovery, higher-exponent result, or noncube strengthening is claimed.

## Definitions and checked declarations

`Nat.Full k n` is exactly the predicate `∀ p ∈ n.primeFactors, p^k ∣ n`.
`Finset.Coprime S` is exactly `S.gcd id = 1`. These are reproduced from the
pinned Formal Conjectures utility sources with their Apache-2.0 attribution.
The positive hypotheses exclude vacuous zero examples.

| Declaration | Scope |
| --- | --- |
| `Erdos939.triples_infinite` | Infinitude of the full positive 3-powerful, coprime solution set. |
| `Erdos939.erdos_939.variants.triples` | The source statement, replacing only `answer(True)` by `True` and omitting metadata attributes. |

The stronger internal predicate `Good a b c` includes `a.Coprime b`,
positivity, the three fullness conditions, `a+b=c`, and `3 ∣ a*b*c`.
With the sum identity, coprimality of the summands also implies pairwise
coprimality of all three entries. The final theorem does not impose the
extra divisibility invariant on the whole solution set: it proves that an
infinite subset satisfies it, then uses set inclusion.

## Proof outline

The seed is Nitaj's identity
`2^3 * 3^5 * 73^3 + 271^3 = 919^3`.
Lean checks its positivity, coprimality, fullness, and divisibility invariant.

For positive coprime summands `x > y` with `z=x+y`, define
`A=x*(x+2*y)^3`, `B=y*(2*x+y)^3`, and `C=(x+y)*(x-y)^3`.
The checked polynomial identity is `B+C=A`. Multiplication by cubes preserves
3-fullness. Any common prime of the two linear factors divides 3; the
invariant `3 ∣ x*y*z` excludes that prime. This gives coprimality, while the
old entries as factors preserve the invariant. Positivity and `A>z` are
proved. Summands may be swapped before the next step; they cannot be equal.

If the set of `Good` triples were finite, its third coordinate would attain
a maximum. Applying the construction to that triple gives a larger third
coordinate, a contradiction. No finite enumeration, numerical cutoff, or
assumed infinitude theorem is used.
