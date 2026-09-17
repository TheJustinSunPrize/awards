# Independent semantic audit of the four-prime theorem

Date: 2026-09-17. Auditor: the separate proof-attempt agent.

Result: no mismatch was identified between `Erdos700.FourPrime.four_prime_exact`
and the local four-prime lemma in the human-readable manuscript. No omitted
pair, narrower minimization range, extra mathematical hypothesis, or assumed
conclusion was found in the source proof reviewed here.

This is a source-level semantic audit, supplemented by a compiled dependency
axiom check. The independent complete build and final-theorem axiom audit are
recorded in `verification/`. This audit did not modify any theorem source.

## Snapshot

The reviewed final `Erdos700/FourPrime.lean` has SHA-256:

`796ED3599CCA2973D7E6A6D3B556B7460F657A524529A1453914D237696B3DEC`

`Erdos700/Minimum.lean` has SHA-256:

`4B3EBD40441FAA26AD3C4CF31727318926CD0ABE56D59353E136B2ABB7BAE481`

Release packaging addendum (2026-09-17): the packet text was normalized
to UTF-8 with LF line endings, no trailing horizontal whitespace, and one
final newline. Lean source changes were limited to CRLF-to-LF conversion and
removal of an extra final blank line; no other source characters changed.
No mathematical or Lean content changed: every released
Lean source was compared with the original audited snapshot after that
same whitespace normalization and matched exactly. The two hashes above
identify the normalized release bytes. A fresh build and final theorem
audit of those release bytes are recorded under `verification/`.

The local comparison copy of the upstream Formal Conjectures problem 700
statement has SHA-256:

`AA583A47B578A8AC29FA2A6A050683F3D030623DF21D7566EEB561C0B040A375`

## Exact statement and scope

The final theorem quantifies natural numbers `P,A,B,C`, assumes exactly

- `1 ≤ A`;
- `3*A ≤ B`;
- `10*B^2 ≤ C`;
- `100*C^5 ≤ P`;
- primality of `P`, `P+A`, `P+B`, and `P+C`;

and concludes

```text
f (P*(P+A)*(P+B)*(P+C)) = P*(P+A)*(P+B).
```

There are no surrounding section variables or additional implicit hypotheses
in the theorem's source. These assumptions match the human-readable local
lemma: the natural-number formulation loses no positive-integer cases.
`A ≥ 1` and the other parameter inequalities imply `B,C > 0`; primality implies
`P > 0`. The derived strict ordering is `P < P+A < P+B < P+C`.

The theorem is conditional on the four displayed integers being prime. It
does not itself assert that any such quadruple exists, that infinitely many
exist, or any asymptotic statement.

## Definition of the minimum and its nonempty range

The local definition of `Erdos700.f` is textually the same mathematical
definition used by the checked upstream `FormalConjectures/ErdosProblems/700.lean`:

```lean
noncomputable def f (n : ℕ) : ℕ :=
  sInf {m | ∃ k, 1 < k ∧ k ≤ n / 2 ∧ m = Nat.gcd n (n.choose k)}
```

Thus the index range is exactly `2 ≤ k ≤ floor(n/2)`, with the natural-number
binomial coefficient and gcd. It is not a restricted set of prime indices,
indices divisible by a selected factor, or a different gcd function.

The use of `sInf` does not hide an empty-set case. `largest_prime_in_range`
proves that the largest prime `s` lies in the range for the product of the four
primes. `gcd_four_primes_at_largest` proves equality with the product of the
three smaller primes at this index. That witness establishes nonemptiness
before `Nat.sInf_mem` is used for the lower bound.

The upper-bound witness is exactly the manuscript's `k=P+C`. Its gcd proof
uses primality and strict ordering to show the three smaller primes divide
the binomial while `P+C` does not. Distinctness also makes the product
squarefree for this step. The argument does not assume the six exclusions
in order to construct the witness.

## Natural numbers, integer arithmetic, and digit positions

The prime, row, index, gcd, and binomial coefficient remain natural numbers.
The cast to integers is used for parameter inequalities, signed polynomial
coefficients, and Euclidean division. All four bases are positive, and the
casted divisions/moduli are connected back to natural-number operations in
`IntDigitSupport.lean`; no truncating subtraction is introduced into the
signed carry calculations.

The source digit bounds follow from Lucas, the four legal row expansions,
and a proved quotient range. They are not hypotheses of `four_prime_exact`.
`ParameterDigits.parameter_quotient_lt_cube` proves that range from
`2*k ≤ N`, `P ≤ x`, and `N < 2*P^4`. Hence `k/x < x^3`, so the three source
digits exhaust the quotient. This applies through the endpoint
`k=floor(N/2)` as well as to smaller indices.

The target digit positions are correctly shifted by the initially removed
factor of the target base `q`:

| Digit of `k/q` | Integer expression used |
| --- | --- |
| Low | `(k/q) % q` |
| Middle | `(k/q/q) % q` |
| High | `(k/q/q/q) % q` |

The third expression is the high digit of the quotient, not an extra digit.
The target bounds come directly from `int_lucas_three_digit_bounds`. The
target interface need not assume `q ∣ N` separately to obtain those bounds;
the prime-factor property is established in the main proof and is used when
deriving divisibility of `k`.

## All six unordered pairs

`NoTwoMissing` explicitly lists all six unordered pairs. The assembled proof
handles them in the same order:

| Missing pair | Source base | Target base | Exclusion used |
| --- | --- | --- | --- |
| `P, P+A` | `P+A` | `P` | `Arithmetic.pairAP_zero_digits` |
| `P, P+B` | `P` | `P+B` | `ParameterP.pairPB_global_digits` |
| `P, P+C` | `P` | `P+C` | `ParameterP.pairPC_global_digits` |
| `P+A, P+B` | `P+A` | `P+B` | `PairADigits.pairAB_global_digits` |
| `P+A, P+C` | `P+A` | `P+C` | `PairADigits.pairAC_global_digits` |
| `P+B, P+C` | `P+B` | `P+C` | `ParameterBC.pairBC_actual_digits` |

Reversing the first pair is intentional and matches the residue argument in
the manuscript. It needs no separate target digit hypothesis: divisibility
of the source quotient by `P` already forces all three source digits to
vanish. The main proof then contradicts the original positive index.

For every pair, divisibility of the source quotient by the other prime is
proved using the corresponding binomial nondivisibility, Lucas's lowest
digit implication, and distinctness of the two primes. It is not assumed
without proof and is not confused with divisibility of the original index.

The target `P+B` bounds are exactly `(C, q-B, R-1)` in the manuscript's
notation. The target `P+C` bounds are exactly `(q-F, U-1, q-D)`. Pair proofs
that only need the first two bounds intentionally discard the third; this
strengthens their applicability and does not weaken the final conclusion.

## Auxiliary hypotheses and generic lemmas

The generic carry lemmas expose size and digit hypotheses. The main theorem
does not retain any of them as additional assumptions:

- Row digit legality is discharged by `ParameterDigits`.
- Signed carry ranges and large-base inequalities are discharged by
  `ParameterP`, the global wrappers in `PairADigits`, and `ParameterBC`.
- Actual integer remainders are connected to the normalization functions
  before the normalized exclusions are applied.
- The source representations and target bounds are derived independently
  from the two supposed missing primes.

In particular, the last pair constructs its internal `H,J,K` and derives the
middle correction `-2*H`; it does not assume the desired contradictory
middle interval. No generic lemma used by the main proof assumes
`NoTwoMissing`, the minimum equality, or a logically equivalent conclusion.

After the pair exclusions, `threeOfFour_of_noTwoMissing` is the elementary
propositional step that at least three primes divide every relevant
binomial. The smallest product of three of the ordered primes supplies the
gcd lower bound, which is combined with the witnessed upper bound.

## Dependency trust check

`AuditCoreIndependent.lean` was an internal auxiliary audit, not included in
this packet. It was run successfully with the configured Lean 4.33.1/Mathlib
environment. Its twelve `#print axioms` queries cover the
minimum framework, the integer Lucas support, source quotient divisibility,
all six pair exclusions, the quotient range, and a row expansion.

All queried declarations depend only on subsets of the standard axioms
`propext`, `Classical.choice`, and `Quot.sound`. No `sorryAx` or custom axiom
appeared. A source scan of the local `Erdos700` files also found no `sorry`,
`admit`, custom `axiom`, `native_decide`, `unsafe`, `extern`, or
`implemented_by` declaration.

The included `Audit.lean` reproduces the complete final theorem's transitive
axiom audit, together with its type and the definition of `f`; the public
result is recorded in `verification/canonical-audit.log`.

The upstream open problem file, which contains unproved problem statements,
is used only as a comparison source for the definition of `f`; it is not
imported by this development.

## What this audit does not establish

This audit does not establish novelty or priority in the literature, prize
eligibility, or the truth of an unformalized external statement. It does not
claim that Maynard's theorem, the admissible tuple construction, the
infinite-family consequence, or `f(N)~N^(3/4)` has been formalized here.

The conclusion audited is the complete local four-prime equality criterion,
with the original parameters and the original full minimization range.
