# Internal semantic audit: the four-prime theorem and its zero-gap counterexample

Date: 2026-09-17. Reviewer: the separate internal audit agent.

**Source-review result: the new counterexample statements concern concrete natural numbers and leave no primality, digit, or auxiliary arithmetic assumption unproved.** They certify the gcd at one admissible index, derive a strict upper bound for the minimum, and refute the proposed universal zero-gap extension. The preceding five positive theorem statements are unchanged. The final fresh build, source binding, and 11-declaration axiom audit passed as recorded below.

This is internal AI-assisted review, not external human peer review or designated prize verification. The reviewer implemented `CounterexampleLucas.lean` and then reviewed its integration and the final counterexample statements. Another internal agent assembled `Counterexample.lean`; a third prepared the primality certificates; the root agent handled project integration and documentation. The reviewer also participated in preceding versions. These roles do not establish external independence, historical priority, organizer acceptance, or an award.

## Reviewed source snapshot

The reviewed frozen source bytes have these SHA-256 digests:

| File | SHA-256 |
| --- | --- |
| `Erdos700/Counterexample.lean` | `b805e372901deac15f059355cefbd9070f8fec9c68ddee6d1f18207a644db10c` |
| `Erdos700/CounterexamplePrimes.lean` | `6fde684b8329216abcece02cbb5418d1f10ee0abb3441008c3324f6c61c8da1e` |
| `Erdos700/CounterexampleLucas.lean` | `7a95a15773e6afbc09ca2d509bfd0d33822880fac77a13fa11e30dbef376c5b3` |
| `Erdos700/FourPrime.lean` | `aff6314ea5fe169b19bbbdbe8dc8970c4260c6b836c939125967fb084546e033` |
| `Erdos700/Minimum.lean` | `4b3ebd40441faa26ad3c4cf31727318926cd0abe56d59353e136b2abb7bae481` |
| `Audit.lean` | `3cb8685e8267e39e13aef4c04fa68dc845cc8eb00f7003273bc437f248b85d67` |

The source scan found no `sorry`, `admit`, custom `axiom`, `native_decide`, `unsafe`, `extern`, or `implemented_by` declaration. The audit explicitly prints the definitions of `f`, `P`, `N`, and `k`, then the types and transitive axiom lists of all five positive and six new counterexample declarations. It does not audit only an abstract helper while omitting the final concrete result.

## Exact concrete definitions

`Erdos700.Counterexample` defines ordinary natural numbers:

```lean
def P : ℕ := 25480409371
def N : ℕ := P * (P + 6) * (P + 18) * (P + 48)
def k : ℕ := 19 * P ^ 2 * (P + 18)
```

Their values are

```text
N = 421527202027998836984769084169268008898197
k = 314320570951028896159815520413631.
```

The unchanged definition of the function is

```lean
noncomputable def f (n : ℕ) : ℕ :=
  sInf {m | ∃ k, 1 < k ∧ k ≤ n / 2 ∧ m = Nat.gcd n (n.choose k)}
```

Thus the index condition is exactly `2<=k<=floor(N/2)`. No alternate function, restricted divisibility range, truncated digit predicate, or hypothetical binomial coefficient replaces the original objects.

## The six newly audited declarations

All names in this table are in `Erdos700.Counterexample`. None has an explicit or implicit mathematical hypothesis.

| Declaration | Exact mathematical content |
| --- | --- |
| `four_primes` | `P`, `P+6`, `P+18`, and `P+48` are prime. |
| `index_in_range` | `1<k` and `k<=N/2`. |
| `gcd_at_index` | `Nat.gcd N (N.choose k) = (P+6)*(P+48)`. |
| `f_strict_upper_bound` | `f N < P*(P+6)*(P+18)`. |
| `zero_gap_counterexample` | Bundles the offset inequalities, equality `48=3*18-6`, the old strong size bound, all four primality facts, index range, exact gcd, and strict upper bound. |
| `zero_gap_extension_false` | Negates the universal exact-value criterion with `c>=3b-a` and `P>=100c^5`. |

The final negation is precisely

```lean
¬ ∀ p a b c : ℕ, 1 ≤ a → 3 * a ≤ b → 3 * b - a ≤ c →
  100 * c ^ 5 ≤ p → p.Prime → (p + a).Prime → (p + b).Prime →
  (p + c).Prime →
  f (p * (p + a) * (p + b) * (p + c)) = p * (p + a) * (p + b)
```

This refutes the proposed change even with the earlier, stronger size premise. The proof specializes the universal assertion at `p=P,a=6,b=18,c=48`; all its premises are proved directly. Natural subtraction is harmless here: the concrete `3*18-6` is 48, with no truncation. The counterexample does not satisfy the maintained positive theorem's `3b-a+1<=c` condition, so it does not contradict any of the existing positive theorems.

## Concrete primality certificates

`CounterexamplePrimes.lean` invokes Mathlib's `lucas_primality`, a sufficient primality criterion with no primality premise on its target. For each target `m`, the file proves `g^(m-1)=1` in `ZMod m` and `g^((m-1)/r)!=1` for every prime `r` dividing `m-1`. The factorizations and witnesses are:

| Target `m` | Complete factorization of `m-1` | Witness `g` |
| --- | --- | --- |
| `25480409371` | `2*3*5*13*17*3843199` | `7` |
| `25480409377` | `2^5*3*523*507497` | `13` |
| `25480409389` | `2^2*3*7*563*538789` | `2` |
| `25480409419` | `2*3^2*37*263*145471` | `2` |

Each smaller prime factor has a proved `Nat.Prime` declaration, discharged by `norm_num`. The product equalities are exact arithmetic. Prime divisibility of a product reduces every possible prime divisor to one of the listed factors, including the repeated factors of 2 and 3. `reduce_mod_char` produces proofs of the modular-power identities, and ordinary `decide` closes the resulting finite inequalities. This is not `native_decide`, a Python primality flag, a probable-prime test, or an unproved assertion that the factorization is complete.

The main file derives `four_primes` from those four unconditional declarations after reducing the concrete additions. No target prime is assumed in order to prove itself. The modular criterion is distinct from the binomial Lucas theorem used next.

## Converse Lucas interface

The new helper `CounterexampleLucas.not_dvd_choose_of_digits_lt` takes a prime `p`, bounds `n<p^d` and `k<p^d`, and exactly `d` digit comparisons

```text
∀ i, i<d → k/p^i % p <= n/p^i % p.
```

It concludes `p` does not divide `n.choose k`. This is a general proved implication, not a certificate axiom. A short induction proves that a prime larger than `n` cannot divide `n!`. The identity `choose(n,k)*k!*(n-k)!=n!` then shows that a binomial formed from ordered legal digits is nonzero modulo the prime. Mathlib's one-digit Lucas congruence and the prime product-divisibility rule reattach one digit at a time. Induction on `d` finishes the result; the power bounds prove the tail vanishes. At `d=0`, both input integers are zero and `choose(0,0)=1`.

There is no evaluation of a huge factorial or binomial coefficient in this construction. The use of factorials is a universal symbolic argument. The helper imports the proved Mathlib Lucas theorem, not an upstream open-conjecture declaration.

## Exact digits and divisibility pattern

The main counterexample applies the finite converse with `d=5` at base `P` and `d=4` at base `q=P+18`. `interval_cases` exhausts the finite digit positions and `norm_num` proves each concrete quotient, remainder comparison, and power bound. Both original numbers have units digit zero at these two bases. The quotient lists, in increasing place value and padded with final zeroes where useful, are

| Base | Digits of `N/base` | Digits of `k/base` |
| --- | --- | --- |
| `P` | `[5184,1260,72,1]` | `[0,342,19,0]` |
| `q=P+18` | `[6480,q-684,q-1,0]` | `[6156,q-684,18,0]` |

The exact comparisons prove that neither `P` nor `P+18` divides `N.choose k`.

For the other two primes, the existing forward Lucas lemma states that nondivisibility would require the units digit of `k` to be at most that of `N`. The latter is zero, but the actual residues are

```text
k mod (P+6) = 8208,
k mod (P+48) = 25479096139 = (P+48)-1313280.
```

Both are positive. The concrete arithmetic contradiction therefore proves that `P+6` and `P+48` do divide the binomial coefficient. These proofs reason about the actual `N.choose k`; they do not postulate its four-prime support.

## From the support pattern to the claimed conclusions

Primality and the two missing factors give

```text
Coprime (P*(P+18)) (N.choose k).
```

The other two primes are distinct, so their coprimality and individual divisibility give `(P+6)*(P+48) | N.choose k`. After reordering the four-factor product, `Nat.gcd_mul_of_coprime_of_dvd` proves the exact gcd. This argument controls repeated prime factors as well: the original integer is the product of these four distinct primes, and the coprime factors contribute nothing to the gcd.

The exact gcd value is

```text
(P+6)*(P+48) = 649251263089686721963,
```

strictly below

```text
P*(P+6)*(P+18) = 16543187948686502107761484559263.
```

The range theorem supplies an actual member of the set defining `f N`. `Nat.sInf_le` therefore gives `f N <= (P+6)*(P+48)`, and the strict numerical comparison gives `f_strict_upper_bound`. This step needs no enumeration of the full index range and does not claim that the displayed quadratic value is the exact minimum. The explicit witness also rules out relying on the empty-set convention.

## Preserved positive results

All 16 preceding internal library modules are byte-identical to version 5. Their five final declarations remain in `Erdos700.FourPrime`:

- `four_prime_exact_cubic`: `a>=1`, `b>=3a`, `c>=3b-a+1`, `P>=12c^3`, and the four primes imply `f(N)=P(P+a)(P+b)`.
- `four_prime_exact_boundary`: the same offsets with `P>=100c^5`.
- `four_prime_exact_linear`: `c>=3b+1` with the old size bound.
- `four_prime_exact_relaxed`: `c>=b(b-a)+b+1` with the old size bound.
- `four_prime_exact`: `c>=10b^2` with the old size bound.

The common premises in the last three rows are still `a>=1`, `b>=3a`, and primality of all four displayed integers. The old declarations are genuine corollaries, not restated assumptions. The new counterexample import does not enter their proofs.

The positive proof still covers all six missing-prime pairs and every index in the minimum range. Its active cubic estimates are `11c^3<P`, `13c^2<P`, `7c^3<P`, and `10c<=P`, all following from `P>=12c^3` and the derived `c>=9`. The 33 offset certificates remain 32 strict signs and one nonnegative sign `R-1>=0`. Exact row expansions, integer/natural casts, coprimality before source division, and the product bound `N<2P^4` are unchanged. No new counterexample theorem is used to prove a positive case.

## Documentation correspondence

The [formal counterexample note](docs/counterexample-formal.md), [README](README.md), and [submission scope](SUBMISSION.md) distinguish the six new concrete declarations from the five retained positive criteria. They correctly state the old strong threshold in the refuted universal statement and do not assert an exact counterexample minimum. The [version-5 note](docs/cubic-size.md) is explicitly historical: its original counterexample was external computation, while version 6 supplies the separate Lean proof. The updated Python checker describes its output as supplemental and refers to the formal proof without presenting its own execution as Lean verification.

The [main manuscript](docs/proof.md) retains the same positive theorem, the valid `12c^2` carry margin, and the separate human-readable Maynard consequence. Its new counterexample section links the formal treatment. The positive example `P=75011,a=2,b=6,c=18` remains a supporting Python primality check; version 6's new formal primality certificates concern the four much larger counterexample primes. These two roles are not conflated.

The coefficient 12, the positive offset condition, and the negative example are not described as a globally optimal characterization. Neither official verification nor an award is inferred from local Lean checks. No additional historical-priority search was performed for this bounded semantic review.

## Verification status

The complete project compiled successfully with Lean 4.33.1. A separate fresh verification project then rebuilt all 20 local modules, including all three new counterexample modules (1682 jobs, exit 0). Its strict audit `lake env lean -DwarningAsError=true Audit.lean` also returned exit 0. The completed record is dated 2026-09-17 at 12:19:28 UTC.

The evidence is the [fresh build log](verification/canonical-build.log), [strict audit log](verification/canonical-audit.log), [build record](verification/build-record.json), and [source hash list](verification/source-files.json). This review read all 11 printed declaration types and transitive axiom lists. In this snapshot each of the 11 lists contains exactly `propext`, `Classical.choice`, and `Quot.sound`, with no `sorryAx` or extra axiom. The printed definitions of `f`, `P`, `N`, and `k` agree with the expressions reviewed above.

This review independently matched all 24 current source/configuration hashes and byte counts against both recorded lists. The counterexample root has the `b805e372...db10c` digest displayed above; the positive root remains unchanged. The recorded source and configuration bytes are identical before and after the fresh build. All nine dependency revisions match the pinned manifest, their tracked working trees are clean, and their state is unchanged after verification.

The fresh build cleared inherited `LEAN_PATH` and excluded the original project's directory from the library search path. It rebuilt the copied local sources while reusing precompiled dependency caches. These are version-6 records for the full package, not substituted evidence from an earlier version. They provide local Lean verification, not an alternative proof checker or organizer acceptance.

## Scope

The formalized scope now includes both the local four-prime sufficient criterion and this explicit counterexample to deleting the gap condition's final `+1`. The external Python calculations remain optional supporting checks; they are not premises of the Lean declarations. Maynard's theorem, prime-tuple infinitude, and the asymptotic limit remain outside this Lean development. No exact value of `f` at the counterexample, globally optimal offset criterion, or optimal coefficient 12 is asserted. The work remains partial progress on Erdős 700, not a complete solution or an official prize decision.
