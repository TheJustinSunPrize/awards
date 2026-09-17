# Internal semantic audit of the cubic-size four-prime criterion

Date: 2026-09-17. Reviewer: the separate internal audit agent.

**Source-review result: the cubic threshold supplies every size estimate used by the local proof.** The new theorem keeps `c>=3b-a+1` and replaces `P>=100c^5` by `P>=12c^3`. The older four declaration names and mathematical statements are retained as corollaries. The constant 12 and the offset conditions are sufficient conditions; this review makes no optimality claim.

This is internal AI-assisted review, not external peer review or designated prize verification. For this revision, another internal agent changed the base-size helper and parameter wrappers; the root agent assembled the main theorem and documentation; this reviewer read the resulting sources without editing Lean. The reviewer participated in earlier versions of the project. Source meaning and final reproducible build evidence are separate parts of the review.

## Exact statement and minimum range

`Erdos700.FourPrime.four_prime_exact_cubic` quantifies natural numbers `P,A,B,C`, assumes exactly

```text
1 <= A, 3*A <= B, 3*B-A+1 <= C, 12*C^3 <= P,
Prime P, Prime (P+A), Prime (P+B), Prime (P+C),
```

and concludes

```text
Erdos700.f (P*(P+A)*(P+B)*(P+C)) = P*(P+A)*(P+B).
```

There are no surrounding variables, assumed pair exclusions, prime-existence assertions, or extra size premises. The unchanged function is

```lean
noncomputable def f (n : ℕ) : ℕ :=
  sInf {m | ∃ k, 1 < k ∧ k ≤ n / 2 ∧ m = Nat.gcd n (n.choose k)}
```

The theorem therefore covers every integer index `2<=k<=floor(N/2)`. It is not a conclusion about selected indices. The largest-prime index `k=P+C` is proved to lie in that range and attain the displayed value. This establishes nonemptiness before `Nat.sInf_mem` is used, so the empty-set convention is irrelevant.

The root proves `A<=3*B` before using `Nat.cast_sub` to translate the natural expression `3*B-A+1` into the intended integer expression. Its cast of `12*C^3<=P` is exact. The ordering `0<A<B<C` follows from the offset hypotheses, yielding four distinct primes.

## Reviewed source snapshot

The frozen source bytes reviewed have these SHA-256 digests:

| Source | SHA-256 |
| --- | --- |
| `Erdos700/FourPrime.lean` | `aff6314ea5fe169b19bbbdbe8dc8970c4260c6b836c939125967fb084546e033` |
| `Erdos700/Bounds.lean` | `7c9b19858bee231bc14f3b1d0a1d5e9a867093d0311a978ea7c658ba19970faa` |
| `Erdos700/ParameterDigits.lean` | `cf9a7e9acd301b7b91b78d5de41b0182eeffcc707e11544f1e4ddcc587351031` |
| `Erdos700/ParameterP.lean` | `536f5c7ad7cea4961beaf6a5e762355782fe7fbb3ee633be2ce93aacadc96dbd` |
| `Erdos700/ParameterBC.lean` | `d29e179384212f22275b75bfc431814e663708a6c51027ba09fddf685e183d5d` |
| `Erdos700/PairADigits.lean` | `d61feb35a406f278c8c422c6dffcd6c43e2dc5f07397ffb4a983b188a68521b7` |
| `Erdos700/PairBC.lean` | `2f24e879bb5462e032f088e8c7dab539a90612d0504db9b89a9ea584c5522be3` |
| `Erdos700/Minimum.lean` | `4b3ebd40441faa26ad3c4cf31727318926cd0abe56d59353e136b2abb7bae481` |

Ten library modules are byte-identical to version 4: `Arithmetic`, `DigitSupport`, `IntDigitSupport`, `Lucas`, `Minimum`, `PairA`, `PairBC`, `PairPDigits`, `PrimeSource`, and `RowExpansions`. The six changed library modules are the other six listed above. The aggregate library and five-root audit file were also reviewed. One comment in unchanged `PairA.lean` mentions the historical `100c^5` threshold; its abstract lemma has no such premise, and the current root and wrappers all use the stated cubic bound.

## Why the smaller base is sufficient

The unchanged offset certificates give `c>=9`. Every caller of the revised helper explicitly derives its new hypothesis `2<=c`; no call relies on the old generic assumption `1<=c`.

The revised `Bounds.large_base_thresholds` proves, from `c>=2` and `P>=12c^3`,

```text
11c^3 < P, 13c^2 < P, 7c^3 < P.
```

The first and third inequalities follow from `c^3>0`. For the second, the proof uses `2c^2<=c^3` and `c^2>0`, so `13c^2<24c^2<=12c^3<=P`. This is why strengthening the helper's lower bound on `c` is necessary; the middle estimate would be false for `c=1,P=12`. The actual parameter range is safely above that exceptional value.

All 33 offset-only polynomial certificates are unchanged: 32 are strict inequalities and one is the nonnegative inequality `R-1>=0`, where `R=a+c-3b`. Their substitution remains `a=1+x`, `b=3a+y`, `c=3b-a+1+z` for nonnegative `x,y,z`. The special certificate `R-1=z` allows equality. Generated identities are proved by Lean tactics and are not accepted on the authority of the generation script.

The active size dependencies were checked as follows:

| Consumer | Required estimates supplied by the cubic bound |
| --- | --- |
| `ParameterDigits` | Fixed low digits below `c^3<P`, fixed middle digits below `3c^2<P`, fixed high digits below `3c<P`; residual digits legal by positivity of the quantities subtracted. |
| `ParameterP` | With `0<=d<=c`, `S<=3c`, `T<=3c^2`, and `Z,C<c^3`, its cubic sums are below `4c^3`; its middle-coefficient sums are below `9c^2`. The existing stronger helper margins discharge all six explicit size premises. |
| `PairADigits` wrappers | With `S1<=2c`, `T1<=c^2`, and `0<=d<=c`, `2d^2*S1<=4c^3`, `C+d*T1<2c^3`, and `3d*S1+U-1<9c^2`. The same helper margins discharge every local size premise. |
| `ParameterBC` | The base is `q=P+c`; the wrapper derives `q>10c^3` from `P>11c^3`. All remaining premises depend only on the unchanged offset certificates and actual source digit bounds. |
| Uniform source length | Since `c<=c^3`, the new bound gives `10c<=P`. The existing fourth-power lemma gives `N<=(P+c)^4<2P^4`, and every relevant `k` then satisfies `k/x<x^3` for each base `x>=P`. |

The last estimate ensures that the three source digits exhaust the quotient; it continues to cover the endpoint `k=floor(N/2)`. No quintic bound is retained in an active hypothesis of the new proof. The four old corollaries intentionally retain their original quintic assumptions.

## Digit interpretation and all six exclusions

The normalized rows are the exact quotient expansions of `N` at each prime base. In particular, at `P+b` the high digit is `R-1`, which may be zero. The unchanged integer interfaces connect actual division and remainder to digit bounds. The expressions `(k/q)%q`, `(k/q/q)%q`, and `(k/q/q/q)%q` are the low, middle, and high digits of `k/q`.

Lucas supplies source divisibility and digitwise domination when a prime is absent from a binomial coefficient. The second prime divides the source quotient because it is coprime to the first source factor; that coprimality step is explicit in `PrimeSource`, not assumed from divisibility of the original index alone.

The root supplies every pair:

| Missing pair | Source to target | Exclusion |
| --- | --- | --- |
| `P,P+A` | `P+A` to `P` | `Arithmetic.pairAP_zero_digits` |
| `P,P+B` | `P` to `P+B` | `ParameterP.pairPB_global_digits` |
| `P,P+C` | `P` to `P+C` | `ParameterP.pairPC_global_digits` |
| `P+A,P+B` | `P+A` to `P+B` | `PairADigits.pairAB_global_digits` |
| `P+A,P+C` | `P+A` to `P+C` | `PairADigits.pairAC_global_digits` |
| `P+B,P+C` | `P+B` to `P+C` | `ParameterBC.pairBC_actual_digits` |

The `PairBC` core is unchanged. It uses `L=b(b-a)<=c^2`, not an obsolete quadratic-gap assumption. For `d=c-b`, all carry branches are covered: positive `H` violates the middle digit; zero `H` with negative constant violates the low digit; zero `H` with nonnegative constant either violates the middle digit or forces `k=0`. The high source digit `u=0`, including the possible integer boundary `R=1`, is covered.

The remaining pair cores and the row identities are unchanged. Once the six pairs are excluded, `NoTwoMissing` implies `ThreeOfFour`. Distinct-prime divisibility gives the gcd lower bound, and the independent largest-prime witness gives equality over the full minimum range.

## Compatibility with the four previous statements

`four_prime_exact_boundary` retains `100*C^5<=P` and exactly its previous offset condition. It proves `C>=1`, then

```text
12*C^3 <= 100*C^3 <= 100*C^5 <= P,
```

using monotonicity of natural powers for the middle inequality. It invokes the cubic theorem only after deriving the new bound.

`four_prime_exact_linear`, `four_prime_exact_relaxed`, and `four_prime_exact` retain respectively `3*B+1<=C`, `B*(B-A)+B+1<=C`, and `10*B^2<=C`, each with its old `100*C^5<=P` assumption. They use the same valid offset implications as before. Their declaration names and types are preserved. The new theorem does not call the old corollaries, so their stronger premises are not used circularly.

## Zero-boundary counterexample and limits

An exact, separate computation disproves the proposed further replacement `c>=3b-a`. Take `a=6,b=18,c=48,P=25480409371` and the four primes `P,P+6,P+18,P+48`. This `P` exceeds even `100*48^5`. For `k=19P^2(P+18)`, exact Lucas digits give

```text
gcd(N, choose(N,k)) = (P+6)(P+48) < P(P+6)(P+18),
2 <= k < N/2.
```

At base `P`, the quotient digit lists are `[5184,1260,72,1]` and `[0,342,19,0]`. At `q=P+18` they are `[6480,q-684,q-1,0]` and `[6156,q-684,18,0]`. Thus those two primes are absent. The units residues at the other bases are nonzero, so the other two primes are present. Exhaustive trial division certifies the four particular primes; the full binomial coefficient and the full minimum are not computed.

This is supporting computation and a hand-checked counterexample argument, not part of the Lean formalization. It neither refutes the maintained `c>=3b-a+1` hypothesis nor proves that the present sufficient conditions or the coefficient 12 are optimal. It does not require or claim infinitely many primes in that fixed offset pattern.

The packaged [counterexample verifier](tools/check_counterexample.py) checks this fixed instance without a search, and records [the exact certificate](verification/counterexample.json). This review independently reran exhaustive trial division for all four numbers, reconstructed `N` and `k` from every stored digit array, checked digit legality and all violating positions, and matched the recorded checker hash. The exact gcd is obtained from Lucas' theorem and squarefreeness, not direct evaluation of `choose(N,k)`.

## Manuscript and the positive new-range example

The [proof manuscript](docs/proof.md) and [cubic-size note](docs/cubic-size.md) state the same local theorem and retain the correct distinction between the local Lean proof and the human-readable Maynard consequence. In the positive-carry branch of the last pair, the manuscript now uses the appropriate estimate `q/d>=P/c>=12c^2>7c^2`. This leaves the normalized middle digit strictly between `U-1` and `q`, exactly as required. The inherited offset identities and the allowance of the zero digit `R-1` remain valid.

The new positive example `P=75011,a=2,b=6,c=18` has four primes `75011,75013,75017,75029`. It obeys `12*18^3=69984<=P<188956800=100*18^5`, so it lies outside the old size range. The two size thresholds have ratio 2700. This review independently confirmed primality by exhaustive trial division through the integer square root 273 for each number and checked the inequalities. The [portable checker](tools/check_witness.py) and [record](verification/witness.json) are supporting computation, not a Lean proof of those particular prime values or a direct enumeration of the minimum.

The earlier extension notes are labelled historical and retain the correct old theorem statements and examples. The source hash in [the auxiliary bounds certificate](tools/bounds-certificates.json) matches the revised `Bounds.lean`; its 33 polynomial identities remain unchanged, while the separate base-threshold lemma is checked by Lean. No new historical-priority search was performed for this bounded source audit.

## Verification status

The complete project compiled successfully with Lean 4.33.1. A separate fresh verification project then rebuilt all 17 local modules (1609 jobs, exit 0), and its strict audit `lake env lean -DwarningAsError=true Audit.lean` also returned exit 0. The verification record is dated 2026-09-17 at 12:00:46 UTC. The printed types match the cubic theorem and all four retained corollaries; each transitive axiom list contains only `propext`, `Classical.choice`, and `Quot.sound`.

The completed evidence is the [fresh build log](verification/canonical-build.log), [strict audit log](verification/canonical-audit.log), [build record](verification/build-record.json), and [source hash list](verification/source-files.json). This review read all five printed types and axiom lists and independently matched all 21 recorded source/configuration hashes and byte counts against the current files. The reviewed root hash is the `aff6314e...46e033` digest displayed above. Every recorded dependency revision matches the manifest, all nine tracked dependency working trees are recorded clean, and their state is unchanged after the build.

The fresh build cleared inherited `LEAN_PATH` and excluded the original project directory from the library search path; the local modules were rebuilt from the copied source bytes. Precompiled dependency caches were reused. This is a fresh local Lean verification, not an alternative proof checker or organizer acceptance. The evidence belongs to the cubic theorem and is not substituted from an earlier project.

A scan of local Lean sources found no `sorry`, `admit`, custom `axiom`, `native_decide`, `unsafe`, `extern`, or `implemented_by` declaration. The unchanged Lucas bridge uses Mathlib's proved theorem and does not import the upstream open-conjecture statement file. `Audit.lean` queries the exact definition of `f` and all five root declaration types and transitive axiom lists.

## Scope

Only the local conditional four-prime theorem and its four compatibility corollaries are formalized here. Maynard's theorem, the existence of infinitely many admissible prime tuples, and the asymptotic consequence remain human-readable mathematics outside the Lean development. The cubic size refinement does not change the exponent 3/4. This is partial progress on Erdős 700, not a complete solution or an official prize decision. External peer review, historical priority, recipient identity, and award eligibility are not established by these local checks.
