# Internal semantic audit of the offset-dependent four-prime criterion

Date: 2026-09-17. Reviewer: the separate internal audit agent.

**Source-review result: no mismatch or retained stronger separation hypothesis was found.** The new root theorem uses `3*B-A+1 <= C`, covers all six pairs and the full minimum range, and retains the three preceding theorem statements as corollaries. This is a sufficient condition; no claim of an optimal threshold is made.

This is internal AI-assisted review, not external peer review or designated prize verification. In this revision, the reviewer implemented the `Bounds` certificates and their generator; another internal agent adapted the parameter wrappers; the root agent assembled the main theorem and documentation. The reviewers therefore participated in the work being assessed. The review covers source meaning, while completed build and axiom evidence are recorded separately below.

## Reviewed snapshot and exact statement

SHA-256 of the source bytes reviewed:

| Source | SHA-256 |
| --- | --- |
| `Erdos700/FourPrime.lean` | `8b0f9a5ebac7ffbeab520bdaa0156f11f6560e5ea3c6ff07e80db4c3ffc27b1d` |
| `Erdos700/Bounds.lean` | `48210f2c367b3b929d94ef75819c4d1d1118f2e129387ae0cabe365d95d04ff2` |
| `Erdos700/ParameterDigits.lean` | `6bc9fd1d9f6ce8aced2300c2cea8592e9256c0a3dc0bd5f52eb70698e9402b01` |
| `Erdos700/ParameterBC.lean` | `7cfd4cbe5cb70136781a53ac15c9a82bb271b91e64498c631f463e1eca9a5280` |
| `Erdos700/PairBC.lean` | `2f24e879bb5462e032f088e8c7dab539a90612d0504db9b89a9ea584c5522be3` |
| `Erdos700/Minimum.lean` | `4b3ebd40441faa26ad3c4cf31727318926cd0abe56d59353e136b2abb7bae481` |

Ten library modules are byte-identical to version 3: `Arithmetic`, `DigitSupport`, `IntDigitSupport`, `Lucas`, `Minimum`, `PairA`, `PairBC`, `PairPDigits`, `PrimeSource`, and `RowExpansions`. The six changed library modules are `Bounds`, `FourPrime`, `ParameterDigits`, `ParameterBC`, `ParameterP`, and `PairADigits`. The root audit file was also reviewed.

`Erdos700.FourPrime.four_prime_exact_boundary` quantifies natural numbers `P,A,B,C`, assumes exactly

```text
1 <= A, 3*A <= B, 3*B-A+1 <= C, 100*C^5 <= P,
Prime P, Prime (P+A), Prime (P+B), Prime (P+C),
```

and concludes

```text
Erdos700.f (P*(P+A)*(P+B)*(P+C)) = P*(P+A)*(P+B).
```

There are no surrounding section variables, assumed pair exclusions, or additional implicit mathematical hypotheses. The definition of the function is unchanged:

```lean
noncomputable def f (n : ℕ) : ℕ :=
  sInf {m | ∃ k, 1 < k ∧ k ≤ n / 2 ∧ m = Nat.gcd n (n.choose k)}
```

Thus the index range is every natural `2 <= k <= floor(n/2)`, not selected prime indices or a restricted divisibility class. The witness `k=P+C` is proved to belong to this range and to attain the product of the three smaller primes. This proves the set nonempty before `Nat.sInf_mem` is used. No empty-set convention supplies the conclusion.

## Natural subtraction and the integer interface

The natural-number expression `3*B-A+1` contains truncated subtraction. The root explicitly proves `hA3B : A <= 3*B`, casts the natural inequality, and uses `Nat.cast_sub hA3B`. Its integer hypothesis is therefore the intended ordinary difference `3*b-a+1 <= c`. No potentially negative integer difference is silently replaced by natural subtraction.

Primes, the binomial row, and the index remain natural numbers. Signed polynomial coefficients and Euclidean divisions are integers. The unchanged `IntDigitSupport` lemmas identify their quotients and remainders with the natural-number operations, and all four bases are positive. Source quotient divisibility by the second prime follows from Lucas, the explicit source representation, and distinctness of the two primes; it is not inferred from `q | k` without dividing out the coprime source factor.

## The zero high-digit boundary

Write `R=a+c-3*b`. The high digit of `N/(P+b)` is `R-1`. The previous proof used a strict inequality for this quantity; the new parameter range gives only

```text
R-1 >= 0.
```

That is exactly what digit legality needs. The parameter substitution is

```text
a=1+x, b=3*a+y, c=3*b-a+1+z, with x,y,z >= 0.
```

Under this substitution `R-1=z`, so strict positivity would be false at `z=0`. The exported lemma has been changed to

```text
Bounds.R_at_least_one : 0 <= a-3*b+c-1.
```

The uniform lower bound is now `c>=9`, supplied by `Bounds.c_at_least_9 : 0<c-8`. The 33 certificates consist of **32 strict inequalities and one nonnegative inequality**. The auxiliary generator checks the conclusion's `<` or `<=` sign against the Lean statement and records the distinction in its JSON. Each polynomial identity is checked by Lean `ring`, and each asserted sign by `positivity`; Python generation is not a trusted proof oracle.

`ParameterDigits.digit_bounds_b` uses the nonnegative result directly. Its declared high-digit requirement is `0 <= R-1 < P+b`; it does not require `R>1`. At `R=1`, a source representation at `P+b` has `0<=u<=R-1`, hence `u=0`. The last-pair proof includes that case rather than requiring a positive high source digit.

The `P` versus `P+b` and `P+a` versus `P+b` arguments also remain valid: after a middle borrow they use `u<=R`, not `R>1`. Their zero-source branches and the subsequent contradictions do not omit the value `R=1`.

## All size conditions and all six pairs

The new range still implies `a<b<c`, `c>2*b`, `c>a+b`, and `c>=9`. All local wrapper hypotheses on `c` were changed to `3*b-a+1<=c`; the older separation conditions appear only in compatibility corollaries.

The four normalized row expansions retain their exact algebraic identities. The other fixed row digits remain positive and smaller than the relevant bases, except that the explicitly permitted high digit `R-1` may be zero. `ParameterDigits` proves `N<2*P^4` and then `k/x<x^3` for each base `x>=P` and every index with `2*k<=N`. Consequently the three source digits exhaust the quotient, including at the endpoint `k=floor(N/2)`. These estimates follow from the current parameters and are not extra root assumptions.

The target low, middle, and high expressions are `(k/q)%q`, `(k/q/q)%q`, and `(k/q/q/q)%q`. These are the three digits of `k/q`. Actual division and remainder are connected to any normalization functions before their bounds are used.

| Missing pair | Source | Target | Exclusion supplied by the root |
| --- | --- | --- | --- |
| `P, P+A` | `P+A` | `P` | `Arithmetic.pairAP_zero_digits` |
| `P, P+B` | `P` | `P+B` | `ParameterP.pairPB_global_digits` |
| `P, P+C` | `P` | `P+C` | `ParameterP.pairPC_global_digits` |
| `P+A, P+B` | `P+A` | `P+B` | `PairADigits.pairAB_global_digits` |
| `P+A, P+C` | `P+A` | `P+C` | `PairADigits.pairAC_global_digits` |
| `P+B, P+C` | `P+B` | `P+C` | `ParameterBC.pairBC_actual_digits` |

The first orientation is intentional: its residue argument forces all source digits to vanish, contradicting the positive original index. No target digit hypothesis is needed there. After all six exclusions, `NoTwoMissing` implies `ThreeOfFour`; distinct-prime divisibility gives the gcd lower bound, while the independent largest-prime witness gives equality.

For the last pair, put `q=P+c`, `d=c-b`, `L=b*(b-a)`, `U=3*c^2-2*c*(a+b)+a*b`, and `F=c*(c-a)*(c-b)`. The unchanged `PairBC` core requires `L<=c^2`, not the obsolete quadratic-gap condition `L<d`. `ParameterBC` derives `0<d<c`, `u<c`, `v<q`, `w<=d*L`, `1<=U<=3*c^2`, `10*c^3<q`, and `d*L<F` from the new parameters. `L<c^2` is supplied by the regenerated `L_less_c_squared` certificate. The internal coarse-size lemma then proves every carry and normalization bound.

That core constructs `0<=H<d`, `d*J=H*q+w`, and `K=u*d^2-w+d*H`, with the exact quotient identity

```text
k/q = u*q^2 + (J-2*u*d-2*H)*q + K.
```

For `H>0`, the actual middle digit lies strictly between `U-1` and `q`, contradicting its bound. For `H=0,K<0`, the inequality `-K<=w<=d*L<F` makes the low digit too large. For `H=0,K>=0`, one has `J<=u*d`: when `u>0` the middle digit is too large, and when `u=0` the remaining digits force `k=0`. Thus the newly allowed zero high source digit is fully covered. No positive-carry or sign branch is excluded by assumption.

## Human-readable proof and supporting example

The [main manuscript](docs/proof.md) and [extension note](docs/boundary-extension.md) state the new parameter range and correctly allow `R=1`. The revised proof of positivity for the row quantity `B=(2*b-a)*c+2*a*b-3*b^2` uses the valid identity

```text
B = 3*b*(b-a) + a^2 + (2*b-a)*(c-3*b+a).
```

Each displayed factor has the required sign since `b>=3*a`, `a>=1`, and `c-3*b+a>=1`. The old argument through `c-3*b>0` is not used. The upper bound follows from `2*b*c-B=a*(c-2*b)+3*b^2>0`. The remaining manuscript row estimates and pair arguments agree with the formal interfaces.

The extension note distinguishes an integer boundary from a prime example. Under the root's large-`P` condition, all four primes are odd, hence `a,b,c` are even; the exact equality `c=3*b-a+1` would make `c` odd. The integer lemmas nevertheless cover `R=1`, without asserting a prime tuple on that exact boundary.

The supporting example uses `a=2,b=6,c=18,P=189078581`, above `100*18^5=188956800`, and the four displayed integers `189078581,189078583,189078587,189078599`. The claimed thresholds `360,31,19,17` and the separation comparisons are correct. The included trial-division implementation checks every odd divisor through the integer square root after treating 2. Its [record](verification/witness.json) is supporting computation, separate from the universal Lean theorem. It neither enumerates the binomial-gcd minimum nor formally certifies primality in Lean.

## The three retained statements

All previous declaration names and types remain:

- `four_prime_exact_linear` keeps `3*B+1<=C` and derives `3*B-A+1<=C` before invoking the new theorem.
- `four_prime_exact_relaxed` keeps `B*(B-A)+B+1<=C`. It proves `B-A>=2`, derives the version-3 condition, and invokes the preceding corollary. The ordering premises justify the natural-number subtraction.
- `four_prime_exact` keeps `10*B^2<=C`. Using `B*(B-A)<=B^2` and `B>=3`, it derives the version-2 condition and invokes that corollary.

The root boundary theorem does not call these corollaries, so no stronger old condition is used circularly to establish the new result.

## Verification status and limits

The regenerated `Bounds` module and the complete project compiled successfully with Lean 4.33.1. A separate fresh-project build then rebuilt all 17 local modules (1609 jobs, exit 0). The strict final audit also returned exit 0. The recorded types match the new boundary theorem and all three retained statements; each transitive axiom list contains only `propext`, `Classical.choice`, and `Quot.sound`.

The completed evidence is the [build log](verification/canonical-build.log), [strict audit log](verification/canonical-audit.log), [build record](verification/build-record.json), and [source hash list](verification/source-files.json). This review checked the four printed axiom lists and matched all 21 recorded source/configuration hashes against the current bytes. All nine dependency revisions match the manifest and their tracked working trees are clean. The verification used a fresh local build directory and removed the inherited `LEAN_PATH`; precompiled dependency caches were reused. These checks are local verification, not an independent alternative proof checker or organizer acceptance.

The local source scan found no `sorry`, `admit`, custom `axiom`, `native_decide`, `unsafe`, `extern`, or `implemented_by` declaration. The unchanged Lucas bridge imports Mathlib's proved Lucas theorem, not the upstream open-conjecture file or unfinished declarations. `Audit.lean` queries the exact function and all four root theorem types and transitive axiom lists.

This audit does not assert external peer review, organizer verification, historical priority, recipient identity, or award eligibility. The theorem is conditional on the four displayed integers being prime; it does not formalize their existence or infinitude. Maynard's theorem, the infinite-family consequence, and the asymptotic limit remain outside this Lean development. The parameter extension leaves the 3/4 exponent unchanged and is partial progress, not a complete solution of Erdős 700 or a proof that this sufficient threshold is optimal.
