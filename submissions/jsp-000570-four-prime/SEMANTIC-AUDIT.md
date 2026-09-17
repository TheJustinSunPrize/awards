# Internal semantic audit of the linear four-prime criterion

Date: 2026-09-17. Reviewer: the separate internal audit agent.

**Result: no semantic mismatch or retained quadratic-gap hypothesis was found.**
The reviewed root theorem proves the stated local four-prime equality with
`3*B+1 <= C`. Its proof supplies all six pair exclusions over the full required
minimum range. The previous two sufficient conditions remain corollaries with
their existing declaration names and statements.

This is an internal AI-assisted source review, not external peer review or
designated prize verification. The reviewer also contributed the parameter
wrappers and positive-polynomial certificates. The last-pair implementation
and the root assembly were written by other internal agents. This audit does
not claim that the reviewers are independent of the work's acceptance.

## Reviewed snapshot

SHA-256 of the exact source bytes reviewed:

| Source | SHA-256 |
| --- | --- |
| `Erdos700/FourPrime.lean` | `2b4e70cb0920261376488d68fa7885f830ee2be382cc9062c7a2e816a2dc3505` |
| `Erdos700/PairBC.lean` | `2f24e879bb5462e032f088e8c7dab539a90612d0504db9b89a9ea584c5522be3` |
| `Erdos700/Minimum.lean` | `4b3ebd40441faa26ad3c4cf31727318926cd0abe56d59353e136b2abb7bae481` |
| `Erdos700/ParameterBC.lean` | `759a40914d9adb714b03f2df22d63b8a9a979ce2b009b4a1a0b7e09f04a162e8` |
| `Erdos700/Bounds.lean` | `d8b9d77e16591bd8b882e4021f50f839a4f0e11ac963666058ace2d28092d969` |

The source review covers the 17 local library modules and the root audit file.
Nine library files are byte-identical to the preceding quadratic-separation
development: `Arithmetic`, `DigitSupport`, `IntDigitSupport`, `Lucas`,
`Minimum`, `PairA`, `PairPDigits`, `PrimeSource`, and `RowExpansions`.
The seven changed library files were reviewed for the new parameter condition,
with particular attention to `PairBC`, `ParameterBC`, and `FourPrime`.

## Root statement and the function being minimized

`Erdos700.FourPrime.four_prime_exact_linear` quantifies natural numbers
`P,A,B,C`, assumes exactly

```text
1 <= A, 3*A <= B, 3*B+1 <= C, 100*C^5 <= P,
Prime P, Prime (P+A), Prime (P+B), Prime (P+C),
```

and concludes

```text
Erdos700.f (P*(P+A)*(P+B)*(P+C)) = P*(P+A)*(P+B).
```

There are no section variables or additional implicit mathematical hypotheses.
The definition in `Minimum.lean` is

```lean
noncomputable def f (n : ℕ) : ℕ :=
  sInf {m | ∃ k, 1 < k ∧ k ≤ n / 2 ∧ m = Nat.gcd n (n.choose k)}
```

This is the minimum over every natural index `2 <= k <= floor(n/2)`, using the
ordinary natural-number binomial coefficient and gcd. It is not a minimum
over selected prime indices or over a restricted divisibility class.

The use of `sInf` does not supply the result through an empty-set convention.
`largest_prime_in_range` proves that `k=P+C` belongs to the range, and
`gcd_four_primes_at_largest` proves the claimed value there. This establishes
nonemptiness before `Nat.sInf_mem` is used for the lower bound. The upper-bound
witness needs ordered distinct primes, not the six pair exclusions.

## Lucas, source quotients, and the six pairs

The natural-number prime, row, and index remain unchanged. Integer variables
are introduced only for signed polynomial coefficients and Euclidean division.
`IntDigitSupport` connects integer division and remainder to their
natural-number counterparts. All four bases are positive.

The three quotient digits exhaust the source representation because
`ParameterDigits` proves `N < 2*P^4` and then `k/x < x^3` for every required
base `x >= P` and every index satisfying `2*k <= N`. These facts follow from
the linear parameter assumptions and `100*C^5 <= P`; they are not root
hypotheses. The argument includes the endpoint `k=floor(N/2)`.

The four normalized row expansions have their first three digit bounds proved
by `ParameterDigits`. Lucas then yields the source digits and the actual target
remainders. The low, middle, and high target expressions are respectively
`(k/q)%q`, `(k/q/q)%q`, and `(k/q/q/q)%q`: they are the three digits of `k/q`.
Discarding an unused high target bound in some pair arguments does not restrict
the indices covered.

Every quotient-divisibility input is proved from the other missing prime and
the source representation by `missing_prime_dvd_int_source`. Distinctness of
the two primes rules out divisibility of the source base by the other prime.
The proof does not confuse `q | k` with `q | k/x`.

`NoTwoMissing` contains all six unordered pairs, and the root supplies each:

| Missing pair | Source | Target | Exclusion |
| --- | --- | --- | --- |
| `P, P+A` | `P+A` | `P` | `Arithmetic.pairAP_zero_digits` |
| `P, P+B` | `P` | `P+B` | `ParameterP.pairPB_global_digits` |
| `P, P+C` | `P` | `P+C` | `ParameterP.pairPC_global_digits` |
| `P+A, P+B` | `P+A` | `P+B` | `PairADigits.pairAB_global_digits` |
| `P+A, P+C` | `P+A` | `P+C` | `PairADigits.pairAC_global_digits` |
| `P+B, P+C` | `P+B` | `P+C` | `ParameterBC.pairBC_actual_digits` |

The first orientation is intentional. Divisibility by `P` alone forces all
three source digits to vanish, contradicting the positive original index.
The other five arguments use actual quotient digit bounds. After these six
exclusions, the elementary `ThreeOfFour` step and distinct-prime divisibility
give the gcd lower bound by the product of the three smallest primes.

## Why the last pair no longer requires a quadratic gap

Write `q=P+c`, `d=c-b`, `L=b*(b-a)`,
`U=3*c^2-2*c*(a+b)+a*b`, and `F=c*(c-a)*(c-b)`.
The new caller-facing `PairBC.source_pair_exclusion_of_large_base` assumes
`L <= c^2`. It does not assume `L < d`.

From source divisibility the proof constructs, rather than assumes,
integers `H,J,K` satisfying

```text
0 <= H < d,
d*J = H*q+w,
K = u*d^2-w+d*H,
k/q = u*q^2 + (J-2*u*d-2*H)*q + K.
```

The coefficient `-2*H` is retained. The congruence range proves the complete
interval `0 <= H < d`; no carry value is omitted. Bounds on `K` and the
corrected middle coefficient justify one-borrow normalization. The lemmas
`polynomial_low_digit`, `polynomial_middle_digit`, and
`two_digits_normalize` identify the normalization functions with genuine
integer quotient/remainder digits before they are used in the source theorem.

For `H>0`, the correction is bounded by `4*c^2` and `L<=c^2` gives

```text
q - 4*c^2*d <= d*E <= d*q - q + c^2*d,
E = J-2*u*d-2*H+lowCarry(K).
```

Since `q>7*c^2*d` and `U<=3*c^2`, this forces `U-1<E<q`. Thus `E` is already
the actual nonnegative middle digit and violates its target bound.

For `H=0`, the new argument splits on the sign of `K` before using `u`:

1. If `K<0`, then `-K=w-u*d^2 <= w <= d*L < F`. Consequently the normalized
   low digit `q+K` exceeds `q-F`, a contradiction. This works for every
   nonnegative `u` and does not compare `L` with `d`.
2. If `K>=0`, the identity `K=d*(u*d-J)` implies `J<=u*d`. If `u>0`, then
   `J-2*u*d<0`; the margin `U-1<q-2*u*d` makes its normalized middle digit too
   large. If `u=0`, then `J=0`, hence `w=0`; together with `H=0` this forces
   the original index to vanish, contradicting `k>0`.

This change removes the previous use of `d>L` to force a positive low
coefficient. The unused special-case helper for `u=0,t>0` is harmless; the
actual exclusion handles that case through the first sign branch above.

## Discharge of every size hypothesis

`ParameterBC.pairBC_actual_digits` substitutes the displayed `q,d,L,U,F`
and derives all its coarse inputs from `a>=1`, `b>=3a`, `c>=3b+1`, and
`p>=100*c^5`:

- `0<d<c`, and the source high bound implies `u<c`.
- `L<c^2` follows from `Bounds.L_less_c_squared`, so `L<=c^2` is available.
- Positivity of the row's middle subtraction proves `v<q`.
- The low source bound is exactly `w<=d*L`.
- The positive integer `U` satisfies `1<=U<=3*c^2`.
- `10*c^3<q` follows from `large_base_thresholds` and `c>=10`.
- `d*L<F` follows from `Bounds.p2_to_p3_low_gap` and `d>0`.

`PairBC.large_base_estimates` then supplies all finer carry, normalization,
and middle-margin bounds. Its proof uses `L<=c^2`, `u<c`, and `d<c`, not the
removed `L<d` assumption.

The 33 parameter certificates in `Bounds` use the nonnegative substitution
`a=1+x`, `b=3*a+y`, `c=3*b+1+z`. Their identities are checked by Lean `ring`
and their strict signs by `positivity`. The auxiliary Python generator is not
a proof oracle. `largest_gap_exceeds_L` is absent; it has been replaced by
`L_less_c_squared`. Every global wrapper uses the linear condition. A source
search found the older quadratic conditions only in the compatibility
corollaries described next.

## Compatibility corollaries

`four_prime_exact_relaxed` retains the version-2 natural-number hypothesis
`B*(B-A)+B+1<=C`. From `A>=1` and `B>=3*A` it proves `2<=B-A`, hence
`3*B+1<=C`, and invokes the linear theorem. The natural subtraction is safe:
the ordering assumptions imply `A<=B`, and the proof works directly with
the natural-number difference.

`four_prime_exact` retains the version-1 hypothesis `10*B^2<=C`. It derives
the version-2 bound using `B*(B-A)<=B^2` and `B>=3`, then applies the preceding
corollary. Neither older condition is used to prove the linear theorem.

## Verification evidence and limits

The new bounds and three associated wrapper modules compiled successfully in
the configured Lean 4.33.1 environment. The last-pair file was separately
compiled by its implementing agent. The root assembly then completed a
whole-project build, followed by a separate fresh-project rebuild of all
17 local modules (1609 jobs, exit 0). The strict root audit also returned
exit 0. The final types and transitive axiom lists of all three declarations
were inspected: each uses only `propext`, `Classical.choice`, and `Quot.sound`.

The [build log](verification/canonical-build.log),
[strict audit log](verification/canonical-audit.log),
[build record](verification/build-record.json), and
[source hash list](verification/source-files.json) record that verification.
The record binds 21 source/configuration files to unchanged bytes before and
after the build, with all nine dependency revisions matching the manifest and
their tracked working trees clean. The inherited `LEAN_PATH` was removed;
local sources were rebuilt and precompiled dependency caches were reused.
This source review alone is not a claim that an independent alternative proof
checker, external reviewer, or prize organizer has verified the result.

The local source scan found no `sorry`, `admit`, custom `axiom`,
`native_decide`, `unsafe`, `extern`, or `implemented_by` declaration. The
project imports Mathlib's Lucas theorem, not the upstream open-conjecture file
or any unfinished problem statement. `Audit.lean` queries the exact function
and all three root declarations and their transitive axiom lists.

The audited theorem is conditional on its four displayed integers being prime.
It does not itself prove prime existence, infinitely many prime quadruples,
Maynard's theorem, or an asymptotic limit. Any Maynard-based infinite-family
argument remains outside this Lean formalization. This development is partial
progress on Erdős 700, not a full characterization or a proof of all its open
upper-bound questions. This audit establishes neither historical priority nor
prize eligibility, recipient identity, or an award decision.
