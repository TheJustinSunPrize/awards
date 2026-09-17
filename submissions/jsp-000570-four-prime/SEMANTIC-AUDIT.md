# Current v2 semantic audit

Date: 2026-09-17. Internal AI-assisted source review by a separate agent.
This is not external human peer review or designated organizer verification.

**Finding:** no semantic mismatch or additional mathematical assumption was
identified in the current relaxed theorem. This report is a source-level
review. The root agent has reported a successful assembled `lake build`
(exit code 0), including both the relaxed theorem and the original corollary.
The subsequent [fresh build record](verification/build-record.json) and
[final axiom audit](verification/canonical-audit.log) also pass: all 17 local
modules were rebuilt, and both root theorems use only `propext`,
`Classical.choice`, and `Quot.sound`. These checks remain internal verification.

Reviewed `Erdos700/FourPrime.lean` SHA-256:
`1C9E6D14F7900D68A26D8351A038F20ABF58D3D0967463DEDFA3A9707F97C267`.

## Statement and natural subtraction

`four_prime_exact_relaxed` retains the original conclusion

```text
f(P(P+A)(P+B)(P+C)) = P(P+A)(P+B)
```

and assumes exactly `A>=1`, `B>=3A`, `C>=B(B-A)+B+1`, `P>=100C^5`, and
primality of the four displayed factors. No source digits, carry inequalities,
pair exclusions, or minimum equality are hypotheses of the final theorem.

The new natural-number subtraction is handled correctly. The proof first
establishes `A<=B`, casts the complete natural inequality to integers, then
uses `Nat.cast_sub hABnat`. Therefore integer `b-a` is exactly the cast of
natural `B-A`; there is no silent replacement of truncated subtraction.
The parameter assumptions still imply `0<A<B<C` and hence four distinct,
strictly ordered primes.

## Preservation of the original theorem

The name `four_prime_exact` remains available with its original statement,
including `C>=10B^2`. It is now proved as a corollary of the relaxed theorem.
The implication is valid: `B(B-A)<=B^2`, while `B>=3` implies
`B^2+B+1<=10B^2`. No old assumption has been silently replaced in the
backward-compatible declaration.

The parameter region is enlarged; the conclusion and exponent are unchanged.
For example, the gap tuple `(A,B,C)=(2,6,32)` satisfies the new gap inequality
and fails the old one. This observation concerns the gap region, not a claim
that a particular translate has all four factors prime.

## Definition, range, and all six pairs

`Minimum.lean` is byte-for-byte unchanged from v1 (SHA-256
`4B3EBD40441FAA26AD3C4CF31727318926CD0ABE56D59353E136B2ABB7BAE481`).
In particular, `f` still takes the infimum of all gcd values with
`1<k<=floor(N/2)`. The proof supplies the witness `k=P+C` before using
`Nat.sInf_mem`, so it does not exploit the empty-set convention.

The six pair directions are unchanged and exhaustive:

| Missing pair | Source -> target |
| --- | --- |
| `P, P+A` | `P+A -> P` |
| `P, P+B` | `P -> P+B` |
| `P, P+C` | `P -> P+C` |
| `P+A, P+B` | `P+A -> P+B` |
| `P+A, P+C` | `P+A -> P+C` |
| `P+B, P+C` | `P+B -> P+C` |

Source digits are derived from Lucas and the proved `k/x<x^3` range.
Target bounds remain actual integer Euclidean remainders at the correct
positions. Divisibility of each source quotient by the second prime is
proved from the two missing primes and their distinctness. Auxiliary size
conditions are discharged by wrappers using the new parameter inequality;
none is retained as an extra hypothesis of the final theorem.

The first pair intentionally uses the reversed source direction and forces
all source digits to be zero, contradicting the positive original index.
All other directions still match their respective row expansions.

## Bounds and auxiliary generator

The auditor directly observed a successful `lake build Erdos700.Bounds`
under Lean 4.33.1: exit code 0, no warnings. All 33 strict inequalities have
new certificates after substituting

```text
a=1+x, b=3a+y, c=b(b-a)+b+1+z, with x,y,z>=0.
```

Each expanded polynomial has nonnegative integer coefficients and a positive
constant coefficient. Lean checks the identities with `ring` and their signs
with `positivity`. The renamed lower-bound lemma is `c_at_least_10`, proving
`0<c-9`; no old `c>=90` assumption remains in the reviewed relaxed modules.
The four downstream wrapper modules have also been reported as successfully
built by their responsible agent. The root agent's assembled project build
has subsequently passed, including `four_prime_exact_relaxed` and
`four_prime_exact`. The separate final fresh-build and axiom-list checks have
also passed, as recorded in the verification links above.

`tools/generate_bounds.py` is portable and reads only this project's
`Erdos700/Bounds.lean`. With Python 3 and SymPy installed, run:

```text
python tools/generate_bounds.py
```

It regenerates the 33 right-hand-side polynomials, compares them with the
current Lean identities, checks coefficient signs, and writes
`tools/bounds-certificates.json`. It does not modify Lean source or depend on
the old v1 source path. This tool is an auxiliary generator, not part of the
trusted proof; acceptance rests on Lean's checks.

No `sorry`, custom `axiom`, `admit`, `native_decide`, `unsafe`, `extern`, or
`implemented_by` declaration was found by a source scan of the Lean modules.
This source scan does not replace the final imported-axiom audit.

## Scope

This audit does not establish novelty, priority, prize eligibility, or a
formalized Maynard theorem. The conditional local equality criterion is the
statement reviewed. Neither the existence of infinitely many prime
quadruples nor the infinite-family asymptotic consequence is claimed to be
formalized by this development.
