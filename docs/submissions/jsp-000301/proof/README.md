# Locally checked Lean proof

[Counterexample.lean](Counterexample.lean) compiles with Lean 4.34.0, commit
`293d5d0c0c3f3dded4688b3ccd6a33939ac5102b`. It imports Lean's bundled
libraries only; no mathlib package, network service, or additional axiom is
needed by the proof. The toolchain selector is pinned in
[lean-toolchain](lean-toolchain).

## Statement and proof route

`Prime p` is defined by p ≥ 2 and the absence of proper divisors other than
1. `prime_iff` proves that this is equivalent to the unbounded conventional
condition that every natural divisor d is 1 or p. There is no weakened,
unverified prime predicate hidden in the finite definition.

`Powerful n` is `0 < n ∧ ∀ p : Nat, Prime p → p ∣ n → p*p ∣ n`.
`Square n` is `∃ a : Nat, a*a = n`. No bounds occur in those quantified
definitions. The redundant positivity matches the original domain of
positive integers exactly.

`prime_dvd_mul` proves Euclid's prime-divisor property using the bundled
gcd and coprimality lemmas. `prime_divisor_eq` identifies a prime divisor
of a prime. The two factorizations then reduce the unbounded powerful
conditions to the primes 23 and 2,3,13. Only these small primality and exact
divisibility facts use decidable computation. `decide +kernel` invokes Lean's
kernel, not native execution with an assumed result. Squares are excluded
by monotonicity of multiplication and the interval between 110² and 111².

The complete target theorems are:

```lean
JSP000301.counterexample :
  ∃ n : Nat, 0 < n ∧ Powerful n ∧ Powerful (n + 1) ∧
    ¬ Square n ∧ ¬ Square (n + 1)

JSP000301.original_claim_false :
  ¬ (∀ n : Nat, 0 < n → Powerful n → Powerful (n + 1) →
    Square n ∨ Square (n + 1))
```

The witness is 12167. This is the same full yes/no statement as the catalog,
not a conjecture about the frequency, minimality, or count of counterexamples.
The mathematical witness was already known and recorded in the catalog.

## Reproduction

With a Lean 4.34.0 distribution available, run from the repository root:

```sh
python3 docs/submissions/jsp-000301/proof/verify.py "$(command -v lean)"
```

Install the pinned release and put its executable on PATH before running the command.
The distribution was downloaded from the official Lean release and its full
archive SHA-256 matched the digest in the official GitHub release metadata.
See [release metadata](../evidence/lean-release.json) and
[download verification](../evidence/toolchain-download.json).

The runner creates fresh project output in a temporary directory, compiles
the actual source, saves compiler output including all `#print axioms`
commands, then runs the distribution's `leanchecker` on the resulting module.
It records versions, hashes, platform and exit codes. Temporary module output
is deleted afterward; reproducible source and logs are retained. Neither
tool loads a previously built version of this proof. The distribution's
bundled libraries remain prebuilt dependencies.

Both compilation and replay returned exit code 0. The main theorems and
audited supporting lemmas depend only on `propext` and `Quot.sound`, standard
Lean axioms for propositional extensionality and quotients. This is **not an
axiom-free proof**, but there is no incomplete-proof axiom, custom axiom,
`sorry`, `admit`, or `native_decide` in the final source. The replay utility
uses the same Lean kernel; it is not an independent implementation or an
independent human review.

## Earlier attempts and limits

An initial large finite enumeration timed out after 240 seconds. A kernel
enumeration retry was stopped with SIGTERM before replacing that approach.
The first algebraic attempt exposed a missing explicit arithmetic hypothesis;
Lean emitted an error and incomplete-proof dependencies for that failed
attempt. Those diagnostics are retained as failed attempts only. The final
source fixes the hypothesis, and the successful final log has no such
dependency. Historical failure logs must not be mistaken for the accepted
proof's axiom audit.

The contribution PR and intake issue provide immutable Git commit references.
No permanent scholarly archive, separate checker implementation, signed statement
comparison, minimum-safe-version approval, or independently isolated rebuild is claimed. The check ran as the
ordinary session user; the runner did not itself disable networking or impose
a memory cap. These limitations are recorded rather than converted into
passing isolation or review flags.
