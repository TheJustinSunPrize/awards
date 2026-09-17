# JSP-000247 / Erdős 291: the general prime-divisibility criterion

This package formalizes **Stefan Steinerberger's known necessary and sufficient criterion** for cancellation in the denominator of a harmonic number. It covers every prime `p ≤ n`, rather than only the prime 3.

Let `L(n) = lcm(1, …, n)` and `a(n) = ∑_{i=1}^n L(n)/i`. Put `k = n / p^(Nat.log p n)`, the leading base-`p` digit of `n`. The proved theorem is

```text
p ∣ gcd(a(n), L(n))  ↔  p ∣ numerator(1 + 1/2 + … + 1/k).
```

`Erdos291Criterion.steinerberger_generalization` has the exact type of the corresponding Formal Conjectures variant, with the original definitions, a primality hypothesis, and `p ≤ n`. `Erdos291Criterion/Audit.lean` repeats the definitions and statement separately and checks this correspondence.

This is a formalization contribution. It does not settle whether `gcd(a(n), L(n)) = 1` infinitely often, the density-zero conjecture, or the asymptotic counting conjecture. It does not establish award eligibility or mathematical priority.

## Proof idea

Write `P = p^floor(log_p n)` and `k = floor(n/P)`. The exponent of `p` in `L(n)` is exactly `floor(log_p n)`. Consequently `p` divides `L(n)/i` whenever `P` does not divide `i`.

The remaining terms are indexed by `i = Pj`, `1 ≤ j ≤ k`. Their sum is exactly `w * a(k)`, where `w = (L(n)/P)/L(k)` is an integer not divisible by `p`. Thus `p ∣ a(n)` precisely when `p ∣ a(k)`. Since `k < p`, reducing `a(k)/L(k)` to lowest terms preserves this divisibility. Finally `p ≤ n` ensures `p ∣ L(n)`.

This argument uses a unit factor `w`; it does not assume the two harmonic numerators themselves are congruent without that factor.

## Reproduce

Install the toolchain named in `lean-toolchain`, then run from this directory:

```sh
lake exe cache get Mathlib.NumberTheory.Chebyshev Mathlib.Data.Rat.Lemmas Mathlib.Tactic.FieldSimp Mathlib.Tactic.Ring Mathlib.Tactic.NormNum
bash tools/verify.sh
```

The complete dependency revisions are pinned in `lake-manifest.json`. Cached `.olean` files and discovery computations are not accepted as the final evidence: the verification script also invokes `leanchecker --fresh` to replay the imported environment. This uses the bundled Lean kernel, not an independent verifier implementation.

## Attribution and related work

- [Erdős Problems 291](https://www.erdosproblems.com/291) attributes the criterion to Stefan Steinerberger.
- [Formal Conjectures statement](https://github.com/google-deepmind/formal-conjectures/blob/40e7c98697de6f66b8cbdbf641749ab39ed9c152/FormalConjectures/ErdosProblems/291.lean): `erdos_291.variants.steinerberger_generalization`. The definitions and statement are adapted under Apache-2.0; see `NOTICE`.
- [Prize PR #216](https://github.com/TheJustinSunPrize/awards/pull/216) proves the prime-3 infinitude result. The present submission supplies the general necessary-and-sufficient criterion. No proof code from #216 is incorporated.
- [Woett's related development](https://github.com/Woett/Lean-files/blob/main/ErdosProblem291.lean) concerns unbounded gcds for periodic numerator sequences under additional hypotheses. It is related prior work, not a dependency of this proof.
- Mathlib supplies the factorization of `lcm(1, …, n)` and standard divisibility and rational-number lemmas.

New proof and packaging: GitHub account `James-16`, with substantial OpenAI Codex assistance. The mathematical result remains attributed to Steinerberger; the formal statement remains attributed to its authors. No exhaustive priority claim is made.

## Evidence

See `verification/RESULTS.md`, the recorded build and axiom output, and `verification/SHA256SUMS`. Boundary checks include `p=2`, an example with `p=11` and leading digit 3, and a counterexample showing why the hypothesis `p ≤ n` matters.
