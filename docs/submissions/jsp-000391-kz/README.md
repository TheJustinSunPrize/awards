# JSP-000391: Stoll's general-base digit recurrence

## Contribution and review request

This is a Lean formalization of Thomas Stoll's 2005 Theorem 1.3, a general-base digit-generating construction associated with JSP-000391 / Erdos Problem 482. It covers every integer radix g >= 2, every positive real target w, every shift in the theorem's admissible interval, and every digit index. It is not a finite numerical example.

Mathematical discovery belongs to Stoll and the earlier literature. This submission seeks review of a formalization contribution, not a new mathematical discovery. It does not claim to formalize all results in Stoll's 2005 or 2006 papers, classify every possible recurrence, establish global first-formalization priority, or create an entitlement to any award. Please assess scope, attribution, originality of the formalization, and eligibility.

Proposed recipient placeholder: `RECIPIENT-JSP-000391-KZ-A`, confirmation pending. The implementation and verification were prepared with OpenAI ChatGPT assistance under the submitting account's direction. No independent human or organizer approval is claimed.

## Mathematical statement and fidelity

Let `m = floor(log_g(w))` and `t = w/g^m`. The formal proof establishes `1 <= t < g`. Set

```
a = g / ((g - 1) * (t + g))
b = (g - 1) * (t + g) = g/a
-1/g <= e < (g + 1)*(g - 2)/g
```

The integer sequence is genuinely defined by recursion, starting with `v(0)=1`:

```
v(n+1) = floor(a*(v(n)+e))                 when n is even
v(n+1) = floor(b*(v(n)+1/(g-1)))           when n is odd
```

The index shift is `v(n) = u_(n+1)` relative to the paper. For every `n >= 0`,

```
v(2*n+2) - g*v(2*n) = digit(n)
```

where `digit(0)=floor(t)` is the leading significant digit and `digit(n+1)=floor(t*g^(n+1))-g*floor(t*g^n)`. These are standard floor-difference radix digits. Leading and fractional positions are not interchanged. For targets with two radix expansions, floor truncation chooses the terminating expansion, not an eventually all-(g-1) expansion.

The proof additionally establishes that every digit is in `[0,g)` and that decoding the first n+1 digits and dividing by g^n converges to t, with error in `[0,g^(-n))`. Thus the label "digit" is supported by bounds and reconstruction, not merely assigned to a new arbitrary sequence. Multiplying by g^m restores the original target w.

`jsp000391` supplies the explicit admissible shift e=-1/g. This proves the parameter conditions are satisfiable for every radix. Real parameters and real floor require Lean's `noncomputable` definitions; this is not an admitted proof or an assumed computational oracle. The result is a mathematical correctness theorem, not a claim of a faster numerical algorithm.

## Proof outline

Define the integer geometric sum G(0)=0 and G(n+1)=g*G(n)+1. Prove `(g-1)*G(n)=g^n-1`. Starting from the specified initial value, paired induction establishes

```
v(2*n+1) = G(n)
v(2*n+2) = floor((t+g)*g^n)
```

The expanding step is an exact algebraic identity. The contracting step uses the two defining floor inequalities, the lower and upper shift bounds, and t>=1. No numerical experiment is used in this induction. Translating the second closed form by the integer g^(n+1) yields the required digit differences. Separate floor estimates prove the digit bounds and truncation error, and an Archimedean bound proves convergence.

## Reproduction

With the pinned toolchain available, run from this directory:

```sh
sha256sum -c SOURCE_SHA256SUMS
lake exe cache get
lake build --wfail
lake env leanchecker JSP000391
lake env leanchecker JSP000391Main
lake env lean Audit.lean
```

The Lean compiler and Mathlib revisions are fixed by `lean-toolchain`, `lakefile.lean`, and the committed `lake-manifest.json`. All imported Mathlib infrastructure remains credited to its contributors. The [full verification scripts](https://github.com/ketianzhang1-lang/jsp-000301-lean/tree/56f083c6183e93eeffc334e04e39a26548bfae96/projects/jsp-000391/scripts) additionally check actual dependency revisions, transitive axiom reports, negative controls and NaNoda. The selected target proofs and their full transitive dependencies are independently replayed; no nonstandard axioms are permitted.

See [VERIFICATION.md](VERIFICATION.md) for the exact tested proof commit, actual run results, artifact checksums, retention limits and remaining review boundaries. Two checker implementations run by one contributor are not independent human certification.

## References and prior-work screening

- [Stoll, Journal of Integer Sequences 8 (2005), Article 05.3.2](https://cs.uwaterloo.ca/journals/JIS/VOL8/Stoll/stoll56.html), Theorem 1.3 and Section 2.2.
- [Original article PDF](https://cs.uwaterloo.ca/journals/JIS/VOL8/Stoll/stoll56.pdf).
- [Erdos Problem 482](https://www.erdosproblems.com/482).
- [Pinned prize catalog entry](https://github.com/TheJustinSunPrize/awards/blob/f4e7173d89dfe91022a185427d63452c8ffbf6ae/problems/catalog-0301-0400.md#JSP-000391).

On September 16, 2026, bounded official issue/PR searches for JSP-000391 and Erdos 482, and public code searches for Erdos482 and the digit-recurrence terminology, did not identify an earlier matching complete Lean proof. This is limited search evidence, not certification that none exists or that this contribution has priority.

This is an evidence-intake proposal. No existing catalog flags, candidate/award records, recipient profiles, schemas, validators, tests or unrelated proof submissions are changed. Exact mathematical attribution and MIT licensing of the newly written code are retained.
