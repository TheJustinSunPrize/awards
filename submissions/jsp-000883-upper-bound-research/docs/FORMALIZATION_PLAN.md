# Lean work still required

The files in `lean/` are target definitions only. They do not discharge the proof obligations below. Passing a build of those files would NOT certify the proposed mathematics.

## Arithmetic construction

Prove p divides L, `v_p(L)=1`, p does not divide k, and consequently p does not divide m. Prove `m>=2k`, ensure every natural subtraction in the descending block is nontruncated, and prove the two directions' interval identities.

## Two multiples and valuations

Prove the residue/direction lemma `2s>=p` implies either `r<=s` or `p−r<=s`. Build two distinct in-range multiples of p. Prove the lower valuation estimate for all q≠p and the exact estimate at a prime q dividing k.

Use either `Nat.factorization` or the natural padic valuation API with all positivity/prime assumptions made explicit. Do not assume the main inequality as a helper axiom. Avoid factoring the enormous numerical witness in the universal proof.

## Binomial coefficient bridge

Prove or reuse the identity between `choose(n,k)*k!` and the k-term descending product, with `k<=n`. Translate the valuation inequalities into divisibility of the actual `Nat.choose` value for every nonexceptional element. Translate the strict valuation at q into failure of divisibility for m.

## Minimum and asymptotics

Supply actual admissible witnesses and apply minimality of the natural infimum; do not use its empty-set convention. Formally establish eventual existence of a prime in `(k/2,(2k−2)/3]` from a proved prime-number-theorem result or another proved interval theorem. Prove the Big-O endpoint and the Little-o comparison with the natural-number lcm cast to Real.

The fixed Mathlib configuration is a starting configuration only. If its available prime-distribution APIs require an external library, pin and attribute that library and inspect the final axiom closure. This has not been resolved here.

## Required verification, not yet run

Compile the universal finite theorem and the unconditional asymptotic theorem, check their exact types against the intended statements, and run `#print axioms` for every final result. Check no `sorryAx` or custom mathematical axiom enters through dependencies. Independently reproduce the build; where required, use an additional checker. Record real commands, exit codes and hashes.

No final theorem currently exists to audit, so this package intentionally does not offer an “axiom audit passed” file or a success-marked Lean verifier.
