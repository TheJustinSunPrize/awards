# Compatible-prime extension for reciprocal subset sums

Scoped Lean evidence for **JSP-000266 / Erdős 320**. This package independently formalizes the compatible-prime extension from Bettin–Grenié–Molteni–Sanna (BGMS), together with exact doubling, a finite counting lower bound, executable obstruction tests and arbitrarily large doubling multiples of each irreducible seed.

The main theorem retains arbitrary positive `m`, arbitrary prime `p` and arbitrary natural exponent `k`. If `p` divides none of the reduced numerators of

`1/m − sum_{1 ≤ j < m} w_j/j`, for `w_j ∈ {−1,0,1}`,

then `S(m*p^k) = 2*S(m*p^k−1)`. There is no assumption `m < p` or `p ∤ m`. Exponent zero is included. Here `S(N)` counts distinct rational sums of subsets of `{1,...,N}`, including the empty subset.

**This is not a full formalization of the asymptotic solution of Erdős 320 and does not claim new mathematics, first-formalization priority or award eligibility.** The known mathematics is attributed in [PRIOR_ART.md](PRIOR_ART.md). Existing Lean work for this problem is explicitly compared there. No catalog or award status is changed.

## Contents and verification

- [ReciprocalDoubling.lean](ReciprocalDoubling.lean): 26 named theorems, including the full extension, exact-doubling equivalence, counting lower bound and correctness of executable tests.
- [STATEMENT.md](STATEMENT.md): exact quantifiers and correspondence to the original counting function.
- [PROOF.md](PROOF.md): mathematical proof and the role of each hypothesis.
- [VERIFICATION.md](VERIFICATION.md): environment, replay and limitations.
- [Audit.lean](Audit.lean): axiom audit of every named theorem.
- [Evaluation.lean](Evaluation.lean), [tools/check_small.py](tools/check_small.py): Lean/Python exact cross-checks, including rejection of an incompatible prime.

Use Lean **4.34.0** and Mathlib **5ed2965256430c3649e86755f9576b54eca72435**, as locked by the manifest:

```sh
lake exe cache get
python3 tools/verify.py
```

The script checks actual compiler and all nine dependency revisions, builds the module, audits every theorem, checks executable results against independent rational/integer computations, and performs `lake env leanchecker --fresh --verbose ReciprocalDoubling`. Full logs and hashed inputs are in `verification/`. The official Lean kernel is used; this is not an independent kernel implementation or organizer-designated verification.

The finite tests use powersets and difference sets and are intended for small inputs. The universally quantified theorems do not depend on the Python checks or numerical tables. Exact examples include all `4*2^k` and `4*23^k`, while prime 3 is formally proved incompatible with seed 4. The first example demonstrates the unrestricted statement; it is not a new prime-power result.

Prepared with GPT/Codex assistance by public GitHub account `green3sf`. The submitter has an interest in recognition of this formal contribution. Acceptance, attribution and any recognition remain for the organizers to assess.
