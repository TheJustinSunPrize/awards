# Four-prime binomial gcds: partial progress on Erdős 700

This project proves a local sufficient condition for the function

    f(N) = min { gcd(N, choose(N,k)) : 2 <= k <= floor(N/2) }.

For natural numbers P,a,b,c, assume

    1 <= a, 3a <= b, 3b-a+1 <= c, 12c^3 <= P,
    P, P+a, P+b, P+c are prime.

Then the Lean theorem `Erdos700.FourPrime.four_prime_exact_cubic` proves

    f(P(P+a)(P+b)(P+c)) = P(P+a)(P+b).

Version 5 weakens only the base-size requirement to `P >= 12c^3`, keeping
`c >= 3b-a+1`. All four preceding declarations keep their published types as
corollaries: `four_prime_exact_boundary`, `four_prime_exact_linear`,
`four_prime_exact_relaxed`, and `four_prime_exact`.
See [the cubic-size extension note](docs/cubic-size.md).

The function and minimization range match the current formal statement of Erdős 700. No pair-exclusion statement or prime-existence theorem is assumed by the final declaration.

## Verification

The complete local theorem compiled with Lean 4.33.1. A fresh standalone `lake build` rebuilt all 17 local modules successfully, with the inherited `LEAN_PATH` cleared. The final audit, run with `-DwarningAsError=true`, printed the complete theorem types and the exact definition of `f`; the new theorem and all four preceding corollaries depend only on `propext`, `Classical.choice`, and `Quot.sound`. There is no `sorryAx` or custom axiom in those dependency lists. See [the build log](verification/canonical-build.log), [the audit log](verification/canonical-audit.log), and [the build record](verification/build-record.json). The dependency pin is Mathlib `0df444a360eaa60ab8c11dca51a86af692955474` (v4.33.1).

To reproduce with the pinned Lean toolchain installed:

```sh
lake exe cache get
lake build
lake env lean -DwarningAsError=true Audit.lean
```

The Mathlib cache contains precompiled dependency artifacts. The local proof modules are built from source. This workflow is not an independent alternative checker or organizer verification.

## Scope and prior work

The [mathematical note](docs/proof.md) combines the local criterion with Maynard's theorem to derive infinitely many N with f(N)/N^(3/4) tending to 1. **That infinite-family consequence, Maynard's theorem, and the asymptotic limit are not formalized in this project.** Only the displayed local four-prime theorem is the Lean submission target.

The preceding three-prime / 2/3-exponent result is credited on the [problem page](https://www.erdosproblems.com/700) to GPT 5.6 Sol Pro prompted by Liam Price; [its manuscript](https://www.overleaf.com/read/pmnwkfnhhxhn#82956e) is cited explicitly. The full characterization and general logarithmic upper-bound questions remain open in this submission. No first solution of the already answered square-root infinitude question is claimed. See [the limited novelty review](docs/novelty.md).

This packet requests review as **partial progress** on JSP-000570, not a full-resolution status change or an award announcement. Historical priority, external peer review, official verification, recipient confirmation, and prize eligibility are not established by these local checks.

## Attribution and license

The project was prepared with OpenAI Codex assistance for mathematical exploration, Lean implementation, and internal review. Internal parallel AI audits are not external human peer review. New recipient attribution remains `RECIPIENT-JSP-000570-A`, pending confirmation; no private identity or payment information is included.

The definition of `f` follows the Apache-2.0-licensed Formal Conjectures statement; its attribution is retained in `Minimum.lean`. Mathlib and Lean are external pinned dependencies, not vendored here. The predecessor's manuscript is linked rather than redistributed. This project's proof source and original accompanying materials are provided under Apache-2.0; see [LICENSE](LICENSE).
