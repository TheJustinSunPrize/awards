# Candidate observation

## English

This candidate observation is associated with [JSP-000873 — multiply perfect numbers](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0801-0900.md#JSP-000873). It publishes `Statement.lean` and `Proof.lean` for a complete, machine-checked Lean formalization of an existence observation for the `k = 3` component of the multiply perfect numbers question: the divisor-sum function `σ` (Mathlib's `ArithmeticFunction.sigma 1`) satisfies `σ(120) = 360 = 3 * 120` and `σ(672) = 2016 = 3 * 672`, i.e. `120` and `672` are triply perfect (3-perfect) numbers. The theorems proved are `jsp000873 : ∃ (n k : ℕ), 1 < k ∧ ArithmeticFunction.sigma 1 n = k * n` (witnessed by `n = 120`, `k = 3`) and `jsp000873_second : 1 < 3 ∧ ArithmeticFunction.sigma 1 672 = 3 * 672`.

**Scope boundary:** a multiply perfect number is a positive integer `n` with `σ(n) = k * n` for some integer `k > 1` (`k = 2` gives the classical perfect numbers). This observation records only the concrete existence instances for the `k = 3` component. It does not address the catalogued asymptotic question — whether the multiplier `σ(n)/n` must be of smaller order than the iterated logarithm of `n` — nor infinitude or density aspects, does not resolve the catalogued open problem, which remains Open, and makes no award claim.

The formal source is pinned to the public repository [Yaohua-Leo/jsp-000873-lean](https://github.com/Yaohua-Leo/jsp-000873-lean) at commit `5037b9f684fc09a68c0b6ebf898aab39f18f1cc7` on branch `main`. A local Lean compilation was run with the pinned toolchain `leanprover/lean4:v4.35.0-rc2` and Mathlib `v4.35.0-rc2`: `lake env lean JSP000873.lean` produces zero output, and `#print axioms` for both theorems reports exactly `[propext, Classical.choice, Quot.sound]`. These compiler results are reproducibility evidence for the stated formal theorems; they are not official JSP verification or award admission.

The catalog entry records "No later than 2004 (bibliographic evidence)" with no publication details, so the `posed.citation` field points to the catalog entry itself as the source of record rather than to an external publication.

The candidate remains under verification. No award decision, recipient identity, solver or formalizer credit, payment, or official verification is asserted.
