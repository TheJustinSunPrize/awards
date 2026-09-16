# Candidate observation

## English

This preliminary observation is associated with [JSP-000108 — equidistant neighbors in planar point sets](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0101-0200.md#JSP-000108). It publishes a pinned Lean package in [`submissions/jsp-000108`](../../../submissions/jsp-000108/README.md), including the statement correspondence, source attribution, license notices, dependency lock, reproduction script, and axiom report.

**Claim boundary: full negative theorem for the exact strong fixed-constant formalization.** The theorem `JSP000108.not_jsp_000108` proves the negation of

```text
∃ c > 0, eventually f(n) ≤ n^(c / log log n).
```

This classification does not claim the separately recorded weaker `n^(o(1))` variant, independent equivalence between every possible reading of the catalog prose and the encoded proposition, an official JSP verification decision, an award, eligibility, or recipient confirmation.

The formal statement is attributed to [Formal Conjectures at commit `40e7c98697de6f66b8cbdbf641749ab39ed9c152`](https://github.com/google-deepmind/formal-conjectures/blob/40e7c98697de6f66b8cbdbf641749ab39ed9c152/FormalConjectures/ErdosProblems/92.lean). The proof and supporting files are attributed to [plby/lean-proofs at commit `8822f7ddef30fadbd92e1c6ab4ed897af356af5e`](https://github.com/plby/lean-proofs/tree/8822f7ddef30fadbd92e1c6ab4ed897af356af5e); the package preserves the public source headers and Apache-2.0 notice.

The package reports a local Lean 4.33.1 build with pinned Mathlib revision `0df444a360eaa60ab8c11dca51a86af692955474`. That build and axiom report are reproducibility evidence only, not independent mathematical review or official verification. The candidate remains under verification.
