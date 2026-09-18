# Citation

## English

Observation candidate for JSP-000307 (Erdős problem 307): "Can three
consecutive integers have strictly decreasing largest prime factors?"

This record proves only the **existence** of a witness triple
(n = 13, with largest prime factors 13 > 7 > 5) in Lean 4 / Mathlib
v4.33.0. It does **not** prove the full result recorded in the catalog
(Balog 2001: infinitely many such triples exist), it does not resolve
the catalogued problem, and it makes **no award claim**.

The catalog entry for JSP-000307 remains `Solved` with `Lean proof: No`
and `Eligible to claim: No`. This observation record is published for
transparency only; it does not change any catalog status or eligibility
field.

Main theorem (`JSP000307.JSP_307`, in `JSP000307.lean`):

```lean
∃ n : ℕ, IsLPF n 13 ∧ IsLPF (n + 1) 7 ∧ IsLPF (n + 2) 5 ∧ 13 > 7 ∧ 7 > 5
```

Axiom audit: every proved theorem depends only on `[propext,
Classical.choice, Quot.sound]`. No `sorry`, no `admit`, no
`native_decide`, no custom axioms.

Lean author: lyssom (with AI assistance from MiniMax-M3). No recipient
identity is confirmed or claimed in this record (`recipients: []`).
