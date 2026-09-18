# Citation

## English

Observation candidate for JSP-000307 (Erdős problem 307): "Can three
consecutive integers have strictly decreasing largest prime factors?"

The catalog records the problem as Solved with the deeper Balog 2001
result (infinitely many such triples exist). This observation records
only the **existence** of one witness triple, proved by a complete
Lean 4 / Mathlib v4.33.0 formalization at
https://github.com/lyssom/jsp-000307-lean.

Witness: `n = 13`. The triple (13, 14, 15) has largest prime factors
(13, 7, 5), with `13 > 7 > 5`.

Theorem (`JSP000307.JSP_307`):

```lean
∃ n : ℕ, IsLPF n 13 ∧ IsLPF (n + 1) 7 ∧ IsLPF (n + 2) 5 ∧ 13 > 7 ∧ 7 > 5
```

Scope honesty: this formalization does NOT formalize the Balog 2001
"infinitely many" theorem. It only proves that at least one such
triple exists. Tier evaluation should reflect "Partial Progress /
Contribution" rather than full resolution.

Axiom audit: every proved theorem depends only on `[propext,
Classical.choice, Quot.sound]`. No `sorry`, no `admit`, no
`native_decide` trust oracle, no custom mathematical axioms.
This matches the gold standard of `plby/lean-proofs` in the
upstream `TheJustinSunPrize/awards` repo.

Toolchain (pinned, immutable): Lean v4.33.0, Mathlib v4.33.0.