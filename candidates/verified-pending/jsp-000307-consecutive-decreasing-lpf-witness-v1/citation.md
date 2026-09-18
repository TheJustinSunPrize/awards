# Citation

## English

Verified-pending candidate for JSP-000307 (Erdős problem 307): "Can three
consecutive integers have strictly decreasing largest prime factors?"

The catalog records the problem as Solved with the deeper Balog 2001
result (infinitely many such triples exist). This candidate records
only the **existence** of one witness triple, proved by a complete
Lean 4 / Mathlib v4.33.0 formalization at
https://github.com/lyssom/jsp-000307-lean.

Witness: `n = 13`. The triple (13, 14, 15) has largest prime factors
(13, 7, 5), with `13 > 7 > 5`.

Theorem (`JSP000307.JSP_307`):

```lean
∃ n : ℕ, IsLPF n 13 ∧ IsLPF (n + 1) 7 ∧ IsLPF (n + 2) 5 ∧ 13 > 7 ∧ 7 > 5
```

Recipient: Liu Yu (刘煜) / GitHub `lyssom`, with public publication
consent at https://gist.github.com/lyssom/113fe050f18bdc8ac01bce07dc54c71e.

Status: `under-verification`. The Lean formalization has been built
(8707 jobs, axiom audit `[propext, Classical.choice, Quot.sound]` only,
no `sorry`/`admit`/`native_decide`/custom axioms), but the formal
verification record (`verification/record.yaml` with pinned commits,
independent checkers, and statement comparison) has **not yet been
completed**. The `verification/formal` field is intentionally `null`
until an independent reviewer closes the statement comparison
(`equivalent`) and an independent runner reproduces the build.

Scope honesty: this formalization does NOT formalize the Balog 2001
"infinitely many" theorem. It only proves that at least one such
triple exists. Tier evaluation should reflect "Partial Progress /
Contribution" rather than full resolution.

Toolchain (pinned, immutable): Lean v4.33.0, Mathlib v4.33.0.