# Greedy perfect difference sets with explicit cubic bounds

Scoped Lean evidence for **JSP-000999 / Erdős 1194**: an executable greedy construction extending any finite Sidon set of positive integers to an infinite perfect difference set, with explicit bounds on both representation endpoints and finite counting witnesses.

For any positive difference `d`, the empty-seed construction has exactly one ordered pair `(u,v)` with `u,v ∈ A`, `u>v` and `u−v=d`, and its top endpoint satisfies

`u ≤ 2*(2*d+1)^3`.

For a seed `S` of size `k` and maximum `M` (zero if empty), the bound is `M + 2*(k+2*d+1)^3`. The seed is retained. After `n` steps there are exactly `k+2*n` elements, all at most `M + 2*(k+2*n+1)^3`.

**This formalizes known greedy-construction mathematics. It does not improve the cubic exponent, solve the optimal-growth problem, or claim first-formalization priority or award eligibility.** Existing formal work on the same problem proves a different, lower-bound direction; see [PRIOR_ART.md](PRIOR_ART.md). No catalog or award record is changed.

## Evidence

- [PerfectDifference.lean](PerfectDifference.lean): 36 named theorems. Main entries: `finite_seed_completion`, `completion_endpoint_bound`, `exists_perfect_cubic`.
- [STATEMENT.md](STATEMENT.md): exact quantifiers, definitions and relation to the original problem.
- [PROOF.md](PROOF.md): finite obstructions, iteration and cubic estimates.
- [VERIFICATION.md](VERIFICATION.md): reproducible checks and their limits.
- [Audit.lean](Audit.lean): axiom closures of all named theorems.
- [Evaluation.lean](Evaluation.lean), [tools/check_small.py](tools/check_small.py): formal finite controls and supplemental exact Lean/Python comparisons.

Pinned environment: Lean **4.34.0**, Mathlib **5ed2965256430c3649e86755f9576b54eca72435**.

```sh
lake exe cache get
python3 tools/verify.py
```

The verification script checks the compiler and all nine dependency revisions, builds the proof, audits every named theorem, compares executable outputs against exact Python computations, and runs `lake env leanchecker --fresh --verbose PerfectDifference`. Logs and input hashes are retained in `verification/`. Compiled dependency caches are used; the kernel replay is Lean's official implementation, not an independent implementation or organizer-designated verification.

Finite-stage definitions are executable, but the finite obstruction enumeration costs at least cubic work in the current stage size and is intended here for small checks. The infinite set is a mathematical union, not a finite exhaustive output. Python checks are supplementary to the universal Lean proofs.

Prepared with GPT/Codex assistance by public GitHub account `green3sf`. The submitter has an interest in recognition of this formal contribution. Acceptance, attribution and any recognition remain for the organizers to assess.
