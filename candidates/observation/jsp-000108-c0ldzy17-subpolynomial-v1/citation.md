# Candidate observation: the full subpolynomial question

## English

This observation concerns the full negative answer to [JSP-000108](https://github.com/TheJustinSunPrize/awards/blob/f4e7173d89dfe91022a185427d63452c8ffbf6ae/problems/catalog-0101-0200.md#JSP-000108), corresponding to the weak variant of Erdős Problem 92. The proved source endpoint is `Jsp108.jsp_000108`:

```text
¬ ∃ o : ℕ → ℝ, o =o[atTop] (1 : ℕ → ℝ) ∧
    ∀ n, (Erdos92.f n : ℝ) ≤ (n : ℝ) ^ (o n).
```

The second endpoint, `Jsp108.jsp_000108_eventually`, also rules out an eventual bound. The [submission pointer and statement](../../../submissions/jsp-000108-c0ldzy17/README.md) describe the proof-source package, provenance, and reproduction procedure. The local Lean 4.33.1 project build passed with 10,329 jobs; the endpoint reports list only `propext`, `Classical.choice`, and `Quot.sound`. Stock checking of all nine local modules passed. A fresh stock-kernel replay also passed for all 132,794 declarations in the dependency closure of the three final endpoints, using an initially empty trust-level-zero environment. The three axiom declarations match the toolchain's canonical `Init` declarations in kind, type, and universe parameters. Immutable external release references remain to be inserted. These local checks do not constitute designated independent review.

The exact scope differs from [PR 256](https://github.com/TheJustinSunPrize/awards/pull/256), which addresses `∃ C > 0, eventually f(n) ≤ n^(C / log log n)` and explicitly does not claim the arbitrary `o(1)` variant. Refuting that narrower family alone would not prove the target recorded here.

The underlying mathematical result is attributed to [Sawin's fixed-power construction](https://arxiv.org/abs/2605.20579) and the [Alon–Bloom–Gowers–Litt–Sawin–Shankar–Tsimerman–Wang–Matchett Wood exposition](https://arxiv.org/abs/2605.20695). Formal reuse includes Naganori Yamaguchi's Sawin tower development, Logical Intelligence's unconditional arithmetic/geometric components, Formal Conjectures definitions, Kim Morrison's counting infrastructure, and plby's credited Codex / GPT-5.6 Sol pruning development. The source package preserves source-specific attribution and states the unresolved license boundary for the reconstructed plby adapters.

This remains an observation candidate with status `under-verification`. `verification.formal`, the verification record, independent review, and the decision are null. A formal candidate record requires an actually issued statement with the required curator signatures; none are invented here. No award, recipient confirmation, eligibility, verified priority, or independent review is announced.
