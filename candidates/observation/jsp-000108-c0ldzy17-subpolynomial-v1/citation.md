# Candidate observation: the full subpolynomial question

## English

This observation concerns the full negative answer to [JSP-000108](https://github.com/TheJustinSunPrize/awards/blob/f4e7173d89dfe91022a185427d63452c8ffbf6ae/problems/catalog-0101-0200.md#JSP-000108), corresponding to the weak variant of Erdos Problem 92. The proved endpoint is `Jsp108.jsp_000108`:

```text
¬ ∃ o : ℕ → ℝ, o =o[atTop] (1 : ℕ → ℝ) ∧
    ∀ n, (Erdos92.f n : ℝ) ≤ (n : ℝ) ^ (o n).
```

The second endpoint, `Jsp108.jsp_000108_eventually`, also rules out an eventual bound. The [submission pointer and statement](../../../submissions/jsp-000108-c0ldzy17/README.md) provide exact source pins, archive identifiers, SHA-256, byte count, evidence, and reproduction instructions. The complete proof is published in [release v1.1.0](https://github.com/c0ldzy17/jsp-000108-lean/releases/tag/v1.1.0), pinned to commit `11cfb8098dfb5527a5943d35b2698b4786233f4e`.

The Lean 4.33.1 build passed with 10,329 jobs. All three endpoints use only `propext`, `Classical.choice`, and `Quot.sound`. Stock checking of all nine local modules passed. Fresh stock-kernel replay checked 132,615 declarations for the three final endpoints in an empty trust-level-zero environment. The axiom declaration kinds, types, and universe parameters match the pinned toolchain Init. These local checks do not constitute designated independent review.

The scope differs from [PR 256](https://github.com/TheJustinSunPrize/awards/pull/256), which addresses the fixed-constant `C / log log n` bound and explicitly excludes the arbitrary `o(1)` variant. Refuting that narrower family alone would not prove this target.

The mathematics is attributed to [Sawin](https://arxiv.org/abs/2605.20579) and the [Alon–Bloom–Gowers–Litt–Sawin–Shankar–Tsimerman–Wang–Matchett Wood exposition](https://arxiv.org/abs/2605.20695). Formal reuse includes Naganori Yamaguchi, Logical Intelligence, Formal Conjectures authors, and Kim Morrison. The earlier plby / Codex / GPT-5.6 Sol reduction remains credited as prior work. Version 1.1 replaces the two previously reconstructed adapters with newly written proofs, includes all proof sources directly, and explicitly licenses original additions under Apache-2.0. The historical plby reduction remains credited and all upstream notices are preserved.

This observation candidate remains `under-verification`. The formal verification record, independent review, and decision are null. A signed formal statement and designated independent review remain for the curatorial process. No award, recipient confirmation, eligibility, or established first priority is asserted.

The original [v1.0.0 release](https://github.com/c0ldzy17/jsp-000108-lean/releases/tag/v1.0.0) remains available. Version 1.1 preserves the mathematical scope and supplies new adapter implementations and explicit licensing; it does not claim a new mathematical discovery.
