## Contribution

This pull request submits a complete Lean formalization of the negative answer
for [JSP-000660](https://github.com/TheJustinSunPrize/awards/blob/f4e7173d89dfe91022a185427d63452c8ffbf6ae/problems/catalog-0601-0700.md#JSP-000660):

> Does every dense graph contain a sufficiently dense subgraph whose vertex
degrees are comparable?

The package defines the exact quantified assertion as
`JSP000660.target_statement` and proves its negation in
`JSP000660.not_jsp_000660`. It also supplies the literal
`False ↔ target_statement` form as `JSP000660.answer_false_iff`. The proof uses
an explicit complete bipartite counterexample and does not substitute a finite
special case.

This is a formalization contribution only. It claims no new mathematical
discovery, award, eligibility decision, recipient confirmation, or independent
review. The proposed recipient remains `RECIPIENT-JSP-000660-A` pending the
public review process.

## Attribution and sources

The mathematical result is attributed to the Erdős--Simonovits problem and
Noga Alon's negative construction in [Problems and results in extremal
combinatorics--II](https://doi.org/10.1016/j.disc.2007.08.090), Section 2 and
Proposition 2.1. The exact formal statement follows the public [Formal
Conjectures Erdős Problem 1077 source](https://github.com/google-deepmind/formal-conjectures/blob/40e7c98697de6f66b8cbdbf641749ab39ed9c152/FormalConjectures/ErdosProblems/1077.lean).

The retained proof is copied byte-for-byte from the immutable public
[plby/lean-proofs source](https://github.com/plby/lean-proofs/blob/dfe2d78128b493c572cf525b1b8edf4897fb7664/src/latest/ErdosProblems/Erdos1077.lean).
Its source header credits Codex and GPT-5.6 Sol for the formalization and the
Formal Conjectures authors for the statement. The wrapper and packaging were
prepared with OpenAI Codex assistance. Apache License 2.0 is retained in the
package.

## Validation

- Lean `4.33.1` and Mathlib revision
  `0df444a360eaa60ab8c11dca51a86af692955474` are pinned.
- `./verify.sh`, `lake build`, and direct Lean checks for both modules passed.
- The audited declarations use only `[propext, Classical.choice, Quot.sound]`.
- The source scan found no `sorry`, `admit`, `sorryAx`, `native_decide`, or
  `unsafe` proof escape.
- The official repository `validate`, `links`, `build`, `check`, and all 22
  repository tests passed.
- `SHA256SUMS` records the package bytes. Build products under `.lake/` are not
  committed.

The repository's structural CI and this local kernel check do not replace an
independent mathematical review or an award decision.
