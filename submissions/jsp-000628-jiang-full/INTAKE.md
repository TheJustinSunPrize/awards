# Formal-proof evidence intake

Problem: [JSP-000628](../../problems/catalog-0601-0700.md#jsp-000628),
Erdős Problem 767.

Requested review: record that Tao Jiang's complete 2004 theorem for positive
`k` and `n ≥ 3k + 3` has a public Lean 4 formalization, and assess the
catalog's current `Lean proof: No` marker in light of that evidence.

Pinned standalone proof package:
[636fa0570b02fc20f58516d3a41ca6a6735bf24d](https://github.com/zeke-ai/erdos-767-jiang-lean/tree/636fa0570b02fc20f58516d3a41ca6a6735bf24d).

The retained proof originated in
[`plby/lean-proofs` commit `8822f7d`](https://github.com/plby/lean-proofs/tree/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems).
The source identifies Tao Jiang as informal author and Codex / GPT-5.6 Sol as
formal authors. This submission packages, rebuilds, audits, and pins that
existing Apache-2.0 work; it does not claim a new mathematical result or
exclusive formal authorship.

Local verification rebuilt all retained modules and completed
`lake build ErdosProblems.Erdos767` successfully (8,732 jobs). The final
theorem's axiom closure contains only `propext`, `Classical.choice`, and
`Quot.sound`; see [the verification summary](verification/summary.json).

PR #573 is complementary: it formalizes Chen--Ning's later critical-threshold
sharpness construction but explicitly omits Jiang's upper bound and full
extremal equality. This package supplies the complete original theorem, not
the stronger 2026 formula for all `n ≥ k + 2`.

Please assess statement fidelity, provenance, attribution, and whether this
evidence warrants correcting the catalog marker. No award amount, solving
share, confirmed recipient, or payment right is asserted. This changes no
candidate, recipient, verification, or award record.
