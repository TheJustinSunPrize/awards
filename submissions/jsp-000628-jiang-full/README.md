# JSP-000628 / Erdős 767: Jiang's full theorem

This package provides a reproducible Lean 4 formalization of Tao Jiang's
2004 solution to Erdős Problem 767. It proves the complete-bipartite
construction is extremal for every positive `k` and every
`n ≥ 3 * k + 3`:

```lean
theorem Erdos767.erdos_767 (k n : ℕ) (hk : 0 < k)
    (hn : 3 * k + 3 ≤ n) :
    chordCycleExtremalNumber k n =
      (k + 1) * n - (k + 1) ^ 2
```

This is the original Jiang theorem listed by JSP-000628. It is distinct from
PR #573, which formalizes only Chen--Ning's later critical-threshold
sharpness construction and explicitly omits the upper bound and full
extremal formula.

## Provenance

The proof source is retained from `plby/lean-proofs`, pinned at commit
`8822f7ddef30fadbd92e1c6ab4ed897af356af5e`. The upstream files identify
Tao Jiang as the informal author and Codex / GPT-5.6 Sol as formal authors.
The source is Apache-2.0 licensed; original copyright and license headers are
preserved. No mathematical novelty or exclusive authorship is claimed here.

Upstream source:

<https://github.com/plby/lean-proofs/tree/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems>

Pinned standalone proof package:

<https://github.com/zeke-ai/erdos-767-jiang-lean/tree/636fa0570b02fc20f58516d3a41ca6a6735bf24d>

## Verification

The package pins Lean 4.33.0 and Mathlib commit
`db584cd6d46c92f209a44c0f1c829460d327499d`.

Run:

```sh
lake update
lake exe cache get
lake build ErdosProblems.Erdos767
lake env lean Audit.lean
```

The audited upstream build completed successfully with 8,732 jobs. Lean
reported only the standard axioms `propext`, `Classical.choice`, and
`Quot.sound` for `Erdos767.erdos_767`.
