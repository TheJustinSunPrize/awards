# Draft title

Lean evidence for JSP-000360: unbounded additive improvement over the Erdos construction

# Draft body

This submission formalizes a qualitative consequence of Chen and Dai (2007):
for every natural r and M, there is an N >= M for which Erdos's standard
lcm-bounded set can be extended by exactly r elements while retaining all
pairwise lcm bounds.

## Scope and attribution

- Problem: JSP-000360 / Erdos #441.
- Intended contribution: Lean formalization of a known mathematical result.
- Mathematical source: Yong-Gao Chen and Li-Xia Dai, Acta Arithmetica 128 (2007),
  125-133, Theorem 1(ii).
- Earlier formal evidence inspected: plby/lean-proofs at
  8822f7ddef30fadbd92e1c6ab4ed897af356af5e, Erdos441.lean. Its explicit
  construction adds one element on an infinite family of bounds.
- New scope here: an arbitrary number of additional elements, using a factorial
  recurrence. This is not a claim to the first formal proof of the entire problem.
- Exclusions: the sharp extremal asymptotic formula and the quantitative
  iterated-logarithm bound are not proved here.
- OpenAI Codex assistance was used. No recipient or award record is proposed.

## Formal statement

`JSP000360.unbounded_extension` quantifies over all natural r and M and produces
N >= M and a finite A containing the standard construction, with A contained in
[1,N], `Nat.lcm a b <= N` for all a,b in A, and the exact cardinality increment r.
See STATEMENT.md for the definitions and PROOF.md for the mathematical proof.

## Reproduction and verification

Lean 4.19.0; Mathlib c44e0c8ee63ca166450922a373c7409c5d26b00b.
Dependencies are locked in lake-manifest.json.

```sh
lake exe cache get Mathlib.Data.Nat.Factorial.Basic Mathlib.Data.Nat.GCD.Basic Mathlib.Data.Finset.Card Mathlib.Tactic
lake build
lake env lean Audit.lean
```

Local source check, project build, and final theorem audit passed on Windows
x86_64 on 2026-09-17. Axioms: propext, Classical.choice, Quot.sound. No sorryAx
or compiled-evaluation axiom occurs in the final theorem's axiom list.
Official dependency caches were reused. Independent-machine reproduction has
not yet been performed. Build output and SHA-256 checksums accompany the files.

## Requested review

Please review the statement correspondence, mathematical attribution, duplicate
scope, and suitability of this incremental formalization as formal evidence.
No catalog eligibility flag or prize decision should be inferred from this PR.

## Draft status

This file is a prepared description, not evidence that a PR has been submitted.
The official submission path and prize recognition of this scope are unconfirmed.
