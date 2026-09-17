# JSP-000660: balanced subgraphs in dense graphs

## English

This submission provides a source-faithful Lean formalization of the negative
answer to JSP-000660, whose catalogue wording is:

> Does every dense graph contain a sufficiently dense subgraph whose vertex
degrees are comparable?

The exact quantified assertion is defined as `JSP000660.target_statement`.
The theorem `JSP000660.not_jsp_000660` proves its negation, and
`JSP000660.answer_false_iff` packages the negative answer as
`False ↔ target_statement`. The proof uses an explicit complete bipartite
counterexample and does not replace the quantified statement with a special
finite instance.

This is a formalization submission, not a claim of mathematical discovery, an
award, eligibility, recipient confirmation, or independent review. The proposed
recipient placeholder is `RECIPIENT-JSP-000660-A` pending the review required by
the public prize process.

## Provenance and attribution

- Catalogue entry: [JSP-000660](https://github.com/TheJustinSunPrize/awards/blob/f4e7173d89dfe91022a185427d63452c8ffbf6ae/problems/catalog-0601-0700.md#JSP-000660).
- The source result is Noga Alon's [Problems and results in extremal
  combinatorics--II](https://doi.org/10.1016/j.disc.2007.08.090), *Discrete
  Mathematics* 308 (2008), 4460--4472, Section 2 and Proposition 2.1.
- The exact formal statement is the public [Formal Conjectures Erdős Problem
  1077 source](https://github.com/google-deepmind/formal-conjectures/blob/40e7c98697de6f66b8cbdbf641749ab39ed9c152/FormalConjectures/ErdosProblems/1077.lean).
- The retained Lean proof is the immutable public source at [plby/lean-proofs
  commit `dfe2d78128b493c572cf525b1b8edf4897fb7664`](https://github.com/plby/lean-proofs/blob/dfe2d78128b493c572cf525b1b8edf4897fb7664/src/latest/ErdosProblems/Erdos1077.lean).
- The mathematical result is attributed in the source record to the
  Erdős--Simonovits question and Alon's negative construction. The copied proof
  source retains its public authorship header (Codex and GPT-5.6 Sol, with the
  Formal Conjectures statement authors). The JSP wrapper and packaging were
  prepared with OpenAI Codex assistance.

The source proof is released under Apache License 2.0; the license text is
included as `LICENSE-APACHE-2.0.txt`.

## Reproduction

With Lean `4.33.1` and the pinned Mathlib revision in `lake-manifest.json`:

```sh
./verify.sh
```

The script checks forbidden proof escapes, builds both modules, and prints the
Lean axiom reports. Generated `.lake/` files are build products and are not part
of this submission.
