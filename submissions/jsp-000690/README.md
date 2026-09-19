# JSP-000690 — Lean formalization

This submission formalizes a positive answer to **JSP-000690 (Erdős problem 834)**: a finite simple 3-uniform, critically 3-chromatic hypergraph with minimum degree at least 7 exists. The directory `submissions/jsp-000690/` is proposed as the review location for this contribution. Acceptance, eligibility, and any award remain subject to the organizers' review and applicable rules.

The mathematical construction is due to **Ruiliang Li**, *On an Erdős–Lovász problem: 3-critical 3-graphs of minimum degree 7*, [arXiv:2512.24850v1](https://arxiv.org/html/2512.24850v1), Theorem 1.2 and Section 4, equation (5).

**The Lean formalization was jointly completed by [superpilot69](https://github.com/superpilot69) and ChatGPT 6 Astra.** The submitter's X/Twitter account is [@wofuhuola](https://x.com/wofuhuola). See [ATTRIBUTION.md](ATTRIBUTION.md) for attribution and contribution details.

## Proven statement

The unconditional main theorem, `JSP690.jsp_000690`, is in [JSP690/Result.lean](JSP690/Result.lean). Its strengthened version, `JSP690.jsp_000690_nine_vertices`, proves the existence of a hypergraph with all of these properties:

- Exactly 9 vertices and 22 distinct edges, each containing exactly 3 distinct vertices.
- Chromatic number exactly 3: a proper 3-coloring exists, and no proper coloring with any number of colors below 3 exists.
- Every proper subhypergraph, obtained by deleting edges, vertices, or both, admits a proper 2-coloring on its own vertex set.
- Every vertex has degree at least 7, and some vertex has degree exactly 7.

Here a proper coloring means that every edge contains two vertices of different colors: it is the usual weak hypergraph coloring. Criticality is **chromatic criticality**. Deleting a vertex removes all incident edges; it does not shorten those edges.

Vertices are `Fin n`, and edges are `BitVec n`, representing unordered vertex subsets. The hypergraph is an edge list proved to have no duplicates. [JSP690/Encoding.lean](JSP690/Encoding.lean) connects this encoding to vertex-set equality. [JSP690/Subgraph.lean](JSP690/Subgraph.lean) defines genuine proper subhypergraphs and proves the general bridge from single-edge and single-vertex deletion certificates to colorability of every proper subhypergraph on its literal vertex subtype.

## Reproduce the verification

The project uses **Lean 4.34.0 and its bundled Std library**, with no Mathlib or third-party package dependency. The version is pinned in [lean-toolchain](lean-toolchain). Have Python 3 and Lake available on `PATH`, with the pinned Lean toolchain installed or managed by elan. From the repository root, run:

```sh
cd submissions/jsp-000690
python3 scripts/verify.py --clean
```

If Lake is outside `PATH`, supply its executable explicitly:

```sh
python3 scripts/verify.py --clean --lake /path/to/lean-4.34.0/bin/lake
```

The [verification script](scripts/verify.py) checks the Lean version and compiler commit, cleans and rebuilds the package, runs [Audit.lean](Audit.lean), checks the nine audited theorems' axiom dependencies, and records source SHA-256 hashes. It uses only Python's standard library.

The checked source contains no `sorry`, admitted proof, or added mathematical axiom. The recorded transitive axiom dependencies of all nine audited theorems are only Lean's `propext` and `Quot.sound`. Finite certificates are checked by Lean; external searches and the paper's arguments are not assumed as proof premises.

Review the [verification report](verification/result.json) and [build and axiom-audit log](verification/build-and-axioms.log) for the recorded result. Running the command above regenerates both files.

## Review scope

This contribution is the Lean formalization of Li's known construction and its required properties. The main theorem and the definitions it uses are provided for the organizers to assess against JSP-000690 and the prize's submission requirements.
