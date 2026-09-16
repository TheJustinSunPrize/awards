# JSP-000078 / Erdős 58: arbitrary graphs

This submission extends the existing finite-graph Lean proof of Gyárfás's theorem to arbitrary vertex types. The catalog entry is [JSP-000078](../../problems/catalog-0001-0100.md#JSP-000078). The full statement is `Jsp000078.erdos_58` in [General.lean](Jsp000078/General.lean).

For any simple graph $G$, any natural number $k$, and a finite set of odd simple-cycle lengths of cardinality at most $k$, it proves both:

- `G.chromaticNumber ≤ 2*k+2`;
- `G.chromaticNumber = 2*k+2` if and only if $G$ contains a not-necessarily-induced copy of $K_{2k+2}$.

There is no assumption that the vertex type is finite, countable, nonempty, or locally finite. The case $k=0$ is included.

## Contribution and attribution

**The mathematical theorem is due to András Gyárfás (1992), following a conjecture of Bollobás and Erdős.** The substantial finite formalization is existing work from [plby/lean-proofs](https://github.com/plby/lean-proofs/tree/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos58). Its published main-file header credits **Codex and GPT-5.6 Sol** as formal authors. Boris Alexeev published and maintains the source repository. All 35 needed source files are included unchanged, with their original notices, and are listed in [vendor-manifest.json](vendor-manifest.json).

The contribution submitted by **MaxwellLaw**, with **OpenAI Codex assistance**, is the general-graph extension, its definition bridge, and this reproducible package. It uses the classical de Bruijn–Erdős compactness principle through Mathlib's Rado selection lemma, formalized by **Bhavik Mehta**. Neither the finite proof nor the underlying mathematics is claimed as new work by this submitter.

The standard cycle-length definitions are an unchanged copy of the Formal Conjectures authors' [Circumference.lean](https://github.com/google-deepmind/formal-conjectures/blob/40e7c98697de6f66b8cbdbf641749ab39ed9c152/FormalConjecturesForMathlib/Combinatorics/SimpleGraph/Circumference.lean), relocated to [CycleLengths.lean](Jsp000078/CycleLengths.lean).

See [REFERENCES.md](REFERENCES.md) for mathematical references, immutable source links, and the exact reuse boundary. This is an extension submission for review, not a claim of first formalization of the finite result, an independent referee report, or an award decision.

## Proof and statement correspondence

[Compactness.lean](Jsp000078/Compactness.lean) constructs a global $n$-coloring from colorings of every finite induced subgraph. Rado selection gives a global function that agrees locally with one finite coloring; applying that property to the two endpoints of any edge proves properness.

[General.lean](Jsp000078/General.lean) applies the finite theorem to each induced subgraph. Odd-cycle lengths can only disappear when taking an induced subgraph, so the same cardinality bound holds. Compactness gives the upper bound. If the global graph has no $K_{2k+2}$, the finite theorem's equality characterization makes every finite induced subgraph $2k+1$-colorable. Compactness again gives a global $2k+1$-coloring, contradicting equality. Conversely, a copy of $K_{2k+2}$ forces the matching lower bound.

`Jsp000078.oddCycleLengths_eq` proves equality between the finite source's cycle-length set and the standard definition. `Jsp000078.erdos_58_encard` uses extended cardinality; the final `Jsp000078.erdos_58` retains the standard statement's separate finiteness and natural-cardinality hypotheses. Its statement matches the pinned [Formal Conjectures target](https://github.com/google-deepmind/formal-conjectures/blob/40e7c98697de6f66b8cbdbf641749ab39ed9c152/FormalConjectures/ErdosProblems/58.lean), with only the theorem namespace changed.

The 2021 strengthening involving consecutive odd lengths is not the theorem formalized here.

## Reproduction

Run from this directory with `elan` and Python 3 installed:

```sh
lake exe cache get
python3 verify.py
```

- Lean: `leanprover/lean4:v4.33.0`.
- Mathlib: `db584cd6d46c92f209a44c0f1c829460d327499d`.
- All transitive Lake dependencies are pinned in [lake-manifest.json](lake-manifest.json).
- [Audit.lean](Audit.lean) checks the exported signature and prints full transitive axiom dependencies for the finite core and new results.
- [verify.py](verify.py) runs the build, axiom audit, and batch kernel replay of all 39 mathematical modules, saving logs and a source-hashed summary under the logs directory.
- [VERIFICATION.md](VERIFICATION.md) records actual verification results and their limits.

New Lean code is released under [Apache 2.0](LICENSE). Vendored material retains its original notices; the published finite proof and standard-definition source identify Apache 2.0 as their license. Original prose follows the repository's [content license](../../LICENSE-CONTENT).
