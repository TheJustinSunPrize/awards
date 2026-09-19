# JSP-000766 / Erdős 922: arbitrary graphs

This package extends the existing finite-graph Lean proof of Folkman's theorem to arbitrary vertex types. The [catalog entry](../../problems/catalog-0701-0800.md#JSP-000766) asks whether a hereditary lower bound on independent sets forces a bound on the chromatic number.

For any simple graph `G` and natural number `k`, suppose that every finite vertex set `S` contains an independent subset `I` with

```text
I ⊆ S                  |S| ≤ 2|I| + k.
```

Then `G` admits a proper coloring with the palette `Fin (k + 2)`, and its Mathlib chromatic number is at most `k + 2`. There is no finiteness, countability, local-finiteness, decidability, or nonemptiness assumption on the vertex type. The case `k = 0` is included.

## Statement and proof

[General.lean](Jsp000766/General.lean) exports:

- `Jsp000766.erdos_922_colorable`: the global coloring.
- `Jsp000766.erdos_922`: the chromatic-number upper bound.
- `Jsp000766.finite_subgraphs_iff_finsets`: equivalence with the literal condition on every finite subgraph, allowing edge deletion.
- `Jsp000766.erdos_922_of_finite_subgraphs`: the coloring and bound from that literal hypothesis.

The inequality `|S| ≤ 2|I| + k` is the exact integral form of `|I| ≥ (|S| - k) / 2`. It introduces no floor, rounding, or natural-number division. In the subgraph formulation, an explicit finiteness hypothesis guards `H.verts.ncard`, so infinite sets are not silently assigned natural cardinality zero.

The local condition passes to every induced subgraph by mapping finite sets into the ambient vertex type and pulling back their independent witnesses. For each finite induced subgraph, the existing theorem `Erdos922.erdos_922` supplies a `(k + 2)`-coloring. [Compactness.lean](Jsp000766/Compactness.lean) applies Mathlib's Rado selection lemma to obtain a single global coloring.

## Attribution and contribution boundary

The mathematical theorem is due to **Jon H. Folkman (1970)**, answering Erdős and Hajnal. The substantial finite formalization is existing work from [plby/lean-proofs](https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos922.lean), whose published header credits **Codex / GPT-5.6 Sol** as formal authors. That source is retrieved unchanged from a fixed commit, with its full published header retained locally. Its SHA-256 and byte count are in [source-manifest.json](source-manifest.json).

The new contribution submitted by **MaxwellLaw**, with **OpenAI Codex assistance**, is the arbitrary-graph extension and equivalence of the finite-subgraph formulations. The compactness application is reused from MaxwellLaw's [JSP-000078 PR #130](https://github.com/TheJustinSunPrize/awards/pull/130), with only its namespace and provenance comment changed. It rests on the classical de Bruijn–Erdős theorem and Mathlib's Rado selection formalization by **Bhavik Mehta**. This package has no code dependency on PR #130 and can be reviewed and built independently.

The earlier finite-proof verification registered by **zifanersuotang** in [issue #19](https://github.com/TheJustinSunPrize/awards/issues/19) is credited. That record explicitly excludes the infinite extension. The checks published here were run for this package; they do not turn the submitter into an independent referee.

See [REFERENCES.md](REFERENCES.md) for full mathematical and software references, including the modern exposition by Bonamy and coauthors, immutable links, and the reuse boundary. No claim is made to the mathematical discovery, the existing finite proof, exclusive priority, or an award decision.

## Reproduction

Install `elan` and Python 3.9 or newer, then run from this directory:

```sh
python3 fetch_source.py
lake exe cache get
python3 verify.py
```

Lean is pinned to `leanprover/lean4:v4.33.0`, Mathlib to `db584cd6d46c92f209a44c0f1c829460d327499d`, and all transitive Lake dependencies are pinned in [lake-manifest.json](lake-manifest.json). No GitHub authentication is needed to fetch the public finite proof.

The source fetcher checks the pinned SHA-256 and byte count before saving anything. An existing mismatched source causes failure instead of being overwritten. Downloaded source, compiler output, and new verification logs are ignored by Git.

[Audit.lean](Audit.lean) prints the unrestricted theorem signatures and transitive axiom dependencies. [verify.py](verify.py) checks the source, compiles the package, audits all seven named results, and replays all declarations from the external finite proof and three package modules against a Mathlib-only environment. [VERIFICATION.md](VERIFICATION.md) records actual results, evidence, and verification limits.

## Licensing

New proof and supporting code are licensed under [Apache 2.0](LICENSE). Reused compactness code and verification utilities retain their notices and are credited in [REFERENCES.md](REFERENCES.md). Original prose follows the repository's [content license](../../LICENSE-CONTENT).

The external finite proof is **not redistributed or relicensed by this package**. The pinned source and [upstream license notice](https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/LICENSE) remain authoritative for that material. The fetcher retrieves it directly from its public source for local reproduction.
