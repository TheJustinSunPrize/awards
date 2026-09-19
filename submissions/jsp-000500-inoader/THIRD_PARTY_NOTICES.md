# Sources and licenses

JSP500/Brooks.lean adapts the generic theorem from
[nwinter/erdos-617-r5](https://github.com/nwinter/erdos-617-r5/blob/32f1bfe6759299ef3a1c6e8b4c3c637528a9881b/lean617/Lean617/R6/Brooks.lean),
commit `32f1bfe6759299ef3a1c6e8b4c3c637528a9881b`, Apache-2.0.
The source's formalization follows Mariusz Zając, *A short proof of Brooks’ theorem*, arXiv:1805.11176.
Imports were reduced and the fixed r=6 application removed; any compatibility edits are local.

The mathematical r=7 roadmap is Robert Sneiderman’s preprint in
[Robby955/erdos-617-fixed-cases](https://github.com/Robby955/erdos-617-fixed-cases/blob/fb628c8cf5ea7173c245c9542b69d72c11cce4a4/r7-r8/main.tex).
This preprint supplies the target and a mathematical roadmap. The present Lean proof replaces the finite exhaustive step by direct counting and finishes with unconditional edge floors and vertex deletion.
The weighted light-edge counting proof in this project replaces the finite exhaustive lemma with a direct proof.

JSP500/Vendor/*.lean are adapted from the same pinned nwinter repository, from matching filenames under lean617/Lean617/. Only their generic graph-theoretic exports are intended for use here. Original conditional structures are preserved; unconditional exports must pass a separate axiom audit.


Generic edge-accounting and clique-edge counting helpers in
`JSP500/GraphAccounting.lean` and `JSP500/CliquePeeling.lean` also adapt elementary
helpers from the pinned nwinter repository. Local changes provide the finite
induced-graph and instance interfaces used here. The fixed r=7 modules connect
the weighted counting argument, colored core bounds, edge floors, clique
deletion, and final contradiction. Mathlib retains its own Apache-2.0 license.

The adapted sources' Apache-2.0 license is included at
[LICENSES/nwinter-Apache-2.0.txt](LICENSES/nwinter-Apache-2.0.txt).
The submission's code is distributed under [Apache-2.0](LICENSE), with these
source notices preserved. Preparation and proof development used OpenAI Codex
assistance under the public applicant account `inoader`.
