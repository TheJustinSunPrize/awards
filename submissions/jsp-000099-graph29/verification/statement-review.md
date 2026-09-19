# Statement and evidence review

This is an internal source review by AI assistants, not a review by an official prize verifier or by the mathematical authors.

- The final statement uses Mathlib's `SimpleGraph`, induced graphs, and regular degree, rather than a bespoke substitute for graph regularity.
- It quantifies over every vertex subset of size at least seven, not just subsets of size seven, and includes common degree zero.
- The concrete graph is undirected and loopless. Its encoded adjacency lists agree with the separately decoded public graph6 witness.
- The generic certificate theorem proves the validity of all pruning and branching rules. A forged state checkpoint is rejected by equality tests whose relationship to the proved checker is itself established in Lean.
- No original mathematical discovery is claimed for the graph or finite lower bound; these are attributed to Dyson and McKay.
- The existential theorem is a concrete witness for the known bound. It does not define and prove a theorem about a formal Ramsey-minimum constant, improve the bound, prove equality, or settle the asymptotic problem.
- No completed matching witness formalization was found in the bounded prior-art search. This is not an exhaustive priority claim.
- Local checking uses pinned compiled dependency objects. Filesystem isolation and rebuilding every dependency from source are not claimed. The organizing body retains responsibility for designated verification and award adjudication.
