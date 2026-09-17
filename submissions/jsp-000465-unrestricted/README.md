# JSP-000465: the unrestricted compactness question

This submission formalizes the known Lefkowitz--Wigderson counterexample to the **unrestricted** Erdős--Simonovits compactness question (Erdős problem 575).

**Scope matters:** the current JSP-000465 record cites a counterexample consisting of connected bipartite graphs. The present construction has a disconnected member and both members are forests. It does not formalize that connected result or a version excluding forests. No change to the catalog's Lean-proof, eligibility, or award fields is requested. Maintainers may treat this as related formal evidence or separate the unrestricted statement from the connected result.

## Statement and correspondence

For a finite family of finite simple graphs containing a bipartite member, the unrestricted question asks whether some bipartite member has extremal number at most a constant times the family's extremal number.

The Lean file uses mathlib's `SimpleGraph`, `SimpleGraph.Copy`, `SimpleGraph.Free`, `SimpleGraph.IsBipartite`, and `SimpleGraph.extremalNumber`. Copies are injective graph homomorphisms: containment is ordinary subgraph containment, not induced containment. The family extremal number is defined by the analogous maximum over all labelled graphs on `Fin n` that avoid every member. Finite indexed families allow members of different orders.

`Erdos575.not_unrestrictedCompactness` negates the universally quantified assertion, even when the proposed bound is allowed to start at an arbitrary threshold. Its quantitative lemma, `Erdos575.no_member_bound`, states that for each of the two members, every nonnegative real constant `C`, and every threshold `N`, there exists `n >= N` such that

```text
C * ex(n; family) < ex(n; member).
```

There are no assumptions about unproved extremal estimates in the theorem.

## Proof outline

The two forbidden graphs are the two-edge star on three vertices and two disjoint edges on four vertices. Both are explicitly two-colored. Any two distinct edges either share an endpoint or are disjoint, so a graph avoiding both has at most one edge. On `2m` vertices, a matching avoids the two-edge star and has at least `m` edges; a star avoids two disjoint edges and has at least `m` edges for `m >= 1`. Injective maps into the finite edge sets establish these lower bounds. Taking `m` larger than the proposed constant and threshold disproves every eventual bound.

## Attribution and duplicate search

The mathematical counterexample was pointed out by **Jordan Lefkowitz** and is recorded in **Yuval Wigderson**, [The Erdős--Simonovits compactness conjecture needs more assumptions](https://ywigderson.math.ethz.ch/math/static/Compactness.pdf). That note also explains why restrictions on forests matter. This submission does not claim a new mathematical solution or global priority for formalization.

Source context:

- [Erdős problem 575](https://www.erdosproblems.com/575).
- [JSP-000465 catalog entry](../../problems/catalog-0401-0500.md#JSP-000465).
- [The connected result cited by the catalog](https://cdn.openai.com/pdf/ten-proofs-oai.pdf), Chapter 10; not proved by this submission.

A bounded public search inspected `plby/lean-proofs`, `google-deepmind/formal-conjectures`, the Erdős problem status data, GitHub code search, and open prize-repository submissions. The two additional #575 files found were an empty proof block in `daedalus/alphaproof-nexus` and a statement ending in `sorry` in `ryantuck/erdos-ai`. This search is not a guarantee of global novelty. The present Lean proof was written in this session with Codex assistance; no text from those proof stubs was copied.

## Reproduce

The project is in [`lean/`](lean/), with Lean 4.34.0 and mathlib pinned to commit `5ed2965256430c3649e86755f9576b54eca72435`.

```sh
cd submissions/jsp-000465-unrestricted/lean
lake exe cache get Mathlib.Combinatorics.SimpleGraph.Extremal.Basic Mathlib.Combinatorics.SimpleGraph.Bipartite Mathlib.Algebra.Order.Archimedean.Real.Basic Mathlib.Tactic.FinCases Mathlib.Tactic.NormNum Mathlib.Tactic.Tauto
lake build
python verify.py
```

The final command invokes `lake env lean Erdos575.lean`, fails on compilation errors, and checks the transitive axiom list against the three standard axioms. See [verification.md](verification.md) for the local results. Repository validation checks record consistency, not mathematical truth or prize acceptance.

## License and submission status

The new Lean source is offered under the MIT license included in the Lean project. mathlib and its dependencies retain their own licenses. This prose is offered under CC BY 4.0, consistent with the repository's content convention.

This is a public proof contribution for review. It records no award decision, independent verifier endorsement, or confirmed recipient profile.
