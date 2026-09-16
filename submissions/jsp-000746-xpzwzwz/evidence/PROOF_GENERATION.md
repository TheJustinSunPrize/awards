# Explicit propositional proof generation

The repository includes the exact DIMACS instance `core.cnf`, a textual LRAT
trace `core.lrat`, and the meaning of all input clauses in `schur_core.json`.

The 153 variables enumerate pairs `1 ≤ a < b ≤ 18` lexicographically, starting
at index 1. A positive literal denotes adjacency. A triangle supplies three
negative literals. A distinct Schur triple supplies three positive literals.
The retained core has 602 clauses. It was found from the full instance by
greedy clause deletion in a pseudorandom order seeded with 746.

The raw trace was generated with CaDiCaL bundled with Lean 4.34.0:

```sh
cadical --lrat --no-binary evidence/core.cnf evidence/core.lrat
```

Exit code 20 denotes UNSAT. This command is optional and not part of a Lean
build. The checked-in trace is sufficient to regenerate the proof source:

```sh
python3 scripts/generate_rup.py
lake build
```

The generator follows dependencies backward from the final empty clause,
retaining 9,697 derived clauses, then emits 39 independent proof fragments.
It only accepts positive, previously defined RUP hint IDs, rejecting RAT
steps. Deletion hints are irrelevant for the emitted persistent proof terms.

A clause `L₁ ∨ … ∨ Lₖ` is represented as its contradiction form:
`¬L₁ → … → ¬Lₖ → False`, simplifying double-negated atoms classically.
For each RUP step, the generator assumes that every literal of the target
clause is false, performs the indicated unit propagations, and derives the
conflict. Each propagation becomes an explicit Lean lambda or application;
positive atoms can use `Classical.byContradiction`. The final theorem applies
these fragment lemmas in dependency order.

Lean checks all terms. In particular, a bug in hint parsing, sign handling,
clause numbering, source generation, or SAT solving cannot silently become a
new assumption in the main theorem. The source-level statement correspondence
still requires human review; it is explained in `../STATEMENT.md` and implemented
by `Basic.lean` and `Main.lean`.
