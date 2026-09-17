# Reproduction and verification evidence

Proof commit: `a337720331a34599114a9d4669d6518d5e608f6f` in `ketianzhang1-lang/jsp-000301-lean`.

Lean: `leanprover/lean4:v4.34.0`. Mathlib: `5ed2965256430c3649e86755f9576b54eca72435`. All dependencies are locked by the committed `lake-manifest.json`.

```sh
git clone https://github.com/ketianzhang1-lang/jsp-000301-lean.git
cd jsp-000301-lean
git checkout a337720331a34599114a9d4669d6518d5e608f6f
lake exe cache get Mathlib.Algebra.Polynomial.Expand Mathlib.Tactic
lake build --wfail
lake env leanchecker -v JSP000393
```

Do not regenerate the dependency manifest with `lake update`.

The local build completed with exit code 0, as did bundled leanchecker replay of `JSP000393`. Both main theorem axiom checks reported only `propext`, `Classical.choice`, and `Quot.sound`. The proof contains no `sorry`, `admit`, `native_decide`, or added axiom.

- [Build output](https://github.com/ketianzhang1-lang/jsp-000301-lean/blob/a337720331a34599114a9d4669d6518d5e608f6f/evidence/build.log)
- [Bundled leanchecker output](https://github.com/ketianzhang1-lang/jsp-000301-lean/blob/a337720331a34599114a9d4669d6518d5e608f6f/evidence/leanchecker.log)
- [Local evidence manifest](https://github.com/ketianzhang1-lang/jsp-000301-lean/blob/a337720331a34599114a9d4669d6518d5e608f6f/evidence/local-verification.json)
- [Clean GitHub verification run](https://github.com/ketianzhang1-lang/jsp-000301-lean/actions/runs/35168428244)

The GitHub run completed successfully on 17 September 2026 for the pinned proof commit. It passed compilation, bundled leanchecker, NaNoda and strict project axiom auditing. NaNoda checked 392,622 declarations with zero typechecker errors. It reported one pretty-printer error, `Unable to print axioms`; this was not a typechecking failure. The separate strict axiom audit checked all 41 declarations under `JSP000393` and found only the allowlisted `propext`, `Classical.choice`, and `Quot.sound`. The workflow uses pinned Lean action, exporter and NaNoda revisions.

These successful checks establish verification evidence for this packet's scoped statements. They do not make the whole catalog problem solved by this implementation or establish prize eligibility. The official problem-index conventions require the full mathematical problem and a corresponding formal proof; a partial component does not make a combined record eligible.

The local environment needed an alias for its own process-executable filesystem lookup, described in [provenance](PROVENANCE.md). No proof or kernel code was modified. Bundled leanchecker is a separate replay using the Lean implementation; NaNoda uses a separate implementation. Neither is a human statement-fidelity review or Prize approval. Reviewers must assess the mathematical scope and provenance separately.
