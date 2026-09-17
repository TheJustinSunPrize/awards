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

The GitHub run requests compilation, bundled leanchecker, NaNoda and strict project axiom auditing. At packet preparation it was running; its final conclusion must be checked at the linked run. The workflow uses pinned Lean action, exporter and NaNoda revisions.

The local environment needed an alias for its own process-executable filesystem lookup, described in [provenance](PROVENANCE.md). No proof or kernel code was modified. Bundled leanchecker is a separate replay using the Lean implementation; NaNoda uses a separate implementation. Neither is a human statement-fidelity review or Prize approval. Reviewers must assess the mathematical scope and provenance separately.
