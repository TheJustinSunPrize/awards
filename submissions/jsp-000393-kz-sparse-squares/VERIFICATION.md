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

## Completed CI result

The linked run completed successfully on 2026-09-17 at 01:04:23 UTC for the exact proof commit above. Job `105034651595` recorded:

- `lake build --wfail`: success; 3,093 build jobs completed or replayed.
- Bundled Lean kernel replay of `JSP000393`: success.
- Project axiom audit: all 41 declarations under `JSP000393` passed the allowlist `propext`, `Classical.choice`, `Quot.sound`. The two main theorems also printed exactly those axioms.
- NaNoda: 392,622 declarations checked, zero typechecker errors, and one pretty-printer error (`Unable to print axioms`). Its configuration allowed `Lean.trustCompiler` and set `unpermitted_axiom_hard_error` to `false`. This was **not a strict NaNoda axiom-allowlist run**. The separate project axiom audit described above was strict and passed.

The workflow uses Lean action `50fcf42d2e460296f1a34b402e990d1b24f8b596`, exporter `6cea97789dc088ea47fcea15692db85685aedac5`, and NaNoda `4c544ed4099c8227f07d5de77ad1e69fb0740a27`.

These successful checks establish verification evidence for this packet's scoped statements. They do not make the whole catalog problem solved by this implementation or establish prize eligibility. The official problem-index conventions require the full mathematical problem and a corresponding formal proof; a partial component does not make a combined record eligible.

## Archived evidence

The actual CI output from the build through the completed axiom audit is preserved as an unmodified contiguous excerpt, with surrounding setup and cleanup omitted:

- [External pinned log](https://github.com/ketianzhang1-lang/jsp-000301-lean/blob/edbb663aac14387805a9986b257d39e90d8f5cd2/evidence/ci-verification-excerpt.log), also copied in [this packet](evidence/ci-verification-excerpt.log).
- Archive identifier: proof-repository commit `edbb663aac14387805a9986b257d39e90d8f5cd2`, path `evidence/ci-verification-excerpt.log`.
- Log size: 14,754 bytes. SHA-256: `858e383d3f86444935afe8f1d074b426b395ba62b9583bda61e0117029dae854`.
- [Machine-readable CI result and limits](evidence/ci-verification.json).

GitHub Actions artifact `10475493496` contains only the resolved dependency manifest. It is 846 bytes, SHA-256 `7556ececd5d4e8181ddb422d7c44dc144a5e7c68b61fdd2c5dfeb0e7a1ea380a`, with advertised expiry 2026-12-16. It is not a proof-export archive. The pinned log above preserves the verification results separately. The full NaNoda export was not retained by this workflow and must be regenerated for reproduction.

These are contributor-run checks using a cached Mathlib environment. No independent human certification, offline rebuild of every dependency, guaranteed permanent hosting, or organizer acceptance is claimed.

## Submission repository checks

All 22 official validator tests passed, along with `manage.py validate`, `links`, `build`, `check`, and `history --base f4e7173d89dfe91022a185427d63452c8ffbf6ae`. Generated data remained unchanged. All four proof/dependency files in `SOURCE.json` were fetched from the pinned proof commit and matched the recorded byte counts and SHA-256 hashes. The external CI-log archive was read back successfully. The raw log intentionally retains the original whitespace.

Only this submission packet is added to the official base; no candidate, award, recipient profile, catalog flag, validator, or schema is changed. These repository checks validate packaging and references, not eligibility or payment.

The local environment needed an alias for its own process-executable filesystem lookup, described in [provenance](PROVENANCE.md). No proof or kernel code was modified. Bundled leanchecker is a separate replay using the Lean implementation; NaNoda uses a separate implementation. Neither is a human statement-fidelity review or Prize approval. Reviewers must assess the mathematical scope and provenance separately.
