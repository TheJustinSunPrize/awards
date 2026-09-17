# Public verification receipt: JSP-000749

This receipt reports contributor-run verification of the stated upper-bound component, not organizer approval, independent human certification, global priority or prize eligibility.

## Source and exact observed run

- Proof repository: `ketianzhang1-lang/jsp-000301-lean`.
- Immutable proof commit: **`fddb23254d8b8530ce2bac9b9e50304557349512`**.
- Project directory: `projects/jsp-000749`.
- [Successful workflow run 35173096659](https://github.com/ketianzhang1-lang/jsp-000301-lean/actions/runs/35173096659), job **105048771559**, public run number 1.
- Run started **2026-09-17 02:05:55 UTC** (September 16 in US Eastern time).
- Lean **4.34.0**, compiler `293d5d0c0c3f3dded4688b3ccd6a33939ac5102b`.
- Mathlib **`5ed2965256430c3649e86755f9576b54eca72435`**; all nine resolved dependency revisions are committed and checked against their actual Git checkouts.

The fifteen files in `SOURCE_SHA256SUMS` match the successful public source archive and the previously delivered local proof package byte-for-byte. Publication did not change the theorem statements or Lean proofs. Documentation is outside that source manifest and is separately tracked in Git. Seven compact log/configuration files in `evidence/public/` are byte-identical to the public artifact; verify them using `EVIDENCE_SHA256SUMS`.

## Actual results

`lake build --wfail` completed successfully: **3,099 total dependency/build jobs**, including compilation of all six project modules. This is not a claim of 3,099 new proofs.

All six `lake env leanchecker` invocations exited successfully: Counting, Estimates, Construction, Main, the root module, and StatementCheck. The individual replay logs are empty because these successful commands emit no output; they are retained in the full artifact. This is a same-kernel implementation replay, not an independently implemented checker and not a fresh full-library reconstruction.

All **twelve** named target axiom closures contain only `propext`, `Classical.choice`, and `Quot.sound`. Eleven implementation declarations are printed by Audit.lean and the plain endpoint is printed by StatementCheck.lean. Exact reports and theorem types are in the submitted logs. No admitted proof, native-evaluation axiom or compiler-trust axiom is permitted.

The deliberately false arithmetic proposition `1=0` was rejected with the message that `decide` proved it false. Finite diagnostics passed 59 exact binomial bounds, 147,677 colour-class-size checks and small graph-colouring semantic tests. These finite diagnostics are not dependencies of the universal Lean proofs.

**NaNoda returned `Checked 14502 declarations with no errors`.** All twelve named target closures were exported, including the explicit plain-quantifier endpoint. The checker is pinned to `ammkrn/nanoda_lib@4c544ed4099c8227f07d5de77ad1e69fb0740a27`, and the same-toolchain exporter to `leanprover/lean4export@6cea97789dc088ea47fcea15692db85685aedac5`. The configuration permits only the standard three axioms and sets `unpermitted_axiom_hard_error: true`. Definition/statement pretty-printing completed; the actual printed statements were inspected. NaNoda is an independent checker implementation, but operated here by the same contributor, not an independent human verifier.

## Evidence integrity and retention

[Artifact 10477044264](https://github.com/ketianzhang1-lang/jsp-000301-lean/actions/runs/35173096659/artifacts/10477044264), name `jsp-000749-verification`.

- Downloaded ZIP bytes: **9,960,144**.
- ZIP SHA-256: **`d2c62540c3ec3007a0d5dd94a8e8dba24f116f54bba0d135c04a3a78270fd002`**.
- Source archive SHA-256: `4770ea339f7ae3396a5628eab2487d03d50bbf486aa3729987be9108e98f8d74`.
- Compressed checker export SHA-256: `4dc89f2e3429cf5ac6f69093a394f57fdbf15781714c1c62a45d871f5099091b`.
- Checker configuration SHA-256: `1b7d3cfe3e62d532748455b2d074347b6c3ed736765246daa02a36b38c6067aa`.

The ZIP was downloaded and its digest checked before inspecting the logs, archive, target statements and source identity. GitHub reports artifact expiry at **2026-12-16 02:05:55 UTC**. A backup is supplied to the contributor. This is finite-retention GitHub evidence, not independently guaranteed permanent archival. The public proof remains pinned by Git commit.

## Boundaries and repository checks

Cached compiled Mathlib and network access were used. No network-disabled rebuild of all dependencies, official minimum-safe-version approval, designated verification, independent human signature, permanent external archive, recipient confirmation or award is asserted. The local preliminary receipt and the initial source README predate this public run and must not be substituted for its actual results.

This package requests review only of `m(n)<=4*n^2*2^n` for every n>=2, with positivity, attainment and exact-three-colour existence. It does not solve the original precise-growth question. Official repository schema/tests are separate structural checks and do not execute or certify this Lean proof. The exact-package preflight result, once completed, is linked in the PR description; it is not inferred from older submissions.
