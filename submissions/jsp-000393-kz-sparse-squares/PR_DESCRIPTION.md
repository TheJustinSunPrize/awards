## Contribution and scope

Submit the known Coppersmith–Davenport sparse-square construction for **scoped formalization review**. For every natural k, the Lean proof gives integer polynomials F_k with exactly 13^k nonzero coefficients and exactly 12^k nonzero coefficients in F_k². It also proves that, for every natural M, some P satisfies M*T(P²) < T(P).

**This is a constructive component, not a proof of the full Schinzel lower-bound theorem or a claim of new mathematics.** Existing full-result registration [#44](https://github.com/TheJustinSunPrize/awards/issues/44) and its contributors are acknowledged.

## Source and actual checks

[Submission packet](https://github.com/ketianzhang1-lang/awards/tree/2f6a4ab4bf4fa8c4c483609cbd7b27997ec71e8d/submissions/jsp-000393-kz-sparse-squares) contains exact statements, attribution, reproduction, source hashes and verification limits.

Proof commit: `a337720331a34599114a9d4669d6518d5e608f6f`.

[Proof CI](https://github.com/ketianzhang1-lang/jsp-000301-lean/actions/runs/35168428244) succeeded: Lean build with warnings as errors, bundled kernel replay, and strict three-axiom audit of all 41 project declarations. NaNoda checked 392,622 declarations without typechecker errors but reported one pretty-printer error; its own axiom configuration was not strict. These limits are disclosed in VERIFICATION.md.

[Archived CI excerpt](https://github.com/ketianzhang1-lang/jsp-000301-lean/blob/edbb663aac14387805a9986b257d39e90d8f5cd2/evidence/ci-verification-excerpt.log): 14,754 bytes; SHA-256 `858e383d3f86444935afe8f1d074b426b395ba62b9583bda61e0117029dae854`.

All 22 official validator tests and validate/links/build/check/history passed locally. Four pinned source/dependency files matched their recorded hashes. Generated data is unchanged.

## Requested review

Please assess scope, fidelity, overlap, attribution and whether this additional formalization merits recognition. Mathematical credit remains with Coppersmith and Davenport and earlier cited contributors. OpenAI Codex assistance is disclosed.

Proposed recipient: `RECIPIENT-JSP-000393-KZ-A`; confirmation pending. This is contributor-run verification, not independent human or organizer approval. No catalog eligibility change, candidate record, award or payment entitlement is asserted.
