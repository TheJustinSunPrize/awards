# Verification receipt: JSP-000883

## Immutable proof and completed cloud run

- Proof commit: `d951a581d98d209c168ec4066af97df52a7a9498`.
- [Run 35174825512](https://github.com/ketianzhang1-lang/jsp-000301-lean/actions/runs/35174825512),
  job `105054087728`: completed successfully on 2026-09-17.
- Lean: `leanprover/lean4:v4.34.0`.
- Mathlib: `5ed2965256430c3649e86755f9576b54eca72435` (`v4.34.0`).
- Every dependency checkout was checked against its locked revision, and
  the manifest was checked for changes.

## Actual proof checks

| Check | Result |
| --- | --- |
| `lake build --wfail` | Passed; 3,095 build jobs |
| Bundled kernel replay | Passed for JSP000883, Compatibility and Audit |
| Nine target axiom audits | Passed; only propext, Classical.choice and Quot.sound |
| False-arithmetic negative control | Rejected as required |
| Independent NaNoda replay | 6,675 declarations checked with no errors |
| Strict NaNoda axiom allowlist | Enabled, with unpermitted axioms treated as errors |
| Source bytes against published Git blobs | All 11 submitted proof/workflow files matched |
| Source bytes against tested source archive | All 10 proof-project files matched |

The independently exported dependency closure includes the explicit infinite
family, the bounds and both compatibility theorems. The nine axiom reports
include the product identity, modular obstruction and original-shape Monier
theorem. Actual compact logs and printed statements are retained in `evidence/`.

The main proof has no `sorry`, custom axiom, `admit`, or compiler-trust
verification shortcut. The compatibility module imports only the proved
project, not the original conjecture file with placeholders.

## Downloaded artifact

[Full CI artifact 10478082980](https://github.com/ketianzhang1-lang/jsp-000301-lean/actions/runs/35174825512/artifacts/10478082980)
was downloaded and checked against GitHub's metadata:

- Size: **4,046,754 bytes**.
- SHA-256: `4c8f827bc74dfdaa72dfa2f75e28b21d28db7954195703033e658cb1218755b1`.
- Scheduled expiration: **2026-12-16 02:32:45 UTC**.

`evidence/artifact-receipt.json` records the comparison. Original compact
logs are copied without rewriting. The compressed proof export and tested
source archive remain in the full artifact. The checksums for those files
are retained for use after downloading that artifact; they are not a claim
that those large files are included in this compact directory.

## Repository package checks

The exact package is checked against official repository base
`f4e7173d89dfe91022a185427d63452c8ffbf6ae`:

- All **22 official repository tests** passed.
- `manage.py validate`, `links`, `build`, `check`, and `history --base`
  all passed.
- Existing records and generated indexes were unchanged.
- The final diff contains only the new `docs/submissions/jsp-000883-kz/`
  directory. Source checksums were rechecked after copying.

The actual outputs and command receipt are retained as
`evidence/repository-*.log` and `evidence/preflight.json`. English prose and
retained mathematical symbols were checked for unintended Chinese text.

## Scope and limitations

This proves the complete known Monier factorial-bound component and an
explicit infinite family. It does not prove Cambie's stronger bound or solve
the open improvement problem. Original mathematical and statement authors
are credited in `README.md` and `PROOF.md`.

Official compiled Mathlib caches were used. Bundled `leanchecker` uses the
same kernel implementation; NaNoda is an independent implementation. No
whole-library source rebuild, independent human review, permanent external
archive, organizer certification or award eligibility is claimed.

The hosted runner emitted Node.js action deprecation notices. These were
workflow infrastructure notices; the Lean build with `--wfail` and all proof
checks succeeded. The raw printed-statement file retains its trailing blank
line, as emitted by the checker.
