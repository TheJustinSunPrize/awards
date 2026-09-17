# Verification receipt: 2026-09-17

## Verified source

- Repository: https://github.com/ketianzhang1-lang/jsp-000301-lean
- Exact proof commit: `c32d8195dc69e19d9bcf96987543f306c71749f2`.
- Project directory: `projects/jsp-000388`.
- [Passing CI run 35168280490](https://github.com/ketianzhang1-lang/jsp-000301-lean/actions/runs/35168280490).
- [Pinned workflow](https://github.com/ketianzhang1-lang/jsp-000301-lean/blob/c32d8195dc69e19d9bcf96987543f306c71749f2/.github/workflows/jsp-000388.yml).
- All twelve files of the proof project are copied unchanged into this package;
  submission and verification documents are additional files.

## Observed results

| Check | Result |
| --- | --- |
| `lake build --wfail` | Passed, 3,093 jobs |
| Bundled `leanchecker JSP000388` | Passed |
| Six target axiom audits | Passed |
| Actual dependency revisions versus lockfile | Passed |
| Invalid `1 = 0` negative-control gate | Rejected, as required |
| Strict-allowlist NaNoda | 13,616 declarations checked, no errors |

The six audited targets are in `Audit.lean`. The normalized difference lemma
uses `propext` and `Quot.sound`. The five remaining audited targets use only
`propext`, `Classical.choice`, and `Quot.sound`. No `sorryAx`, custom solution
axiom, compiler-trust axiom or native-evaluation axiom is permitted.

The bundled replay uses the same Lean kernel implementation. NaNoda is the
separate checker used here, with the permitted axiom list explicitly fixed to
the three standard axioms above and unpermitted axioms configured as hard
errors. A successful proof check must still be accompanied by substantive
statement-fidelity and attribution review.

Lean: `leanprover/lean4:v4.34.0`. Mathlib:
`5ed2965256430c3649e86755f9576b54eca72435`. Every transitive package revision is
in the included `lake-manifest.json`. Exporter:
`leanprover/lean4export@6cea97789dc088ea47fcea15692db85685aedac5`.
NaNoda: `ammkrn/nanoda_lib@4c544ed4099c8227f07d5de77ad1e69fb0740a27`.
The included scripts pin and check these revisions.

## Evidence artifact

- ID: `10476380822`, name `jsp-000388-evidence`.
- Size: `8905823` bytes.
- SHA-256: `dd840c3a9c9cbed8dd45683eb03b908f6b385216303fb2c83a9492f6dc3b5bb1`.
- [Artifact download](https://github.com/ketianzhang1-lang/jsp-000301-lean/actions/runs/35168280490/artifacts/10476380822).
- Reported expiry: `2026-12-16T00:52:09Z`.

The artifact contains the tested source archive, build/replay/audit logs,
negative-control output, exported dependency closure, NaNoda configuration and
output, and hashes. Metadata is preserved in `verification/artifact.json` and
an exact selection of CI output lines in `verification/ci-excerpt.log`.
The full artifact digest and size were reported by GitHub; a separate local
binary download and independent rehash are not claimed. GitHub Actions has
finite retention and is not a permanent independent archive. The compact
source and receipt are preserved in the submitted Git repository.

## Reproduction and limits

Check out the exact commit and enter the project directory. Keep the committed
manifest; do not run `lake update` for this reproduction.

```sh
lake exe cache get
bash scripts/verify.sh
bash scripts/verify_nanoda.sh
```

The observed runner was GitHub-hosted `ubuntu-24.04`; network access and cached
Mathlib artifacts were used. The run checked the target module and exported
dependency closure, not a source rebuild of every imported standard-library
and Mathlib module. No offline-isolated reconstruction, independent human
sign-off, official minimum-safe-version approval, prize verification, award,
or payment decision is asserted.

An earlier development run failed the warning-as-error gate because
`push_neg` was deprecated. It was replaced with `push Not`; only the passing
commit above is offered as the verified source.
