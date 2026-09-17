# JSP-000250 verification receipt

## English

This receipt records contributor-run checks of the exact upper-bound
formalization. It is supporting evidence for review, with no independent
human certification, recipient confirmation, or award decision.

## Immutable inputs

- Source commit: `567770d9977669a0846c491d0822fda8dddf9011` in
  [ketianzhang1-lang/jsp-000301-lean](https://github.com/ketianzhang1-lang/jsp-000301-lean/tree/567770d9977669a0846c491d0822fda8dddf9011/projects/jsp-000250).
- Lean: `leanprover/lean4:v4.34.0`.
- Mathlib: `5ed2965256430c3649e86755f9576b54eca72435`.
  The [lockfile](lake-manifest.json) pins every dependency; the verification
  script compared the actual checked-out revisions to that file.
- Exporter: `leanprover/lean4export` at
  `6cea97789dc088ea47fcea15692db85685aedac5`.
- NaNoda: `ammkrn/nanoda_lib` at
  `4c544ed4099c8227f07d5de77ad1e69fb0740a27`, built with `cargo build --release --locked`.
- Exact [workflow](https://github.com/ketianzhang1-lang/jsp-000301-lean/blob/567770d9977669a0846c491d0822fda8dddf9011/.github/workflows/jsp-000250.yml).

## Observed checks

The public [workflow run 35168833566](https://github.com/ketianzhang1-lang/jsp-000301-lean/actions/runs/35168833566)
ran on a fresh GitHub-hosted Ubuntu 24.04 runner on 2026-09-17.
The completed run concluded `success`.

| Check | Observed result |
| --- | --- |
| `lake build --wfail` | Passed; warnings are errors |
| `lake env leanchecker JSP000250` | Passed |
| Eight `#print axioms` audits | Passed; every audited declaration depends only on a subset of `propext`, `Classical.choice`, `Quot.sound` |
| Source and dependency audit | No `sorry`, `admit`, added `axiom`, `native_decide` or `unsafe` in the proof module; every dependency revision matches the lockfile |
| False arithmetic negative control | `example : (1 : Nat) = 0 := by decide` was rejected |
| Independent NaNoda implementation | Passed: 32,060 declarations checked with no errors |

The eight exported and audited declarations are `prime_obstruction_split`,
`prime_not_representable`, `firstException_spec`,
`smaller_denominators_representable`, `log_lcm_bound`,
`prime_exception_upper_bound`, `firstException_upper_bound`, and
`firstException_isBigO`, all in the `JSP000250` namespace. The export contains
their dependency closure. NaNoda runs with a hard-error policy for every axiom
outside the three-standard-axiom allowlist. Definitions and theorem statements
are printed in the archived `nanoda-statements.txt`.

## Evidence locations and integrity

- Full Actions artifact: [10475792964](https://github.com/ketianzhang1-lang/jsp-000301-lean/actions/runs/35168833566/artifacts/10475792964), `jsp-000250-evidence`.
- ZIP size: `30595278` bytes.
- ZIP SHA-256: `ed229205dff7f877e3a63ff9007a1cf8a5ad0c1c63e49e01baabe1a84613cf74`.
- Current artifact retention deadline: `2026-12-16T01:00:25Z`.
- Compressed export: `30617188` bytes, SHA-256 `74c8d363400215dce021571627cbaca487f1b57a1b6df626ac7b030b239b3d08`.
- Tested source archive: `9066` bytes, SHA-256 `3d020b952d26d3db3ee8107370af27d48e88e19d15579185cd8b158779c84deb`.
- Checker configuration SHA-256: `f459dc30748d12457f7e12b41c6aa47ae1548bfa1617bea26fa233fbbbca9ff3`.

The ZIP digest was checked after download. The source archive was compared
byte for byte against the pinned project, and the internal export, source
archive and checker-configuration hashes were independently recomputed.

The [preserved text evidence](https://github.com/ketianzhang1-lang/jsp-000301-lean/tree/44eb9a9d43764820558349af550c2246f1843108/verification/jsp-000250/run-35168833566)
is pinned at commit `44eb9a9d43764820558349af550c2246f1843108`. It includes
the unmodified logs extracted from the artifact and completed job/step results
retrieved from GitHub. `leanchecker.log` is empty on this successful run;
the completed build/replay step records successful command exit.

The complete Actions artifact includes the compressed export and tested source
archive. Actions artifacts have a retention deadline; the smaller text logs,
checker configuration, statements and checksums are additionally preserved at
the immutable Git commit linked above. The export can be reproduced from the
pinned source using [scripts/verify_nanoda.sh](scripts/verify_nanoda.sh).

## Reproduction limits

Mathlib's cache was downloaded over the network. Neither the complete Mathlib
source tree nor every imported theorem was rebuilt from source offline.
The independent checker validates the exported target dependency closure.
The exporter and NaNoda were built during the run; no undocumented local
development modifications are required by the reproduction instructions.
Checker implementation independence does not amount to an independent human
review or a claim that the tool versions are free of defects.

This submission adds only proof-intake files. Official repository validation,
data checks, immutable-history checks, and all 22 existing unit tests also
passed locally. Public preflight of the exact submission commit is linked
from the pull-request description. Mathematical statement correspondence,
novelty, attribution, partial-result eligibility and any award remain subject
to the organizers' review.
