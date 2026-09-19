# Contributor verification results

These results concern only the **known k=-1 special case** of JSP-000390 / Erdős 479.
They are not an independent human review, organizer verification, or an award decision.

## Exact source and run

- Proof source commit: `22e9b888c2378df7c2039ceceddccbfc5b883387` in `ketianzhang1-lang/jsp-000301-lean`.
- Project directory: `projects/jsp-000390-minus-one`.
- [Successful public run](https://github.com/ketianzhang1-lang/jsp-000301-lean/actions/runs/35140570379), workflow run 4; job `104943756014`.
- Lean 4.34.0; Mathlib `5ed2965256430c3649e86755f9576b54eca72435` and all transitive revisions pinned in the included manifest.
- The six submitted proof/configuration/audit/license files match the source archive from this run byte-for-byte.

## Observed results

`lake build --wfail`: **passed**, 950 jobs. The target `JSP000390` was compiled from source.

`lake env leanchecker JSP000390`: **passed**. This uses the same Lean kernel implementation as the compiler, not a second implementation.

Actual target axiom reports:

| Declaration (JSP000390 namespace) | Transitive axioms |
| --- | --- |
| three_pow_succ_dvd | propext, Quot.sound |
| three_pow_is_solution | propext, Quot.sound |
| minus_one_unbounded | propext, Classical.choice, Quot.sound |
| minus_one_infinite | propext, Classical.choice, Quot.sound |
| minus_one_infinite_unrestricted | propext, Classical.choice, Quot.sound |

All five reports and all nine actual dependency revision checks passed. No custom mathematical axioms, admitted proofs, or native-evaluation axioms were used by these targets.

A deliberately false proposition, `1 = 0`, was rejected by the same Lean invocation. This is a pipeline sanity check, not a general proof of checker soundness.

**NaNoda 0.4.17**, commit `4c544ed4099c8227f07d5de77ad1e69fb0740a27`, checked the five target declarations and their complete exported dependency closures. The pinned exporter is `leanprover/lean4export@6cea97789dc088ea47fcea15692db85685aedac5`, built using the same Lean 4.34.0 toolchain. The exact output is:

```text
Checked 3775 declarations with no errors
```

The strict NaNoda allowlist is `[propext, Classical.choice, Quot.sound]` with `unpermitted_axiom_hard_error: true`. No compiler-trust axiom is permitted. Pretty-printed target statements and definitions were also produced without errors. Exporting target closures instead of all imported tactic declarations does not omit any dependency of a requested theorem.

## Evidence archive

[Run artifact](https://github.com/ketianzhang1-lang/jsp-000301-lean/actions/runs/35140570379/artifacts/10465540346): `jsp-000390-minus-one-evidence`, ID `10465540346`.

- ZIP size: **1,934,102 bytes**.
- ZIP SHA-256: `2cec9094bc6727d6bc3c6da745f1281020661be0d55146a22ab526f111705a3e`.
- Included source archive: `source.tar.gz`, **6,943 bytes**.
- Source archive SHA-256: `896c0380599d5a9a4732d54905c1cbc191b0f6641489c51829c45a1f5be79963`.
- Compressed proof export SHA-256: `31e78723c4e4e774ad42b10bc32b2861c1436e7b80bf5cfd59672e3c7a5a74eb`.

The downloaded ZIP checksum and the included source contents were checked before this record was written. The artifact contains the build, kernel replay, axiom, negative-control and NaNoda logs, checker configuration, pretty-printed statements, exported proof dependencies, source snapshot and checksums.

GitHub reports artifact expiry on **2026-12-15**. This is finite-retention evidence, not an independent permanent archive. The source remains linked to an exact public Git commit. Additional archival and organizer-required verification may still be necessary.

## Limits

Both checker implementations were run by the same submitting contributor using AI-assisted tooling. Official Mathlib caches and network access were used. No offline rebuild of all Mathlib, independent human statement signature, organizer-approved minimum safe version, full-original-problem solution, global first-formalization priority, or entitlement to payment is asserted.
