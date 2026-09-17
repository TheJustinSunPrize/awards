# Verification evidence

## Successfully checked proof

- Source repository: https://github.com/ketianzhang1-lang/jsp-000301-lean
- Immutable source commit: `b1de908cb5d9cb006b54c3d44accceca7a979a96`
- Directory: `projects/jsp-000399`
- [Completed proof run](https://github.com/ketianzhang1-lang/jsp-000301-lean/actions/runs/35168262095): SUCCESS on 2026-09-17.
- Lean: `leanprover/lean4:v4.34.0`.
- Mathlib: `5ed2965256430c3649e86755f9576b54eca72435` (v4.34.0). All actual transitive package revisions were compared with lake-manifest.json.

Actual successful checks:
1. `lake build --wfail`: both JSP000399 and Compatibility built, 3094 jobs total.
2. Bundled Lean kernel replay of JSP000399 and Compatibility: both commands exited successfully.
3. Seven declaration axiom audits, including the exact-statement adapter: only `propext`, `Classical.choice`, and `Quot.sound` occur.
4. False-arithmetic negative control: the attempted proof of `(1 : Nat) = 0` was rejected.
5. Separate Python enumeration: two unequal 27-element positive integer sets, with all 2925 triple sums equal including multiplicities.
6. Independently implemented NaNoda checker with strict axiom allowlist: **7511 declarations checked with no errors**. No sorry or native-evaluation axiom is permitted.

The source proof itself checks the finite claim in Lean's kernel through `decide +kernel`. The Python calculation is supplemental.

## Artifact and reproduction

[Proof evidence artifact](https://github.com/ketianzhang1-lang/jsp-000301-lean/actions/runs/35168262095/artifacts/10475917176):
- Artifact ID: `10475917176`.
- Size: 4803287 bytes.
- SHA-256: `7dc5e08e681e479ffc7e146e5795933a8b5844a9c29f77fca8fda4033698629b`.
- GitHub expiry reported: `2026-12-16T00:51:53Z`.

It includes the tested source archive, build and axiom logs, kernel replay logs, negative control and cross-check logs, exported proof, NaNoda configuration, statement rendering and checker logs. Reproduce using the commands in README.md. The exporter and independent checker commits are pinned in scripts/verify_nanoda.sh.

## Limits and intake

These are contributor-run checks on GitHub-hosted Linux. Cached Mathlib and network access were used; a clean offline rebuild of all dependencies was not performed. A successful check is not independent human review, organizer certification, a priority decision or payment authorization. No organizer-approved minimum safe toolchain version or independent permanent archive is claimed. GitHub artifacts have finite retention.

Only a complete proof of the 27-element negative result is claimed. Scope relative to the whole catalog entry remains partial. Source histories include failed development attempts; the successful immutable commit and run above supersede those attempts.

The submission PR will link the exact-package preflight separately. That check tests the official repository format, byte identity of proof files, unchanged official data and isolated additive change scope; it does not replace mathematical verification.
