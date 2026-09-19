# Verification receipt: JSP-000924

This is contributor-produced verification evidence, not an organizer decision,
independent human sign-off, or authorization of a prize.

## Fixed proof source

- Repository: `ketianzhang1-lang/jsp-000301-lean`.
- Commit: `563243740fea68d752dbd743e83f9b2a55f846ad`.
- Project: `projects/jsp-000924`.
- Public proof run: https://github.com/ketianzhang1-lang/jsp-000301-lean/actions/runs/35160681367
- Job: `105010479740`; completed successfully on September 16, 2026.
- Lean 4.34.0; Mathlib `5ed2965256430c3649e86755f9576b54eca72435`.
- All nine dependency revisions are locked and checked against the actual checkouts.

All eleven source, audit, script, provenance, configuration, and license files
listed in SOURCE_SHA256SUMS are copied byte-for-byte from the tested source archive.
The submission README and this receipt are subsequent explanatory documents.
The development README in the original archive predates the completed check.

## Actual observed results

- `lake build --wfail`: passed (8,925 dependency/build jobs, including actual
  compilation of JSP000924, not 8,925 newly written proofs).
- `lake env leanchecker JSP000924`: passed with exit zero and an empty output log.
  This is the same Lean kernel implementation, not a second implementation.
- All six target axiom audits: only `propext`, `Classical.choice`, `Quot.sound`.
- Negative control `1=0`: rejected by Lean.
- Exact Python diagnostics: 10,260 proper-divisor tests and 20 checks of failure
  of the specified seven-prime list. These finite diagnostics are not a substitute
  for the universally quantified Lean theorem.
- NaNoda 0.4.17: **Checked 6372 declarations with no errors**.

The NaNoda checker revision is
`4c544ed4099c8227f07d5de77ad1e69fb0740a27`.
The same-toolchain exporter revision is
`6cea97789dc088ea47fcea15692db85685aedac5`.
All six audited theorems and their complete transitive dependencies were exported.
Only the standard three axioms were allowed; unpermitted axioms cause hard errors.
No native-evaluation or compiler-trust axiom was permitted. Printed definitions
and target statements were inspected in the original downloaded artifact.

The five compact logs in `evidence/` are the unchanged files from that artifact.
The original source archive, exported proof, checker configuration, complete
checker build log, and printed statements remain in the full artifact and backup.

## Artifact integrity and retention

Artifact ID: `10473036511`, name `jsp-000924-evidence`.
Artifact: https://github.com/ketianzhang1-lang/jsp-000301-lean/actions/runs/35160681367/artifacts/10473036511

ZIP bytes: **3,788,486**.
ZIP SHA-256: `8049531abb9a5f20a090d9e55963271084ed8086604f37ebd5c32ae07d30db17`.

The downloaded ZIP hash was verified locally before its contents were inspected.
Inner source archive SHA-256:
`fb279cdb2af2d323745989fcfd39f4ac90fc9aa7e485fc2d677184e450f2977a`.

GitHub reports expiration on **December 15, 2026**. This is finite-retention
evidence, not independent permanent archival. A local backup is included in the
package supplied to the contributor; the public Git source is commit-pinned.

## Review boundaries

Official Mathlib caches and network access were used. The proof checker
implementations were both run by the submitting contributor. No offline rebuild
of all dependencies, independent human review, organizer-approved minimum safe
version, global priority, confirmed recipient, prize tier, or payment entitlement
is asserted. Whether this known fourth-power-family formalization qualifies for a
contribution award remains a question for the organizers.

The source DOES NOT assert that its Sierpinski numbers lack all finite prime
covers. That open statement is distinct from the specifically named failed list.
The prior unrestricted infinitude proof is acknowledged in PROVENANCE.md.
