# Verification-tool attribution

The proof submission uses the official Lean kernel and an independent Nanoda check of an exported theorem closure. The optional `leanchecker --fresh` step reuses Lean's kernel and is not counted as an independent implementation.

- **Lean 4.34.0**: Lean authors, Apache-2.0; official release commit `293d5d0c0c3f3dded4688b3ccd6a33939ac5102b`. https://github.com/leanprover/lean4/releases/tag/v4.34.0
- **lean4export**: Lean contributors, Apache-2.0; commit `076e8e57707e813375e8f9da8bf989799ace9680`. Original upstream source was built without logic modifications for Lean 4.34.0. License is included as `LICENSE-lean4export`. https://github.com/leanprover/lean4export/tree/076e8e57707e813375e8f9da8bf989799ace9680
- **Nanoda 0.4.17**: Nanoda contributors, Apache-2.0; commit `4c544ed4099c8227f07d5de77ad1e69fb0740a27`. An existing local release binary was reused without modification; this run did not rebuild it. Binary SHA-256: `cfd89798e7f5f984f852e2410694e8c4efe1463b613f75e85c8dc904b499e146`. License fetched from that exact source commit is included as `LICENSE-Nanoda`. https://github.com/ammkrn/nanoda_lib/tree/4c544ed4099c8227f07d5de77ad1e69fb0740a27

These components do not certify prize eligibility. Machine checks must be accompanied by exact statement review and the prize maintainers' own records and signatures. The optional network-denial wrapper is recorded separately from filesystem isolation and dependency rebuilding; neither of those additional properties is claimed.
