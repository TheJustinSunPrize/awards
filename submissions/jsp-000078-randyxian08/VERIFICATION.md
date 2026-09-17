# Observed verification

The final verification completed on 2026-09-17. The complete command
`SSL_CERT_FILE=/etc/ssl/cert.pem bash scripts/verify.sh` exited with code 0.
The certificate variable selects the system CA store on the checking machine;
it does not disable certificate validation.

## Results

| Check | Observed result |
| --- | --- |
| Toolchain | Lean 4.33.0, commit d8b18978322de05a8f3dba51ef03cf5461676c17, arm64 macOS |
| Mathlib | db584cd6d46c92f209a44c0f1c829460d327499d |
| Dependency identity | All 9 package revisions matched the Lake manifest; no tracked dependency source modifications |
| Finite proof sources | All 35 file blob IDs and byte counts matched the fixed upstream Git tree; SHA-256 lock retained |
| Finite proof | Compiled all 35 unchanged modules successfully |
| General-graph proof | Compactness, definitions, general theorem, and root library compiled successfully |
| Axiom audit | All four expected reports accepted; no sorryAx or custom mathematical axioms |
| Kernel replay | Successfully replayed 3,203 declarations from all 39 project mathematical modules |
| Verification tooling | 11 tests passed, including rejection of corrupted/truncated source and forbidden axiom reports |

The actual final type printed by Lean is:

```lean
@JSP000078.erdos_58_exact_statement :
  ∀ {V : Type u_1} (G : SimpleGraph V) (k : ℕ),
    G.oddCycleLengths.Finite →
    G.oddCycleLengths.ncard ≤ k →
      G.chromaticNumber ≤ 2 * ↑k + 2 ∧
        (G.chromaticNumber = 2 * ↑k + 2 ↔
          (SimpleGraph.completeGraph (Fin (2 * k + 2))).IsContained G)
```

The compactness lemma, finite theorem, and final theorem depend on exactly
`propext`, `Classical.choice`, and `Quot.sound`. The definition alignment uses
only `propext` and `Quot.sound`. These reports are transitive, not source-text
estimates. The final signature has no hidden finite/countable vertex premise.

## Evidence and scope

The verification archive contains actual logs, the exact source files, pinned
dependency manifests, the original finite modules, and a source-hash summary.
Its URL, SHA-256, and byte count are recorded in `artifacts.json` in the
submission directory. The release's `JSP000078_verified_20260917.zip` contains
the proof and these logs. Large log artifacts remain in the contributor's
release archive rather than the award repository's source record directories.

Key archive files under `evidence/`:

- `complete-verification.log`: successful final script output.
- `initial-finite-build.log`: initial compilation of the finite sources.
- `general-proof.log`, `compactness.log`, and `finite-proof.log`: final stages.
- `axioms.log` and `axioms.json`: actual transitive reports and final type.
- `replay.log` and `replay.json`: exact module closure and successful replay.
- `verification-summary.json`: source hashes, counts, and toolchain.
- `upstream-tree-check.json` and `upstream-manifest.json`: source identity.

Final Lake stages may reuse objects already built from the same local sources.
The separate kernel replay collects all project mathematical declarations from
the compiled modules and checks them against an environment importing Mathlib
only. It rejects custom axioms, unsafe/partial declarations, and overlapping
names. The utility is reused unchanged from PR #130 and attributed in
[REFERENCES.md](REFERENCES.md); it is not a new independently implemented checker.

Official Mathlib dependency caches were used. Mathlib itself and its dependencies
were not freshly replayed. This is checking with the same Lean kernel, not an
independent human referee attestation, official prize verification, or an award.
Absolute local workspace prefixes in archived logs are replaced with
`<WORKSPACE>` or `<USER>`; unredacted originals remain local.

## Changes from the supplied candidate

No change to the mathematical statements or proof strategy was needed.
The deprecated `push_neg` spelling was changed to `push Not`, and source status
comments were updated. The complete final proof was rebuilt and audited after
that change. No assumptions or proof placeholders were added.

The reproducer now has a fixed hash lock for every finite-proof source and
reuses matching local files. A transient download mismatch was rejected rather
than accepted as proof source; the local file and a fresh download both matched
the fixed upstream Git blob. The new lock was checked against the GitHub tree
at the pinned commit, and all 35 files are checked on every run. The initial
network failure and mismatch logs remain in the archive for transparency.

The script also adds the attributed kernel replay as a required success stage.
These tooling improvements and the supplementary lemmas do not establish
priority over the already-public arbitrary-graph extension in PR #130.
