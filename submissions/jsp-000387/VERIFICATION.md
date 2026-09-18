# Local verification record

Checked on 2026-09-16 on macOS, arm64.

## Inputs

- Awards base: `f4e7173d89dfe91022a185427d63452c8ffbf6ae`.
- Lean: `4.34.0`, release build, commit
  `293d5d0c0c3f3dded4688b3ccd6a33939ac5102b`.
- Mathlib: `5ed2965256430c3649e86755f9576b54eca72435` (`v4.34.0`).
- Transitive dependency revisions: [lake-manifest.json](lake-manifest.json).
- Submitted file checksums: [SHA256SUMS](SHA256SUMS).

## Results

| Check | Result |
| --- | --- |
| `lake build` | Passed; `FullField` compiled locally. |
| `lake env lean -DwarningAsError=true FullField.lean` | Passed. |
| `lake env lean -DwarningAsError=true Audit.lean` | Passed; all three guarded axiom reports match. |
| `lake env leanchecker --fresh --verbose FullField` | Passed; kernel replay from an empty environment. |

The three submitted theorem declarations have exactly the axiom dependencies
`[propext, Classical.choice, Quot.sound]`. There is no `sorryAx` or custom axiom.
The proof source contains no placeholder proof, native decision procedure,
unsafe declaration, or environment-modifying metaprogram.

The audited final theorem is:

```lean
JSP000387.exists_full_field_ordering
    (K : Type*) [Field K] [Fintype K] :
    ∃ a : ℕ → K, JSP000387.IsFullFieldOrdering K a
```

The [definition and interpretation of the predicate](README.md#exact-scope)
are part of the statement review. In particular, the proof covers every finite
field, all its nonzero elements, and every prefix length from `1` through
`card K - 1`. It does not cover arbitrary nonzero subsets.

The official awards commands `validate`, `links`, `build`, `check`, and
`history --base f4e7173d89dfe91022a185427d63452c8ffbf6ae` also passed, as did
all 22 existing Python unit tests. Generated award/candidate JSON was unchanged.
The final submission run uses Python `3.12.14` and the exact requirements:
PyYAML `6.0.3`, jsonschema `4.26.0`, and markdown-it-py `3.0.0`.
The earlier exploratory Python 3.9 run has been superseded by this run with the
same Python minor version and dependency pins as the repository's CI.
The Lean checks use their exact pinned toolchain and library versions.

The sanitized [verification log](verification.log) records command output.

## Verification limits

Mathlib dependencies were obtained through its binary cache. Fresh replay
checks imported declarations as well as this package's declarations using
Lean's kernel. It is not a clean source build of all of Mathlib, an independently
implemented checker, an independently conducted review, or a network-isolated
verification run.

No signed curator statement, recipient consent, permanent external archive,
minimum-safe-version attestation, or award decision is supplied. This local
record is supplementary evidence for reviewing the full-field lemma, not an
official `verification/record.yaml`.
