# Independent implementation verification

Nanoda 0.4.17 checks 10,694 declarations in the exported closure of:

- `JSP000359.original_problem`: the real-threshold counting bound and sharp greatest liminf.
- `JSP000359.mem_real_count_iff`: the finite counting definition includes exactly every index meeting the original least-common-multiple threshold, for nonnegative real thresholds and increasing positive sequences.
- `JSP000359.normalized_count_bounded`: normalized counts lie in `[0,2]`.

The checker also prints the actual counting, normalization, liminf and least-common-multiple definitions. It accepts only `propext`, `Classical.choice`, and `Quot.sound`. The two original Lean source files remain byte-for-byte identical to the previously submitted Lean verification record.

## Reproduction

Use Python 3.11 or newer, the pinned Lean 4.19.0 toolchain and dependencies, and these clean tool sources:

- [lean4export v4.19.0](https://github.com/leanprover/lean4export/tree/bae5a4a9c1cddec1fd97a82907cb5be9da884b2d), commit `bae5a4a9c1cddec1fd97a82907cb5be9da884b2d`, built with Lean 4.19.0 using `lake build`.
- [Nanoda 0.4.17](https://github.com/ammkrn/nanoda_lib/tree/4c544ed4099c8227f07d5de77ad1e69fb0740a27), commit `4c544ed4099c8227f07d5de77ad1e69fb0740a27`, built using `cargo build --release --locked`.

After installing the dependencies and running the existing `python verify.py`, run:

```sh
python verify_independent.py --exporter /path/to/lean4export --nanoda /path/to/nanoda_bin --exporter-source /path/to/lean4export-source --nanoda-source /path/to/nanoda-source
```

The script checks tool and dependency source revisions and tracked cleanliness, matches the package files against the previous verification record, builds the unchanged proof modules, and exports the three targets. It checks the export and requires rejection of a final theorem whose proof was replaced by zero and one replaced by an unpermitted axiom. Rejections must be semantic proof/axiom errors, not merely parser failures.

Exact binary, source, script, export, configuration and log hashes are recorded in `verification/independent-result.json`. Export format is 3.1.0. The large export and invalid controls remain in the ignored `.independent-check/` directory.

This is a separate checker implementation operated by the submitter. It is not an independent-person review, a network-isolated build, or the prize's designated verification. Earlier attribution and overlap disclosures are unchanged; no first-formalization, stronger mathematical result, priority or award entitlement is claimed.
