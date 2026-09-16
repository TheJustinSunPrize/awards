# External implementation check

The final five-point theorem and its transitive dependencies were exported and
checked by Nanoda, a Rust implementation separate from Lean's C++ kernel.
This adds an independent implementation check. It is still run by the submitter,
not an independent reviewer, and is not the Prize's designated offline audit.

## Pinned tools

- Lean: 4.19.0, commit `6caaee842e9495688c1567e78c0e68dbb96942aa`.
- [lean4export](https://github.com/leanprover/lean4export/tree/bae5a4a9c1cddec1fd97a82907cb5be9da884b2d):
  commit `bae5a4a9c1cddec1fd97a82907cb5be9da884b2d` (tag `v4.19.0`), export format 3.1.0.
- [Nanoda](https://github.com/ammkrn/nanoda_lib/tree/4c544ed4099c8227f07d5de77ad1e69fb0740a27):
  version 0.4.17, commit `4c544ed4099c8227f07d5de77ad1e69fb0740a27`.

Both tools were built from the pinned, tracked-clean sources. Nanoda was built
using `cargo build --release --locked`, Rust 1.98.1, with the Windows GNU
self-contained linker. The proof checker source was not modified. Binary SHA-256
values are in the record; other platforms can produce different binary hashes.

## Result and scope

The export contains the closure of exactly
`SendovFivePointPlane.finite_set_large_angle`. Nanoda checked **18,045 declarations**
with no errors. The exported final statement, the `Point` abbreviation and both
angle definitions are printed in the [successful log](verification/nanoda-final.log).
They express at least five distinct standard Euclidean-plane points, three
pairwise distinct vertices, and a lower bound of `3*pi/5` on the standard
inner-product angle.

The allow-list contains only `propext`, `Classical.choice`, and `Quot.sound`.
Unpermitted axioms are hard errors; blanket permission is explicitly disabled.
The three admitted axioms are printed in the successful log.

Two deliberately invalid copies test rejection:

1. Replace the final theorem's proof expression by the natural-number literal
   zero. The checker must fail at type/definitional-equality checking.
2. Replace that theorem declaration by a syntactically valid axiom with the same
   name and type. The checker must reject this unpermitted axiom.

The [record](verification/independent-result.json) binds the proof source hashes,
export metadata, input hashes, binary hashes, script/config hashes and all three
exit codes. The script requires the expected semantic rejection messages, not
just any nonzero exit. Malformed-input rejection is not counted as an axiom test.

No network-isolated rebuild or official statement-fidelity/attribution review is
claimed. The check establishes neither a first-formalization priority nor award
eligibility, and does not extend the theorem to the general Sendov lower bound.

## Reproduce

Clone the two upstream tool repositories at the commits above. In the exporter
checkout, run `lake build` with Lean 4.19.0. In the Nanoda checkout, run
`cargo build --release --locked` with a suitable Rust toolchain.

Run this package's local verification first, then the external check (Python 3.11+):

```sh
python verify.py
python verify_independent.py \
  --exporter /path/to/lean4export/.lake/build/bin/lean4export \
  --nanoda /path/to/nanoda_lib/target/release/nanoda_bin \
  --exporter-source /path/to/lean4export \
  --nanoda-source /path/to/nanoda_lib
```

On Windows, use the corresponding `.exe` paths and shell-appropriate line
continuation syntax. If required, add the Rust toolchain's `bin` directory to
the process PATH for its runtime DLL.

The export and invalid controls are written to the ignored `.independent-check/`
directory; their hashes are recorded, but these large generated files are not
committed. The portable [configuration](verification/nanoda-config.json) also
allows checking a reproduced `final.ndjson` directly.
