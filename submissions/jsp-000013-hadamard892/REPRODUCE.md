# Reproduce the order-892 proof

## English

Use the committed `lean-toolchain` and `lake-manifest.json`; do not update their
versions. The verified run used Lean 4.34.0 and Mathlib commit
`5ed2965256430c3649e86755f9576b54eca72435`. Run the commands below from this
package's directory. A dependency cache is allowed; delete or omit this package's
own `.lake/build` before a fresh run.

```sh
lake exe cache get
```

Build `leanprover/lean4export` at commit
`076e8e57707e813375e8f9da8bf989799ace9680` with the same Lean 4.34.0 toolchain.
Use Nanoda 0.4.17 from `ammkrn/nanoda_lib`, commit
`4c544ed4099c8227f07d5de77ad1e69fb0740a27`. Tool repository links, exact
binary hashes and provenance limits are in
[TOOL_PROVENANCE.json](verification/TOOL_PROVENANCE.json).

The following placeholders must be replaced with the corresponding local paths.
On macOS, `--deny-network` checks its policy using a reachable loopback control
before running the proof commands. On other platforms, omit that flag only if
you also report that the same network policy was not reproduced, or supply an
independently documented equivalent isolation method.

```sh
python3 tools/verify.py \
  --project . --module Hadamard892 \
  --theorem Hadamard892.goethals_seidel_hadamard \
  --theorem Hadamard892.matrix892_isHadamard \
  --theorem Hadamard892.exists_hadamard892 \
  --output verification-local --timeout 1800 --threads 1 \
  --lean-bin /absolute/path/to/lean-4.34.0/bin \
  --exporter /absolute/path/to/lean4export \
  --nanoda /absolute/path/to/nanoda_bin \
  --deny-network
```

The driver compiles the six modules in dependency order, writes their local
`.olean` files, replays `leanchecker --fresh`, exports the three theorem roots,
and runs Nanoda with hard errors for unknown requested roots and unpermitted
axioms. Read the new receipt and all logs; do not infer success merely from the
existence of the output directory. The output directory includes the actual
`proof.ndjson` export. Proof-export bytes can depend on the exact toolchain and
dependencies, so compare the recorded versions as well as the hash.

After a successful run, the separate error-control module can be checked with:

```sh
lake env lean -j 1 NegativeControls.lean
```

For the recorded macOS run that command was also wrapped in
`sandbox-exec -p '(version 1)(allow default)(deny network*)'`, using the same
freshly compiled production modules. This is a proof that the corrupted input
fails the correlation criterion, so a successful compilation is the expected
negative-control outcome.

The receipt redacts machine-specific paths. It preserves source hashes, command
arguments, exit codes, durations, dependency pins and the applied isolation
limits. The driver itself is provided and hashed in the receipt. External
official verification and a permanent archive identifier are still pending.
