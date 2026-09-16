# Reproduce the independent proof check

Use the project's pinned Lean and Mathlib versions. The verified toolchain is recorded in `../verification/verification.public.json`; do not substitute another version without rerunning every check.

`verify_export.py` accepts explicit tool locations so it does not depend on the submitter's computer paths. A reviewer needs Python 3, the pinned Lean toolchain, `lean4export` built for that exact Lean version, and Nanoda. Tool source commits and licensing are listed in `THIRD_PARTY_NOTICES.md`.

For the Lean 4.34.0 package, set these paths for your machine:

```sh
TASK_PROOF_PROJECT=/path/to/proof-project
TASK_LEAN_BIN=/path/to/lean-4.34.0/bin
TASK_EXPORTER=/path/to/lean4export/.lake/build/bin/lean4export
TASK_NANODA=/path/to/nanoda/target/release/nanoda_bin

python3 verify_export.py \
  --project "$TASK_PROOF_PROJECT" \
  --lean-bin "$TASK_LEAN_BIN" \
  --exporter "$TASK_EXPORTER" \
  --nanoda "$TASK_NANODA" \
  --module Erdos466 \
  --theorem Erdos466General.erdos_466_parameter_classification \
  --theorem Erdos466General.erdos_466 \
  --output verification-results \
  --timeout 1800 \
  --threads 2 \
  --deny-network
```

The script freshly compiles local imported proof modules in dependency order, runs `leanchecker --fresh`, exports both named theorems with their transitive dependencies, and checks the exported declarations using Nanoda. It stops on any failed stage. The script records all actual exit codes and hashes, and rejects a result if a local source changes during the run.

Nanoda permits only `propext`, `Classical.choice`, and `Quot.sound`; other axioms are hard errors. Its output prints the exact checked theorem types and admitted axioms. `leanchecker` reuses Lean's kernel. Nanoda is the separate Rust implementation.

To rebuild the exporter, use its listed source commit and run its `lake build lean4export` with the pinned Lean bin directory first in `PATH`. To rebuild Nanoda, use its listed source commit and the upstream Cargo build instructions. Rebuilt binary hashes can differ by compiler and platform; preserve source commits, local build instructions, and the actual hashes alongside the new results.

A successful run proves only the exact formal theorem statements recorded in the exported closure. It does not itself establish equivalence to the original problem, novelty, or award acceptance. On macOS, `--deny-network` uses `/usr/bin/sandbox-exec` with `(version 1)(allow default)(deny network*)` for every compilation, kernel replay, export, and Nanoda command. Before checking, a control confirms that an accessible loopback connection is refused under the policy. Failure to establish this control aborts the run. This restricts network access for the checking commands; it does not isolate the filesystem, rebuild cached dependencies from source, or generate official curator/verifier signatures. These distinctions remain explicit in the record. On other platforms, use an independently verified equivalent network isolation mechanism; omitting the flag must be disclosed.

The script writes both a raw `verification.json` and a publication copy `verification.public.json`. The publication copy replaces local machine paths with transparent placeholders such as `<project>`, `<lean-bin>`, `<exporter>`, `<nanoda>`, and `<verification-output>`. Do not change hashes, exit codes, theorem names, or checking results when preparing that copy; keep the raw record for reproduction.
