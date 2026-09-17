# External verification and reproduction

## Recorded result

The four submitted modules passed direct compilation with `autoImplicit=false`
and warnings treated as errors, all **39 theorem axiom audits**, and bundled
Lean module replay. Nanoda independently rechecked the exported declaration
closure: **27862 declarations**, with the unqualified message
`Checked 27862 declarations with no errors`.

The full report and compact logs are under [verification/local](verification/local/verification.json).
The exported NDJSON has **151351934 bytes**, SHA-256:

```text
1c98fc4b8d7d78c6328515cc18118e894176f14cef9038cc500df06f5af6fad3
```

The export audit requires all requested declarations to be actual theorems,
checks format version and Lean commit, rejects unsafe declarations, and permits
only `propext`, `Classical.choice`, and `Quot.sound`. The Nanoda configuration
makes unpermitted axioms hard errors; `unsafe_permit_all_axioms` is false.
Natural-number and string kernel extensions are enabled. Two checker threads
are used. Configuration and platform-specific binary hashes are recorded.

### Positive and negative controls

Four correct imported Lean certificates compile. The intentionally false
unit-fraction and modular certificates fail to compile. A separate valid export
containing a theorem of `True` is accepted by Nanoda. Keeping the same proof and
valid export syntax while changing that theorem's type to `False` is rejected
with the pinned checker's `self.def_eq(u, v)` assertion. Both control hashes and
exit codes are retained. The external negative control therefore exercises proof
checking, not merely rejection of malformed JSON.

## Tool sources

[external-toolchain.json](external-toolchain.json) records unmodified checkouts:

| Tool | Revision |
| --- | --- |
| [lean4export](https://github.com/leanprover/lean4export) | `076e8e57707e813375e8f9da8bf989799ace9680` |
| [Nanoda](https://github.com/ammkrn/nanoda_lib) | `4c544ed4099c8227f07d5de77ad1e69fb0740a27` |

The exporter is built against the same Lean 4.34.0 commit as the proofs and emits
format 3.1.0. Nanoda 0.4.17 was built with Rust 1.94.0 from its committed lockfile;
the lockfile SHA-256 is in the manifest. The local build used checksum-verified
registry downloads through a mirror and the existing platform compiler.
Neither checker source was patched, and no additional axiom was permitted.

## Running the optional external check

First perform the dependency and package setup in [README.md](README.md).
In addition to Python, Git, and Elan, this step requires Rust/Cargo and a working
platform C linker. From the proof-package directory:

```sh
mkdir -p .verification-tools
git clone --no-checkout https://github.com/leanprover/lean4export.git .verification-tools/lean4export
git -C .verification-tools/lean4export checkout --detach 076e8e57707e813375e8f9da8bf989799ace9680
(cd .verification-tools/lean4export && lake build)
git clone --no-checkout https://github.com/ammkrn/nanoda_lib.git .verification-tools/nanoda_lib
git -C .verification-tools/nanoda_lib checkout --detach 4c544ed4099c8227f07d5de77ad1e69fb0740a27
(cd .verification-tools/nanoda_lib && cargo build --locked --release --jobs 2)
python3 verify.py \
  --exporter .verification-tools/lean4export/.lake/build/bin/lean4export \
  --nanoda .verification-tools/nanoda_lib/target/release/nanoda_bin
```

The verifier invokes the built binaries without downloading or publishing.
Results go under `verification/latest/`; build objects, full exports, checker
configurations, and pretty-printer files stay in its ignored `build/` directory.
The reproduction commands describe a fresh setup; the recorded local run instead
used pinned archive dependency paths already present on the contributor's host.
This distinction is not hidden by the successful checker result.

## Trust and scope

Bundled `leanchecker` shares Lean's C++ kernel and trusts imported declarations.
Nanoda is a separately implemented Rust type checker. It rechecks the exported
transitive closure, including reached library declarations, rather than treating
every imported theorem as an axiom. This does not mean that all of Mathlib was
exported, rebuilt, or checked.

The exporter, compiler implementations, foundational axioms, hardware, and
correspondence between the mathematical problem and formal statement remain in
the trust boundary. The checks were run by the submitter on one host. They are
not independently administered human review, network-isolated organizer
verification, or a finding of novelty, first priority, or award eligibility.

The source and compact evidence are versioned in Git. Large generated exports
are excluded from the Git source package. The full NDJSON export is not published with this update; the verifier regenerates
it from the pinned source and the report records its checksum and size. No
independently administered permanent archive is claimed.
