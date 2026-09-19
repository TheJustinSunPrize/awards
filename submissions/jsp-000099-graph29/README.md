# Erdős 82: a formal certificate for a known 29-vertex witness

**LOCAL VERIFICATION PASSED — OFFICIAL REVIEW OUTSTANDING.** This package contains a Lean formalization associated with **JSP-000099 / Erdős 82**, prepared for official review. The recorded local build, fresh kernel replay, export, and independent checker run succeeded. This document does not assert submission, official verification, acceptance, priority, or award eligibility.

## Contribution and exact scope

The formalized result is an explicit undirected simple graph on 29 vertices with **no regular induced subgraph on seven or more vertices**. Every subset size from 7 through 29 is covered, and the possible common degree includes zero. This is a witness for the known finite lower bound `N_{≥7} ≥ 30`.

The graph and mathematical lower bound are due to **Paul W. Dyson and Brendan D. McKay**. The proposed contribution is a Lean formalization: a proved certificate-checking procedure, a correspondence with Mathlib's graph definitions, and concrete witness certificates. It does not claim a new graph, a better numerical bound, the equality `N_{≥7} = 30`, or a solution to the open asymptotic questions in Erdős 82. See [STATEMENT.md](STATEMENT.md) for the exact statement and its relationship to the prize catalog.

## Sources and witness identity

- Dyson and McKay, [*Ramsey numbers for regular induced subgraphs*, arXiv:2604.08215v3](https://arxiv.org/html/2604.08215v3), Theorem 1.2 and Section 5.1.
- The authors' [data page](https://users.cecs.anu.edu.au/~bdm/data/ramsey.html), section “Regular induced subgraphs,” the 29-vertex sample for `k = 7`.
- [Original compressed graph6 stream](https://users.cecs.anu.edu.au/~bdm/data/regsub_ge7.29some.g6.gz).

The witness is the **first graph6 line** of that stream. Its 29 vertices and 202 edges are represented in `Graph29.lean` and in the supporting data. The SHA-256 of the selected line **including its terminating LF** is:

```text
464ffb9db0b700c3ba7104fabbd76e2e338e7276a1c4b1184f67bc9c6692033b
```

The original mathematical work and source data retain their attribution; no ownership of them is asserted. Lean, Mathlib, and other dependencies retain their upstream licenses and attribution.

## Proof architecture

| Component | Role |
| --- | --- |
| `RegularCertificate.lean` | Defines regularity by finite neighbor counts and proves soundness of the generic certificate rules. |
| `Graph29.lean` and `GraphBridge.lean` | Define the concrete graph, establish symmetry and absence of loops, and connect the neighbor-count predicate to Mathlib's induced-graph regularity. |
| `MaskCertificate.lean` | Connects the compact bit-mask representation to the finite-set checker through proved equivalences. |
| `CheckpointCertificate.lean` and `CertificateSteps.lean` | Check exact state labels and compose locally justified proof steps without trusting generator output. |
| Degree certificate modules | Establish the absence of a regular induced subgraph for each possible common degree. Large certificates may be split into import-linked parts. |
| `Erdos82Finite.lean` | Combines the cases into `graph29_no_regular_induced` and the existential theorem `exists_graph29`. |
| `supporting-computation/` | Records witness provenance and separate computational checks; these are not premises of the Lean theorem. |

The external generator proposes a certificate. The Lean proof justifies the checker and establishes acceptance of the certificate. Checkpoint labels are checked for equality with the actual state; a label cannot silently discard candidates. The final theorem does not assume the C++ result or a data-file label.

## Recorded local verification

The [verification record](verification/verification.json) reports the actual command outcomes and source/executable hashes. The main source hash is `92db846ccc1b5ccc44f3d6bcb8b7b9f78c39bf321388942b66d190b22951c1a7`; [source-manifest.json](source-manifest.json) identifies the local proof sources.

| Check | Outcome | Recorded seconds |
| --- | --- | ---: |
| Compile all 40 local modules | Every exit code 0; source and object hashes recorded | 928.779 total |
| Fresh Lean kernel replay, `leanchecker --fresh` | Exit code 0 | 435.108 |
| Export both target theorem closures | Exit code 0 | 34.433 |
| Nanoda independent checking | Exit code 0; 108,865 declarations checked without errors | 207.524 |

Compilation time is the sum of the module durations in [compile-build.json](verification/compile-build.json). The verification runner reused this just-completed build only after matching source and compiled-object hashes. The fresh kernel, export, and Nanoda stages were then actually executed; their outcomes are not inferred from the successful build.

The [axiom audit](verification/axiom-audit.log) and [Nanoda output](verification/nanoda.stdout.log) report only `propext`, `Quot.sound`, and `Classical.choice`. The [negative controls](verification/negative-controls.json) also passed: the checker rejects a false cardinality cutoff and forged selected/possible checkpoint states.

The checking commands ran under macOS network denial, with a successful accessible/denied control comparison. **The filesystem was not isolated, and cached dependencies were used rather than rebuilt from source.** These conditions are recorded explicitly in `verification.json`; this is local reproduction evidence, not the organizer's designated isolated verification.

The generated theorem export is **198,732,937 bytes**, SHA-256 **`d59a72d39ddff64256307a275acdabb24082fa6b7a2cfe9467d4dea5f3be3089`**. The large export is not included in the PR package; the supplied verification tool regenerates it.

Separately, exhaustive C++ computation checked all **536,249,296** subsets of sizes 7 through 29 and found no regular induced subgraph. An independent data check confirmed the graph6 decoding, symmetry, looplessness, edge count, and subset counts. The generator reproduced all **33 certificate modules byte for byte**. These checks support provenance and reproducibility; they are not assumptions of the formal theorem.

## Reproduction

1. Verify the proof-source hashes in `source-manifest.json` and the witness-line hash above. Use `lean-toolchain` and the pinned dependencies in `lake-manifest.json` without silently updating them.
2. Prepare Lean **4.34.0** and Mathlib revision **`5ed2965256430c3649e86755f9576b54eca72435`**. Prepare compatible `lean4export` and Nanoda binaries, matching the recorded executable hashes when reproducing the exact environment. Download dependency sources and caches before imposing network isolation:

   ```sh
   lake exe cache get
   ```

   A standalone build can use `lake build Erdos82Finite`. The full verification runner below compiles local modules serially, which is preferable on machines with limited memory.

3. Optionally regenerate the certificates and compare their exact source bytes:

   ```sh
   python3 tools/regenerate.py
   ```

   This step requires Python 3 and a C++17 compiler available as `clang++`. A successful comparison checks reproducibility of the untrusted generator; it does not replace proof checking.

4. Review the theorem types and axiom closures of `Erdos82Finite.graph29_no_regular_induced` and `Erdos82Finite.exists_graph29` in `verification/axiom-audit.log` and compare them with `STATEMENT.md`.
5. Use `tools/verify.py` to compile the local import closure serially, replay the compiled target using the matching Lean toolchain's fresh kernel checker, export the theorem closures with a compatible `lean4export`, and check them with Nanoda under the declared axiom policy. For example, on macOS with the supported network-denial mechanism:

   ```sh
   python3 tools/verify.py \
     --project . \
     --module Erdos82Finite \
     --theorem Erdos82Finite.graph29_no_regular_induced \
     --theorem Erdos82Finite.exists_graph29 \
     --lean-bin /path/to/lean-4.34.0/bin \
     --exporter /path/to/compatible/lean4export \
     --nanoda /path/to/nanoda_bin \
     --output verification/local-run \
     --threads 1 \
     --deny-network
   ```

   Replace the placeholder paths with the prepared binaries. The default runner recompiles all local modules. Its optional `--existing-build-receipt` mode reuses only actual successful build artifacts whose source and object hashes match. Fresh kernel replay and independent checking run in either mode. The network-denial option requires macOS `sandbox-exec`; reproductions on other systems must report their actual isolation mechanism and conditions. The resulting records and logs identify the checks performed by that run.

## Related work, priority, and official review

[Issue #51](https://github.com/TheJustinSunPrize/awards/issues/51) previously proposed formalizing this same finite lower bound. It is acknowledged as a related public proposal. The reviewed issue described source review only and did not supply a completed witness proof. It is not official approval of this submission's scope, a reservation, or a priority determination. The bounded prior-art search is described in [STATEMENT.md](STATEMENT.md); it does not establish global first-formalization priority.

The [prize rules](https://www.hejustinsun.com/prize/rules) distinguish submission, designated offline verification, PR finalization, and award evaluation. Local automated checks and repository CI are evidence for review; they do not replace the organizer's designated verification or decide the reward. The organizer must assess whether this formalization of a known finite subresult qualifies for an award. Neither a successful build, a submitted PR, nor the solver/formalizer allocation policy guarantees payment.

**Local verification is complete. Official designated verification, eligibility assessment, and any award decision remain outstanding.**
