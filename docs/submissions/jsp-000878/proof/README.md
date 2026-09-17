# Reproduction

The package contains a Mathlib-only [statement](Statement.lean), a new statement bridge and a small compatibility patch. The substantive prior proof remains at its attributed public source; it is fetched by exact Git blob and checked against SHA-256 rather than being republished as our own work.

Requirements: Python 3, GitHub CLI `gh` for read-only public API calls, Git, Lean **4.34.0**, and a built Mathlib checkout at `5ed2965256430c3649e86755f9576b54eca72435` (tag `v4.34.0`). Use the actual toolchain binary path, not an ambiguous toolchain-manager shim. Obtain Lean from its official release or a normal toolchain manager. No private token or identity belongs in this packet.

Prepare Mathlib with `lake exe cache get` followed by `lake build Mathlib` in that pinned checkout. The second command handles unavailable cache entries. Then run, substituting your installation paths and dedicated local output directories:

```sh
python3 reproduce.py --lean /path/to/toolchain/bin/lean \
  --mathlib /path/to/mathlib4 --work proof-work --evidence verification-run
```

The script checks the Mathlib commit and tracked-file cleanliness, downloads the 29 source modules pinned in [source-lock.json](source-lock.json), checks their Git blob and SHA-256 identities, applies only [compatibility.json](compatibility.json), and checks each resulting hash. It scans proof code for forbidden constructs, compiles the full closure plus [Statement.lean](Statement.lean) and [Main.lean](Main.lean), audits all three final declarations, replays the problem modules and bridge with the same-toolchain `leanchecker`, and verifies that false arithmetic is rejected. It writes logs and a receipt whose `verified` field stays false unless all steps succeed. `--fetch-only` is a source-lock check, not proof verification.

The default rebuilds every problem module. Optional `--resume-receipt` is only for continuing a recorded local compilation: it checks compiler, Mathlib, complete source-lock, source and output hashes. Resumed stages are explicitly labeled. The bridge is always recompiled and the axiom audit and replay always rerun. Imported Mathlib modules are reused; this is not a fresh replay of every Mathlib theorem and not an independent human or external-kernel review.

## Compatibility patch

The upstream files declare Lean/Mathlib 4.33.0. The 4.34.0 attempt exposed changes in `Erdos1058Assembly.lean` and `Erdos1058BugeaudLaurentProof.lean`:

- `Finset.prod_le_prod` for naturals now needs the comparison hypothesis alone, so the old separate nonnegativity tactic branch is removed.
- Unrestricted `norm_num` rewrites factorization into `padicValNat`, leaving otherwise equivalent linear-arithmetic terms syntactically different. Two digit-sum identities now use only subtraction and multiplication simplification; the last numerical comparison normalizes only natural casts.

- The lifting-the-exponent identity is converted from `padicValNat` to factorization using the proved `Nat.factorization_def` equality, rather than an invalid definitional `change`. Adjacent cast simplifications are restricted for the same normal-form reason.

The [reviewable patch](compatibility.patch) changes tactics only. Every theorem statement and hypothesis is retained. Both original and patched source hashes are recorded. An initial failed compilation must remain labeled as a failed attempt, not a successful verification.
