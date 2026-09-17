# Verification receipt

## Scope and source

- Target: `JSP000736.erdos_885_k_eq_4`.
- Proof repository: [ketianzhang1-lang/jsp-000301-lean](https://github.com/ketianzhang1-lang/jsp-000301-lean).
- Source commit: `b67c69abefe3daaeea454008e9ddadaf2c4adc1e`.
- Project directory: `projects/jsp-000736`.
- Lean: `leanprover/lean4:v4.34.0`.
- Mathlib: `5ed2965256430c3649e86755f9576b54eca72435`.
- All nine dependency commits: [lake-manifest.json](lake-manifest.json).
- Definition and theorem compared with Formal Conjectures source at
  `c252a41054125b5fd9c8356e2137cd9b55337657`.

## Local validation

The build completed successfully (3,093 jobs). `leanchecker JSP000736` exited
successfully. Three theorem axiom audits allowed only `propext`,
`Classical.choice`, and `Quot.sound`. `Challenge.lean` successfully elaborated
the independently restated original definition and k = 4 target. All nine
checked-out dependency revisions matched the manifest. A false arithmetic
negative control was rejected. Source scanning found no proof placeholders,
custom axioms or `native_decide` in the proof or statement check.

Local execution used a loader compatibility wrapper setting Lean's sysroot,
PATH and LD_PRELOAD to correct /proc/self/exe resolution in the sandbox.
It did not edit proof source or proof checker logic. A separate clean GitHub
runner checks the same pinned source without that local wrapper.

## Clean CI and independent checker

[Proof verification run 35169128730](https://github.com/ketianzhang1-lang/jsp-000301-lean/actions/runs/35169128730)
checks the exact source commit above on Ubuntu 24.04 using a standard Elan
installation, pinned dependency revisions and the official Mathlib cache.

**Passed on 2026-09-17.** Every workflow step succeeded. Log review confirms
that the corrected source scan executed, all three theorem axiom audits and
all nine dependency checks passed, and NaNoda checked **7,286 declarations
with no errors**. The archived source commit was checked against the pinned
commit. The independent checker's printed theorem retains the four distinct
positive naturals and intersection cardinality of at least four.

Compact receipts: [axiom audit](verification/axioms.log),
[NaNoda result](verification/nanoda.log),
[printed definitions and target](verification/nanoda-statements.txt),
[export checksums](verification/CHECKER_SHA256SUMS),
[source archive checksum](verification/ARCHIVE_SHA256).
The underscore in NaNoda's pretty-printed theorem omits its proof term for
readability; the full proof closure was exported and checked.

[Artifact 10476086883](https://github.com/ketianzhang1-lang/jsp-000301-lean/actions/runs/35169128730/artifacts/10476086883):
4,289,506 bytes; ZIP SHA-256
`a2d65a174f1233c406f12952c2de1bd3b0ad865b5e234fe69894faad0384e777`.
API-reported expiration: 2026-12-16. The ZIP was downloaded and its digest
verified. The proof export and NaNoda configuration match the first run's
digests, consistent with the unchanged Lean source.

The checker script pins:

- lean4export: `6cea97789dc088ea47fcea15692db85685aedac5`.
- NaNoda: `4c544ed4099c8227f07d5de77ad1e69fb0740a27`.

NaNoda receives the entire exported proof dependency closure, with
`unpermitted_axiom_hard_error: true` and the three-standard-axiom allowlist.
Its artifact includes the serialized proof, SHA-256 digest, checker output,
printed target statement and source archive. Downloadable Actions artifacts
have retention limits; the source and reproduction scripts remain pinned.
No external human mathematical review or permanent third-party archive is
claimed. Machine verification does not establish a prize decision.

## Licenses and modifications

The original definition and theorem statement are attributed to The Formal
Conjectures Authors. This package replaces the upstream proof hole for the
k = 4 theorem with a concrete certificate, supporting finiteness proof and
cardinality argument under the `JSP000736` namespace. It does not import or
rely on the upstream open theorem. Proof and adapted code are Apache-2.0; see
[LICENSE](LICENSE). Upstream descriptions and mathematical credit remain
with their stated authors.

## Verification history

The initial [run 35168831936](https://github.com/ketianzhang1-lang/jsp-000301-lean/actions/runs/35168831936)
passed Lean, leanchecker and NaNoda (7,286 declarations), but log review found
that its optional `rg` source scan was skipped because ripgrep was absent.
Commit `b67c69abefe3daaeea454008e9ddadaf2c4adc1e` replaces that scan with an
assertion in the required Python audit. The Lean proof is unchanged. The final
run above is the authoritative receipt for the corrected audit script.
