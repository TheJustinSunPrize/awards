# JSP-000092 near-linear formalization: draft intake

## English

This is a **draft observation candidate awaiting intake review**. It records
submitted public evidence, with no published decision and no activated formal
verification record. The related discussion is
[issue #110](https://github.com/TheJustinSunPrize/awards/issues/110); the
[formalization submission](https://github.com/TheJustinSunPrize/awards/issues/110#issuecomment-5702779062)
supplements that issue's mathematical note.

### Scope and attribution

The submitted theorem is `JSP092.erdos75_near_linear`. It concerns a graph with
both vertex cardinality and chromatic cardinality aleph-one. For every positive
real epsilon, a threshold uniform over all finite subgraphs yields an ambient
independent set of size strictly greater than `n^(1-epsilon)`.

The target is the affirmative right-hand proposition in the
[pinned Formal Conjectures Erdős 75 statement](https://github.com/google-deepmind/formal-conjectures/blob/40e7c98697de6f66b8cbdbf641749ab39ed9c152/FormalConjectures/ErdosProblems/75.lean).
The stronger fixed-linear question is outside this submission. The problem
bank's solution and eligibility fields are unchanged, and this draft records
no resolution date for the full problem.

The mathematical route follows Sections 2–5 of the
[note attached to issue #110](https://github.com/user-attachments/files/32296106/JSP-000092_submission.md):
the Specker triple graph, nested unbounded color fibers, recursive dyadic
coloring, finite coordinate ranking, and logarithm-versus-power asymptotics.
Earlier mathematical sources are credited in the
[implementation's statement contract](https://github.com/SphereDonout/lean-proofs/blob/e868aa77b273d3b0fd598eff499731ea105a29ef/jsp-000092/docs/statement-contract.md).
This submission offers formalization work for review and makes no mathematical
discovery-priority claim.

### Pinned source and submitted local evidence

- [Proof project](https://github.com/SphereDonout/lean-proofs/tree/e868aa77b273d3b0fd598eff499731ea105a29ef/jsp-000092),
  commit `e868aa77b273d3b0fd598eff499731ea105a29ef`.
- [Top-level theorem](https://github.com/SphereDonout/lean-proofs/blob/e868aa77b273d3b0fd598eff499731ea105a29ef/jsp-000092/JSP092/Main.lean).
- [Reproduction instructions](https://github.com/SphereDonout/lean-proofs/blob/e868aa77b273d3b0fd598eff499731ea105a29ef/jsp-000092/README.md).
- [Submitted verification report](https://github.com/SphereDonout/lean-proofs/blob/e868aa77b273d3b0fd598eff499731ea105a29ef/jsp-000092/docs/final-verification.md).

The submitted environment pins Lean `leanprover/lean4:v4.33.1`, Mathlib
`0df444a360eaa60ab8c11dca51a86af692955474`, and Formal Conjectures
`40e7c98697de6f66b8cbdbf641749ab39ed9c152`. The proof imports the coloring
support module without importing the admitted Erdős 75 theorem.

The submitted local run rebuilt project outputs with warnings treated as
errors and retained upstream dependency caches. It checked an exact target
transcription and 25 transitive axiom reports. The final theorem's reported
axioms are `propext`, `Classical.choice`, and `Quot.sound`. The separate AI-agent
semantic reviews are internal development reviews, not external human or
prize-authorized verification. No independent proof-kernel rerun or fully
isolated, cache-free dependency rebuild is claimed.

### External artifacts

The [GitHub release](https://github.com/SphereDonout/lean-proofs/releases/tag/jsp-000092-e868aa7)
has release ID `390180843` and tag `jsp-000092-e868aa7`, targeting the proof
commit above. These are versioned GitHub-hosted artifacts, not a DOI archive;
the hashes identify the exact submitted bytes.

| Artifact | Asset ID | SHA-256 | Bytes |
| --- | --- | --- | ---: |
| [Source archive](https://github.com/SphereDonout/lean-proofs/releases/download/jsp-000092-e868aa7/jsp-000092-e868aa7.tar.gz) | `568567733` | `fb798cf4f6e0ba9d07daaa46bfd386407be5f7d5c653da2413694fb2cb8ed2ee` | 34320 |
| [Build log](https://github.com/SphereDonout/lean-proofs/releases/download/jsp-000092-e868aa7/build-clean.txt) | `568567732` | `9441368d7388cf6c2587d4b9c35dd6408597a5079b2d8d84af06e05c5eb3a98d` | 1070 |
| [Axiom report](https://github.com/SphereDonout/lean-proofs/releases/download/jsp-000092-e868aa7/axioms.txt) | `568567726` | `62df5499dcc51e1b2781d911c56da0f2f920c18d6c36a439dd5604b6724dd937` | 6480 |

The release's [checksum file](https://github.com/SphereDonout/lean-proofs/releases/download/jsp-000092-e868aa7/SHA256SUMS)
lists the same artifact hashes. Large source and log artifacts remain external
to this awards repository.

### Review stage requested

This preliminary intake uses the observation draft template. The structured
verification fields and `verification/record.yaml` remain null. Before entering
the formal channel, maintainers must arrange an actually issued statement with
registered curator signatories and suitable verifier evidence, as required by
the repository's statement schema and record guide. No signatories, verifier
profiles, attestations, or review decisions are fabricated by this draft.

Requested review covers the near-linear scope, original-problem correspondence,
proof reproduction, mathematical attribution, and the submitted formalization
contribution. This draft does not constitute an award announcement.
