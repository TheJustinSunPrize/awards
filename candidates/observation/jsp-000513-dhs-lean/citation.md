# JSP-000513: additional Lean formalization submitted for review

## English

This is a **draft observation candidate**, requesting review of an additional
complete Lean implementation. It records no award, eligibility determination,
formal verification approval, or first-formalization priority.

The mathematical result is Theorem 2 of Dvorak, Hu and Sereni,
[A 4-choosable graph that is not (8:2)-choosable](https://arxiv.org/abs/1806.03880v2),
[Advances in Combinatorics (2019), Paper No. 5](https://doi.org/10.19086/aic.10811).
It supplies a finite graph G which is (4:1)-choosable but not (8:2)-choosable,
answering the doubling question in JSP-000513 negatively.

### Submitted implementation

- [Pinned proof source](https://github.com/MoringSatr/jsp-prize-000513/tree/0cb53aef1dd9410732dfb74c2ff03093d826688c).
- [Exact main theorem](https://github.com/MoringSatr/jsp-prize-000513/blob/0cb53aef1dd9410732dfb74c2ff03093d826688c/JSP000513/Uniformization.lean).
- [Statement and construction review](https://github.com/MoringSatr/jsp-prize-000513/blob/0cb53aef1dd9410732dfb74c2ff03093d826688c/docs/FORMALIZATION.md).
- [Build, axiom, export and replay logs](https://github.com/MoringSatr/jsp-prize-000513/tree/0cb53aef1dd9410732dfb74c2ff03093d826688c/docs/verification).
- Final theorem: `JSP000513.jsp000513` in `JSP000513/Uniformization.lean`.
- Lean 4.22.0; mathlib v4.22.0, commit `79e94a093aff4a60fb1b1f92d9681e407124c2ca`.
- Full proof chain: Lemma 3, Corollary 4, Lemmas 5–8, and the final uniformization.
- Local build and all 89 public theorem axiom reports passed. The final theorem
  reports only `propext`, `Classical.choice`, and `Quot.sound`.
- Replay of all 17 project modules with `lean4checker` v4.22.0, commit
  `0531c5e62c6bbc21af6c8b4adc2a16d201bf8b65`, passed with exit 0. This is the
  same Lean kernel operating against imported environments, not a second
  independently implemented checker or a fresh replay of all mathlib.
- Positive component results quantify over arbitrary color types. Half-lists
  constrain cardinalities only. The final statement explicitly requires a finite
  vertex type and quantifies over all lists of the stated size.
- The concrete G5 gadget has 37 vertices, proved in Lean. It is not identified
  with the final, larger counterexample graph.

The implementation was developed with Codex assistance. Reproduce with
`./scripts/bootstrap`, `./scripts/check reproduction`, and `./scripts/replay`.

[Versioned source-and-evidence archive](https://github.com/MoringSatr/jsp-prize-000513/releases/download/proof-v1/jsp-prize-000513-0cb53ae.tar.gz):
34,756 bytes; SHA-256 `d721353b6bf259f5d3dcf789e00e742de5822fc4baee3e3419151e5010c50638`.
This GitHub release identifies the exact bytes supplied for review; it is not
represented as a DOI or as satisfying a permanent-archive requirement.
Per-file hashes are also pinned in `docs/source-sha256.json` in the proof source.

### Existing work and requested handling

[Issue #16](https://github.com/TheJustinSunPrize/awards/issues/16) already registers
another complete proof of this result, from
[plby/lean-proofs at 8822f7ddef30fadbd92e1c6ab4ed897af356af5e](https://github.com/plby/lean-proofs/tree/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos632).
This submission is an additional implementation, not a duplicate problem
recommendation, and does not supersede that attribution or its earlier registration.
Please assess whether this additional work merits recording or any formalization
credit under the published rules. No reward or share is requested for mathematical
discovery. No first-formalization, novelty, or priority entitlement is asserted.

The 2019 mathematical resolution date is preserved. The new implementation and
local checks were completed in 2026; their relevance to any achievement-date
criterion is for the organizers to decide. This PR leaves the catalog's claim
flags and all announced award records unchanged.

### Verification boundary

The local build is evidence for review, not the repository's completed verification
record. `verification.formal` and `verification/record.yaml` remain null because
authorized curator signatures, an independent implementation check, safe-version
approval and independent statement review have not been issued. A source-side
statement review is not substituted for the repository's two-curator statement
process. No signatures or reviewer identities are manufactured.

The version pins document the environment actually checked; no minimum-safe-version
or current-release compliance is asserted. Contributor-prepared logs are separate
from independent review. Permanent archival confirmation and any further isolation
requirements remain for review. The candidate can advance only through the normal
verification and attribution process.
