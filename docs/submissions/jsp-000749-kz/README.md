# JSP-000749: classical Property B upper bound (scoped component)

## Contribution and precise scope

Submit a complete Lean formalization of the known all-parameter upper-bound component of JSP-000749 / Erdos Problem 901. For every natural n>=2, the proof gives `0 < m(n) <= 4*n^2*2^n`, where m(n) is the least edge count of a finite simple n-uniform hypergraph of weak chromatic number exactly three. The minimum is proved attained and positive. The existence theorem gives a family on `Fin (2*n^2)` with at most the displayed number of distinct edges, and every proper edge subfamily is two-colourable.

**This is not a solution of the full precise-growth problem, an improvement of the known bound, or an optimal constant.** It is a known-result formalization contribution. Minimality is for edge subfamilies; vertex-criticality is not claimed because isolated vertices may remain. No mathematical discovery, global first-formalization priority, award tier or payment entitlement is asserted.

The new code was independently written with OpenAI ChatGPT assistance under the submitting account's direction. Original mathematics remains credited to Erdos and the cited literature, and Mathlib contributors retain infrastructure credit. Proposed recipient placeholder: `RECIPIENT-JSP-000749-KZ-A`, confirmation pending. This is a self-submission with a direct interest in the outcome, not independent human certification.

## Statement correspondence

- `JSP000749.jsp000749_upper_bound`: all-parameter existence, uniformity, explicit edge bound, exact weak chromatic number three, and edge-subfamily minimality.
- `JSP000749.m_attained`, `m_positive`, `m_upper_bound`: genuine attained positive minimum and its bound.
- `JSP000749StatementCheck.plain_upper_bound`: a separate explicit finite-set/colour-function endpoint, independent of the names of our custom predicates. The adapter is contributor-written, not an independent review.

Edges and the edge family are both ordinary finite sets; repetitions cannot inflate cardinalities. Colourability uses actual functions into `Fin k` and demands two differently coloured vertices in each edge. The n>=2 premise is not omitted. The proof quantifies over every n>=2 and every colouring, rather than checking finitely many numerical cases.

See [PROOF.md](PROOF.md) for the argument and semantic details. The finite tuple-counting proof establishes the probabilistic existence bound without importing random simulations, solver certificates, unproved estimates or native-computation proof axioms. The minimal-obstruction reduction supplies exact three-colourability.

## Verified public source

Pinned source: [ketianzhang1-lang/jsp-000301-lean at fddb23254d8b8530ce2bac9b9e50304557349512](https://github.com/ketianzhang1-lang/jsp-000301-lean/tree/fddb23254d8b8530ce2bac9b9e50304557349512/projects/jsp-000749).

[Public proof CI](https://github.com/ketianzhang1-lang/jsp-000301-lean/actions/runs/35173096659) passed the Lake build with warnings as errors, six bundled kernel replays, twelve target axiom audits, actual dependency-pin checks, false-arithmetic control, finite diagnostics and strict-allowlist NaNoda. NaNoda checked **14,502 declarations with no errors**. The unchanged proof/configuration/script/license files are identified by `SOURCE_SHA256SUMS`; the compact public-run logs/configuration have `EVIDENCE_SHA256SUMS`.

See [VERIFICATION.md](VERIFICATION.md) for exact source identity, artifact hash and finite retention, tools and trust boundaries. These are contributor-run checks, not designated organizer verification, independent human approval, or an award decision. The source commit's initial README predates completed CI; this submission receipt records the later observed results.

## Reproduction

Use the pinned Lean 4.34.0 toolchain and committed nine-package manifest. From this directory:

```sh
sha256sum -c SOURCE_SHA256SUMS
sha256sum -c EVIDENCE_SHA256SUMS
lake exe cache get
bash scripts/verify.sh
bash scripts/verify_nanoda.sh
```

The seven compact logs/configuration files were copied byte-for-byte from the successful public run. New reproductions write to `evidence/ci/`, preserving the submitted historical logs in `evidence/public/`. The full source archive, checker export, statements and build logs remain in the linked artifact and the contributor backup. No full-library offline rebuild is claimed.

## Sources and prior-work disclosure

- P. Erdos, *On a combinatorial problem. II*, Acta Math. Acad. Sci. Hungar. 15 (1964), 445-447: https://doi.org/10.1007/BF01897152
- Duraj, Kozik, Shabanov, *Random hypergraphs and property B*, which records the classical bound and sharper asymptotic coefficient: https://arxiv.org/abs/2102.12968
- Original question: https://www.erdosproblems.com/901
- Official catalog: https://github.com/TheJustinSunPrize/awards/blob/f4e7173d89dfe91022a185427d63452c8ffbf6ae/problems/catalog-0701-0800.md#JSP-000749
- Prior incomplete public statement/attempt: https://github.com/rjwalters/lean-genius/blob/main/proofs/Proofs/Erdos901Problem.lean . Its main upper-bound proof contained `sorry` when inspected. This source is acknowledged but not imported, copied or relied upon; its other claims are not assumed correct.

Bounded official Issue/PR and public code searches did not identify an earlier matching completed upper-bound implementation. Search indexing and alternate names limit that finding; it is not a certificate of global priority. No attempt is made to reserve priority using an unfinished official PR.

## Requested handling

Please review statement fidelity, attribution, prior overlap, formalization contribution, appropriate intake placement and eligibility for this known upper-bound component. This evidence directory does not modify catalog flags, candidate/award records, recipient profiles, curator signatures, existing decisions, or payment statuses. Formal verification and any prize evaluation remain with the designated organizers.
