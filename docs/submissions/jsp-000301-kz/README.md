# JSP-000301: formalization and verification evidence

## English

This is a submission for review of the Lean formalization component of
[JSP-000301](../../../problems/catalog-0301-0400.md#JSP-000301), not an award
announcement, an official verification record, or a claim to mathematical discovery
or first-formalization priority. Please determine whether this contribution remains
eligible under the published rules, taking earlier valid submissions into account.

Submitting public account: `ketianzhang1-lang`.
Proposed recipient placeholder: `RECIPIENT-JSP-000301-KZ-A`.
Recipient confirmation and attribution remain pending; the placeholder is specific
to this submission and does not identify any earlier submitter.

## Included proof and locked environment

The following files are copied unchanged from proof commit
`e1a17b0d6728b9d4929d1d4abd3721a27377369a` in the
[public proof repository](https://github.com/ketianzhang1-lang/jsp-000301-lean/tree/e1a17b0d6728b9d4929d1d4abd3721a27377369a):

- [JSP000301.lean](JSP000301.lean): complete definitions and proof.
- [lakefile.lean](lakefile.lean), [lean-toolchain](lean-toolchain), and
  [lake-manifest.json](lake-manifest.json): reproducible Lean/Mathlib project.
- [LICENSE](LICENSE): original MIT license for the mirrored source.
- [SHA256SUMS](SHA256SUMS): content hashes for these five files.

Lean is `v4.34.0`; Mathlib is pinned to
`5ed2965256430c3649e86755f9576b54eca72435`. The manifest fixes transitive
library revisions. Do not run `lake update` for locked-snapshot reproduction.

After checking out this PR, run from the repository root:

```sh
cd docs/submissions/jsp-000301-kz
sha256sum -c SHA256SUMS
lake exe cache get
lake build --wfail
lake env leanchecker JSP000301
```

The source repository's [pinned verification workflow](https://github.com/ketianzhang1-lang/jsp-000301-lean/blob/e1a17b0d6728b9d4929d1d4abd3721a27377369a/.github/workflows/ci.yml)
provides the additional NaNoda and project axiom-audit commands. The award repository's
record CI is not a substitute for running that proof verification.

## Statement fidelity and scope

In namespace `JSP000301`, the definitions are:

```lean
def Powerful (n : Nat) : Prop :=
  forall p : Nat, Nat.Prime p -> p ∣ n -> p ^ 2 ∣ n

def PerfectSquare (n : Nat) : Prop :=
  exists m : Nat, m ^ 2 = n
```

The main theorem `JSP000301.jsp_000301_counterexample` states existence of
`n : Nat` with `0 < n`, both `n` and `n + 1` powerful, and neither a square.
`JSP000301.jsp_000301_disproved` directly negates the universal catalog claim.
All quantifiers range over natural numbers. Positivity is an explicit hypothesis
rather than part of the local `Powerful` definition; `n + 1` is then positive too.
There are no additional hypotheses weakening the question.

The witness is `n = 12167`. The proof uses the catalog's factorizations
`12167 = 23^3` and `12168 = 2^3 * 3^2 * 13^2`, prime-divisor lemmas, and the
interval between `110^2` and `111^2` to exclude squares. It uses standard Mathlib
primality, divisibility, and arithmetic lemmas rather than new mathematical axioms.

This addresses only the stated yes/no question. It does not resolve the separate
counting question in Erdős problem #365 or any question about three consecutive
powerful numbers. The catalog's mathematical credit and unknown historical dates
are preserved.

## Observed verification evidence

[Run 13](https://github.com/ketianzhang1-lang/jsp-000301-lean/actions/runs/35131699133)
at the pinned proof commit completed successfully on September 16, 2026. It repeated
verification after committing the manifest produced by successful
[run 12](https://github.com/ketianzhang1-lang/jsp-000301-lean/actions/runs/35130895580).

| Check | Observed result in run 13 |
| --- | --- |
| `lake build --wfail` | Passed; project module freshly compiled. |
| Bundled `leanchecker` | Passed. |
| NaNoda v0.4.17 | Checked 188,335 declarations with no typechecker errors. |
| Separate project axiom-audit | Audited 9 declarations under `JSP000301`; all within `propext`, `Classical.choice`, `Quot.sound`. |

NaNoda also reported one pretty-printer error: `Unable to print axioms`. This is
not omitted or represented as an entirely error-free log: typechecking returned
success, followed by the successful separate project axiom audit. The source has
no `sorry`, `admit`, `native_decide`, or added axiom declarations.

The whole-environment NaNoda allowlist additionally includes `Lean.trustCompiler`.
The separate project audit allows only the three foundational axioms above. No
project dependency on `Lean.trustCompiler` or a native-evaluation axiom is accepted
by that project audit.

| Tool | Pinned revision |
| --- | --- |
| lean-action | `50fcf42d2e460296f1a34b402e990d1b24f8b596` |
| lean4export | `6cea97789dc088ea47fcea15692db85685aedac5` |
| NaNoda | `4c544ed4099c8227f07d5de77ad1e69fb0740a27` |
| axiom-audit | `46024e005996495c65ef609368e11ab39c4222e3` |

The workflow fixes tool checkout revisions to avoid the stale parser described in
[lean-action PR 177](https://github.com/leanprover/lean-action/pull/177), without
changing checker semantics. A more detailed
[verification report](https://github.com/ketianzhang1-lang/jsp-000301-lean/blob/a42d756719684060b39799db4f10be5ec7de142b/VERIFICATION.md)
is available at a pinned documentation commit.

External artifact: run 13's `lake-manifest` archive, ID `10461443614`, is 828 bytes
with reported ZIP SHA-256
`c156d8c61cbab5ca9a7b539bbfa078d4fc53e3c4781b2cb17f65bd941c3ae04c`.
Its [download record](https://github.com/ketianzhang1-lang/jsp-000301-lean/actions/runs/35131699133/artifacts/10461443614)
has limited retention. The actual manifest is also retained in the pinned source
commit and mirrored here; its own hash is in `SHA256SUMS`. No independently managed
permanent log archive is claimed.

## Verification limits and record handling

These are contributor-controlled, network-enabled GitHub-hosted Ubuntu runs using
upstream precompiled Mathlib cache files. They are not the Prize's designated offline
verification, a full rebuild of all dependencies, or an independent human review.
The Lean build and bundled leanchecker share a kernel implementation; NaNoda is a
separate implementation, but all were operated in the contributor's workflow.
Official statement review, isolation checks, minimum-safe-version approval, recipient
confirmation, priority adjudication, and award evaluation are still pending.

This PR deliberately does not create a candidate or award record, change catalog
eligibility flags, or supply reviewer signatures. In particular, the current award
schema requires a numeric original proposal year while JSP-000301's catalog says
that year is unverified. No year is invented to satisfy the schema. Please advise
how to record the submitted evidence under the maintainers' current intake process.
The files can be relocated to an appropriate record after that determination.

## Attribution, prior submissions, and conflicts

The mathematical counterexample predates this work. Attribution belongs to the
classical sources recorded in the catalog; their original historical priority is
not re-adjudicated here. This application concerns this project's formalization,
operation, and verification evidence only, not the mathematical-solver role.

OpenAI ChatGPT assisted with Lean source, documentation, and CI configuration under
the submitting account's direction. This is a self-submission, not a recommendation
from an independent reviewer. No third-party Lean proof file was copied; the source
uses Mathlib definitions, tactics, and lemmas under their upstream licenses.

Earlier filings include
[25](https://github.com/TheJustinSunPrize/awards/issues/25),
[64](https://github.com/TheJustinSunPrize/awards/issues/64), and
[156](https://github.com/TheJustinSunPrize/awards/issues/156), among others.
This submission does not contest their priority or claim that extra checker evidence
outranks an earlier valid formalization. Please determine whether any applicable
same-window or contribution-recognition provision covers this later submission;
no entitlement, award level, or payment allocation is asserted.

Recipient confirmation is pending. No private contacts, identity documents, or
payment information are included. Additional professional conflicts have not been
independently confirmed for this submission. The mirrored source retains its MIT
license; this review narrative is contributed under the repository's content license.
