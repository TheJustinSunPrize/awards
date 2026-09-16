# JSP-001007: half-residue sieve counterexample — formal evidence

## Scope and attribution

This submission formalizes the negative answer described in
[JSP-001007](catalog-1001-1022.md#JSP-001007), corresponding to
[Green's Problem 44](https://people.maths.ox.ac.uk/greenbj/papers/open-problems.pdf#page=22)
and the counterexample case of [Erdős #1202](https://www.erdosproblems.com/1202).

The mathematical construction is attributed to Liam Price and GPT-5.4 Pro,
[A Counterexample to a Half-Residue Sieve Bound](https://www.overleaf.com/read/qyhdmrchqnvb),
as in the existing catalog. This is an AI-assisted formalization submission;
no new mathematical discovery or first-publication priority is claimed.

## Theorems and correspondence

The self-contained package is in [submissions/jsp-001007](../submissions/jsp-001007/README.md).
Its [pinned source](https://github.com/tester-lean/awards/tree/f26433803cfbd924569aebbdcc1c39321ecb9971/submissions/jsp-001007) is commit `f26433803cfbd924569aebbdcc1c39321ecb9971`.

`JSP001007.green44_counterexample` proves that, for every positive k and all
sufficiently large N, there are k distinct increasing primes p_i and forbidden
residue-class sets A_i such that:

- p_i^10 < N^9, equivalently p_i < N^(9/10).
- Each A_i has exactly (p_i-1)/2 elements in ZMod(p_i).
- More than N/10 integers in [1,N] avoid every A_i.

In particular this refutes the k=1000 question in Green's list.
`JSP001007.not_green44_conjecture` additionally proves the direct negation of the
package's recorded conjecture at epsilon=1/10. It handles k=0 and proves the
conversions between natural-number division and real density, and between
integer powers and the real prime bound. No conjectural prime-distribution
hypothesis remains: the package includes a proved Chebyshev-type count bound,
a clustering argument, and the final numerical assembly.

The package does not claim the positive large-sieve theorem for primes below
N^(1/2), or every stronger quantitative result from the mathematical write-up.

## Verification

- Lean: 4.35.0-rc1.
- mathlib: `96f4f6ca6e9dcdb26fec36ec10fa90c7f424e94d`.
- Six source modules plus the library entry point built successfully.
- Five key theorem audits use only `propext`, `Classical.choice`, and `Quot.sound`.
- nanoda 0.4.17 independently checked both final endpoints and their full exported
  dependency closure: **43,725 declarations, no errors**.
- The checker permits only those three axioms, with unpermitted axioms treated
  as hard errors. It uses the normal Nat and String reduction extensions.
- Exporter: `leanprover/lean4export@fd0d78eaa91750096cf519907b266efb1b26bf22`.
- Checker: `ammkrn/nanoda_lib@4c544ed4099c8227f07d5de77ad1e69fb0740a27`.

[Build, audit, and checker logs](../submissions/jsp-001007/VERIFICATION.md),
[exact metadata](../submissions/jsp-001007/evidence/metadata.json),
and [reproduction scripts](../submissions/jsp-001007/README.md#build) are included.
The source was rebuilt in a separate review workspace using pinned upstream
caches. The submitter ran the automated checks; independent human statement
review and any curator verification remain pending.

## Archived artifacts

[Evidence archive](https://github.com/tester-lean/awards/releases/download/jsp-001007-v1/jsp-001007-evidence.tar.gz)
([release](https://github.com/tester-lean/awards/releases/tag/jsp-001007-v1)):

- Archive ID: `tester-lean/awards@jsp-001007-v1/jsp-001007-evidence.tar.gz`.
- SHA-256: `4a9d722b7f54898aeee4a5e9ac15916471505d07a065c9fa664d909f97b40125`.
- Bytes: `42470298`.

The archive contains the pinned proof source, theorem export, strict checker
configuration, verification logs, and dependency licenses. Export hash and size
are recorded in the included metadata. First-party proof code is Apache-2.0;
third-party licenses and attribution are retained.

## Intake status

The proposed Lean status is **Yes**, backed by the pinned proof and automated
checks. Eligibility is **Pending verification**, and claim status remains
**Unavailable** while intake is pending. These are screening fields; no formal
candidate record, confirmed recipient, award level, or payment is asserted.
Recipient confirmation uses a placeholder until the required evidence is supplied.
