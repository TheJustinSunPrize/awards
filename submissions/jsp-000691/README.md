# JSP-000691 / Erdős 835: composite-successor obstruction

## English

This submission formalizes the known Ma–Tang necessary condition: for `k ≥ 1`,
if the `k`-subsets of a `2k`-element set admit `k+1` colours such that every
`(k+1)`-subset contains all colours, then `k+1` is prime.

This is a **partial-result formalization**. It does not settle Erdős 835, does
not construct a colouring for any `k > 2`, and does not exclude the remaining
prime-successor cases. Mathematical discovery is credited to Jie Ma and Quanyu
Tang; the submission requests review of the new Lean formalization contribution.

The exact `Erdos835.Property` definition is reproduced from Formal Conjectures
under Apache-2.0. Its unproved assertions are not imported.

## Reproduction

Install Elan, then run from this directory:

```sh
lake exe cache get Mathlib.Combinatorics.Enumerative.DoubleCounting Mathlib.Data.Finset.Powerset Mathlib.Data.Fintype.Powerset Mathlib.Data.Nat.Choose.Lucas Mathlib.Tactic.Tauto Mathlib.Tactic.NormNum
lake build
lake env lean -DwarningAsError=true Prize835.lean
python3 scripts/verify.py
lake env leanchecker --verbose --fresh Prize835
```

The toolchain and all dependency revisions are pinned. See
[the statement correspondence](STATEMENT.md),
[attribution and prior-art screening](PRIOR_ART.md), and
[verification evidence](evidence/verification.json).

Local build, axiom audit, three negative controls, and
[fresh-environment kernel replay](evidence/kernel-replay.json) passed. The replay
uses the bundled Lean kernel, not an independently implemented checker. Pinned
upstream caches were used; a complete source rebuild of mathlib and independent
human review are not claimed.

## Requested review

Please assess eligibility for the Lean formalization role under Section 5 of
the published prize rules, including whether this 2026 formalization of a known
partial result qualifies. No award, priority determination, tier, or payment is
asserted. The proposed recipient is `RECIPIENT-jsp-000691-A`, pending confirmation.
This is a self-submission prepared with ChatGPT assistance; the applicant has a
direct interest in the award outcome. No solver-role allocation is requested.

This package proposes an intake location for the Lean-containing PR. It does
not change the catalogue's open status, eligibility flag, any candidate record,
or any award record. Independent designated verification, recipient confirmation,
and committee adjudication remain pending.
