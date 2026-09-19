# JSP-000780 / Erdős 939: infinitely many 3-powerful triples

This package proves the entire solved **triples subquestion** of Erdős 939:
there are infinitely many positive coprime 3-powerful triples `a + b = c`.
It supplies a new Lean proof of known mathematics, using Nitaj's 1995 seed
and a specialization of Cohn's 1998 transformation.

The separate higher-exponent questions in Erdős 939 are not resolved here.
Cohn's stronger requirement that none of the entries is a cube is not claimed.
The existing Price/Aristotle proof for exponents `r ≥ 6` is separate prior art
and is not claimed as this applicant's contribution.

## Reproduction

Install Elan and Python, then run in this directory:

```sh
lake exe cache get Mathlib.Algebra.GCDMonoid.Finset Mathlib.Algebra.GCDMonoid.Nat Mathlib.Data.Nat.PrimeFin Mathlib.Data.Nat.GCD.Basic Mathlib.Data.Set.Finite.Lemmas Mathlib.Tactic.NormNum Mathlib.Tactic.Ring Mathlib.Tactic.Positivity Mathlib.Tactic.Linarith
lake build
lake env lean -DwarningAsError=true Prize939.lean
python3 scripts/verify.py
lake env leanchecker --verbose --fresh Prize939
```

Lean and dependency revisions are pinned. See [statement correspondence](STATEMENT.md),
[prior-art screening](PRIOR_ART.md), and [verification evidence](evidence/verification.json).
The final statement matches the pinned Formal Conjectures triples variant,
with `answer(True)` reduced to `True`. Its unproved results are not imported.

Checks use cached pinned dependencies. Fresh replay uses the bundled Lean
kernel; a full mathlib source rebuild, independently implemented checker,
and independent human verification are not claimed.

## Requested review

Please assess this 2026 formalization of a known, fully proved subquestion
under Sections 2.5, 4.2, and 5 of the
[published rules](https://www.hejustinsun.com/prize/rules).
The applicant requests consideration for the **Lean formal verifier role
(30% of an eligible awarded allocation)**, not the mathematical solver role.
The seed, construction, infinitude theorem, and matching statement are parts
of this single contribution, not separate payment requests.

The proposed recipient is `RECIPIENT-jsp-000780-A`, pending confirmation.
This is a self-submission prepared by the applicant with ChatGPT assistance;
the applicant has a direct interest in its award outcome.
Catalogue inclusion and a successful Lean build do not establish eligibility,
priority, award tier, or payment. All remain subject to designated review.
This intake package changes no catalogue, candidate, recipient, or award record.
