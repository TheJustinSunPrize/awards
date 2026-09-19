# JSP-000603: exact degree certificates for magic configurations

This package formalizes the degree formula and uniqueness of normalized weak magic
weights, then gives an executable rational certificate with a proof of its
correctness for finite real planar point sets. It includes the empty, singleton
and collinear cases. It is a scoped formal contribution to
[JSP-000603 / Erdős 735](https://www.erdosproblems.com/735).

**It does not prove the ABKPR geometric classification**, claim a new solution of
Murty's problem, or request that the catalog be marked fully formalized. The
underlying mathematical formula is already in Ackerman, Buchin, Knauer, Pinchasi
and Rote, *There are not too many magic configurations* (2008), final section on
weakly magic configurations. See [PRIOR_ART.md](PRIOR_ART.md).

## What is proved

For a noncollinear finite point set, let `k(a)` be the number of its determined
lines through point `a`, let `n` be the number of points, and set

```
R = sum_a 1/(k(a)-1)
Y = (n+R)/(1+R)
w(a) = (k(a)-Y)/(k(a)-1).
```

Every normalized weak magic weighting must equal `w`, including signed weights.
Positive weights exist exactly when the following finite, rational conditions hold:

```
n-1 < (1+R)(k(a)-1)                       for every point a
(|l|-1)(1+R) = (n-1) sum_{a in l} 1/(k(a)-1)  for every determined line l.
```

The complete theorem also handles sets of size at most one and wholly collinear
sets. Real solvability is equivalent to rational solvability, even when the
point coordinates are irrational. The geometric interface constructs every line
using Mathlib's `affineSpan` of two distinct points, proves pair uniqueness, and
connects the checker to a direct equal-positive-line-sum statement.

Key declarations in [MagicWeights.lean](MagicWeights.lean):

- `weight_eq_formula`, `weakMagic_unique` — forced weights and uniqueness.
- `magic_iff_degreeCertificate`, `magic_iff_all_cases` — exact finite criteria.
- `determinedLines_linearSpace` — genuine affine geometry to incidence bridge.
- `real_magic_iff_rational` — rational witnesses suffice.
- `accepts_iff`, `rejects_iff` — executable checker correctness.
- `geometric_accepts_iff_common_sum` — original equal-line-sum formulation.

`STATEMENT.md` gives the quantifiers and limits; `PROOF.md` explains the proof.
The two concrete Lean incidence examples are a five-point obstruction and the
seven-point failed-Fano table. Their coordinate realizations are checked in
Python, not proved individually in Lean.

## Reproduce

Requires Git, Python 3 and elan/lake. The toolchain is Lean **4.34.0**. Mathlib and
all transitive packages are pinned by `lake-manifest.json`; the Mathlib commit is
`5ed2965256430c3649e86755f9576b54eca72435`.

From this directory:

```sh
lake exe cache get Mathlib.Algebra.BigOperators.Fin Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic Mathlib.Basic.Real.Basic Mathlib.Data.Rat.BigOperators Mathlib.Data.Rat.Cast.Order Mathlib.Tactic.FieldSimp Mathlib.Tactic.Linarith Mathlib.Tactic.NormNum Mathlib.Tactic.Positivity
python3 tools/verify.py
```

The script checks dependency pins, builds the proof, audits every named theorem,
executes the Boolean checker, cross-checks 916 exact point configurations, and
runs `lake env leanchecker --fresh --verbose MagicWeights`.

The audit admits only the usual `propext`, `Classical.choice` and `Quot.sound`
axioms. There are no custom axioms, unfinished proofs, or native computation
shortcuts in the submitted Lean proof. The fresh replay uses Lean's official
kernel; it is not an independent implementation or organizer-designated review.
Cached dependency builds are used; a source rebuild of all dependencies is not
claimed. The verification logs and input hashes are in `verification/`.

## Exact rational-coordinate convenience tool

```sh
python3 tools/magic_certificate.py examples/five-points.json
python3 tools/magic_certificate.py examples/failed-fano.json
```

Input coordinates are integers or rational strings, never floating-point
approximations. A rejection reports the nonpositive candidate weights or failing
line sums. The Python implementation is supplementary and is not itself formally
verified. `tools/check_small.py` independently solves the line equations by exact
Gaussian elimination and checks the returned weights.

The Lean `accepts` function is executable on **supplied finite incidence data**.
Extracting those data from arbitrary real coordinates in `determinedLines` uses
classical decisions and is noncomputable. The theorem is not a claim that arbitrary
real inputs can be automatically decided by a numerical program.

Prepared with GPT/Codex assistance by public GitHub account `green3sf`.
No award eligibility, recipient confirmation, or first-formalization priority is claimed.
