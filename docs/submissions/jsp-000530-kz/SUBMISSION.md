# Contribution for JSP-000530 / Erdős 654

## Requested review

Please assess the attached Lean formalization of the known negative answer
to the strong no-four-concyclic version of Erdős 654. In the prize catalog
this is a scoped component of JSP-000530. The version that additionally
forbids three collinear points is not claimed.

Proposed recipient: `RECIPIENT-JSP-000530-KZ-A`, confirmation pending.
The contribution is submitted by the connected public GitHub account with
OpenAI ChatGPT assistance. Mathematical credit remains with Aletheia and
the authors of the published account. The even/odd coordinate adaptation
and Lean implementation are described in README.md.

This is a self-submission for review of formalization work. No new
mathematical discovery, global first priority, independent human sign-off,
official approval, award allocation, or right to payment is asserted.

## Statement fidelity

`counterexample_family` proves the following for **every natural m**:

- S is a finite subset of the standard Euclidean complex plane.
- S has exactly 4m distinct points.
- Every circle with any center and radius contains at most three points of S.
- Every p in S has at most 3m-1 distinct distances to S excluding p itself.

`not_asymptotically_all_distances` then negates the epsilon/N formulation
of the claim that a point must see (1-o(1))n distances. Its witness uses
epsilon = 1/8 and m = N+1, so it gives arbitrarily large counterexamples.

No geometric conclusion is assumed, and the geometry is not replaced by
an abstract distance table. `sqDist_eq_dist_sq` links the coordinate algebra
to Mathlib's Euclidean distance on the complex plane. `NoFourConcyclic`
quantifies over all actual metric circles. The final theorem has no
unproved mathematical hypotheses.

## Original sources and overlap

- Prize record: https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0501-0600.md#JSP-000530
- Original problem: https://www.erdosproblems.com/654
- Published account: https://arxiv.org/abs/2601.22401v3, Section 3.1.
- Raw original model transcript (consult with the corrections in the published
  account): https://github.com/google-deepmind/superhuman/blob/main/aletheia/Erdos/Erdos.tex

The no-three-collinear version is specifically excluded. The raw transcript's
claim about that version was rejected in the published account and is not
used. The proof also does not require the raw transcript's unnecessary
claim that cross-axis distances are irrational.

At the search checkpoint, no matching award-repository pull request was
returned for JSP-000530 / Erdős 654. This limited check is not a claim of
worldwide first formalization. Earlier contributions submitted by the same
account concern JSP-000301, JSP-000390, JSP-000391, and JSP-000924 and are
separate problems. Existing prize records are left unchanged.

## Package

The proof, dependency lock, compiler version, audit commands and checker
scripts are included here. SOURCE_SHA256SUMS covers the files copied from
the proof project. Verification results and their limitations are recorded
in VERIFICATION.md. All additions are confined to this submission directory.
