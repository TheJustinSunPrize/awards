# Proof outline

The counting formula and uniqueness below follow the final “Weakly magic
configurations” discussion in ABKPR; the Lean implementation and checker packaging
were developed for this submission.

Let `Y` be the total normalized weight. Summing the line equations through point
`a` counts `a` exactly `k(a)` times and every other point once. Therefore

```
Y + (k(a)-1)w(a) = k(a).
```

For noncollinear configurations `k(a)>1`. Rearrange to
`w(a)=1+(1-Y)/(k(a)-1)` and sum over all points. With
`R=sum 1/(k(a)-1)`, this yields `Y=(n+R)/(1+R)` and the forced weights.

Substituting the formula into positivity and each line equation, and multiplying
only by proved-positive denominators, yields `DegreeCertificate`. Necessity uses
the incidence identity; sufficiency simply verifies the explicit candidate on
**every** determined line. In particular, positivity alone is insufficient.

The remaining formal steps are:

- The two-points/one-line incidence property implies that, unless the entire
  point set is one line, each point has at least two lines through it.
- If the full point set is a line, uniqueness of the line through two points
  forces it to be the only line. Uniform weights `1/n` work. Sets of size zero
  or one determine no lines and are handled separately.
- Mathlib's affine-line uniqueness theorem verifies the incidence condition for
  arbitrary injective point configurations. Thus the combinatorial assumptions
  are proved for the geometric application.
- The degree formula commutes with rational-to-real coercion. This supplies a
  rational solution whenever a real solution exists, with degenerate cases
  treated separately.
- Dividing any positive common-line-sum weighting by its common sum gives the
  normalized formulation. The converse takes common sum one.

The example proof terms use ordinary simplification, arithmetic normalization and
kernel computation. The executable evaluation is also recorded, but evaluation
output is not used as an axiom or a replacement for the proof terms.
