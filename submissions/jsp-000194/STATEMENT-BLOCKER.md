# JSP-000194: statement-fidelity blocker

This file records why the existing JSP-000194 candidate cannot truthfully be
promoted to a complete formal proof by this update.

## The catalog does not freeze one proposition

The catalogue wording asks:

> How many ordinary lines, each containing exactly two of the points, must a
> finite noncollinear planar point set determine?

Its cited literature contains several non-equivalent quantitative results,
including Motzkin's square-root bound, the Kelly--Moser linear bound, and the
later asymptotic Dirac--Motzkin/Green--Tao classification.  The existing
candidate proves only the three-point specialization and explicitly labels it
as partial.  That finite specialization is not a source-faithful formalization
of the arbitrary finite-set question.

The possible targets are not interchangeable.  For example, a theorem that
there is one ordinary line, a theorem that there are at least three, Motzkin's
inequality, a `3n/7` bound, and an asymptotic sharp bound have different
quantifiers, conclusions, and proof obligations.  Choosing one silently would
turn a target-selection decision into a false claim of exact statement
identity.

## Reproducibility investigation

The pinned public Formal Conjectures file numbered `194` concerns chaotic
orderings of the rationals and reals; it is not the JSP ordinary-lines entry.
No pinned formal source in the assigned repository supplies the JSP-000194
ordinary-lines proposition or a complete quantitative proof.  A public Lean
formalization of the finite Sylvester--Gallai theorem supplies only existence
of an ordinary line, which is strictly weaker than the catalog's quantitative
question and cannot be used as a substitute.

Therefore no `sorry`-free Lean artifact is claimed here for JSP-000194.  The
existing observation and its scope are preserved.  Completion requires an
independent statement-adjudication decision selecting the exact source theorem
and a proof of that theorem; this file does not make that decision or provide
an assumed theorem.

## Sources

- [JSP-000194 catalogue entry](https://github.com/TheJustinSunPrize/awards/blob/aea6bf0c1b85e9ba4efe5b5b74231988d5e966a9/problems/catalog-0101-0200.md#JSP-000194)
- [Motzkin, *The Lines and Planes Connecting the Points of a Finite Set*](https://doi.org/10.1090/S0002-9947-1951-0041447-9)
- [Kelly--Moser, *On the Number of Ordinary Lines Determined by n Points*](https://www.cambridge.org/core/journals/canadian-journal-of-mathematics/article/on-the-number-of-ordinary-lines-determined-by-n-points/C2BBECD090CBA344F80C4B28AA45F2E3)
- [Green--Tao, *On sets defining few ordinary lines*](https://arxiv.org/abs/1208.4714)

No award, eligibility, recipient, or official verification claim is made.
