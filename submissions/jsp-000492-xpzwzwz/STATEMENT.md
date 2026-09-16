# JSP-000492 / Erdős 605 — statement and prior-art audit

Statement correspondence and prior-art review, checked 2026-09-17. Local build and audit results are recorded separately in `evidence/`.

## Earlier formalization

The official repository already has [Issue 16](https://github.com/TheJustinSunPrize/awards/issues/16), a batch registration of eighteen existing proofs, explicitly including JSP-000492 / Erdős 605. It reports a complete proof of the same repeated-distance question, using the unit sphere and common distance √2, with a function tending to infinity and configurations for every n. A search of PR titles alone misses this submission.

The immutable source is [Erdos605.lean at commit 8822f7ddef30fadbd92e1c6ab4ed897af356af5e](https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos605.lean). The source was successfully retrieved during this audit. Its construction already uses exactly the point/line grid and the scale function described below. Its header credits the informal proof to Paul Erdős, Dean Hickerson, and János Pach, and the formal proof to Codex and GPT-5.6 Sol.

Issue 16 reports SHA-256 `61b4bbf881f9228d5e99077f2f53792c0ec5c0e6d835b67bb4985e421a0488ac`, a successful compile at 2026-09-16 17:41:19 +08:00, successful target-module replay at 17:41:38, and axiom set `[propext, Classical.choice, Quot.sound]`. These are the submitter's recorded checks; this audit did not independently rebuild that source.

The public GitHub issue-search API queries `repo:TheJustinSunPrize/awards 605`, `"Erdos605"`, and `"erdos_605"` each returned Issue 16. The broader query `repo:TheJustinSunPrize/awards 492` returned an unrelated PR because it did not reliably match the padded identifier. Search-engine queries did not locate a separate proof, which is not evidence of absence.

Consequently this work cannot be described as a first formalization or an unsubmitted problem. This additional implementation discloses the existing proof and issue. It contributes a modular standalone package and explicit all-large-size threshold, without claiming a new mathematical route. No prize eligibility or priority is established here.

## Mathematical statement

[Erdős Problem 605](https://www.erdosproblems.com/605) asks whether spherical n-point configurations can have a number of pairs at one common distance whose ratio to n tends to infinity. The [LaTeX statement](https://www.erdosproblems.com/latex/605) has no requirement that every prescribed radius or every prescribed distance be handled.

Write `C_d(S)` for the cardinality of the set of unordered two-element subsets `{p,q}` of S with Euclidean distance d. A sufficient strong form is:

For every natural K, there is a natural N such that, for every n ≥ N, there is a finite subset S of the unit sphere in ℝ³ with `|S| = n` and `C_√2(S) ≥ K*n`.

The eventual quantifiers express divergence of the achievable ratio and imply the original existence-of-f question. Fixing the unit sphere and √2 is an additional property of this construction, rather than a restriction present in the original question. Use `repeatedDistanceCount` or a distance-parameterized count: calling this `unitDistanceCount` while its defining distance is √2 would be misleading.

An explicit all-n witness is available. Let `m(n)` be the largest nonnegative integer m with `3*m^3 ≤ n`, and set `f(n) = (m(n) / 24 : ℕ)` viewed as a real number (integer division, as in `quota`). Then `m(n) → ∞`; for positive m(n), maximality and `(m+1) ≤ 2*m` give `n < 3*(m+1)^3 ≤ 24*m^3`. Since `24*f(n) ≤ m(n)`, this gives `f(n)*n ≤ m^4`. For m=0 the desired lower bound is zero. Arbitrary additional distinct sphere points provide exactly n points while retaining all selected pairs.

## Finite construction and required checks

For a positive integer m, normalize the following nonzero vectors to norm one:

* Point vectors `P(x,y) = (x,y,1)` for `0 ≤ x < m`, `0 ≤ y < 2*m^2`: there are `2*m^3` of these.
* Line vectors `L(a,b) = (a,-1,b)` for `0 ≤ a < m`, `0 ≤ b < m^2`: there are `m^3` of these.

Normalization is injective within each family: the fixed coordinate 1 or −1 determines the positive scale. The families are disjoint because the point vectors have nonnegative second coordinate while the normalized line vectors have negative second coordinate. The union consequently has exactly `3*m^3` points.

Each triple `(a,b,x)` in the indicated ranges defines an incidence with `y=a*x+b`. Since `a*x+b ≤ (m−1)^2+(m^2−1) < 2*m^2`, that point occurs in the grid. The dot product is `a*x−y+b=0`. After normalization both vectors have norm one and their distance is √2.

There are `m*m^2*m=m^4` triples. Each defines a different unordered pair: disjointness of the point and line families prevents swapping the two roles, and injectivity recovers both indices. Counting ordered pairs or allowing coincident endpoints would not suffice. Other pairs may also have distance √2; only a lower bound of m^4 is claimed.

## Radius versus diameter discrepancy

The remarks on the Erdős Problems page use `D>1`, call D a radius, and attach the exponent 4/3 to `u_√2`. This appears to be a radius/diameter terminology error, rather than a different normalization that our proof should attempt to follow.

The original [Erdős–Hickerson–Pach 1989 publisher abstract](https://doi.org/10.1080/00029890.1989.11972243) states the special construction on the unit sphere at distance √2. Scaling its distances to one makes the sphere radius `1/√2` and diameter √2. The [Swanepoel–Valtr author PDF](https://personal.lse.ac.uk/swanepoe/swanepoel-valtr-unitdistance.pdf) explicitly uses **diameter D > 1** in its abstract. An [author-hosted survey by Pach](https://www.renyi.hu/~pach/publications/chap1.pdf) likewise identifies the exceptional sphere radius as `1/√2` for unit distances.

Accordingly, a correct description is “unit sphere, distance √2”, or after proving the scaling step, “sphere of radius 1/√2, unit distance”. Do not claim unit-distance bounds on radius √2, the result for every prescribed radius/diameter, the general √log n improvement, a matching upper bound, or the full contents of either paper.
