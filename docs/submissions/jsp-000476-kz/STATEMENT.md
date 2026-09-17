# Statement correspondence and limitations

## Original problem

JSP-000476 asks for the largest size of a subset of {1,...,N} having no
nonempty subset whose sum is a square. Nguyen–Vu, *Squares in sumsets*,
arXiv:0811.1311v2, Question 1.1 and Theorem 1.4, describe the problem and
its n^(1/3+o(1)) solution. Example 1.2 attributes the prime-multiple
lower-bound construction to Erdős.

## Definitions and quantifiers

- `multiples p m` is the Finset image of i=0,...,m-1 under p*(i+1).
  For positive p, the proved `multiples_card` gives cardinality exactly m.
- `SquareSumFree A` quantifies over every Finset S included in A and
  requires S to be nonempty. It excludes equality with x^2 for every
  natural x. Finsets implement distinct summands, as required.
- `PowerSumFree A` has the same quantifiers and excludes x^k for every
  natural x and every integer exponent k>=2 represented as a natural.
  Its square case is proved explicitly.
- `triangle m` is the sum of 1 through m. `triangle_double` establishes
  2*triangle m = m*(m+1), without natural-division rounding issues.
- `exact_criterion` assumes only primality of p, and applies to every m,
  including zero. It states a necessary and sufficient condition for
  this particular family, not for arbitrary sets of m integers.
- `cubic_lower_bound` quantifies over all N,m with 2*m^3<=N and produces
  a set of cardinality exactly m contained in [1,N]. Its property is
  stronger than the square-free subset-sum property in the original
  problem. The case m=0 gives the empty set and is explicitly handled.

## Claimed contribution

The package establishes the classical construction uniformly, gives an exact
failure witness when the triangular coefficient bound reaches p, and states
perfect-power avoidance in the same independently written proof.
The upper bound for arbitrary sets is outside its scope. No equivalence to
Nguyen–Vu's full asymptotic theorem, first-formalization claim, or new
mathematical discovery is asserted. An existing plby formalization is linked
and attributed in README.md. Assessing incremental eligibility and overlap
requires organizer review.

## Review status

Contributor-side statement comparison only. No independent human review,
committee approval, recipient confirmation, catalog status change or award
is claimed by this submission. Lean and NaNoda checking establish the stated
formal theorem relative to their trusted bases; they do not themselves
establish award eligibility.
