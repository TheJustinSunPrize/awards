# References and dependency map

## Original problem

- P. Erdős and G. Purdy, *Some extremal problems in geometry*, Journal of
  Combinatorial Theory, Series A 10 (1971), 246--252,
  [DOI 10.1016/0097-3165(71)90028-8](https://doi.org/10.1016/0097-3165%2871%2990028-8).
  This is the primary source already cited by the catalog entry.

## Equal-distance quadruples

- L. Guth and N. H. Katz, *On the Erdős distinct distance problem in the
  plane*, Annals of Mathematics 181 (2015), 155--190,
  [published PDF](https://annals.math.princeton.edu/wp-content/uploads/annals-v181-n1-p02-p.pdf),
  [arXiv:1011.4105](https://arxiv.org/abs/1011.4105).

  Proposition 2.2 proves `|Q(P)| = O(n^3 log n)`. Its definition (2.1) is the
  same ordered quadruple convention used in [PROOF.md](PROOF.md):
  `(p_1,p_2,p_3,p_4) in P^4` with
  `d(p_1,p_2) = d(p_3,p_4) != 0`, without requiring all four entries to be
  distinct.

## Isosceles-triangle count

- N. H. Katz and G. Tardos, *A new entropy inequality for the Erdős distance
  problem*, Contemporary Mathematics 342 (2004), 119--126,
  [author-hosted PDF](https://www.renyi.hu/~tardos/katz.pdf).

  Corollary 8 proves, for every positive `epsilon`, an upper bound

  \[
  O\left(n^{(117-34e)/(55-16e)+\epsilon}\right)
  \]

  for the number of isosceles triangles determined by `n` planar points. The
  submission only changes the convention by marking the apex (a factor of at
  most three) and separately adds at most `binom(n,2)` collinear midpoint
  configurations.

The exact identity, the equivalence reduction, and the bounded-collinearity
corollary are proved directly in this submission. No uncited asymptotic result
is used.
