# Statement and scope review

Review date: 2026-09-16. This is a submitter-side, AI-assisted review, not an organizer's signature or an external referee certificate.

Reviewed canonical source: `Erdos466.lean`, SHA-256 `1e4c3c35392b21578cf3f620b56dc3dee6f0db3c3040d9b1afca92a2d0c2a20a`.

## Correspondence checks

- The ambient space is the standard two-dimensional real Euclidean space; distances use its standard metric.
- `distToInt` uses nearest-integer rounding. The interval lemma bounds the distance from every integer; the endpoint lemma identifies the non-strict half-integer case.
- `Realizable` requires injective points and the original pairwise condition `delta <= distToInt (dist ...)`, not an assumed conclusion, restricted configuration class, or strict substitute at the endpoint.
- The construction has integer coordinates, but the upper bound applies to arbitrary real planar configurations.
- The finite-cardinality bound is uniform over disk centers: it translates points to a disk centered at zero before applying a finite compactness cover.
- For every positive parameter, `N_realizable` proves that the natural-number supremum is an attained maximum. The empty configuration ensures the set of admissible cardinalities is nonempty.
- Radius monotonicity upgrades finite-prefix constructions to a full `atTop` limit. A constant upper bound of three excludes that limit at and above one half.
- The maximum-cardinality classification assumes `delta > 0`. Only the infinite construction permits `delta = 0`; no maximum-cardinality assertion is made there.
- The original existence question is derived with `delta = 1/10`.

## Documentation corrections made during review

The submission now points to the actual canonical source. The discussion of unbounded finite cardinalities at zero separation specifies a disk of positive radius. The maximum-cardinality and limit discussion explicitly reinstates positive separation after the more general infinite construction.

## Contribution comparison and limits

The inspected prior plby source at commit `8822f7ddef30fadbd92e1c6ab4ed897af356af5e` already proves the original existence result. This package adds the all-parameter statement, non-strict endpoint obstruction, and their combined classification relative to that source. The mathematical construction and odd-distance obstruction are classical, as credited in `ATTRIBUTION.md`.

This review does not establish global priority, certify the absence of an equivalent formalization elsewhere, confer recipient status, or decide prize eligibility. Machine-check results are recorded separately in `verification/verification.public.json`.

## Bounded public duplicate check

Four additional search groups on 2026-09-16 covered the official issue/PR index, the latest corresponding plby source, and two public searches using all-parameter and half-integer endpoint terminology. No matching all-parameter equivalence or planar no-four-half-integer Lean theorem was found in that scope. [Issue #16](https://github.com/TheJustinSunPrize/awards/issues/16) still describes the fixed `delta = 1/10` result. The [latest corresponding plby file inspected](https://github.com/plby/lean-proofs/blob/cecc3fc4b7725db36692f0eca3c24712a481cfba/src/latest/ErdosProblems/Erdos466.lean) has SHA-256 `0c829ffc09a32513c62ba654c5b5e661e5a35820601d3a0e88ebae09b2f04f5e`, the same fixed-parameter source bytes already credited above. Unindexed work and differently named formalizations remain outside the conclusion.
