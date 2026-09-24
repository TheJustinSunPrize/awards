# Scope and prior work

The target comes from [Erdős Problem 882](https://www.erdosproblems.com/882). This package formalizes its known refined **upper bound**. It does not claim to solve other subquestions or a new open mathematical problem. The constant `C=3` applies when both logarithms have base 2; changing the inner logarithm to the natural logarithm requires adjusting the additive constant.

The original condition says that the numerical set of nonempty subset sums is primitive; distinct subset sums are not assumed. Two equivalence theorems in `Primitive.lean` check this distinction. The expanded definition, attainment theorem, and order characterization in `Maximum.lean` check the actual maximum. Formal Conjectures revision `40e7c98697de6f66b8cbdbf641749ab39ed9c152` has no `882.lean`, so no mechanical correspondence with a nonexistent upstream Lean declaration is claimed.

[Official PR #31](https://github.com/TheJustinSunPrize/awards/pull/31), at fixed head `83f20bbe58d116a9a290c86821fa4ee1a29dd3eb`, proves the leading asymptotic and explicitly excludes the refined half-log-log bound. This package adapts the primitivity-to-injectivity proof from its Apache-2.0 addition [Erdos882Upper.lean](https://github.com/zifanersuotang/awards/blob/83f20bbe58d116a9a290c86821fa4ee1a29dd3eb/submissions/jsp-000733/Erdos882Upper.lean), with attribution. It neither copies nor imports the separately licensed lower-construction source `Erdos882Existing.lean`.

Earlier screening also found stronger finite bounds in lean-genius revision `dc62f771ed5010abfdb04247dff6143e0e69d3e7`:

- [Erdos1Wip01OQ02.lean](https://github.com/rjwalters/lean-genius/blob/dc62f771ed5010abfdb04247dff6143e0e69d3e7/proofs/Proofs/Erdos1Wip01OQ02.lean#L223): `4^k≤12kn²+1`.
- [Erdos1OQ02.lean](https://github.com/rjwalters/lean-genius/blob/dc62f771ed5010abfdb04247dff6143e0e69d3e7/proofs/Proofs/Erdos1OQ02.lean#L461): a square-root-scale distinct-subset-sums bound.

Those declarations contain actual `by` proofs and are relevant to the route for Problem 882. This screening inspected source only and did not recompile the third-party projects. A reusable license was not established, and no source was copied. No complete proof from the original condition to the final half-log-log bound for the actual maximum was found in the bounded set of files inspected. This is not a global priority claim.

The contribution is therefore the reproducible connection of the original primitivity condition, the actual maximum, and the complete explicit refined logarithmic bound. The generic second-moment inequality must not be presented as a first formalization. Verification scope is limited to the recorded run; award eligibility remains for the organizers to determine.
