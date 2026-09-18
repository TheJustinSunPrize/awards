# JSP-000904: exact counting reduction for repeated-distance four-sets

## Request and scope

Please review a self-contained counting reduction and scoped consequences for
[JSP-000904](../../../problems/catalog-0901-1000.md#JSP-000904), corresponding
to [Erdős Problem 1087](https://www.erdosproblems.com/1087).

For an `n`-point set `P` in the Euclidean plane, let `F(P)` be the number of
four-point subsets whose six edges do not all have distinct lengths. The
submission proves an exact identity expressing a weighted version of `F(P)` in
terms of:

- the ordered equal-distance quadruple count used by Guth and Katz; and
- the number of isosceles configurations with a distinguished apex.

It then records three consequences:

1. the published Guth--Katz and Katz--Tardos estimates imply
   `F(P) = O_epsilon(n^(3.1358624898 + epsilon))`;
2. the requested `n^(3+o(1))` bound is equivalent, at this exponent precision,
   to an `n^(2+o(1))` upper bound for the distinguished-apex isosceles count;
3. if every line contains at most `L` points of `P`, then
   `F(P) = O(n^3 log n + L n^3)`, so the requested bound holds in particular
   when no three points are collinear.

This is a **partial-scope contribution**. It does not prove the required
`n^(2+o(1))` isosceles estimate for arbitrary planar point sets and therefore
does not solve JSP-000904. No change to the problem status, Lean flag, claim
status, candidates, awards, or payment records is requested.

## Files

- [PROOF.md](PROOF.md) gives the definitions and proofs.
- [STATEMENT_MAP.md](STATEMENT_MAP.md) separates the original problem from the
  scoped claims proved here.
- [REFERENCES.md](REFERENCES.md) identifies the external theorems and the exact
  way each is used.
- [scripts/check_counts.py](scripts/check_counts.py) independently enumerates
  the finite counting objects with exact squared distances.

## Reproduction

The checker uses only the Python standard library:

```sh
python3 docs/submissions/jsp-000904-distance-counting/scripts/check_counts.py
```

It exhaustively checks all 382 subsets of size at least four of the `3 x 3`
integer grid, checks 200 deterministic pseudorandom point sets, and verifies a
rhombus attaining the sharp local multiplicity constant 10. The checker tests
the two intermediate double-counting identities, the combined identity, and
both inequalities relating the weighted and unweighted counts.

These finite checks guard against orientation, endpoint-sharing, and
multiplicity mistakes. They are not a proof for arbitrary `n`, a Lean
formalization, or independent mathematical review.

## Attribution and review status

The external estimates are due to Guth--Katz and Katz--Tardos and are cited at
their primary sources. The elementary reduction and exposition were prepared
in a ChatGPT conversation with OpenAI Codex assistance. This submission does
not assert priority for the reduction, a confirmed recipient identity, or
independent verification. The submitting GitHub account has an interest in the
review of this contribution.

Bounded searches of this repository's public issues and pull requests for the
exact catalog identifier and for `1087` returned no matching submission on
2026-09-17. This is duplicate screening, not a priority claim.
