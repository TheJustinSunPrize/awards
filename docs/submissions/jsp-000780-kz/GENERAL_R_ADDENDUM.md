# Supplement to PR #370: all exponents r ≥ 6 and prior-proof disclosure

This supplements the earlier r=6-only submission. Its general proof now
constructs, for **every r ≥ 6**, infinitely many sets of exactly r−2 distinct
positive r-full integers whose collective gcd is 1 and whose sum is r-full.
The totals are also pairwise distinct as the parameter varies.

- [Immutable source and reproduction scripts](https://github.com/ketianzhang1-lang/jsp-000301-lean/tree/b680afc09c4249542a3c2ea8c75fcefb13522b37/projects/jsp-000780-general)
- [Proof outline](https://github.com/ketianzhang1-lang/jsp-000301-lean/blob/b680afc09c4249542a3c2ea8c75fcefb13522b37/projects/jsp-000780-general/PROOF.md)
- [Contributor-run CI](https://github.com/ketianzhang1-lang/jsp-000301-lean/actions/runs/35177584518)
- [Provenance and overlap](https://github.com/ketianzhang1-lang/jsp-000301-lean/blob/b680afc09c4249542a3c2ea8c75fcefb13522b37/projects/jsp-000780-general/PROVENANCE.md)

The explicit parameters are q_t=B(H+t)+1, X=q_t^r, Y=B^r. The modulus B
is a product of coefficients after splitting the j=3 binomial term;
H=2^r·2^(r+1)+2. Primality of q_t is unnecessary. The set consists of
(X−Y)^r and the split odd-binomial monomials. The source includes a full
proof of positivity, distinctness, exact cardinality, fullness, gcd and
infinitude, including translation to the original prime-factor predicate.

## Material overlap disclosure

The underlying construction was already attributed to GPT-5.5 Pro prompted
by Liam Price. In addition, [PR #65's prior-art assessment](https://github.com/inoader/awards/blob/b5b70857b2d77d6a060e00956beb8e19918b48f9/submissions/jsp-000780/PRIOR_ART.md)
reports a 2026-05-24 Aristotle formalization covering every r≥6, with named
declarations `infinite_rpowerful_sums` and `infinite_rpowerful_sum_tuples`.
The original discussion link could not be retrieved directly in this session;
that prior proof has not been independently replayed here. This report is
explicitly disclosed and no first-formalization priority is claimed.

The new implementation expands the account holder's earlier formal scope.
It is not a new mathematical discovery and is not submitted as a second
award claim. Reviewers should assess whether any contribution remains
eligible given the preceding general formalization. No payment entitlement
is asserted. The existing recipient records remain unchanged.

The r=4 existence problem, r=5 infinitude problem, and full JSP-000780 entry
remain outside this submission's proved scope.

## Verification

Local Lean 4.34.0 compilation of seven modules, kernel replays of `Adapter`
and `Audit`, and five target axiom audits passed. The only target axioms
are `propext`, `Classical.choice`, and `Quot.sound`. There are no proof holes
or new axioms. The local cache lacks complete git metadata, so the clean CI
run linked above is the source of any claim about fresh dependency revision
checks or independent NaNoda validation. Its current status must be checked;
local compilation alone does not establish CI success.
