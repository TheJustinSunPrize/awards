# Review request and mathematical increment

This package requests review of an incremental formalization for
[JSP-000925](../../../problems/catalog-0901-1000.md#JSP-000925), related to
[existing-proof registration #24](https://github.com/TheJustinSunPrize/awards/issues/24).
The catalog at base commit `f4e7173d89dfe91022a185427d63452c8ffbf6ae` says
**Eligible to claim: No**. This submission does not override that status or
establish any entitlement. Please determine whether the strictness and explicit
existence/uniqueness increment is eligible for consideration, or belongs in a
different intake location. The proposed recipient remains
`RECIPIENT-JSP-000925-KZ-A`, confirmation pending.

The prior theorem already establishes the intended non-strict result. This is
not a first solution, a first formalization of the whole problem, or a new
mathematical theorem. The mathematical result is credited to Balint; the imported
formal development is credited separately in [PROVENANCE.md](PROVENANCE.md).

## What changes mathematically

| Part | Pinned prior theorem | This supplement |
| --- | --- | --- |
| Outward gap comparison | Non-strict | Strict, except the equal central mirror pair |
| Derivative-root selector | Assumed | Constructed from the polynomial hypotheses |
| Uniqueness in each root interval | Not in the final theorem | Included in the final theorem |
| Translation, positive spacing, leading coefficient | Arbitrary | Arbitrary |
| Degree | Arbitrary | Arbitrary |

For exact quantifiers and small-degree behavior see [STATEMENT.md](STATEMENT.md).
The source is [JSP000925Strict.lean](JSP000925Strict.lean). Both final statements
use the actual polynomial derivative; neither assumes the desired gap property.

## Strictness argument

Normalize the roots to the integers from 0 through N. Write
`s = moment 1 N u`, `t = moment 2 N u`, `v = moment 3 N u`, and `z = u^2`.
The imported moment estimates give `s>0`, `t^2<=s*v`, and `s^3<=4*t`.
In particular, `t>0` and `v>=0`. The numerator of the second derivative of the
imported phase is `4*u*D`, where

    D = (3*t + 4*z*v)*(pi^2 + 4*z*s^2) - 4*s*(s + 2*z*t)^2.

The new `strict_algebra` lemma checks the exact identity

    s*D = (3*pi^2 - 16)*s*t
        + 4*s*(4*t - s^3)
        + 4*z*(pi^2 - 4)*s*v
        + 4*z*(4*(s*v - t^2) + t*(4*t - s^3))
        + 16*z^2*s^2*(s*v - t^2).

Every term is nonnegative and the first is strictly positive. Thus for `u>0`
the phase has positive second derivative. Its continuity at the endpoints and
this interior positivity give strict convexity on `[0,N/2]`.

At each relevant critical point the imported phase identity is
`phase(b_k-N/2) = b_k-k-1/2`. Its secant slope across a gap of length L is
`(L-1)/L`. Strict convexity orders successive slopes, hence orders the positive
gaps strictly. The even-N central case uses the slope from the midpoint to the
first right-hand critical point and reflection symmetry; this case is treated
separately in `canonical_strict`. For odd N the central mirror pair is equal
and correctly excluded from the strict predicate.

Affine normalization proves `strict_gap_theorem`. Rolle's theorem constructs
one critical point in every open root interval. The imported strict decrease of
the logarithmic derivative proves uniqueness there. Combining these results
gives `exists_unique_strict_gaps` with no selector assumption.

## Review boundaries

The submitter is requesting consideration of their own assisted contribution;
this is not an independent human verification. Contributor-run checks and
their trust limits are recorded in [VERIFICATION.md](VERIFICATION.md).
The package does not change official catalog flags, recipients, candidates,
awards, or published decisions. Attribution, statement fidelity, substantive
novelty of the formalization increment, eligibility, and any award allocation
remain for the organizers to assess.
