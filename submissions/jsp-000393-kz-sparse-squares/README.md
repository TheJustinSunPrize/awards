# JSP-000393: sparse-square construction for scoped review

This packet requests review of an AI-assisted Lean formalization of a known constructive component of JSP-000393 / Erdős 485. It does not claim a complete solution, mathematical novelty, first formalization, independent referee approval, or an award.

## Contribution and exact scope

For the Coppersmith–Davenport seed

    S(x) = (1 + 2x - 2x² + 4x³ - 10x⁴ + 50x⁵ + 125x⁶)(1 - 110x⁶),

define F₀ = 1 and Fₖ₊₁(x) = S(x)Fₖ(x²⁵). With T(P) denoting the number of nonzero coefficients, the formal proof establishes, for every natural k,

    T(Fₖ) = 13ᵏ and T(Fₖ²) = 12ᵏ.

It also proves for every natural M that there exists P in ℤ[x] with M T(P²) < T(P). The proof includes the seed identities, support counts, collision-free multiplication lemma, recursive construction and growth comparison.

The exact statements and all hypotheses are recorded in [STATEMENT.md](STATEMENT.md). The original problem's Schinzel lower-bound theorem is outside this contribution's scope. No problem-bank solved status or first-Lean-proof status change is requested.

## Public evidence

- [Pinned proof repository](https://github.com/ketianzhang1-lang/jsp-000301-lean/tree/a337720331a34599114a9d4669d6518d5e608f6f)
- [Lean source](https://github.com/ketianzhang1-lang/jsp-000301-lean/blob/a337720331a34599114a9d4669d6518d5e608f6f/JSP000393.lean)
- [Reproduction and verification](VERIFICATION.md)
- [Machine-readable source pins and hashes](SOURCE.json)
- [Attribution, assistance and contribution limits](PROVENANCE.md)

## Prior work and requested handling

[Existing issue #44](https://github.com/TheJustinSunPrize/awards/issues/44) already registers plby/lean-proofs' formalization of the full Schinzel result. This packet links that existing registration and does not replace its credits or open a duplicate full-solution claim. The prior entry was checked for scope; an exhaustive overlap audit of every auxiliary result was not performed.

The explicit seed appears in Coppersmith and Davenport, *Polynomials whose powers are sparse*, Acta Arithmetica 58(1), 79–87 (1991), p. 86; product constructions are discussed on pp. 80–81. [Primary paper](https://matwbn.icm.edu.pl/ksiazki/aa/aa58/aa5816.pdf).

Please assess the statement match, overlap with existing work, and whether this additional constructive formalization is eligible for any recognition. If not, this packet may be treated as supplementary evidence only. The proposed recipient placeholder is `RECIPIENT-JSP-000393-KZ-A`; written recipient confirmation is pending. No public candidate, award level, payment, or confirmed recipient record is asserted by this submission.

The submitter seeks recognition for the documented implementation and evidence preparation, which is a relevant attribution interest. AI assistance and original mathematical credits are disclosed. No independent referee relationship or attestation is claimed.
