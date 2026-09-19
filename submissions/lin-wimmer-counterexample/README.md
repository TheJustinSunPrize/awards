# Lin--Wimmer rank-minimization counterexample

This is an independently written Lean formalization of the counterexample in
Section 3 of Shuo Shi, Juan Zhang and Yun Zhang,
[arXiv:2609.07113v1](https://arxiv.org/html/2609.07113v1), submitted 7 September 2026.
The mathematical counterexample belongs to those authors. This submission claims
only the new formalization, not discovery of the mathematical result.

## Statement and scope

The original conjecture is on page 443 of Minghua Lin and Harald K. Wimmer,
*The generalized Sylvester matrix equation, rank minimization and Roth's
equivalence theorem*, Bull. Aust. Math. Soc. 84 (2011), 441--443,
[doi:10.1017/S0004972711002334](https://doi.org/10.1017/S0004972711002334).
It equates the minimum rank of `AX-XB-C` with the minimum rank of
`P [A C; 0 B] - [A 0; 0 B] P`, with the latter minimum taken over invertible `P`.
The same `X`, respectively the same `P`, appears in both terms. This differs from
the valid theorem with two independent unknown matrices.

`Proof.lean` uses Mathlib's `Matrix.rank`, `Matrix.fromBlocks`, `IsUnit`,
`IsLeast` and natural-number infima. It proves the following for **every field**:

- `LinWimmer.left_minimum`: the left minimum for the explicit 3-by-3 matrices is 2.
- `LinWimmer.right_minimum`: the right minimum is 1, attained by an explicitly
  invertible 6-by-6 block matrix.
- `LinWimmer.minima_values`: both natural-number infima have these exact values.
- `LinWimmer.refutation`: the universally quantified original rank conjecture is false.

The `IsLeast` results establish both attainment and universal lower bounds, so
the infima do not rely on an empty-set convention. The result includes fields of
characteristic two. The extra dimensional-minimality theorem of Section 4 of the
2026 paper is outside this formalization.

For the left lower bound, one of two 2-by-2 minors is invertible. For the right
lower bound, we use `M_0^2 = 0` and `M_C^2 != 0`: no invertible intertwiner can
make the difference zero. Thus this development does not assume Roth's theorem
as an axiom or require formalizing it as a prerequisite.

## Reproduction

Use the pinned `lean-toolchain` and Mathlib revision in `lakefile.toml`:

```sh
lake update
lake exe cache get
python3 verify.py
```

The verifier compiles the proof, checks the four terminal axiom reports, and runs
`leanchecker` on the compiled module. The expected axioms are exactly
`propext`, `Classical.choice`, and `Quot.sound`. There are no admitted proofs,
additional mathematical axioms, or native-computation trust axioms in their closures.

`leanchecker` replays declarations using the same Lean kernel; it is **not** an
independently implemented checker. The recorded local run reused an existing
pinned Mathlib cache. No clean-room build, independent expert endorsement,
organizer acceptance, or prize decision is claimed.

## Attribution and review status

- Original conjecture: Lin and Wimmer (2011).
- Mathematical counterexample: Shi, Zhang and Zhang (2026).
- This Lean source: generated and iteratively checked with OpenAI Codex in this
  contributor's session, using the cited mathematical argument and Mathlib APIs.
- Any proposed recipient remains `RECIPIENT--A` pending the organizer's identity
  and contribution confirmation. Bibliographic attribution is not a recipient nomination.
- No matching JSP entry was found in the current public catalog. No JSP ID is
  invented or borrowed. Problem-bank inclusion and formalization eligibility
  require maintainer/organizer review.
- The contributor seeks review of their formalization and therefore has a direct
  interest in attribution. No relationship with the mathematical authors or
  organizers is claimed.

See `dedup.json` for the scope and limits of the public duplicate check.
This is submitted evidence, not a first-formalizer priority certification.

## License

This newly written proof and reproduction code are offered under Apache-2.0,
as in the repository's source-code license. The cited papers retain their own
rights; no paper PDF or paper source is redistributed in this package.
