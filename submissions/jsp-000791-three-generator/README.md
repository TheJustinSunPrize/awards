# JSP-000791: a three-generator lower bound (partial scope)

## English

This submission supplies Lean evidence for a quantitative component of
[JSP-000791](../../problems/catalog-0701-0800.md#JSP-000791) /
[Erdos Problem 951](https://www.erdosproblems.com/951).

Let `a : Nat -> Real` be strictly increasing, with `a 0 > 1`. Suppose every
pair of distinct finitely supported natural exponent vectors gives monomials
at distance at least one. The checked theorem is

```lean
JSP791.sequence_third_generator_gt_cutoff
  (ha : 1 < a 0) (hm : StrictMono a) (hs : SequenceSeparated a) :
  (4309405275 : Real) / 1000000000 < a 2
```

Thus the third generator is strictly greater than **4.309405275**. The
separation hypothesis covers all finitely supported exponent vectors, including
the zero vector, whose product is 1. There is no finite exponent cutoff,
assumed counterexample, or auxiliary polynomial assumption in the final theorem.

This does **not** prove the eventual prime-counting conjecture, construct a
finite counterexample, prove an upper bound, or establish an infinite extension
of a finite counterexample. The theorem bounds every admissible triple; it
does not by itself give a strict inequality for the infimum of their maxima.
Review is requested only for this quantitative partial formalization.

### Attribution and provenance

The mathematical comparison argument and the numerical lower threshold are
from [Patrick White + Claude's public working report, 28 July 2026, Section 2](https://www.erdosproblemaday.com/report/951).
That report claims a sharper algebraic barrier and an upper existence bound.
Those further claims are not imported as assumptions or certified here.

The present Lean implementation is new work prepared by the submitting
`zilan520` account with OpenAI Codex assistance. It replaces the report's
derivative/root-enclosure steps with exact rational affine bounds and
Bernstein polynomial identities checked by Lean's `ring` and order tactics.
We claim no new mathematical discovery, no authorship of the report, and no
global first-formalization priority.

The [Formal Conjectures statement](https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/951.lean)
was consulted for the finitely supported exponent formulation. It is not a
dependency; its unfinished conjecture proofs are not imported. Original Erdos
references and the finite/all-sufficiently-large distinction are linked on the
problem page. Earlier finite-counterexample work by Barreto/Price and
Sothanaphan is separate from the lower bound formalized here.

### Proof structure and statement correspondence

- `ThreeGenerator.lean`: separation implies `a >= 2`, `b >= a+1`, `c >= b+1`.
  It derives `c >= (5+sqrt 13)/2` and, when `c < 4.31`, the comparisons
  `a^2 >= c+1`, `b^2 >= a*c+1`, `c^2 >= a^2*b+1`.
- `LowerCertificate.lean`: three exact polynomial positivity certificates on
  `[4.3,4.309405275]`. Every rational identity is verified by `ring`; positive
  Bernstein coefficients and interval factors establish each sign. The Python
  generator is a convenience and is not in the proof trust chain.
- `SharpLower.lean`: forces `a^7 >= c^4+1`, obtains an affine lower bound for
  `a`, and combines the comparisons to contradict `c <= 4.309405275`.
- `SequenceBridge.lean`: embeds arbitrary three-component exponent vectors
  into natural-indexed finitely supported vectors, proves that embedding
  injective and that monomial values agree, and derives the final theorem
  directly from the infinite-sequence hypotheses.

### Reproduce

Lean is pinned to `4.34.0`; Mathlib is pinned to
`5ed2965256430c3649e86755f9576b54eca72435`; transitive dependencies are locked
in `lake-manifest.json`. With Python 3.10+ and the pinned Lean toolchain:

```sh
lake exe cache get
python verify.py
```

The verifier checks dependency revisions and tracked-source cleanliness, runs
`lake build`, then rechecks every supplied module with `--trust=0`. It audits
every explicitly printed target and records source/log hashes. Only `propext`,
`Classical.choice`, and `Quot.sound` are permitted. See
[INDEPENDENT.md](INDEPENDENT.md) for the independent implementation check and
two deliberately invalid controls.

This evidence was produced by the submitting operator. It is not an independent
human review, the organizer's isolated verification, acceptance, or an award.
No problem-bank eligibility flags, recipient records, or award records are changed.

Code is contributed under the repository MIT license; documentation follows the
repository content license. Referenced third-party PDFs/code are not republished.
