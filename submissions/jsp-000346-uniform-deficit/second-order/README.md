# A second-order omission obstruction for product-distinct sequences

This package strengthens the omission-bound direction of **JSP-000346 / Erdős 421**. It supplies a complete Lean proof of the following quantified result under the original natural-density-one hypothesis.

Let `a` be a strictly increasing sequence of natural numbers whose products over distinct nonempty consecutive index intervals are all different. Let `E(N)` count the positive integers at most `N` outside its range. If the sequence has natural density one, then for every integer `k≥1` there is `N₀` such that every `N≥N₀` satisfies

`k*floor(sqrt(N)) + (k−1)*floor(cuberoot(N)) ≤ k*E(N)`.

Equivalently in standard asymptotic notation,

`liminf (E(N)−sqrt(N))/N^(1/3) ≥ 1`.

Thus the obstruction has a positive cube-root second-order term. The Lean endpoint theorem is `second_order_of_natural_density`, which uses the usual real-valued limit of the proportion of retained integers. The exact integer statement is formalized; the translation from floors to the displayed real-root asymptotic notation is explained in [PROOF.md](PROOF.md).

## Relation to existing bounds

Pratt's inspected Proposition 7.1 gives the density-one bound `(1−o(1))*sqrt(N)`. The earlier parent submission proves an unconditional coefficient-one bound with fourth-root error. The updated [PR #457](https://github.com/TheJustinSunPrize/awards/pull/457) improves that *unconditional* error to logarithmic/inverse-factorial size and is explicitly credited here.

The present result gives an additional positive term under density one, rather than a further reduction in the unconditional error. It does not supersede #457's stronger hypothesis-free finite estimate. Our proof counts disjoint two-term and three-term block products; no #457 code is copied or imported.

This is a mathematical strengthening relative to the inspected statements, not a claim of worldwide discovery priority. It does not solve the density-one existence problem, construct an optimal sequence, prove the second-order coefficient sharp, or establish award eligibility. External mathematical review remains necessary to assess originality and significance.

## Evidence

- [SecondOrder.lean](SecondOrder.lean): 17 named theorems, including finite inequalities, root estimates, an explicit threshold, and the natural-density bridge.
- [STATEMENT.md](STATEMENT.md), [PROOF.md](PROOF.md): exact statement and short mathematical argument.
- [PRIOR_ART.md](PRIOR_ART.md): pinned source comparison and limits of novelty checks.
- [VERIFICATION.md](VERIFICATION.md): checking procedure, results and limitations.

Pinned environment: Lean 4.34.0, Mathlib `5ed2965256430c3649e86755f9576b54eca72435`. From this directory:

```sh
lake exe cache get
python3 tools/verify.py
```

The script audits all theorem closures and performs fresh replay using Lean's official kernel. It also compares exact finite cases and executable integer roots. Python is supplementary, not an assumption of the Lean proofs. Source, commands and logs are hashed.

Prepared with GPT/Codex assistance under public account `green3sf`. The submitter has an interest in recognition of the contribution. This continues the existing PR #470 rather than creating a duplicate submission. Mathematical attribution is retained; new source is MIT-licensed.
