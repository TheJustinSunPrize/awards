# JSP-000346: a uniform square-root bound on omitted integers

This AI-assisted contribution proves an explicit necessary condition for the sequences in [Erdős 421](https://www.erdosproblems.com/421): if an increasing sequence has distinct products on all distinct nonempty consecutive blocks, then, for every natural number N,

\[
E(N)\ge \lfloor\sqrt N\rfloor-\lfloor\sqrt{\lfloor\sqrt N\rfloor}\rfloor-1,
\]

where E(N) counts omitted **positive** integers at most N. There is **no density assumption**. In particular, E(N) is at least `sqrt(N) - N^(1/4) - 2`, and its lower limiting ratio to sqrt(N) is at least one. At N = 100,000,000 the integer bound gives at least **9,899 omissions**.

This is a scoped quantitative supplement. It does not construct a density-one sequence, prove the full existence theorem, establish optimality, or settle the question of an O(sqrt(N)) omission construction. Worldwide priority and prize eligibility remain unestablished.

## Contribution and comparison

[Pratt's Proposition 7.1](https://www.erdosproblems.com/static/421-Pratt.pdf), in the version identified in [PRIOR_ART.md](PRIOR_ART.md), gives an unconditional coefficient 1/3 and a coefficient one under a density-one assumption. [PR #457](https://github.com/TheJustinSunPrize/awards/pull/457) gives an unconditional coefficient 1/2 using disjoint triples. The result here gives coefficient one unconditionally, with an explicit finite error term.

The proof counts products of **adjacent members of the sequence**, even when the integers between those members are absent. Those products provide missing values above an intermediate cutoff. Combining them with omissions below that cutoff removes the need for a density hypothesis. See the complete [mathematical proof](PROOF.md) and [formal statement correspondence](STATEMENT.md).

## Verification

[ProductDeficit.lean](ProductDeficit.lean) contains eight named theorems, including an explicit bridge from the original interval-product injectivity condition. All eight axiom closures contain only `propext`, `Classical.choice`, and `Quot.sound`. There are no admitted proof obligations, additional mathematical axioms, or reliance on executable search output in the proof.

Local build, axiom audit, exhaustive small-case checks, and fresh Lean kernel replay are recorded in [verification/verification.json](verification/verification.json). The small-case check enumerates all 524,287 subsets across cutoffs 0 through 18 and checks the stronger adjacency-condition theorem. It also checks that the hypothesis cannot be removed, that the adjacency condition is weaker than the original block condition, and that the original condition has nonempty examples.

The kernel replay uses Lean's own official kernel, not an independently implemented checker. Compiled dependency caches were used; a full source rebuild of every dependency, network isolation, filesystem isolation, Nanoda verification, human referee review, and organizer-designated verification are not claimed.

## Reproduction

Install Lean 4.34.0 and Python 3.11 or newer. Put the Lean toolchain's executables, including `lake` and `leanchecker`, on PATH. In this directory, retain the committed manifest and run:

```sh
lake exe cache get Mathlib.Data.Finset.Sort Mathlib.Data.Nat.Sqrt Mathlib.Algebra.BigOperators.Intervals Mathlib.Tactic.Linarith Mathlib.Tactic.NormNum Mathlib.Tactic.Positivity
python3 tools/check_environment.py
python3 tools/verify.py
```

The manifest fixes Mathlib to `5ed2965256430c3649e86755f9576b54eca72435` and fixes all nine dependencies. Lake may first fetch missing package checkouts. `tools/check_environment.py` rejects differing revisions or tracked-source modifications. Do not replace the manifest with a newer dependency resolution when reproducing the recorded result.

## Requested review

Please review the mathematical argument, exact statement correspondence, comparison with Pratt and PR #457, and whether this scoped quantitative/formalization contribution is eligible for assessment under JSP-000346. The submitting account has a direct interest in possible recognition. No recipient designation, award amount, entitlement, or official certification is asserted. This package changes no problem status, candidate, recipient, or award record.

The proof and documentation were developed with GPT assistance and are offered under [MIT](LICENSE). Mathematical context and prior results are credited in [PRIOR_ART.md](PRIOR_ART.md). No third-party proof source or paper is redistributed in this package.
