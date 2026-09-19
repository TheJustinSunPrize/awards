# Exact nine- and ten-point Sendov cases (partial scope)

`JSP404.alpha_nine_ten_exact` proves, for the actual Euclidean-plane extremal quantity,

```text
forall N : Nat, 9 <= N -> N <= 10 -> alpha N = 5*pi/7.
```

`JSP404.guaranteed_nine_five_pi_sevenths` is the corresponding universal guarantee. There is no general-position assumption. This extends the separately verified small cases and power-of-two family in `../lean434`. It is not the arbitrary-cardinality Sendov classification or an award announcement.

## Mathematical and source attribution

The problem is Erdős 504 / JSP-000404 (planar minimax angles), not the polynomial Sendov conjecture. These are formal proofs of classical values, not claims to discover those values. The lower-bound certificate was generated independently here. The actual `Point`, `alpha`, finite-maximum infrastructure and upper construction are attributed to superpilot69 and contributors, PR42, pinned at `722cb3caa86710c788296ca0ec954a79e9a0adcc`, through the sibling package's dependency manifest. The geometric direction-model conversion is our previously submitted sibling module `SendovDirectionModel`.

The historical reference is Sendov, *A minimax problem for point configurations*, Acta Mathematica Hungarica 69 (1995), 27–46, [DOI](https://doi.org/10.1007/BF01874605). The exact value here follows the intermediate branch with numerator **2**, as in the final theorem and the source correction documented in [PR #42](https://github.com/TheJustinSunPrize/awards/pull/42). Our explicit statement is the extremal equality above, not a proof of a conflicting transcription or of the stronger historical strict-angle variant.

PR300, pinned at `e80d0b209dc60257c1109ee8ea904ea0d7dd5ef4`, independently states exact N=3..8 and the dyadic family. Our earlier PR body discloses the overlap and chronology. No global priority or award entitlement is asserted for this extension. No source from PR300 is used in these proofs.

## Proof structure

1. `NineTheoryTrial`: 5,617 checked linear-arithmetic and logical lemmas.
2. `NineRUPChunk000` through `034` and `NinePropositionalTrial`: 17,025 propositional resolution steps, joined into a contradiction conditional on their input clauses.
3. `NineCNFDirectChunk000` through `016`, `NineCNFDirectAll`: 8,230 explicit classical proofs connecting those input clauses to the real inequalities.
4. `NineModelTrial`: instantiates every retained input with the exact nine-point model's range and triangle constraints; proves unconditionally `Model 9 t -> 7/2 <= t`.
5. `NinePointExactTrial`: finite maximum angle, geometric transfer, cardinality monotonicity and the attributed upper construction yield the stated exact values.

Historical internal names ending in `Trial` are retained. The final statements are unconditional and contain no assumed model bound. Z3 and CaDiCaL were used only to discover the certificate; neither solver is needed to check the supplied Lean terms. No compiled-evaluation oracle is used.

## Reproduction

Use Lean 4.34.0 and Python 3.11 or later. Keep this directory beside the unchanged `../lean434` directory. Fetch the pinned dependencies and their Mathlib caches before an offline review, then run:

```sh
lake update
python verify.py
```

The verifier validates the sibling package's recorded source hashes and pinned Git dependencies, builds the sibling package, and checks each new module in dependency order with `lean --trust=0`. It bounds compiler parallelism and audits printed axiom closures. The final proof uses only `propext`, `Classical.choice`, and `Quot.sound`.

The default command checks every module. An interrupted local run can use `python verify.py --resume`; a checkpoint is reused only when its source, compiled artifact and log hashes match and its dependency-audit output is valid. Local checkpoints are excluded from Git. The recorded release run preserved 35 completed module checks after correcting the parser to recognize Lean's `does not depend on any axioms` output, then rechecked the affected module and completed the remaining checks. `verification/verify-initial.py` preserves the initial script bytes for provenance; it is not the reproduction entry point. The verification record associates each check with the verifier hash used. No theorem, Lean kernel, or axiom policy was weakened by that parser correction.

For an independent implementation, build the pinned exporter/checker in `INDEPENDENT.md` and run `verify_independent.py` with its four documented binary/source arguments. It exports the final theorem, checks it with Nanoda, and requires rejection of a deliberately invalid proof and an unpermitted axiom. The large generated exports are ignored by Git.

The records in `verification/` report submitter-run checks, including exact source, script and log hashes. They do not represent an independent operator, the prize's designated isolated verification, maintainer acceptance, or a committee award decision.
