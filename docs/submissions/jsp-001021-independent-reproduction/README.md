# JSP-001021 / Erdős 1216 — independent n=15 reproduction

This submission records an independently reconstructed proof that every tournament on 15 vertices contains a transitive subtournament on 5 vertices. Consequently the universal formula proposed in Erdős Problem 1216 fails at `n = 15`, since `floor(log2 15) + 1 = 4`.

## Scope and prior work

This is **not a new mathematical solution and not a first formalization claim**. Reid and Parker proved the stronger 14-vertex result in 1970. After this reconstruction was completed, an existing complete Lean formalization was located in `plby/lean-proofs`, pinned at commit `8822f7ddef30fadbd92e1c6ab4ed897af356af5e`, in `src/latest/ErdosProblems/Erdos1216.lean`. That source formalizes the stronger 14-vertex theorem and uses it to refute the proposed formula.

Accordingly, this submission is offered only as a supplementary independent mathematical reproduction with an executable finite checker. It claims no priority, new discovery, award eligibility, recipient status, or payment entitlement.

## Contents

- `PROOF.md`: mathematical proof and scope audit.
- `verify.py`: Python 3.10+ standard-library checker for all finite case analyses used in the proof.
- `verification-results.json`: actual output from the included checker.

Run:

```sh
python verify.py
```

Do not use `python -O`, because assertions are part of the checker.

## Verification boundary

The checker validates the finite ingredients used by the argument: the seven-vertex tournament model, all six local classification permutations, all 14 cyclic triples, all 196 ordered cyclic-triple pairs, the 12 normalized pair cases, 21 affine automorphisms, and all ten directed edges of the final transitive 5-set witness.

This is **not Lean verification**. No successful Lean compilation was obtained for this reconstruction, and no external Lean build is represented here as independently rerun. Repository CI, if green, should not be interpreted as mathematical verification or award approval.
