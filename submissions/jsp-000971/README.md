# JSP-000971 / Erdős 1166: alternative formalization for review

## English

This submission provides an alternative Lean formalization of the almost-sure O(log²n) bound on the number of distinct sites that have ever been most visited by time n in planar simple symmetric random walk.

**Existing formalization:** plby/lean-proofs already contains `Erdos1166.erdos_1166`, with integration-file history dating to August 2026. This is not a first-formalization claim or a new mathematical solution. See [PRIOR_ART.md](PRIOR_ART.md). The official catalog's `Eligible to claim: No` marker is left unchanged. Please determine whether this alternative implementation and reproducibility contribution is admissible for review; no award entitlement or allocation is asserted.

## Exact statement

The principal theorem is `JSP000971.erdos_1166` in [Final.lean](Final.lean): under the canonical planar simple symmetric random-walk law, almost every path has C>0 and a natural N such that every n≥N satisfies

```
(card (historical s n) : ℝ) ≤ C * (Real.log (n : ℝ)) ^ 2
```

Time 0 is included, all tied maximizers are counted, the union counts distinct sites, and C and N may depend on the path. The law starts at the origin with independent uniform nearest-neighbor increments. Both probabilistic inputs are discharged, not retained as assumptions. A standard Mathlib big-O theorem is also provided.

[PROOF.md](PROOF.md) gives the mathematical argument and definition correspondence. [Counting.lean](Counting.lean) is a deterministic theorem for arbitrary sequences. The maximum-tail route covers the maximum by n+1 recentered origin tails, proves a summable inverse-square probability bound, and applies Borel–Cantelli. The eventual-three-sites input reuses the attributed upstream 1165 development.

## Reproduction and evidence

The nine root Lean files in this PR are byte-identical to the pinned complete proof project identified in [evidence.json](evidence.json). The 785-file upstream closure and compiler logs are kept in that external project/archive rather than duplicated into the awards repository. The toolchain is Lean 4.33.0 with Mathlib commit `db584cd6d46c92f209a44c0f1c829460d327499d`.

After installing the pinned Lean toolchain, run:

```sh
bash reproduce.sh
```

The script fetches the exact public proof commit, checks that all nine submitted Lean files match it, obtains the fixed Mathlib cache, and runs the complete project verification. Verification includes the packaged-source audit, complete build, strict integration compilation, transitive axiom reports and Lean-kernel replay. See the external logs and `verification/results.json` for the checks actually completed before submission.

No independently implemented checker or independent human statement-fidelity review is asserted. Lean's own checker is identified as such. Public GitHub commit/release evidence is not represented as an independently administered institutional archive.

## Attribution and record impact

This is a self-submission prepared with Codex assistance. The submitting account has an attribution interest; that is a relevant conflict for review. No verified recipient identity, affiliation, authorization to allocate a prize, or official review signature is asserted. No candidate, award, recipient, catalog eligibility or public decision record is modified.

Original mathematics and reused Lean work retain their credit. See [NOTICE](NOTICE) and [LICENSE](LICENSE). The newly submitted root files concern counting, definition bridges, a maximum-local-time tail route and final assembly; substantial upstream probability theory is explicitly reused.
