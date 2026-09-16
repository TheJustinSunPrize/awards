# JSP-000733 / Erdős 882: the refined upper bound

This package proves the refined upper bound for the actual maximum cardinality in the original problem: for every natural number `n ≥ 32`,

\[
f(n)\le\log_2 n+\tfrac12\log_2(\log_2 n)+3.
\]

It also proves the eventual statement with an existential constant. Both logarithms have base 2. Here `f(n)` is the largest cardinality of a subset `A ⊆ {1,…,n}` whose **numerical nonempty subset sums** form a primitive set. The final theorem has no additional injectivity, counting-bound, or maximum-attainment hypothesis.

The main declarations in `LogBound.lean` are:

```lean
theorem maximumSize_refined_upper_bound {n : ℕ} (hn : 32 ≤ n) :
    (maximumSize n : ℝ) ≤ Real.logb 2 (n : ℝ) +
      (1 / 2 : ℝ) * Real.logb 2 (Real.logb 2 (n : ℝ)) + 3

theorem refined_upper_bound :
    ∃ C : ℝ, ∀ᶠ n : ℕ in Filter.atTop,
      (maximumSize n : ℝ) ≤ Real.logb 2 (n : ℝ) +
        (1 / 2 : ℝ) * Real.logb 2 (Real.logb 2 (n : ℝ)) + C
```

`Maximum.lean` proves attainment, the order characterization of the maximum, and equality with a maximum defined directly using the numerical subset-sum image. `Audit.lean` prints these definitions, the full target, and axiom dependencies.

## Reproduction

Lean `4.33.1` and mathlib `0df444a360eaa60ab8c11dca51a86af692955474` are pinned; the manifest fixes all nine dependencies. After installing the pinned toolchain, run from the package directory:

```text
lake exe cache get
python verify.py
python test_verify.py
```

Alternatively, pass `--lean-bin <Lean-bin-directory>` to the verifier. The final run, run ID, and source hashes are recorded in `logs/results.json`; that record must show `PASS` and process exit code 0 for the run being considered. The verifier recompiles seven project modules, audits fifteen declarations, runs actual negative controls, and runs `leanchecker --fresh Audit` with the same Lean kernel. The six Python regression tests are recorded separately and do not replace Lean compilation.

Official dependency caches were used. Not all mathlib sources were rebuilt, and no second kernel implementation was run. Logs are explicitly labeled path-redacted copies; see `logs/REDACTION.md` and `logs/redaction-manifest.json` for the rules and original/copy hashes. Original records remain local. Hashes do not provide independent certification.

## Files and scope

`Moment`, `Energy`, and `Counting` establish the finite second-moment bound; `Primitive` connects it to the original condition; `Maximum` handles the actual maximum; `LogBound` proves the refined upper bound; and `Audit` checks the target and axioms.

This formalizes a known upper bound and makes no new mathematical discovery claim. Stronger formalized generic finite second-moment bounds already exist. The deliverable here connects the original conditions and the actual Erdős 882 maximum to the complete refined logarithmic bound. Sources, reuse, and bounded prior-art screening are recorded in [SCOPE_AND_PRIOR_ART.md](SCOPE_AND_PRIOR_ART.md); the mathematical proof is in [PROOF.md](PROOF.md).

This English package is prepared for intake and formalization-contribution review. No organizer acceptance or award is claimed. The Chinese deliverable and the earlier finite-bound trial remain unchanged as separate records. Only documentation and Lean comments were translated; comment-stripped Lean source equality is checked in `TRANSLATION_CHECK.json`. The translated source bytes were separately recompiled and verified, as recorded in this package's final logs.
