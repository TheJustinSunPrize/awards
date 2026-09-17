# JSP-000301: an infinite family of nonsquare powerful pairs

This package proves the negative answer to [JSP-000301](../../problems/catalog-0301-0400.md#JSP-000301) and strengthens the single counterexample to an unbounded, explicitly constructed family:

```lean
theorem unbounded_counterexamples (B : ℕ) :
    ∃ n > B, Powerful n ∧ Powerful (n + 1) ∧
      ¬ IsSquare n ∧ ¬ IsSquare (n + 1)
```

`Powerful n` means `0 < n` and, for every natural prime `p` dividing `n`, `p²` divides `n`. Both `Nat.Prime` and `IsSquare` are the ordinary Mathlib predicates; the prime-divisor and square-root quantifiers are unbounded. `jsp_000301` directly negates the catalog's universal assertion. This does not address the separate counting-bound question in [Erdős #365](https://www.erdosproblems.com/365).

## Construction and statement correspondence

Begin with `(x₀, y₀) = (23, 78)` and set

```text
xₖ₊₁ = 24335 xₖ +  7176 yₖ
yₖ₊₁ = 82524 xₖ + 24335 yₖ
nₖ   = 23 xₖ²
```

The inductively proved invariants are `23 xₖ² + 1 = 2 yₖ²`, `23 ∣ xₖ`, `2 ∣ yₖ`, `k + 23 ≤ xₖ`, and `yₖ > 0`. Consequently both `nₖ` and `nₖ + 1` are powerful. Their factorizations have odd exponents at 23 and 2 respectively, which excludes squareness. The growth bound gives `n_B > B`, establishing infinitely many distinct counterexamples.

The first pair is `(12167, 12168)`; the next is `(28821995554247, 28821995554248)`. The proofs of the invariants and unboundedness cover every index, without finite enumeration or an assumed Pell theorem.

## Mathematical credit and previous submissions

The mathematics is classical, not a new discovery. The seed is Golomb's counterexample, already recorded in the catalog. The recurrence specializes the Pell multiplication method in D. T. Walker, *Consecutive Integer Pairs of Powerful Numbers and Related Diophantine Equations*, Fibonacci Quarterly 14 (1976), 111–116, [Lemma 3.3](https://www.fq.math.ca/Scanned/14-2/walker.pdf). Its multiplier `24335 + 3588√46` satisfies `24335² − 46·3588² = 1`; Walker also records this unit in Section 2.

Earlier JSP-000301 formalizations include PRs [#13](https://github.com/TheJustinSunPrize/awards/pull/13), [#17](https://github.com/TheJustinSunPrize/awards/pull/17), [#55](https://github.com/TheJustinSunPrize/awards/pull/55), [#103](https://github.com/TheJustinSunPrize/awards/pull/103), and [#187](https://github.com/TheJustinSunPrize/awards/pull/187), and issue [#25](https://github.com/TheJustinSunPrize/awards/issues/25). The original disproof therefore overlaps existing work. This submission requests review specifically of the recursive infinite family and its unboundedness proof. A bounded search of the repository's issue and PR descriptions on 2026-09-17 found no submission of this family; it does not establish global priority. The Lean source here was developed for this submission, without importing those proof packages.

Prepared with OpenAI Codex assistance. Any formalization-recipient identity remains `RECIPIENT-JSP000301-INFINITE-A`, confirmation pending. Contributor verification is not an independent referee attestation. No catalog eligibility flags, candidate records, award decisions or payment status are changed.

## Reproduction and verification

Lean is pinned to `v4.34.0`; Mathlib is pinned to commit `5ed2965256430c3649e86755f9576b54eca72435`, with transitive dependencies locked in [lake-manifest.json](lake-manifest.json). From this directory, with Lean's version manager installed:

```sh
lake exe cache get Mathlib/Data/Nat/Factorization/Defs.lean Mathlib/Tactic/Linarith.lean Mathlib/Tactic/NormNum/Prime.lean
lake build
lake env leanchecker --verbose Main
```

The cache command accelerates the build; the proof-checking entry point is `lake build`. The source prints axiom reports for all three public results. The exact-module replay checks this submission's compiled declarations against its imported environment. It uses Lean's own kernel, not an independently implemented checker.

Local checks on macOS arm64, 2026-09-17: `lake build`, direct source elaboration, and exact-module kernel replay passed. Each public result depends only on `propext`, `Classical.choice`, and `Quot.sound`. There are no proof holes, new axiom declarations or compiler-based decision proofs. Imported standard-library and pinned Mathlib cache artifacts remain trusted; a full dependency rebuild and independent organizer verification are not claimed.

| Artifact | Bytes | SHA-256 |
| --- | ---: | --- |
| `Main.lean` | 3843 | `a386283cda7ba0434bcaa4c8e16df0b6cfa9eceeeaae30a53969bb663e953218` |
| `lake-manifest.json` | 3550 | `1c1dedd4443f20f76c3429046fc110453df202980f7589e912b7598cbf66faff` |

The six-file proof package at Git commit `5f4829ebc106688bf5821a648250400315fc089d` is permanently archived in Software Heritage as [`swh:1:dir:4793210223f03742780e770dbf1d892b99f84ccb`](https://archive.softwareheritage.org/swh:1:dir:4793210223f03742780e770dbf1d892b99f84ccb/). [Archival request 2481747](https://archive.softwareheritage.org/api/1/origin/save/2481747/) completed successfully with a full visit. All six archived files were retrieved and matched byte-for-byte to that commit; the source and dependency-lock sizes and SHA-256 values are listed above. Designated independent verifier review remains pending. Local proof checks and repository CI do not determine prize eligibility or an award.
