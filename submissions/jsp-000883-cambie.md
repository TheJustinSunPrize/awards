# JSP-000883: Cambie's least-common-multiple upper bound

**Proposed intake record; maintainer direction and designated verification pending.** This record accompanies the included Lean formalization of Stijn Cambie's known partial result for [Erdős Problem 1063](https://www.erdosproblems.com/1063). It does not announce an award or change the catalog's screening fields.

```lean
theorem Erdos1063.erdos_1063.variants.cambie_upper_bound
    {k : ℕ} (hk : 3 ≤ k) :
    Erdos1063.n k ≤ k * (Finset.Icc 1 (k - 1)).lcm id
```

`n k` is the least natural `n ≥ 2*k` for which exactly one of `n, …, n-k+1` fails to divide `Nat.choose n k`. The explicit witness `N = k*lcm(1,…,k-1)` has exceptional offset zero and proves the defining set is nonempty. All arithmetic and the least common multiple are over natural numbers.

The addition beyond [PR #56](https://github.com/TheJustinSunPrize/awards/pull/56), head `40446d5328cd5b23d4f7ac0569931deca13b6bcd`, is Cambie's least-common-multiple bound; that PR covers Monier's factorial bound. Official searches refreshed on 2026-09-16 found no other directly relevant PR. This is bounded screening, not a global-priority claim.

Mathematical credit: **Stijn Cambie**. The definition is reproduced with the Formal Conjectures Authors' Apache-2.0 attribution from [fixed source](https://github.com/google-deepmind/formal-conjectures/blob/40e7c98697de6f66b8cbdbf641749ab39ed9c152/FormalConjectures/ErdosProblems/1063.lean). The Lean implementation and supporting materials were prepared with Codex assistance. The proof repository preserves third-party licenses and attribution. No new mathematical result or solution of the full growth-rate problem is claimed.

## Pinned evidence

- [Included proof package](jsp-000883-cambie/README.md): [statement](jsp-000883-cambie/Statement.lean), [proof](jsp-000883-cambie/Cambie.lean), [audit](jsp-000883-cambie/Audit.lean), pinned configuration, verification script, and disclosed redacted evidence.
- Repository: [pcycho/erdos1063-cambie](https://github.com/pcycho/erdos1063-cambie).
- [Fixed source commit](https://github.com/pcycho/erdos1063-cambie/tree/396c09bfdf4cf8306261b8176a1917aa72135459): `396c09bfdf4cf8306261b8176a1917aa72135459`.
- [Versioned release](https://github.com/pcycho/erdos1063-cambie/releases/tag/v1.0.0): release ID `390108377`.
- [Evidence ZIP](https://github.com/pcycho/erdos1063-cambie/releases/download/v1.0.0/erdos1063-cambie-public.zip): SHA-256 `12e771df851260f230f62cf55b544719acdef8e290324796fb689d69cae7d152`; `72757` bytes.
- Toolchain: Lean `4.33.1`; Mathlib `0df444a360eaa60ab8c11dca51a86af692955474`; transitive dependencies pinned by the manifest.

The included directory is a byte-for-byte copy of the 71-file public package in that fixed source commit and release. Its [package hash manifest](jsp-000883-cambie/PACKAGE_SHA256.json) covers the other 70 files, and the eight audited source/configuration hashes in [the verification record](jsp-000883-cambie/logs/results.json) match the included files. No proof logic or recorded evidence was changed when adding this directory. Lean binaries, compiled libraries, dependency caches, private logs, and the ZIP itself are excluded. The external source commit and release remain available as the fixed reference copy.

From the awards repository root, enter `submissions/jsp-000883-cambie/`, obtain the pinned toolchain and dependency cache as described in its [README](jsp-000883-cambie/README.md), and run `python -X utf8 verify.py`. Recorded run `e38f0a6fd3e344dfa4cc67d05e224346` completed at 2026-09-16 16:44:03 UTC, exit 0: project recompilation, statement alignment, axiom audit, negative tests, and same-kernel fresh replay passed. Each audited declaration depends only on `propext`, `Classical.choice`, and `Quot.sound`. This exact-byte inclusion does not claim a new Lean execution. Official caches were used; all of Mathlib was not rebuilt, and no separate kernel implementation was run. Public evidence contains explicitly labeled redacted logs; original outputs remain local.

## Pending review

The release is an external versioned copy, not a permanent DOI archive. Permanent archival and the proposed intake location remain pending; review is requested with those limitations disclosed. No official verification, prize eligibility, priority, or allocation is asserted.

`pcycho` is the publishing GitHub account, not a verified legal identity or confirmed recipient. Any prospective recipient remains `RECIPIENT-JSP-000883-A` pending confirmation. This record makes no recipient nomination or award announcement.
