# JSP-000108 proof-source pointer

## English

**The revised complete build, fresh kernel replay, and canonical-axiom comparison passed. A separate rebuild from the published original archive also passed. This candidate does not claim completed official verification or an award.**

The target is the full subpolynomial question in [JSP-000108](https://github.com/TheJustinSunPrize/awards/blob/f4e7173d89dfe91022a185427d63452c8ffbf6ae/problems/catalog-0101-0200.md#JSP-000108), corresponding to the [canonical weak Erdos 92 variant](https://github.com/google-deepmind/formal-conjectures/blob/40e7c98697de6f66b8cbdbf641749ab39ed9c152/FormalConjectures/ErdosProblems/92.lean).

```text
Jsp108.jsp_000108 :
  ¬ ∃ o : ℕ → ℝ, o =o[atTop] (1 : ℕ → ℝ) ∧
    ∀ n, (Erdos92.f n : ℝ) ≤ (n : ℝ) ^ (o n)

Jsp108.jsp_000108_eventually :
  ¬ ∃ o : ℕ → ℝ, o =o[atTop] (1 : ℕ → ℝ) ∧
    ∀ᶠ n in atTop, (Erdos92.f n : ℝ) ≤ (n : ℝ) ^ (o n)
```

For each center in a finite planar set, f uses the maximum number of other points at a common distance from that center, then optimizes the minimum such count over sets of exactly n points. The radius may depend on the center. The eventual endpoint prevents exceptional small cardinalities from deciding the negative result.

| External evidence | Pinned reference |
|---|---|
| Proof repository | [c0ldzy17/jsp-000108-lean](https://github.com/c0ldzy17/jsp-000108-lean) |
| Proof commit | `11cfb8098dfb5527a5943d35b2698b4786233f4e` |
| Source archive | [release archive](https://github.com/c0ldzy17/jsp-000108-lean/releases/download/v1.1.0/jsp-000108-source.zip) |
| SHA-256 | `b375749d3f0a292c3096c17f42acfd1ce115b75ec2a39327699ffbacb81a9f79` |
| Bytes | `5052124` |
| Build evidence | [build log](https://github.com/c0ldzy17/jsp-000108-lean/blob/11cfb8098dfb5527a5943d35b2698b4786233f4e/lake-build.log) |
| Endpoint axiom audit | [axioms](https://github.com/c0ldzy17/jsp-000108-lean/blob/11cfb8098dfb5527a5943d35b2698b4786233f4e/axioms.txt) |
| Fresh kernel replay | [replay](https://github.com/c0ldzy17/jsp-000108-lean/blob/11cfb8098dfb5527a5943d35b2698b4786233f4e/kernel-replay.txt) |

GitHub release ID: `390698742`; source archive asset ID: `570231394`. The published asset digest and byte count match the local archive. Large artifacts remain outside the awards repository, following its [record conventions](../../docs/records.md).

From the extracted archive root:

```sh
lake exe cache get
sh scripts/verify.sh
```

Completed evidence: Lean 4.33.1 build with 10,329 jobs; all three endpoints use exactly propext, Classical.choice, Quot.sound; stock checking of all nine local modules; fresh replay of 132,615 declarations into an empty trust-level-zero environment. Canonical axiom kinds, types, and universe parameters also match the pinned toolchain Init. These are stock Lean kernel checks, not independent external reviews or a separately implemented kernel.

The mathematics is credited to [Sawin](https://arxiv.org/abs/2605.20579) and the [Alon–Bloom–Gowers–Litt–Sawin–Shankar–Tsimerman–Wang–Matchett Wood exposition](https://arxiv.org/abs/2605.20695). Formal reuse includes Naganori Yamaguchi, Logical Intelligence, Formal Conjectures authors, and Kim Morrison; the earlier plby development remains credited as prior work. Version 1.1 replaces the two previously reconstructed plby adapters with newly written pruning and geometry proofs, retains the explicitly licensed canonical definitions and boundedness lemma, and licenses the original additions under Apache-2.0. The earlier plby reduction remains credited; all upstream notices are preserved.

The [observation candidate](../../candidates/observation/jsp-000108-c0ldzy17-subpolynomial-v1/citation.md) remains under verification. [PR 256](https://github.com/TheJustinSunPrize/awards/pull/256) has the narrower fixed-constant C / log log n scope. Official review, recipient confirmation, priority, and award decisions remain pending.

Additional evidence: [canonical axiom types](https://github.com/c0ldzy17/jsp-000108-lean/blob/11cfb8098dfb5527a5943d35b2698b4786233f4e/canonical-axioms.txt), [stock checker](https://github.com/c0ldzy17/jsp-000108-lean/blob/11cfb8098dfb5527a5943d35b2698b4786233f4e/leanchecker.txt), [environment](https://github.com/c0ldzy17/jsp-000108-lean/blob/11cfb8098dfb5527a5943d35b2698b4786233f4e/ENVIRONMENT.md).

The original [v1.0.0 release](https://github.com/c0ldzy17/jsp-000108-lean/releases/tag/v1.0.0) remains available. Version 1.1 preserves the mathematical scope and supplies new adapter implementations and explicit licensing; it does not claim a new mathematical discovery.

Reproduction evidence: [original archive rebuild](https://github.com/c0ldzy17/jsp-000108-lean/blob/11cfb8098dfb5527a5943d35b2698b4786233f4e/original-clean-build.log). The pinned Mathlib cache was reused; the project and bundled proof developments began without compiled artifacts. The revised proof checks reused vendor outputs; the precise cache, source-comparison, and network-isolation scope is in the environment report.
