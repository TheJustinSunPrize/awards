# JSP-000108 proof-source pointer

## English

**The complete local build, full fresh kernel replay, and canonical-axiom declaration comparison passed. This candidate does not claim completed official verification or an award.**

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
| Proof commit | `2adec0fcdef83bc137eecfe4a01d08f98d1d6a9a` |
| Source archive | [release archive](https://github.com/c0ldzy17/jsp-000108-lean/releases/download/v1.0.0/jsp-000108-source.zip) |
| SHA-256 | `01c27dce2820c79bdda6ed400b13d69736847e1db7e971d9fda984cd53e42ef8` |
| Bytes | `5016196` |
| Build evidence | [build log](https://github.com/c0ldzy17/jsp-000108-lean/blob/2adec0fcdef83bc137eecfe4a01d08f98d1d6a9a/lake-build.log) |
| Endpoint axiom audit | [axioms](https://github.com/c0ldzy17/jsp-000108-lean/blob/2adec0fcdef83bc137eecfe4a01d08f98d1d6a9a/axioms.txt) |
| Fresh kernel replay | [replay](https://github.com/c0ldzy17/jsp-000108-lean/blob/2adec0fcdef83bc137eecfe4a01d08f98d1d6a9a/kernel-replay.txt) |

GitHub release ID: `390630986`; source archive asset ID: `570058056`. The published asset digest and byte count match the local archive. Large artifacts remain outside the awards repository, following its [record conventions](../../docs/records.md).

From the extracted archive root:

```sh
python3 scripts/prepare_pruning_geometry.py
lake exe cache get
sh scripts/verify.sh
```

Completed evidence: Lean 4.33.1 build with 10,329 jobs; all three endpoints use exactly propext, Classical.choice, Quot.sound; stock checking of all nine local modules; fresh replay of 132,794 declarations into an empty trust-level-zero environment. Canonical axiom kinds, types, and universe parameters also match the pinned toolchain Init. These are stock Lean kernel checks, not independent external reviews or a separately implemented kernel.

The mathematics is credited to [Sawin](https://arxiv.org/abs/2605.20579) and the [Alon–Bloom–Gowers–Litt–Sawin–Shankar–Tsimerman–Wang–Matchett Wood exposition](https://arxiv.org/abs/2605.20695). Formal reuse includes Naganori Yamaguchi, Logical Intelligence, Formal Conjectures authors, Kim Morrison, and plby. New integration and transfer work, source-specific licenses, and the unestablished license boundary for reconstructed plby adapters are documented in the archive.

The [observation candidate](../../candidates/observation/jsp-000108-c0ldzy17-subpolynomial-v1/citation.md) remains under verification. [PR 256](https://github.com/TheJustinSunPrize/awards/pull/256) has the narrower fixed-constant C / log log n scope. Official review, recipient confirmation, priority, and award decisions remain pending.

Additional evidence: [canonical axiom types](https://github.com/c0ldzy17/jsp-000108-lean/blob/2adec0fcdef83bc137eecfe4a01d08f98d1d6a9a/canonical-axioms.txt), [stock checker](https://github.com/c0ldzy17/jsp-000108-lean/blob/2adec0fcdef83bc137eecfe4a01d08f98d1d6a9a/leanchecker.txt), [environment](https://github.com/c0ldzy17/jsp-000108-lean/blob/2adec0fcdef83bc137eecfe4a01d08f98d1d6a9a/ENVIRONMENT.md).
