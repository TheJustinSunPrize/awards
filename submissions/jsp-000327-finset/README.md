# JSP-000327: finite-set resolution and a three-factor criterion

This package gives a complete negative answer to [JSP-000327](../../problems/catalog-0301-0400.md#JSP-000327), corresponding to [Erdős #397](https://www.erdosproblems.com/397). Let `C(n) = binomial(2n,n)`. There are infinitely many pairs of disjoint finite sets of natural indices with equal products of `C`. The terminal theorem uses the original finite-set formulation directly:

```lean
theorem jsp_000327 :
    ¬ {s : Finset ℕ × Finset ℕ | Disjoint s.1 s.2 ∧
      s.1.prod Nat.centralBinom = s.2.prod Nat.centralBinom}.Finite
```

The exhibited sets are nonempty, each contains three distinct indices, and every index can exceed any prescribed bound. Thus the counterexamples also satisfy restrictions excluding zero indices, repeated factors and empty products. This is an infinite family, not a finite search or a single example. It does not classify all possible equalities between arbitrary finite sets.

## Solution and additional criterion

The factorial definition gives the positive-coefficient recurrence

```text
C(n+1) / C(n) = 2(2n+1)/(n+1).
```

Applying it at `a`, `b`, `b+1` and `c`, and cancelling the nonzero coefficients, gives the general equivalence proved in `three_factor_iff`, for all natural `a,b,c`:

```text
C(a) C(b+2) C(c) = C(a+1) C(b) C(c+1)
    if and only if
(a+1)(2b+1)(2b+3)(c+1) = (2a+1)(b+1)(b+2)(2c+1).
```

There are no hypotheses that these six indices are distinct in this auxiliary algebraic criterion. Distinctness is proved separately for the family used to solve the original problem.

For `b = 2a`, write `A = (a+1)(4a+1)(4a+3)` and `D = 2(a+1)(2a+1)²`. The criterion is `A(c+1) = D(2c+1)`. Expansion gives

```text
2D − A = a+1,
A − D = (a+1)(8a²+8a+1).
```

Consequently `(a+1)c = (a+1)(8a²+8a+1)`. Since `a+1` is positive, the equality holds exactly when `c = 8a²+8a+1`. `doubled_middle_iff` proves both directions, including uniqueness within this parameter pattern.

Set `c = 8a²+8a+1` and, for each `a ≥ 2`, define

```text
M(a) = {a,   2a+2, c  },
N(a) = {a+1, 2a,   c+1}.
```

The strict ordering `a < a+1 < 2a < 2a+2 < c < c+1` proves that all six indices are distinct. The criterion proves equality of the two products. The minimum of `M(a) ∪ N(a)` is `a`; hence different parameters give different set pairs. Injecting the natural numbers by `k ↦ (M(k+2), N(k+2))` proves that the original solution set is infinite. Choosing `a = B+2` proves the stronger `unbounded_solutions` statement with all six indices greater than `B`. For example, `a=2` gives `M={2,6,49}` and `N={3,4,50}`.

## Prior work and contribution scope

The quadratic infinite family is already attributed to Neel Somani and GPT-5.2 Pro; a Lean proof is attributed to Lawrence Wu and Aristotle in the [catalog-linked pinned source](https://github.com/plby/lean-proofs/blob/1268917deaaaa0d674f651287027baa26cea9920/src/latest/ErdosProblems/Erdos397.lean). That source establishes infinitely many list pairs with no repeated indices. Related recipient recommendation [#220](https://github.com/TheJustinSunPrize/awards/issues/220) predates this submission. Neither the infinite family nor the negative answer is claimed as a new mathematical discovery or a first Lean proof.

The review request is limited to the independently developed general three-factor equivalence, its doubled-middle uniqueness consequence, and the explicit finite-set statement correspondence with cardinalities, disjointness and unbounded indices. These two auxiliary equivalences are not stated in the catalog-linked source; this comparison does not establish global priority. This package imports Mathlib only, and neither imports nor copies the earlier submission's Lean proof.

Prepared with OpenAI Codex assistance. Any formalization-recipient identity remains `RECIPIENT-JSP000327-FINSET-A`, confirmation pending. No catalog status, eligibility flag, candidate, award decision or payment status is changed. Any novelty assessment, eligibility decision and designated independent verification belong to the organizers.

## Reproduction and verification

Lean is pinned to `v4.34.0`; Mathlib is pinned to `5ed2965256430c3649e86755f9576b54eca72435`, with transitive dependencies locked in [lake-manifest.json](lake-manifest.json). With the pinned Lean toolchain installed, run from this directory:

```sh
lake exe cache get Mathlib.Data.Nat.Choose.Central Mathlib.Data.Rat.Cast.Order Mathlib.Data.Set.Finite.Basic Mathlib.Tactic.FieldSimp Mathlib.Tactic.Linarith Mathlib.Tactic.NormNum Mathlib.Tactic.Positivity Mathlib.Tactic.Ring
lake build
lake env leanchecker --verbose Main
```

The cache command accelerates the build; `lake build` is the normal proof-checking entry point. All five public results print their axiom reports. Local build, direct elaboration and exact-module kernel replay on macOS arm64, 2026-09-17, passed with only `propext`, `Classical.choice` and `Quot.sound`. There are no proof holes, new axiom declarations or compiler-based decision proofs. The exact-module replay uses Lean's own kernel and the pinned imported environment; a full dependency rebuild or an independently implemented checker is not claimed.

| Artifact | Bytes | SHA-256 |
| --- | ---: | --- |
| `Main.lean` | 5369 | `84c0d0531eb91958aa0848d323738052328aca8c0edcfb7494f174a996a11b8c` |
| `lake-manifest.json` | 3548 | `0bbf1b25564f2c16834270d97386b11ce890e316eeff7c3911ba8f442cba86db` |

Permanent archival evidence, including its immutable identifier and byte comparison, is recorded in the pull request once available. Designated independent verification remains pending. Local checks and repository CI do not establish prize eligibility or an award.
