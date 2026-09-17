# JSP-000445: Erdős 554 for every n ≥ 4: R_k(C_{2n+1})/R_k(K_3) → 0, via the ACJMR25 bound R_k(C_{2l+1}) ≤ (4l−2)^k k^{k/l} + 1

Catalog entry: [JSP-000445](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0401-0500.md#JSP-000445) · Problem source: [erdosproblems.com/554](https://www.erdosproblems.com/554)

## Problem

Let `R_k(G)` be the least `m` such that every `k`-colouring of the edges of `K_m` has a monochromatic copy of `G`. Show that `lim_{k→∞} R_k(C_{2n+1}) / R_k(K_3) = 0` for every `n ≥ 2`.

## Scope

Partial progress: the statement of Erdős Problem 554 is proved for every `n ≥ 4`, and the problem is formally reduced to the two open cases `n = 2` (`C_5`) and `n = 3` (`C_7`), which remain open and are not claimed. The ingredients are Theorem 1.1 of Axenovich–Cames van Batenburg–Janzer–Michel–Rundström (arXiv:2510.17981, formalized here in full, with Lemma 2.1 for colourings with `k` colours in total and the Erdős–Faudree–Rousseau–Schelp level lemma) and OpenAI's lower bound for `R_k(K_3)` (Lean code from openai/ten-proofs, Apache-2.0, reused with attribution). The combination for `n ≥ 4` was pointed out on the erdosproblems.com forum in August 2026; this submission is its machine-checked version. Theorem 1.2 of ACJMR25 and the `k`-local version of Lemma 2.1 are not formalized.

## Formal statements

All results are in `Erdos554.lean`. OpenAI's file `MulticolorTriangleRamsey.lean` (openai/ten-proofs @94bc0feb, Apache-2.0) is included as Part I with its license notice and a list of modifications (six deprecated lemma names replaced for Mathlib v4.34). `oddCycleRamseyNumber` and the #554 statement are defined in the file with OpenAI's edge-colouring conventions (`TopEdgeLabeling (Fin n) (Fin k)`, `labelGraph`, copies via `⊑`). formal-conjectures has no file for Erdős 554. The idea of organising the EFRS argument along a BFS address order was suggested by the declaration outline of an unlicensed Erdős 570 development in plby/lean-proofs; no code from it is used.

```lean
theorem erdos_554_of_four_le {n : ℕ} (hn : 4 ≤ n) : Erdos554Statement n

theorem erdos_554_iff : Erdos554Problem ↔ Erdos554Statement 2 ∧ Erdos554Statement 3

theorem oddCycleRamseyNumber_le {k l : ℕ} (hk : 1 ≤ k) (hl : 1 ≤ l) :
    (oddCycleRamseyNumber l k : ℝ) ≤ (4 * (l : ℝ) - 2) ^ k * (k : ℝ) ^ ((k : ℝ) / l) + 1

theorem hasMonoOddCycle_of_lt {n k l : ℕ} (hk : 1 ≤ k) (hl : 1 ≤ l)
    (hn : (4 * (l : ℝ) - 2) ^ k * (k : ℝ) ^ ((k : ℝ) / l) < n)
    (C : TopEdgeLabeling (Fin n) (Fin k)) : HasMonoOddCycle C l

theorem card_le_of_colorable {V : Type*} [Fintype V] [DecidableEq V] {k l χ : ℕ}
    (hk : 1 ≤ k) (hl : 1 ≤ l) (C : TopEdgeLabeling V (Fin k))
    (hcol : ∀ (v : V) (c : Fin k),
      ((C.labelGraph c).induce
        {x | (C.labelGraph c).Reachable v x ∧ (C.labelGraph c).dist v x ≤ l}).Colorable χ) :
    (Fintype.card V : ℝ) ≤ (χ : ℝ) ^ k * (k : ℝ) ^ ((k : ℝ) / l)

theorem level_colorable {l i : ℕ} (hfree : ¬ (cycleGraph (2 * l + 1)).IsContained G)
    (hi : 1 ≤ i) (hil : i ≤ l) :
    (G.induce {x | G.dist v x = i}).Colorable (2 * l - 1)

theorem exists_forcesMonoOddCycle {k l : ℕ} (hk : 1 ≤ k) (hl : 1 ≤ l) :
    ∃ n, ForcesMonoOddCycle l n k

theorem forcesMonoOddCycle_iff {k l n : ℕ} (hk : 1 ≤ k) (hl : 1 ≤ l) :
    ForcesMonoOddCycle l n k ↔ oddCycleRamseyNumber l k ≤ n

theorem oddCycleRamseyNumber_one (k : ℕ) :
    oddCycleRamseyNumber 1 k = triangleRamseyNumber k

theorem quantitativeLowerBound_explicit_all :
    ∀ k : ℕ, 2 ≤ k →
      (((1 : ℝ) / (6 * Real.exp 38)) *
        (k : ℝ) ^ ((1 : ℝ) / 3) / Real.log (k : ℝ)) ^ k ≤
          (triangleRamseyNumber k : ℝ)
```

`oddCycleRamseyNumber_le : 1 ≤ k → 1 ≤ l → (R_k(C_{2l+1}) : ℝ) ≤ (4l−2)^k · k^{k/l} + 1` (ACJMR25 Theorem 1.1; colouring form `hasMonoOddCycle_of_lt`), `card_le_of_colorable` (ACJMR25 Lemma 2.1), `level_colorable` (EFRS78 level lemma), `erdos_554_of_four_le : 4 ≤ n → Tendsto (fun k => R_k(C_{2n+1}) / R_k(K_3)) atTop (𝓝 0)` and `erdos_554_iff : Erdos554Problem ↔ Erdos554Statement 2 ∧ Erdos554Statement 3`. The Ramsey numbers are genuine minima: `exists_forcesMonoOddCycle` (nonempty `sInf` set), `forcesMonoOddCycle_iff` (threshold property), and `oddCycleRamseyNumber_one` shows the definition agrees with OpenAI's `triangleRamseyNumber` for `l = 1`.

## Proof outline

(1) EFRS level lemma: order each BFS level by an ancestor-address key and colour vertices by the length of the longest key-increasing path (Gallai–Roy); a long increasing path yields a segment whose endpoints merge at a critical depth, which together with the two ancestor chains forms a `C_{2l+1}`. Colouring balls by distance parity and level colour gives `4l−2` colours. (2) ACJMR25 Lemma 2.1 by strong induction on vertex sets with weights `β^{-d_S(u)}`, `β = χ k^{1/l}`: pick a colour carrying weight at `v`, a radius where the ball grows by at most `k^{1/l}`, a heaviest colour class of the ball, delete the rest of the next ball; the total weight does not decrease. For `S = V`, `|V| ≤ χ^k k^{k/l}`. (3) Theorem 1.1 with `χ = 4l−2`. (4) With OpenAI's `R_k(K_3) ≥ (k^{1/3}/(6e^{38} log k))^k`, for `n ≥ 4` one has `1/n < 1/3`, so eventually `R_k(C_{2n+1}) ≤ 2^{1−k} R_k(K_3)`.

## Build and verification

- Lean `v4.34.0` (`leanprover/lean4:v4.34.0`)
- Mathlib tag `v4.34.0`, commit `5ed2965256430c3649e86755f9576b54eca72435`; all dependencies are pinned in `lake-manifest.json`

```sh
lake exe cache get
lake build
```

`#print axioms` (see `verification/axioms.txt`):

```
'Erdos554.erdos_554_of_four_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos554.erdos_554_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos554.oddCycleRamseyNumber_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos554.hasMonoOddCycle_of_lt' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos554.card_le_of_colorable' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos554.level_colorable' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos554.exists_forcesMonoOddCycle' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos554.forcesMonoOddCycle_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos554.oddCycleRamseyNumber_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosProblems.MulticolourTriangleRamsey.quantitativeLowerBound_explicit_all' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

The file contains no `sorry`, no `axiom` declarations and no `native_decide`. The build log and the SHA-256 of
`Erdos554.lean` (`98786812071e60c11badabe66b53947585e387b93c94adaf29e7342a669e0d70`) are in `verification/`.

## Attribution

- Mathematics: M. Axenovich, W. Cames van Batenburg, O. Janzer, L. Michel, M. Rundström, *An improved upper bound for the multicolour Ramsey number of odd cycles*, arXiv:2510.17981 (2025) [ACJMR25], cited by the catalog record JSP-000445; P. Erdős, R. J. Faudree, C. C. Rousseau, R. H. Schelp, J. Graph Theory 2 (1978) [EFRS78]; OpenAI, *Ten advances in mathematics and theoretical computer science* (2026), Chapter 9 (lower bound for R_k(K_3), Erdős 183), with Lean code at github.com/openai/ten-proofs (Apache-2.0); the deduction for n ≥ 4 was noted on the erdosproblems.com/554 forum (mysticflounder, 2026-08-01; W. Cames van Batenburg, 2026-08-02). Problem of Erdős and Graham [Er81c].
- Lean formalization: GitHub user `baobingzhang`, developed with AI assistance (Anthropic Claude).


No priority for the mathematics is claimed; the contribution is the Lean formalization.
