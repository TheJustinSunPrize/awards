# JSP-000963: Erdős 1158, Erdős's 1964 bounds n^{t − O(r^{1−t})} ≤ ex_t(n, K_t(r)) ≪ n^{t − r^{1−t}} for complete t-partite t-uniform hypergraphs

Catalog entry: [JSP-000963](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0901-1000.md#JSP-000963) · Problem source: [erdosproblems.com/1158](https://www.erdosproblems.com/1158)

## Problem

Let `K_t(r)` be the complete `t`-partite `t`-uniform hypergraph with `r` vertices in each class. Is it true that `ex_t(n, K_t(r)) ≥ n^{t − r^{1−t} − o(1)}` for all `t, r`?

## Scope

Partial progress: the bounds recorded on erdosproblems.com/1158 and credited in the catalog record JSP-000963 to Erdős [Er64f], `n^{t − O(r^{1−t})} ≤ ex_t(n, K_t(r)) ≪ n^{t − r^{1−t}}`, with the lower bound in the form `n^{t − t·r^{1−t}}` (the implied constant in `O(r^{1−t})` is `t`; Erdős states a constant independent of the uniformity, which is not established here). The question itself (exponent `t − r^{1−t} − o(1)`, known only for `t = 2`, `r ≤ 3`) remains open and is not claimed.

## Formal statements

All results are in `Erdos1158.lean`. formal-conjectures has no file for Erdős 1158; `Uniform` and `ContainsKt` are copied verbatim from the statement-only file `Statements/Erdos1158KtrHypergraphLowerBound.lean` in WoshuaJolk/jig-verifier (Apache-2.0; no proof code exists there or was used). `ex` is defined in the file and shown to be a genuine maximum.

```lean
theorem erdos_1158 (t r : ℕ) (ht : 1 ≤ t) (hr : 2 ≤ r) :
    (∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, 2 * t ≤ n →
      c * (n : ℝ) ^ ((t : ℝ) - t * (r : ℝ) ^ (1 - (t : ℝ))) ≤ ex t r n) ∧
    (∃ C : ℝ, 0 < C ∧ ∀ n : ℕ,
      (ex t r n : ℝ) ≤ C * (n : ℝ) ^ ((t : ℝ) - (r : ℝ) ^ (1 - (t : ℝ))))

theorem erdos_1158_upper (t r : ℕ) (ht : 1 ≤ t) (hr : 1 ≤ r) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, ∀ E : Finset (Finset (Fin n)), Uniform E t →
      ¬ ContainsKt E t r → (#E : ℝ) ≤ C * (n : ℝ) ^ ((t : ℝ) - (r : ℝ) ^ (1 - (t : ℝ)))

theorem erdos_1158_upper_explicit (t r : ℕ) (ht : 1 ≤ t) (hr : 1 ≤ r) (n : ℕ)
    (E : Finset (Finset (Fin n))) (hE : Uniform E t) (hK : ¬ ContainsKt E t r) :
    (#E : ℝ) ≤ boxConst r (t - 1) * (n : ℝ) ^ ((t : ℝ) - (r : ℝ) ^ (1 - (t : ℝ)))

theorem erdos_1158_lower (t r : ℕ) (ht : 1 ≤ t) (hr : 2 ≤ r) :
    ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, 2 * t ≤ n → ∃ E : Finset (Finset (Fin n)), Uniform E t ∧
      ¬ ContainsKt E t r ∧ c * (n : ℝ) ^ ((t : ℝ) - t * (r : ℝ) ^ (1 - (t : ℝ))) ≤ #E

theorem erdos_1158_lower_explicit (t r : ℕ) (ht : 1 ≤ t) (hr : 2 ≤ r) (n : ℕ) (hn : 2 * t ≤ n) :
    ∃ E : Finset (Finset (Fin n)), Uniform E t ∧ ¬ ContainsKt E t r ∧
      (n : ℝ) ^ ((t : ℝ) - t * ((r : ℝ) - 1) / ((r : ℝ) ^ t - 1)) / lowerConst t r ≤ #E

theorem erdos_1158_lower_eventually (t r : ℕ) (ht : 1 ≤ t) (hr : 2 ≤ r) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∃ E : Finset (Finset (Fin n)), Uniform E t ∧ ¬ ContainsKt E t r ∧
      (n : ℝ) ^ ((t : ℝ) - t * ((r : ℝ) - 1) / ((r : ℝ) ^ t - 1) - ε) ≤ #E

theorem deletion_exponent_le (t r : ℕ) (ht : 1 ≤ t) (hr : 2 ≤ r) :
    (t : ℝ) * ((r : ℝ) - 1) / ((r : ℝ) ^ t - 1) ≤ t * (r : ℝ) ^ (1 - (t : ℝ))

theorem card_le_ex {t r n : ℕ} {E : Finset (Finset (Fin n))} (hE : Uniform E t)
    (hK : ¬ ContainsKt E t r) : #E ≤ ex t r n

theorem exists_card_eq_ex (t r n : ℕ) (hr : 1 ≤ r) :
    ∃ E : Finset (Finset (Fin n)), Uniform E t ∧ ¬ ContainsKt E t r ∧ #E = ex t r n
```

With `Uniform E t`, `ContainsKt E t r` (copied from the jig-verifier statement file, Apache-2.0) and `ex t r n` the maximum size of a `K_t(r)`-free `t`-uniform hypergraph on `Fin n` (`card_le_ex`, `exists_card_eq_ex`): `erdos_1158_upper : 1 ≤ t → 1 ≤ r → ∃ C > 0, ∀ n E, Uniform E t → ¬ ContainsKt E t r → #E ≤ C·n^{t − r^{1−t}}` (explicit constant in `erdos_1158_upper_explicit`), `erdos_1158_lower : 1 ≤ t → 2 ≤ r → ∃ c > 0, ∀ n ≥ 2t, ∃ E, Uniform E t ∧ ¬ ContainsKt E t r ∧ c·n^{t − t·r^{1−t}} ≤ #E` (with the sharper deletion exponent `t − t(r−1)/(r^t−1)` in `erdos_1158_lower_explicit` / `erdos_1158_lower_eventually`, and `deletion_exponent_le`), and the combined `erdos_1158` for `ex`.

## Proof outline

Upper bound: Erdős's induction on the uniformity in a 'box' form — a set of `(t+1)`-tuples with no `r × ⋯ × r` box satisfies `|S|^{r^t}·n ≤ K_t·n^{(t+1)r^t}` — obtained by double counting `r`-sets of extensions, `d^r ≤ r^r·r!·(C(d,r)+1)` and the power-mean inequality; injective ordered edges connect this to hypergraphs (injectivity forces disjoint parts). Lower bound: first-moment deletion written with binomial weights (no probability library): keep each `t`-set with weight `p = c·n^{−β}`, `β = t(r−1)/(r^t−1)`, count at most `n^{rt}` potential copies of `K_t(r)`, and delete one edge from each copy.

## Build and verification

- Lean `v4.34.0` (`leanprover/lean4:v4.34.0`)
- Mathlib tag `v4.34.0`, commit `5ed2965256430c3649e86755f9576b54eca72435`; all dependencies are pinned in `lake-manifest.json`

```sh
lake exe cache get
lake build
```

`#print axioms` (see `verification/axioms.txt`):

```
'Erdos1158.erdos_1158' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos1158.erdos_1158_upper' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos1158.erdos_1158_upper_explicit' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos1158.erdos_1158_lower' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos1158.erdos_1158_lower_explicit' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos1158.erdos_1158_lower_eventually' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos1158.deletion_exponent_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos1158.card_le_ex' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos1158.exists_card_eq_ex' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The file contains no `sorry`, no `axiom` declarations and no `native_decide`. The build log and the SHA-256 of
`Erdos1158.lean` (`1bf516202d10ff5758b6319e7dd46b6fd2d81f97a46f06b1bd082605cbf839c7`) are in `verification/`.

## Attribution

- Mathematics: P. Erdős, *On extremal problems of graphs and generalized graphs*, Israel J. Math. 2 (1964) 183–190 [Er64f], Theorem 1, cited by the catalog record JSP-000963 and erdosproblems.com/1158 (Erdős proves the upper bound and indicates the lower bound follows by combining his methods with Erdős–Rényi's). The deletion-method presentation and constants were written during the AI-assisted formalization.
- Lean formalization: GitHub user `baobingzhang`, developed with AI assistance (Anthropic Claude).


No priority for the mathematics is claimed; the contribution is the Lean formalization.
