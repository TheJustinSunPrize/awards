# JSP-000859: Erdős 1033: the answer to 'is h(n) ≥ (2(√3−1) − o(1))n?' is no (butterfly blow-up construction, 2026)

Catalog entry: [JSP-000859](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0801-0900.md#JSP-000859) · Problem source: [erdosproblems.com/1033](https://www.erdosproblems.com/1033)

## Problem

Let `h(n)` be such that every graph on `n` vertices with `> n²/4` edges contains a triangle whose vertices have degrees summing to at least `h(n)`. Estimate `h(n)`. In particular, is it true that `h(n) ≥ (2(√3−1) − o(1))n`?

## Scope

Partial progress: the explicit 'in particular' question of Erdős Problem 1033 is answered in the negative, formalizing the butterfly blow-up construction posted on the erdosproblems.com/1033 forum in 2026 (rickyc with GPT-5.5 Pro; confirmed by J. Land; densities optimized by W. Cames van Batenburg). Estimating `h(n)` in general (between Fan's `21n/16` and about `1.4639n`) remains open, and the upper bound `h(n) ≤ 1.46392n + O(1)` for all `n` is not formalized (only along `n = 10060s`).

## Formal statements

All results are in `Erdos1033.lean`. formal-conjectures has no file for Erdős 1033; `h` follows the erdosproblems.com wording and the statement-only proposal in formal-conjectures PR #5885 (closed, not merged). `h_spec`, `le_h` and `erdos_1033_of_bound` show the result does not depend on the `sSup` convention.

```lean
theorem erdos_1033 :
    ¬ ∃ o : ℕ → ℝ, o =o[atTop] (1 : ℕ → ℝ) ∧
      ∀ᶠ n : ℕ in atTop, (2 * (Real.sqrt 3 - 1) - o n) * n ≤ h n

theorem erdos_1033_eps :
    ¬ ∀ ε > (0 : ℝ), ∀ᶠ n : ℕ in atTop, (2 * (Real.sqrt 3 - 1) - ε) * n ≤ h n

theorem erdos_1033_of_bound (f : ℕ → ℝ)
    (hf : ∀ n, ∀ G : SimpleGraph (Fin n), (n : ℝ) ^ 2 / 4 < (G.edgeSet.ncard : ℝ) →
      ∃ T : Finset (Fin n), G.IsNClique 3 T ∧ f n ≤ (∑ v ∈ T, G.degree v : ℝ)) :
    ¬ ∃ o : ℕ → ℝ, o =o[atTop] (1 : ℕ → ℝ) ∧
      ∀ᶠ n : ℕ in atTop, (2 * (Real.sqrt 3 - 1) - o n) * n ≤ f n

theorem exists_graph (s : ℕ) (hs : 0 < s) :
    ∃ H : SimpleGraph (Fin (10060 * s)),
      ((10060 * s : ℕ) : ℝ) ^ 2 / 4 < (H.edgeSet.ncard : ℝ) ∧
      (∃ T : Finset (Fin (10060 * s)), H.IsNClique 3 T) ∧
      ∀ T : Finset (Fin (10060 * s)), H.IsNClique 3 T → ∑ v ∈ T, H.degree v = 14727 * s

theorem h_le (s : ℕ) (hs : 0 < s) : h (10060 * s) ≤ 14727 * s

theorem h_spec (n : ℕ) (G : SimpleGraph (Fin n))
    (hG : (n : ℝ) ^ 2 / 4 < (G.edgeSet.ncard : ℝ)) :
    ∃ T : Finset (Fin n), G.IsNClique 3 T ∧ h n ≤ (∑ v ∈ T, G.degree v : ℝ)

theorem le_h (n : ℕ) (hn : 3 ≤ n) (x : ℝ)
    (hx : ∀ G : SimpleGraph (Fin n), (n : ℝ) ^ 2 / 4 < (G.edgeSet.ncard : ℝ) →
      ∃ T : Finset (Fin n), G.IsNClique 3 T ∧ x ≤ (∑ v ∈ T, G.degree v : ℝ)) :
    x ≤ h n

theorem ratio_lt : (14727 : ℝ) / 10060 < 2 * (Real.sqrt 3 - 1)
```

With `h n := sSup {x : ℝ | ∀ G : SimpleGraph (Fin n), n²/4 < |E(G)| → ∃ T, G.IsNClique 3 T ∧ x ≤ ∑_{v∈T} deg v}` (the best such bound: `h_spec` shows `h n` itself has the defining property, via Mantel's theorem, and `le_h` shows every admissible `x` is at most `h n` for `n ≥ 3`): `exists_graph` gives, for every `s > 0`, a graph on `10060s` vertices with more than `n²/4` edges that contains a triangle and in which every triangle has degree sum exactly `14727s`; hence `h_le : h(10060s) ≤ 14727s`, `ratio_lt : 14727/10060 < 2(√3−1)`, and `erdos_1033 : ¬ ∃ o = o(1), ∀ᶠ n, (2(√3−1) − o n)·n ≤ h n`, `erdos_1033_eps`, and `erdos_1033_of_bound` (the same negation for every function with the defining property).

## Proof outline

The graph has five parts `a = Fin 16 × Fin(268s)`, `b = Fin(2476s)`, `c = Fin 16 × Fin(45s)`, `d = e = Fin 23 × Fin(56s)`, with complete joins `ab`, `bc`, `ad`, `ae` and circulant joins `a–c` (iff `(j − i) mod 16 < 7`) and `d–e` (iff `(j − i) mod 23 < 7`). Explicit counting gives degrees `5367s, 5008s, 4352s, 4680s, 4680s`; a case split shows every triangle has type `abc` or `ade`, with degree sum exactly `14727s`; the handshake lemma gives `25301312s² > (10060s)²/4` edges; and `34847² < 3·20120²` gives `14727/10060 < 2(√3−1) ≈ 1.4641`. Since the conjectured bound is an eventual statement, the subsequence `n = 10060s` refutes it.

## Build and verification

- Lean `v4.34.0` (`leanprover/lean4:v4.34.0`)
- Mathlib tag `v4.34.0`, commit `5ed2965256430c3649e86755f9576b54eca72435`; all dependencies are pinned in `lake-manifest.json`

```sh
lake exe cache get
lake build
```

`#print axioms` (see `verification/axioms.txt`):

```
'Erdos1033.erdos_1033' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos1033.erdos_1033_eps' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos1033.erdos_1033_of_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos1033.exists_graph' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos1033.h_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos1033.h_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos1033.le_h' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos1033.ratio_lt' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The file contains no `sorry`, no `axiom` declarations and no `native_decide`. The build log and the SHA-256 of
`Erdos1033.lean` (`630e361082f7997a47cf086d9aa1d129765ba55f017f91a795af2f8fdd4e03dc`) are in `verification/`.

## Attribution

- Mathematics: Construction: forum user rickyc (erdosproblems.com/forum/thread/1033, 27 June 2026, found with GPT-5.5 Pro), confirmed by Johan Land (26 July 2026) and optimized by Wouter Cames van Batenburg (27 July 2026); the integer parameters used here are a rational instance of the same butterfly blow-up found in our search. Problem of Bollobás and Erdős [Er82e, Er93]; earlier bounds by Erdős–Laskar [ErLa85] and Fan [Fa88], cited by the catalog record JSP-000859.
- Lean formalization: GitHub user `baobingzhang`, developed with AI assistance (Anthropic Claude).


No priority for the mathematics is claimed; the contribution is the Lean formalization.
