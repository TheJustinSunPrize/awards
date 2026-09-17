# JSP-000022: Černý conjecture, the Pin–Frankl bound (n³−n)/6 for all synchronizing automata and Kari's bound n²−3n+3 for Eulerian automata

Catalog entry: [JSP-000022](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0001-0100.md#JSP-000022)

## Problem

Černý conjecture (1964; formal-conjectures `cerny_conjecture`): every synchronizing deterministic finite automaton with `n` states has a synchronizing (reset) word of length at most `(n − 1)²`.

## Scope

Partial progress: the classical cubic upper bound `(n³ − n)/6` for all synchronizing automata (Pin 1983 via Frankl 1982), and the full conjecture for Eulerian automata (Kari 2003, bound `n² − 3n + 3`). The Černý conjecture for general automata remains open and is not addressed; the later cubic improvements (Szykuła 2018, Shitov 2019, FC `shitov_upper_bound`) are not formalized.

## Formal statements

All results are in `Cerny.lean`. `DFA.IsSynchronizingWord` and `DFA.IsSynchronizing` are copied verbatim from Google DeepMind's formal-conjectures `FormalConjecturesForMathlib/Computability/DFA.lean` (Apache-2.0); the automaton type is Mathlib's `DFA`. Eulerian is Kari's in-degree condition (in-degree |Σ| counted with multiplicity), without strong connectivity, so it also covers definitions that add strong connectivity. ℕ subtraction n³ − n never truncates; (n−2)(n−1)+1 = n² − 3n + 3 for n ≥ 1.

```lean
theorem frankl_skew_bollobas {V : Type*} [DecidableEq V] {m a b : ℕ}
    (A B : Fin m → Finset V) (hA : ∀ i, (A i).card = a) (hB : ∀ i, (B i).card = b)
    (hAB : ∀ i, Disjoint (A i) (B i))
    (hcross : ∀ i j, i < j → ¬ Disjoint (A i) (B j)) :
    m ≤ (a + b).choose a

theorem exists_shrink (M : DFA α σ) (hM : M.IsSynchronizing) (S : Finset σ)
    (hS : 2 ≤ S.card) :
    ∃ w : List α, (S.image fun q => M.evalFrom q w).card < S.card ∧
      w.length ≤ (Fintype.card σ - S.card + 2).choose 2

theorem pin_frankl_bound {α σ : Type*} [Fintype σ] (M : DFA α σ) (hM : M.IsSynchronizing) :
    ∃ w : List α, M.IsSynchronizingWord w ∧
      6 * w.length ≤ Fintype.card σ ^ 3 - Fintype.card σ

theorem pin_frankl_bound' {α σ : Type*} [Fintype σ] (M : DFA α σ) (hM : M.IsSynchronizing) :
    ∃ w : List α, M.IsSynchronizingWord w ∧
      w.length ≤ (Fintype.card σ ^ 3 - Fintype.card σ) / 6

theorem kari_eulerian_bound {α σ : Type*} [Fintype α] [Fintype σ] [DecidableEq σ]
    (M : DFA α σ)
    (hE : ∀ q : σ, Fintype.card {pa : σ × α // M.step pa.1 pa.2 = q} = Fintype.card α)
    (hM : M.IsSynchronizing) :
    ∃ w : List α, M.IsSynchronizingWord w ∧
      w.length ≤ (Fintype.card σ - 2) * (Fintype.card σ - 1) + 1 ∧
      w.length ≤ (Fintype.card σ - 1) ^ 2

theorem cerny_conjecture_eulerian {α σ : Type*} [Fintype α] [Fintype σ] [DecidableEq σ]
    (M : DFA α σ)
    (hE : ∀ q : σ, Fintype.card {pa : σ × α // M.step pa.1 pa.2 = q} = Fintype.card α)
    (hM : M.IsSynchronizing) :
    ∃ w : List α, M.IsSynchronizingWord w ∧ w.length ≤ (Fintype.card σ - 1) ^ 2
```

With Mathlib's `DFA α σ` and `DFA.IsSynchronizingWord`/`DFA.IsSynchronizing` copied verbatim from formal-conjectures: `frankl_skew_bollobas` (a-sets Aᵢ, b-sets Bᵢ, Aᵢ ∩ Bᵢ = ∅, Aᵢ ∩ Bⱼ ≠ ∅ for i < j ⇒ m ≤ C(a+b, a)), `exists_shrink` (Pin's lemma: a k-set of states, k ≥ 2, shrinks under a word of length ≤ C(n−k+2, 2)), `pin_frankl_bound` (every synchronizing DFA with n states has a synchronizing word w with 6|w| ≤ n³ − n; arbitrary alphabet, same binders as FC's `cerny_conjecture`), `pin_frankl_bound'` (|w| ≤ (n³ − n)/6), `kari_eulerian_bound` (finite alphabet, every state has exactly |Σ| incoming transitions: |w| ≤ (n−2)(n−1)+1 and ≤ (n−1)²), `cerny_conjecture_eulerian` (the Černý bound for Eulerian automata in the shape of FC's conclusion). Sanity examples: a synchronizing Eulerian 2-state automaton and a non-synchronizing one.

## Proof outline

Frankl: polynomial method — with gⱼ = ∏_{y∈Bⱼ}(X − c_y), the coefficient-product vectors indexed by Sym^a{0,…,b} are linearly independent by a triangular argument, giving m ≤ C(a+b, a). Pin: for a shortest shrinking word of a k-set S, the merged pairs {xᵢ, yᵢ} ⊆ Sᵢ and complements Q ∖ Sᵢ satisfy Frankl's hypotheses (a = 2, b = n − k) after reversing the order; summing C(n−k+2, 2) over k gives C(n+1, 3) = (n³ − n)/6. Kari: the in-degree condition gives ∑_b |P.(bw)⁻¹| = |Σ|·|P.w⁻¹|; a chain of subspaces in the coordinate-sum-zero hyperplane of ℚ^Q shows each proper nonempty P changes size under some word of length ≤ n − 1; iterate from a 2-merged preimage set.

## Build and verification

- Lean `v4.34.0` (`leanprover/lean4:v4.34.0`)
- Mathlib tag `v4.34.0`, commit `5ed2965256430c3649e86755f9576b54eca72435`; all dependencies are pinned in `lake-manifest.json`

```sh
lake exe cache get
lake build
```

`#print axioms` (see `verification/axioms.txt`):

```
'CernyConjecture.frankl_skew_bollobas' depends on axioms: [propext, Classical.choice, Quot.sound]
'CernyConjecture.exists_shrink' depends on axioms: [propext, Classical.choice, Quot.sound]
'CernyConjecture.pin_frankl_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'CernyConjecture.pin_frankl_bound'' depends on axioms: [propext, Classical.choice, Quot.sound]
'CernyConjecture.kari_eulerian_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'CernyConjecture.cerny_conjecture_eulerian' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The file contains no `sorry`, no `axiom` declarations and no `native_decide`. The build log and the SHA-256 of
`Cerny.lean` (`2dee94e90b217e8723369521a2ed58e2b89ed9a209d7632835baf1e5470239ad`) are in `verification/`.

## Attribution

- Mathematics: J.-E. Pin, On two combinatorial problems arising from automata theory, Ann. Discrete Math. 17 (1983) 535–548; P. Frankl, An extremal problem for two families of sets, European J. Combin. 3 (1982) 125–127; J. Kari, Synchronizing finite automata on Eulerian digraphs, Theoret. Comput. Sci. 295 (2003) 223–232, Theorem 2; J. Černý (1964). Lean formalization written with AI assistance (Anthropic Claude); Frankl's original paper was not consulted (standard statement used).
- Lean formalization: GitHub user `baobingzhang`, developed with AI assistance (Anthropic Claude).


No priority for the mathematics is claimed; the contribution is the Lean formalization.
