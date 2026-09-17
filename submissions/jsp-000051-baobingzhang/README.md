# JSP-000051: Erdős 12, the Erdős–Sárközy construction of good sets with |A∩[1,N]| > N/f(N) infinitely often

Catalog entry: [JSP-000051](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0001-0100.md#JSP-000051) · Problem source: [erdosproblems.com/12](https://www.erdosproblems.com/12)

## Problem

Call an infinite `A ⊆ ℕ` good if there are no distinct `b, c ∈ A` and `a ∈ A` with `a ∣ b + c` and `b, c > a`. Is there a good `A` with `liminf |A∩[1,N]|/N^{1/2} > 0`? Is there `c > 0` such that every good `A` has `|A∩[1,N]| < N^{1−c}` for infinitely many `N`? Must `∑_{n∈A} 1/n` converge for every good `A`?

## Scope

Partial progress: the Erdős–Sárközy theorem that good sets can be almost of positive density along a subsequence, i.e. the formal-conjectures variant `erdos_12.variants.erdos_sarkozy`. Parts (i) and (ii) of Erdős Problem 12 (which already have formal proofs by others, not ours), part (iii) (convergence of the reciprocal sum, open), and the Erdős–Sárközy density-0 theorem are not formalized or claimed.

## Formal statements

All results are in `Erdos12.lean`. `IsGood` and the statement of `erdos_12.variants.erdos_sarkozy` are copied verbatim from Google DeepMind's formal-conjectures project (`FormalConjectures/ErdosProblems/12.lean`, Apache-2.0).

```lean
theorem erdos_12.variants.erdos_sarkozy (f : ℕ → ℕ) (hf : atTop.Tendsto f atTop) :
    ∃ A, IsGood A ∧ {N : ℕ | (N : ℝ) / f N < (A ∩ Icc 1 N).ncard}.Infinite
```

`erdos_12.variants.erdos_sarkozy : ∀ f : ℕ → ℕ, Tendsto f atTop atTop → ∃ A, IsGood A ∧ {N : ℕ | (N : ℝ) / f N < (A ∩ Icc 1 N).ncard}.Infinite` is proved with its exact formal-conjectures name, statement and definition of `IsGood`. The constructed set satisfies the stronger property that no triple `a < b, c` with `a ∣ b + c` exists at all.

## Proof outline

Choose `g` with `f N ≥ m` for `N ≥ g m`. With scales `u 0 = 1`, `u (i+1) = 3·(u i)!·K`, where `K = g(3·(u i)! + 1) + 1`, block `i` is the `K` numbers `M t + 1` (`M = (u i)!`, `2K ≤ t < 3K`), and `A` is the union of the blocks. If `a < x` are in `A`, then either `x` is in the same block and `2x < 3a`, or `x` is in a later block and `x ≡ 1 (mod a)` because `a ≤ u(i+1)` divides the later factorial. For `a ∣ b + c` with `b, c > a` this gives `2a < b + c < 3a`, or `a ∣ 2`, or `a ∣ c + 1` with `a < c + 1 < 2a`, all impossible since `a ≥ 3`. At `N = u(i+1) = 3MK`, block `i` gives `K` elements of `[1, N]` while `f N ≥ 3M + 1`, so `N / f N < K`.

## Build and verification

- Lean `v4.34.0` (`leanprover/lean4:v4.34.0`)
- Mathlib tag `v4.34.0`, commit `5ed2965256430c3649e86755f9576b54eca72435`; all dependencies are pinned in `lake-manifest.json`

```sh
lake exe cache get
lake build
```

`#print axioms` (see `verification/axioms.txt`):

```
'Erdos12.erdos_12.variants.erdos_sarkozy' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The file contains no `sorry`, no `axiom` declarations and no `native_decide`. The build log and the SHA-256 of
`Erdos12.lean` (`76a907aa2c72b75219fd94ab69ca027523288d60094349fc334b2f963c8fddef`) are in `verification/`.

## Attribution

- Mathematics: P. Erdős and A. Sárközy, *On the divisibility properties of sequences of integers*, Proc. London Math. Soc. (3) 21 (1970), 97–101 [ErSa70], cited by the catalog record JSP-000051 and erdosproblems.com/12. The construction idea (progressions ≡ 1 modulo a factorial of the previous scale, confined to short intervals) follows Erdős–Sárközy; the specific parameters were chosen for the formal proof.
- Lean formalization: GitHub user `baobingzhang`, developed with AI assistance (Anthropic Claude).


No priority for the mathematics is claimed; the contribution is the Lean formalization.
