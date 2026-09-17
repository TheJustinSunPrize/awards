import Mathlib

/-!
# Erdős Problem 12: the Erdős–Sárközy construction of dense "good" sets

Call `A ⊆ ℕ` *good* if it is infinite and there are no `a, b, c ∈ A` with `b ≠ c`,
`a ∣ b + c` and `b, c > a`. Erdős Problem 12 asks (i) whether some good `A` has
`liminf |A ∩ [1, N]| / √N > 0`, (ii) whether there is `c > 0` such that every good `A` has
`|A ∩ [1, N]| < N^(1-c)` for infinitely many `N`, and (iii) whether `∑_{n ∈ A} 1/n < ∞` for every
good `A`. Erdős and Sárközy [ErSa70] proved that every good set has density `0`, and that this is
essentially best possible: for every `f(N) → ∞` there is a good `A` with
`|A ∩ [1, N]| > N / f(N)` for infinitely many `N`. This file proves the second statement.

`IsGood` and the statement of `erdos_12.variants.erdos_sarkozy` (category "research solved") are
copied verbatim from Google DeepMind's formal-conjectures project
(`FormalConjectures/ErdosProblems/12.lean`, Apache-2.0). The main theorem
`Erdos12.erdos_12.variants.erdos_sarkozy` has exactly the name and statement used there. Note that
`IsGood` asks for `b = c` whenever `a ∣ b + c`, `a < b`, `a < c`; the set constructed below
satisfies the stronger property that no such triple exists at all (not even with `b = c`).

## Construction

Let `g` be such that `f N ≥ m` whenever `N ≥ g m` (it exists as `f → ∞`). For `v : ℕ` put
`M = v!` and `K(v) = g (3 M + 1) + 1 ≥ 1`. Define `u 0 = 1` and `u (i + 1) = 3 · (u i)! · K(u i)`,
and let block `i` consist of the `K = K(u i)` numbers `M t + 1` with `M = (u i)!` and
`2K ≤ t < 3K`. The good set is the union of all blocks. Every element `n` of block `i` satisfies
`u i < 2MK + 1 ≤ n ≤ 3MK = u (i + 1)`, and `u` is strictly increasing.

## Proof

* **Shape of larger elements** (`two_mul_lt_or_eq_mul_add_one`). Let `a` be in block `i` and
  `x > a` in block `j`. Then `j ≥ i`, since block `j < i` lies below `u (j + 1) ≤ u i < a`.
  If `j = i`, then `2x ≤ 2M(3K - 1) + 2 ≤ 6MK < 3(2MK + 1) ≤ 3a`. If `j > i`, then
  `a ≤ u (i + 1) ≤ u j`, so `a ∣ (u j)!` and `x ≡ 1 (mod a)`.
* **No bad triple** (`false_of_dvd_add`). Let `3 ≤ a < b, c` with `a ∣ b + c`, where each of
  `b, c` satisfies `2x < 3a` or `x ≡ 1 (mod a)`. If both are `< 3a/2` then `2a < b + c < 3a`.
  If both are `≡ 1` then `a ∣ 2`. If `b ≡ 1` and `2c < 3a` then `a ∣ c + 1` with
  `a < c + 1 < 2a`. Each case is impossible. Every element is at least `2MK + 1 ≥ 3`.
* **Density** (`card_block_le_ncard`). At `N = u (i + 1) = 3MK`, block `i` contributes `K`
  elements of `[1, N]`, and `N ≥ K > g (3M + 1)` gives `f N ≥ 3M + 1`, so
  `N / f N ≤ 3MK / (3M + 1) < K ≤ |A ∩ [1, N]|`. As `u` is strictly increasing, this happens for
  infinitely many `N`.

The construction (blocks of an arithmetic progression `≡ 1` modulo a factorial of the previous
scale, each confined to an interval `(y, 3y/2]`) follows the idea of Erdős and Sárközy; the
specific parameters are chosen here for a short formal proof.

## What remains open

This is only a variant of Erdős Problem 12. Part (iii) (`∑_{n ∈ A} 1/n < ∞`) is open. Parts (i)
and (ii) and the density-`0` theorem of Erdős–Sárközy are not proved in this file.

## References

* [ErSa70] Erdős, P. and Sárközy, A., _On the divisibility properties of sequences of integers_.
  Proc. London Math. Soc. (3) (1970), 97-101.
* [erdosproblems.com/12](https://www.erdosproblems.com/12)
-/

open Filter Set
open scoped Nat

namespace Erdos12

/--
A set `A` is "good" if it is infinite and there are no distinct `a,b,c` in `A`
such that `a ∣ (b+c)` and `b > a`, `c > a`.
-/
abbrev IsGood (A : Set ℕ) : Prop := A.Infinite ∧
  ∀ᵉ (a ∈ A) (b ∈ A) (c ∈ A), a ∣ b + c → a < b →
  a < c → b = c

namespace ErdosSarkozy

/-- The number of elements `K(v) = g (3 · v! + 1) + 1` of the block built at scale `v`. -/
def blockLen (g : ℕ → ℕ) (v : ℕ) : ℕ := g (3 * v ! + 1) + 1

/-- The scales: `scale g 0 = 1` and `scale g (i + 1) = 3 · (scale g i)! · K(scale g i)`. -/
def scale (g : ℕ → ℕ) : ℕ → ℕ
  | 0 => 1
  | i + 1 => 3 * (scale g i) ! * blockLen g (scale g i)

/-- Block `i`: the numbers `M t + 1` with `M = (scale g i)!` and `2K ≤ t < 3K`,
`K = K(scale g i)`. -/
def block (g : ℕ → ℕ) (i : ℕ) : Set ℕ :=
  {n | ∃ t, 2 * blockLen g (scale g i) ≤ t ∧ t < 3 * blockLen g (scale g i) ∧
    n = (scale g i) ! * t + 1}

/-- The good set: the union of all blocks. -/
def goodSet (g : ℕ → ℕ) : Set ℕ := ⋃ i, block g i

theorem one_le_blockLen (g : ℕ → ℕ) (v : ℕ) : 1 ≤ blockLen g v := Nat.le_add_left 1 _

theorem scale_lt_succ (g : ℕ → ℕ) (i : ℕ) : scale g i < scale g (i + 1) := by
  have h1 := Nat.self_le_factorial (scale g i)
  have h2 : 0 < scale g i := by
    cases i with
    | zero => simp [scale]
    | succ i =>
      have := Nat.factorial_pos (scale g i)
      have := one_le_blockLen g (scale g i)
      simp only [scale]
      positivity
  have h3 : (scale g i) ! * 1 ≤ (scale g i) ! * blockLen g (scale g i) :=
    Nat.mul_le_mul_left _ (one_le_blockLen g _)
  show scale g i < 3 * (scale g i) ! * blockLen g (scale g i)
  rw [Nat.mul_assoc]
  omega

theorem scale_strictMono (g : ℕ → ℕ) : StrictMono (scale g) :=
  strictMono_nat_of_lt_succ (scale_lt_succ g)

/-- Every element of block `i` is at least `2 M K + 1`. -/
theorem lower_of_mem_block {g : ℕ → ℕ} {i n : ℕ} (hn : n ∈ block g i) :
    2 * ((scale g i) ! * blockLen g (scale g i)) + 1 ≤ n := by
  obtain ⟨t, ht1, -, rfl⟩ := hn
  have := Nat.mul_le_mul_left ((scale g i) !) ht1
  rw [Nat.mul_left_comm] at this
  omega

/-- Every element of block `i` is at most `M (3K - 1) + 1`, i.e. `n + M ≤ 3 M K + 1`. -/
theorem upper_of_mem_block {g : ℕ → ℕ} {i n : ℕ} (hn : n ∈ block g i) :
    n + (scale g i) ! ≤ 3 * ((scale g i) ! * blockLen g (scale g i)) + 1 := by
  obtain ⟨t, -, ht2, rfl⟩ := hn
  have := Nat.mul_le_mul_left ((scale g i) !) (Nat.succ_le_of_lt ht2)
  rw [Nat.mul_succ, Nat.mul_left_comm] at this
  omega

theorem three_le_of_mem_block {g : ℕ → ℕ} {i n : ℕ} (hn : n ∈ block g i) : 3 ≤ n := by
  have h1 := lower_of_mem_block hn
  have h2 : 1 * 1 ≤ (scale g i) ! * blockLen g (scale g i) :=
    Nat.mul_le_mul (Nat.factorial_pos _) (one_le_blockLen g _)
  omega

theorem scale_lt_of_mem_block {g : ℕ → ℕ} {i n : ℕ} (hn : n ∈ block g i) : scale g i < n := by
  have h1 := lower_of_mem_block hn
  have h2 := Nat.self_le_factorial (scale g i)
  have h3 : (scale g i) ! * 1 ≤ (scale g i) ! * blockLen g (scale g i) :=
    Nat.mul_le_mul_left _ (one_le_blockLen g _)
  omega

theorem le_scale_succ_of_mem_block {g : ℕ → ℕ} {i n : ℕ} (hn : n ∈ block g i) :
    n ≤ scale g (i + 1) := by
  have h1 := upper_of_mem_block hn
  have h2 := Nat.factorial_pos (scale g i)
  show n ≤ 3 * (scale g i) ! * blockLen g (scale g i)
  rw [Nat.mul_assoc]
  omega

/-- Two elements of the same block are within a factor `3/2` of each other. -/
theorem two_mul_lt_of_mem_block {g : ℕ → ℕ} {i a n : ℕ} (ha : a ∈ block g i)
    (hn : n ∈ block g i) : 2 * n < 3 * a := by
  have h1 := lower_of_mem_block ha
  have h2 := upper_of_mem_block hn
  have h3 := Nat.factorial_pos (scale g i)
  omega

/-- An element of a later block is `≡ 1` modulo every element of an earlier block. -/
theorem exists_eq_mul_add_one {g : ℕ → ℕ} {i j a n : ℕ} (ha : a ∈ block g i)
    (hn : n ∈ block g j) (hij : i < j) : ∃ q, n = a * q + 1 := by
  have h1 : a ≤ scale g j :=
    (le_scale_succ_of_mem_block ha).trans ((scale_strictMono g).monotone hij)
  have h2 : 0 < a := by have := three_le_of_mem_block ha; omega
  obtain ⟨r, hr⟩ := Nat.dvd_factorial h2 h1
  obtain ⟨t, -, -, rfl⟩ := hn
  exact ⟨r * t, by rw [hr, Nat.mul_assoc]⟩

/-- If `a < x` are in the good set, then `x < 3a/2` or `x ≡ 1 (mod a)`. -/
theorem two_mul_lt_or_eq_mul_add_one {g : ℕ → ℕ} {i j a x : ℕ} (ha : a ∈ block g i)
    (hx : x ∈ block g j) (hax : a < x) : 2 * x < 3 * a ∨ ∃ q, x = a * q + 1 := by
  rcases lt_trichotomy i j with h | rfl | h
  · exact Or.inr (exists_eq_mul_add_one ha hx h)
  · exact Or.inl (two_mul_lt_of_mem_block ha hx)
  · exfalso
    have h1 := le_scale_succ_of_mem_block hx
    have h2 := (scale_strictMono g).monotone (show j + 1 ≤ i by omega)
    have h3 := scale_lt_of_mem_block ha
    omega

/-- The arithmetic core: no `3 ≤ a < b, c` with `a ∣ b + c` when each of `b, c` is either
`< 3a/2` or `≡ 1 (mod a)`. -/
theorem false_of_dvd_add {a b c : ℕ} (ha : 3 ≤ a) (hab : a < b) (hac : a < c) (hdvd : a ∣ b + c)
    (hb : 2 * b < 3 * a ∨ ∃ q, b = a * q + 1) (hc : 2 * c < 3 * a ∨ ∃ q, c = a * q + 1) :
    False := by
  obtain ⟨m, hm⟩ := hdvd
  rcases hb with hb | ⟨q, rfl⟩ <;> rcases hc with hc | ⟨r, rfl⟩
  · -- `2a < b + c = a m < 3a`
    have h1 : a * 2 < a * m := by omega
    have h2 : a * m < a * 3 := by omega
    have := Nat.lt_of_mul_lt_mul_left h1
    have := Nat.lt_of_mul_lt_mul_left h2
    omega
  · -- `b + 1 = a (m - r)` with `a < b + 1 < 2a`
    have h1 : a * (r + 1) < a * m := by rw [Nat.mul_succ]; omega
    have h2 : a * m < a * (r + 2) := by rw [Nat.mul_add]; omega
    have := Nat.lt_of_mul_lt_mul_left h1
    have := Nat.lt_of_mul_lt_mul_left h2
    omega
  · -- `c + 1 = a (m - q)` with `a < c + 1 < 2a`
    have h1 : a * (q + 1) < a * m := by rw [Nat.mul_succ]; omega
    have h2 : a * m < a * (q + 2) := by rw [Nat.mul_add]; omega
    have := Nat.lt_of_mul_lt_mul_left h1
    have := Nat.lt_of_mul_lt_mul_left h2
    omega
  · -- `a (q + r) + 2 = a m`, so `a ∣ 2`
    have h1 : a * (q + r) < a * m := by rw [Nat.mul_add]; omega
    have h2 := Nat.lt_of_mul_lt_mul_left h1
    have h3 : a * (q + r + 1) ≤ a * m := Nat.mul_le_mul_left _ h2
    rw [Nat.mul_succ, Nat.mul_add] at h3
    rw [Nat.mul_add] at h1
    omega

theorem isGood_goodSet (g : ℕ → ℕ) : IsGood (goodSet g) := by
  refine ⟨?_, ?_⟩
  · refine Set.infinite_of_not_bddAbove ?_
    rintro ⟨B, hB⟩
    have hmem : (scale g B) ! * (2 * blockLen g (scale g B)) + 1 ∈ block g B :=
      ⟨_, le_rfl, by have := one_le_blockLen g (scale g B); omega, rfl⟩
    have h1 := hB (Set.mem_iUnion.mpr ⟨B, hmem⟩)
    have h2 := scale_lt_of_mem_block hmem
    have h3 := (scale_strictMono g).id_le B
    simp only [id] at h3
    omega
  · intro a ha b hb c hc hdvd hab hac
    exfalso
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp ha
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hb
    obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hc
    exact false_of_dvd_add (three_le_of_mem_block hi) hab hac hdvd
      (two_mul_lt_or_eq_mul_add_one hi hj hab) (two_mul_lt_or_eq_mul_add_one hi hk hac)

/-- Block `i` alone puts `K` elements of the good set into `[1, scale g (i + 1)]`. -/
theorem card_block_le_ncard (g : ℕ → ℕ) (i : ℕ) :
    blockLen g (scale g i) ≤ (goodSet g ∩ Icc 1 (scale g (i + 1))).ncard := by
  set K := blockLen g (scale g i) with hK
  set s := (Finset.Ico (2 * K) (3 * K)).image (fun t => (scale g i) ! * t + 1) with hs
  have hsub : (s : Set ℕ) ⊆ goodSet g ∩ Icc 1 (scale g (i + 1)) := by
    intro n hn
    rw [hs, Finset.coe_image, Finset.coe_Ico] at hn
    obtain ⟨t, ⟨ht1, ht2⟩, rfl⟩ := hn
    have hmem : (scale g i) ! * t + 1 ∈ block g i := ⟨t, ht1, ht2, rfl⟩
    exact ⟨Set.mem_iUnion.mpr ⟨i, hmem⟩, Nat.le_add_left 1 _, le_scale_succ_of_mem_block hmem⟩
  have hinj : Function.Injective (fun t => (scale g i) ! * t + 1) := by
    intro t₁ t₂ h
    exact Nat.eq_of_mul_eq_mul_left (Nat.factorial_pos _) (by simpa using h)
  calc K = s.card := by rw [hs, Finset.card_image_of_injective _ hinj, Nat.card_Ico]; omega
    _ = (s : Set ℕ).ncard := (Set.ncard_coe_finset s).symm
    _ ≤ _ := Set.ncard_le_ncard hsub ((Set.finite_Icc 1 _).subset Set.inter_subset_right)

end ErdosSarkozy

open ErdosSarkozy

/--
Given any function $f(x)\to \infty$ as $x\to \infty$ there exists a set $A$ with the property
that there are no distinct $a,b,c \in A$ such that $a \mid (b+c)$ and $b,c > a$, such that there are
infinitely many $N$ such that $$\lvert A\cap\{1,\ldots,N\}\rvert > \frac{N}{f(N)}.
-/
theorem erdos_12.variants.erdos_sarkozy (f : ℕ → ℕ) (hf : atTop.Tendsto f atTop) :
    ∃ A, IsGood A ∧ {N : ℕ | (N : ℝ) / f N < (A ∩ Icc 1 N).ncard}.Infinite := by
  choose g hg using Filter.tendsto_atTop_atTop.mp hf
  refine ⟨goodSet g, isGood_goodSet g, ?_⟩
  have hinj : Function.Injective (fun i => scale g (i + 1)) :=
    (scale_strictMono g).injective.comp (add_left_injective 1)
  refine (Set.infinite_range_of_injective hinj).mono ?_
  rintro _ ⟨i, rfl⟩
  show ((scale g (i + 1) : ℕ) : ℝ) / f (scale g (i + 1)) <
    (goodSet g ∩ Icc 1 (scale g (i + 1))).ncard
  have hMpos : 0 < (scale g i) ! := Nat.factorial_pos _
  have hK1 : 1 ≤ blockLen g (scale g i) := one_le_blockLen g _
  have hN : scale g (i + 1) = blockLen g (scale g i) * (3 * (scale g i) !) := by
    rw [Nat.mul_comm]; rfl
  have hKdef : blockLen g (scale g i) = g (3 * (scale g i) ! + 1) + 1 := rfl
  -- `N = 3 M K ≥ K > g (3 M + 1)`, hence `f N ≥ 3 M + 1`.
  have hKN : blockLen g (scale g i) * 1 ≤ scale g (i + 1) := by
    rw [hN]; exact Nat.mul_le_mul_left _ (by omega)
  have hf' : 3 * (scale g i) ! + 1 ≤ f (scale g (i + 1)) := hg _ _ (by omega)
  -- `N = 3 M K < K (3 M + 1) ≤ K f(N)`.
  have hlt : scale g (i + 1) < blockLen g (scale g i) * f (scale g (i + 1)) := by
    have h1 := Nat.mul_le_mul_left (blockLen g (scale g i)) hf'
    rw [Nat.mul_succ] at h1
    omega
  have hfpos : (0 : ℝ) < f (scale g (i + 1)) := by
    have : 0 < f (scale g (i + 1)) := by omega
    exact_mod_cast this
  rw [div_lt_iff₀ hfpos]
  calc ((scale g (i + 1) : ℕ) : ℝ)
      < (blockLen g (scale g i) : ℝ) * (f (scale g (i + 1)) : ℝ) := by exact_mod_cast hlt
    _ ≤ ((goodSet g ∩ Icc 1 (scale g (i + 1))).ncard : ℝ) * (f (scale g (i + 1)) : ℝ) := by
      gcongr
      exact_mod_cast card_block_le_ncard g i

end Erdos12
