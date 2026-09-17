import Mathlib

/-!
# Erdős Problem 600: the Ruzsa–Szemerédi bound `e(n, r) = o(n²)`

Let `e(n, r)` be minimal such that every graph on `n` vertices with at least `e(n, r)` edges, each
edge contained in at least one triangle, must have an edge contained in at least `r` triangles.
Erdős Problem 600 asks (for `r ≥ 2`) whether `e(n, r + 1) - e(n, r) → ∞` and whether
`e(n, r + 1) / e(n, r) → 1`; both questions are open. This file proves the known result of
Ruzsa and Szemerédi (1978) that `e(n, r) = o(n²)` for every fixed `r`.

`Erdos600Prop` and `eFunction` are copied verbatim from Google DeepMind's formal-conjectures
project (`FormalConjectures/ErdosProblems/600.lean`, Apache-2.0), as is
`SimpleGraph.trianglesContaining`
(`FormalConjecturesForMathlib/Combinatorics/SimpleGraph/Clique.lean`, Apache-2.0), which is
inlined here. The main theorem `Erdos600.erdos_600.variants.ruzsa_szemeredi_upper_bound` has
exactly the name and statement used there.

## Proof

Fix `r` and `ε > 0`, put `ε' = ε / (6 (r + 1))`, and let `G` be a graph on `n` vertices with at
least `⌈ε n²⌉` edges, each in a triangle, and suppose every edge lies in fewer than `r` triangles.
Every triangle contains an edge, so `G` has at most `r · #E ≤ r n²` triangles, which is less than
`triangleRemovalBound ε' · n³` once `n` is large. Mathlib's triangle removal lemma gives a
triangle-free `G' ≤ G` with `#D < ε' n²`, where `D = E(G) \ E(G')`. Every triangle of `G` contains
an edge of `D`. Each edge `e` of `G` lies in a triangle `t`, which contains some `d ∈ D`, so
`e ∈ t.sym2` for some triangle `t` through some `d ∈ D`. Hence
`#E ≤ ∑_{d ∈ D} #(triangles through d) · 6 ≤ 6 r #D < 6 (r + 1) ε' n² = ε n²`, a contradiction.
So `e(n, r) ≤ ⌈ε n²⌉ ≤ 2 ε n²` for large `n`.

## Main results

* `Erdos600.erdos600Prop_ceil`: for `n > r / triangleRemovalBound (ε / (6 (r + 1)))`,
  `Erdos600Prop n ⌈ε n²⌉₊ r`.
* `Erdos600.erdos_600.variants.ruzsa_szemeredi_upper_bound`: `e(n, r) = o(n²)`.

## References

* [RuSz78] Ruzsa, I. Z. and Szemerédi, E., _Triple systems with no six points carrying three
  triangles_. Combinatorics (Proc. Fifth Hungarian Colloq., Keszthely, 1976), Vol. II (1978),
  939-945.
* [erdosproblems.com/600](https://www.erdosproblems.com/600)
-/

open Filter
open scoped Topology

namespace SimpleGraph

open scoped Classical in
/-- The triangles of `G` containing the edge `uv`, that is, the `3`-cliques of `G` whose vertex
set contains both endpoints of `uv`. -/
noncomputable def trianglesContaining {α : Type*} [Fintype α] (G : SimpleGraph α)
    (uv : Sym2 α) : Finset (Finset α) :=
  (G.cliqueFinset 3).filter (fun t ↦ uv.toFinset ⊆ t)

end SimpleGraph

namespace Erdos600

open Finset SimpleGraph

open scoped Classical in
/--
Let $e(n,r)$ be minimal such that every graph on $n$ vertices with at least $e(n,r)$ edges,
each edge contained in at least one triangle, must have an edge contained in at least
$r$ triangles.
-/
def Erdos600Prop (n : ℕ) (e : ℕ) (r : ℕ) : Prop :=
  ∀ G : SimpleGraph (Fin n), G.edgeFinset.card ≥ e →
  (∀ uv ∈ G.edgeFinset, (G.trianglesContaining uv).Nonempty) →
  ∃ uv ∈ G.edgeFinset, r ≤ (G.trianglesContaining uv).card

noncomputable def eFunction (n : ℕ) (r : ℕ) : ℕ := sInf {e : ℕ | Erdos600Prop n e r}

/-- Membership in `trianglesContaining`, stated without decidability instances. -/
theorem mem_trianglesContaining {α : Type*} [Fintype α] {G : SimpleGraph α} {uv : Sym2 α}
    {t : Finset α} : t ∈ G.trianglesContaining uv ↔ G.IsNClique 3 t ∧ ∀ a ∈ uv, a ∈ t := by
  classical
  unfold trianglesContaining
  simp only [mem_filter, mem_cliqueFinset_iff, Finset.subset_iff, Sym2.mem_toFinset]

/-- The key step: for `n` large compared with the triangle removal constant, every graph on `n`
vertices with at least `ε n²` edges, each in a triangle, has an edge in at least `r` triangles. -/
theorem erdos600Prop_ceil (r n : ℕ) {ε : ℝ} (hε : 0 < ε)
    (hn : (r : ℝ) < triangleRemovalBound (ε / (6 * (r + 1))) * n) :
    Erdos600Prop n ⌈ε * (n : ℝ) ^ 2⌉₊ r := by
  classical
  intro G hcard htri
  by_contra hcon
  push Not at hcon
  set ε' : ℝ := ε / (6 * (r + 1)) with hε'
  have hn0 : 0 < n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h
      simp only [CharP.cast_eq_zero, mul_zero] at hn
      exact absurd hn (not_lt.2 r.cast_nonneg)
    · exact h
  -- Every triangle contains an edge, so there are at most `r · #E` triangles.
  have hT : #(G.cliqueFinset 3) ≤ r * #G.edgeFinset := by
    have hsub : G.cliqueFinset 3 ⊆ G.edgeFinset.biUnion G.trianglesContaining := by
      intro t ht
      have ht' := ht
      rw [mem_cliqueFinset_iff, is3Clique_iff] at ht'
      obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := ht'
      rw [mem_biUnion]
      refine ⟨s(a, b), by simpa using hab, ?_⟩
      rw [mem_trianglesContaining, mem_cliqueFinset_iff.symm]
      refine ⟨ht, ?_⟩
      intro x hx
      rw [Sym2.mem_iff] at hx
      rcases hx with rfl | rfl <;> simp
    calc #(G.cliqueFinset 3) ≤ #(G.edgeFinset.biUnion G.trianglesContaining) := card_le_card hsub
      _ ≤ ∑ e ∈ G.edgeFinset, #(G.trianglesContaining e) := card_biUnion_le
      _ ≤ ∑ _e ∈ G.edgeFinset, r := sum_le_sum fun e he => (hcon e he).le
      _ = r * #G.edgeFinset := by rw [sum_const, smul_eq_mul, mul_comm]
  have hE : #G.edgeFinset ≤ n ^ 2 := by
    calc #G.edgeFinset ≤ (Fintype.card (Fin n)).choose 2 := card_edgeFinset_le_card_choose_two
      _ ≤ (Fintype.card (Fin n)) ^ 2 := Nat.choose_le_pow _ _
      _ = n ^ 2 := by rw [Fintype.card_fin]
  have hTlt : (#(G.cliqueFinset 3) : ℝ) < triangleRemovalBound ε' * Fintype.card (Fin n) ^ 3 := by
    rw [Fintype.card_fin]
    have h1 : (#(G.cliqueFinset 3) : ℝ) ≤ r * n ^ 2 := by
      have := hT.trans (Nat.mul_le_mul_left r hE)
      exact_mod_cast this
    have hn2 : (0 : ℝ) < (n : ℝ) ^ 2 := by positivity
    calc (#(G.cliqueFinset 3) : ℝ) ≤ r * n ^ 2 := h1
      _ < triangleRemovalBound ε' * n * n ^ 2 := mul_lt_mul_of_pos_right hn hn2
      _ = triangleRemovalBound ε' * n ^ 3 := by ring
  obtain ⟨G', hG'le, _, hdel, hfree⟩ := triangle_removal hTlt
  set D := G.edgeFinset \ G'.edgeFinset with hD
  -- Every edge of `G` lies in a triangle through a deleted edge.
  have hsub : G.edgeFinset ⊆ D.biUnion (fun d => (G.trianglesContaining d).biUnion
      (fun t => t.sym2)) := by
    intro e he
    obtain ⟨t, ht⟩ := htri e he
    rw [mem_trianglesContaining] at ht
    obtain ⟨htc, het⟩ := ht
    have hd : ∃ d ∈ D, ∀ a ∈ d, a ∈ t := by
      by_contra hnone
      have ht3 := htc
      rw [is3Clique_iff] at ht3
      obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := ht3
      have key : ∀ x y : Fin n, G.Adj x y → x ∈ ({a, b, c} : Finset (Fin n)) →
          y ∈ ({a, b, c} : Finset (Fin n)) → G'.Adj x y := by
        intro x y hxy hx hy
        by_contra hG'
        refine hnone ⟨s(x, y), ?_, ?_⟩
        · exact mem_sdiff.2 ⟨by simpa using hxy, by simpa using hG'⟩
        · intro z hz
          rw [Sym2.mem_iff] at hz
          rcases hz with rfl | rfl <;> assumption
      refine hfree {a, b, c} ?_
      rw [is3Clique_iff]
      exact ⟨a, b, c, key _ _ hab (by simp) (by simp), key _ _ hac (by simp) (by simp),
        key _ _ hbc (by simp) (by simp), rfl⟩
    obtain ⟨d, hdD, hdt⟩ := hd
    rw [mem_biUnion]
    refine ⟨d, hdD, ?_⟩
    rw [mem_biUnion]
    refine ⟨t, ?_, ?_⟩
    · exact mem_trianglesContaining.2 ⟨htc, hdt⟩
    · rw [mem_sym2_iff]
      exact het
  have hDsub : D ⊆ G.edgeFinset := sdiff_subset
  have hcardE : #G.edgeFinset ≤ #D * (r * 6) := by
    calc #G.edgeFinset ≤ #(D.biUnion (fun d => (G.trianglesContaining d).biUnion
          (fun t => t.sym2))) := card_le_card hsub
      _ ≤ ∑ d ∈ D, #((G.trianglesContaining d).biUnion (fun t => t.sym2)) := card_biUnion_le
      _ ≤ ∑ _d ∈ D, r * 6 := by
        refine sum_le_sum fun d hdD => ?_
        calc #((G.trianglesContaining d).biUnion (fun t => t.sym2))
            ≤ ∑ t ∈ G.trianglesContaining d, #t.sym2 := card_biUnion_le
          _ = ∑ _t ∈ G.trianglesContaining d, 6 := by
            refine sum_congr rfl fun t ht => ?_
            rw [mem_trianglesContaining] at ht
            rw [card_sym2, ht.1.card_eq]
            rfl
          _ = #(G.trianglesContaining d) * 6 := by rw [sum_const, smul_eq_mul]
          _ ≤ r * 6 := Nat.mul_le_mul_right 6 (hcon d (hDsub hdD)).le
      _ = #D * (r * 6) := by rw [sum_const, smul_eq_mul]
  have hDcard : (#D : ℝ) < ε' * n ^ 2 := by
    rw [hD, cast_card_sdiff (edgeFinset_mono hG'le)]
    simpa [Fintype.card_fin] using hdel
  have hcardE' : ((#G.edgeFinset : ℕ) : ℝ) ≤ #D * (r * 6) := by exact_mod_cast hcardE
  have hge : ε * (n : ℝ) ^ 2 ≤ #G.edgeFinset :=
    (Nat.le_ceil _).trans (by exact_mod_cast hcard)
  have hr : (0 : ℝ) ≤ r := r.cast_nonneg
  have hD0 : (0 : ℝ) ≤ #D := (#D).cast_nonneg
  have h6 : (0 : ℝ) < 6 * (r + 1) := by positivity
  have hεeq : ε = ε' * (6 * (r + 1)) := by rw [hε']; field_simp
  have : (#D : ℝ) * (r * 6) < ε' * n ^ 2 * (6 * (r + 1)) := by
    calc (#D : ℝ) * (r * 6) ≤ #D * (6 * (r + 1)) := by nlinarith
      _ < ε' * n ^ 2 * (6 * (r + 1)) := mul_lt_mul_of_pos_right hDcard h6
  nlinarith

/--
Ruzsa and Szemerédi [RuSz78] proved that $e(n,r)=o(n^2)$ for any fixed $r$.
-/
theorem erdos_600.variants.ruzsa_szemeredi_upper_bound :
    ∀ r : ℕ, (fun (n : ℕ) ↦ (eFunction n r : ℝ)) =o[atTop] (fun (n : ℕ) ↦ (n : ℝ)^2) := by
  intro r
  rw [Asymptotics.isLittleO_iff]
  intro c hc
  set ε : ℝ := c / 2 with hεdef
  have hε : 0 < ε := by positivity
  set δ : ℝ := triangleRemovalBound (ε / (6 * (r + 1))) with hδdef
  have hδ : 0 < δ := triangleRemovalBound_pos (by positivity)
  obtain ⟨N, hN⟩ := exists_nat_gt (r / δ + 1 / ε + 1)
  filter_upwards [eventually_ge_atTop N] with n hn
  have hnN : (N : ℝ) ≤ n := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ n := by
    have : (0 : ℝ) ≤ r / δ := by positivity
    have : (0 : ℝ) ≤ 1 / ε := by positivity
    linarith
  have hbig : (r : ℝ) < δ * n := by
    have h1 : (r : ℝ) / δ < n := by
      have : (0 : ℝ) ≤ 1 / ε := by positivity
      linarith
    rwa [div_lt_iff₀ hδ, mul_comm] at h1
  have hsmall : 1 ≤ ε * (n : ℝ) ^ 2 := by
    have h1 : 1 / ε < n := by
      have : (0 : ℝ) ≤ r / δ := by positivity
      linarith
    have h2 : 1 < ε * n := by rwa [div_lt_iff₀ hε, mul_comm] at h1
    nlinarith
  have hle : eFunction n r ≤ ⌈ε * (n : ℝ) ^ 2⌉₊ := Nat.sInf_le (erdos600Prop_ceil r n hε hbig)
  have hceil : (⌈ε * (n : ℝ) ^ 2⌉₊ : ℝ) < ε * n ^ 2 + 1 := Nat.ceil_lt_add_one (by positivity)
  rw [Real.norm_natCast, norm_pow, Real.norm_natCast]
  calc (eFunction n r : ℝ) ≤ ⌈ε * (n : ℝ) ^ 2⌉₊ := by exact_mod_cast hle
    _ ≤ ε * n ^ 2 + 1 := hceil.le
    _ ≤ c * n ^ 2 := by
      have : c * (n : ℝ) ^ 2 = 2 * (ε * n ^ 2) := by rw [hεdef]; ring
      linarith

end Erdos600
