import Mathlib

/-!
# Erdős Problem 332: positive (upper Banach) density forces `D(A)` to have bounded gaps

For `A ⊆ ℕ` let `D(A)` be the set of integers that occur infinitely often as `a₁ - a₂` with
`a₁, a₂ ∈ A`. Erdős and Graham [ErGr80, p. 50] asked, as an open-ended question, which conditions
on `A` ensure that `D(A)` has bounded gaps. erdosproblems.com/332 records that Prikry, Tijdeman and
Stewart showed that positive density is sufficient ([St78], [Ti79]). In a forum comment on
erdosproblems.com/forum/thread/332 (user "aditya", 4 May 2026, introduced as "an observation by
GPT 5.5 pro") the condition was weakened to positive upper Banach density. This file proves:

* `erdos_332.variants.upperBanachDensity_pos`:
  `0 < upperBanachDensity A → HasBoundedGaps (D_A A)`;
* `erdos_332.variants.upperDensity_pos`: `0 < A.upperDensity → HasBoundedGaps (D_A A)`;
* `erdos_332.variants.hasPosDensity`: `A.HasPosDensity → HasBoundedGaps (D_A A)` (the condition
  as recorded, with natural density).

Each is the statement `erdos_332` of Google DeepMind's formal-conjectures project
(`FormalConjectures/ErdosProblems/332.lean`, category "research open", with the condition left
as a placeholder `answer(…)`) with that condition filled in. The definitions `D_A` and
`HasBoundedGaps` are copied verbatim from that file, and `Set.partialDensity`,
`Set.upperDensity`, `Set.HasDensity` and `Set.HasPosDensity` verbatim from
`FormalConjecturesForMathlib/Data/Set/Density.lean` (both Apache-2.0). `upperBanachDensity` is
in neither formal-conjectures nor Mathlib and is defined here in the standard way,
`limsup_{L → ∞} max_M |A ∩ [M, M + L)| / L` (the limit exists, so this is the usual value).
`upperDensity_le_upperBanachDensity` shows that the Banach version is the strongest of the three.

Non-vacuity: `HasBoundedGaps S` asks for an element of `S` in every window `[z, z + M)`, so it
fails for `S = ∅` and forces `S` to be unbounded in both directions. The hypotheses are
satisfiable: `upperDensity_univ` shows `ℕ` has upper density `1`.

## Proof

* `D(A) = -D(A)` (swap the pair), `0 ∈ D(A)` if `A` is infinite, and `D(A) = ∅` if `A` is finite.
* Call a finite `F ⊆ ℤ` separated if `s - t ∉ D(A)` for distinct `s, t ∈ F`. Then only finitely
  many `a ∈ A` satisfy `a + s = b + t` with `b ∈ A` and `s ≠ t` in `F`; say all are `≤ K`. So the
  translates `(A ∩ [max(M, K + 1), M + L)) + s`, `s ∈ F`, are pairwise disjoint subsets of
  `[M - T, M + L + T)` with `T = max |s|`, giving
  `|F| · |A ∩ [M, M + L)| ≤ L + 2T + |F| (K + 1)` for all `M, L` (`exists_count_bound`).
* Dividing by `L` and letting `L → ∞` gives `|F| · d*(A) ≤ 1`
  (`card_mul_upperBanachDensity_le_one`).
* If `d*(A) > 0`, separated sets have at most `1 / d*(A)` elements; hence `A` is infinite (else
  every finite set is separated). Take a separated `F` of maximal size and `R = max |f|`. For
  `z ∈ ℤ` put `w = z + R`: either `w ∈ F` and `w - w = 0 ∈ D(A)`, or `F ∪ {w}` is not separated;
  in both cases `w - f ∈ D(A)` for some `f ∈ F`, and `z ≤ w - f < z + 2R + 1`
  (`hasBoundedGaps_of_card_le`).
* Upper density is at most upper Banach density (take `M = 0`), and a set of natural density
  `α > 0` has upper density `α`.

## What remains open

The problem asks for sufficient conditions in general and has no single definitive answer. This
file proves the classical sufficient condition and its Banach-density strengthening only; it says
nothing about sets of zero upper Banach density, nor about the related questions of when `D(A)`
has positive density, when `∑_{d ∈ D(A)} 1/d = ∞`, or when `D(A) ≠ ∅`.
-/

open Filter

open scoped Topology

namespace Set

/--
Given a set `S` and an element `b` in an order `β`, where all intervals bounded above are finite,
we define the partial density of `S` (relative to a set `A`) to be the proportion of elements in
`{x ∈ A | x < b}` that lie in `S ∩ A`.

This definition was inspired from https://github.com/b-mehta/unit-fractions
-/
@[inline]
noncomputable abbrev partialDensity {β : Type*} [Preorder β] [LocallyFiniteOrderBot β]
    (S : Set β) (A : Set β := Set.univ) (b : β) : ℝ :=
  ((S ∩ A) ∩ Iio b).ncard / (A ∩ Iio b).ncard

/--
Given a set `S` in an order `β`, where all intervals bounded above are finite, we define the upper
density of `S` (relative to a set `A`) to be the limsup of the partial densities of `S`
(relative to `A`) for `b → ∞`.
-/
noncomputable def upperDensity {β : Type*} [Preorder β] [LocallyFiniteOrderBot β]
    (S : Set β) (A : Set β := Set.univ) : ℝ :=
  atTop.limsup fun (b : β) ↦ S.partialDensity A b

/--
A set `S` in an order `β` where all intervals bounded above are finite is said to have
density `α : ℝ` (relative to a set `A`) if the proportion of `x ∈ S` such that `x < n`
in `A` tends to `α` as `n → ∞`.

When `β = ℕ` this by default defines the natural density of a set
(i.e., relative to all of `ℕ`).
-/
def HasDensity {β : Type*} [Preorder β] [LocallyFiniteOrderBot β]
    (S : Set β) (α : ℝ) (A : Set β := Set.univ) : Prop :=
  Tendsto (fun (b : β) => S.partialDensity A b) atTop (𝓝 α)

/--
A set `S` in an order `β` where all intervals bounded above are finite is said to have
positive density (relative to a set `A`) if there exists a positive `α : ℝ` such that
`S` has density `α` (relative to a set `A`).
-/
def HasPosDensity {β : Type*} [Preorder β] [LocallyFiniteOrderBot β]
    (S : Set β) (A : Set β := Set.univ) : Prop :=
  ∃ α > 0, S.HasDensity α A

end Set

namespace Erdos332

open Set

/--
The set of numbers $D(A)$ which occur infinitely often as $a_1 - a_2$ with $a_1, a_2 \in A$.
-/
noncomputable def D_A (A : Set ℕ) : Set ℤ :=
  { d : ℤ | Set.Infinite { (a, b) : ℕ × ℕ | a ∈ A ∧ b ∈ A ∧ (a : ℤ) - (b : ℤ) = d } }

/--
A set $S \subseteq \mathbb{Z}$ has bounded gaps if it is syndetic, meaning there is a uniform
bound $M$ such that every interval of length $M$ contains an element of $S$.
-/
def HasBoundedGaps (S : Set ℤ) : Prop :=
  ∃ M : ℕ, M > 0 ∧ ∀ z : ℤ, ∃ s ∈ S, z ≤ s ∧ s < z + (M : ℤ)

/-- Sanity check that the density hypotheses are satisfiable: `ℕ` has upper density `1`. -/
theorem upperDensity_univ : (Set.univ : Set ℕ).upperDensity = 1 := by
  unfold Set.upperDensity
  have h : ∀ᶠ N : ℕ in atTop, (Set.univ : Set ℕ).partialDensity Set.univ N = (fun _ => (1 : ℝ)) N :=
    (eventually_ge_atTop 1).mono fun N hN => by
      simp only [Set.partialDensity, Set.inter_univ, Set.univ_inter, ncard_Iio_nat]
      exact div_self (by exact_mod_cast (by omega : N ≠ 0))
  rw [limsup_congr h, limsup_const]

/-- The upper Banach density of `A ⊆ ℕ`: the limsup, as `L → ∞`, of
`max_M |A ∩ [M, M + L)| / L`. -/
noncomputable def upperBanachDensity (A : Set ℕ) : ℝ :=
  atTop.limsup fun L : ℕ ↦ (⨆ M : ℕ, ((A ∩ Ico M (M + L)).ncard : ℝ)) / L

theorem mem_D_A {A : Set ℕ} {d : ℤ} :
    d ∈ D_A A ↔ {p : ℕ × ℕ | p.1 ∈ A ∧ p.2 ∈ A ∧ (p.1 : ℤ) - p.2 = d}.Infinite :=
  Iff.rfl

theorem neg_mem_D_A {A : Set ℕ} {d : ℤ} (h : d ∈ D_A A) : -d ∈ D_A A := by
  rw [mem_D_A] at *
  refine (h.image Prod.swap_injective.injOn).mono ?_
  rintro _ ⟨⟨a, b⟩, ⟨ha, hb, hd⟩, rfl⟩
  exact ⟨hb, ha, by simp only [Prod.swap_prod_mk]; omega⟩

theorem zero_mem_D_A {A : Set ℕ} (hA : A.Infinite) : (0 : ℤ) ∈ D_A A := by
  rw [mem_D_A]
  refine (hA.image (f := fun a => (a, a)) fun x _ y _ h => (Prod.ext_iff.1 h).1).mono ?_
  rintro _ ⟨a, ha, rfl⟩
  exact ⟨ha, ha, sub_self _⟩

theorem D_A_eq_empty_of_finite {A : Set ℕ} (hA : A.Finite) : D_A A = ∅ := by
  ext d
  simp only [mem_D_A, Set.mem_empty_iff_false, iff_false, Set.not_infinite]
  exact (hA.prod hA).subset fun p hp => ⟨hp.1, hp.2.1⟩

/-- A finite set `F ⊆ ℤ` is separated (for `A`) if no difference of two distinct elements of `F`
lies in `D(A)`, i.e. the translates `A + s`, `s ∈ F`, pairwise meet in finite sets. -/
def Separated (A : Set ℕ) (F : Finset ℤ) : Prop :=
  ∀ s ∈ F, ∀ t ∈ F, s ≠ t → s - t ∉ D_A A

/-- Counting: the translates `A ∩ [M, M + L) + s` (`s ∈ F`) are disjoint up to a bounded
exceptional set, so `|F| · |A ∩ [M, M + L)| ≤ L + C` uniformly in `M` and `L`. -/
theorem exists_count_bound {A : Set ℕ} {F : Finset ℤ} (hF : Separated A F) :
    ∃ C : ℕ, ∀ M L : ℕ, F.card * (A ∩ Ico M (M + L)).ncard ≤ L + C := by
  classical
  set E : Set ℕ := ⋃ p ∈ F.offDiag,
    Prod.fst '' {q : ℕ × ℕ | q.1 ∈ A ∧ q.2 ∈ A ∧ (q.1 : ℤ) - q.2 = p.2 - p.1} with hE
  have hEfin : E.Finite := by
    refine F.offDiag.finite_toSet.biUnion fun p hp => Set.Finite.image _ ?_
    rw [Finset.mem_coe, Finset.mem_offDiag] at hp
    have := hF p.2 hp.2.1 p.1 hp.1 (Ne.symm hp.2.2)
    rwa [mem_D_A, Set.not_infinite] at this
  obtain ⟨K, hK⟩ := hEfin.bddAbove
  set T : ℕ := F.sup Int.natAbs with hT
  refine ⟨2 * T + F.card * (K + 1), fun M L => ?_⟩
  set S := (Finset.Ico M (M + L)).filter (· ∈ A) with hSdef
  set S' := S.filter (K < ·) with hS'def
  have hS : (A ∩ Ico M (M + L)).ncard = S.card := by
    rw [← Set.ncard_coe_finset]
    congr 1
    ext x
    simp [S, and_comm]
  have hSS' : S.card ≤ S'.card + (K + 1) := by
    calc S.card ≤ (S' ∪ Finset.range (K + 1)).card := by
          refine Finset.card_le_card fun x hx => ?_
          simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_range, S']
          by_cases h : K < x
          · exact Or.inl ⟨hx, h⟩
          · exact Or.inr (by omega)
      _ ≤ S'.card + (Finset.range (K + 1)).card := Finset.card_union_le _ _
      _ = S'.card + (K + 1) := by rw [Finset.card_range]
  have hinj : Set.InjOn (fun q : ℤ × ℕ => (q.2 : ℤ) + q.1) (F ×ˢ S' : Finset (ℤ × ℕ)) := by
    rintro ⟨s, a⟩ hsa ⟨t, b⟩ htb h
    simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, S', S, Finset.mem_filter,
      Finset.mem_Ico] at hsa htb
    simp only at h
    by_cases hst : s = t
    · subst hst
      simp only [Prod.mk.injEq, true_and]
      omega
    · exfalso
      have haE : a ∈ E := by
        simp only [E, Set.mem_iUnion]
        refine ⟨(s, t), Finset.mem_offDiag.2 ⟨hsa.1, htb.1, hst⟩, ⟨a, b⟩,
          ⟨hsa.2.1.2, htb.2.1.2, ?_⟩, rfl⟩
        simp only
        omega
      have := hK haE
      omega
  have himg : (F ×ˢ S').image (fun q : ℤ × ℕ => (q.2 : ℤ) + q.1) ⊆
      Finset.Ico ((M : ℤ) - T) (M + L + T) := by
    intro x hx
    simp only [Finset.mem_image, Finset.mem_product, Prod.exists] at hx
    obtain ⟨s, a, ⟨hs, ha⟩, rfl⟩ := hx
    have hsT : s.natAbs ≤ T := Finset.le_sup (f := Int.natAbs) hs
    simp only [S', S, Finset.mem_filter, Finset.mem_Ico] at ha
    simp only [Finset.mem_Ico]
    omega
  have hcard := Finset.card_le_card himg
  rw [Finset.card_image_of_injOn hinj, Finset.card_product, Int.card_Ico] at hcard
  have h2 : ((M : ℤ) + L + T - (M - T)).toNat = L + 2 * T := by omega
  rw [h2] at hcard
  rw [hS]
  calc F.card * S.card ≤ F.card * (S'.card + (K + 1)) := Nat.mul_le_mul_left _ hSS'
    _ = F.card * S'.card + F.card * (K + 1) := by ring
    _ ≤ L + (2 * T + F.card * (K + 1)) := by omega


/-- If `n > 0` and `n · u(L) · L ≤ L + C` for all `L > 0`, then `n · limsup u ≤ 1`. -/
theorem mul_limsup_le_one {u : ℕ → ℝ} {n C : ℕ} (hn : 0 < n) (hu0 : ∀ L, 0 ≤ u L)
    (hu : ∀ L : ℕ, 0 < L → (n : ℝ) * (u L * L) ≤ L + C) : (n : ℝ) * atTop.limsup u ≤ 1 := by
  have hn' : (0 : ℝ) < n := Nat.cast_pos.2 hn
  refine le_of_forall_pos_le_add fun ε hε => ?_
  have hev : ∀ᶠ L : ℕ in atTop, u L ≤ (1 + ε) / n := by
    obtain ⟨L₀, hL₀⟩ := exists_nat_gt ((C : ℝ) / ε)
    filter_upwards [eventually_ge_atTop (L₀ + 1)] with L hL
    have hLpos : (0 : ℝ) < L := by exact_mod_cast (by omega : 0 < L)
    have hCL : (C : ℝ) ≤ ε * L := by
      have : (C : ℝ) / ε < L := hL₀.trans_le (by exact_mod_cast (by omega : L₀ ≤ L))
      rw [div_lt_iff₀ hε] at this
      linarith
    rw [le_div_iff₀ hn']
    have h1 := hu L (by omega)
    have h2 : (u L * n) * L ≤ (1 + ε) * L := by nlinarith
    exact le_of_mul_le_mul_right h2 hLpos
  have hlim : atTop.limsup u ≤ (1 + ε) / n :=
    limsup_le_of_le (isCoboundedUnder_le_of_le atTop hu0) hev
  calc (n : ℝ) * atTop.limsup u ≤ n * ((1 + ε) / n) := mul_le_mul_of_nonneg_left hlim hn'.le
    _ = 1 + ε := by field_simp

/-- A separated set `F` satisfies `|F| · d*(A) ≤ 1`. -/
theorem card_mul_upperBanachDensity_le_one {A : Set ℕ} {F : Finset ℤ} (hF : Separated A F) :
    (F.card : ℝ) * upperBanachDensity A ≤ 1 := by
  rcases Nat.eq_zero_or_pos F.card with h | hn
  · simp [h]
  obtain ⟨C, hC⟩ := exists_count_bound hF
  refine mul_limsup_le_one (C := C) hn
    (fun L => div_nonneg (Real.iSup_nonneg fun _ => Nat.cast_nonneg _) (Nat.cast_nonneg _))
    fun L hL => ?_
  have hL' : (L : ℝ) ≠ 0 := by exact_mod_cast hL.ne'
  rw [div_mul_cancel₀ _ hL', Real.mul_iSup_of_nonneg (Nat.cast_nonneg _)]
  exact ciSup_le fun M => by exact_mod_cast hC M L

/-- Upper density is at most upper Banach density. -/
theorem upperDensity_le_upperBanachDensity (A : Set ℕ) :
    A.upperDensity ≤ upperBanachDensity A := by
  have hbdd : ∀ L M : ℕ, ((A ∩ Ico M (M + L)).ncard : ℝ) ≤ L := fun L M => by
    have := Set.ncard_le_ncard (Set.inter_subset_right (s := A) (t := Ico M (M + L)))
      (Set.finite_Ico _ _)
    rw [ncard_Ico_nat] at this
    exact_mod_cast this.trans (by omega)
  unfold Set.upperDensity upperBanachDensity
  refine limsup_le_limsup (Eventually.of_forall fun N => ?_)
    (isCoboundedUnder_le_of_le atTop fun N => by positivity)
    (isBoundedUnder_of ⟨1, fun L => div_le_one_of_le₀ (ciSup_le (hbdd L)) (Nat.cast_nonneg _)⟩)
  simp only [Set.partialDensity, Set.inter_univ, Set.univ_inter, ncard_Iio_nat]
  refine div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg _)
  have : A ∩ Iio N = A ∩ Ico 0 (0 + N) := by ext; simp
  rw [this]
  exact le_ciSup (f := fun M : ℕ => ((A ∩ Ico M (M + N)).ncard : ℝ))
    ⟨N, forall_mem_range.2 (hbdd N)⟩ 0

/-- If separated sets have bounded size, then `D(A)` has bounded gaps: a maximal separated set
`F` satisfies `ℤ = F + D(A)`. -/
theorem hasBoundedGaps_of_card_le {A : Set ℕ} {B : ℕ}
    (hB : ∀ F : Finset ℤ, Separated A F → F.card ≤ B) : HasBoundedGaps (D_A A) := by
  classical
  have hAinf : A.Infinite := by
    intro hfin
    have hsep : Separated A (Finset.Icc (0 : ℤ) B) := by
      intro s _ t _ _
      rw [D_A_eq_empty_of_finite hfin]
      exact Set.notMem_empty _
    have := hB _ hsep
    rw [Int.card_Icc] at this
    omega
  have h0 := zero_mem_D_A hAinf
  let P : ℕ → Prop := fun k => ∃ F : Finset ℤ, Separated A F ∧ F.card = k
  have hP0 : P 0 := ⟨∅, by simp [Separated], rfl⟩
  obtain ⟨F, hF, hFcard⟩ : P (Nat.findGreatest P B) := Nat.findGreatest_spec (Nat.zero_le _) hP0
  have hmax : ∀ G : Finset ℤ, Separated A G → G.card ≤ F.card := fun G hG =>
    hFcard ▸ Nat.le_findGreatest (hB G hG) ⟨G, hG, rfl⟩
  set R : ℕ := F.sup Int.natAbs with hR
  refine ⟨2 * R + 1, by omega, fun z => ?_⟩
  have key : ∃ f ∈ F, z + R - f ∈ D_A A := by
    by_cases hw : z + R ∈ F
    · exact ⟨z + R, hw, by simpa using h0⟩
    · have hnot : ¬ Separated A (insert (z + R) F) := fun h => by
        have := hmax _ h
        rw [Finset.card_insert_of_notMem hw] at this
        omega
      simp only [Separated, not_forall, not_not, Finset.mem_insert] at hnot
      obtain ⟨s, hs, t, ht, hst, hd⟩ := hnot
      rcases hs with rfl | hs <;> rcases ht with rfl | ht
      · exact absurd rfl hst
      · exact ⟨t, ht, hd⟩
      · exact ⟨s, hs, by simpa using neg_mem_D_A hd⟩
      · exact absurd hd (hF s hs t ht hst)
  obtain ⟨f, hf, hd⟩ := key
  have hfR : f.natAbs ≤ R := Finset.le_sup (f := Int.natAbs) hf
  exact ⟨z + R - f, hd, by omega, by omega⟩

theorem erdos_332.variants.upperBanachDensity_pos (A : Set ℕ) :
    0 < upperBanachDensity A → HasBoundedGaps (D_A A) := fun hA =>
  hasBoundedGaps_of_card_le fun _ hF =>
    Nat.le_floor <| (le_div_iff₀ hA).2 (card_mul_upperBanachDensity_le_one hF)

theorem erdos_332.variants.upperDensity_pos (A : Set ℕ) :
    0 < A.upperDensity → HasBoundedGaps (D_A A) := fun hA =>
  erdos_332.variants.upperBanachDensity_pos A (hA.trans_le (upperDensity_le_upperBanachDensity A))

theorem erdos_332.variants.hasPosDensity (A : Set ℕ) :
    A.HasPosDensity → HasBoundedGaps (D_A A) := fun ⟨α, hα, hA⟩ =>
  erdos_332.variants.upperDensity_pos A (by rwa [Set.upperDensity, hA.limsup_eq])

end Erdos332
