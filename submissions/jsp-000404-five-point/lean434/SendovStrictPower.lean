import SendovDirectionModel
import JSP404.BinaryEncoding

/-! Strict power-of-two counting for the direction model.
A padded circular binning leaves one unused bit at an extreme vertex.
The general Sendov half-step refinement is not established here. -/
namespace SendovStrictPower
open SendovDirectionModel

/-- Reversing edges that cross the angular cut makes each bin a source/sink graph. -/
def Arrow {N n : ℕ} {t : ℝ} (m : Model N t) (a : ℝ) (c : Fin n) (i j : Fin N) : Prop :=
  (i < j ∧ a ≤ m.theta i j ∧ (c : ℝ) ≤ m.theta i j-a ∧ m.theta i j-a < (c : ℝ)+1) ∨
  (j < i ∧ m.theta j i < a ∧ (c : ℝ) ≤ m.theta j i-a+n ∧ m.theta j i-a+n < (c : ℝ)+1)

lemma no_two_step {N n : ℕ} {t a : ℝ} (m : Model N t) (ht : t < n)
    (c : Fin n) (i j k : Fin N) (hij : Arrow m a c i j) (hjk : Arrow m a c j k) : False := by
  rcases hij with ⟨hij,ha,hb,hc⟩ | ⟨hji,ha,hb,hc⟩ <;>
    rcases hjk with ⟨hjk,hd,he,hf⟩ | ⟨hkj,hd,he,hf⟩
  · rcases m.triangle i j k hij hjk with h | h <;> rcases h with ⟨h1,h2,h3,h4,h5⟩ <;> linarith
  · rcases lt_trichotomy i k with hik | hik | hki
    · rcases m.triangle i k j hik hkj with h | h <;> rcases h with ⟨h1,h2,h3,h4,h5⟩ <;> linarith
    · subst k; linarith
    · rcases m.triangle k i j hki hij with h | h <;> rcases h with ⟨h1,h2,h3,h4,h5⟩ <;> linarith
  · rcases lt_trichotomy i k with hik | hik | hki
    · rcases m.triangle j i k hji hik with h | h <;> rcases h with ⟨h1,h2,h3,h4,h5⟩ <;> linarith
    · subst k; linarith
    · rcases m.triangle j k i hjk hki with h | h <;> rcases h with ⟨h1,h2,h3,h4,h5⟩ <;> linarith
  · rcases m.triangle k j i hkj hji with h | h <;> rcases h with ⟨h1,h2,h3,h4,h5⟩ <;> linarith

lemma arrow_cover {N n : ℕ} {t a : ℝ} (m : Model N t) (ht : t < n)
    (ha : 0 ≤ a) (hat : a < t) (i j : Fin N) (hne : i ≠ j) :
    ∃ c : Fin n, Arrow m a c i j ∨ Arrow m a c j i := by
  have ordered (i j : Fin N) (hij : i < j) :
      ∃ c : Fin n, Arrow m a c i j ∨ Arrow m a c j i := by
    obtain ⟨hx,hxt⟩ := m.range i j hij
    by_cases hcut : m.theta i j < a
    · let s := m.theta i j-a+n
      have hs : 0 ≤ s := by dsimp [s]; linarith
      have hsn : s < n := by dsimp [s]; linarith
      let c : Fin n := ⟨⌊s⌋₊, (Nat.floor_lt hs).mpr hsn⟩
      refine ⟨c, Or.inr (Or.inr ⟨hij,hcut,?_,?_⟩)⟩
      · exact Nat.floor_le hs
      · exact Nat.lt_floor_add_one s
    · let s := m.theta i j-a
      have hs : 0 ≤ s := by dsimp [s]; linarith
      have hsn : s < n := by dsimp [s]; linarith
      let c : Fin n := ⟨⌊s⌋₊, (Nat.floor_lt hs).mpr hsn⟩
      refine ⟨c, Or.inl (Or.inl ⟨hij,le_of_not_gt hcut,?_,?_⟩)⟩
      · exact Nat.floor_le hs
      · exact Nat.lt_floor_add_one s
  rcases lt_or_gt_of_ne hne with hij | hji
  · exact ordered i j hij
  · obtain ⟨c,h⟩ := ordered j i hji
    exact ⟨c,h.symm⟩

#print axioms no_two_step
#print axioms arrow_cover

/-- An isolated coordinate at one vertex leaves an additional unused Boolean word. -/
lemma card_add_one_le {V : Type*} [Fintype V] {n : ℕ}
    (A : Fin n → V → V → Prop)
    (no_path : ∀ c i j k, A c i j → A c j k → False)
    (cover : ∀ i j, i ≠ j → ∃ c, A c i j ∨ A c j i)
    (v : V) (d : Fin n) (isolated : ∀ j, ¬ A d v j ∧ ¬ A d j v) :
    Fintype.card V + 1 ≤ 2^n := by
  classical
  let bit (i : V) (c : Fin n) : Bool := decide (∃ j, A c i j)
  have hb {c : Fin n} {i j : V} (h : A c i j) :
      bit i c = true ∧ bit j c = false := by
    have hi : ∃ k, A c i k := ⟨j,h⟩
    have hj : ¬ ∃ k, A c j k := by rintro ⟨k,hk⟩; exact no_path c i j k h hk
    simp [bit,hi,hj]
  have sep (i j : V) (hne : i ≠ j) :
      ∃ c, bit i c ≠ bit j c ∧ (A c i j ∨ A c j i) := by
    obtain ⟨c,h⟩ := cover i j hne
    refine ⟨c,?_,h⟩
    rcases h with h | h
    · rw [(hb h).1,(hb h).2]; decide
    · rw [(hb h).2,(hb h).1]; decide
  have hinj : Function.Injective bit := by
    intro i j h
    by_contra hne
    obtain ⟨c,hc,_⟩ := sep i j hne
    exact hc (congrFun h c)
  let extra : Fin n → Bool := fun c => if c=d then true else bit v c
  have hextra (j : V) : extra ≠ bit j := by
    intro heq
    by_cases hj : v=j
    · subst j
      have hv : ¬ ∃ k, A d v k := by rintro ⟨k,hk⟩; exact (isolated k).1 hk
      have h := congrFun heq d
      simpa [extra,bit,hv] using h
    · obtain ⟨c,hc,hA⟩ := sep v j hj
      have hcd : c ≠ d := by
        intro he; subst c
        rcases hA with hA | hA
        · exact (isolated j).1 hA
        · exact (isolated j).2 hA
      exact hc (by simpa [extra,hcd] using congrFun heq c)
  let encode : Option V → (Fin n → Bool)
    | none => extra
    | some i => bit i
  have hei : Function.Injective encode := by
    intro x y h
    cases x with
    | none =>
      cases y with
      | none => rfl
      | some j => exact (hextra j h).elim
    | some i =>
      cases y with
      | none => exact (hextra i h.symm).elim
      | some j => exact congrArg some (hinj h)
  simpa using Fintype.card_le_of_injective encode hei

lemma exists_isolated_cut {N n : ℕ} {t : ℝ} (m : Model N t)
    (hN : 2 ≤ N) (hn : 2 ≤ n) (ht : t < n) :
    ∃ a : ℝ, 0 ≤ a ∧ a < t ∧ ∃ v : Fin N, ∃ d : Fin n,
      ∀ j, ¬ Arrow m a d v j ∧ ¬ Arrow m a d j v := by
  classical
  let v : Fin N := ⟨0,by omega⟩
  let s : Finset (Fin N) := Finset.univ.filter (v < ·)
  have hs : s.Nonempty := by
    refine ⟨⟨1,by omega⟩,?_⟩
    simp [s,v]
  obtain ⟨u,hu,hmin⟩ := s.exists_min_image (fun j => m.theta v j) hs
  have hvu : v < u := (Finset.mem_filter.mp hu).2
  let a := m.theta v u
  obtain ⟨ha,hat⟩ := m.range v u hvu
  have hlow (j : Fin N) (hvj : v < j) : a ≤ m.theta v j :=
    hmin j (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hvj⟩)
  have hnreal : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hupper (j : Fin N) (hvj : v < j) : m.theta v j-a < (n : ℝ)-1 := by
    by_cases hju : j=u
    · subst j; dsimp [a]; linarith
    · rcases lt_or_gt_of_ne hju with hju | huj
      · rcases m.triangle v j u hvj hju with h | h <;>
          rcases h with ⟨h1,h2,h3,h4,h5⟩ <;> dsimp [a] <;> linarith
      · rcases m.triangle v u j hvu huj with h | h <;>
          rcases h with ⟨h1,h2,h3,h4,h5⟩ <;> dsimp [a] <;> linarith
  let d : Fin n := ⟨n-1,by omega⟩
  have hd : (d : ℝ) = (n : ℝ)-1 := by
    dsimp [d]
    rw [Nat.cast_sub (by omega)]
    norm_num
  refine ⟨a,ha,hat,v,d,?_⟩
  intro j
  constructor
  · rintro (⟨hvj,h1,h2,h3⟩ | ⟨hjv,h1,h2,h3⟩)
    · have hh := hupper j hvj; rw [hd] at h2; linarith
    · have : ¬ j < v := by change ¬ j.val < 0; omega
      exact this hjv
  · rintro (⟨hjv,h1,h2,h3⟩ | ⟨hvj,h1,h2,h3⟩)
    · have : ¬ j < v := by change ¬ j.val < 0; omega
      exact this hjv
    · exact (not_lt_of_ge (hlow j hvj)) h1

/-- For every size and integer n>=2, strict angular room excludes 2^n labels. -/
theorem model_card_lt {N n : ℕ} {t : ℝ} (m : Model N t)
    (hN : 2 ≤ N) (hn : 2 ≤ n) (ht : t < n) : N < 2^n := by
  obtain ⟨a,ha,hat,v,d,hisolated⟩ := exists_isolated_cut m hN hn ht
  have hh := card_add_one_le (Arrow m a) (no_two_step m ht)
    (arrow_cover m ht ha hat) v d hisolated
  simp only [Fintype.card_fin] at hh
  omega

#print axioms card_add_one_le
#print axioms exists_isolated_cut
#print axioms model_card_lt
end SendovStrictPower
