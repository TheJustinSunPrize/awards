import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Finset.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace JSP000689
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Every vertex of the edge has the same Boolean colour. -/
def Mono (e : Finset V) (c : V → Bool) : Prop :=
  ∀ x ∈ e, ∀ y ∈ e, c x = c y

def Proper (H : Finset (Finset V)) (S : Finset V) (c : V → Bool) : Prop :=
  ∀ e ∈ H, e ⊆ S → ¬ Mono e c

noncomputable def restrict (S : Finset V) (c : V → Bool) : V → Bool :=
  fun x => if x ∈ S then c x else false

noncomputable def colors (H : Finset (Finset V)) (S : Finset V) : Finset (V → Bool) :=
  by
  classical
  exact univ.filter fun c => (∀ x ∉ S, c x = false) ∧ Proper H S c

@[simp] theorem mem_colors (H : Finset (Finset V)) (S : Finset V) (c : V → Bool) :
    c ∈ colors H S ↔ (∀ x ∉ S, c x = false) ∧ Proper H S c := by
  classical
  simp [colors]

theorem restrict_mem {H : Finset (Finset V)} {S T : Finset V} {c : V → Bool}
    (h : c ∈ colors H S) (hTS : T ⊆ S) : restrict T c ∈ colors H T := by
  classical
  obtain ⟨hs, hp⟩ := mem_colors H S c |>.mp h
  rw [mem_colors]
  refine ⟨by intro x hx; simp [restrict, hx], ?_⟩
  intro e he heT hm
  apply hp e he (heT.trans hTS)
  intro x hx y hy
  simpa [restrict, heT hx, heT hy] using hm x hx y hy

noncomputable def extensions (H : Finset (Finset V)) (S : Finset V) (v : V) :
    Finset (V → Bool) := by
  classical
  exact univ.filter fun c => (∀ x ∉ S, c x = false) ∧ Proper H (S.erase v) c

@[simp] theorem mem_extensions (H : Finset (Finset V)) (S : Finset V) (v : V)
    (c : V → Bool) : c ∈ extensions H S v ↔
      (∀ x ∉ S, c x = false) ∧ Proper H (S.erase v) c := by
  classical
  simp [extensions]

theorem card_extensions (H : Finset (Finset V)) (S : Finset V) (v : V) (hv : v ∈ S) :
    (extensions H S v).card = 2 * (colors H (S.erase v)).card := by
  classical
  have hcard : (extensions H S v).card =
      ((colors H (S.erase v)) ×ˢ (univ : Finset Bool)).card := by
    apply card_bij (fun c _ => (restrict (S.erase v) c, c v))
    · intro c hc
      obtain ⟨hs, hp⟩ := (mem_extensions H S v c).mp hc
      simp only [mem_product, mem_univ, and_true, mem_colors]
      refine ⟨by intro x hx; simp [restrict, hx], ?_⟩
      intro e he heS hm
      apply hp e he heS
      intro x hx y hy
      simpa [restrict, heS hx, heS hy] using hm x hx y hy
    · intro c hc d hd heq
      obtain ⟨hcS, _⟩ := (mem_extensions H S v c).mp hc
      obtain ⟨hdS, _⟩ := (mem_extensions H S v d).mp hd
      have h1 := congrArg Prod.fst heq
      have h2 := congrArg Prod.snd heq
      funext x
      by_cases hx : x = v
      · simpa [hx] using h2
      by_cases hxS : x ∈ S
      · have ht : x ∈ S.erase v := mem_erase.mpr ⟨hx, hxS⟩
        simpa [restrict, ht] using congrFun h1 x
      · rw [hcS x hxS, hdS x hxS]
    · rintro ⟨c, b⟩ hb
      have hc := (mem_product.mp hb).1
      obtain ⟨hcS, hp⟩ := (mem_colors H (S.erase v) c).mp hc
      refine ⟨Function.update c v b, ?_, ?_⟩
      · rw [mem_extensions]
        refine ⟨?_, ?_⟩
        · intro x hx
          have hxv : x ≠ v := by aesop
          simp [Function.update_of_ne hxv, hcS x (by simp [hx])]
        · intro e he heS hm
          apply hp e he heS
          intro x hx y hy
          have hxv := (mem_erase.mp (heS hx)).1
          have hyv := (mem_erase.mp (heS hy)).1
          simpa [Function.update_of_ne hxv, Function.update_of_ne hyv] using hm x hx y hy
      · apply Prod.ext
        · funext x
          by_cases hx : x ∈ S.erase v
          · simp [restrict, hx, Function.update_of_ne (mem_erase.mp hx).1]
          · simp [restrict, hx, hcS x hx]
        · simp
  simpa [card_product, Nat.mul_comm] using hcard

noncomputable def bad (H : Finset (Finset V)) (S : Finset V) (v : V) (e : Finset V) :
    Finset (V → Bool) := by
  classical
  exact (extensions H S v).filter (Mono e)

/-- A monochromatic edge is recoverable from one retained vertex. -/
theorem card_bad_le (H : Finset (Finset V)) (S : Finset V) (v a : V) (e : Finset V)
    (heS : e ⊆ S) (hv : v ∈ e) (ha : a ∈ e) (hav : a ≠ v) :
    (bad H S v e).card ≤ (colors H (S \ e.erase a)).card := by
  classical
  let U := S \ e.erase a
  have hvU : v ∉ U := by simp [U, hv, Ne.symm hav]
  have hUT : U ⊆ S.erase v := by
    intro x hx
    exact mem_erase.mpr ⟨by intro h; subst x; exact hvU hx, (mem_sdiff.mp hx).1⟩
  apply card_le_card_of_injOn (restrict U)
  · intro c hc
    obtain ⟨hcE, hm⟩ := mem_filter.mp hc
    obtain ⟨hcS, hp⟩ := (mem_extensions H S v c).mp hcE
    change restrict U c ∈ colors H U
    rw [mem_colors]
    refine ⟨by intro x hx; simp [restrict, hx], ?_⟩
    intro f hf hfU hmono
    apply hp f hf (hfU.trans hUT)
    intro x hx y hy
    simpa [restrict, hfU hx, hfU hy] using hmono x hx y hy
  · intro c hc d hd heq
    obtain ⟨hcE, hcm⟩ := mem_filter.mp hc
    obtain ⟨hdE, hdm⟩ := mem_filter.mp hd
    have hcS := ((mem_extensions H S v c).mp hcE).1
    have hdS := ((mem_extensions H S v d).mp hdE).1
    have haU : a ∈ U := by simp [U, heS ha]
    have heqa : c a = d a := by simpa [restrict, haU] using congrFun heq a
    funext x
    by_cases hxS : x ∈ S
    · by_cases hxU : x ∈ U
      · simpa [restrict, hxU] using congrFun heq x
      · have hxe : x ∈ e := by
          have : x ∈ e.erase a := by simpa [U, hxS] using hxU
          exact mem_of_mem_erase this
        exact (hcm x hxe a ha).trans (heqa.trans (hdm a ha x hxe))
    · rw [hcS x hxS, hdS x hxS]

/-- Every extension is either proper or monochromatic on an incident edge. -/
theorem extension_cover (H : Finset (Finset V)) (S : Finset V) (v : V) :
    extensions H S v ⊆ colors H S ∪
      (H.filter fun e => e ⊆ S ∧ v ∈ e).biUnion (bad H S v) := by
  classical
  intro c hc
  obtain ⟨hcS, hp⟩ := (mem_extensions H S v c).mp hc
  by_cases h : Proper H S c
  · exact mem_union_left _ ((mem_colors H S c).mpr ⟨hcS,h⟩)
  · simp only [Proper, not_forall, not_not] at h
    obtain ⟨e, he, heS, hm⟩ := h
    have hv : v ∈ e := by
      by_contra hv
      apply hp e he (subset_erase.mpr ⟨heS, hv⟩) hm
    exact mem_union_right _ (mem_biUnion.mpr
      ⟨e, mem_filter.mpr ⟨he, heS, hv⟩, mem_filter.mpr ⟨hc, hm⟩⟩)

end JSP000689
