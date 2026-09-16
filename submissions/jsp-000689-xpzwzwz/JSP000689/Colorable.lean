import JSP000689.Growth

namespace JSP000689
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Number of incident edges; the hypergraph is a finite set of finite vertex sets. -/
def degree (H : Finset (Finset V)) (v : V) : ℕ :=
  (H.filter fun e => v ∈ e).card

/-- A counting criterion for two-colourability, with a tunable growth factor. -/
theorem extension_growth (H : Finset (Finset V)) (r : ℕ) (hr : 2 ≤ r)
    (hu : ∀ e ∈ H, e.card = r) (β : ℚ) (hβ : 1 ≤ β)
    (hd : ∀ v, (degree H v : ℚ) ≤ (2 - β) * β ^ (r - 2))
    (S : Finset V) : ∀ v ∈ S,
      β * (colors H (S.erase v)).card ≤ (colors H S).card := by
  classical
  induction S using Finset.strongInductionOn with
  | _ S ih =>
    intro v hv
    let T := S.erase v
    let I := H.filter fun e => e ⊆ S ∧ v ∈ e
    let q : ℚ := β ^ (r - 2)
    let n : ℚ := (colors H T).card
    have hbpos : 0 < β := lt_of_lt_of_le (by norm_num) hβ
    have hqpos : 0 < q := pow_pos hbpos _
    have hn : 0 ≤ n := Nat.cast_nonneg _
    have hbad : ∀ e ∈ I, q * (bad H S v e).card ≤ n := by
      intro e he
      obtain ⟨heH, heS, hve⟩ := mem_filter.mp he
      have her := hu e heH
      have hne : (e.erase v).Nonempty := by
        apply card_pos.mp
        rw [card_erase_of_mem hve, her]
        omega
      obtain ⟨a, hae⟩ := hne
      have hav : a ≠ v := (mem_erase.mp hae).1
      have ha : a ∈ e := (mem_erase.mp hae).2
      let U := S \ e.erase a
      have hUT : U ⊆ T := by
        intro x hx
        obtain ⟨hxS, hxE⟩ := mem_sdiff.mp hx
        apply mem_erase.mpr
        refine ⟨?_, hxS⟩
        intro hxv
        subst x
        exact hxE (mem_erase.mpr ⟨hav.symm, hve⟩)
      have hc : T.card - U.card = r - 2 := by
        have heS' : e.erase a ⊆ S := (erase_subset a e).trans heS
        have hcU : U.card = S.card - (r - 1) := by
          dsimp [U]
          rw [card_sdiff_of_subset heS', card_erase_of_mem ha, her]
        have hcT : T.card = S.card - 1 := card_erase_of_mem hv
        have hle : r ≤ S.card := her ▸ card_le_card heS
        omega
      have hiter := growth_iterate (fun W => (colors H W).card) β hbpos.le T U hUT
        (fun W hWT w hw => ih W (lt_of_le_of_lt hWT (erase_ssubset hv)) w hw)
      rw [hc] at hiter
      have hbadcard : (bad H S v e).card ≤ (colors H U).card :=
        card_bad_le H S v a e heS hve ha hav
      have hbadcast : ((bad H S v e).card : ℚ) ≤ (colors H U).card := by
        exact_mod_cast hbadcard
      exact (mul_le_mul_of_nonneg_left hbadcast hqpos.le).trans hiter
    have hI : (I.card : ℚ) ≤ degree H v := by
      exact_mod_cast (card_le_card (show I ⊆ H.filter (fun e => v ∈ e) from by
        intro e he
        obtain ⟨heH, _, hve⟩ := mem_filter.mp he
        exact mem_filter.mpr ⟨heH, hve⟩))
    have hsum : q * (∑ e ∈ I, ((bad H S v e).card : ℚ)) ≤ (2 - β) * q * n := by
      calc
        q * (∑ e ∈ I, ((bad H S v e).card : ℚ)) =
            ∑ e ∈ I, q * ((bad H S v e).card : ℚ) := mul_sum ..
        _ ≤ ∑ _e ∈ I, n := sum_le_sum hbad
        _ = (I.card : ℚ) * n := by simp
        _ ≤ (degree H v : ℚ) * n := mul_le_mul_of_nonneg_right hI hn
        _ ≤ ((2 - β) * q) * n := mul_le_mul_of_nonneg_right (hd v) hn
    have hrec : 2 * n ≤ (colors H S).card + ∑ e ∈ I, ((bad H S v e).card : ℚ) := by
      dsimp [n, T, I]
      exact_mod_cast counting_recurrence H S v hv
    have hrecq := mul_le_mul_of_nonneg_left hrec hqpos.le
    apply (mul_le_mul_iff_right₀ hqpos).mp
    change q * (β * n) ≤ q * (colors H S).card
    nlinarith

/-- Any hypergraph obeying the counting criterion has a proper Boolean colouring. -/
theorem colorable (H : Finset (Finset V)) (r : ℕ) (hr : 2 ≤ r)
    (hu : ∀ e ∈ H, e.card = r) (β : ℚ) (hβ : 1 ≤ β)
    (hd : ∀ v, (degree H v : ℚ) ≤ (2 - β) * β ^ (r - 2)) :
    ∃ c : V → Bool, ∀ e ∈ H, ¬ Mono e c := by
  classical
  have hempty : (colors H ∅).Nonempty := by
    refine ⟨fun _ => false, ?_⟩
    rw [mem_colors]
    refine ⟨by simp, ?_⟩
    intro e he heE
    have hemp : e = ∅ := subset_empty.mp heE
    have hzero : r = 0 := by simpa [hemp] using (hu e he).symm
    omega
  have hbase : (1 : ℚ) ≤ (colors H ∅).card := by
    exact_mod_cast hempty.card_pos
  have hg := growth_iterate (fun S => (colors H S).card) β (by linarith)
    (univ : Finset V) ∅ (empty_subset _)
    (fun S _ v hv => extension_growth H r hr hu β hβ hd S v hv)
  have hp : 0 < β ^ ((univ : Finset V).card - (∅ : Finset V).card) :=
    pow_pos (by linarith) _
  have hpos : 0 < ((colors H univ).card : ℚ) := by nlinarith
  have hnat : 0 < (colors H univ).card := by exact_mod_cast hpos
  obtain ⟨c, hc⟩ := card_pos.mp hnat
  exact ⟨c, fun e he => ((mem_colors H univ c).mp hc).2 e he (subset_univ _)⟩

end JSP000689
