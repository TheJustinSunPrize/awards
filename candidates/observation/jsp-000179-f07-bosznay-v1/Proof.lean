import Mathlib
import Statement

namespace JSP000179

open scoped BigOperators
set_option autoImplicit false

lemma separate_nat
    {Q U V D T : ℕ} (hQ : 0 < Q) (hV : V < Q) (hT : T < Q)
    (h : U * Q + V = D * Q + T) : U = D ∧ V = T := by
  have hmod := congrArg (fun z => z % Q) h
  have hVT : V = T := by
    simpa [Nat.add_mod, Nat.mul_mod, Nat.mod_eq_of_lt hV,
      Nat.mod_eq_of_lt hT] using hmod
  have hprod : U * Q = D * Q := by omega
  exact ⟨Nat.eq_of_mul_eq_mul_right hQ hprod, hVT⟩

lemma two_mul_tri (n : ℕ) : 2 * tri n = n * (n + 1) := by
  have hEven : Even n ∨ Even (n + 1) := by
    rcases Nat.even_or_odd n with hn | hn
    · exact Or.inl hn
    · exact Or.inr hn.add_one
  have hdvd : 2 ∣ n * (n + 1) := by
    exact (even_iff_two_dvd).mp ((Nat.even_mul).mpr hEven)
  exact Nat.mul_div_cancel' hdvd

private lemma index_nat_bounds (q : ℕ) (hq : 2 ≤ q) (i : Fin (q - 1)) :
    1 ≤ i.1 + 1 ∧ i.1 + 1 < q := by
  omega

private lemma tri_lt_cube (q : ℕ) (hq : 2 ≤ q) (i : Fin (q - 1)) :
    tri (i.1 + 1) < q ^ 3 := by
  have hi := (index_nat_bounds q hq i)
  have hprod : (i.1 + 1) * (i.1 + 2) < q * q := by
    calc
      (i.1 + 1) * (i.1 + 2) < q * (i.1 + 2) :=
        Nat.mul_lt_mul_of_pos_right hi.2 (by omega)
      _ ≤ q * q := Nat.mul_le_mul_left q (by omega)
  have htri : tri (i.1 + 1) ≤ (i.1 + 1) * (i.1 + 2) := by
    dsimp [tri]
    exact Nat.div_le_self _ _
  have hqcube : q * q ≤ q ^ 3 := by
    nlinarith [show 1 ≤ q from by omega]
  exact lt_of_le_of_lt htri (lt_of_lt_of_le hprod hqcube)

private lemma tri_lt_sq (q : ℕ) (hq : 2 ≤ q) (i : Fin (q - 1)) :
    tri (i.1 + 1) < q ^ 2 := by
  have hi := (index_nat_bounds q hq i)
  have hprod : (i.1 + 1) * (i.1 + 2) < q * q := by
    calc
      (i.1 + 1) * (i.1 + 2) < q * (i.1 + 2) :=
        Nat.mul_lt_mul_of_pos_right hi.2 (by omega)
      _ ≤ q * q := Nat.mul_le_mul_left q (by omega)
  have htri : tri (i.1 + 1) ≤ (i.1 + 1) * (i.1 + 2) := by
    dsimp [tri]
    exact Nat.div_le_self _ _
  exact lt_of_le_of_lt htri (by simpa [pow_two] using hprod)

private lemma tri_mono {a b : ℕ} (hab : a ≤ b) : tri a ≤ tri b := by
  apply Nat.div_le_div_right
  exact Nat.mul_le_mul hab (by omega)

private lemma bosznay_strict (q : ℕ) (hq : 2 ≤ q)
    {i j : Fin (q - 1)} (hij : i < j) :
    bosznay q i < bosznay q j := by
  have hxy : i.1 + 1 < j.1 + 1 := by omega
  have hqpos : 0 < q ^ 3 := pow_pos (by omega) 3
  have hlin : (i.1 + 1) * q ^ 3 < (j.1 + 1) * q ^ 3 :=
    Nat.mul_lt_mul_of_pos_right hxy hqpos
  have htri : tri (i.1 + 1) ≤ tri (j.1 + 1) :=
    tri_mono (Nat.le_of_lt hxy)
  dsimp [bosznay]
  omega

private lemma bosznay_injective (q : ℕ) (hq : 2 ≤ q) :
    Function.Injective (bosznay q) := by
  intro i j hij
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact (Nat.ne_of_lt (bosznay_strict q hq hlt)) hij
  · exact (Nat.ne_of_lt (bosznay_strict q hq hgt)) hij.symm

private lemma bosznay_bounds (q : ℕ) (hq : 2 ≤ q) (i : Fin (q - 1)) :
    1 ≤ bosznay q i ∧ bosznay q i ≤ q ^ 4 := by
  have hi := index_nat_bounds q hq i
  have htri := tri_lt_sq q hq i
  have hq3 : 1 ≤ q ^ 3 := Nat.one_le_pow 3 q (by omega)
  have hlinlow : 1 ≤ (i.1 + 1) * q ^ 3 := by
    have h := Nat.mul_le_mul hi.1 hq3
    simpa using h
  have hxi : i.1 + 1 ≤ q - 1 := by omega
  have hlinear : (i.1 + 1) * q ^ 3 ≤ (q - 1) * q ^ 3 :=
    Nat.mul_le_mul_right (q ^ 3) hxi
  have htri' : tri (i.1 + 1) ≤ q ^ 2 := Nat.le_of_lt htri
  have hq2q3 : q ^ 2 ≤ q ^ 3 := by
    calc
      q ^ 2 = q ^ 2 * 1 := by simp
      _ ≤ q ^ 2 * q := Nat.mul_le_mul_left (q ^ 2) (by omega)
      _ = q ^ 3 := by ring
  have hupper : (i.1 + 1) * q ^ 3 + tri (i.1 + 1) ≤ q ^ 4 := by
    calc
      (i.1 + 1) * q ^ 3 + tri (i.1 + 1) ≤
          (q - 1) * q ^ 3 + q ^ 2 := Nat.add_le_add hlinear htri'
      _ ≤ (q - 1) * q ^ 3 + q ^ 3 := Nat.add_le_add_left hq2q3 _
      _ = ((q - 1) + 1) * q ^ 3 := by simp [Nat.add_mul]
      _ = q * q ^ 3 := by rw [Nat.sub_add_cancel (by omega)]
      _ = q ^ 4 := by ring
  dsimp [bosznay]
  exact ⟨le_trans hlinlow (Nat.le_add_right _ _), hupper⟩

private lemma card_lt_q (q : ℕ) (hq : 2 ≤ q) (s : Finset (Fin (q - 1))) :
    s.card < q := by
  have hcard : s.card ≤ q - 1 := by
    simpa using (Finset.card_le_card (Finset.subset_univ s))
  exact lt_of_le_of_lt hcard (Nat.sub_lt (by omega) (by omega))

private lemma tri_sum_lt_cube (q : ℕ) (hq : 2 ≤ q)
    (s : Finset (Fin (q - 1))) (hs : s.Nonempty) :
    (∑ j ∈ s, tri (j.1 + 1)) < q ^ 3 := by
  have hsum :
      (∑ j ∈ s, tri (j.1 + 1)) < ∑ _j ∈ s, q ^ 2 := by
    apply Finset.sum_lt_sum_of_nonempty hs
    intro j hj
    exact tri_lt_sq q hq j
  have hconst : (∑ _j ∈ s, q ^ 2) = s.card * (q ^ 2) := by
    simp [Finset.sum_const]
  have hcard := card_lt_q q hq s
  have hprod : s.card * (q ^ 2) < q * (q ^ 2) :=
    Nat.mul_lt_mul_of_pos_right hcard (by positivity)
  calc
    (∑ j ∈ s, tri (j.1 + 1)) < ∑ _j ∈ s, q ^ 2 := hsum
    _ = s.card * (q ^ 2) := hconst
    _ < q * (q ^ 2) := hprod
    _ = q ^ 3 := by ring

private lemma tri_center_product_lt_cube (q : ℕ) (hq : 2 ≤ q)
    (i : Fin (q - 1)) (s : Finset (Fin (q - 1))) :
    s.card * tri (i.1 + 1) < q ^ 3 := by
  have hcard := card_lt_q q hq s
  have htri := tri_lt_sq q hq i
  have hk : s.card * tri (i.1 + 1) ≤ q * tri (i.1 + 1) := by
    exact Nat.mul_le_mul_right _ (Nat.le_of_lt hcard)
  have hprod : q * tri (i.1 + 1) < q * (q ^ 2) :=
    Nat.mul_lt_mul_of_pos_left htri (by omega)
  calc
    s.card * tri (i.1 + 1) ≤ q * tri (i.1 + 1) := hk
    _ < q * (q ^ 2) := hprod
    _ = q ^ 3 := by ring

private lemma quadratic_sum_eq
    (q : ℕ) (i : Fin (q - 1)) (s : Finset (Fin (q - 1)))
    (hlin : (∑ j ∈ s, (j.1 + 1)) = s.card * (i.1 + 1))
    (htri : (∑ j ∈ s, tri (j.1 + 1)) = s.card * tri (i.1 + 1)) :
    (∑ j ∈ s, (j.1 + 1) ^ 2) = s.card * (i.1 + 1) ^ 2 := by
  have hsum2 :
      (∑ j ∈ s, (j.1 + 1) * ((j.1 + 1) + 1)) =
        s.card * ((i.1 + 1) * ((i.1 + 1) + 1)) := by
    calc
      (∑ j ∈ s, (j.1 + 1) * ((j.1 + 1) + 1)) =
          2 * (∑ j ∈ s, tri (j.1 + 1)) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro j hj
            exact (two_mul_tri (j.1 + 1)).symm
      _ = 2 * (s.card * tri (i.1 + 1)) := by rw [htri]
      _ = s.card * ((i.1 + 1) * ((i.1 + 1) + 1)) := by
        calc
          2 * (s.card * tri (i.1 + 1)) =
              s.card * (2 * tri (i.1 + 1)) := by ring
          _ = s.card * ((i.1 + 1) * ((i.1 + 1) + 1)) := by
            rw [two_mul_tri]
  have hsum2' :
      (∑ j ∈ s, (j.1 + 1) ^ 2) + (∑ j ∈ s, (j.1 + 1)) =
        s.card * (i.1 + 1) ^ 2 + s.card * (i.1 + 1) := by
    simpa [pow_two, Nat.mul_add, Finset.sum_add_distrib] using hsum2
  omega

private lemma all_indices_equal
    (q : ℕ) (i : Fin (q - 1)) (s : Finset (Fin (q - 1)))
    (hlin : (∑ j ∈ s, (j.1 + 1)) = s.card * (i.1 + 1))
    (hquad : (∑ j ∈ s, (j.1 + 1) ^ 2) = s.card * (i.1 + 1) ^ 2) :
    ∀ j ∈ s, j = i := by
  intro j hj
  let x : Fin (q - 1) → ℚ := fun k => (k.1 + 1 : ℚ)
  let a : ℚ := (i.1 + 1 : ℚ)
  have hlinQ : (∑ k ∈ s, x k) = (s.card : ℚ) * a := by
    dsimp [x, a]
    exact_mod_cast hlin
  have hquadQ : (∑ k ∈ s, (x k) ^ 2) = (s.card : ℚ) * a ^ 2 := by
    dsimp [x, a]
    exact_mod_cast hquad
  have hvar : (∑ k ∈ s, (x k - a) ^ 2) = 0 := by
    have hid :
        (∑ k ∈ s, (x k - a) ^ 2) =
          (∑ k ∈ s, (x k) ^ 2) - 2 * a * (∑ k ∈ s, x k) +
            (s.card : ℚ) * a ^ 2 := by
      calc
        (∑ k ∈ s, (x k - a) ^ 2) =
            ∑ k ∈ s, ((x k) ^ 2 - 2 * a * x k + a ^ 2) := by
              apply Finset.sum_congr rfl
              intro k hk
              ring
        _ = (∑ k ∈ s, (x k) ^ 2) - 2 * a * (∑ k ∈ s, x k) +
              (s.card : ℚ) * a ^ 2 := by
              simp [Finset.sum_sub_distrib, Finset.sum_add_distrib,
                Finset.mul_sum, Finset.sum_const]
    rw [hid, hquadQ, hlinQ]
    ring
  have hzero : (x j - a) ^ 2 = 0 := by
    have hnonneg : ∀ k ∈ s, 0 ≤ (x k - a) ^ 2 := by
      intro k hk
      positivity
    exact (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp hvar j hj
  have hx : x j = a := by
    have hsub : x j - a = 0 := sq_eq_zero_iff.mp hzero
    linarith
  dsimp [x, a] at hx
  have hnat : j.1 + 1 = i.1 + 1 := by exact_mod_cast hx
  have hval : j.1 = i.1 := by omega
  exact Fin.ext hval

/-- Bosznay's construction has no averaging relation among distinct indexed
members. This is the finite construction quoted in Section 1 of
Pham--Zakharov, arXiv:2410.14624v2. -/
theorem bosznay_nonAveraging (q : ℕ) (hq : 2 ≤ q) : IsNonAveraging q := by
  intro i s hnotmem hs haverage
  let Q := q ^ 3
  let U := ∑ j ∈ s, (j.1 + 1)
  let V := ∑ j ∈ s, tri (j.1 + 1)
  let D := s.card * (i.1 + 1)
  let T := s.card * tri (i.1 + 1)
  have hExpand : U * Q + V = D * Q + T := by
    dsimp [U, V, D, T, Q]
    dsimp [bosznay] at haverage
    rw [Finset.sum_add_distrib] at haverage
    rw [← Finset.sum_mul] at haverage
    rw [Nat.mul_add] at haverage
    simpa [Nat.mul_assoc] using haverage
  have hsep := separate_nat (Q := Q) (U := U) (V := V) (D := D) (T := T)
      (by dsimp [Q]; positivity)
      (by
        dsimp [V, Q]
        exact tri_sum_lt_cube q hq s hs)
      (by
        dsimp [T, Q]
        exact tri_center_product_lt_cube q hq i s)
      hExpand
  have hlin : (∑ j ∈ s, (j.1 + 1)) = s.card * (i.1 + 1) := by
    exact hsep.1
  have htri : (∑ j ∈ s, tri (j.1 + 1)) = s.card * tri (i.1 + 1) := by
    exact hsep.2
  rcases hs with ⟨j, hj⟩
  have hji : j = i := all_indices_equal q i s hlin (quadratic_sum_eq q i s hlin htri) j hj
  exact hnotmem (hji ▸ hj)

/-- The displayed values are distinct, lie in `[q^4]`, and form a
non-averaging subset of that interval. -/
theorem bosznay_construction (q : ℕ) (hq : 2 ≤ q) :
    (BosznaySet q).card = q - 1 ∧
      (∀ a ∈ BosznaySet q, 1 ≤ a ∧ a ≤ q ^ 4) ∧
        NonAveragingSet (BosznaySet q) := by
  have hinj : Function.Injective (bosznay q) := bosznay_injective q hq
  have hcard : (BosznaySet q).card = q - 1 := by
    unfold BosznaySet
    rw [Finset.card_image_of_injective _ hinj]
    simp
  have hbounds : ∀ a ∈ BosznaySet q, 1 ≤ a ∧ a ≤ q ^ 4 := by
    intro a ha
    rcases Finset.mem_image.mp ha with ⟨i, hi, rfl⟩
    exact bosznay_bounds q hq i
  have hset : NonAveragingSet (BosznaySet q) := by
    classical
    intro a ha t ht hnot htnon
    rcases Finset.mem_image.mp ha with ⟨i, hi, hai⟩
    have hpre : Set.InjOn (bosznay q)
        ((bosznay q) ⁻¹' (↑t : Set ℕ)) := by
      intro x hx y hy hxy
      exact hinj hxy
    let s : Finset (Fin (q - 1)) := t.preimage (bosznay q) hpre
    have hs_mem (x : Fin (q - 1)) :
        x ∈ s ↔ bosznay q x ∈ t := by
      dsimp [s]
      exact Finset.mem_preimage
    have hs_nonempty : s.Nonempty := by
      rcases htnon with ⟨z, hzt⟩
      have hzA : z ∈ BosznaySet q := ht hzt
      rcases Finset.mem_image.mp hzA with ⟨j, hj, hjz⟩
      refine ⟨j, (hs_mem j).2 ?_⟩
      rw [hjz]
      exact hzt
    have hi_not : i ∉ s := by
      intro his
      have hit : bosznay q i ∈ t := (hs_mem i).mp his
      exact hnot (hai ▸ hit)
    have himage : Finset.image (bosznay q) s = t := by
      apply Finset.ext
      intro z
      constructor
      · intro hz
        rcases Finset.mem_image.mp hz with ⟨j, hjs, rfl⟩
        exact (hs_mem j).mp hjs
      · intro hzt
        have hzA : z ∈ BosznaySet q := ht hzt
        rcases Finset.mem_image.mp hzA with ⟨j, hj, hjz⟩
        apply Finset.mem_image.mpr
        refine ⟨j, (hs_mem j).2 ?_, hjz⟩
        simpa [hjz] using hzt
    have hcard_st : s.card = t.card := by
      have hc := Finset.card_image_of_injective s hinj
      rw [himage] at hc
      exact hc.symm
    intro heq
    apply (show (∑ j ∈ s, bosznay q j) ≠
        s.card * bosznay q i from
          bosznay_nonAveraging q hq i s hi_not hs_nonempty)
    have hsum : (∑ z ∈ t, z) = ∑ j ∈ s, bosznay q j := by
      have hpre_s : Set.InjOn (bosznay q) (↑s : Set (Fin (q - 1))) := by
        intro x hx y hy hxy
        exact hinj hxy
      rw [← himage]
      exact Finset.sum_image hpre_s
    calc
      (∑ j ∈ s, bosznay q j) = ∑ z ∈ t, z := hsum.symm
      _ = t.card * a := heq
      _ = s.card * bosznay q i := by rw [← hcard_st, ← hai]
  exact ⟨hcard, hbounds, hset⟩

end JSP000179
