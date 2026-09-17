/- Copyright 2026 James-16. Apache 2.0. Developed with OpenAI Codex assistance. -/
import Erdos141FirstCases.Statements
import Mathlib.Data.Nat.Prime.Infinite
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

namespace Erdos141FirstCases

theorem nth_next_of_no_prime_between (n p q : ℕ) (hn : Nat.nth Nat.Prime n = p)
    (hq : q.Prime) (hpq : p < q)
    (hgap : ∀ x, p < x → x < q → ¬x.Prime) :
    Nat.nth Nat.Prime (n + 1) = q := by
  have hi : (Set.ofPred Nat.Prime).Infinite := by
    intro hf
    exact Nat.not_bddAbove_setOfPred_prime hf.bddAbove
  have hm := Nat.nth_strictMono hi
  have hlo : p < Nat.nth Nat.Prime (n + 1) := by
    rw [← hn]
    exact hm (Nat.lt_succ_self n)
  have hle : Nat.nth Nat.Prime (n + 1) ≤ q := by
    apply (Nat.isLeast_nth_of_infinite hi (n + 1)).2
    refine ⟨hq, ?_⟩
    intro j hj
    exact (hm.monotone (Nat.le_of_lt_succ hj)).trans_lt (hn ▸ hpq)
  rcases hle.eq_or_lt with he | hlt
  · exact he
  · exact (hgap _ hlo hlt (Nat.nth_mem_of_infinite hi _)).elim

theorem progression_from_certificates (p d k : ℕ) (hd : 0 < d) (hk : 0 < k)
    (hprime : ∀ i < k, Nat.Prime (p + i * d))
    (hgap : ∀ i, i + 1 < k → ∀ x, p + i * d < x →
      x < p + (i + 1) * d → ¬x.Prime) :
    ∃ s : Set ℕ, Erdos141.Set.IsAPAndPrimeProgressionOfLength s k := by
  let a := Nat.count Nat.Prime p
  have hnth : ∀ i < k, Nat.nth Nat.Prime (a + i) = p + i * d := by
    intro i
    induction i with
    | zero =>
      intro _
      simpa [a] using Nat.nth_count (by simpa using hprime 0 hk)
    | succ i ih =>
      intro hik
      have hprev := ih (Nat.lt_trans (Nat.lt_succ_self i) hik)
      have hstep : p + i * d < p + (i + 1) * d := by
        simpa only [Nat.add_mul, one_mul, Nat.add_assoc] using
          (Nat.lt_add_of_pos_right hd : p + i * d < p + i * d + d)
      simpa only [Nat.add_assoc] using
        nth_next_of_no_prime_between (a + i) _ _ hprev (hprime (i + 1) hik) hstep
          (hgap i hik)
  let f : Fin k → ℕ := fun i => p + i.val * d
  let s : Set ℕ := Set.range f
  have hfinj : Function.Injective f := by
    intro i j hij
    apply Fin.ext
    exact Nat.eq_of_mul_eq_mul_right hd (Nat.add_left_cancel hij)
  have hcard : ENat.card s = k := by
    change s.encard = k
    simpa only [Set.image_univ, Set.encard_univ, ENat.card_eq_coe_fintype_card,
      Fintype.card_fin] using hfinj.encard_image (Set.univ : Set (Fin k))
  refine ⟨s, ⟨p, d, hcard, ?_⟩, a, hcard, ?_⟩
  · ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨i.val, by exact_mod_cast i.isLt, by simp [f]⟩
    · rintro ⟨i, hi, rfl⟩
      refine ⟨⟨i, by exact_mod_cast hi⟩, ?_⟩
      simp [f]
  · ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨i.val, by exact_mod_cast i.isLt, hnth i.val i.isLt⟩
    · rintro ⟨i, hi, rfl⟩
      have hik : i < k := by exact_mod_cast hi
      exact ⟨⟨i, hik⟩, (hnth i hik).symm⟩

end Erdos141FirstCases
