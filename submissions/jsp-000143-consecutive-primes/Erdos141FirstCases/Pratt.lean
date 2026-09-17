import Mathlib.NumberTheory.LucasPrimality
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.ReduceModChar

namespace Erdos141FirstCases

theorem prime_dvd_list_prod {q : ℕ} (hq : q.Prime) (L : List ℕ)
    (h : q ∣ L.prod) : ∃ r ∈ L, q ∣ r := by
  induction L with
  | nil => simpa using (hq.not_dvd_one h)
  | cons r rs ih =>
    rcases hq.dvd_mul.mp h with hr | hrs
    · exact ⟨r, List.mem_cons_self, hr⟩
    · obtain ⟨s, hs, hqs⟩ := ih hrs
      exact ⟨s, List.mem_cons_of_mem r hs, hqs⟩

/-- Lucas's criterion with an explicit, fully factored predecessor. -/
theorem pratt (p a : ℕ) (L : List ℕ) (hfac : p - 1 = L.prod)
    (hprime : ∀ q ∈ L, q.Prime)
    (hpow : (a : ZMod p) ^ (p - 1) = 1)
    (horder : ∀ q ∈ L, (a : ZMod p) ^ ((p - 1) / q) ≠ 1) : p.Prime := by
  apply lucas_primality p (a : ZMod p) hpow
  intro q hq hqd
  rw [hfac] at hqd
  obtain ⟨r, hr, hqr⟩ := prime_dvd_list_prod hq L hqd
  rcases (Nat.dvd_prime (hprime r hr)).mp hqr with h1 | rfl
  · exact (hq.ne_one h1).elim
  · exact horder q hr

end Erdos141FirstCases
