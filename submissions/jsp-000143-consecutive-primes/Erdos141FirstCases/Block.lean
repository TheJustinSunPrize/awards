/- Copyright 2026 James-16. Apache 2.0. Developed with OpenAI Codex assistance. -/
import Erdos141FirstCases.Composites

namespace Erdos141FirstCases

def BlockCertificate (base : ℕ) (L : List ℕ) : Prop :=
  ∀ r : Fin L.length,
    (L[r] ≠ 0 → 2 ≤ L[r] ∧ L[r] < start + (base + r) ∧
      (start + (base + r)) % L[r] = 0) ∧
    (L[r] = 0 → (base + r.val) % 210 = 0 ∨ base + r.val ∈ exceptional)

theorem composite_from_block (base : ℕ) (L : List ℕ) (hc : BlockCertificate base L)
    (r : ℕ) (hr : r < L.length) (hmod : (base + r) % 210 ≠ 0) :
    ¬ Nat.Prime (start + (base + r)) := by
  have hc := hc ⟨r, hr⟩
  by_cases hd : L[r] = 0
  · exact composite_exceptional (base + r) ((hc.2 hd).resolve_left hmod)
  · obtain ⟨hlo, hhi, hdiv⟩ := hc.1 hd
    exact Nat.not_prime_of_dvd_of_lt (Nat.dvd_of_mod_eq_zero hdiv) hlo hhi

end Erdos141FirstCases
