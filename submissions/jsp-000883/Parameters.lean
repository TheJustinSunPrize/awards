import SizeBounds
import Mathlib.Analysis.SpecialFunctions.Pow.NthRootLemmas

namespace Erdos1063

def scale (k : ℕ) : ℕ := Nat.nthRoot 16 k
def center (k : ℕ) : ℕ := k / (scale k)^2 + 1
def cost (k : ℕ) : ℕ := center k + (2*center k*scale k + k/(scale k+1))
def exponentCost (k : ℕ) : ℕ := 3+2*cost k

theorem parameter_arithmetic {t k : ℕ} (ht : 2 ≤ t) (hpow : t^16 ≤ k) :
    let E := k/t^2+1
    E < k ∧ k ≤ t^2*E ∧ k < (E+1)^2 ∧
      (E + (2*E*t + k/(t+1)))*t ≤ 7*k := by
  let E := k/t^2+1
  have ht0 : 0 < t := by omega
  have ht2 : 0 < t^2 := pow_pos ht0 _
  have h4 : t^4 ≤ k := le_trans (Nat.pow_le_pow_right ht0 (by decide : 4 ≤ 16)) hpow
  have h2 : t^2 ≤ k := le_trans (Nat.pow_le_pow_right ht0 (by decide : 2 ≤ 4)) h4
  have hdiv : k/t^2*t^2 ≤ k := Nat.div_mul_le_self k (t^2)
  have hEprod : E*t^2 ≤ 2*k := by dsimp [E]; nlinarith
  have hEmod := Nat.mod_lt k ht2
  have hEdiv := Nat.div_add_mod k (t^2)
  have hkE : k < t^2*E := by dsimp [E]; nlinarith
  have hEge : t^2 ≤ E := by
    have hh : t^2 ≤ k/t^2 := (Nat.le_div_iff_mul_le ht2).mpr (by nlinarith [h4])
    dsimp [E]
    omega
  have hfour : 4*E ≤ E*t^2 := by
    have hh := Nat.mul_le_mul_left E (by nlinarith : 4 ≤ t^2)
    simpa [Nat.mul_comm] using hh
  have hElt : E < k := by nlinarith
  have hy : k < (E+1)^2 := by nlinarith
  have hEt : E*t ≤ E*t^2 := Nat.mul_le_mul_left E (by nlinarith)
  have hquot : k/(t+1)*t ≤ k := le_trans
    (Nat.mul_le_mul_left (k/(t+1)) (by omega : t ≤ t+1)) (Nat.div_mul_le_self k (t+1))
  refine ⟨hElt, le_of_lt hkE, hy, ?_⟩
  change (E+(2*E*t+k/(t+1)))*t ≤ 7*k
  nlinarith

theorem scale_pow_le (k : ℕ) : (scale k)^16 ≤ k :=
  Nat.pow_nthRoot_le_iff.mpr (Or.inl (by decide))

theorem lt_scale_succ_pow (k : ℕ) : k < (scale k+1)^16 :=
  Nat.lt_pow_nthRoot_add_one (by decide) k

theorem scale_ge_of_pow_le {k t : ℕ} (h : t^16 ≤ k) : t ≤ scale k :=
  (Nat.le_nthRoot_iff (by decide)).mpr h

theorem parameter_witness {k : ℕ} (hk : 2^16 ≤ k) :
    ∃ n : ℕ, 2*k ≤ n ∧
      (∃ i0 < k, ¬ (n-i0) ∣ n.choose k ∧ ∀ i < k, i ≠ i0 → n-i ∣ n.choose k) ∧
      n ≤ 4*k^(exponentCost k) * ((scale k)^2)^k.primeCounting := by
  have ht := scale_ge_of_pow_le hk
  have hp := parameter_arithmetic ht (scale_pow_le k)
  exact exists_coarse_bounded_witness (M := scale k) (by norm_num at hk; omega)
    hp.1 (pow_pos (by omega) _) hp.2.1 hp.2.2.1

#print axioms parameter_arithmetic
#print axioms parameter_witness
end Erdos1063
