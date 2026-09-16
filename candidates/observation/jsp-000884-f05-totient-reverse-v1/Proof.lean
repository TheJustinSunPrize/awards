import Statement

set_option autoImplicit false

open Nat Set
open JSP000884

noncomputable section

/--
An attributed reproduction of the reverse-inequality infinitude theorem from
Erdos1064.lean.  The explicit family is `30 * 2 ^ k` for `k : ℕ`.
-/
theorem solution : target := by
  change reverseTotientSet.Infinite
  apply Set.infinite_of_injective_forall_mem (f := fun k : ℕ ↦ 30 * 2 ^ k)
  · intro a b hab
    simp only at hab
    have : (2 : ℕ) ^ a = 2 ^ b := by omega
    exact Nat.pow_right_injective (le_refl 2) this
  · intro k
    simp only [reverseTotientSet, Set.mem_ofPred_eq]
    have hφ : Nat.totient (30 * 2 ^ k) = 8 * 2 ^ k := by
      have h : 30 * 2 ^ k = 2 ^ (k + 1) * 15 := by ring
      rw [h, Nat.totient_mul (by norm_num),
        Nat.totient_prime_pow Nat.prime_two (by omega),
        show Nat.totient 15 = 8 from rfl, Nat.add_sub_cancel]
      ring
    have hsub : 30 * 2 ^ k - Nat.totient (30 * 2 ^ k) = 22 * 2 ^ k := by
      rw [hφ]
      omega
    have hφsub : Nat.totient (22 * 2 ^ k) = 10 * 2 ^ k := by
      rw [show 22 * 2 ^ k = 2 ^ (k + 1) * 11 by ring,
        Nat.totient_mul (by norm_num), Nat.totient_prime_pow (by norm_num) (by omega),
        show Nat.totient 11 = 10 from rfl, Nat.add_sub_cancel]
      ring
    rw [hsub, hφ, hφsub]
    have : (0 : ℕ) < 2 ^ k := pow_pos (by norm_num) k
    omega
