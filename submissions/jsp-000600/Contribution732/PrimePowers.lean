import Contribution732.Counting

/-!
# Prime-power orders in Alon's arbitrary-profile construction

The new finite-field/profile construction is instantiated with Mathlib's
`GaloisField p k`.  Its cardinality theorem requires `k ≠ 0`; the hypotheses
below make that restriction explicit.  In particular, the order `p ^ k`
need not itself be prime.

The construction is due to Noga Alon.  This file supplies a new formalized
prime-power specialization, extending the prime-only upstream implementation.
-/

namespace Contribution732

noncomputable section

noncomputable instance galoisFieldFintype (p k : ℕ) [Fact p.Prime] :
    Fintype (GaloisField p k) := Fintype.ofFinite (GaloisField p k)

lemma card_galoisField (p k : ℕ) [Fact p.Prime] (hk : 0 < k) :
    Fintype.card (GaloisField p k) = p ^ k := by
  rw [← Nat.card_eq_fintype_card]
  exact GaloisField.card p k (by omega)

/-- Every permitted truncation profile is realized at every prime-power
order, and the ground set may be enlarged beyond the projective-plane size. -/
theorem exists_compatible_of_prime_power_profile (p k n : ℕ)
    (hp : p.Prime) (hk : 0 < k) (m : Multiset ℕ)
    (hqn : (p ^ k) ^ 2 + p ^ k + 1 ≤ n)
    (hmcard : m.card = (p ^ k) ^ 2 + p ^ k + 1)
    (hmbounds : ∀ a ∈ m, 3 ≤ a ∧ a ≤ p ^ k + 1) :
    ∃ sizes : Multiset ℕ, Erdos732.BlockCompatible n sizes ∧
      sizes.filter (fun a ↦ 3 ≤ a) = m := by
  letI : Fact p.Prime := ⟨hp⟩
  have hnfield : Fintype.card (GaloisField p k) ^ 2 +
      Fintype.card (GaloisField p k) + 1 ≤ n := by
    simpa only [card_galoisField p k hk] using hqn
  apply exists_compatible_of_profile (GaloisField p k) n hnfield m
  · simpa only [card_galoisField p k hk] using hmcard
  · simpa only [card_galoisField p k hk] using hmbounds

/-- The exact stars-and-bars family count at every prime-power order.  The
binomial coefficient counts a constructed family of distinct compatible
multisets, not all compatible multisets on the ground set. -/
theorem complete_prime_power_profile_family (p k n : ℕ)
    (hp : p.Prime) (hk : 0 < k)
    (hqn : (p ^ k) ^ 2 + p ^ k + 1 ≤ n) :
    ∃ S : Finset (Multiset ℕ),
      S.card = Nat.choose ((p ^ k) ^ 2 + p ^ k + 1 + p ^ k - 2) (p ^ k - 2) ∧
      ∀ sizes ∈ S, Erdos732.BlockCompatible n sizes := by
  letI : Fact p.Prime := ⟨hp⟩
  have hnfield : Fintype.card (GaloisField p k) ^ 2 +
      Fintype.card (GaloisField p k) + 1 ≤ n := by
    simpa only [card_galoisField p k hk] using hqn
  simpa only [card_galoisField p k hk] using
    complete_profile_family (GaloisField p k) n hnfield

/-- Order four is a concrete non-prime order absent from the prime-field
upstream statement.  Its 21 projective-plane lines give 253 different
compatible block-size multisets on every ground set of size at least 21. -/
theorem order_four_profile_family (n : ℕ) (hn : 21 ≤ n) :
    ∃ S : Finset (Multiset ℕ),
      S.card = 253 ∧ ∀ sizes ∈ S, Erdos732.BlockCompatible n sizes := by
  have h := complete_prime_power_profile_family 2 2 n
    (by norm_num) (by norm_num) (by convert hn using 1 <;> norm_num)
  norm_num [Nat.choose] at h
  exact h

/-- At prime order five, allowing all profile multiplicities gives 5984
compatible multisets, compared with 125 in the prior bounded-frequency family. -/
theorem order_five_profile_family (n : ℕ) (hn : 31 ≤ n) :
    ∃ S : Finset (Multiset ℕ),
      S.card = 5984 ∧ ∀ sizes ∈ S, Erdos732.BlockCompatible n sizes := by
  have h := complete_prime_power_profile_family 5 1 n
    (by norm_num) (by norm_num) (by convert hn using 1 <;> norm_num)
  norm_num [Nat.choose] at h
  exact h

end

end Contribution732
