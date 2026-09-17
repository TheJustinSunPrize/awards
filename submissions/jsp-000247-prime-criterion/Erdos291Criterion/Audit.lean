import Erdos291Criterion

/-! Statement-fidelity and boundary checks. No conjecture repository is imported. -/
namespace Erdos291CriterionAudit

-- Repeated definitions make the exact public target reviewable here.
def L (n : ℕ) : ℕ := (Finset.Icc 1 n).lcm (fun x ↦ x)
def a (n : ℕ) : ℕ := ∑ k ∈ Finset.Icc 1 n, L n / k

theorem exact_public_statement (n p : ℕ) (hp : p.Prime) (hpn : p ≤ n) :
    let k := n / p ^ Nat.log p n
    p ∣ Nat.gcd (a n) (L n) ↔
      (p : ℤ) ∣ (∑ i ∈ Finset.Icc 1 k, (1 : ℚ) / i).num := by
  exact Erdos291Criterion.steinerberger_generalization n p hp hpn

-- p=2 is covered by the criterion. A leading digit p-1 alone does not suffice.
example : ¬2 ∣ Nat.gcd (a 2) (L 2) := by decide

-- Divisibility can occur with a leading digit other than p-1: 33 = 30 in base 11.
example : 33 / 11 ^ Nat.log 11 33 = 3 := by decide
example : 11 ∣ Nat.gcd (a 33) (L 33) := by decide

-- The hypothesis p ≤ n cannot simply be dropped (n=2, p=3).
example : ¬(3 ∣ Nat.gcd (a 2) (L 2) ↔
    (3 : ℤ) ∣ (∑ i ∈ Finset.Icc 1 ((2 : ℕ) / 3 ^ Nat.log 3 2), (1 : ℚ) / i).num) := by
  have hn : ¬3 ∣ Nat.gcd (a 2) (L 2) := by decide
  have hk : (2 : ℕ) / 3 ^ Nat.log 3 2 = 2 := by decide
  rw [hk]
  simp only [hn, false_iff, not_not]
  norm_num [Finset.sum_Icc_succ_top]

#print axioms Erdos291Criterion.steinerberger_generalization
#print axioms exact_public_statement
#check @exact_public_statement

end Erdos291CriterionAudit
