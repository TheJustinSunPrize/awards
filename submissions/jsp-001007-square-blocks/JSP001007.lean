import Mathlib
import JSP001007.Arithmetic
import JSP001007.PrimeBlocks

/-!
# JSP-001007 / the uniform half-residue sieve question

This repair keeps the arithmetic and downstream construction unchanged, and
isolates the repaired prime-block argument in JSP001007.PrimeBlocks.
The original revision failed native compilation, as reported by the user.
A repair is not a successful compiler run: see VERIFICATION.md for this
revision's actual compilation and transitive-axiom audit status.

The argument is independent of the unproved declarations in
FormalConjectures/GreensOpenProblems/44.lean.

Main statement: for every k and every lower bound N0, there are k distinct odd
primes below N^(9/10), and sets of exactly half their residue classes, leaving
strictly more than N/10 integers in [1,N].

The only global number-theoretic input is Mathlib's proved divergence of the
sum of the reciprocals of the primes. No additional axioms are introduced.
-/

set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

open scoped BigOperators

namespace JSP001007

/-- Remove the initial floor(p/2) residue classes. -/
def forbidden (p : ℕ) : Finset (ZMod p) :=
  (Finset.range (p / 2)).image (fun a : ℕ => (a : ZMod p))

lemma forbidden_card (p : ℕ) : (forbidden p).card = p / 2 := by
  classical
  have hinj : Set.InjOn (fun a : ℕ => (a : ZMod p)) (Finset.range (p / 2)) := by
    intro a ha b hb hab
    have hap : a < p :=
      (Finset.mem_range.mp ha).trans_le (Nat.div_le_self p 2)
    have hbp : b < p :=
      (Finset.mem_range.mp hb).trans_le (Nat.div_le_self p 2)
    have hv := congrArg ZMod.val hab
    simpa only [ZMod.val_natCast, Nat.mod_eq_of_lt hap,
      Nat.mod_eq_of_lt hbp] using hv
  exact (Finset.card_image_of_injOn hinj).trans (Finset.card_range _)

lemma avoids_forbidden_of_mod_ge (x p : ℕ) (h : p / 2 ≤ x % p) :
    (x : ZMod p) ∉ forbidden p := by
  intro hx
  obtain ⟨a, ha, he⟩ := Finset.mem_image.mp hx
  have ha' : a < p / 2 := Finset.mem_range.mp ha
  have hap : a < p := ha'.trans_le (Nat.div_le_self p 2)
  have hv := congrArg ZMod.val he
  simp only [ZMod.val_natCast, Nat.mod_eq_of_lt hap] at hv
  omega

/-- The same survivor-set definition as the half-residue sieve framework. -/
def remaining {k : ℕ} (N : ℕ) (p : Fin k → ℕ)
    (A : (i : Fin k) → Finset (ZMod (p i))) : Finset ℕ :=
  (Finset.Icc 1 N).filter (fun x => ∀ i, (x : ZMod (p i)) ∉ A i)

/-- An individual point in the common high-residue window survives every
    modulus in a sufficiently narrow cluster. -/
private lemma window_point_avoids
    (M J H p j s : ℕ)
    (hM : 64 ≤ M) (hH : 8 * H ≤ M) (hD : 8 * J * H ≤ M)
    (hpL : M ≤ p) (hpU : p ≤ M + H)
    (hj : j < J) (hs : s < M / 4) :
    ((j * M + 3 * (M / 4) + s : ℕ) : ZMod p) ∉ forbidden p := by
  exact avoids_forbidden_of_mod_ge _ _
    (Arithmetic.window_point_mod M J H p j s hM hH hD hpL hpU hj hs)

/-- Counting a rectangular set of surviving points; all floor effects are
    included, rather than discarded in an asymptotic estimate. -/
theorem window_card_bound {k : ℕ} (M J H : ℕ) (p : Fin k → ℕ)
    (hM : 64 ≤ M) (hH : 8 * H ≤ M) (hD : 8 * J * H ≤ M)
    (hpL : ∀ i, M ≤ p i) (hpU : ∀ i, p i ≤ M + H) :
    J * (M / 4) ≤
      (remaining (J * M) p (fun i => forbidden (p i))).card := by
  classical
  let T : ℕ := M / 4
  let rectangle := (Finset.range J).product (Finset.range T)
  let f : ℕ × ℕ → ℕ := fun a => a.1 * M + 3 * T + a.2
  let S : Finset ℕ := rectangle.image f
  have hinj : Set.InjOn f rectangle := by
    intro a ha b hb hab
    have haS : a.2 < T :=
      Finset.mem_range.mp (Finset.mem_product.mp ha).2
    have hbS : b.2 < T :=
      Finset.mem_range.mp (Finset.mem_product.mp hb).2
    have hpair := Arithmetic.window_points_injective M a.1 b.1 a.2 b.2
      hM haS hbS hab
    exact Prod.ext hpair.1 hpair.2

  have hcard : S.card = J * T := by
    calc
      S.card = rectangle.card := Finset.card_image_of_injOn hinj
      _ = J * T := by simp [rectangle]
  have hsub : S ⊆ remaining (J * M) p (fun i => forbidden (p i)) := by
    intro x hx
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
    have haJ : a.1 < J :=
      Finset.mem_range.mp (Finset.mem_product.mp ha).1
    have haS : a.2 < T :=
      Finset.mem_range.mp (Finset.mem_product.mp ha).2
    have hinterval := Arithmetic.window_point_in_interval M J a.1 a.2 hM haJ haS
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_Icc.mpr hinterval, ?_⟩
    intro i
    exact window_point_avoids M J H (p i) a.1 a.2
      hM hH hD (hpL i) (hpU i) haJ haS
  calc
    J * (M / 4) = S.card := hcard.symm
    _ ≤ _ := Finset.card_le_card hsub

/-- Full quantified counterexample, including arbitrarily large N.

In particular, k is NOT fixed to 1000. All moduli are distinct odd primes.
-/
theorem counterexamples (k N0 : ℕ) :
    ∃ (N : ℕ) (p : Fin k → ℕ)
      (A : (i : Fin k) → Finset (ZMod (p i))),
      N0 ≤ N ∧
      (∀ i, (p i).Prime ∧ 2 < p i) ∧
      StrictMono p ∧
      (∀ i, (p i) ^ 10 < N ^ 9) ∧
      (∀ i, (A i).card = (p i) / 2) ∧
      N < 10 * (remaining N p A).card := by
  classical
  obtain ⟨q, hq, hcount⟩ := large_primeBlock k (1000000000000 + N0)
  have hqbig : 1000000000000 ≤ q := by omega
  let M : ℕ := q ^ 2
  let J : ℕ := q / 100
  let H : ℕ := 2 * q + 1
  let N : ℕ := J * M
  let e : Fin k ↪o ℕ := (primeBlock q).orderEmbOfCardLe hcount
  let p : Fin k → ℕ := e
  let A : (i : Fin k) → Finset (ZMod (p i)) := fun i => forbidden (p i)
  have hpBlock (i : Fin k) : p i ∈ primeBlock q :=
    Finset.orderEmbOfCardLe_mem (primeBlock q) hcount i
  have hpPrime (i : Fin k) : (p i).Prime :=
    (Finset.mem_filter.mp (hpBlock i)).2
  have hpL (i : Fin k) : M ≤ p i :=
    (Finset.mem_Ico.mp (Finset.mem_filter.mp (hpBlock i)).1).1
  have hpSquare (i : Fin k) : p i < (q + 1) ^ 2 :=
    (Finset.mem_Ico.mp (Finset.mem_filter.mp (hpBlock i)).1).2
  have hpU (i : Fin k) : p i ≤ M + H := by
    have ht := hpSquare i
    dsimp [M, H]
    nlinarith
  have hconditions : 64 ≤ M ∧ 0 < J ∧ 8 * H ≤ M ∧
      8 * J * H ≤ M ∧ q ≤ M := Arithmetic.cluster_conditions q hqbig
  obtain ⟨hM, hJ, hH, hD, hqM⟩ := hconditions
  have hMN : M ≤ N := by
    have hm := Nat.mul_le_mul_right M (by omega : 1 ≤ J)
    simpa only [one_mul, N] using hm
  have hN0 : N0 ≤ N := by omega
  have hsurv := window_card_bound M J H p hM hH hD hpL hpU
  have hratio : M < 10 * (M / 4) := Arithmetic.window_density M hM
  have hdensity : N < 10 * (remaining N p A).card := by
    calc
      N < J * (10 * (M / 4)) := Nat.mul_lt_mul_of_pos_left hratio hJ
      _ = 10 * (J * (M / 4)) := by ring
      _ ≤ 10 * (remaining N p A).card := Nat.mul_le_mul_left 10 hsurv
  refine ⟨N, p, A, hN0, ?_, e.strictMono, ?_, ?_, hdensity⟩
  · intro i
    exact ⟨hpPrime i, by have := hpL i; omega⟩
  · intro i
    apply Arithmetic.cutoff_ten (hpPrime i).one_lt.le
    exact Arithmetic.cluster_cutoff_four hqbig (hpSquare i).le
  · intro i
    exact forbidden_card (p i)

/-- The fixed-(epsilon,eta) necessary consequence of the original proposed
    bound, written without real powers. Even this weaker bound is false. -/
def UniformTenthSieve : Prop :=
  ∃ k : ℕ, ∀ (N : ℕ) (p : Fin k → ℕ)
    (A : (i : Fin k) → Finset (ZMod (p i))),
    (∀ i, (p i).Prime) → StrictMono p →
    (∀ i, (p i) ^ 10 < N ^ 9) →
    (∀ i, (A i).card = (p i) / 2) →
    10 * (remaining N p A).card ≤ N

theorem not_uniform_tenth_sieve : ¬ UniformTenthSieve := by
  rintro ⟨k, hk⟩
  obtain ⟨N, p, A, _, hp, hm, he, hc, hd⟩ := counterexamples k 1
  exact (not_le_of_gt hd) (hk N p A (fun i => (hp i).1) hm he hc)

/-- Bridge from the exact integer exponent inequality to the conventional
    real-power notation N^(1 - epsilon), for epsilon = 1/10. -/
private lemma real_cutoff {p N : ℕ} (h : p ^ 10 < N ^ 9) :
    (p : ℝ) < (N : ℝ) ^ (1 - (1 / 10 : ℝ)) := by
  have hR : (p : ℝ) ^ 10 < (N : ℝ) ^ 9 := by exact_mod_cast h
  have hroot := Real.rpow_lt_rpow (by positivity : 0 ≤ (p : ℝ) ^ 10)
    hR (by norm_num : 0 < (1 / 10 : ℝ))
  have hleft : ((p : ℝ) ^ 10) ^ (1 / 10 : ℝ) = (p : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity : 0 ≤ (p : ℝ))]
    norm_num
  have hright : ((N : ℝ) ^ 9) ^ (1 / 10 : ℝ) =
      (N : ℝ) ^ (1 - (1 / 10 : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity : 0 ≤ (N : ℝ))]
    norm_num
  simpa only [hleft, hright] using hroot

/-- The original uniform claim, using (p-1)/2 forbidden classes and
    independent exponent/density parameters. -/
def ErdosUniformSieve : Prop :=
  ∀ (epsilon eta : ℝ), 0 < epsilon → 0 < eta →
    ∃ k : ℕ, ∀ (N : ℕ) (p : Fin k → ℕ)
      (A : (i : Fin k) → Finset (ZMod (p i))),
      (∀ i, (p i).Prime) → StrictMono p →
      (∀ i, (p i : ℝ) < (N : ℝ) ^ (1 - epsilon)) →
      (∀ i, (A i).card = (p i - 1) / 2) →
      ((remaining N p A).card : ℝ) < eta * (N : ℝ)

/-- Negative answer to the uniform question. -/
theorem not_erdos_uniform_sieve : ¬ ErdosUniformSieve := by
  intro h
  obtain ⟨k, hk⟩ := h (1 / 10) (1 / 10) (by norm_num) (by norm_num)
  obtain ⟨N, p, A, _, hp, hm, he, hc, hd⟩ := counterexamples k 1
  have hc' : ∀ i, (A i).card = (p i - 1) / 2 := by
    intro i
    have hodd : p i % 2 = 1 :=
      (hp i).1.eq_two_or_odd.resolve_left (by have := (hp i).2; omega)
    have hh := hc i
    omega
  have hsmall := hk N p A (fun i => (hp i).1) hm
    (fun i => real_cutoff (he i)) hc'
  have hlarge : (N : ℝ) < 10 * ((remaining N p A).card : ℝ) := by
    exact_mod_cast hd
  nlinarith

/-- Even allowing a threshold N0 depending on epsilon, eta and k does not
    salvage the uniform proposed bound. -/
def ErdosEventualUniformSieve : Prop :=
  ∀ (epsilon eta : ℝ), 0 < epsilon → 0 < eta →
    ∃ k N0 : ℕ, ∀ (N : ℕ) (p : Fin k → ℕ)
      (A : (i : Fin k) → Finset (ZMod (p i))),
      N0 ≤ N →
      (∀ i, (p i).Prime) → StrictMono p →
      (∀ i, (p i : ℝ) < (N : ℝ) ^ (1 - epsilon)) →
      (∀ i, (A i).card = (p i - 1) / 2) →
      ((remaining N p A).card : ℝ) < eta * (N : ℝ)

theorem not_erdos_eventual_uniform_sieve : ¬ ErdosEventualUniformSieve := by
  intro h
  obtain ⟨k, N0, hk⟩ := h (1 / 10) (1 / 10) (by norm_num) (by norm_num)
  obtain ⟨N, p, A, hN0, hp, hm, he, hc, hd⟩ := counterexamples k N0
  have hc' : ∀ i, (A i).card = (p i - 1) / 2 := by
    intro i
    have hodd : p i % 2 = 1 :=
      (hp i).1.eq_two_or_odd.resolve_left (by have := (hp i).2; omega)
    have hh := hc i
    omega
  have hsmall := hk N p A hN0 (fun i => (hp i).1) hm
    (fun i => real_cutoff (he i)) hc'
  have hlarge : (N : ℝ) < 10 * ((remaining N p A).card : ℝ) := by
    exact_mod_cast hd
  nlinarith

/-- The fixed-1000-prime formulation follows from the all-k construction.
    This does not use Green44.green_44 or any declaration with an unfinished proof. -/
theorem fixed_1000_counterexample :
    ∃ (N : ℕ) (p : Fin 1000 → ℕ)
      (A : (i : Fin 1000) → Finset (ZMod (p i))),
      (∀ i, (p i).Prime) ∧ StrictMono p ∧
      (p 999) ^ 10 < N ^ 9 ∧
      (∀ i, (A i).card = (p i) / 2) ∧
      N < 10 * (remaining N p A).card := by
  obtain ⟨N, p, A, _, hp, hm, he, hc, hd⟩ := counterexamples 1000 1
  exact ⟨N, p, A, (fun i => (hp i).1), hm, he 999, hc, hd⟩

#print axioms JSP001007.counterexamples
#print axioms JSP001007.not_uniform_tenth_sieve
#print axioms JSP001007.not_erdos_uniform_sieve
#print axioms JSP001007.not_erdos_eventual_uniform_sieve
#print axioms JSP001007.fixed_1000_counterexample

end JSP001007
