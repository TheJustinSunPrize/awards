import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

/-!
An unbounded additive improvement over the Erdos construction (JSP-000360).
Based on Chen and Dai, Acta Arithmetica 128 (2007), Theorem 1(ii).
The factorial construction sacrifices their quantitative iterated-log bound.
-/
namespace JSP000360

def offsets : ℕ → ℕ
  | 0 => 2
  | n + 1 => offsets n + (2 * offsets n).factorial

lemma offsets_strict : StrictMono offsets := by
  apply strictMono_nat_of_lt_succ
  intro n
  simp only [offsets]
  exact Nat.lt_add_of_pos_right (Nat.factorial_pos _)

lemma offsets_two (n : ℕ) : 2 ≤ offsets n :=
  offsets_strict.monotone (Nat.zero_le n)

lemma offsets_even (n : ℕ) : 2 ∣ offsets n := by
  induction n with
  | zero => decide
  | succ n ih =>
    exact dvd_add ih (Nat.dvd_factorial (by decide) (by have := offsets_two n; omega))

lemma offsets_congr {i n m : ℕ} (hin : i ≤ n) (hm : 0 < m)
    (hmi : m ≤ 2 * offsets i) : m ∣ offsets n - offsets i := by
  induction n, hin using Nat.le_induction with
  | base => simp
  | succ n hin ih =>
    have hle := offsets_strict.monotone hin
    have hd : m ∣ (2 * offsets n).factorial :=
      Nat.dvd_factorial hm (by omega)
    have heq : offsets (n + 1) - offsets i =
        (offsets n - offsets i) + (2 * offsets n).factorial := by
      simp only [offsets]
      omega
    rw [heq]
    exact dvd_add ih hd

def base (K : ℕ) : Finset ℕ :=
  Finset.Icc 1 K ∪ (Finset.Icc 1 K).image (2 * ·)

def standard (N : ℕ) : Finset ℕ :=
  (Finset.Icc 1 N).filter fun a =>
    2 * a ^ 2 ≤ N ∨ (2 ∣ a ∧ a ^ 2 ≤ 2 * N)

def Admissible (N : ℕ) (A : Finset ℕ) : Prop :=
  A ⊆ Finset.Icc 1 N ∧ ∀ a ∈ A, ∀ b ∈ A, Nat.lcm a b ≤ N

lemma lcm_le_product {a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    Nat.lcm a b ≤ a * b :=
  Nat.le_of_dvd (Nat.mul_pos ha hb) (Nat.lcm_dvd_mul a b)

lemma common_factor_bound {a b c : ℕ} (ha : 0 < a)
    (hca : c ∣ a) (hcb : c ∣ b) : c * Nat.lcm a b ≤ a * b := by
  have hc : c ≤ Nat.gcd a b :=
    Nat.le_of_dvd (Nat.gcd_pos_of_pos_left b ha) (Nat.dvd_gcd hca hcb)
  calc
    c * Nat.lcm a b ≤ Nat.gcd a b * Nat.lcm a b := Nat.mul_le_mul_right _ hc
    _ = a * b := Nat.gcd_mul_lcm a b

lemma base_eq_standard {K : ℕ} (hK : 2 ≤ K) : base K = standard (2 * K ^ 2) := by
  ext a
  simp only [base, standard, Finset.mem_union, Finset.mem_image,
    Finset.mem_Icc, Finset.mem_filter]
  constructor
  · rintro (⟨ha, hak⟩ | ⟨h, ⟨hh, hhk⟩, rfl⟩)
    · refine ⟨⟨ha, by nlinarith⟩, Or.inl ?_⟩
      nlinarith [Nat.pow_le_pow_left hak 2]
    · refine ⟨⟨by omega, by nlinarith⟩, Or.inr ⟨by omega, ?_⟩⟩
      nlinarith [Nat.pow_le_pow_left hhk 2]
  · rintro ⟨⟨ha, _⟩, hsmall | ⟨⟨h, heq⟩, hlarge⟩⟩
    · left
      exact ⟨ha, by nlinarith⟩
    · right
      refine ⟨h, ⟨by omega, ?_⟩, heq.symm⟩
      subst a
      nlinarith

lemma base_admissible {K : ℕ} (hK : 2 ≤ K) : Admissible (2*K^2) (base K) := by
  constructor
  · intro a ha
    rw [base_eq_standard hK] at ha
    exact (Finset.mem_filter.mp ha).1
  · intro a ha b hb
    simp only [base, Finset.mem_union, Finset.mem_image, Finset.mem_Icc] at ha hb
    rcases ha with ⟨ha, hak⟩ | ⟨u, ⟨hu, huk⟩, rfl⟩
    · rcases hb with ⟨hb, hbk⟩ | ⟨v, ⟨hv, hvk⟩, rfl⟩
      · have hl := lcm_le_product ha hb
        have hp := Nat.mul_le_mul hak hbk
        nlinarith
      · have hl := lcm_le_product ha (show 0 < 2*v by omega)
        have hp := Nat.mul_le_mul hak hvk
        nlinarith
    · rcases hb with ⟨hb, hbk⟩ | ⟨v, ⟨hv, hvk⟩, rfl⟩
      · have hl := lcm_le_product (show 0 < 2*u by omega) hb
        have hp := Nat.mul_le_mul huk hbk
        nlinarith
      · have hl := common_factor_bound (c := 2) (show 0 < 2*u by omega)
          (dvd_mul_right 2 u) (dvd_mul_right 2 v)
        have hp := Nat.mul_le_mul huk hvk
        nlinarith

/- A finite offset family is sufficient. This separates the lcm argument from
the factorial construction and makes all its assumptions explicit. -/
theorem extend_base (K D r : ℕ) (d : ℕ → ℕ)
    (hK : 2 ≤ K) (hKD : 3*D ≤ K) (hKeven : 2 ∣ K)
    (hdpos : ∀ i < r, 0 < d i)
    (hdle : ∀ i < r, d i ≤ D)
    (hdeven : ∀ i < r, 2 ∣ d i)
    (hdinj : Function.Injective d)
    (hcongr : ∀ i < r, ∀ j < d i, d i + j ∣ K + d i) :
    ∃ A : Finset ℕ, base K ⊆ A ∧ Admissible (2*K^2) A ∧
      A.card = (base K).card + r := by
  let E := (Finset.range r).image (fun i => 2*(K+d i))
  have hextra : ∀ a ∈ E, ∃ i < r, a = 2*(K+d i) := by
    intro a ha
    obtain ⟨i, hi, heq⟩ := Finset.mem_image.mp ha
    exact ⟨i, Finset.mem_range.mp hi, heq.symm⟩
  have hcross : ∀ i < r, ∀ h, 1 ≤ h → h ≤ K →
      Nat.lcm (2*(K+d i)) (2*h) ≤ 2*K^2 := by
    intro i hi h hh hhk
    have hd := hdle i hi
    have hp := hdpos i hi
    by_cases hinterior : h ≤ K-d i
    · have hl := common_factor_bound (b := 2*h) (c := 2)
          (show 0 < 2*(K+d i) by omega)
          (dvd_mul_right 2 _) (dvd_mul_right 2 _)
      have ht : h+d i ≤ K := by omega
      have hm := Nat.mul_le_mul_left (K+d i) ht
      nlinarith
    · let j := K-h
      have hj : j < d i := by dsimp [j]; omega
      have hdiv := hcongr i hi j hj
      have heq : K+d i = h+(d i+j) := by dsimp [j]; omega
      have hdivh : d i+j ∣ h := by
        rw [heq] at hdiv
        exact (Nat.dvd_add_iff_left (dvd_refl (d i+j))).mpr hdiv
      have hl := common_factor_bound (c := 2*(d i+j))
        (show 0 < 2*(K+d i) by omega)
        (Nat.mul_dvd_mul_left 2 hdiv) (Nat.mul_dvd_mul_left 2 hdivh)
      have htwo : 2 ≤ d i+j := by
        obtain ⟨q, hq⟩ := hdeven i hi
        omega
      have hl4 : 4 * Nat.lcm (2*(K+d i)) (2*h) ≤
          4*(K+d i)*h := by
        have := Nat.mul_le_mul_right (Nat.lcm (2*(K+d i)) (2*h))
          (show 4 ≤ 2*(d i+j) by omega)
        nlinarith
      have hm := Nat.mul_le_mul_left (K+d i) hhk
      have hm2 := Nat.mul_le_mul_right K (show d i ≤ K by omega)
      nlinarith
  have hdis : Disjoint (base K) E := by
    apply Finset.disjoint_left.mpr
    intro a ha he
    obtain ⟨i, hi, rfl⟩ := hextra a he
    have hp := hdpos i hi
    simp only [base, Finset.mem_union, Finset.mem_image, Finset.mem_Icc] at ha
    rcases ha with ⟨_, h⟩ | ⟨u, ⟨_, hu⟩, heq⟩ <;> omega
  refine ⟨base K ∪ E, Finset.subset_union_left, ?_, ?_⟩
  · constructor
    · intro a ha
      rcases Finset.mem_union.mp ha with ha | ha
      · exact (base_admissible hK).1 ha
      · obtain ⟨i, hi, rfl⟩ := hextra a ha
        have hd := hdle i hi
        exact Finset.mem_Icc.mpr ⟨by omega, by nlinarith⟩
    · have hc : ∀ a ∈ E, ∀ b ∈ base K, Nat.lcm a b ≤ 2*K^2 := by
        intro a ha b hb
        obtain ⟨i, hi, rfl⟩ := hextra a ha
        simp only [base, Finset.mem_union, Finset.mem_image, Finset.mem_Icc] at hb
        rcases hb with ⟨hb, hbk⟩ | ⟨h, ⟨hh, hhk⟩, rfl⟩
        · have hdvd : Nat.lcm (2*(K+d i)) b ∣ Nat.lcm (2*(K+d i)) (2*b) :=
            Nat.lcm_dvd (Nat.dvd_lcm_left _ _)
              ((dvd_mul_left b 2).trans (Nat.dvd_lcm_right _ _))
          exact (Nat.le_of_dvd (Nat.lcm_pos (by omega) (by omega)) hdvd).trans
            (hcross i hi b hb hbk)
        · exact hcross i hi h hh hhk
      intro a ha b hb
      rcases Finset.mem_union.mp ha with ha | ha
      · rcases Finset.mem_union.mp hb with hb | hb
        · exact (base_admissible hK).2 a ha b hb
        · simpa [Nat.lcm_comm] using hc b hb a ha
      · rcases Finset.mem_union.mp hb with hb | hb
        · exact hc a ha b hb
        · obtain ⟨i, hi, rfl⟩ := hextra a ha
          obtain ⟨j, hj, rfl⟩ := hextra b hb
          have hdi := hdle i hi
          have hdj := hdle j hj
          have h4i : 4 ∣ 2*(K+d i) := by
            simpa using Nat.mul_dvd_mul_left 2 (dvd_add hKeven (hdeven i hi))
          have h4j : 4 ∣ 2*(K+d j) := by
            simpa using Nat.mul_dvd_mul_left 2 (dvd_add hKeven (hdeven j hj))
          have hl := common_factor_bound (c := 4) (show 0 < 2*(K+d i) by omega) h4i h4j
          have hm := Nat.mul_le_mul (show K+d i ≤ K+D by omega)
            (show K+d j ≤ K+D by omega)
          have hsq := Nat.mul_self_le_mul_self hKD
          nlinarith
  · rw [Finset.card_union_of_disjoint hdis]
    have he : E.card = r := by
      dsimp [E]
      rw [Finset.card_image_of_injective]
      · exact Finset.card_range r
      · intro i j h
        dsimp at h
        apply hdinj
        omega
    rw [he]

theorem unbounded_extension (r M : ℕ) :
    ∃ N ≥ M, ∃ A : Finset ℕ,
      standard N ⊆ A ∧ Admissible N A ∧ A.card = (standard N).card + r := by
  let D := offsets r
  let P := (2*D).factorial
  let K := (4+2*M)*P-D
  have hD : 2 ≤ D := offsets_two r
  have hP : D ≤ P := by
    have := Nat.self_le_factorial (2*D)
    dsimp [P]
    omega
  have hPeven : 2 ∣ P := Nat.dvd_factorial (by decide) (by omega)
  have hprod : D ≤ (4+2*M)*P := by nlinarith
  have hKeq : K+D = (4+2*M)*P := Nat.sub_add_cancel hprod
  have hKD : 3*D ≤ K := by nlinarith
  have hK : 2 ≤ K := by omega
  have hKM : M ≤ K := by nlinarith
  have hKeven : 2 ∣ K := Nat.dvd_sub
    (hPeven.trans (dvd_mul_left P (4+2*M))) (offsets_even r)
  have hcongr : ∀ i < r, ∀ j < offsets i, offsets i+j ∣ K+offsets i := by
    intro i hi j hj
    have hle : offsets i ≤ D := offsets_strict.monotone (by omega)
    have hpos := offsets_two i
    have hmpos : 0 < offsets i+j := by omega
    have hmle : offsets i+j ≤ 2*offsets i := by omega
    have hdP : offsets i+j ∣ P := Nat.dvd_factorial hmpos (by omega)
    have hdDiff : offsets i+j ∣ D-offsets i := offsets_congr (by omega) hmpos hmle
    have hsum : (K+offsets i)+(D-offsets i) = K+D := by omega
    have hdSum : offsets i+j ∣ (K+offsets i)+(D-offsets i) := by
      rw [hsum, hKeq]
      exact hdP.trans (dvd_mul_left P (4+2*M))
    exact (Nat.dvd_add_iff_left hdDiff).mpr hdSum
  obtain ⟨A, hsub, hadm, hcard⟩ := extend_base K D r offsets hK hKD hKeven
    (fun i _ => by have := offsets_two i; omega)
    (fun i hi => offsets_strict.monotone (by omega))
    (fun i _ => offsets_even i) offsets_strict.injective hcongr
  refine ⟨2*K^2, by nlinarith, A, ?_, hadm, ?_⟩
  · simpa [← base_eq_standard hK] using hsub
  · simpa [← base_eq_standard hK] using hcard

#print axioms unbounded_extension
end JSP000360
