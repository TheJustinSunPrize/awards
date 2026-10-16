/-
Negative answer to Erdős problem 1202.

The claim refuted here is the question recorded at
https://www.erdosproblems.com/1202 and as Problem 44 of Ben Green's open-problem
list in its general form: for every `ε, η > 0`, some fixed number of primes
below `n^(1-ε)` should force every half-residue sieve to leave at most `ε n`
integers up to `n`. Liam Price and GPT-5.4 Pro showed that this fails. One
positive `ε` is enough, and the construction below produces, for every `k`,
primes below `n^(9/10)` whose upper halves leave more than `n/10` survivors.
-/

import JSP001007.Blocks
import JSP001007.PrimeCount
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Finset.Sort
import Mathlib.Tactic

open Finset Real

namespace JSP001007

/-- Positive integers `m ≤ n` avoiding every forbidden residue class `A i`. -/
def survivors (n : ℕ) {k : ℕ} (p : Fin k → ℕ)
    (A : (i : Fin k) → Finset (ZMod (p i))) : Finset ℕ :=
  (Icc 1 n).filter fun m => ∀ i, (m : ZMod (p i)) ∉ A i

/--
The universal claim on erdosproblems.com/1202. The source quantifies both `ε`
and `η`, while the displayed bound uses only `ε`; both quantifiers are kept.
-/
def UniversalHalfResidueBound : Prop :=
  ∀ ε η : ℝ, 0 < ε → 0 < η →
    ∃ k : ℕ, ∀ (n : ℕ) (p : Fin k → ℕ) (A : (i : Fin k) → Finset (ZMod (p i))),
      (∀ i, (p i).Prime) →
      StrictMono p →
      (∀ i, (p i : ℝ) < (n : ℝ) ^ (1 - ε)) →
      (∀ i, (A i).card = (p i - 1) / 2) →
      ((survivors n p A).card : ℝ) ≤ ε * n

lemma two_pow_poly (t : ℕ) (ht : 2 ≤ t) :
    (1024 * t + 32) * t ≤ 2 ^ (32 * t) := by
  induction t, ht using Nat.le_induction with
  | base => norm_num
  | succ m hm ihm =>
    have hm1 : 0 < m := by omega
    have hstep : (1024 * (m + 1) + 32) * (m + 1) ≤ 50 * ((1024 * m + 32) * m) := by
      have hm_sq : m ≤ m * m := Nat.le_mul_of_pos_right m hm1
      have h1056 : 1056 ≤ 1056 * (m * m) :=
        Nat.le_mul_of_pos_right 1056 (Nat.mul_pos hm1 hm1)
      have h2080 : 2080 * m ≤ 2080 * (m * m) := Nat.mul_le_mul_left _ hm_sq
      have hsum : 1024 * m * m + 2080 * m + 1056 ≤
          1024 * m * m + 2080 * (m * m) + 1056 * (m * m) := by
        gcongr
      have h4160 : 1024 * m * m + 2080 * (m * m) + 1056 * (m * m) = 4160 * (m * m) := by
        ring
      have h50 : 4160 * (m * m) ≤ 50 * (1024 * (m * m)) := by
        calc
          4160 * (m * m) ≤ (50 * 1024) * (m * m) :=
            Nat.mul_le_mul_right _ (by norm_num)
          _ = 50 * (1024 * (m * m)) := by rw [Nat.mul_assoc]
      have hgrow : 1024 * (m * m) ≤ (1024 * m + 32) * m := by
        have : 1024 * m * m ≤ (1024 * m + 32) * m := by
          apply Nat.mul_le_mul_right
          omega
        simpa [Nat.mul_assoc] using this
      calc
        (1024 * (m + 1) + 32) * (m + 1) = 1024 * m * m + 2080 * m + 1056 := by ring
        _ ≤ 1024 * m * m + 2080 * (m * m) + 1056 * (m * m) := hsum
        _ = 4160 * (m * m) := h4160
        _ ≤ 50 * (1024 * (m * m)) := h50
        _ ≤ 50 * ((1024 * m + 32) * m) := Nat.mul_le_mul_left _ hgrow
    calc
      (1024 * (m + 1) + 32) * (m + 1) ≤ 50 * ((1024 * m + 32) * m) := hstep
      _ ≤ 50 * 2 ^ (32 * m) := Nat.mul_le_mul_left _ ihm
      _ ≤ 2 ^ 32 * 2 ^ (32 * m) := by
            apply Nat.mul_le_mul_right
            norm_num
      _ = 2 ^ (32 * (m + 1)) := by
            rw [← Nat.pow_add]
            congr 1
            omega

lemma exists_prime_window {M H k : ℕ} (hH : 0 < H) (hk : 0 < k)
    (hcard : k * ((M - 1) / H + 1) ≤ ((Ioc M (2 * M)).filter Nat.Prime).card) :
    ∃ (B : ℕ) (S : Finset ℕ), S.card = k ∧
      (∀ p ∈ S, p.Prime ∧ B ≤ p ∧ p < B + H ∧ p ≤ 2 * M) ∧ M < B := by
  classical
  let P := (Ioc M (2 * M)).filter Nat.Prime
  let J := (M - 1) / H + 1
  let fiber : ℕ → Finset ℕ := fun j => P.filter fun p => (p - (M + 1)) / H = j
  have hJpos : 0 < J := by
    dsimp [J]
    exact Nat.succ_pos _
  have hmem : ∀ p ∈ P, (p - (M + 1)) / H ∈ range J := by
    intro p hp
    have hpI := (mem_filter.mp hp).1
    have hlo : M < p := (mem_Ioc.mp hpI).1
    have hhi : p ≤ 2 * M := (mem_Ioc.mp hpI).2
    have hsub : p - (M + 1) ≤ M - 1 := by omega
    have hdiv : (p - (M + 1)) / H ≤ (M - 1) / H := Nat.div_le_div_right hsub
    exact mem_range.mpr (by omega)
  have hsum : #P = ∑ j ∈ range J, (fiber j).card := by
    simpa [fiber] using
      (Finset.card_eq_sum_card_fiberwise (s := P) (t := range J)
        (f := fun p => (p - (M + 1)) / H) hmem)
  have hex : ∃ j ∈ range J, k ≤ (fiber j).card := by
    by_contra hnone
    push Not at hnone
    have hlt : ∀ j ∈ range J, (fiber j).card ≤ k - 1 := by
      intro j hj
      have hcardlt : (fiber j).card < k := hnone j hj
      omega
    have hle : ∑ j ∈ range J, (fiber j).card ≤ # (range J) * (k - 1) := by
      refine (Finset.sum_le_sum fun j hj => hlt j hj).trans ?_
      simp
    have hcardle : P.card ≤ J * (k - 1) := by
      simpa [hsum, card_range] using hle
    have hneed : J * k ≤ P.card := by
      rw [Nat.mul_comm]
      simpa [J, P] using hcard
    have hcontr : J * k ≤ J * (k - 1) := hneed.trans hcardle
    have : k ≤ k - 1 := Nat.le_of_mul_le_mul_left hcontr hJpos
    omega
  obtain ⟨j, hj, hjcard⟩ := hex
  obtain ⟨S, hSsub, hScard⟩ := Finset.exists_subset_card_eq hjcard
  refine ⟨M + 1 + j * H, S, hScard, ?_, ?_⟩
  · intro p hp
    have hpP : p ∈ P := (mem_filter.mp (hSsub hp)).1
    have hprime : p.Prime := (mem_filter.mp hpP).2
    have hid : (p - (M + 1)) / H = j := (mem_filter.mp (hSsub hp)).2
    have hpI : M < p ∧ p ≤ 2 * M := mem_Ioc.mp (mem_filter.mp hpP).1
    have hdiv := (Nat.div_add_mod (p - (M + 1)) H).symm
    have hmod := Nat.mod_lt (p - (M + 1)) hH
    have hlo : j * H ≤ p - (M + 1) := by
      have : (p - (M + 1)) / H * H ≤ p - (M + 1) := Nat.div_mul_le_self _ _
      simpa [hid, Nat.mul_comm] using this
    have hhi : p - (M + 1) < (j + 1) * H := by
      have hdecomp : p - (M + 1) = j * H + (p - (M + 1)) % H := by
        simpa [hid, Nat.mul_comm] using hdiv
      calc
        p - (M + 1) = j * H + (p - (M + 1)) % H := hdecomp
        _ < j * H + H := Nat.add_lt_add_left hmod _
        _ = (j + 1) * H := by rw [Nat.succ_mul]
    have hM1 : M + 1 ≤ p := Nat.succ_le_of_lt hpI.1
    have hBle : M + 1 + j * H ≤ p := by
      calc
        M + 1 + j * H ≤ M + 1 + (p - (M + 1)) := Nat.add_le_add_left hlo _
        _ = p := Nat.add_sub_of_le hM1
    have hBlt : p < M + 1 + j * H + H := by
      have hsplit : p = M + 1 + (p - (M + 1)) := (Nat.add_sub_of_le hM1).symm
      have hhi' : p - (M + 1) < j * H + H := by simpa [Nat.succ_mul] using hhi
      calc
        p = M + 1 + (p - (M + 1)) := hsplit
        _ < M + 1 + (j * H + H) := Nat.add_lt_add_left hhi' _
        _ = M + 1 + j * H + H := by rw [← Nat.add_assoc]
    exact ⟨hprime, hBle, hBlt, hpI.2⟩
  · exact (Nat.lt_add_one M).trans_le (Nat.le_add_right _ _)

lemma pow_ten_lt_nine {t : ℕ} (ht : 2 ≤ t) :
    (2 ^ (64 * t + 1)) ^ 10 < (2 ^ (72 * t + 1)) ^ 9 := by
  have hlt : 10 * (64 * t + 1) < 9 * (72 * t + 1) := by omega
  calc
    (2 ^ (64 * t + 1)) ^ 10 = 2 ^ ((64 * t + 1) * 10) := by rw [← Nat.pow_mul]
    _ = 2 ^ (10 * (64 * t + 1)) := by rw [Nat.mul_comm]
    _ < 2 ^ (9 * (72 * t + 1)) := Nat.pow_lt_pow_right (by norm_num) hlt
    _ = 2 ^ ((72 * t + 1) * 9) := by rw [Nat.mul_comm]
    _ = (2 ^ (72 * t + 1)) ^ 9 := by rw [Nat.pow_mul]

lemma nat_lt_rpow_nine_tenths {p N : ℕ} (hN : 0 < N) (h : p ^ 10 < N ^ 9) :
    (p : ℝ) < (N : ℝ) ^ (9 / 10 : ℝ) := by
  have hreal : (p : ℝ) ^ 10 < (N : ℝ) ^ 9 := by exact_mod_cast h
  have hroot : (p : ℝ) < ((N : ℝ) ^ 9) ^ (10 : ℝ)⁻¹ :=
    (Real.lt_rpow_inv_iff_of_pos (by positivity) (by positivity)
      (by norm_num : (0 : ℝ) < 10)).2 (by simpa [Real.rpow_natCast] using hreal)
  have hpow : ((N : ℝ) ^ 9) ^ (10 : ℝ)⁻¹ = (N : ℝ) ^ (9 / 10 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity : (0 : ℝ) ≤ N)]
    norm_num
  simpa [hpow] using hroot

set_option maxHeartbeats 1500000 in
lemma counterexample_of_k (k : ℕ) (hk : 0 < k) :
    ∃ (n : ℕ) (p : Fin k → ℕ) (A : (i : Fin k) → Finset (ZMod (p i))),
      (∀ i, (p i).Prime) ∧
      StrictMono p ∧
      (∀ i, (p i : ℝ) < (n : ℝ) ^ (9 / 10 : ℝ)) ∧
      (∀ i, (A i).card = (p i - 1) / 2) ∧
      (1 / 10 : ℝ) * n < (survivors n p A).card := by
  classical
  let t := k + 1
  have ht : 2 ≤ t := by omega
  let M := 2 ^ (64 * t)
  let H := 2 ^ (32 * t)
  let Q := 2 ^ (8 * t)
  let D := 1024 * t + 32
  have hMbig : 2 ^ 24 ≤ M := by
    have : 24 ≤ 64 * t := by omega
    exact Nat.pow_le_pow_right (by norm_num) this
  have hHpos : 0 < H := by positivity
  have hQpos : 0 < Q := by positivity
  have hMpos : 0 < M := by positivity
  have hlog : Nat.log 2 (2 * M) = 64 * t + 1 := by
    have h2M : 2 * M = 2 ^ (64 * t + 1) := by
      dsimp [M]
      rw [← Nat.pow_succ']
    rw [h2M, Nat.log_pow (by norm_num : 1 < 2)]
  have hD : 16 * (Nat.log 2 (2 * M) + 1) = D := by
    rw [hlog]
    dsimp [D]
    ring
  have hcount0 := many_primes_Ioc hMbig
  have hcount : M < ((Ioc M (2 * M)).filter Nat.Prime).card * D := by
    simpa [hD] using hcount0
  have hHH : M = H * H := by
    dsimp [M, H]
    rw [← Nat.pow_add]
    apply congrArg (fun e => 2 ^ e)
    rw [← Nat.two_mul, ← Nat.mul_assoc]
  have hpred : (H * H - 1) / H = H - 1 := by
    have hrepr : H * H - 1 = (H - 1) + H * (H - 1) := by
      calc
        H * H - 1 = H * ((H - 1) + 1) - 1 := by
          have : H = (H - 1) + 1 := by omega
          rw [← this]
        _ = H * (H - 1) + H - 1 := by rw [Nat.mul_add, Nat.mul_one]
        _ = (H - 1) + H * (H - 1) := by omega
    rw [hrepr, Nat.add_mul_div_left (H - 1) (H - 1) hHpos]
    have : (H - 1) / H = 0 := Nat.div_eq_of_lt (by omega)
    simp [this]
  have hJ : (M - 1) / H + 1 = H := by
    rw [hHH, hpred]
    exact Nat.sub_add_cancel (Nat.succ_le_of_lt hHpos)
  have hpoly : D * t ≤ H := by
    simpa [D, H] using two_pow_poly t ht
  have hk_eq : k = t - 1 := by omega
  have hsub : D * (t - 1) = D * t - D := by
    simpa [Nat.mul_one] using Nat.mul_sub_left_distrib D t 1
  have hkD : k * D ≤ H - D := by
    rw [hk_eq, Nat.mul_comm]
    exact (hsub.symm ▸ Nat.sub_le_sub_right hpoly D)
  have hprod : k * D * H ≤ (H - D) * H := Nat.mul_le_mul_right _ hkD
  have hdiff : (H - D) * H = M - D * H := by
    calc
      (H - D) * H = H * (H - D) := Nat.mul_comm _ _
      _ = H * H - H * D := Nat.mul_sub_left_distrib H H D
      _ = M - D * H := by rw [← hHH, Nat.mul_comm H D]
  have hDpos : 0 < D := by
    dsimp [D]
    exact lt_of_lt_of_le (by decide : 0 < 32) (Nat.le_add_left 32 (1024 * t))
  have hDH : 1 ≤ D * H := Nat.succ_le_of_lt (Nat.mul_pos hDpos hHpos)
  have hcancel : k * H < ((Ioc M (2 * M)).filter Nat.Prime).card := by
    have hle : k * D * H ≤ M - D * H := by
      rw [← hdiff]
      exact hprod
    have hle1 : M - D * H ≤ M - 1 := Nat.sub_le_sub_left hDH M
    have hltM : k * D * H < M :=
      (hle.trans hle1).trans_lt (Nat.sub_lt hMpos (by decide : 0 < 1))
    have hlt : k * D * H < ((Ioc M (2 * M)).filter Nat.Prime).card * D := hltM.trans hcount
    have hcomm : k * H * D < ((Ioc M (2 * M)).filter Nat.Prime).card * D := by
      rw [Nat.mul_assoc, Nat.mul_comm H D, ← Nat.mul_assoc]
      exact hlt
    exact (Nat.mul_lt_mul_right hDpos).mp hcomm
  have hwindowCard : k * ((M - 1) / H + 1) ≤
      ((Ioc M (2 * M)).filter Nat.Prime).card := by
    rw [hJ]
    exact Nat.le_of_lt hcancel
  obtain ⟨B, S, hScard, hS, hBM⟩ := exists_prime_window hHpos hk hwindowCard
  have hBpos : 0 < B := hMpos.trans hBM
  have hMne : M ≠ 1 := ne_of_gt (lt_of_lt_of_le (by decide : 1 < 2 ^ 24) hMbig)
  have hB_le : B ≤ 2 * M - 1 := by
    have hne : S.Nonempty := card_pos.mp (by rw [hScard]; exact hk)
    obtain ⟨p0, hp0⟩ := hne
    have hp0' := hS p0 hp0
    have hnot : ¬ (2 * M).Prime := Nat.not_prime_mul (by decide) hMne
    have hne2 : p0 ≠ 2 * M := by
      intro h
      exact hnot (h ▸ hp0'.1)
    exact hp0'.2.1.trans (Nat.le_sub_one_of_lt (Nat.lt_of_le_of_ne hp0'.2.2.2 hne2))
  let N := Q * (2 * M)
  have hNpos : 0 < N := by dsimp [N]; positivity
  have h4exp : 4 ≤ 64 * t := by
    calc
      4 ≤ 64 * 2 := by decide
      _ ≤ 64 * t := Nat.mul_le_mul_left _ ht
  have h1exp : 1 ≤ 64 * t := (by decide : (1 : ℕ) ≤ 4).trans h4exp
  have hM16 : M / 16 = 2 ^ (64 * t - 4) := by
    have h16 : (16 : ℕ) = 2 ^ 4 := by norm_num
    rw [h16]
    dsimp [M]
    exact Nat.pow_div h4exp (by norm_num)
  have hM2 : M / 2 = 2 ^ (64 * t - 1) := by
    have h2 : (2 : ℕ) = 2 ^ 1 := by norm_num
    rw [h2]
    dsimp [M]
    exact Nat.pow_div h1exp (by norm_num)
  have h8 : M / 2 = 8 * (M / 16) := by
    rw [hM2, hM16]
    have : (8 : ℕ) = 2 ^ 3 := by norm_num
    rw [this, ← Nat.pow_add]
    apply congrArg (fun e => 2 ^ e)
    have hsum : (64 * t - 4) + 4 = 64 * t := Nat.sub_add_cancel h4exp
    have hsplit : (64 * t - 4) + 3 + 1 = 64 * t := by
      simpa [Nat.add_assoc, show (3 : ℕ) + 1 = 4 by decide] using hsum
    have : 64 * t - 1 = 3 + (64 * t - 4) := by
      simpa [Nat.add_comm] using (Nat.eq_sub_of_add_eq hsplit).symm
    exact this
  have hQH : (Q - 1) * H ≤ M / 16 := by
    have hpow : Q * H = 2 ^ (40 * t) := by
      dsimp [Q, H]
      rw [← Nat.pow_add]
      apply congrArg (fun e => 2 ^ e)
      rw [← Nat.add_mul]
    have h40 : 40 * t ≤ 64 * t - 4 := by
      have h24 : 4 ≤ 24 * t := by
        calc
          4 ≤ 24 * 2 := by decide
          _ ≤ 24 * t := Nat.mul_le_mul_left _ ht
      have hsum : 40 * t + 4 ≤ 64 * t := by
        calc
          40 * t + 4 ≤ 40 * t + 24 * t := Nat.add_le_add_left h24 _
          _ = 64 * t := by rw [← Nat.add_mul]
      exact Nat.le_sub_of_add_le hsum
    calc
      (Q - 1) * H ≤ Q * H := Nat.mul_le_mul_right _ (Nat.sub_le _ _)
      _ = 2 ^ (40 * t) := hpow
      _ ≤ 2 ^ (64 * t - 4) := Nat.pow_le_pow_right (by norm_num) h40
      _ = M / 16 := hM16.symm
  let lo := M / 16
  let hi := (B - 1) / 2
  have hlo_pos : 0 < lo := by
    dsimp [lo]
    rw [hM16]
    positivity
  have hlo_hi : lo ≤ hi := by
    dsimp [lo, hi]
    have hhalf : M / 2 ≤ (B - 1) / 2 :=
      Nat.div_le_div_right (Nat.le_sub_one_of_lt hBM)
    have hsmall : M / 16 ≤ M / 2 := by
      rw [h8]
      exact Nat.le_mul_of_pos_left _ (by norm_num)
    exact hsmall.trans hhalf
  have hhi_lt : hi < B := by
    dsimp [hi]
    exact (Nat.div_le_self (B - 1) 2).trans_lt (Nat.sub_lt hBpos (by decide))
  let R := blockSet B Q lo hi
  have hRcard : R.card = Q * (hi + 1 - lo) := blockSet_card hhi_lt hlo_hi
  have hspan : 7 * (M / 16) + 1 ≤ hi + 1 - lo := by
    have hhalf : M / 2 ≤ hi := by
      dsimp [hi]
      exact Nat.div_le_div_right (Nat.le_sub_one_of_lt hBM)
    have hsuble : M / 2 + 1 - lo ≤ hi + 1 - lo :=
      Nat.sub_le_sub_right (Nat.add_le_add_right hhalf 1) lo
    have hident : M / 2 + 1 - lo = 7 * (M / 16) + 1 := by
      dsimp [lo]
      have hle : M / 16 ≤ M / 2 := by
        rw [h8]
        exact Nat.le_mul_of_pos_left _ (by norm_num)
      have hdiff : M / 2 - M / 16 = 7 * (M / 16) := by
        rw [h8]
        have hsub := (Nat.sub_mul 8 1 (M / 16)).symm
        simpa [Nat.one_mul, show (8 : ℕ) - 1 = 7 by decide] using hsub
      rw [Nat.add_comm (M / 2) 1, Nat.add_sub_assoc hle, hdiff, Nat.add_comm]
    exact hident ▸ hsuble
  have hN32 : N = 32 * (Q * (M / 16)) := by
    have hMeq : M = 16 * (M / 16) := by
      have hdvd : 16 ∣ M := by
        rw [show (16 : ℕ) = 2 ^ 4 by norm_num]
        dsimp [M]
        exact Nat.pow_dvd_pow _ h4exp
      exact (Nat.mul_div_cancel' hdvd).symm
    have h2 : 2 * M = 32 * (M / 16) := by
      conv_lhs => rw [hMeq]
      rw [← Nat.mul_assoc, show (2 : ℕ) * 16 = 32 by decide]
    dsimp [N]
    rw [h2, Nat.mul_left_comm]
  have hten : N < 10 * R.card := by
    have hlt_span : 7 * (M / 16) < hi + 1 - lo :=
      lt_of_lt_of_le (Nat.lt_succ_self _) hspan
    have hcardlt : Q * (7 * (M / 16)) < R.card := by
      rw [hRcard]
      exact Nat.mul_lt_mul_of_pos_left hlt_span hQpos
    have hx : 0 < Q * (M / 16) := by positivity
    have h32 : 32 * (Q * (M / 16)) < 70 * (Q * (M / 16)) :=
      Nat.mul_lt_mul_of_pos_right (by norm_num) hx
    have h70 : 70 * (Q * (M / 16)) = 10 * (Q * (7 * (M / 16))) := by
      rw [show (70 : ℕ) = 10 * 7 by decide, Nat.mul_assoc]
      apply congrArg (fun z => 10 * z)
      exact Nat.mul_left_comm 7 Q (M / 16)
    have h10 : 10 * (Q * (7 * (M / 16))) < 10 * R.card :=
      Nat.mul_lt_mul_of_pos_left hcardlt (by norm_num)
    calc
      N = 32 * (Q * (M / 16)) := hN32
      _ < 70 * (Q * (M / 16)) := h32
      _ = 10 * (Q * (7 * (M / 16))) := h70
      _ < 10 * R.card := h10
  have h2M : 2 * M = 2 ^ (64 * t + 1) := by
    dsimp [M]
    rw [← Nat.pow_succ']
  have hNpow : N = 2 ^ (72 * t + 1) := by
    dsimp [N, Q]
    rw [h2M, ← Nat.pow_add]
    apply congrArg (fun e => 2 ^ e)
    rw [← Nat.add_assoc, ← Nat.add_mul]
  let prime : Fin k → ℕ := fun i => S.orderEmbOfFin hScard i
  have hmem_prime (i : Fin k) : prime i ∈ S := orderEmbOfFin_mem S hScard i
  have hprime_all (i : Fin k) : (prime i).Prime := (hS _ (hmem_prime i)).1
  have hmono : StrictMono prime := (S.orderEmbOfFin hScard).strictMono
  let A : (i : Fin k) → Finset (ZMod (prime i)) := fun i =>
    have : NeZero (prime i) := ⟨(hprime_all i).ne_zero⟩
    upperHalf (prime i)
  have hAcard : ∀ i, (A i).card = (prime i - 1) / 2 := by
    intro i
    have : NeZero (prime i) := ⟨(hprime_all i).ne_zero⟩
    have hgt : 2 < prime i := by
      have hBlo : B ≤ prime i := (hS _ (hmem_prime i)).2.1
      have hMlt : M < prime i := lt_of_lt_of_le hBM hBlo
      have h24 : 2 ^ 24 ≤ prime i := hMbig.trans hMlt.le
      exact lt_of_lt_of_le (by decide : 2 < 2 ^ 24) h24
    dsimp [A]
    exact upperHalf_card (hprime_all i) hgt
  have hRsub : R ⊆ survivors N prime A := by
    intro m hm
    obtain ⟨qr, hqr, rfl⟩ := mem_image.mp hm
    have hq : qr.1 < Q := mem_range.mp (mem_product.mp hqr).1
    have hr := mem_Icc.mp (mem_product.mp hqr).2
    refine mem_filter.mpr ⟨?_, ?_⟩
    · refine mem_Icc.mpr ⟨?_, ?_⟩
      · have hlo1 : 1 ≤ lo := Nat.succ_le_of_lt hlo_pos
        exact hlo1.trans (hr.1.trans (Nat.le_add_left qr.2 (B * qr.1)))
      · have hrlt : qr.2 < B := by
          have hrhi : qr.2 ≤ (B - 1) / 2 := by
            dsimp [hi] at hr
            exact hr.2
          exact hrhi.trans_lt
            ((Nat.div_le_self (B - 1) 2).trans_lt (Nat.sub_lt hBpos (by decide : 0 < 1)))
        have hlt : B * qr.1 + qr.2 < B * (qr.1 + 1) := by
          rw [Nat.mul_succ]
          exact Nat.add_lt_add_left hrlt _
        have hle1 : B * (qr.1 + 1) ≤ B * Q :=
          Nat.mul_le_mul_left _ (Nat.succ_le_of_lt hq)
        have hle2 : B * Q ≤ (2 * M - 1) * Q := Nat.mul_le_mul_right _ hB_le
        have hle3 : (2 * M - 1) * Q ≤ 2 * M * Q :=
          Nat.mul_le_mul_right _ (Nat.sub_le _ _)
        have hNeq : 2 * M * Q = N := by
          dsimp [N]
          rw [Nat.mul_comm]
        have hstep1 : B * qr.1 + qr.2 < B * Q := hlt.trans_le hle1
        have hstep2 : B * qr.1 + qr.2 < (2 * M - 1) * Q := hstep1.trans_le hle2
        have hstep3 : B * qr.1 + qr.2 ≤ 2 * M * Q :=
          Nat.le_of_lt (hstep2.trans_le hle3)
        rw [hNeq] at hstep3
        exact hstep3
    · intro i
      have hSi := hS _ (hmem_prime i)
      have : NeZero (prime i) := ⟨(hprime_all i).ne_zero⟩
      have hgt : 2 < prime i := by
        have hMlt : M < prime i := lt_of_lt_of_le hBM hSi.2.1
        exact lt_of_lt_of_le (by decide : 2 < 2 ^ 24) (hMbig.trans hMlt.le)
      have hrhi : qr.2 ≤ (B - 1) / 2 := by
        dsimp [hi] at hr
        exact hr.2
      have hres := block_residue_le_half (B := B) (H := H) (Q := Q) (M := M)
        (p := prime i) (q := qr.1) (r := qr.2) hBpos hSi.2.1 hSi.2.2.1 hq hQH hr.1
        hrhi (hprime_all i) hgt
      have hcomm : (B * qr.1 + qr.2) % prime i = (qr.1 * B + qr.2) % prime i := by
        rw [Nat.mul_comm]
      rw [← hcomm] at hres
      dsimp [A]
      exact not_mem_upperHalf_of_mod_le (hprime_all i) hres
  have hsurvive : N < 10 * (survivors N prime A).card :=
    hten.trans_le (Nat.mul_le_mul_left _ (card_le_card hRsub))
  have hsmall : ∀ i, (prime i : ℝ) < (N : ℝ) ^ (9 / 10 : ℝ) := by
    intro i
    have hple : prime i ≤ 2 * M - 1 := by
      have hSi := hS _ (hmem_prime i)
      have hnot : ¬ (2 * M).Prime := Nat.not_prime_mul (by decide) hMne
      have hne : prime i ≠ 2 * M := by
        intro h
        exact hnot (h ▸ hSi.1)
      exact Nat.le_sub_one_of_lt (Nat.lt_of_le_of_ne hSi.2.2.2 hne)
    have hpow : prime i ^ 10 < (2 * M) ^ 10 := by
      have hlt : prime i < 2 * M :=
        lt_of_le_of_lt hple
          (Nat.sub_lt (Nat.mul_pos (by decide : 0 < 2) hMpos) (by decide : 0 < 1))
      exact Nat.pow_lt_pow_left hlt (by decide : (10 : ℕ) ≠ 0)
    have hchain : prime i ^ 10 < N ^ 9 := by
      calc
        prime i ^ 10 < (2 * M) ^ 10 := hpow
        _ = (2 ^ (64 * t + 1)) ^ 10 := by rw [h2M]
        _ < (2 ^ (72 * t + 1)) ^ 9 := pow_ten_lt_nine ht
        _ = N ^ 9 := by rw [hNpow]
    exact nat_lt_rpow_nine_tenths hNpos hchain
  refine ⟨N, prime, A, hprime_all, hmono, hsmall, hAcard, ?_⟩
  have hcast : (N : ℝ) < 10 * ((survivors N prime A).card : ℝ) := by
    exact_mod_cast hsurvive
  linarith

/-- Erdős problem 1202 has a negative answer. -/
theorem not_universalHalfResidueBound : ¬ UniversalHalfResidueBound := by
  intro hclaim
  obtain ⟨k, hk⟩ := hclaim (1 / 10) 1 (by norm_num) (by norm_num)
  by_cases hk0 : k = 0
  · subst hk0
    let p : Fin 0 → ℕ := Fin.elim0
    let A : (i : Fin 0) → Finset (ZMod (p i)) := fun i => Fin.elim0 i
    have hle := hk 1 p A (fun i => i.elim0) (fun a b _ => a.elim0)
      (fun i => i.elim0) (fun i => i.elim0)
    have hcard : (survivors 1 p A).card = 1 := by
      simp [survivors, p, A]
    rw [hcard] at hle
    norm_num at hle
  · have hkpos : 0 < k := Nat.pos_of_ne_zero hk0
    obtain ⟨n, p, A, hp, hmono, hbound, hcard, hgt⟩ := counterexample_of_k k hkpos
    have hsmall := hk n p A hp hmono ?_ hcard
    · exact not_lt_of_ge hsmall hgt
    · intro i
      have hexp : (1 : ℝ) - (10 : ℝ)⁻¹ = 9 / 10 := by norm_num
      simpa [hexp] using hbound i

end JSP001007
