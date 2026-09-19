import Mathlib

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-!
# JSP-000697 / Erdős–Graham–Selfridge problem B30 (erdosproblems.com #841)

For a positive integer `n`, let `t_n` be the smallest `t` such that some subset of
`{n+1, …, n+t}` has product with `n` equal to a perfect square (with `t_n = 0` when
`n` is itself a square). Erdős, Graham and Selfridge asked for estimates of `t_n`;
the example `t_6 = 6` (via `6·8·12 = 24²`) is classical, and the problem was resolved
asymptotically by Bui–Pratt–Zaharescu (2024).

This file formalizes the finite, exactly verifiable content of the problem:

* `squareProduct_zero_of_isSquare` — `t_n = 0` for square `n`.
* `not_squareProduct_of_odd_factorization` — the general obstruction: if a prime
  `p` divides `n` to an odd power, then `t_n ≥ p`.
* `jsp_000697` — the canonical example `t_6 = 6`, certified by an exhaustive
  sublist check.
* `jsp_000697_prime` — `t_p = p` for every prime `p` sandwiched in `(k², 2k²)`
  (witness `{2k², 2p} ⊆ (p, 2p]` with `p · 2k² · 2p = (2pk)²`), instantiated
  for all 23 primes `5 ≤ p ≤ 97`.
* `isLeast_squareProduct_*` — exact certified values of `t_n` for every
  non-square `n ≤ 27` and for `n ∈ {33, 34, 38, 39, 40}`, plus explicit
  upper/lower bounds for `n ∈ {28, 30, 32, 35}` (where the exhaustive
  check would enumerate ≥ 2048 sublists).

Since `Nat.sqrt` does not reduce in the kernel, exhaustive checks enumerate
sublists of `List.range'` (avoiding `Finset.powerset`'s nodup obligations) and
test squareness with the fuel-bounded binary-search root `binSqrt`, whose
correctness is proved once in `binSqrtLoop_spec`/`isSquare_iff_binSqrt`.
-/

/-- `SquareProduct n t` holds if some subset of `{n+1, …, n+t}` multiplies `n`
to a perfect square. The empty subset is allowed, matching the convention
`t_n = 0` for square `n`. -/
def SquareProduct (n t : ℕ) : Prop :=
  ∃ s ∈ (Finset.Ioc n (n + t)).powerset, IsSquare (n * s.prod id)

/-- Kernel-reducible floor square root by binary search. `binSqrtLoop m lo hi`
maintains the invariant `lo² ≤ m < hi²` and halves `hi - lo` each step, so `m + 1`
units of fuel always suffice. -/
def binSqrtLoop (m lo hi : ℕ) : ℕ → ℕ
  | 0 => lo
  | fuel + 1 =>
    if hi ≤ lo + 1 then lo
    else if (lo + hi) / 2 * ((lo + hi) / 2) ≤ m then
      binSqrtLoop m ((lo + hi) / 2) hi fuel
    else binSqrtLoop m lo ((lo + hi) / 2) fuel

/-- Floor square root computed by binary search (kernel-reducible). -/
def binSqrt (m : ℕ) : ℕ := binSqrtLoop m 0 (m + 1) (m + 1)

theorem binSqrtLoop_spec {m lo hi : ℕ} (hlo : lo * lo ≤ m) (hhi : m < hi * hi) :
    ∀ fuel, hi - lo ≤ fuel →
      binSqrtLoop m lo hi fuel * binSqrtLoop m lo hi fuel ≤ m ∧
        m < (binSqrtLoop m lo hi fuel + 1) * (binSqrtLoop m lo hi fuel + 1) := by
  intro fuel
  induction fuel generalizing lo hi with
  | zero =>
    intro hgap
    have h : hi ≤ lo := by omega
    nlinarith
  | succ fuel ih =>
    intro hgap
    simp only [binSqrtLoop]
    split
    · rename_i hle
      refine ⟨hlo, ?_⟩
      have h2 : hi * hi ≤ (lo + 1) * (lo + 1) := by nlinarith
      omega
    · rename_i hgt
      push Not at hgt
      split
      · rename_i hmid
        refine ih hmid hhi ?_
        have hm1 : lo + 1 ≤ (lo + hi) / 2 := by
          rw [Nat.le_div_iff_mul_le (by norm_num : 0 < 2)]
          omega
        omega
      · rename_i hmid
        refine ih hlo (lt_of_not_ge hmid) ?_
        have hm2 : (lo + hi) / 2 < hi := by
          rw [Nat.div_lt_iff_lt_mul (by norm_num : 0 < 2)]
          omega
        omega

theorem binSqrt_spec (m : ℕ) :
    binSqrt m * binSqrt m ≤ m ∧ m < (binSqrt m + 1) * (binSqrt m + 1) :=
  binSqrtLoop_spec (m := m) (lo := 0) (hi := m + 1) (by simp)
    (lt_of_lt_of_le (Nat.lt_succ_self m) (by nlinarith)) (m + 1) (by omega)

/-- `m` is a square iff `binSqrt m` squares back to `m`. -/
theorem isSquare_iff_binSqrt {m : ℕ} : IsSquare m ↔ binSqrt m * binSqrt m = m := by
  obtain ⟨h1, h2⟩ := binSqrt_spec m
  constructor
  · rintro ⟨r, rfl⟩
    have hb1 : binSqrt (r * r) ≤ r := by nlinarith
    have hb2 : r ≤ binSqrt (r * r) := by nlinarith
    rw [le_antisymm hb1 hb2]
  · intro h
    exact ⟨binSqrt m, h.symm⟩

/-- Enlarging the interval preserves witnesses. -/
theorem squareProduct_mono {n t u : ℕ} (h : t ≤ u) (hw : SquareProduct n t) :
    SquareProduct n u := by
  obtain ⟨s, hs, hsq⟩ := hw
  exact ⟨s, Finset.mem_powerset.mpr ((Finset.mem_powerset.mp hs).trans
    (Finset.Ioc_subset_Ioc_right (by omega))), hsq⟩

/-- If `n` is a square, the empty subset already works: `t_n = 0`. -/
theorem squareProduct_zero_of_isSquare {n : ℕ} (h : IsSquare n) :
    SquareProduct n 0 := by
  refine ⟨∅, ?_, ?_⟩
  · simp
  · simpa using h

theorem isLeast_squareProduct_zero {n : ℕ} (h : IsSquare n) :
    IsLeast {t | SquareProduct n t} 0 :=
  ⟨squareProduct_zero_of_isSquare h, fun _ _ => Nat.zero_le _⟩

/-- The general lower bound: if `p` is prime, `p ∣ n`, and `p` occurs to an odd
power in `n`, then no subset of `{n+1, …, n+t}` with `t < p` can multiply `n` to a
square — no element of that interval is divisible by `p`, so `p` still occurs to an
odd power in the product. In particular `t_n ≥ p`. -/
theorem not_squareProduct_of_odd_factorization {n t p : ℕ} (hn : 0 < n) (hp : p.Prime)
    (hpn : p ∣ n) (ht : t < p) (hodd : Odd (n.factorization p)) :
    ¬ SquareProduct n t := by
  rintro ⟨s, hs, hsq⟩
  rw [Finset.mem_powerset] at hs
  have hpi : ∀ i ∈ s, ¬ p ∣ i := by
    intro i hi hdvd
    have hmem := Finset.mem_Ioc.mp (hs hi)
    have hd : p ∣ i - n := Nat.dvd_sub hdvd hpn
    have hle : p ≤ i - n := Nat.le_of_dvd (by omega) hd
    omega
  have hprod : s.prod id ≠ 0 := by
    rw [Finset.prod_ne_zero_iff]
    intro i hi
    show i ≠ 0
    have hmem := Finset.mem_Ioc.mp (hs hi)
    omega
  have hzero : (s.prod id).factorization p = 0 := by
    rw [Nat.factorization_prod_apply (fun i hi => by
      show i ≠ 0
      have hmem := Finset.mem_Ioc.mp (hs hi)
      omega)]
    exact Finset.sum_eq_zero fun i hi => Nat.factorization_eq_zero_of_not_dvd (hpi i hi)
  have hf : (n * s.prod id).factorization p = n.factorization p := by
    rw [Nat.factorization_mul hn.ne' hprod, Finsupp.add_apply, hzero, add_zero]
  have hev := (Nat.isSquare_iff_even_factorization.mp hsq) p hp
  rw [hf] at hev
  obtain ⟨k, hk⟩ := hodd
  obtain ⟨j, hj⟩ := hev
  omega

/-- If `p` is prime, `p ∣ n`, and `p² ∤ n`, then `p` occurs exactly once in `n`. -/
theorem factorization_eq_one_of_sqfree {n p : ℕ} (hp : p.Prime) (hpn : p ∣ n)
    (hp2 : ¬ p * p ∣ n) : n.factorization p = 1 := by
  obtain ⟨m, rfl⟩ := hpn
  have hp0 : p ≠ 0 := hp.ne_zero
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact hp2 (by simp)
  have hpm : ¬ p ∣ m := fun ⟨j, hj⟩ => hp2 ⟨j, by rw [hj]; ring⟩
  rw [Nat.factorization_mul hp0 hm0, Finsupp.add_apply,
    Nat.Prime.factorization_self hp, Nat.factorization_eq_zero_of_not_dvd hpm]

/-- Every prime `p` satisfies `t_p ≥ p`. -/
theorem squareProduct_prime_lower {p : ℕ} (hp : p.Prime) :
    ∀ t ∈ {t | SquareProduct p t}, p ≤ t := by
  intro t ht
  by_contra hlt
  exact not_squareProduct_of_odd_factorization hp.pos hp dvd_rfl (lt_of_not_ge hlt)
    (by rw [Nat.Prime.factorization_self hp]; exact ⟨0, rfl⟩) ht

/-- If `k² < p < 2k²` then `{2k², 2p} ⊆ (p, 2p]` and
`p · 2k² · 2p = (2pk)²`, giving `t_p ≤ p`. -/
theorem squareProduct_prime_upper {p k : ℕ} (hp : p.Prime) (h1 : k ^ 2 < p)
    (h2 : p < 2 * k ^ 2) : SquareProduct p p := by
  have hp0 : 0 < p := hp.pos
  have hne : 2 * k ^ 2 ≠ 2 * p := by omega
  refine ⟨{2 * k ^ 2, 2 * p}, Finset.mem_powerset.mpr ?_, ?_⟩
  · intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl <;> simp only [Finset.mem_Ioc] <;> omega
  · have hprod : ({2 * k ^ 2, 2 * p} : Finset ℕ).prod id = 2 * k ^ 2 * (2 * p) := by
      rw [Finset.prod_pair hne]; rfl
    rw [hprod]
    exact ⟨2 * p * k, by ring⟩

/-- `t_p = p` whenever `k² < p < 2k²`: the witness `{2k², 2p} ⊆ (p, 2p]` gives
`p · 2k² · 2p = (2pk)²`, and the obstruction bound `t_p ≥ p` matches. Every
prime `5 ≤ p ≤ 97` satisfies the sandwich for some `k ≤ 7` (instances below). -/
theorem jsp_000697_prime {p k : ℕ} (hp : p.Prime) (h1 : k ^ 2 < p)
    (h2 : p < 2 * k ^ 2) : IsLeast {t | SquareProduct p t} p :=
  ⟨squareProduct_prime_upper hp h1 h2, squareProduct_prime_lower hp⟩

/-- Every subset of `Ioc n (n + u)` is realized by a sublist of
`List.range' (n + 1) u` with the same product. -/
theorem exists_sublist_prod {n u : ℕ} {s : Finset ℕ}
    (hs : s ⊆ Finset.Ioc n (n + u)) :
    ∃ l ∈ (List.range' (n + 1) u).sublists, l.prod = s.prod id := by
  have hsub : s.val ⊆ (List.range' (n + 1) u : Multiset ℕ) := by
    intro x hx
    have hI := Finset.mem_Ioc.mp (hs hx)
    rw [Multiset.mem_coe, List.mem_range'_1]
    exact ⟨by omega, by omega⟩
  have hle : s.val ≤ (List.range' (n + 1) u : Multiset ℕ) :=
    Finset.val_le_iff_val_subset.mpr hsub
  have hl₀ : (s.val.toList : Multiset ℕ) = s.val := Multiset.coe_toList _
  rw [← hl₀, Multiset.coe_le] at hle
  obtain ⟨l, hperm, hsublist⟩ := hle
  refine ⟨l, List.mem_sublists.mpr hsublist, ?_⟩
  calc l.prod = s.val.toList.prod := hperm.prod_eq
    _ = s.val.prod := by rw [← Multiset.prod_coe, hl₀]
    _ = s.prod id := Finset.prod_val s

/-- Exactness certificate from an explicit subset witness and an exhaustive
kernel check that no sublist of the shorter interval works. -/
theorem isLeast_of_witness {n t : ℕ} (s : Finset ℕ)
    (hmem : s ∈ (Finset.Ioc n (n + t)).powerset) (r : ℕ) (hr : n * s.prod id = r * r)
    (hchk : ∀ l ∈ (List.range' (n + 1) (t - 1)).sublists,
      binSqrt (n * l.prod) * binSqrt (n * l.prod) ≠ n * l.prod) :
    IsLeast {u | SquareProduct n u} t := by
  refine ⟨⟨s, hmem, r, hr⟩, fun u hu => ?_⟩
  by_contra hlt
  obtain ⟨s', hs', hsq'⟩ := squareProduct_mono (by omega : u ≤ t - 1) hu
  rw [Finset.mem_powerset] at hs'
  obtain ⟨l, hlmem, hlprod⟩ := exists_sublist_prod hs'
  rw [← hlprod] at hsq'
  exact hchk l hlmem (isSquare_iff_binSqrt.mp hsq')

/-- Exactness certificate when the witness attains the obstruction bound:
if `p` divides `n` exactly once then `t_n ≥ p`, so a witness subset of `(n, n+p]`
proves `t_n = p`. -/
theorem isLeast_of_prime_factor {n p : ℕ} (s : Finset ℕ) (hp : p.Prime)
    (hpn : p ∣ n) (hp2 : ¬ p * p ∣ n)
    (hmem : s ∈ (Finset.Ioc n (n + p)).powerset) (r : ℕ)
    (hr : n * s.prod id = r * r) : IsLeast {u | SquareProduct n u} p := by
  have hn : 0 < n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h; exact absurd (dvd_zero _) hp2
    · exact h
  refine ⟨⟨s, hmem, r, hr⟩, fun u hu => ?_⟩
  by_contra hlt
  exact not_squareProduct_of_odd_factorization hn hp hpn (lt_of_not_ge hlt)
    (by rw [factorization_eq_one_of_sqfree hp hpn hp2]; exact ⟨0, rfl⟩) hu

/-- The canonical Erdős–Graham–Selfridge example: `t_6 = 6`, witnessed by
`{8, 12} ⊆ {7, …, 12}` with `6·8·12 = 576 = 24²`; no shorter interval works. -/
theorem jsp_000697 : IsLeast {t | SquareProduct 6 t} 6 :=
  isLeast_of_witness {8, 12} (Finset.mem_powerset.mpr (by decide)) 24 (by decide) (by decide)

/-- `t_2 = 4`, witnessed by `{3, 6}` with `2·3·6 = 36 = 6²`. -/
theorem isLeast_squareProduct_2 : IsLeast {t | SquareProduct 2 t} 4 :=
  isLeast_of_witness {3, 6} (Finset.mem_powerset.mpr (by decide)) 6 (by decide) (by decide)

/-- `t_3 = 5`, witnessed by `{6, 8}` with `3·6·8 = 144 = 12²`. -/
theorem isLeast_squareProduct_3 : IsLeast {t | SquareProduct 3 t} 5 :=
  isLeast_of_witness {6, 8} (Finset.mem_powerset.mpr (by decide)) 12 (by decide) (by decide)

/-- `t_8 = 7`, witnessed by `{10, 12, 15}` with `8·10·12·15 = 14400 = 120²`. -/
theorem isLeast_squareProduct_8 : IsLeast {t | SquareProduct 8 t} 7 :=
  isLeast_of_witness {10, 12, 15} (Finset.mem_powerset.mpr (by decide)) 120 (by decide) (by decide)

/-- `t_10 = 8`, witnessed by `{12, 15, 18}` with `10·12·15·18 = 32400 = 180²`. -/
theorem isLeast_squareProduct_10 : IsLeast {t | SquareProduct 10 t} 8 :=
  isLeast_of_witness {12, 15, 18} (Finset.mem_powerset.mpr (by decide)) 180 (by decide) (by decide)

/-- `t_12 = 8`, witnessed by `{15, 20}` with `12·15·20 = 3600 = 60²`. -/
theorem isLeast_squareProduct_12 : IsLeast {t | SquareProduct 12 t} 8 :=
  isLeast_of_witness {15, 20} (Finset.mem_powerset.mpr (by decide)) 60 (by decide) (by decide)

/-- `t_14 = 7` attains the obstruction bound (`7 ∥ 14`), witnessed by
`{15, 18, 20, 21}` with `14·15·18·20·21 = 1587600 = 1260²`. -/
theorem isLeast_squareProduct_14 : IsLeast {t | SquareProduct 14 t} 7 :=
  isLeast_of_prime_factor {15, 18, 20, 21} (by norm_num) (by decide) (by decide)
    (Finset.mem_powerset.mpr (by decide)) 1260 (by decide)

/-- `t_15 = 9`, witnessed by `{18, 20, 24}` with `15·18·20·24 = 129600 = 360²`. -/
theorem isLeast_squareProduct_15 : IsLeast {t | SquareProduct 15 t} 9 :=
  isLeast_of_witness {18, 20, 24} (Finset.mem_powerset.mpr (by decide)) 360 (by decide) (by decide)

/-- `t_18 = 9`, witnessed by `{24, 27}` with `18·24·27 = 11664 = 108²`. -/
theorem isLeast_squareProduct_18 : IsLeast {t | SquareProduct 18 t} 9 :=
  isLeast_of_witness {24, 27} (Finset.mem_powerset.mpr (by decide)) 108 (by decide) (by decide)

/-- `t_20 = 10`, witnessed by `{24, 30}` with `20·24·30 = 14400 = 120²`. -/
theorem isLeast_squareProduct_20 : IsLeast {t | SquareProduct 20 t} 10 :=
  isLeast_of_witness {24, 30} (Finset.mem_powerset.mpr (by decide)) 120 (by decide) (by decide)

/-- `t_21 = 7` attains the obstruction bound (`7 ∥ 21`), witnessed by `{27, 28}`
with `21·27·28 = 15876 = 126²`. -/
theorem isLeast_squareProduct_21 : IsLeast {t | SquareProduct 21 t} 7 :=
  isLeast_of_prime_factor {27, 28} (by norm_num) (by decide) (by decide)
    (Finset.mem_powerset.mpr (by decide)) 126 (by decide)

/-- `t_22 = 11` attains the obstruction bound (`11 ∥ 22`), witnessed by `{24, 33}`
with `22·24·33 = 17424 = 132²`. -/
theorem isLeast_squareProduct_22 : IsLeast {t | SquareProduct 22 t} 11 :=
  isLeast_of_prime_factor {24, 33} (by norm_num) (by decide) (by decide)
    (Finset.mem_powerset.mpr (by decide)) 132 (by decide)

/-- `t_24 = 8`, witnessed by `{27, 32}` with `24·27·32 = 20736 = 144²`. -/
theorem isLeast_squareProduct_24 : IsLeast {t | SquareProduct 24 t} 8 :=
  isLeast_of_witness {27, 32} (Finset.mem_powerset.mpr (by decide)) 144 (by decide) (by decide)

/-- `t_26 = 13` attains the obstruction bound (`13 ∥ 26`), witnessed by
`{27, 32, 39}` with `26·27·32·39 = 876096 = 936²`. -/
theorem isLeast_squareProduct_26 : IsLeast {t | SquareProduct 26 t} 13 :=
  isLeast_of_prime_factor {27, 32, 39} (by norm_num) (by decide) (by decide)
    (Finset.mem_powerset.mpr (by decide)) 936 (by decide)

/-- `t_27 = 8`, witnessed by `{28, 30, 32, 35}` with `27·28·30·32·35 = 25401600 = 5040²`. -/
theorem isLeast_squareProduct_27 : IsLeast {t | SquareProduct 27 t} 8 :=
  isLeast_of_witness {28, 30, 32, 35} (Finset.mem_powerset.mpr (by decide)) 5040 (by decide) (by decide)

/-- For `n = 28` the obstruction bound (`7 ∥ 28`) gives `t_28 ≥ 7`, while the
witness `{32, 35, 40}` with `28·32·35·40 = 1254400 = 1120²` gives `t_28 ≤ 12`.
(The exact value `t_28 = 12` is left uncertified: the exhaustive check would
enumerate 2048 sublists.) -/
theorem squareProduct_28_lower {t : ℕ} (ht : t < 7) : ¬ SquareProduct 28 t := by
  have h1 : (28 : ℕ).factorization 7 = 1 :=
    factorization_eq_one_of_sqfree (by norm_num) (by norm_num) (by norm_num)
  exact not_squareProduct_of_odd_factorization (by norm_num) (by norm_num)
    (by norm_num) ht (by rw [h1]; exact ⟨0, rfl⟩)

theorem squareProduct_28_upper : SquareProduct 28 12 :=
  ⟨{32, 35, 40}, Finset.mem_powerset.mpr (by decide), 1120, by decide⟩

/-- For `n = 30` the obstruction bound (`5 ∥ 30`) gives `t_30 ≥ 5`, while the
witness `{35, 42}` with `30·35·42 = 44100 = 210²` gives `t_30 ≤ 12`.
(The exact value `t_30 = 12` is left uncertified: the exhaustive check would
enumerate 2048 sublists.) -/
theorem squareProduct_30_lower {t : ℕ} (ht : t < 5) : ¬ SquareProduct 30 t := by
  have h1 : (30 : ℕ).factorization 5 = 1 :=
    factorization_eq_one_of_sqfree (by norm_num) (by norm_num) (by norm_num)
  exact not_squareProduct_of_odd_factorization (by norm_num) (by norm_num)
    (by norm_num) ht (by rw [h1]; exact ⟨0, rfl⟩)

theorem squareProduct_30_upper : SquareProduct 30 12 :=
  ⟨{35, 42}, Finset.mem_powerset.mpr (by decide), 210, by decide⟩

/-- `t_33 = 11` attains the obstruction bound (`11 ∥ 33`), witnessed by
`{35, 40, 42, 44}` with `33·35·40·42·44 = 85377600 = 9240²`. -/
theorem isLeast_squareProduct_33 : IsLeast {t | SquareProduct 33 t} 11 :=
  isLeast_of_prime_factor {35, 40, 42, 44} (by norm_num) (by decide) (by decide)
    (Finset.mem_powerset.mpr (by decide)) 9240 (by decide)

/-- `t_34 = 17` attains the obstruction bound (`17 ∥ 34`), witnessed by
`{35, 42, 45, 51}` with `34·35·42·45·51 = 114704100 = 10710²`. -/
theorem isLeast_squareProduct_34 : IsLeast {t | SquareProduct 34 t} 17 :=
  isLeast_of_prime_factor {35, 42, 45, 51} (by norm_num) (by decide) (by decide)
    (Finset.mem_powerset.mpr (by decide)) 10710 (by decide)

/-- For `n = 32` the obstruction bound (`2 ∥ 32`, as `32 = 2⁵`) gives `t_32 ≥ 2`,
while the witness `{40, 45}` with `32·40·45 = 57600 = 240²` gives `t_32 ≤ 13`.
(The exact value `t_32 = 13` is left uncertified: the exhaustive check would
enumerate 4096 sublists.) -/
theorem squareProduct_32_lower {t : ℕ} (ht : t < 2) : ¬ SquareProduct 32 t := by
  have h1 : (32 : ℕ).factorization 2 = 5 :=
    Nat.factorization_pow_self (p := 2) (n := 5) (by norm_num)
  exact not_squareProduct_of_odd_factorization (by norm_num) (by norm_num)
    (by norm_num) ht (by rw [h1]; exact ⟨2, rfl⟩)

theorem squareProduct_32_upper : SquareProduct 32 13 :=
  ⟨{40, 45}, Finset.mem_powerset.mpr (by decide), 240, by decide⟩

/-- For `n = 35` the obstruction bound (`7 ∥ 35`) gives `t_35 ≥ 7`, while the
witness `{40, 42, 48}` with `35·40·42·48 = 2822400 = 1680²` gives `t_35 ≤ 13`.
(The exact value `t_35 = 13` is left uncertified: the exhaustive check would
enumerate 4096 sublists.) -/
theorem squareProduct_35_lower {t : ℕ} (ht : t < 7) : ¬ SquareProduct 35 t := by
  have h1 : (35 : ℕ).factorization 7 = 1 :=
    factorization_eq_one_of_sqfree (by norm_num) (by norm_num) (by norm_num)
  exact not_squareProduct_of_odd_factorization (by norm_num) (by norm_num)
    (by norm_num) ht (by rw [h1]; exact ⟨0, rfl⟩)

theorem squareProduct_35_upper : SquareProduct 35 13 :=
  ⟨{40, 42, 48}, Finset.mem_powerset.mpr (by decide), 1680, by decide⟩

/-- `t_38 = 19` attains the obstruction bound (`19 ∥ 38`), witnessed by
`{40, 45, 48, 57}` with `38·40·45·48·57 = 187142400 = 13680²`. -/
theorem isLeast_squareProduct_38 : IsLeast {t | SquareProduct 38 t} 19 :=
  isLeast_of_prime_factor {40, 45, 48, 57} (by norm_num) (by decide) (by decide)
    (Finset.mem_powerset.mpr (by decide)) 13680 (by decide)

/-- `t_39 = 13` attains the obstruction bound (`13 ∥ 39`), witnessed by `{48, 52}`
with `39·48·52 = 97344 = 312²`. -/
theorem isLeast_squareProduct_39 : IsLeast {t | SquareProduct 39 t} 13 :=
  isLeast_of_prime_factor {48, 52} (by norm_num) (by decide) (by decide)
    (Finset.mem_powerset.mpr (by decide)) 312 (by decide)

/-- `t_40 = 10`, witnessed by `{45, 50}` with `40·45·50 = 90000 = 300²`. -/
theorem isLeast_squareProduct_40 : IsLeast {t | SquareProduct 40 t} 10 :=
  isLeast_of_witness {45, 50} (Finset.mem_powerset.mpr (by decide)) 300 (by decide) (by decide)

/-! Every prime `5 ≤ p ≤ 97` is sandwiched in `(k², 2k²)` for some `k ≤ 7`,
so `t_p = p` for all of them via `jsp_000697_prime`. -/

theorem isLeast_squareProduct_5 : IsLeast {t | SquareProduct 5 t} 5 :=
  jsp_000697_prime (k := 2) (by norm_num) (by norm_num) (by norm_num)
theorem isLeast_squareProduct_7 : IsLeast {t | SquareProduct 7 t} 7 :=
  jsp_000697_prime (k := 2) (by norm_num) (by norm_num) (by norm_num)
theorem isLeast_squareProduct_11 : IsLeast {t | SquareProduct 11 t} 11 :=
  jsp_000697_prime (k := 3) (by norm_num) (by norm_num) (by norm_num)
theorem isLeast_squareProduct_13 : IsLeast {t | SquareProduct 13 t} 13 :=
  jsp_000697_prime (k := 3) (by norm_num) (by norm_num) (by norm_num)
theorem isLeast_squareProduct_17 : IsLeast {t | SquareProduct 17 t} 17 :=
  jsp_000697_prime (k := 3) (by norm_num) (by norm_num) (by norm_num)
theorem isLeast_squareProduct_19 : IsLeast {t | SquareProduct 19 t} 19 :=
  jsp_000697_prime (k := 4) (by norm_num) (by norm_num) (by norm_num)
theorem isLeast_squareProduct_23 : IsLeast {t | SquareProduct 23 t} 23 :=
  jsp_000697_prime (k := 4) (by norm_num) (by norm_num) (by norm_num)
theorem isLeast_squareProduct_29 : IsLeast {t | SquareProduct 29 t} 29 :=
  jsp_000697_prime (k := 4) (by norm_num) (by norm_num) (by norm_num)
theorem isLeast_squareProduct_31 : IsLeast {t | SquareProduct 31 t} 31 :=
  jsp_000697_prime (k := 4) (by norm_num) (by norm_num) (by norm_num)
theorem isLeast_squareProduct_37 : IsLeast {t | SquareProduct 37 t} 37 :=
  jsp_000697_prime (k := 5) (by norm_num) (by norm_num) (by norm_num)
theorem isLeast_squareProduct_41 : IsLeast {t | SquareProduct 41 t} 41 :=
  jsp_000697_prime (k := 5) (by norm_num) (by norm_num) (by norm_num)
theorem isLeast_squareProduct_43 : IsLeast {t | SquareProduct 43 t} 43 :=
  jsp_000697_prime (k := 5) (by norm_num) (by norm_num) (by norm_num)
theorem isLeast_squareProduct_47 : IsLeast {t | SquareProduct 47 t} 47 :=
  jsp_000697_prime (k := 5) (by norm_num) (by norm_num) (by norm_num)
theorem isLeast_squareProduct_53 : IsLeast {t | SquareProduct 53 t} 53 :=
  jsp_000697_prime (k := 6) (by norm_num) (by norm_num) (by norm_num)
theorem isLeast_squareProduct_59 : IsLeast {t | SquareProduct 59 t} 59 :=
  jsp_000697_prime (k := 6) (by norm_num) (by norm_num) (by norm_num)
theorem isLeast_squareProduct_61 : IsLeast {t | SquareProduct 61 t} 61 :=
  jsp_000697_prime (k := 6) (by norm_num) (by norm_num) (by norm_num)
theorem isLeast_squareProduct_67 : IsLeast {t | SquareProduct 67 t} 67 :=
  jsp_000697_prime (k := 6) (by norm_num) (by norm_num) (by norm_num)
theorem isLeast_squareProduct_71 : IsLeast {t | SquareProduct 71 t} 71 :=
  jsp_000697_prime (k := 6) (by norm_num) (by norm_num) (by norm_num)
theorem isLeast_squareProduct_73 : IsLeast {t | SquareProduct 73 t} 73 :=
  jsp_000697_prime (k := 7) (by norm_num) (by norm_num) (by norm_num)
theorem isLeast_squareProduct_79 : IsLeast {t | SquareProduct 79 t} 79 :=
  jsp_000697_prime (k := 7) (by norm_num) (by norm_num) (by norm_num)
theorem isLeast_squareProduct_83 : IsLeast {t | SquareProduct 83 t} 83 :=
  jsp_000697_prime (k := 7) (by norm_num) (by norm_num) (by norm_num)
theorem isLeast_squareProduct_89 : IsLeast {t | SquareProduct 89 t} 89 :=
  jsp_000697_prime (k := 7) (by norm_num) (by norm_num) (by norm_num)
theorem isLeast_squareProduct_97 : IsLeast {t | SquareProduct 97 t} 97 :=
  jsp_000697_prime (k := 7) (by norm_num) (by norm_num) (by norm_num)

#print axioms jsp_000697
#print axioms jsp_000697_prime
#print axioms isLeast_squareProduct_40
