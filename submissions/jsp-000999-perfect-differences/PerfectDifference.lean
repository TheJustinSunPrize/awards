import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Card
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Order.Lattice.Nat
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
A quantitative greedy completion of any finite Sidon seed to an infinite perfect
integer difference set (JSP-000999 / Erdős 1194). This implements known greedy
construction mathematics, not the open optimal-growth problem.
-/
open Finset
namespace PerfectDifference

/-- The sum formulation includes repeated summands. -/
def Sidon (A : Finset ℕ) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, ∀ e ∈ A,
    a + b = c + e → (a = c ∧ b = e) ∨ (a = e ∧ b = c)

/-- Natural differences, with zero also included for nonempty sets. -/
def differences (A : Finset ℕ) : Finset ℕ :=
  (A.product A).image (fun ab => ab.1 - ab.2)

/-- Forbidden locations for a new pair with prescribed missing difference. -/
def bad (A : Finset ℕ) (d : ℕ) : Finset ℕ :=
  ((((A.product A).product A).product (range 2)).image
    (fun t => t.1.1.1 + t.1.1.2 - t.1.2 - t.2 * d)) ∪
  (((A.product A).product (range 3)).image
    (fun t => (t.1.1 + t.1.2 - t.2 * d) / 2)) ∪
  ((A.product ((range 3).product (range 2))).image
    (fun t => t.1 + t.2.2 * d - t.2.1 * d))

/-- A missing positive difference cannot join two old elements. -/
theorem missing_pair {A : Finset ℕ} {d a b : ℕ} (hd : d ∉ differences A)
    (ha : a ∈ A) (hb : b ∈ A) : a + d ≠ b := by
  intro h
  apply hd
  refine mem_image.mpr ⟨(b,a), mem_product.mpr ⟨hb,ha⟩, ?_⟩
  dsimp
  omega

/-- Collisions between an old sum and a sum using one new element. -/
theorem avoid_one {A : Finset ℕ} {d x : ℕ} (hx : x ∉ bad A d)
    {a b c e : ℕ} (ha : a ∈ A) (hb : b ∈ A) (hc : c ∈ A) (he : e < 2) :
    x + c + e * d ≠ a + b := by
  intro h
  apply hx
  apply mem_union_left
  apply mem_union_left
  exact mem_image.mpr ⟨(((a,b),c),e),
    mem_product.mpr ⟨mem_product.mpr ⟨mem_product.mpr ⟨ha,hb⟩,hc⟩, mem_range.mpr he⟩,
    by dsimp; omega⟩

/-- Collisions between an old sum and a sum using two new elements. -/
theorem avoid_two {A : Finset ℕ} {d x : ℕ} (hx : x ∉ bad A d)
    {a b e : ℕ} (ha : a ∈ A) (hb : b ∈ A) (he : e < 3) :
    2 * x + e * d ≠ a + b := by
  intro h
  apply hx
  apply mem_union_left
  apply mem_union_right
  exact mem_image.mpr ⟨((a,b),e),
    mem_product.mpr ⟨mem_product.mpr ⟨ha,hb⟩,mem_range.mpr he⟩,
    by dsimp; omega⟩

/-- Collisions involving two new summands on one side and one on the other. -/
theorem avoid_shift {A : Finset ℕ} {d x : ℕ} (hx : x ∉ bad A d)
    {a i j : ℕ} (ha : a ∈ A) (hi : i < 3) (hj : j < 2) :
    x + i * d ≠ a + j * d := by
  intro h
  apply hx
  apply mem_union_right
  exact mem_image.mpr ⟨(a,(i,j)),mem_product.mpr
    ⟨ha,mem_product.mpr ⟨mem_range.mpr hi,mem_range.mpr hj⟩⟩,by dsimp; omega⟩

/-- Any nonforbidden pair realizes the missing difference and preserves uniqueness. -/
theorem sidon_insert_pair {A : Finset ℕ} (hA : Sidon A) {d x : ℕ}
    (hd : 0 < d) (hmissing : d ∉ differences A) (hx : x ∉ bad A d) :
    Sidon (insert x (insert (x+d) A)) := by
  have h1 (a b c : ℕ) (ha : a ∈ A) (hb : b ∈ A) (hc : c ∈ A) :
      x+c ≠ a+b ∧ x+c+d ≠ a+b := by
    constructor
    · simpa using avoid_one hx ha hb hc (e := 0) (by omega)
    · simpa using avoid_one hx ha hb hc (e := 1) (by omega)
  have h2 (a b : ℕ) (ha : a ∈ A) (hb : b ∈ A) :
      2*x ≠ a+b ∧ 2*x+d ≠ a+b ∧ 2*x+2*d ≠ a+b := by
    constructor
    · simpa using avoid_two hx ha hb (e := 0) (by omega)
    constructor
    · simpa using avoid_two hx ha hb (e := 1) (by omega)
    · exact avoid_two hx ha hb (e := 2) (by omega)
  have h3 (a : ℕ) (ha : a ∈ A) :
      x ≠ a ∧ x+d ≠ a ∧ x+2*d ≠ a ∧ x ≠ a+d := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa using avoid_shift hx ha (i := 0) (j := 0) (by omega) (by omega)
    · simpa using avoid_shift hx ha (i := 1) (j := 0) (by omega) (by omega)
    · simpa using avoid_shift hx ha (i := 2) (j := 0) (by omega) (by omega)
    · simpa using avoid_shift hx ha (i := 0) (j := 1) (by omega) (by omega)
  have hm (a b : ℕ) (ha : a ∈ A) (hb : b ∈ A) := missing_pair hmissing ha hb
  intro a ha b hb c hc e he heq
  simp only [mem_insert] at ha hb hc he
  rcases ha with ha | ha | ha <;>
    rcases hb with hb | hb | hb <;>
    rcases hc with hc | hc | hc <;>
    rcases he with he | he | he
  · omega
  · omega
  · have := h3 e he
    omega
  · omega
  · omega
  · have := h3 e he
    omega
  · have := h3 c hc
    omega
  · have := h3 c hc
    omega
  · have := h2 c e hc he
    omega
  · omega
  · omega
  · have := h3 e he
    omega
  · omega
  · omega
  · have := h3 e he
    omega
  · have := h3 c hc
    omega
  · have := h3 c hc
    omega
  · have := h2 c e hc he
    omega
  · have := h3 b hb
    omega
  · have := h3 b hb
    omega
  · have := hm b e hb he
    have := hm e b he hb
    omega
  · have := h3 b hb
    omega
  · have := h3 b hb
    omega
  · have := hm b e hb he
    have := hm e b he hb
    omega
  · have := hm b c hb hc
    have := hm c b hc hb
    omega
  · have := hm b c hb hc
    have := hm c b hc hb
    omega
  · have := h1 c e b hc he hb
    omega
  · omega
  · omega
  · have := h3 e he
    omega
  · omega
  · omega
  · have := h3 e he
    omega
  · have := h3 c hc
    omega
  · have := h3 c hc
    omega
  · have := h2 c e hc he
    omega
  · omega
  · omega
  · have := h3 e he
    omega
  · omega
  · omega
  · have := h3 e he
    omega
  · have := h3 c hc
    omega
  · have := h3 c hc
    omega
  · have := h2 c e hc he
    omega
  · have := h3 b hb
    omega
  · have := h3 b hb
    omega
  · have := hm b e hb he
    have := hm e b he hb
    omega
  · have := h3 b hb
    omega
  · have := h3 b hb
    omega
  · have := hm b e hb he
    have := hm e b he hb
    omega
  · have := hm b c hb hc
    have := hm c b hc hb
    omega
  · have := hm b c hb hc
    have := hm c b hc hb
    omega
  · have := h1 c e b hc he hb
    omega
  · have := h3 a ha
    omega
  · have := h3 a ha
    omega
  · have := hm a e ha he
    have := hm e a he ha
    omega
  · have := h3 a ha
    omega
  · have := h3 a ha
    omega
  · have := hm a e ha he
    have := hm e a he ha
    omega
  · have := hm a c ha hc
    have := hm c a hc ha
    omega
  · have := hm a c ha hc
    have := hm c a hc ha
    omega
  · have := h1 c e a hc he ha
    omega
  · have := h3 a ha
    omega
  · have := h3 a ha
    omega
  · have := hm a e ha he
    have := hm e a he ha
    omega
  · have := h3 a ha
    omega
  · have := h3 a ha
    omega
  · have := hm a e ha he
    have := hm e a he ha
    omega
  · have := hm a c ha hc
    have := hm c a hc ha
    omega
  · have := hm a c ha hc
    have := hm c a hc ha
    omega
  · have := h1 c e a hc he ha
    omega
  · have := h2 a b ha hb
    omega
  · have := h2 a b ha hb
    omega
  · have := h1 a b e ha hb he
    omega
  · have := h2 a b ha hb
    omega
  · have := h2 a b ha hb
    omega
  · have := h1 a b e ha hb he
    omega
  · have := h1 a b c ha hb hc
    omega
  · have := h1 a b c ha hb hc
    omega
  · exact hA a ha b hb c hc e he heq

/-- The finite obstruction family has cubic cardinality. -/
theorem bad_card (A : Finset ℕ) (d : ℕ) :
    (bad A d).card ≤ 2*A.card^3 + 3*A.card^2 + 6*A.card := by
  unfold bad
  calc
    _ ≤ _ := card_union_le _ _
    _ ≤ _ := Nat.add_le_add (card_union_le _ _) (card_image_le)
    _ ≤ _ := Nat.add_le_add (Nat.add_le_add card_image_le card_image_le) (le_refl _)
    _ = _ := by simp [card_product, card_range]; ring

/-- Some positive integer at most `card + 1` is outside a finite set. -/
theorem missing_small (F : Finset ℕ) : ∃ n, 0 < n ∧ n ≤ F.card+1 ∧ n ∉ F := by
  have h : F.card < (Icc 1 (F.card+1)).card := by simp
  obtain ⟨n,hn,hout⟩ := exists_mem_notMem_of_card_lt_card h
  have := mem_Icc.mp hn
  exact ⟨n,by omega,by omega,hout⟩

/-- The least positive number outside a finite set; executable, with no choice. -/
def firstMissing (F : Finset ℕ) : ℕ :=
  Nat.find (show ∃ n, 0 < n ∧ n ∉ F from
    let ⟨n,hp,_,hn⟩ := missing_small F; ⟨n,hp,hn⟩)

theorem firstMissing_spec (F : Finset ℕ) :
    0 < firstMissing F ∧ firstMissing F ∉ F := by
  unfold firstMissing
  exact Nat.find_spec (p := fun n => 0 < n ∧ n ∉ F) _

theorem firstMissing_le {F : Finset ℕ} {n : ℕ} (hn : 0 < n) (hout : n ∉ F) :
    firstMissing F ≤ n := Nat.find_min' _ ⟨hn,hout⟩

theorem firstMissing_bound (F : Finset ℕ) : firstMissing F ≤ F.card+1 := by
  obtain ⟨n,hp,hb,hn⟩ := missing_small F
  exact (firstMissing_le hp hn).trans hb

def nextDiff (A : Finset ℕ) : ℕ := firstMissing (differences A)
def nextBase (A : Finset ℕ) : ℕ := firstMissing (bad A (nextDiff A))
def extend (A : Finset ℕ) : Finset ℕ :=
  insert (nextBase A) (insert (nextBase A + nextDiff A) A)

theorem nextDiff_bound (A : Finset ℕ) : nextDiff A ≤ A.card^2+1 := by
  have hc : (differences A).card ≤ A.card^2 := by
    exact (card_image_le).trans_eq (by simp [card_product, pow_two])
  exact (firstMissing_bound _).trans (by omega)

theorem nextBase_fresh (A : Finset ℕ) :
    nextBase A ∉ A ∧ nextBase A + nextDiff A ∉ A := by
  have hx := (firstMissing_spec (bad A (nextDiff A))).2
  constructor
  · intro ha
    have := avoid_shift hx ha (i := 0) (j := 0) (by omega) (by omega)
    simp only [zero_mul, add_zero] at this
    exact this rfl
  · intro ha
    have := avoid_shift hx ha (i := 1) (j := 0) (by omega) (by omega)
    simp only [one_mul, zero_mul, add_zero] at this
    exact this rfl

theorem extend_card (A : Finset ℕ) : (extend A).card = A.card+2 := by
  have hd : 0 < nextDiff A := (firstMissing_spec _).1
  have hf := nextBase_fresh A
  have hnot : nextBase A ∉ insert (nextBase A + nextDiff A) A := by
    simp only [mem_insert, not_or]
    exact ⟨by omega,hf.1⟩
  simp only [extend, card_insert_of_notMem hnot, card_insert_of_notMem hf.2]

theorem subset_extend (A : Finset ℕ) : A ⊆ extend A := by
  intro a ha
  exact mem_insert_of_mem (mem_insert_of_mem ha)

theorem extend_sidon {A : Finset ℕ} (hA : Sidon A) : Sidon (extend A) :=
  sidon_insert_pair hA (firstMissing_spec _).1 (firstMissing_spec _).2
    (firstMissing_spec _).2

theorem new_endpoint_bound (A : Finset ℕ) :
    nextBase A + nextDiff A ≤ 2*(A.card+1)^3 := by
  have h1 := firstMissing_bound (bad A (nextDiff A))
  have h2 := bad_card A (nextDiff A)
  have h3 := nextDiff_bound A
  change nextBase A ≤ _ at h1
  nlinarith


/-- Successive finite approximations; each step adds exactly two elements. -/
def stage (seed : Finset ℕ) : ℕ → Finset ℕ
  | 0 => seed
  | n+1 => extend (stage seed n)

theorem stage_monotone (seed : Finset ℕ) : Monotone (stage seed) :=
  monotone_nat_of_le_succ (fun n => subset_extend (stage seed n))

theorem stage_card (seed : Finset ℕ) (n : ℕ) :
    (stage seed n).card = seed.card+2*n := by
  induction n with
  | zero => simp [stage]
  | succ n ih => rw [stage, extend_card, ih]; omega

theorem stage_sidon {seed : Finset ℕ} (hs : Sidon seed) (n : ℕ) :
    Sidon (stage seed n) := by
  induction n with
  | zero => exact hs
  | succ n ih => exact extend_sidon ih

theorem stage_positive {seed : Finset ℕ} (hs : ∀ a ∈ seed, 0 < a) (n : ℕ) :
    ∀ a ∈ stage seed n, 0 < a := by
  induction n with
  | zero => exact hs
  | succ n ih =>
    intro a ha
    rcases mem_insert.mp ha with rfl | ha
    · exact (firstMissing_spec _).1
    rcases mem_insert.mp ha with rfl | ha
    · have : 0 < nextBase (stage seed n) := (firstMissing_spec _).1
      omega
    · exact ih a ha

theorem differences_mono {A B : Finset ℕ} (h : A ⊆ B) :
    differences A ⊆ differences B := by
  intro d hd
  obtain ⟨⟨a,b⟩,hm,rfl⟩ := mem_image.mp hd
  exact mem_image.mpr ⟨(a,b),mem_product.mpr
    ⟨h (mem_product.mp hm).1,h (mem_product.mp hm).2⟩,rfl⟩

theorem nextDiff_represented (A : Finset ℕ) : nextDiff A ∈ differences (extend A) := by
  apply mem_image.mpr
  refine ⟨(nextBase A+nextDiff A,nextBase A),?_,?_⟩
  · exact mem_product.mpr ⟨mem_insert_of_mem (mem_insert_self _ _),mem_insert_self _ _⟩
  · dsimp; omega

/-- At stage `n`, all positive differences at most `n` are covered. -/
theorem stage_covers (seed : Finset ℕ) (n : ℕ) :
    ∀ d, 0 < d → d ≤ n → d ∈ differences (stage seed n) := by
  induction n with
  | zero => intro d hp hb; omega
  | succ n ih =>
    intro d hp hb
    by_cases hold : d ∈ differences (stage seed n)
    · exact differences_mono (subset_extend _) hold
    have hdle : nextDiff (stage seed n) ≤ d := firstMissing_le hp hold
    have hdgt : n < nextDiff (stage seed n) := by
      have hs : 0 < nextDiff (stage seed n) ∧ nextDiff (stage seed n) ∉ differences (stage seed n) := firstMissing_spec _
      by_contra h
      exact hs.2 (ih _ hs.1 (by omega))
    have heq : d = nextDiff (stage seed n) := by omega
    rw [heq]
    exact nextDiff_represented _

/-- A deliberately simple explicit cubic bound, also valid at stage zero. -/
def bound (seed : Finset ℕ) (n : ℕ) : ℕ :=
  seed.sup id + 2*(seed.card+2*n+1)^3

theorem bound_monotone (seed : Finset ℕ) : Monotone (bound seed) := by
  intro m n h
  unfold bound
  exact Nat.add_le_add_left (Nat.mul_le_mul_left 2
    (Nat.pow_le_pow_left (by omega) 3)) _

theorem stage_bound (seed : Finset ℕ) (n : ℕ) :
    ∀ a ∈ stage seed n, a ≤ bound seed n := by
  induction n with
  | zero =>
    intro a ha
    have : a ≤ seed.sup id := le_sup (f := id) ha
    unfold bound
    omega
  | succ n ih =>
    intro a ha
    have hx := new_endpoint_bound (stage seed n)
    rw [stage_card] at hx
    have hb : nextBase (stage seed n) + nextDiff (stage seed n) ≤ bound seed n := by
      unfold bound
      omega
    have hbn : bound seed n ≤ bound seed (n+1) := bound_monotone seed (by omega)
    rcases mem_insert.mp ha with rfl | ha
    · omega
    rcases mem_insert.mp ha with rfl | ha
    · omega
    · exact (ih a ha).trans hbn

/-- The union of the nested finite stages. -/
def completion (seed : Finset ℕ) : Set ℕ := {a | ∃ n, a ∈ stage seed n}

theorem seed_subset_completion (seed : Finset ℕ) : ↑seed ⊆ completion seed := by
  intro a ha
  exact ⟨0,ha⟩

theorem completion_positive {seed : Finset ℕ} (hs : ∀ a ∈ seed, 0 < a) :
    ∀ a ∈ completion seed, 0 < a := by
  rintro a ⟨n,hn⟩
  exact stage_positive hs n a hn

/-- Uniqueness of sums passes to the nested union. -/
theorem completion_sidon {seed : Finset ℕ} (hs : Sidon seed)
    {a b c e : ℕ} (ha : a ∈ completion seed) (hb : b ∈ completion seed)
    (hc : c ∈ completion seed) (he : e ∈ completion seed) (heq : a+b=c+e) :
    (a=c ∧ b=e) ∨ (a=e ∧ b=c) := by
  obtain ⟨i,hi⟩ := ha
  obtain ⟨j,hj⟩ := hb
  obtain ⟨k,hk⟩ := hc
  obtain ⟨l,hl⟩ := he
  let N := i+j+k+l
  exact stage_sidon hs N a (stage_monotone seed (show i≤N by omega) hi)
    b (stage_monotone seed (show j≤N by omega) hj)
    c (stage_monotone seed (show k≤N by omega) hk)
    e (stage_monotone seed (show l≤N by omega) hl) heq

/-- The ordinary ordered-pair representation of a positive difference. -/
def Represents (A : Set ℕ) (d : ℕ) (p : ℕ × ℕ) : Prop :=
  p.1 ∈ A ∧ p.2 ∈ A ∧ p.2 < p.1 ∧ p.1-p.2=d

def Perfect (A : Set ℕ) : Prop :=
  (∀ a ∈ A, 0<a) ∧ ∀ d, 0<d → ∃! p : ℕ × ℕ, Represents A d p

/-- Every required difference has a representation with explicitly bounded top endpoint. -/
theorem completion_representation (seed : Finset ℕ) {d : ℕ} (hd : 0<d) :
    ∃ p : ℕ × ℕ, Represents (completion seed) d p ∧ p.1 ≤ bound seed d := by
  obtain ⟨⟨a,b⟩,hm,heq⟩ := mem_image.mp (stage_covers seed d d hd (le_refl _))
  obtain ⟨ha,hb⟩ := mem_product.mp hm
  refine ⟨(a,b),⟨⟨d,ha⟩,⟨d,hb⟩,?_,heq⟩,stage_bound seed d a ha⟩
  dsimp at *
  omega

/-- The construction extends any positive finite Sidon seed to a perfect difference set. -/
theorem completion_perfect {seed : Finset ℕ} (hs : Sidon seed)
    (hp : ∀ a ∈ seed, 0<a) : Perfect (completion seed) := by
  refine ⟨completion_positive hp,?_⟩
  intro d hd
  obtain ⟨p,hr,_⟩ := completion_representation seed hd
  refine ⟨p,hr,?_⟩
  rintro ⟨a,b⟩ ⟨ha,hb,hab,hdiff⟩
  obtain ⟨hu,hv,huv,hpdiff⟩ := hr
  have heq : a+p.2=p.1+b := by dsimp at *; omega
  rcases completion_sidon hs ha hv hu hb heq with h | h
  · exact Prod.ext h.1 h.2.symm
  · omega

/-- Every representation, hence the unique one, satisfies the endpoint bound. -/
theorem completion_endpoint_bound {seed : Finset ℕ} (hs : Sidon seed)
    {d : ℕ} (hd : 0<d) {p : ℕ × ℕ} (hp : Represents (completion seed) d p) :
    p.1 ≤ bound seed d := by
  obtain ⟨q,hq,hbound⟩ := completion_representation seed hd
  obtain ⟨ha,hb,hab,heq⟩ := hp
  obtain ⟨hc,he,hce,heq'⟩ := hq
  have hsums : p.1+q.2=q.1+p.2 := by omega
  rcases completion_sidon hs ha he hc hb hsums with h | h
  · omega
  · omega

/-- Finite witnesses give an explicit cube-root counting lower bound. -/
theorem completion_count_witness (seed : Finset ℕ) (n : ℕ) :
    ∃ B : Finset ℕ, (↑B : Set ℕ) ⊆ completion seed ∧
      B.card = seed.card+2*n ∧ ∀ a ∈ B, a ≤ bound seed n := by
  exact ⟨stage seed n,fun a ha => ⟨n,ha⟩,stage_card seed n,stage_bound seed n⟩

/-- Unboundedness is explicit and does not depend on a density interpretation. -/
theorem completion_unbounded (seed : Finset ℕ) (N : ℕ) :
    ∃ a ∈ completion seed, N<a := by
  obtain ⟨⟨a,b⟩,⟨ha,_,_,heq⟩,_⟩ := completion_representation seed (d := N+1) (by omega)
  exact ⟨a,ha,by dsimp at heq; omega⟩

/-- Empty-seed existence, with the endpoint upper bound directly in terms of the difference. -/
theorem exists_perfect_cubic : ∃ A : Set ℕ, Perfect A ∧
    ∀ d, 0<d → ∀ p, Represents A d p → p.1 ≤ 2*(2*d+1)^3 := by
  refine ⟨completion ∅,completion_perfect (by simp [Sidon]) (by simp),?_⟩
  intro d hd p hp
  simpa [bound] using completion_endpoint_bound (seed := ∅) (by simp [Sidon]) hd hp


/-- The completed set is infinite (not just arbitrarily many finite approximations). -/
theorem completion_infinite (seed : Finset ℕ) : (completion seed).Infinite :=
  Set.infinite_of_forall_exists_gt (completion_unbounded seed)

/-- One statement packages seed retention, perfection, infinitude and both cubic bounds. -/
theorem finite_seed_completion {seed : Finset ℕ} (hs : Sidon seed)
    (hp : ∀ a ∈ seed, 0<a) :
    ∃ A : Set ℕ, ↑seed ⊆ A ∧ Perfect A ∧ A.Infinite ∧
      (∀ d, 0<d → ∀ p, Represents A d p → p.1 ≤ bound seed d) ∧
      (∀ n, ∃ B : Finset ℕ, (↑B : Set ℕ) ⊆ A ∧
        B.card = seed.card+2*n ∧ ∀ a ∈ B, a ≤ bound seed n) := by
  exact ⟨completion seed,seed_subset_completion seed,completion_perfect hs hp,
    completion_infinite seed,fun _ hd _ hr => completion_endpoint_bound hs hd hr,
    completion_count_witness seed⟩


end PerfectDifference
