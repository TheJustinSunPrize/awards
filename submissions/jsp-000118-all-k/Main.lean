import Mathlib.Basic.Real.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.List.FinRange
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

namespace JSP000118

noncomputable section

abbrev Point := ℝ × ℝ
structure Square where
  x : ℝ
  y : ℝ
  u : ℝ
  v : ℝ
  side : ℝ

def Square.point (S : Square) (a b : ℝ) : Point :=
  (S.x + a * S.u - b * S.v, S.y + a * S.v + b * S.u)
def Square.interior (S : Square) : Set Point :=
  {p | ∃ a b, |a| < S.side / 2 ∧ |b| < S.side / 2 ∧ p = S.point a b}
def Square.radius (S : Square) (w : Point) : ℝ :=
  S.side / 2 * (|w.1 * S.u + w.2 * S.v| + |-w.1 * S.v + w.2 * S.u|)
def Square.Fits (L : ℝ) (S : Square) : Prop :=
  0 < S.side ∧ S.u ^ 2 + S.v ^ 2 = 1 ∧
  S.radius (1,0) ≤ S.x ∧ S.x + S.radius (1,0) ≤ L ∧
  S.radius (0,1) ≤ S.y ∧ S.y + S.radius (0,1) ≤ L
def Separated (S T : Square) : Prop :=
  ∃ w : Point, w ≠ (0,0) ∧ S.radius w + T.radius w ≤
    |w.1 * (T.x - S.x) + w.2 * (T.y - S.y)|
def Packing (L : ℝ) (P : List Square) : Prop :=
  (∀ S ∈ P, S.Fits L) ∧ P.Pairwise Separated

def total (P : List Square) : ℝ := (P.map Square.side).sum

private theorem linear_strict (A B t a b : ℝ) (ha : |a| < t) (hb : |b| < t)
    (hne : A ≠ 0 ∨ B ≠ 0) : |a * A + b * B| < t * (|A| + |B|) := by
  have hA := abs_nonneg A
  have hB := abs_nonneg B
  have h : |a| * |A| + |b| * |B| < t * |A| + t * |B| := by
    rcases hne with hne | hne
    · exact add_lt_add_of_lt_of_le (mul_lt_mul_of_pos_right ha (abs_pos.mpr hne))
        (mul_le_mul_of_nonneg_right hb.le hB)
    · exact add_lt_add_of_le_of_lt (mul_le_mul_of_nonneg_right ha.le hA)
        (mul_lt_mul_of_pos_right hb (abs_pos.mpr hne))
  calc
    |a * A + b * B| ≤ |a| * |A| + |b| * |B| := by simpa [abs_mul] using abs_add_le (a*A) (b*B)
    _ < t * (|A| + |B|) := by nlinarith

private theorem projection_strict (S : Square) (hunit : S.u^2 + S.v^2 = 1)
    (w : Point) (hw : w ≠ (0,0)) {p : Point} (hp : p ∈ S.interior) :
    |w.1 * (p.1-S.x) + w.2 * (p.2-S.y)| < S.radius w := by
  obtain ⟨a,b,ha,hb,rfl⟩ := hp
  have hne : w.1*S.u+w.2*S.v ≠ 0 ∨ -w.1*S.v+w.2*S.u ≠ 0 := by
    by_contra h
    push Not at h
    have hid : (w.1*S.u+w.2*S.v)^2 + (-w.1*S.v+w.2*S.u)^2 =
        (w.1^2+w.2^2)*(S.u^2+S.v^2) := by ring
    rw [h.1,h.2,hunit] at hid
    have hx : w.1 = 0 := by nlinarith [sq_nonneg w.2]
    have hy : w.2 = 0 := by nlinarith [sq_nonneg w.1]
    exact hw (Prod.ext hx hy)
  dsimp [Square.point,Square.radius]
  convert linear_strict _ _ _ a b ha hb hne using 1
  congr 1
  ring

theorem separated_disjoint {S T : Square} (hs : S.u^2+S.v^2=1)
    (ht : T.u^2+T.v^2=1) (h : Separated S T) : Disjoint S.interior T.interior := by
  obtain ⟨w,hw,hsep⟩ := h
  rw [Set.disjoint_left]
  intro p hp hq
  have hp' := projection_strict S hs w hw hp
  have hq' := projection_strict T ht w hw hq
  have heq : w.1*(T.x-S.x)+w.2*(T.y-S.y) =
      (w.1*(p.1-S.x)+w.2*(p.2-S.y)) - (w.1*(p.1-T.x)+w.2*(p.2-T.y)) := by ring
  have hh := abs_add_le (w.1*(p.1-S.x)+w.2*(p.2-S.y))
    (-(w.1*(p.1-T.x)+w.2*(p.2-T.y)))
  simp only [← sub_eq_add_neg,abs_neg] at hh
  rw [←heq] at hh
  linarith


def axis (x y s : ℝ) : Square := ⟨x+s/2,y+s/2,1,0,s⟩

-- The rational seed is the Raj Singh configuration linked by the public Lean source.
private def a : ℝ := 851228/1048735
private def C : ℝ := 1073566/1048735
private def b : ℝ := 2-a
private def D : ℝ := 2-C
private def E : ℝ := 2*a+C-2
private def h : ℝ := E/(49/41)
private def seed : Fin 17 → Square := ![
  axis 0 0 1, axis 0 1 1, axis 0 2 1, axis 0 3 1,
  axis 1 0 1, axis 1 1 1, axis 1 2 1, axis 1 3 1,
  axis 2 0 a, axis 2 a a, axis 2 (2*a) a,
  axis (2+a) 0 b, axis (2+a) b b,
  axis 2 (4-C) C, axis (2+C) (4-D) D, axis (4-E) (2*b) E,
  ⟨4-3*E/2,2*b+E/2,40/41,9/41,h⟩]

private theorem seed_fits (i : Fin 17) : (seed i).Fits 4 := by
  fin_cases i <;> norm_num [seed,axis,Square.Fits,Square.radius,a,b,C,D,E,h]

set_option maxHeartbeats 4000000 in
private theorem seed_separated (i j : Fin 17) (hij : i < j) : Separated (seed i) (seed j) := by
  fin_cases i <;> fin_cases j <;> norm_num at hij
  all_goals solve
    | (refine ⟨(1,0), ?_, ?_⟩ <;> norm_num [seed,axis,Square.radius,a,b,C,D,E,h])
    | (refine ⟨(0,1), ?_, ?_⟩ <;> norm_num [seed,axis,Square.radius,a,b,C,D,E,h])
    | (refine ⟨(40/41,9/41), ?_, ?_⟩ <;> norm_num [seed,axis,Square.radius,a,b,C,D,E,h])
    | (refine ⟨(-9/41,40/41), ?_, ?_⟩ <;> norm_num [seed,axis,Square.radius,a,b,C,D,E,h])

private def seedList : List Square := (List.finRange 17).map seed
private theorem seed_packing : Packing 4 seedList := by
  constructor
  · intro S hS
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hS
    exact seed_fits i
  · rw [seedList,List.pairwise_map]
    exact (List.pairwise_lt_finRange 17).imp (fun {i j} hij => seed_separated i j hij)
private theorem seed_length : seedList.length = 17 := by simp [seedList]
private theorem seed_total : 16 < total seedList := by
  norm_num [total,seedList,List.finRange,seed,axis,a,b,C,D,E,h]

private def row (k : ℕ) : List Square :=
  (List.range (k+1)).map (fun i : ℕ => axis i k 1)
private def column (k : ℕ) : List Square :=
  (List.range k).map (fun i : ℕ => axis k i 1)
private def extend (k : ℕ) (P : List Square) := P ++ row k ++ column k

private theorem axis_fits {x y L : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hxl : x+1 ≤ L) (hyl : y+1 ≤ L) : (axis x y 1).Fits L := by
  norm_num [axis,Square.Fits,Square.radius]
  exact ⟨hx,by linarith,hy,by linarith⟩

private theorem axis_separated_x {S T : Square}
    (h : S.x + S.radius (1,0) ≤ T.x - T.radius (1,0)) : Separated S T := by
  refine ⟨(1,0), by norm_num, ?_⟩
  simp only [one_mul,zero_mul,add_zero]
  exact le_trans (by linarith) (le_abs_self _)
private theorem axis_separated_y {S T : Square}
    (h : S.y + S.radius (0,1) ≤ T.y - T.radius (0,1)) : Separated S T := by
  refine ⟨(0,1), by norm_num, ?_⟩
  simp only [one_mul,zero_mul,zero_add]
  exact le_trans (by linarith) (le_abs_self _)

private theorem extend_packing (k : ℕ) (P : List Square) (hp : Packing k P) :
    Packing (k+1) (extend k P) := by
  have oldrow : ∀ S ∈ P, ∀ T ∈ row k, Separated S T := by
    intro S hs T ht
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp ht
    apply axis_separated_y
    have hf := (hp.1 S hs).2.2.2.2.2
    norm_num [axis,Square.radius] at hf ⊢
    linarith
  have oldcol : ∀ S ∈ P, ∀ T ∈ column k, Separated S T := by
    intro S hs T ht
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp ht
    apply axis_separated_x
    have hf := (hp.1 S hs).2.2.2.1
    norm_num [axis,Square.radius] at hf ⊢
    linarith
  have rowcol : ∀ S ∈ row k, ∀ T ∈ column k, Separated S T := by
    intro S hs T ht
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hs
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp ht
    have hrev : Separated (axis k j 1) (axis i k 1) := by
      apply axis_separated_y
      have hj' : (j : ℝ)+1 ≤ k := by exact_mod_cast (Nat.succ_le_of_lt (List.mem_range.mp hj))
      norm_num [axis,Square.radius]; linarith
    obtain ⟨w,hw,hsep⟩ := hrev
    refine ⟨w,hw,?_⟩
    have heq : w.1*((axis k j 1).x-(axis i k 1).x)+
        w.2*((axis k j 1).y-(axis i k 1).y) =
        -(w.1*((axis i k 1).x-(axis k j 1).x)+
          w.2*((axis i k 1).y-(axis k j 1).y)) := by ring
    rw [heq,abs_neg]
    linarith
  constructor
  · intro S hs
    simp only [extend,List.mem_append] at hs
    rcases hs with (hs | hs) | hs
    · obtain ⟨hpos,hunit,hx,hxl,hy,hyl⟩ := hp.1 S hs
      exact ⟨hpos,hunit,hx,by linarith,hy,by linarith⟩
    · obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hs
      apply axis_fits (by positivity) (by positivity)
      · exact_mod_cast (Nat.succ_le_of_lt (List.mem_range.mp hi))
      · simp
    · obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hs
      apply axis_fits (by positivity) (by positivity)
      · simp
      · have : (i : ℝ)+1 ≤ k := by exact_mod_cast (Nat.succ_le_of_lt (List.mem_range.mp hi))
        linarith
  · simp only [extend,List.pairwise_append]
    refine ⟨⟨hp.2, ?_, oldrow⟩, ?_, ?_⟩
    · rw [row,List.pairwise_map]
      apply List.pairwise_lt_range.imp
      intro i j hij
      apply axis_separated_x
      have : (i : ℝ)+1 ≤ j := by exact_mod_cast (Nat.succ_le_of_lt hij)
      norm_num [axis,Square.radius]; linarith
    · rw [column,List.pairwise_map]
      apply List.pairwise_lt_range.imp
      intro i j hij
      apply axis_separated_y
      have : (i : ℝ)+1 ≤ j := by exact_mod_cast (Nat.succ_le_of_lt hij)
      norm_num [axis,Square.radius]; linarith
    · intro S hs T ht
      rcases List.mem_append.mp hs with hs | hs
      · exact oldcol S hs T ht
      · exact rowcol S hs T ht

private theorem extend_length (k : ℕ) (P : List Square) :
    (extend k P).length = P.length+2*k+1 := by simp [extend,row,column]; omega
private theorem extend_total (k : ℕ) (P : List Square) :
    total (extend k P) = total P + 2*k+1 := by
  simp [extend,total,row,column,List.map_map,Function.comp_def,axis]
  ring

/-- Explicitly constructed counterexamples in every container size at least four. -/
theorem all_sizes (k : ℕ) (hk : 4 ≤ k) :
    ∃ P : List Square, Packing k P ∧ P.length = k^2+1 ∧ (k : ℝ)^2 < total P := by
  induction k,hk using Nat.le_induction with
  | base => exact ⟨seedList,seed_packing,by norm_num [seed_length],by norm_num; exact seed_total⟩
  | succ k hk ih =>
    obtain ⟨P,hp,hlen,htotal⟩ := ih
    refine ⟨extend k P,by simpa using extend_packing k P hp,?_,?_⟩
    · rw [extend_length,hlen]; ring
    · rw [extend_total]; push_cast; nlinarith

def Square.scale (S : Square) (r : ℝ) : Square := ⟨r*S.x,r*S.y,S.u,S.v,r*S.side⟩
private theorem radius_scale (S : Square) (r : ℝ) (w : Point) :
    (S.scale r).radius w = r*S.radius w := by simp [Square.scale,Square.radius]; ring
private theorem fits_scale {L r : ℝ} (hr : 0 < r) {S : Square} (hf : S.Fits L) :
    (S.scale r).Fits (r*L) := by
  obtain ⟨hs,hu,hx,hxl,hy,hyl⟩ := hf
  refine ⟨mul_pos hr hs,hu,?_,?_,?_,?_⟩
  · change (S.scale r).radius (1,0) ≤ r*S.x
    rw [radius_scale]; exact mul_le_mul_of_nonneg_left hx hr.le
  · change r*S.x+(S.scale r).radius (1,0) ≤ r*L
    rw [radius_scale,←mul_add]; exact mul_le_mul_of_nonneg_left hxl hr.le
  · change (S.scale r).radius (0,1) ≤ r*S.y
    rw [radius_scale]; exact mul_le_mul_of_nonneg_left hy hr.le
  · change r*S.y+(S.scale r).radius (0,1) ≤ r*L
    rw [radius_scale,←mul_add]; exact mul_le_mul_of_nonneg_left hyl hr.le
private theorem separated_scale {r : ℝ} (hr : 0 < r) {S T : Square} (h : Separated S T) :
    Separated (S.scale r) (T.scale r) := by
  obtain ⟨w,hw,hsep⟩ := h
  refine ⟨w,hw,?_⟩
  rw [radius_scale,radius_scale]
  calc
    r*S.radius w+r*T.radius w = r*(S.radius w+T.radius w) := by ring
    _ ≤ r*|w.1*(T.x-S.x)+w.2*(T.y-S.y)| := mul_le_mul_of_nonneg_left hsep hr.le
    _ = |r*(w.1*(T.x-S.x)+w.2*(T.y-S.y))| := by rw [abs_mul,abs_of_pos hr]
    _ = |w.1*((T.scale r).x-(S.scale r).x)+w.2*((T.scale r).y-(S.scale r).y)| := by
      congr 1
      simp [Square.scale]; ring

private theorem packing_scale {L r : ℝ} (hr : 0 < r) {P : List Square} (hp : Packing L P) :
    Packing (r*L) (P.map (fun S => S.scale r)) := by
  constructor
  · intro S hs
    obtain ⟨T,ht,rfl⟩ := List.mem_map.mp hs
    exact fits_scale hr (hp.1 T ht)
  · rw [List.pairwise_map]
    exact hp.2.imp (fun h => separated_scale hr h)
private theorem total_scale (P : List Square) (r : ℝ) :
    total (P.map (fun S => S.scale r)) = r*total P := by
  induction P with
  | nil => simp [total]
  | cons S P ih => simpa [total,Square.scale,mul_add] using congrArg (fun x => r*S.side+x) ih

/-- Every k ≥ 4 has a unit-square packing of k²+1 squares with total side length > k. -/
theorem unit_counterexamples (k : ℕ) (hk : 4 ≤ k) :
    ∃ P : List Square, Packing 1 P ∧ P.length = k^2+1 ∧ (k : ℝ) < total P := by
  obtain ⟨P,hp,hlen,htotal⟩ := all_sizes k hk
  have hkR : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  refine ⟨P.map (fun S => S.scale (1/k)),?_,by simpa using hlen,?_⟩
  · have hp' := packing_scale (one_div_pos.mpr hkR) hp
    simpa [ne_of_gt hkR] using hp'
  · rw [total_scale]
    calc
      (k : ℝ) < total P/k := (lt_div_iff₀ hkR).2 (by nlinarith)
      _ = 1/k*total P := by ring

def Square.carrier (S : Square) : Set Point :=
  {p | ∃ a b, |a| ≤ S.side/2 ∧ |b| ≤ S.side/2 ∧ p=S.point a b}
def box (L : ℝ) : Set Point := {p | 0 ≤ p.1 ∧ p.1 ≤ L ∧ 0 ≤ p.2 ∧ p.2 ≤ L}
private theorem linear_le (A B t a b : ℝ) (ha : |a| ≤ t) (hb : |b| ≤ t) :
    |a*A+b*B| ≤ t*(|A|+|B|) := by
  calc
    |a*A+b*B| ≤ |a| * |A|+|b| * |B| := by simpa [abs_mul] using abs_add_le (a*A) (b*B)
    _ ≤ t*|A|+t*|B| := add_le_add (mul_le_mul_of_nonneg_right ha (abs_nonneg A))
        (mul_le_mul_of_nonneg_right hb (abs_nonneg B))
    _ = t*(|A|+|B|) := by ring

theorem fits_carrier {S : Square} {L : ℝ} (hf : S.Fits L) : S.carrier ⊆ box L := by
  rintro p ⟨a,b,ha,hb,rfl⟩
  obtain ⟨hs,hu,hx,hxl,hy,hyl⟩ := hf
  have h1 := linear_le S.u (-S.v) (S.side/2) a b ha hb
  have h2 := linear_le S.v S.u (S.side/2) a b ha hb
  simp only [abs_neg,mul_neg,←sub_eq_add_neg] at h1
  norm_num [Square.radius] at hx hxl hy hyl
  obtain ⟨hl1,hr1⟩ := abs_le.mp h1
  obtain ⟨hl2,hr2⟩ := abs_le.mp h2
  change 0 ≤ S.x+a*S.u-b*S.v ∧ S.x+a*S.u-b*S.v ≤ L ∧
    0 ≤ S.y+a*S.v+b*S.u ∧ S.y+a*S.v+b*S.u ≤ L
  exact ⟨by linarith,by linarith,by linarith,by linarith⟩

/-- Geometric statement: genuine squares, closed containment and disjoint interiors. -/
theorem geometric_counterexamples (k : ℕ) (hk : 4 ≤ k) :
    ∃ P : List Square, P.length=k^2+1 ∧ (k : ℝ)<total P ∧
      (∀ S ∈ P, 0<S.side ∧ S.u^2+S.v^2=1 ∧ S.carrier ⊆ box 1) ∧
      P.Pairwise (fun S T => Disjoint S.interior T.interior) := by
  obtain ⟨P,hp,hlen,htotal⟩ := unit_counterexamples k hk
  refine ⟨P,hlen,htotal,?_,?_⟩
  · intro S hs
    exact ⟨(hp.1 S hs).1,(hp.1 S hs).2.1,fits_carrier (hp.1 S hs)⟩
  · apply hp.2.imp_of_mem
    intro S T hs ht hsep
    exact separated_disjoint (hp.1 S hs).2.1 (hp.1 T ht).2.1 hsep

/-- The proposed identity f(k²+1)=k would bound every such side sum by k. -/
theorem jsp_000118 :
    ¬ ∀ (k : ℕ) (P : List Square), 1 ≤ k → P.length=k^2+1 →
      (∀ S ∈ P, 0<S.side ∧ S.u^2+S.v^2=1 ∧ S.carrier ⊆ box 1) →
      P.Pairwise (fun S T => Disjoint S.interior T.interior) → total P ≤ k := by
  intro hall
  obtain ⟨P,hlen,htotal,hfits,hdisj⟩ := geometric_counterexamples 4 (by omega)
  have hle := hall 4 P (by omega) hlen hfits hdisj
  norm_num at hle htotal
  linarith

#print axioms all_sizes
#print axioms unit_counterexamples
#print axioms geometric_counterexamples
#print axioms jsp_000118

end

end JSP000118
