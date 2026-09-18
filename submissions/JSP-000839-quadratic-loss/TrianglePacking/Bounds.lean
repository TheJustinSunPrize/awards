import TrianglePacking.Construction
import TrianglePacking.TriangleWeight
import TrianglePacking.WeightedPacking
import TrianglePacking.Parity
import Mathlib.Data.Real.Basic

/-!
# A quadratic obstruction for Erdős problem 1009

The parameter is `c = 6*t`. The family has arbitrarily many vertices, and forces
an additive loss of at least `12*t^2 - 2*t` in the guaranteed triangle packing.
This is a lower-bound formalization, not another proof of Győri's upper bound.
-/

namespace TrianglePacking

open Finset

/-- Edges above the balanced bipartite threshold in the chosen family. -/
def excess (r t : ℕ) : ℕ := 12 * t * r + 36 * t ^ 2 - 6 * t

/-- The lower bound furnished by weighted counting and odd core degrees. -/
def loss (t : ℕ) : ℕ := 12 * t ^ 2 - 2 * t

theorem packing_bound {r s : ℕ} {P : Finset (Finset (Vertex r s))}
    (hP : IsPacking (graph r s) P) :
    6 * P.card ≤ 6 * r * s + s * (s - 1) := by
  have h := hP.weighted_bound weight 12 (fun T hT => triangle_weight (hP.1 T hT))
  rw [total_weight] at h
  nlinarith

theorem packing_twelve {r t : ℕ} (ht : 0 < t)
    {P : Finset (Finset (Vertex r (12 * t)))} (hP : IsPacking (graph r (12 * t)) P) :
    P.card + 4 * t ≤ 12 * t * r + 24 * t ^ 2 := by
  have heven : Even (12 * t) := ⟨6 * t, by omega⟩
  have h := hP.bound_even_core heven (by omega)
  have hs : 12 * t - 2 + 2 = 12 * t := by omega
  nlinarith

lemma excess_add (r : ℕ) {t : ℕ} (ht : 0 < t) :
    excess r t + 6 * t = 12 * t * r + 36 * t ^ 2 := by
  have htt : t ≤ t ^ 2 := by nlinarith [Nat.mul_le_mul_left t ht]
  exact Nat.sub_add_cancel (by nlinarith)

lemma loss_add {t : ℕ} (ht : 0 < t) : loss t + 2 * t = 12 * t ^ 2 := by
  have htt : t ≤ t ^ 2 := by nlinarith [Nat.mul_le_mul_left t ht]
  exact Nat.sub_add_cancel (by nlinarith)

theorem packing_loss {r t : ℕ} (ht : 0 < t)
    {P : Finset (Finset (Vertex r (12 * t)))} (hP : IsPacking (graph r (12 * t)) P) :
    P.card + loss t ≤ excess r t := by
  have h := packing_twelve ht hP
  have hk := excess_add r ht
  have hd := loss_add ht
  omega

theorem balanced_threshold (r t : ℕ) :
    (Fintype.card (Vertex r (12 * t))) ^ 2 / 4 = (r + 6 * t) ^ 2 := by
  rw [vertex_card, show (2 * r + 12 * t) ^ 2 = 4 * (r + 6 * t) ^ 2 by ring]
  omega

theorem edge_count_excess (r : ℕ) {t : ℕ} (ht : 0 < t) :
    (graph r (12 * t)).edgeFinset.card =
      (Fintype.card (Vertex r (12 * t))) ^ 2 / 4 + excess r t := by
  rw [balanced_threshold]
  have hm := edge_card_twelve r t
  have hk := excess_add r ht
  nlinarith

theorem excess_lt_parameter (r : ℕ) {t : ℕ} (ht : 0 < t) :
    excess r t < (6 * t) * Fintype.card (Vertex r (12 * t)) := by
  rw [vertex_card]
  have hk := excess_add r ht
  nlinarith

/-- Counterexamples to every smaller error, with no bound on their order. -/
theorem arbitrarily_large_obstructions {t : ℕ} (ht : 0 < t) (N : ℕ) :
    ∃ r : ℕ,
      N ≤ Fintype.card (Vertex r (12 * t)) ∧
      (graph r (12 * t)).edgeFinset.card =
        (Fintype.card (Vertex r (12 * t))) ^ 2 / 4 + excess r t ∧
      excess r t < (6 * t) * Fintype.card (Vertex r (12 * t)) ∧
      ∀ P : Finset (Finset (Vertex r (12 * t))),
        IsPacking (graph r (12 * t)) P → P.card + loss t ≤ excess r t := by
  refine ⟨N, ?_, edge_count_excess N ht, excess_lt_parameter N ht, ?_⟩
  · rw [vertex_card]
    omega
  · exact fun _ hP => packing_loss ht hP

/-- The assertion of problem 1009 for a fixed nonnegative integer error `f`.
The formulation even allows a threshold on the number of vertices. -/
def IsEventualErrorBound (c : ℝ) (f : ℕ) : Prop :=
  ∃ N : ℕ, ∀ (V : Type) [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ),
    N ≤ Fintype.card V →
    (Fintype.card V) ^ 2 / 4 + k ≤ G.edgeFinset.card →
    (k : ℝ) < c * Fintype.card V →
    ∃ P : Finset (Finset V), IsPacking G P ∧ k ≤ P.card + f

/-- Even an eventual version of the original guarantee needs quadratic loss. -/
theorem error_lower_bound {t f : ℕ} (ht : 0 < t)
    (hf : IsEventualErrorBound (6 * t) f) : 12 * t ^ 2 - 2 * t ≤ f := by
  obtain ⟨N, hf⟩ := hf
  obtain ⟨r, hN, hm, hk, hp⟩ := arbitrarily_large_obstructions ht N
  have hkR : (excess r t : ℝ) < (6 * t : ℝ) * Fintype.card (Vertex r (12 * t)) := by
    exact_mod_cast hk
  obtain ⟨P, hP, hPf⟩ := hf (Vertex r (12 * t)) (graph r (12 * t))
    (excess r t) hN (by omega) hkR
  have h := hp P hP
  change loss t ≤ f
  omega

/-- A guarantee at a larger parameter also applies at every smaller parameter. -/
theorem IsEventualErrorBound.mono_parameter {c d : ℝ} {f : ℕ}
    (hf : IsEventualErrorBound c f) (hd : d ≤ c) : IsEventualErrorBound d f := by
  obtain ⟨N, hf⟩ := hf
  refine ⟨N, fun V _ _ G _ k hN hm hk => ?_⟩
  exact hf V G k hN hm (lt_of_lt_of_le hk (mul_le_mul_of_nonneg_right hd (by positivity)))

/-- The same obstruction applies to every real parameter at least `6*t`. -/
theorem error_lower_bound_of_le {t f : ℕ} {c : ℝ} (ht : 0 < t)
    (hc : (6 * t : ℝ) ≤ c) (hf : IsEventualErrorBound c f) :
    12 * t ^ 2 - 2 * t ≤ f :=
  error_lower_bound ht (hf.mono_parameter hc)

/-- No error independent of the parameter works, even for sufficiently large graphs. -/
theorem no_uniform_error (f : ℕ) :
    ¬∀ c : ℝ, 0 < c → IsEventualErrorBound c f := by
  intro h
  have ht : 0 < f + 1 := by omega
  have hbound := error_lower_bound ht (h (6 * (f + 1 : ℕ)) (by positivity))
  have hadd := loss_add ht
  change loss (f + 1) ≤ f at hbound
  nlinarith

end TrianglePacking
