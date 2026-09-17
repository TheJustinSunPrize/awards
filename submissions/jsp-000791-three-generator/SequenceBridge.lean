import SharpLower
import Mathlib.Data.Finsupp.Basic

noncomputable section

namespace JSP791

/-- The original finitely supported exponent product, on a natural-indexed
sequence. The empty exponent vector has value 1. -/
noncomputable def sequenceMonomial (a : ℕ → ℝ) (u : ℕ →₀ ℕ) : ℝ :=
  u.prod fun i k => a i ^ k

def SequenceSeparated (a : ℕ → ℝ) : Prop :=
  ∀ u v : ℕ →₀ ℕ, u ≠ v → 1 ≤ |sequenceMonomial a u - sequenceMonomial a v|

def embed3 (u : Fin 3 → ℕ) : ℕ →₀ ℕ :=
  Finsupp.single 0 (u 0) + Finsupp.single 1 (u 1) + Finsupp.single 2 (u 2)

lemma embed3_injective : Function.Injective embed3 := by
  intro u v h
  funext i
  fin_cases i
  · simpa [embed3] using congrArg (fun f : ℕ →₀ ℕ => f 0) h
  · simpa [embed3] using congrArg (fun f : ℕ →₀ ℕ => f 1) h
  · simpa [embed3] using congrArg (fun f : ℕ →₀ ℕ => f 2) h

lemma sequenceMonomial_embed3 (a : ℕ → ℝ) (u : Fin 3 → ℕ) :
    sequenceMonomial a (embed3 u) = monomial (a 0) (a 1) (a 2) u := by
  simp [sequenceMonomial,embed3,monomial,Finsupp.prod_add_index,pow_add]

theorem sequence_third_generator_gt_cutoff {a : ℕ → ℝ} (ha : 1 < a 0)
    (hm : StrictMono a) (hs : SequenceSeparated a) :
    (4309405275 : ℝ)/1000000000 < a 2 := by
  apply third_generator_gt_cutoff ha (hm (by norm_num : (0:ℕ)<1)) (hm (by norm_num : (1:ℕ)<2))
  intro u v huv
  have h := hs (embed3 u) (embed3 v) (fun hh => huv (embed3_injective hh))
  simpa only [sequenceMonomial_embed3] using h

end JSP791

#print axioms JSP791.sequence_third_generator_gt_cutoff
