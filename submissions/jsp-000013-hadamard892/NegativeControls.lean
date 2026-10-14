import Hadamard892

namespace Hadamard892
set_option maxRecDepth 200000
set_option maxHeartbeats 0

/-- Change one sign in the first seed. The signs still look valid. -/
def damagedSeed (i : Fin 4) (x : Fin 223) : ℤ :=
  if i = 0 ∧ x = 0 then -seed i x else seed i x

theorem damaged_seed_still_signs (i : Fin 4) (x : Fin 223) :
    damagedSeed i x = 1 ∨ damagedSeed i x = -1 := by
  unfold damagedSeed
  split
  · exact neg_signs (seed_signs i x)
  · exact seed_signs i x

/-- The first nonzero shift detects the damaged input exactly. -/
theorem damaged_shift_one :
    (∑ i : Fin 4, corr (damagedSeed i) (1 : Fin 223)) = -4 := by decide

/-- The complete correlation premise is false for the one-sign corruption. -/
theorem damaged_seed_fails_certificate :
    ¬ (∀ t : Fin 223, (∑ i : Fin 4, corr (damagedSeed i) t) =
      if t = 0 then (892 : ℤ) else 0) := by
  intro h
  have h1 : (∑ i : Fin 4, corr (damagedSeed i) (1 : Fin 223)) = 0 := by
    simpa using h 1
  rw [damaged_shift_one] at h1
  norm_num at h1

#print axioms damaged_seed_fails_certificate
end Hadamard892
