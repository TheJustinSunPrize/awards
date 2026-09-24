import TrianglePacking.Basic

namespace TrianglePacking

open Finset

lemma sum_arcs_triple {V : Type*} [DecidableEq V] (w : V × V → ℕ)
    {a b c : V} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ∑ e ∈ arcs ({a, b, c} : Finset V), w e =
      w (a,b) + w (a,c) + w (b,a) + w (b,c) + w (c,a) + w (c,b) := by
  have he : arcs ({a, b, c} : Finset V) =
      {(a,b), (a,c), (b,a), (b,c), (c,a), (c,b)} := by
    ext ⟨u,v⟩
    simp only [arcs, mem_offDiag, mem_insert, mem_singleton, Prod.mk.injEq]
    aesop
  rw [he]
  simp [hab, hac, hbc, hab.symm, hac.symm, hbc.symm, add_assoc]

/-- Every triangle has total oriented-edge weight at least twelve. -/
theorem triangle_weight {r s : ℕ} {T : Finset (Vertex r s)}
    (hT : (graph r s).IsNClique 3 T) :
    12 ≤ ∑ e ∈ arcs T, weight e := by
  obtain ⟨a,b,c,hab,hac,hbc,rfl⟩ := SimpleGraph.is3Clique_iff.mp hT
  rw [sum_arcs_triple weight hab.ne hac.ne hbc.ne]
  change a ≠ b ∧ (part a ≠ part b ∨ part a = 2) at hab
  change a ≠ c ∧ (part a ≠ part c ∨ part a = 2) at hac
  change b ≠ c ∧ (part b ≠ part c ∨ part b = 2) at hbc
  have hpab := hab.2
  have hpac := hac.2
  have hpbc := hbc.2
  simp only [weight]
  generalize part a = pa at hpab hpac ⊢
  generalize part b = pb at hpab hpbc ⊢
  generalize part c = pc at hpac hpbc ⊢
  fin_cases pa <;> fin_cases pb <;> fin_cases pc <;> norm_num [Fin.ext_iff] at *

end TrianglePacking
