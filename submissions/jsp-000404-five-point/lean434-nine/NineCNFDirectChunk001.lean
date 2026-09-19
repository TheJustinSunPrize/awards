import NineTheoryTrial

set_option maxRecDepth 10000

set_option maxHeartbeats 1000000

namespace NineCNFDirectTrial

theorem clause1287 (t x02 x05 x25 : ℝ) (h : (((x02 ≤ x05) ∧ (x05 ≤ x25) ∧ ((x25 - x02) ≥ 1) ∧ ((x05 - x02) ≤ (t - 1)) ∧ ((x25 - x05) ≤ (t - 1))) ∨ ((x25 ≤ x05) ∧ (x05 ≤ x02) ∧ ((x02 - x25) ≥ 1) ∧ ((x02 - x05) ≤ (t - 1)) ∧ ((x05 - x25) ≤ (t - 1))))) : ((x05 ≤ x25) ∨ ((x02 - x25) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x05 ≤ x25) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x02 - x25) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause1288 (t x02 x05 x25 : ℝ) (h : (((x02 ≤ x05) ∧ (x05 ≤ x25) ∧ ((x25 - x02) ≥ 1) ∧ ((x05 - x02) ≤ (t - 1)) ∧ ((x25 - x05) ≤ (t - 1))) ∨ ((x25 ≤ x05) ∧ (x05 ≤ x02) ∧ ((x02 - x25) ≥ 1) ∧ ((x02 - x05) ≤ (t - 1)) ∧ ((x05 - x25) ≤ (t - 1))))) : ((x05 ≤ x25) ∨ ((x02 - x05) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x05 ≤ x25) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x02 - x05) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause1289 (t x02 x05 x25 : ℝ) (h : (((x02 ≤ x05) ∧ (x05 ≤ x25) ∧ ((x25 - x02) ≥ 1) ∧ ((x05 - x02) ≤ (t - 1)) ∧ ((x25 - x05) ≤ (t - 1))) ∨ ((x25 ≤ x05) ∧ (x05 ≤ x02) ∧ ((x02 - x25) ≥ 1) ∧ ((x02 - x05) ≤ (t - 1)) ∧ ((x05 - x25) ≤ (t - 1))))) : ((x05 ≤ x25) ∨ ((x05 - x25) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x05 ≤ x25) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x05 - x25) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause1290 (t x02 x05 x25 : ℝ) (h : (((x02 ≤ x05) ∧ (x05 ≤ x25) ∧ ((x25 - x02) ≥ 1) ∧ ((x05 - x02) ≤ (t - 1)) ∧ ((x25 - x05) ≤ (t - 1))) ∨ ((x25 ≤ x05) ∧ (x05 ≤ x02) ∧ ((x02 - x25) ≥ 1) ∧ ((x02 - x05) ≤ (t - 1)) ∧ ((x05 - x25) ≤ (t - 1))))) : (((x25 - x02) ≥ 1) ∨ (x25 ≤ x05)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x25 - x02) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x25 ≤ x05) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause1291 (t x02 x05 x25 : ℝ) (h : (((x02 ≤ x05) ∧ (x05 ≤ x25) ∧ ((x25 - x02) ≥ 1) ∧ ((x05 - x02) ≤ (t - 1)) ∧ ((x25 - x05) ≤ (t - 1))) ∨ ((x25 ≤ x05) ∧ (x05 ≤ x02) ∧ ((x02 - x25) ≥ 1) ∧ ((x02 - x05) ≤ (t - 1)) ∧ ((x05 - x25) ≤ (t - 1))))) : (((x25 - x02) ≥ 1) ∨ (x05 ≤ x02)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x25 - x02) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x05 ≤ x02) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause1292 (t x02 x05 x25 : ℝ) (h : (((x02 ≤ x05) ∧ (x05 ≤ x25) ∧ ((x25 - x02) ≥ 1) ∧ ((x05 - x02) ≤ (t - 1)) ∧ ((x25 - x05) ≤ (t - 1))) ∨ ((x25 ≤ x05) ∧ (x05 ≤ x02) ∧ ((x02 - x25) ≥ 1) ∧ ((x02 - x05) ≤ (t - 1)) ∧ ((x05 - x25) ≤ (t - 1))))) : (((x25 - x02) ≥ 1) ∨ ((x02 - x25) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x25 - x02) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x02 - x25) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause1293 (t x02 x05 x25 : ℝ) (h : (((x02 ≤ x05) ∧ (x05 ≤ x25) ∧ ((x25 - x02) ≥ 1) ∧ ((x05 - x02) ≤ (t - 1)) ∧ ((x25 - x05) ≤ (t - 1))) ∨ ((x25 ≤ x05) ∧ (x05 ≤ x02) ∧ ((x02 - x25) ≥ 1) ∧ ((x02 - x05) ≤ (t - 1)) ∧ ((x05 - x25) ≤ (t - 1))))) : (((x25 - x02) ≥ 1) ∨ ((x02 - x05) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x25 - x02) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x02 - x05) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause1294 (t x02 x05 x25 : ℝ) (h : (((x02 ≤ x05) ∧ (x05 ≤ x25) ∧ ((x25 - x02) ≥ 1) ∧ ((x05 - x02) ≤ (t - 1)) ∧ ((x25 - x05) ≤ (t - 1))) ∨ ((x25 ≤ x05) ∧ (x05 ≤ x02) ∧ ((x02 - x25) ≥ 1) ∧ ((x02 - x05) ≤ (t - 1)) ∧ ((x05 - x25) ≤ (t - 1))))) : (((x25 - x02) ≥ 1) ∨ ((x05 - x25) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x25 - x02) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x05 - x25) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause1295 (t x02 x05 x25 : ℝ) (h : (((x02 ≤ x05) ∧ (x05 ≤ x25) ∧ ((x25 - x02) ≥ 1) ∧ ((x05 - x02) ≤ (t - 1)) ∧ ((x25 - x05) ≤ (t - 1))) ∨ ((x25 ≤ x05) ∧ (x05 ≤ x02) ∧ ((x02 - x25) ≥ 1) ∧ ((x02 - x05) ≤ (t - 1)) ∧ ((x05 - x25) ≤ (t - 1))))) : (((x05 - x02) ≤ (t - 1)) ∨ (x25 ≤ x05)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x05 - x02) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x25 ≤ x05) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause1296 (t x02 x05 x25 : ℝ) (h : (((x02 ≤ x05) ∧ (x05 ≤ x25) ∧ ((x25 - x02) ≥ 1) ∧ ((x05 - x02) ≤ (t - 1)) ∧ ((x25 - x05) ≤ (t - 1))) ∨ ((x25 ≤ x05) ∧ (x05 ≤ x02) ∧ ((x02 - x25) ≥ 1) ∧ ((x02 - x05) ≤ (t - 1)) ∧ ((x05 - x25) ≤ (t - 1))))) : (((x05 - x02) ≤ (t - 1)) ∨ (x05 ≤ x02)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x05 - x02) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x05 ≤ x02) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause1297 (t x02 x05 x25 : ℝ) (h : (((x02 ≤ x05) ∧ (x05 ≤ x25) ∧ ((x25 - x02) ≥ 1) ∧ ((x05 - x02) ≤ (t - 1)) ∧ ((x25 - x05) ≤ (t - 1))) ∨ ((x25 ≤ x05) ∧ (x05 ≤ x02) ∧ ((x02 - x25) ≥ 1) ∧ ((x02 - x05) ≤ (t - 1)) ∧ ((x05 - x25) ≤ (t - 1))))) : (((x05 - x02) ≤ (t - 1)) ∨ ((x02 - x25) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x05 - x02) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x02 - x25) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause1298 (t x02 x05 x25 : ℝ) (h : (((x02 ≤ x05) ∧ (x05 ≤ x25) ∧ ((x25 - x02) ≥ 1) ∧ ((x05 - x02) ≤ (t - 1)) ∧ ((x25 - x05) ≤ (t - 1))) ∨ ((x25 ≤ x05) ∧ (x05 ≤ x02) ∧ ((x02 - x25) ≥ 1) ∧ ((x02 - x05) ≤ (t - 1)) ∧ ((x05 - x25) ≤ (t - 1))))) : (((x05 - x02) ≤ (t - 1)) ∨ ((x02 - x05) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x05 - x02) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x02 - x05) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause1299 (t x02 x05 x25 : ℝ) (h : (((x02 ≤ x05) ∧ (x05 ≤ x25) ∧ ((x25 - x02) ≥ 1) ∧ ((x05 - x02) ≤ (t - 1)) ∧ ((x25 - x05) ≤ (t - 1))) ∨ ((x25 ≤ x05) ∧ (x05 ≤ x02) ∧ ((x02 - x25) ≥ 1) ∧ ((x02 - x05) ≤ (t - 1)) ∧ ((x05 - x25) ≤ (t - 1))))) : (((x05 - x02) ≤ (t - 1)) ∨ ((x05 - x25) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x05 - x02) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x05 - x25) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause1300 (t x02 x05 x25 : ℝ) (h : (((x02 ≤ x05) ∧ (x05 ≤ x25) ∧ ((x25 - x02) ≥ 1) ∧ ((x05 - x02) ≤ (t - 1)) ∧ ((x25 - x05) ≤ (t - 1))) ∨ ((x25 ≤ x05) ∧ (x05 ≤ x02) ∧ ((x02 - x25) ≥ 1) ∧ ((x02 - x05) ≤ (t - 1)) ∧ ((x05 - x25) ≤ (t - 1))))) : (((x25 - x05) ≤ (t - 1)) ∨ (x25 ≤ x05)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x25 - x05) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x25 ≤ x05) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause1301 (t x02 x05 x25 : ℝ) (h : (((x02 ≤ x05) ∧ (x05 ≤ x25) ∧ ((x25 - x02) ≥ 1) ∧ ((x05 - x02) ≤ (t - 1)) ∧ ((x25 - x05) ≤ (t - 1))) ∨ ((x25 ≤ x05) ∧ (x05 ≤ x02) ∧ ((x02 - x25) ≥ 1) ∧ ((x02 - x05) ≤ (t - 1)) ∧ ((x05 - x25) ≤ (t - 1))))) : (((x25 - x05) ≤ (t - 1)) ∨ (x05 ≤ x02)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x25 - x05) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x05 ≤ x02) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause1302 (t x02 x05 x25 : ℝ) (h : (((x02 ≤ x05) ∧ (x05 ≤ x25) ∧ ((x25 - x02) ≥ 1) ∧ ((x05 - x02) ≤ (t - 1)) ∧ ((x25 - x05) ≤ (t - 1))) ∨ ((x25 ≤ x05) ∧ (x05 ≤ x02) ∧ ((x02 - x25) ≥ 1) ∧ ((x02 - x05) ≤ (t - 1)) ∧ ((x05 - x25) ≤ (t - 1))))) : (((x25 - x05) ≤ (t - 1)) ∨ ((x02 - x25) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x25 - x05) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x02 - x25) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause1303 (t x02 x05 x25 : ℝ) (h : (((x02 ≤ x05) ∧ (x05 ≤ x25) ∧ ((x25 - x02) ≥ 1) ∧ ((x05 - x02) ≤ (t - 1)) ∧ ((x25 - x05) ≤ (t - 1))) ∨ ((x25 ≤ x05) ∧ (x05 ≤ x02) ∧ ((x02 - x25) ≥ 1) ∧ ((x02 - x05) ≤ (t - 1)) ∧ ((x05 - x25) ≤ (t - 1))))) : (((x25 - x05) ≤ (t - 1)) ∨ ((x02 - x05) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x25 - x05) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x02 - x05) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause1304 (t x02 x05 x25 : ℝ) (h : (((x02 ≤ x05) ∧ (x05 ≤ x25) ∧ ((x25 - x02) ≥ 1) ∧ ((x05 - x02) ≤ (t - 1)) ∧ ((x25 - x05) ≤ (t - 1))) ∨ ((x25 ≤ x05) ∧ (x05 ≤ x02) ∧ ((x02 - x25) ≥ 1) ∧ ((x02 - x05) ≤ (t - 1)) ∧ ((x05 - x25) ≤ (t - 1))))) : (((x25 - x05) ≤ (t - 1)) ∨ ((x05 - x25) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x25 - x05) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x05 - x25) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause1305 (t x23 x24 x34 : ℝ) : (((t + ((-1) * x23)) ≤ 0) ∨ (¬ (x24 ≥ 0)) ∨ ((t + x24 + ((-1) * x34)) ≥ 1) ∨ (¬ ((x23 + ((-1) * x34)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((t + ((-1) * x23)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : (x24 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ¬ ((t + x24 + ((-1) * x34)) ≥ 1) := fun hh => hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x23 + ((-1) * x34)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr hh)))
  have h := NineTheoryTrial.th77 t x23 x24 x34
  exact (fun hh => (fun hh => hh) (hh (And.intro u1 (And.intro u0 (And.intro u2 u3))))) h

theorem clause1306 (t x02 x24 x25 x34 x45 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x34 + ((-1) * x45)) ≥ 1)) ∨ (¬ ((t + x24 + ((-1) * x34)) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x25)) ≤ (-1))) ∨ (¬ ((x25 + ((-1) * x45)) ≤ 0)) ∨ (¬ ((x02 + ((-1) * x24)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x34 + ((-1) * x45)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((t + x24 + ((-1) * x34)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x02 + ((-1) * x25)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x25 + ((-1) * x45)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x02 + ((-1) * x24)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th78 t x02 x24 x25 x34 x45
  exact (fun hh => (fun hh => hh) (hh (And.intro u2 (And.intro u4 (And.intro u0 (And.intro u1 (And.intro u3 u5))))))) h

theorem clause1307 (t x02 x23 x24 x34 x45 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x02 + ((-1) * x24)) ≤ (-1))) ∨ (¬ (x23 ≥ 0)) ∨ (¬ ((x34 + ((-1) * x45)) ≥ 1)) ∨ (¬ ((x02 + ((-1) * x23)) ≥ 1)) ∨ ((t + ((-1) * x34)) ≤ 0) ∨ (¬ ((x24 + ((-1) * x45)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x02 + ((-1) * x24)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : (x23 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x34 + ((-1) * x45)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x02 + ((-1) * x23)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ¬ ((t + ((-1) * x34)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x24 + ((-1) * x45)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th79 t x02 x23 x24 x34 x45
  exact (fun hh => (fun hh => hh) (hh (And.intro u0 (And.intro u5 (And.intro u4 (And.intro u6 (And.intro u2 (And.intro u1 u3)))))))) h

theorem clause1308 (t x34 : ℝ) : ((¬ ((t + ((-1) * x34)) ≤ 0)) ∨ (t ≤ x34)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((t + ((-1) * x34)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ¬ (t ≤ x34) := fun hh => hn (Or.inr hh)
  have h := NineTheoryTrial.th80 t x34
  exact (fun hh => (fun hh => hh u0) (hh.mp u1)) h

theorem clause1310 (t x34 : ℝ) : ((¬ (t ≤ x34)) ∨ (¬ (x34 < t))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (t ≤ x34) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : (x34 < t) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr hh)
  have h := NineTheoryTrial.th81 t x34
  exact (fun hh => (fun hh => hh u0) (hh.mp u1)) h

theorem clause1312 (t x34 : ℝ) (h : (x34 < t)) : ((x34 < t)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x34 < t) := fun hh => hn hh
  exact u0 h

theorem clause1315 (t x02 x04 x24 : ℝ) : (((x02 + ((-1) * x24)) ≥ 1) ∨ ((x02 + ((-1) * x04)) ≤ 0) ∨ (¬ (x02 ≤ x04)) ∨ (¬ (x04 ≤ x24)) ∨ (¬ ((x24 - x02) ≥ 1)) ∨ (¬ ((x04 - x02) ≤ (t - 1))) ∨ (¬ ((x24 - x04) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x02 + ((-1) * x24)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x02 + ((-1) * x04)) ≤ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x02 ≤ x04) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x04 ≤ x24) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x24 - x02) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x04 - x02) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x24 - x04) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th84 t x02 x04 x24
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 (hh).1) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause1320 (t x02 x04 x24 : ℝ) : (((x02 + ((-1) * x24)) ≥ 1) ∨ ((x04 + ((-1) * x24)) ≤ 0) ∨ (¬ (x02 ≤ x04)) ∨ (¬ (x04 ≤ x24)) ∨ (¬ ((x24 - x02) ≥ 1)) ∨ (¬ ((x04 - x02) ≤ (t - 1))) ∨ (¬ ((x24 - x04) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x02 + ((-1) * x24)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x04 + ((-1) * x24)) ≤ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x02 ≤ x04) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x04 ≤ x24) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x24 - x02) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x04 - x02) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x24 - x04) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th84 t x02 x04 x24
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 ((hh).2).1) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause1322 (t x02 x04 x24 : ℝ) : (((x04 + ((-1) * x24)) ≤ 0) ∨ ((t + ((-1) * x04) + x24) ≥ 1) ∨ (¬ (x02 ≤ x04)) ∨ (¬ (x04 ≤ x24)) ∨ (¬ ((x24 - x02) ≥ 1)) ∨ (¬ ((x04 - x02) ≤ (t - 1))) ∨ (¬ ((x24 - x04) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x04 + ((-1) * x24)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + ((-1) * x04) + x24) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x02 ≤ x04) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x04 ≤ x24) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x24 - x02) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x04 - x02) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x24 - x04) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th84 t x02 x04 x24
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause1323 (t x02 x04 x24 : ℝ) : (((x02 + ((-1) * x24)) ≤ (-1)) ∨ ((x04 + ((-1) * x24)) ≥ 0) ∨ (¬ (x02 ≤ x04)) ∨ (¬ (x04 ≤ x24)) ∨ (¬ ((x24 - x02) ≥ 1)) ∨ (¬ ((x04 - x02) ≤ (t - 1))) ∨ (¬ ((x24 - x04) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x02 + ((-1) * x24)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x04 + ((-1) * x24)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x02 ≤ x04) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x04 ≤ x24) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x24 - x02) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x04 - x02) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x24 - x04) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th84 t x02 x04 x24
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause1324 (t x02 x04 x24 : ℝ) : (((x02 + ((-1) * x24)) ≤ (-1)) ∨ ((x02 + ((-1) * x04)) ≥ 0) ∨ (¬ (x02 ≤ x04)) ∨ (¬ (x04 ≤ x24)) ∨ (¬ ((x24 - x02) ≥ 1)) ∨ (¬ ((x04 - x02) ≤ (t - 1))) ∨ (¬ ((x24 - x04) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x02 + ((-1) * x24)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x02 + ((-1) * x04)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x02 ≤ x04) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x04 ≤ x24) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x24 - x02) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x04 - x02) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x24 - x04) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th84 t x02 x04 x24
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause1325 (t x02 x04 x24 : ℝ) : (((x02 + ((-1) * x24)) ≤ (-1)) ∨ ((x02 + ((-1) * x24)) ≥ 1) ∨ (¬ (x02 ≤ x04)) ∨ (¬ (x04 ≤ x24)) ∨ (¬ ((x24 - x02) ≥ 1)) ∨ (¬ ((x04 - x02) ≤ (t - 1))) ∨ (¬ ((x24 - x04) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x02 + ((-1) * x24)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x02 + ((-1) * x24)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x02 ≤ x04) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x04 ≤ x24) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x24 - x02) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x04 - x02) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x24 - x04) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th84 t x02 x04 x24
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause1326 (t x02 x04 x24 : ℝ) : (((x02 + ((-1) * x24)) ≤ (-1)) ∨ ((t + ((-1) * x02) + x04) ≥ 1) ∨ (¬ (x02 ≤ x04)) ∨ (¬ (x04 ≤ x24)) ∨ (¬ ((x24 - x02) ≥ 1)) ∨ (¬ ((x04 - x02) ≤ (t - 1))) ∨ (¬ ((x24 - x04) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x02 + ((-1) * x24)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + ((-1) * x02) + x04) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x02 ≤ x04) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x04 ≤ x24) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x24 - x02) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x04 - x02) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x24 - x04) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th84 t x02 x04 x24
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause1327 (t x02 x04 x24 : ℝ) : (((x02 + ((-1) * x24)) ≤ (-1)) ∨ ((t + ((-1) * x04) + x24) ≥ 1) ∨ (¬ (x02 ≤ x04)) ∨ (¬ (x04 ≤ x24)) ∨ (¬ ((x24 - x02) ≥ 1)) ∨ (¬ ((x04 - x02) ≤ (t - 1))) ∨ (¬ ((x24 - x04) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x02 + ((-1) * x24)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + ((-1) * x04) + x24) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x02 ≤ x04) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x04 ≤ x24) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x24 - x02) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x04 - x02) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x24 - x04) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th84 t x02 x04 x24
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause1335 (t x02 x04 x24 : ℝ) : (((x02 + ((-1) * x24)) ≥ 1) ∨ ((t + x04 + ((-1) * x24)) ≥ 1) ∨ (¬ (x02 ≤ x04)) ∨ (¬ (x04 ≤ x24)) ∨ (¬ ((x24 - x02) ≥ 1)) ∨ (¬ ((x04 - x02) ≤ (t - 1))) ∨ (¬ ((x24 - x04) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x02 + ((-1) * x24)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + x04 + ((-1) * x24)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x02 ≤ x04) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x04 ≤ x24) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x24 - x02) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x04 - x02) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x24 - x04) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th84 t x02 x04 x24
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 ((((hh).2).2).2).2) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause1340 (t x02 x04 x24 : ℝ) : (((x02 + ((-1) * x24)) ≥ 1) ∨ ((x02 + ((-1) * x04)) ≤ 0) ∨ (¬ (x24 ≤ x04)) ∨ (¬ (x04 ≤ x02)) ∨ (¬ ((x02 - x24) ≥ 1)) ∨ (¬ ((x02 - x04) ≤ (t - 1))) ∨ (¬ ((x04 - x24) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x02 + ((-1) * x24)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x02 + ((-1) * x04)) ≤ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x24 ≤ x04) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x04 ≤ x02) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x02 - x24) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x02 - x04) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x04 - x24) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th84 t x02 x04 x24
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 (hh).1) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause1345 (t x02 x04 x24 : ℝ) : (((x02 + ((-1) * x24)) ≥ 1) ∨ ((x04 + ((-1) * x24)) ≤ 0) ∨ (¬ (x24 ≤ x04)) ∨ (¬ (x04 ≤ x02)) ∨ (¬ ((x02 - x24) ≥ 1)) ∨ (¬ ((x02 - x04) ≤ (t - 1))) ∨ (¬ ((x04 - x24) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x02 + ((-1) * x24)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x04 + ((-1) * x24)) ≤ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x24 ≤ x04) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x04 ≤ x02) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x02 - x24) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x02 - x04) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x04 - x24) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th84 t x02 x04 x24
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 ((hh).2).1) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause1347 (t x02 x04 x24 : ℝ) : (((x04 + ((-1) * x24)) ≤ 0) ∨ ((t + ((-1) * x04) + x24) ≥ 1) ∨ (¬ (x24 ≤ x04)) ∨ (¬ (x04 ≤ x02)) ∨ (¬ ((x02 - x24) ≥ 1)) ∨ (¬ ((x02 - x04) ≤ (t - 1))) ∨ (¬ ((x04 - x24) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x04 + ((-1) * x24)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + ((-1) * x04) + x24) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x24 ≤ x04) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x04 ≤ x02) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x02 - x24) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x02 - x04) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x04 - x24) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th84 t x02 x04 x24
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause1348 (t x02 x04 x24 : ℝ) : (((x02 + ((-1) * x24)) ≤ (-1)) ∨ ((x04 + ((-1) * x24)) ≥ 0) ∨ (¬ (x24 ≤ x04)) ∨ (¬ (x04 ≤ x02)) ∨ (¬ ((x02 - x24) ≥ 1)) ∨ (¬ ((x02 - x04) ≤ (t - 1))) ∨ (¬ ((x04 - x24) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x02 + ((-1) * x24)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x04 + ((-1) * x24)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x24 ≤ x04) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x04 ≤ x02) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x02 - x24) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x02 - x04) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x04 - x24) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th84 t x02 x04 x24
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause1349 (t x02 x04 x24 : ℝ) : (((x02 + ((-1) * x24)) ≤ (-1)) ∨ ((x02 + ((-1) * x04)) ≥ 0) ∨ (¬ (x24 ≤ x04)) ∨ (¬ (x04 ≤ x02)) ∨ (¬ ((x02 - x24) ≥ 1)) ∨ (¬ ((x02 - x04) ≤ (t - 1))) ∨ (¬ ((x04 - x24) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x02 + ((-1) * x24)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x02 + ((-1) * x04)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x24 ≤ x04) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x04 ≤ x02) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x02 - x24) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x02 - x04) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x04 - x24) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th84 t x02 x04 x24
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause1350 (t x02 x04 x24 : ℝ) : (((x02 + ((-1) * x24)) ≤ (-1)) ∨ ((x02 + ((-1) * x24)) ≥ 1) ∨ (¬ (x24 ≤ x04)) ∨ (¬ (x04 ≤ x02)) ∨ (¬ ((x02 - x24) ≥ 1)) ∨ (¬ ((x02 - x04) ≤ (t - 1))) ∨ (¬ ((x04 - x24) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x02 + ((-1) * x24)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x02 + ((-1) * x24)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x24 ≤ x04) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x04 ≤ x02) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x02 - x24) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x02 - x04) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x04 - x24) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th84 t x02 x04 x24
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause1351 (t x02 x04 x24 : ℝ) : (((x02 + ((-1) * x24)) ≤ (-1)) ∨ ((t + ((-1) * x02) + x04) ≥ 1) ∨ (¬ (x24 ≤ x04)) ∨ (¬ (x04 ≤ x02)) ∨ (¬ ((x02 - x24) ≥ 1)) ∨ (¬ ((x02 - x04) ≤ (t - 1))) ∨ (¬ ((x04 - x24) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x02 + ((-1) * x24)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + ((-1) * x02) + x04) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x24 ≤ x04) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x04 ≤ x02) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x02 - x24) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x02 - x04) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x04 - x24) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th84 t x02 x04 x24
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause1352 (t x02 x04 x24 : ℝ) : (((x02 + ((-1) * x24)) ≤ (-1)) ∨ ((t + ((-1) * x04) + x24) ≥ 1) ∨ (¬ (x24 ≤ x04)) ∨ (¬ (x04 ≤ x02)) ∨ (¬ ((x02 - x24) ≥ 1)) ∨ (¬ ((x02 - x04) ≤ (t - 1))) ∨ (¬ ((x04 - x24) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x02 + ((-1) * x24)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + ((-1) * x04) + x24) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x24 ≤ x04) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x04 ≤ x02) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x02 - x24) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x02 - x04) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x04 - x24) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th84 t x02 x04 x24
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause1360 (t x02 x04 x24 : ℝ) : (((x02 + ((-1) * x24)) ≥ 1) ∨ ((t + x04 + ((-1) * x24)) ≥ 1) ∨ (¬ (x24 ≤ x04)) ∨ (¬ (x04 ≤ x02)) ∨ (¬ ((x02 - x24) ≥ 1)) ∨ (¬ ((x02 - x04) ≤ (t - 1))) ∨ (¬ ((x04 - x24) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x02 + ((-1) * x24)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + x04 + ((-1) * x24)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x24 ≤ x04) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x04 ≤ x02) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x02 - x24) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x02 - x04) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x04 - x24) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th84 t x02 x04 x24
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 ((((hh).2).2).2).2) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause1413 (t x02 x04 x24 : ℝ) (h : (((x02 ≤ x04) ∧ (x04 ≤ x24) ∧ ((x24 - x02) ≥ 1) ∧ ((x04 - x02) ≤ (t - 1)) ∧ ((x24 - x04) ≤ (t - 1))) ∨ ((x24 ≤ x04) ∧ (x04 ≤ x02) ∧ ((x02 - x24) ≥ 1) ∧ ((x02 - x04) ≤ (t - 1)) ∧ ((x04 - x24) ≤ (t - 1))))) : ((x02 ≤ x04) ∨ (x24 ≤ x04)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x02 ≤ x04) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x24 ≤ x04) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause1414 (t x02 x04 x24 : ℝ) (h : (((x02 ≤ x04) ∧ (x04 ≤ x24) ∧ ((x24 - x02) ≥ 1) ∧ ((x04 - x02) ≤ (t - 1)) ∧ ((x24 - x04) ≤ (t - 1))) ∨ ((x24 ≤ x04) ∧ (x04 ≤ x02) ∧ ((x02 - x24) ≥ 1) ∧ ((x02 - x04) ≤ (t - 1)) ∧ ((x04 - x24) ≤ (t - 1))))) : ((x02 ≤ x04) ∨ (x04 ≤ x02)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x02 ≤ x04) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x04 ≤ x02) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause1415 (t x02 x04 x24 : ℝ) (h : (((x02 ≤ x04) ∧ (x04 ≤ x24) ∧ ((x24 - x02) ≥ 1) ∧ ((x04 - x02) ≤ (t - 1)) ∧ ((x24 - x04) ≤ (t - 1))) ∨ ((x24 ≤ x04) ∧ (x04 ≤ x02) ∧ ((x02 - x24) ≥ 1) ∧ ((x02 - x04) ≤ (t - 1)) ∧ ((x04 - x24) ≤ (t - 1))))) : ((x02 ≤ x04) ∨ ((x02 - x24) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x02 ≤ x04) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x02 - x24) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause1416 (t x02 x04 x24 : ℝ) (h : (((x02 ≤ x04) ∧ (x04 ≤ x24) ∧ ((x24 - x02) ≥ 1) ∧ ((x04 - x02) ≤ (t - 1)) ∧ ((x24 - x04) ≤ (t - 1))) ∨ ((x24 ≤ x04) ∧ (x04 ≤ x02) ∧ ((x02 - x24) ≥ 1) ∧ ((x02 - x04) ≤ (t - 1)) ∧ ((x04 - x24) ≤ (t - 1))))) : ((x02 ≤ x04) ∨ ((x02 - x04) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x02 ≤ x04) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x02 - x04) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause1417 (t x02 x04 x24 : ℝ) (h : (((x02 ≤ x04) ∧ (x04 ≤ x24) ∧ ((x24 - x02) ≥ 1) ∧ ((x04 - x02) ≤ (t - 1)) ∧ ((x24 - x04) ≤ (t - 1))) ∨ ((x24 ≤ x04) ∧ (x04 ≤ x02) ∧ ((x02 - x24) ≥ 1) ∧ ((x02 - x04) ≤ (t - 1)) ∧ ((x04 - x24) ≤ (t - 1))))) : ((x02 ≤ x04) ∨ ((x04 - x24) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x02 ≤ x04) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x04 - x24) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause1418 (t x02 x04 x24 : ℝ) (h : (((x02 ≤ x04) ∧ (x04 ≤ x24) ∧ ((x24 - x02) ≥ 1) ∧ ((x04 - x02) ≤ (t - 1)) ∧ ((x24 - x04) ≤ (t - 1))) ∨ ((x24 ≤ x04) ∧ (x04 ≤ x02) ∧ ((x02 - x24) ≥ 1) ∧ ((x02 - x04) ≤ (t - 1)) ∧ ((x04 - x24) ≤ (t - 1))))) : ((x04 ≤ x24) ∨ (x24 ≤ x04)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x04 ≤ x24) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x24 ≤ x04) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause1419 (t x02 x04 x24 : ℝ) (h : (((x02 ≤ x04) ∧ (x04 ≤ x24) ∧ ((x24 - x02) ≥ 1) ∧ ((x04 - x02) ≤ (t - 1)) ∧ ((x24 - x04) ≤ (t - 1))) ∨ ((x24 ≤ x04) ∧ (x04 ≤ x02) ∧ ((x02 - x24) ≥ 1) ∧ ((x02 - x04) ≤ (t - 1)) ∧ ((x04 - x24) ≤ (t - 1))))) : ((x04 ≤ x24) ∨ (x04 ≤ x02)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x04 ≤ x24) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x04 ≤ x02) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause1420 (t x02 x04 x24 : ℝ) (h : (((x02 ≤ x04) ∧ (x04 ≤ x24) ∧ ((x24 - x02) ≥ 1) ∧ ((x04 - x02) ≤ (t - 1)) ∧ ((x24 - x04) ≤ (t - 1))) ∨ ((x24 ≤ x04) ∧ (x04 ≤ x02) ∧ ((x02 - x24) ≥ 1) ∧ ((x02 - x04) ≤ (t - 1)) ∧ ((x04 - x24) ≤ (t - 1))))) : ((x04 ≤ x24) ∨ ((x02 - x24) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x04 ≤ x24) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x02 - x24) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause1421 (t x02 x04 x24 : ℝ) (h : (((x02 ≤ x04) ∧ (x04 ≤ x24) ∧ ((x24 - x02) ≥ 1) ∧ ((x04 - x02) ≤ (t - 1)) ∧ ((x24 - x04) ≤ (t - 1))) ∨ ((x24 ≤ x04) ∧ (x04 ≤ x02) ∧ ((x02 - x24) ≥ 1) ∧ ((x02 - x04) ≤ (t - 1)) ∧ ((x04 - x24) ≤ (t - 1))))) : ((x04 ≤ x24) ∨ ((x02 - x04) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x04 ≤ x24) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x02 - x04) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause1422 (t x02 x04 x24 : ℝ) (h : (((x02 ≤ x04) ∧ (x04 ≤ x24) ∧ ((x24 - x02) ≥ 1) ∧ ((x04 - x02) ≤ (t - 1)) ∧ ((x24 - x04) ≤ (t - 1))) ∨ ((x24 ≤ x04) ∧ (x04 ≤ x02) ∧ ((x02 - x24) ≥ 1) ∧ ((x02 - x04) ≤ (t - 1)) ∧ ((x04 - x24) ≤ (t - 1))))) : ((x04 ≤ x24) ∨ ((x04 - x24) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x04 ≤ x24) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x04 - x24) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause1423 (t x02 x04 x24 : ℝ) (h : (((x02 ≤ x04) ∧ (x04 ≤ x24) ∧ ((x24 - x02) ≥ 1) ∧ ((x04 - x02) ≤ (t - 1)) ∧ ((x24 - x04) ≤ (t - 1))) ∨ ((x24 ≤ x04) ∧ (x04 ≤ x02) ∧ ((x02 - x24) ≥ 1) ∧ ((x02 - x04) ≤ (t - 1)) ∧ ((x04 - x24) ≤ (t - 1))))) : (((x24 - x02) ≥ 1) ∨ (x24 ≤ x04)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x24 - x02) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x24 ≤ x04) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause1424 (t x02 x04 x24 : ℝ) (h : (((x02 ≤ x04) ∧ (x04 ≤ x24) ∧ ((x24 - x02) ≥ 1) ∧ ((x04 - x02) ≤ (t - 1)) ∧ ((x24 - x04) ≤ (t - 1))) ∨ ((x24 ≤ x04) ∧ (x04 ≤ x02) ∧ ((x02 - x24) ≥ 1) ∧ ((x02 - x04) ≤ (t - 1)) ∧ ((x04 - x24) ≤ (t - 1))))) : (((x24 - x02) ≥ 1) ∨ (x04 ≤ x02)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x24 - x02) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x04 ≤ x02) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause1425 (t x02 x04 x24 : ℝ) (h : (((x02 ≤ x04) ∧ (x04 ≤ x24) ∧ ((x24 - x02) ≥ 1) ∧ ((x04 - x02) ≤ (t - 1)) ∧ ((x24 - x04) ≤ (t - 1))) ∨ ((x24 ≤ x04) ∧ (x04 ≤ x02) ∧ ((x02 - x24) ≥ 1) ∧ ((x02 - x04) ≤ (t - 1)) ∧ ((x04 - x24) ≤ (t - 1))))) : (((x24 - x02) ≥ 1) ∨ ((x02 - x24) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x24 - x02) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x02 - x24) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause1426 (t x02 x04 x24 : ℝ) (h : (((x02 ≤ x04) ∧ (x04 ≤ x24) ∧ ((x24 - x02) ≥ 1) ∧ ((x04 - x02) ≤ (t - 1)) ∧ ((x24 - x04) ≤ (t - 1))) ∨ ((x24 ≤ x04) ∧ (x04 ≤ x02) ∧ ((x02 - x24) ≥ 1) ∧ ((x02 - x04) ≤ (t - 1)) ∧ ((x04 - x24) ≤ (t - 1))))) : (((x24 - x02) ≥ 1) ∨ ((x02 - x04) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x24 - x02) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x02 - x04) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause1427 (t x02 x04 x24 : ℝ) (h : (((x02 ≤ x04) ∧ (x04 ≤ x24) ∧ ((x24 - x02) ≥ 1) ∧ ((x04 - x02) ≤ (t - 1)) ∧ ((x24 - x04) ≤ (t - 1))) ∨ ((x24 ≤ x04) ∧ (x04 ≤ x02) ∧ ((x02 - x24) ≥ 1) ∧ ((x02 - x04) ≤ (t - 1)) ∧ ((x04 - x24) ≤ (t - 1))))) : (((x24 - x02) ≥ 1) ∨ ((x04 - x24) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x24 - x02) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x04 - x24) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause1428 (t x02 x04 x24 : ℝ) (h : (((x02 ≤ x04) ∧ (x04 ≤ x24) ∧ ((x24 - x02) ≥ 1) ∧ ((x04 - x02) ≤ (t - 1)) ∧ ((x24 - x04) ≤ (t - 1))) ∨ ((x24 ≤ x04) ∧ (x04 ≤ x02) ∧ ((x02 - x24) ≥ 1) ∧ ((x02 - x04) ≤ (t - 1)) ∧ ((x04 - x24) ≤ (t - 1))))) : (((x04 - x02) ≤ (t - 1)) ∨ (x24 ≤ x04)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x04 - x02) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x24 ≤ x04) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause1429 (t x02 x04 x24 : ℝ) (h : (((x02 ≤ x04) ∧ (x04 ≤ x24) ∧ ((x24 - x02) ≥ 1) ∧ ((x04 - x02) ≤ (t - 1)) ∧ ((x24 - x04) ≤ (t - 1))) ∨ ((x24 ≤ x04) ∧ (x04 ≤ x02) ∧ ((x02 - x24) ≥ 1) ∧ ((x02 - x04) ≤ (t - 1)) ∧ ((x04 - x24) ≤ (t - 1))))) : (((x04 - x02) ≤ (t - 1)) ∨ (x04 ≤ x02)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x04 - x02) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x04 ≤ x02) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause1430 (t x02 x04 x24 : ℝ) (h : (((x02 ≤ x04) ∧ (x04 ≤ x24) ∧ ((x24 - x02) ≥ 1) ∧ ((x04 - x02) ≤ (t - 1)) ∧ ((x24 - x04) ≤ (t - 1))) ∨ ((x24 ≤ x04) ∧ (x04 ≤ x02) ∧ ((x02 - x24) ≥ 1) ∧ ((x02 - x04) ≤ (t - 1)) ∧ ((x04 - x24) ≤ (t - 1))))) : (((x04 - x02) ≤ (t - 1)) ∨ ((x02 - x24) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x04 - x02) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x02 - x24) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause1431 (t x02 x04 x24 : ℝ) (h : (((x02 ≤ x04) ∧ (x04 ≤ x24) ∧ ((x24 - x02) ≥ 1) ∧ ((x04 - x02) ≤ (t - 1)) ∧ ((x24 - x04) ≤ (t - 1))) ∨ ((x24 ≤ x04) ∧ (x04 ≤ x02) ∧ ((x02 - x24) ≥ 1) ∧ ((x02 - x04) ≤ (t - 1)) ∧ ((x04 - x24) ≤ (t - 1))))) : (((x04 - x02) ≤ (t - 1)) ∨ ((x02 - x04) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x04 - x02) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x02 - x04) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause1432 (t x02 x04 x24 : ℝ) (h : (((x02 ≤ x04) ∧ (x04 ≤ x24) ∧ ((x24 - x02) ≥ 1) ∧ ((x04 - x02) ≤ (t - 1)) ∧ ((x24 - x04) ≤ (t - 1))) ∨ ((x24 ≤ x04) ∧ (x04 ≤ x02) ∧ ((x02 - x24) ≥ 1) ∧ ((x02 - x04) ≤ (t - 1)) ∧ ((x04 - x24) ≤ (t - 1))))) : (((x04 - x02) ≤ (t - 1)) ∨ ((x04 - x24) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x04 - x02) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x04 - x24) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause1433 (t x02 x04 x24 : ℝ) (h : (((x02 ≤ x04) ∧ (x04 ≤ x24) ∧ ((x24 - x02) ≥ 1) ∧ ((x04 - x02) ≤ (t - 1)) ∧ ((x24 - x04) ≤ (t - 1))) ∨ ((x24 ≤ x04) ∧ (x04 ≤ x02) ∧ ((x02 - x24) ≥ 1) ∧ ((x02 - x04) ≤ (t - 1)) ∧ ((x04 - x24) ≤ (t - 1))))) : (((x24 - x04) ≤ (t - 1)) ∨ (x24 ≤ x04)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x24 - x04) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x24 ≤ x04) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause1434 (t x02 x04 x24 : ℝ) (h : (((x02 ≤ x04) ∧ (x04 ≤ x24) ∧ ((x24 - x02) ≥ 1) ∧ ((x04 - x02) ≤ (t - 1)) ∧ ((x24 - x04) ≤ (t - 1))) ∨ ((x24 ≤ x04) ∧ (x04 ≤ x02) ∧ ((x02 - x24) ≥ 1) ∧ ((x02 - x04) ≤ (t - 1)) ∧ ((x04 - x24) ≤ (t - 1))))) : (((x24 - x04) ≤ (t - 1)) ∨ (x04 ≤ x02)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x24 - x04) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x04 ≤ x02) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause1435 (t x02 x04 x24 : ℝ) (h : (((x02 ≤ x04) ∧ (x04 ≤ x24) ∧ ((x24 - x02) ≥ 1) ∧ ((x04 - x02) ≤ (t - 1)) ∧ ((x24 - x04) ≤ (t - 1))) ∨ ((x24 ≤ x04) ∧ (x04 ≤ x02) ∧ ((x02 - x24) ≥ 1) ∧ ((x02 - x04) ≤ (t - 1)) ∧ ((x04 - x24) ≤ (t - 1))))) : (((x24 - x04) ≤ (t - 1)) ∨ ((x02 - x24) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x24 - x04) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x02 - x24) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause1436 (t x02 x04 x24 : ℝ) (h : (((x02 ≤ x04) ∧ (x04 ≤ x24) ∧ ((x24 - x02) ≥ 1) ∧ ((x04 - x02) ≤ (t - 1)) ∧ ((x24 - x04) ≤ (t - 1))) ∨ ((x24 ≤ x04) ∧ (x04 ≤ x02) ∧ ((x02 - x24) ≥ 1) ∧ ((x02 - x04) ≤ (t - 1)) ∧ ((x04 - x24) ≤ (t - 1))))) : (((x24 - x04) ≤ (t - 1)) ∨ ((x02 - x04) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x24 - x04) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x02 - x04) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause1437 (t x02 x04 x24 : ℝ) (h : (((x02 ≤ x04) ∧ (x04 ≤ x24) ∧ ((x24 - x02) ≥ 1) ∧ ((x04 - x02) ≤ (t - 1)) ∧ ((x24 - x04) ≤ (t - 1))) ∨ ((x24 ≤ x04) ∧ (x04 ≤ x02) ∧ ((x02 - x24) ≥ 1) ∧ ((x02 - x04) ≤ (t - 1)) ∧ ((x04 - x24) ≤ (t - 1))))) : (((x24 - x04) ≤ (t - 1)) ∨ ((x04 - x24) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x24 - x04) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x04 - x24) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause1438 (t x02 x23 x24 x34 x45 x46 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x34 + ((-1) * x46)) ≤ (-1))) ∨ (¬ ((x34 + ((-1) * x45)) ≥ 1)) ∨ (¬ ((x23 + ((-1) * x24)) ≤ 0)) ∨ (¬ ((x02 + ((-1) * x23)) ≤ (-1))) ∨ (¬ ((x24 + ((-1) * x45)) ≤ (-1))) ∨ (¬ (x02 ≥ 0)) ∨ ((t + ((-1) * x46)) ≤ 0)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x34 + ((-1) * x46)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x34 + ((-1) * x45)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x23 + ((-1) * x24)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x02 + ((-1) * x23)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x24 + ((-1) * x45)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : (x02 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))))
  have u7 : ¬ ((t + ((-1) * x46)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))
  have h := NineTheoryTrial.th86 t x02 x23 x24 x34 x45 x46
  exact (fun hh => (fun hh => hh) (hh (And.intro u6 (And.intro u0 (And.intro u1 (And.intro u4 (And.intro u5 (And.intro u3 (And.intro u2 u7))))))))) h

theorem clause1439 (t x46 : ℝ) : ((¬ ((t + ((-1) * x46)) ≤ 0)) ∨ (t ≤ x46)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((t + ((-1) * x46)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ¬ (t ≤ x46) := fun hh => hn (Or.inr hh)
  have h := NineTheoryTrial.th87 t x46
  exact (fun hh => (fun hh => hh u0) (hh.mp u1)) h

theorem clause1441 (t x46 : ℝ) : ((¬ (t ≤ x46)) ∨ (¬ (x46 < t))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (t ≤ x46) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : (x46 < t) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr hh)
  have h := NineTheoryTrial.th88 t x46
  exact (fun hh => (fun hh => hh u0) (hh.mp u1)) h

theorem clause1443 (t x46 : ℝ) (h : (x46 < t)) : ((x46 < t)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x46 < t) := fun hh => hn hh
  exact u0 h

theorem clause1444 (x02 : ℝ) (h : (x02 ≥ 0)) : ((x02 ≥ 0)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x02 ≥ 0) := fun hh => hn hh
  exact u0 h

theorem clause1445 (x24 x34 x45 : ℝ) : ((¬ ((x34 + ((-1) * x45)) ≥ 1)) ∨ (¬ ((x24 + ((-1) * x34)) ≥ 0)) ∨ (¬ ((x24 + ((-1) * x45)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x34 + ((-1) * x45)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x24 + ((-1) * x34)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x24 + ((-1) * x45)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th91 x24 x34 x45
  exact (fun hh => (fun hh => hh) (hh (And.intro u0 (And.intro u1 u2)))) h

theorem clause1448 (t x24 x25 x45 : ℝ) : (((x24 + ((-1) * x25)) ≤ 0) ∨ ((x24 + ((-1) * x45)) ≥ 1) ∨ (¬ (x24 ≤ x25)) ∨ (¬ (x25 ≤ x45)) ∨ (¬ ((x45 - x24) ≥ 1)) ∨ (¬ ((x25 - x24) ≤ (t - 1))) ∨ (¬ ((x45 - x25) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x24 + ((-1) * x25)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x24 + ((-1) * x45)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x24 ≤ x25) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x25 ≤ x45) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x45 - x24) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x25 - x24) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x45 - x25) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th93 t x24 x25 x45
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause1453 (t x24 x25 x45 : ℝ) : (((x25 + ((-1) * x45)) ≤ 0) ∨ ((x24 + ((-1) * x45)) ≥ 1) ∨ (¬ (x24 ≤ x25)) ∨ (¬ (x25 ≤ x45)) ∨ (¬ ((x45 - x24) ≥ 1)) ∨ (¬ ((x25 - x24) ≤ (t - 1))) ∨ (¬ ((x45 - x25) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x25 + ((-1) * x45)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x24 + ((-1) * x45)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x24 ≤ x25) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x25 ≤ x45) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x45 - x24) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x25 - x24) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x45 - x25) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th93 t x24 x25 x45
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause1456 (t x24 x25 x45 : ℝ) : (((x24 + ((-1) * x45)) ≤ (-1)) ∨ ((x25 + ((-1) * x45)) ≥ 0) ∨ (¬ (x24 ≤ x25)) ∨ (¬ (x25 ≤ x45)) ∨ (¬ ((x45 - x24) ≥ 1)) ∨ (¬ ((x25 - x24) ≤ (t - 1))) ∨ (¬ ((x45 - x25) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x24 + ((-1) * x45)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x25 + ((-1) * x45)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x24 ≤ x25) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x25 ≤ x45) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x45 - x24) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x25 - x24) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x45 - x25) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th93 t x24 x25 x45
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause1457 (t x24 x25 x45 : ℝ) : (((x24 + ((-1) * x45)) ≤ (-1)) ∨ ((x24 + ((-1) * x25)) ≥ 0) ∨ (¬ (x24 ≤ x25)) ∨ (¬ (x25 ≤ x45)) ∨ (¬ ((x45 - x24) ≥ 1)) ∨ (¬ ((x25 - x24) ≤ (t - 1))) ∨ (¬ ((x45 - x25) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x24 + ((-1) * x45)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x24 + ((-1) * x25)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x24 ≤ x25) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x25 ≤ x45) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x45 - x24) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x25 - x24) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x45 - x25) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th93 t x24 x25 x45
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause1458 (t x24 x25 x45 : ℝ) : (((x24 + ((-1) * x45)) ≤ (-1)) ∨ ((x24 + ((-1) * x45)) ≥ 1) ∨ (¬ (x24 ≤ x25)) ∨ (¬ (x25 ≤ x45)) ∨ (¬ ((x45 - x24) ≥ 1)) ∨ (¬ ((x25 - x24) ≤ (t - 1))) ∨ (¬ ((x45 - x25) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x24 + ((-1) * x45)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x24 + ((-1) * x45)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x24 ≤ x25) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x25 ≤ x45) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x45 - x24) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x25 - x24) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x45 - x25) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th93 t x24 x25 x45
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause1459 (t x24 x25 x45 : ℝ) : (((x24 + ((-1) * x45)) ≤ (-1)) ∨ ((t + ((-1) * x24) + x25) ≥ 1) ∨ (¬ (x24 ≤ x25)) ∨ (¬ (x25 ≤ x45)) ∨ (¬ ((x45 - x24) ≥ 1)) ∨ (¬ ((x25 - x24) ≤ (t - 1))) ∨ (¬ ((x45 - x25) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x24 + ((-1) * x45)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + ((-1) * x24) + x25) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x24 ≤ x25) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x25 ≤ x45) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x45 - x24) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x25 - x24) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x45 - x25) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th93 t x24 x25 x45
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause1460 (t x24 x25 x45 : ℝ) : (((x24 + ((-1) * x45)) ≤ (-1)) ∨ ((t + ((-1) * x25) + x45) ≥ 1) ∨ (¬ (x24 ≤ x25)) ∨ (¬ (x25 ≤ x45)) ∨ (¬ ((x45 - x24) ≥ 1)) ∨ (¬ ((x25 - x24) ≤ (t - 1))) ∨ (¬ ((x45 - x25) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x24 + ((-1) * x45)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + ((-1) * x25) + x45) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x24 ≤ x25) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x25 ≤ x45) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x45 - x24) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x25 - x24) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x45 - x25) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th93 t x24 x25 x45
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause1462 (t x24 x25 x45 : ℝ) : (((t + x24 + ((-1) * x25)) ≥ 1) ∨ ((x24 + ((-1) * x25)) ≥ 0) ∨ (¬ (x24 ≤ x25)) ∨ (¬ (x25 ≤ x45)) ∨ (¬ ((x45 - x24) ≥ 1)) ∨ (¬ ((x25 - x24) ≤ (t - 1))) ∨ (¬ ((x45 - x25) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((t + x24 + ((-1) * x25)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x24 + ((-1) * x25)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x24 ≤ x25) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x25 ≤ x45) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x45 - x24) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x25 - x24) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x45 - x25) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th93 t x24 x25 x45
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause1466 (t x24 x25 x45 : ℝ) : (((t + x25 + ((-1) * x45)) ≥ 1) ∨ ((x25 + ((-1) * x45)) ≥ 0) ∨ (¬ (x24 ≤ x25)) ∨ (¬ (x25 ≤ x45)) ∨ (¬ ((x45 - x24) ≥ 1)) ∨ (¬ ((x25 - x24) ≤ (t - 1))) ∨ (¬ ((x45 - x25) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((t + x25 + ((-1) * x45)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x25 + ((-1) * x45)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x24 ≤ x25) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x25 ≤ x45) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x45 - x24) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x25 - x24) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x45 - x25) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th93 t x24 x25 x45
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 (hh).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause1468 (t x24 x25 x45 : ℝ) : (((t + x25 + ((-1) * x45)) ≥ 1) ∨ ((x24 + ((-1) * x45)) ≥ 1) ∨ (¬ (x24 ≤ x25)) ∨ (¬ (x25 ≤ x45)) ∨ (¬ ((x45 - x24) ≥ 1)) ∨ (¬ ((x25 - x24) ≤ (t - 1))) ∨ (¬ ((x45 - x25) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((t + x25 + ((-1) * x45)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x24 + ((-1) * x45)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x24 ≤ x25) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x25 ≤ x45) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x45 - x24) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x25 - x24) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x45 - x25) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th93 t x24 x25 x45
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause1473 (t x24 x25 x45 : ℝ) : (((x24 + ((-1) * x25)) ≤ 0) ∨ ((x24 + ((-1) * x45)) ≥ 1) ∨ (¬ (x45 ≤ x25)) ∨ (¬ (x25 ≤ x24)) ∨ (¬ ((x24 - x45) ≥ 1)) ∨ (¬ ((x24 - x25) ≤ (t - 1))) ∨ (¬ ((x25 - x45) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x24 + ((-1) * x25)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x24 + ((-1) * x45)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x45 ≤ x25) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x25 ≤ x24) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x24 - x45) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x24 - x25) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x25 - x45) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th93 t x24 x25 x45
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause1474 (t x24 x25 x45 : ℝ) : (((x24 + ((-1) * x25)) ≤ 0) ∨ ((t + ((-1) * x24) + x25) ≥ 1) ∨ (¬ (x45 ≤ x25)) ∨ (¬ (x25 ≤ x24)) ∨ (¬ ((x24 - x45) ≥ 1)) ∨ (¬ ((x24 - x25) ≤ (t - 1))) ∨ (¬ ((x25 - x45) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x24 + ((-1) * x25)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + ((-1) * x24) + x25) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x45 ≤ x25) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x25 ≤ x24) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x24 - x45) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x24 - x25) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x25 - x45) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th93 t x24 x25 x45
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause1477 (t x24 x25 x45 : ℝ) : (((x25 + ((-1) * x45)) ≤ 0) ∨ ((x24 + ((-1) * x25)) ≥ 0) ∨ (¬ (x45 ≤ x25)) ∨ (¬ (x25 ≤ x24)) ∨ (¬ ((x24 - x45) ≥ 1)) ∨ (¬ ((x24 - x25) ≤ (t - 1))) ∨ (¬ ((x25 - x45) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x25 + ((-1) * x45)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x24 + ((-1) * x25)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x45 ≤ x25) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x25 ≤ x24) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x24 - x45) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x24 - x25) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x25 - x45) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th93 t x24 x25 x45
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause1478 (t x24 x25 x45 : ℝ) : (((x25 + ((-1) * x45)) ≤ 0) ∨ ((x24 + ((-1) * x45)) ≥ 1) ∨ (¬ (x45 ≤ x25)) ∨ (¬ (x25 ≤ x24)) ∨ (¬ ((x24 - x45) ≥ 1)) ∨ (¬ ((x24 - x25) ≤ (t - 1))) ∨ (¬ ((x25 - x45) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x25 + ((-1) * x45)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x24 + ((-1) * x45)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x45 ≤ x25) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x25 ≤ x24) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x24 - x45) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x24 - x25) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x25 - x45) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th93 t x24 x25 x45
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause1480 (t x24 x25 x45 : ℝ) : (((x25 + ((-1) * x45)) ≤ 0) ∨ ((t + ((-1) * x25) + x45) ≥ 1) ∨ (¬ (x45 ≤ x25)) ∨ (¬ (x25 ≤ x24)) ∨ (¬ ((x24 - x45) ≥ 1)) ∨ (¬ ((x24 - x25) ≤ (t - 1))) ∨ (¬ ((x25 - x45) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x25 + ((-1) * x45)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + ((-1) * x25) + x45) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x45 ≤ x25) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x25 ≤ x24) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x24 - x45) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x24 - x25) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x25 - x45) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th93 t x24 x25 x45
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause1481 (t x24 x25 x45 : ℝ) : (((x24 + ((-1) * x45)) ≤ (-1)) ∨ ((x25 + ((-1) * x45)) ≥ 0) ∨ (¬ (x45 ≤ x25)) ∨ (¬ (x25 ≤ x24)) ∨ (¬ ((x24 - x45) ≥ 1)) ∨ (¬ ((x24 - x25) ≤ (t - 1))) ∨ (¬ ((x25 - x45) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x24 + ((-1) * x45)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x25 + ((-1) * x45)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x45 ≤ x25) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x25 ≤ x24) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x24 - x45) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x24 - x25) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x25 - x45) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th93 t x24 x25 x45
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause1482 (t x24 x25 x45 : ℝ) : (((x24 + ((-1) * x45)) ≤ (-1)) ∨ ((x24 + ((-1) * x25)) ≥ 0) ∨ (¬ (x45 ≤ x25)) ∨ (¬ (x25 ≤ x24)) ∨ (¬ ((x24 - x45) ≥ 1)) ∨ (¬ ((x24 - x25) ≤ (t - 1))) ∨ (¬ ((x25 - x45) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x24 + ((-1) * x45)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x24 + ((-1) * x25)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x45 ≤ x25) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x25 ≤ x24) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x24 - x45) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x24 - x25) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x25 - x45) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th93 t x24 x25 x45
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause1483 (t x24 x25 x45 : ℝ) : (((x24 + ((-1) * x45)) ≤ (-1)) ∨ ((x24 + ((-1) * x45)) ≥ 1) ∨ (¬ (x45 ≤ x25)) ∨ (¬ (x25 ≤ x24)) ∨ (¬ ((x24 - x45) ≥ 1)) ∨ (¬ ((x24 - x25) ≤ (t - 1))) ∨ (¬ ((x25 - x45) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x24 + ((-1) * x45)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x24 + ((-1) * x45)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x45 ≤ x25) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x25 ≤ x24) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x24 - x45) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x24 - x25) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x25 - x45) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th93 t x24 x25 x45
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause1485 (t x24 x25 x45 : ℝ) : (((x24 + ((-1) * x45)) ≤ (-1)) ∨ ((t + ((-1) * x25) + x45) ≥ 1) ∨ (¬ (x45 ≤ x25)) ∨ (¬ (x25 ≤ x24)) ∨ (¬ ((x24 - x45) ≥ 1)) ∨ (¬ ((x24 - x25) ≤ (t - 1))) ∨ (¬ ((x25 - x45) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x24 + ((-1) * x45)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + ((-1) * x25) + x45) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x45 ≤ x25) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x25 ≤ x24) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x24 - x45) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x24 - x25) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x25 - x45) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th93 t x24 x25 x45
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause1487 (t x24 x25 x45 : ℝ) : (((t + x24 + ((-1) * x25)) ≥ 1) ∨ ((x24 + ((-1) * x25)) ≥ 0) ∨ (¬ (x45 ≤ x25)) ∨ (¬ (x25 ≤ x24)) ∨ (¬ ((x24 - x45) ≥ 1)) ∨ (¬ ((x24 - x25) ≤ (t - 1))) ∨ (¬ ((x25 - x45) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((t + x24 + ((-1) * x25)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x24 + ((-1) * x25)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x45 ≤ x25) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x25 ≤ x24) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x24 - x45) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x24 - x25) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x25 - x45) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th93 t x24 x25 x45
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause1491 (t x24 x25 x45 : ℝ) : (((t + x25 + ((-1) * x45)) ≥ 1) ∨ ((x25 + ((-1) * x45)) ≥ 0) ∨ (¬ (x45 ≤ x25)) ∨ (¬ (x25 ≤ x24)) ∨ (¬ ((x24 - x45) ≥ 1)) ∨ (¬ ((x24 - x25) ≤ (t - 1))) ∨ (¬ ((x25 - x45) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((t + x25 + ((-1) * x45)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x25 + ((-1) * x45)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x45 ≤ x25) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x25 ≤ x24) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x24 - x45) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x24 - x25) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x25 - x45) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th93 t x24 x25 x45
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 (hh).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause1493 (t x24 x25 x45 : ℝ) : (((t + x25 + ((-1) * x45)) ≥ 1) ∨ ((x24 + ((-1) * x45)) ≥ 1) ∨ (¬ (x45 ≤ x25)) ∨ (¬ (x25 ≤ x24)) ∨ (¬ ((x24 - x45) ≥ 1)) ∨ (¬ ((x24 - x25) ≤ (t - 1))) ∨ (¬ ((x25 - x45) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((t + x25 + ((-1) * x45)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x24 + ((-1) * x45)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x45 ≤ x25) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x25 ≤ x24) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x24 - x45) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x24 - x25) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x25 - x45) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th93 t x24 x25 x45
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause1546 (t x24 x25 x45 : ℝ) (h : (((x24 ≤ x25) ∧ (x25 ≤ x45) ∧ ((x45 - x24) ≥ 1) ∧ ((x25 - x24) ≤ (t - 1)) ∧ ((x45 - x25) ≤ (t - 1))) ∨ ((x45 ≤ x25) ∧ (x25 ≤ x24) ∧ ((x24 - x45) ≥ 1) ∧ ((x24 - x25) ≤ (t - 1)) ∧ ((x25 - x45) ≤ (t - 1))))) : ((x24 ≤ x25) ∨ (x45 ≤ x25)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x24 ≤ x25) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x45 ≤ x25) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause1547 (t x24 x25 x45 : ℝ) (h : (((x24 ≤ x25) ∧ (x25 ≤ x45) ∧ ((x45 - x24) ≥ 1) ∧ ((x25 - x24) ≤ (t - 1)) ∧ ((x45 - x25) ≤ (t - 1))) ∨ ((x45 ≤ x25) ∧ (x25 ≤ x24) ∧ ((x24 - x45) ≥ 1) ∧ ((x24 - x25) ≤ (t - 1)) ∧ ((x25 - x45) ≤ (t - 1))))) : ((x24 ≤ x25) ∨ (x25 ≤ x24)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x24 ≤ x25) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x25 ≤ x24) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause1548 (t x24 x25 x45 : ℝ) (h : (((x24 ≤ x25) ∧ (x25 ≤ x45) ∧ ((x45 - x24) ≥ 1) ∧ ((x25 - x24) ≤ (t - 1)) ∧ ((x45 - x25) ≤ (t - 1))) ∨ ((x45 ≤ x25) ∧ (x25 ≤ x24) ∧ ((x24 - x45) ≥ 1) ∧ ((x24 - x25) ≤ (t - 1)) ∧ ((x25 - x45) ≤ (t - 1))))) : ((x24 ≤ x25) ∨ ((x24 - x45) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x24 ≤ x25) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x24 - x45) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause1549 (t x24 x25 x45 : ℝ) (h : (((x24 ≤ x25) ∧ (x25 ≤ x45) ∧ ((x45 - x24) ≥ 1) ∧ ((x25 - x24) ≤ (t - 1)) ∧ ((x45 - x25) ≤ (t - 1))) ∨ ((x45 ≤ x25) ∧ (x25 ≤ x24) ∧ ((x24 - x45) ≥ 1) ∧ ((x24 - x25) ≤ (t - 1)) ∧ ((x25 - x45) ≤ (t - 1))))) : ((x24 ≤ x25) ∨ ((x24 - x25) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x24 ≤ x25) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x24 - x25) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause1550 (t x24 x25 x45 : ℝ) (h : (((x24 ≤ x25) ∧ (x25 ≤ x45) ∧ ((x45 - x24) ≥ 1) ∧ ((x25 - x24) ≤ (t - 1)) ∧ ((x45 - x25) ≤ (t - 1))) ∨ ((x45 ≤ x25) ∧ (x25 ≤ x24) ∧ ((x24 - x45) ≥ 1) ∧ ((x24 - x25) ≤ (t - 1)) ∧ ((x25 - x45) ≤ (t - 1))))) : ((x24 ≤ x25) ∨ ((x25 - x45) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x24 ≤ x25) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x25 - x45) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause1551 (t x24 x25 x45 : ℝ) (h : (((x24 ≤ x25) ∧ (x25 ≤ x45) ∧ ((x45 - x24) ≥ 1) ∧ ((x25 - x24) ≤ (t - 1)) ∧ ((x45 - x25) ≤ (t - 1))) ∨ ((x45 ≤ x25) ∧ (x25 ≤ x24) ∧ ((x24 - x45) ≥ 1) ∧ ((x24 - x25) ≤ (t - 1)) ∧ ((x25 - x45) ≤ (t - 1))))) : ((x25 ≤ x45) ∨ (x45 ≤ x25)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x25 ≤ x45) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x45 ≤ x25) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause1552 (t x24 x25 x45 : ℝ) (h : (((x24 ≤ x25) ∧ (x25 ≤ x45) ∧ ((x45 - x24) ≥ 1) ∧ ((x25 - x24) ≤ (t - 1)) ∧ ((x45 - x25) ≤ (t - 1))) ∨ ((x45 ≤ x25) ∧ (x25 ≤ x24) ∧ ((x24 - x45) ≥ 1) ∧ ((x24 - x25) ≤ (t - 1)) ∧ ((x25 - x45) ≤ (t - 1))))) : ((x25 ≤ x45) ∨ (x25 ≤ x24)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x25 ≤ x45) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x25 ≤ x24) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause1553 (t x24 x25 x45 : ℝ) (h : (((x24 ≤ x25) ∧ (x25 ≤ x45) ∧ ((x45 - x24) ≥ 1) ∧ ((x25 - x24) ≤ (t - 1)) ∧ ((x45 - x25) ≤ (t - 1))) ∨ ((x45 ≤ x25) ∧ (x25 ≤ x24) ∧ ((x24 - x45) ≥ 1) ∧ ((x24 - x25) ≤ (t - 1)) ∧ ((x25 - x45) ≤ (t - 1))))) : ((x25 ≤ x45) ∨ ((x24 - x45) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x25 ≤ x45) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x24 - x45) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause1554 (t x24 x25 x45 : ℝ) (h : (((x24 ≤ x25) ∧ (x25 ≤ x45) ∧ ((x45 - x24) ≥ 1) ∧ ((x25 - x24) ≤ (t - 1)) ∧ ((x45 - x25) ≤ (t - 1))) ∨ ((x45 ≤ x25) ∧ (x25 ≤ x24) ∧ ((x24 - x45) ≥ 1) ∧ ((x24 - x25) ≤ (t - 1)) ∧ ((x25 - x45) ≤ (t - 1))))) : ((x25 ≤ x45) ∨ ((x24 - x25) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x25 ≤ x45) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x24 - x25) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause1555 (t x24 x25 x45 : ℝ) (h : (((x24 ≤ x25) ∧ (x25 ≤ x45) ∧ ((x45 - x24) ≥ 1) ∧ ((x25 - x24) ≤ (t - 1)) ∧ ((x45 - x25) ≤ (t - 1))) ∨ ((x45 ≤ x25) ∧ (x25 ≤ x24) ∧ ((x24 - x45) ≥ 1) ∧ ((x24 - x25) ≤ (t - 1)) ∧ ((x25 - x45) ≤ (t - 1))))) : ((x25 ≤ x45) ∨ ((x25 - x45) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x25 ≤ x45) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x25 - x45) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause1556 (t x24 x25 x45 : ℝ) (h : (((x24 ≤ x25) ∧ (x25 ≤ x45) ∧ ((x45 - x24) ≥ 1) ∧ ((x25 - x24) ≤ (t - 1)) ∧ ((x45 - x25) ≤ (t - 1))) ∨ ((x45 ≤ x25) ∧ (x25 ≤ x24) ∧ ((x24 - x45) ≥ 1) ∧ ((x24 - x25) ≤ (t - 1)) ∧ ((x25 - x45) ≤ (t - 1))))) : (((x45 - x24) ≥ 1) ∨ (x45 ≤ x25)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x45 - x24) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x45 ≤ x25) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause1557 (t x24 x25 x45 : ℝ) (h : (((x24 ≤ x25) ∧ (x25 ≤ x45) ∧ ((x45 - x24) ≥ 1) ∧ ((x25 - x24) ≤ (t - 1)) ∧ ((x45 - x25) ≤ (t - 1))) ∨ ((x45 ≤ x25) ∧ (x25 ≤ x24) ∧ ((x24 - x45) ≥ 1) ∧ ((x24 - x25) ≤ (t - 1)) ∧ ((x25 - x45) ≤ (t - 1))))) : (((x45 - x24) ≥ 1) ∨ (x25 ≤ x24)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x45 - x24) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x25 ≤ x24) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause1558 (t x24 x25 x45 : ℝ) (h : (((x24 ≤ x25) ∧ (x25 ≤ x45) ∧ ((x45 - x24) ≥ 1) ∧ ((x25 - x24) ≤ (t - 1)) ∧ ((x45 - x25) ≤ (t - 1))) ∨ ((x45 ≤ x25) ∧ (x25 ≤ x24) ∧ ((x24 - x45) ≥ 1) ∧ ((x24 - x25) ≤ (t - 1)) ∧ ((x25 - x45) ≤ (t - 1))))) : (((x45 - x24) ≥ 1) ∨ ((x24 - x45) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x45 - x24) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x24 - x45) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause1559 (t x24 x25 x45 : ℝ) (h : (((x24 ≤ x25) ∧ (x25 ≤ x45) ∧ ((x45 - x24) ≥ 1) ∧ ((x25 - x24) ≤ (t - 1)) ∧ ((x45 - x25) ≤ (t - 1))) ∨ ((x45 ≤ x25) ∧ (x25 ≤ x24) ∧ ((x24 - x45) ≥ 1) ∧ ((x24 - x25) ≤ (t - 1)) ∧ ((x25 - x45) ≤ (t - 1))))) : (((x45 - x24) ≥ 1) ∨ ((x24 - x25) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x45 - x24) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x24 - x25) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause1560 (t x24 x25 x45 : ℝ) (h : (((x24 ≤ x25) ∧ (x25 ≤ x45) ∧ ((x45 - x24) ≥ 1) ∧ ((x25 - x24) ≤ (t - 1)) ∧ ((x45 - x25) ≤ (t - 1))) ∨ ((x45 ≤ x25) ∧ (x25 ≤ x24) ∧ ((x24 - x45) ≥ 1) ∧ ((x24 - x25) ≤ (t - 1)) ∧ ((x25 - x45) ≤ (t - 1))))) : (((x45 - x24) ≥ 1) ∨ ((x25 - x45) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x45 - x24) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x25 - x45) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause1561 (t x24 x25 x45 : ℝ) (h : (((x24 ≤ x25) ∧ (x25 ≤ x45) ∧ ((x45 - x24) ≥ 1) ∧ ((x25 - x24) ≤ (t - 1)) ∧ ((x45 - x25) ≤ (t - 1))) ∨ ((x45 ≤ x25) ∧ (x25 ≤ x24) ∧ ((x24 - x45) ≥ 1) ∧ ((x24 - x25) ≤ (t - 1)) ∧ ((x25 - x45) ≤ (t - 1))))) : (((x25 - x24) ≤ (t - 1)) ∨ (x45 ≤ x25)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x25 - x24) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x45 ≤ x25) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause1562 (t x24 x25 x45 : ℝ) (h : (((x24 ≤ x25) ∧ (x25 ≤ x45) ∧ ((x45 - x24) ≥ 1) ∧ ((x25 - x24) ≤ (t - 1)) ∧ ((x45 - x25) ≤ (t - 1))) ∨ ((x45 ≤ x25) ∧ (x25 ≤ x24) ∧ ((x24 - x45) ≥ 1) ∧ ((x24 - x25) ≤ (t - 1)) ∧ ((x25 - x45) ≤ (t - 1))))) : (((x25 - x24) ≤ (t - 1)) ∨ (x25 ≤ x24)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x25 - x24) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x25 ≤ x24) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause1563 (t x24 x25 x45 : ℝ) (h : (((x24 ≤ x25) ∧ (x25 ≤ x45) ∧ ((x45 - x24) ≥ 1) ∧ ((x25 - x24) ≤ (t - 1)) ∧ ((x45 - x25) ≤ (t - 1))) ∨ ((x45 ≤ x25) ∧ (x25 ≤ x24) ∧ ((x24 - x45) ≥ 1) ∧ ((x24 - x25) ≤ (t - 1)) ∧ ((x25 - x45) ≤ (t - 1))))) : (((x25 - x24) ≤ (t - 1)) ∨ ((x24 - x45) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x25 - x24) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x24 - x45) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause1564 (t x24 x25 x45 : ℝ) (h : (((x24 ≤ x25) ∧ (x25 ≤ x45) ∧ ((x45 - x24) ≥ 1) ∧ ((x25 - x24) ≤ (t - 1)) ∧ ((x45 - x25) ≤ (t - 1))) ∨ ((x45 ≤ x25) ∧ (x25 ≤ x24) ∧ ((x24 - x45) ≥ 1) ∧ ((x24 - x25) ≤ (t - 1)) ∧ ((x25 - x45) ≤ (t - 1))))) : (((x25 - x24) ≤ (t - 1)) ∨ ((x24 - x25) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x25 - x24) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x24 - x25) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause1565 (t x24 x25 x45 : ℝ) (h : (((x24 ≤ x25) ∧ (x25 ≤ x45) ∧ ((x45 - x24) ≥ 1) ∧ ((x25 - x24) ≤ (t - 1)) ∧ ((x45 - x25) ≤ (t - 1))) ∨ ((x45 ≤ x25) ∧ (x25 ≤ x24) ∧ ((x24 - x45) ≥ 1) ∧ ((x24 - x25) ≤ (t - 1)) ∧ ((x25 - x45) ≤ (t - 1))))) : (((x25 - x24) ≤ (t - 1)) ∨ ((x25 - x45) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x25 - x24) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x25 - x45) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause1566 (t x24 x25 x45 : ℝ) (h : (((x24 ≤ x25) ∧ (x25 ≤ x45) ∧ ((x45 - x24) ≥ 1) ∧ ((x25 - x24) ≤ (t - 1)) ∧ ((x45 - x25) ≤ (t - 1))) ∨ ((x45 ≤ x25) ∧ (x25 ≤ x24) ∧ ((x24 - x45) ≥ 1) ∧ ((x24 - x25) ≤ (t - 1)) ∧ ((x25 - x45) ≤ (t - 1))))) : (((x45 - x25) ≤ (t - 1)) ∨ (x45 ≤ x25)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x45 - x25) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x45 ≤ x25) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause1567 (t x24 x25 x45 : ℝ) (h : (((x24 ≤ x25) ∧ (x25 ≤ x45) ∧ ((x45 - x24) ≥ 1) ∧ ((x25 - x24) ≤ (t - 1)) ∧ ((x45 - x25) ≤ (t - 1))) ∨ ((x45 ≤ x25) ∧ (x25 ≤ x24) ∧ ((x24 - x45) ≥ 1) ∧ ((x24 - x25) ≤ (t - 1)) ∧ ((x25 - x45) ≤ (t - 1))))) : (((x45 - x25) ≤ (t - 1)) ∨ (x25 ≤ x24)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x45 - x25) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x25 ≤ x24) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause1568 (t x24 x25 x45 : ℝ) (h : (((x24 ≤ x25) ∧ (x25 ≤ x45) ∧ ((x45 - x24) ≥ 1) ∧ ((x25 - x24) ≤ (t - 1)) ∧ ((x45 - x25) ≤ (t - 1))) ∨ ((x45 ≤ x25) ∧ (x25 ≤ x24) ∧ ((x24 - x45) ≥ 1) ∧ ((x24 - x25) ≤ (t - 1)) ∧ ((x25 - x45) ≤ (t - 1))))) : (((x45 - x25) ≤ (t - 1)) ∨ ((x24 - x45) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x45 - x25) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x24 - x45) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause1569 (t x24 x25 x45 : ℝ) (h : (((x24 ≤ x25) ∧ (x25 ≤ x45) ∧ ((x45 - x24) ≥ 1) ∧ ((x25 - x24) ≤ (t - 1)) ∧ ((x45 - x25) ≤ (t - 1))) ∨ ((x45 ≤ x25) ∧ (x25 ≤ x24) ∧ ((x24 - x45) ≥ 1) ∧ ((x24 - x25) ≤ (t - 1)) ∧ ((x25 - x45) ≤ (t - 1))))) : (((x45 - x25) ≤ (t - 1)) ∨ ((x24 - x25) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x45 - x25) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x24 - x25) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause1570 (t x24 x25 x45 : ℝ) (h : (((x24 ≤ x25) ∧ (x25 ≤ x45) ∧ ((x45 - x24) ≥ 1) ∧ ((x25 - x24) ≤ (t - 1)) ∧ ((x45 - x25) ≤ (t - 1))) ∨ ((x45 ≤ x25) ∧ (x25 ≤ x24) ∧ ((x24 - x45) ≥ 1) ∧ ((x24 - x25) ≤ (t - 1)) ∧ ((x25 - x45) ≤ (t - 1))))) : (((x45 - x25) ≤ (t - 1)) ∨ ((x25 - x45) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x45 - x25) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x25 - x45) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause1571 (t x02 x23 x24 x46 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x02 + ((-1) * x24)) ≤ (-1))) ∨ (¬ (x23 ≥ 0)) ∨ (¬ ((x02 + ((-1) * x23)) ≥ 1)) ∨ (¬ ((x24 + ((-1) * x46)) ≤ (-1))) ∨ ((t + ((-1) * x67)) ≤ 0) ∨ (¬ ((x46 + ((-1) * x67)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x02 + ((-1) * x24)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : (x23 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x02 + ((-1) * x23)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x24 + ((-1) * x46)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ¬ ((t + ((-1) * x67)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x46 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th95 t x02 x23 x24 x46 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u2 (And.intro u1 (And.intro u4 (And.intro u5 (And.intro u0 (And.intro u6 u3)))))))) h

theorem clause1572 (x04 x34 x45 : ℝ) : ((¬ ((x34 + ((-1) * x45)) ≥ 1)) ∨ (¬ ((x04 + ((-1) * x34)) ≥ 0)) ∨ (¬ ((x04 + ((-1) * x45)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x34 + ((-1) * x45)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x04 + ((-1) * x34)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x04 + ((-1) * x45)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th96 x04 x34 x45
  exact (fun hh => (fun hh => hh) (hh (And.intro u1 (And.intro u2 u0)))) h

theorem clause1575 (t x04 x05 x45 : ℝ) : (((x04 + ((-1) * x45)) ≥ 1) ∨ ((x04 + ((-1) * x05)) ≤ 0) ∨ (¬ (x04 ≤ x05)) ∨ (¬ (x05 ≤ x45)) ∨ (¬ ((x45 - x04) ≥ 1)) ∨ (¬ ((x05 - x04) ≤ (t - 1))) ∨ (¬ ((x45 - x05) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x04 + ((-1) * x45)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x04 + ((-1) * x05)) ≤ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x04 ≤ x05) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x05 ≤ x45) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x45 - x04) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x05 - x04) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x45 - x05) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th98 t x04 x05 x45
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 (hh).1) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause1580 (t x04 x05 x45 : ℝ) : (((x04 + ((-1) * x45)) ≥ 1) ∨ ((x05 + ((-1) * x45)) ≤ 0) ∨ (¬ (x04 ≤ x05)) ∨ (¬ (x05 ≤ x45)) ∨ (¬ ((x45 - x04) ≥ 1)) ∨ (¬ ((x05 - x04) ≤ (t - 1))) ∨ (¬ ((x45 - x05) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x04 + ((-1) * x45)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x05 + ((-1) * x45)) ≤ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x04 ≤ x05) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x05 ≤ x45) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x45 - x04) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x05 - x04) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x45 - x05) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th98 t x04 x05 x45
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 ((hh).2).1) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause1582 (t x04 x05 x45 : ℝ) : (((x05 + ((-1) * x45)) ≤ 0) ∨ ((t + ((-1) * x05) + x45) ≥ 1) ∨ (¬ (x04 ≤ x05)) ∨ (¬ (x05 ≤ x45)) ∨ (¬ ((x45 - x04) ≥ 1)) ∨ (¬ ((x05 - x04) ≤ (t - 1))) ∨ (¬ ((x45 - x05) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x05 + ((-1) * x45)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + ((-1) * x05) + x45) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x04 ≤ x05) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x05 ≤ x45) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x45 - x04) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x05 - x04) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x45 - x05) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th98 t x04 x05 x45
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause1583 (t x04 x05 x45 : ℝ) : (((x04 + ((-1) * x45)) ≤ (-1)) ∨ ((x05 + ((-1) * x45)) ≥ 0) ∨ (¬ (x04 ≤ x05)) ∨ (¬ (x05 ≤ x45)) ∨ (¬ ((x45 - x04) ≥ 1)) ∨ (¬ ((x05 - x04) ≤ (t - 1))) ∨ (¬ ((x45 - x05) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x04 + ((-1) * x45)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x05 + ((-1) * x45)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x04 ≤ x05) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x05 ≤ x45) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x45 - x04) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x05 - x04) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x45 - x05) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th98 t x04 x05 x45
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause1584 (t x04 x05 x45 : ℝ) : (((x04 + ((-1) * x45)) ≤ (-1)) ∨ ((x04 + ((-1) * x05)) ≥ 0) ∨ (¬ (x04 ≤ x05)) ∨ (¬ (x05 ≤ x45)) ∨ (¬ ((x45 - x04) ≥ 1)) ∨ (¬ ((x05 - x04) ≤ (t - 1))) ∨ (¬ ((x45 - x05) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x04 + ((-1) * x45)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x04 + ((-1) * x05)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x04 ≤ x05) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x05 ≤ x45) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x45 - x04) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x05 - x04) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x45 - x05) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th98 t x04 x05 x45
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause1585 (t x04 x05 x45 : ℝ) : (((x04 + ((-1) * x45)) ≥ 1) ∨ ((x04 + ((-1) * x45)) ≤ (-1)) ∨ (¬ (x04 ≤ x05)) ∨ (¬ (x05 ≤ x45)) ∨ (¬ ((x45 - x04) ≥ 1)) ∨ (¬ ((x05 - x04) ≤ (t - 1))) ∨ (¬ ((x45 - x05) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x04 + ((-1) * x45)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x04 + ((-1) * x45)) ≤ (-1)) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x04 ≤ x05) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x05 ≤ x45) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x45 - x04) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x05 - x04) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x45 - x05) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th98 t x04 x05 x45
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 (((hh).2).2).1) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause1593 (t x04 x05 x45 : ℝ) : (((t + x05 + ((-1) * x45)) ≥ 1) ∨ ((x05 + ((-1) * x45)) ≥ 0) ∨ (¬ (x04 ≤ x05)) ∨ (¬ (x05 ≤ x45)) ∨ (¬ ((x45 - x04) ≥ 1)) ∨ (¬ ((x05 - x04) ≤ (t - 1))) ∨ (¬ ((x45 - x05) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((t + x05 + ((-1) * x45)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x05 + ((-1) * x45)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x04 ≤ x05) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x05 ≤ x45) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x45 - x04) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x05 - x04) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x45 - x05) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th98 t x04 x05 x45
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 (hh).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause1595 (t x04 x05 x45 : ℝ) : (((x04 + ((-1) * x45)) ≥ 1) ∨ ((t + x05 + ((-1) * x45)) ≥ 1) ∨ (¬ (x04 ≤ x05)) ∨ (¬ (x05 ≤ x45)) ∨ (¬ ((x45 - x04) ≥ 1)) ∨ (¬ ((x05 - x04) ≤ (t - 1))) ∨ (¬ ((x45 - x05) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x04 + ((-1) * x45)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + x05 + ((-1) * x45)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x04 ≤ x05) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x05 ≤ x45) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x45 - x04) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x05 - x04) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x45 - x05) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th98 t x04 x05 x45
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 ((((hh).2).2).2).2) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause1600 (t x04 x05 x45 : ℝ) : (((x04 + ((-1) * x45)) ≥ 1) ∨ ((x04 + ((-1) * x05)) ≤ 0) ∨ (¬ (x45 ≤ x05)) ∨ (¬ (x05 ≤ x04)) ∨ (¬ ((x04 - x45) ≥ 1)) ∨ (¬ ((x04 - x05) ≤ (t - 1))) ∨ (¬ ((x05 - x45) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x04 + ((-1) * x45)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x04 + ((-1) * x05)) ≤ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x45 ≤ x05) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x05 ≤ x04) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x04 - x45) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x04 - x05) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x05 - x45) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th98 t x04 x05 x45
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 (hh).1) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause1604 (t x04 x05 x45 : ℝ) : (((x05 + ((-1) * x45)) ≤ 0) ∨ ((x04 + ((-1) * x05)) ≥ 0) ∨ (¬ (x45 ≤ x05)) ∨ (¬ (x05 ≤ x04)) ∨ (¬ ((x04 - x45) ≥ 1)) ∨ (¬ ((x04 - x05) ≤ (t - 1))) ∨ (¬ ((x05 - x45) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x05 + ((-1) * x45)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x04 + ((-1) * x05)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x45 ≤ x05) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x05 ≤ x04) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x04 - x45) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x04 - x05) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x05 - x45) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th98 t x04 x05 x45
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause1605 (t x04 x05 x45 : ℝ) : (((x04 + ((-1) * x45)) ≥ 1) ∨ ((x05 + ((-1) * x45)) ≤ 0) ∨ (¬ (x45 ≤ x05)) ∨ (¬ (x05 ≤ x04)) ∨ (¬ ((x04 - x45) ≥ 1)) ∨ (¬ ((x04 - x05) ≤ (t - 1))) ∨ (¬ ((x05 - x45) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x04 + ((-1) * x45)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x05 + ((-1) * x45)) ≤ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x45 ≤ x05) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x05 ≤ x04) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x04 - x45) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x04 - x05) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x05 - x45) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th98 t x04 x05 x45
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 ((hh).2).1) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause1608 (t x04 x05 x45 : ℝ) : (((x04 + ((-1) * x45)) ≤ (-1)) ∨ ((x05 + ((-1) * x45)) ≥ 0) ∨ (¬ (x45 ≤ x05)) ∨ (¬ (x05 ≤ x04)) ∨ (¬ ((x04 - x45) ≥ 1)) ∨ (¬ ((x04 - x05) ≤ (t - 1))) ∨ (¬ ((x05 - x45) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x04 + ((-1) * x45)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x05 + ((-1) * x45)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x45 ≤ x05) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x05 ≤ x04) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x04 - x45) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x04 - x05) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x05 - x45) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th98 t x04 x05 x45
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause1609 (t x04 x05 x45 : ℝ) : (((x04 + ((-1) * x45)) ≤ (-1)) ∨ ((x04 + ((-1) * x05)) ≥ 0) ∨ (¬ (x45 ≤ x05)) ∨ (¬ (x05 ≤ x04)) ∨ (¬ ((x04 - x45) ≥ 1)) ∨ (¬ ((x04 - x05) ≤ (t - 1))) ∨ (¬ ((x05 - x45) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x04 + ((-1) * x45)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x04 + ((-1) * x05)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x45 ≤ x05) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x05 ≤ x04) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x04 - x45) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x04 - x05) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x05 - x45) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th98 t x04 x05 x45
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause1610 (t x04 x05 x45 : ℝ) : (((x04 + ((-1) * x45)) ≥ 1) ∨ ((x04 + ((-1) * x45)) ≤ (-1)) ∨ (¬ (x45 ≤ x05)) ∨ (¬ (x05 ≤ x04)) ∨ (¬ ((x04 - x45) ≥ 1)) ∨ (¬ ((x04 - x05) ≤ (t - 1))) ∨ (¬ ((x05 - x45) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x04 + ((-1) * x45)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x04 + ((-1) * x45)) ≤ (-1)) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x45 ≤ x05) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x05 ≤ x04) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x04 - x45) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x04 - x05) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x05 - x45) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th98 t x04 x05 x45
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 (((hh).2).2).1) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause1612 (t x04 x05 x45 : ℝ) : (((x04 + ((-1) * x45)) ≤ (-1)) ∨ ((t + ((-1) * x05) + x45) ≥ 1) ∨ (¬ (x45 ≤ x05)) ∨ (¬ (x05 ≤ x04)) ∨ (¬ ((x04 - x45) ≥ 1)) ∨ (¬ ((x04 - x05) ≤ (t - 1))) ∨ (¬ ((x05 - x45) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x04 + ((-1) * x45)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + ((-1) * x05) + x45) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x45 ≤ x05) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x05 ≤ x04) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x04 - x45) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x04 - x05) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x05 - x45) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th98 t x04 x05 x45
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause1620 (t x04 x05 x45 : ℝ) : (((x04 + ((-1) * x45)) ≥ 1) ∨ ((t + x05 + ((-1) * x45)) ≥ 1) ∨ (¬ (x45 ≤ x05)) ∨ (¬ (x05 ≤ x04)) ∨ (¬ ((x04 - x45) ≥ 1)) ∨ (¬ ((x04 - x05) ≤ (t - 1))) ∨ (¬ ((x05 - x45) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x04 + ((-1) * x45)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + x05 + ((-1) * x45)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x45 ≤ x05) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x05 ≤ x04) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x04 - x45) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x04 - x05) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x05 - x45) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th98 t x04 x05 x45
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 ((((hh).2).2).2).2) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause1673 (t x04 x05 x45 : ℝ) (h : (((x04 ≤ x05) ∧ (x05 ≤ x45) ∧ ((x45 - x04) ≥ 1) ∧ ((x05 - x04) ≤ (t - 1)) ∧ ((x45 - x05) ≤ (t - 1))) ∨ ((x45 ≤ x05) ∧ (x05 ≤ x04) ∧ ((x04 - x45) ≥ 1) ∧ ((x04 - x05) ≤ (t - 1)) ∧ ((x05 - x45) ≤ (t - 1))))) : ((x04 ≤ x05) ∨ (x45 ≤ x05)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x04 ≤ x05) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x45 ≤ x05) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause1674 (t x04 x05 x45 : ℝ) (h : (((x04 ≤ x05) ∧ (x05 ≤ x45) ∧ ((x45 - x04) ≥ 1) ∧ ((x05 - x04) ≤ (t - 1)) ∧ ((x45 - x05) ≤ (t - 1))) ∨ ((x45 ≤ x05) ∧ (x05 ≤ x04) ∧ ((x04 - x45) ≥ 1) ∧ ((x04 - x05) ≤ (t - 1)) ∧ ((x05 - x45) ≤ (t - 1))))) : ((x04 ≤ x05) ∨ (x05 ≤ x04)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x04 ≤ x05) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x05 ≤ x04) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause1675 (t x04 x05 x45 : ℝ) (h : (((x04 ≤ x05) ∧ (x05 ≤ x45) ∧ ((x45 - x04) ≥ 1) ∧ ((x05 - x04) ≤ (t - 1)) ∧ ((x45 - x05) ≤ (t - 1))) ∨ ((x45 ≤ x05) ∧ (x05 ≤ x04) ∧ ((x04 - x45) ≥ 1) ∧ ((x04 - x05) ≤ (t - 1)) ∧ ((x05 - x45) ≤ (t - 1))))) : ((x04 ≤ x05) ∨ ((x04 - x45) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x04 ≤ x05) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x04 - x45) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause1676 (t x04 x05 x45 : ℝ) (h : (((x04 ≤ x05) ∧ (x05 ≤ x45) ∧ ((x45 - x04) ≥ 1) ∧ ((x05 - x04) ≤ (t - 1)) ∧ ((x45 - x05) ≤ (t - 1))) ∨ ((x45 ≤ x05) ∧ (x05 ≤ x04) ∧ ((x04 - x45) ≥ 1) ∧ ((x04 - x05) ≤ (t - 1)) ∧ ((x05 - x45) ≤ (t - 1))))) : ((x04 ≤ x05) ∨ ((x04 - x05) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x04 ≤ x05) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x04 - x05) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause1677 (t x04 x05 x45 : ℝ) (h : (((x04 ≤ x05) ∧ (x05 ≤ x45) ∧ ((x45 - x04) ≥ 1) ∧ ((x05 - x04) ≤ (t - 1)) ∧ ((x45 - x05) ≤ (t - 1))) ∨ ((x45 ≤ x05) ∧ (x05 ≤ x04) ∧ ((x04 - x45) ≥ 1) ∧ ((x04 - x05) ≤ (t - 1)) ∧ ((x05 - x45) ≤ (t - 1))))) : ((x04 ≤ x05) ∨ ((x05 - x45) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x04 ≤ x05) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x05 - x45) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause1678 (t x04 x05 x45 : ℝ) (h : (((x04 ≤ x05) ∧ (x05 ≤ x45) ∧ ((x45 - x04) ≥ 1) ∧ ((x05 - x04) ≤ (t - 1)) ∧ ((x45 - x05) ≤ (t - 1))) ∨ ((x45 ≤ x05) ∧ (x05 ≤ x04) ∧ ((x04 - x45) ≥ 1) ∧ ((x04 - x05) ≤ (t - 1)) ∧ ((x05 - x45) ≤ (t - 1))))) : ((x05 ≤ x45) ∨ (x45 ≤ x05)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x05 ≤ x45) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x45 ≤ x05) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause1679 (t x04 x05 x45 : ℝ) (h : (((x04 ≤ x05) ∧ (x05 ≤ x45) ∧ ((x45 - x04) ≥ 1) ∧ ((x05 - x04) ≤ (t - 1)) ∧ ((x45 - x05) ≤ (t - 1))) ∨ ((x45 ≤ x05) ∧ (x05 ≤ x04) ∧ ((x04 - x45) ≥ 1) ∧ ((x04 - x05) ≤ (t - 1)) ∧ ((x05 - x45) ≤ (t - 1))))) : ((x05 ≤ x45) ∨ (x05 ≤ x04)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x05 ≤ x45) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x05 ≤ x04) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause1680 (t x04 x05 x45 : ℝ) (h : (((x04 ≤ x05) ∧ (x05 ≤ x45) ∧ ((x45 - x04) ≥ 1) ∧ ((x05 - x04) ≤ (t - 1)) ∧ ((x45 - x05) ≤ (t - 1))) ∨ ((x45 ≤ x05) ∧ (x05 ≤ x04) ∧ ((x04 - x45) ≥ 1) ∧ ((x04 - x05) ≤ (t - 1)) ∧ ((x05 - x45) ≤ (t - 1))))) : ((x05 ≤ x45) ∨ ((x04 - x45) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x05 ≤ x45) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x04 - x45) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause1681 (t x04 x05 x45 : ℝ) (h : (((x04 ≤ x05) ∧ (x05 ≤ x45) ∧ ((x45 - x04) ≥ 1) ∧ ((x05 - x04) ≤ (t - 1)) ∧ ((x45 - x05) ≤ (t - 1))) ∨ ((x45 ≤ x05) ∧ (x05 ≤ x04) ∧ ((x04 - x45) ≥ 1) ∧ ((x04 - x05) ≤ (t - 1)) ∧ ((x05 - x45) ≤ (t - 1))))) : ((x05 ≤ x45) ∨ ((x04 - x05) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x05 ≤ x45) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x04 - x05) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause1682 (t x04 x05 x45 : ℝ) (h : (((x04 ≤ x05) ∧ (x05 ≤ x45) ∧ ((x45 - x04) ≥ 1) ∧ ((x05 - x04) ≤ (t - 1)) ∧ ((x45 - x05) ≤ (t - 1))) ∨ ((x45 ≤ x05) ∧ (x05 ≤ x04) ∧ ((x04 - x45) ≥ 1) ∧ ((x04 - x05) ≤ (t - 1)) ∧ ((x05 - x45) ≤ (t - 1))))) : ((x05 ≤ x45) ∨ ((x05 - x45) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x05 ≤ x45) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x05 - x45) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause1683 (t x04 x05 x45 : ℝ) (h : (((x04 ≤ x05) ∧ (x05 ≤ x45) ∧ ((x45 - x04) ≥ 1) ∧ ((x05 - x04) ≤ (t - 1)) ∧ ((x45 - x05) ≤ (t - 1))) ∨ ((x45 ≤ x05) ∧ (x05 ≤ x04) ∧ ((x04 - x45) ≥ 1) ∧ ((x04 - x05) ≤ (t - 1)) ∧ ((x05 - x45) ≤ (t - 1))))) : (((x45 - x04) ≥ 1) ∨ (x45 ≤ x05)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x45 - x04) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x45 ≤ x05) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause1684 (t x04 x05 x45 : ℝ) (h : (((x04 ≤ x05) ∧ (x05 ≤ x45) ∧ ((x45 - x04) ≥ 1) ∧ ((x05 - x04) ≤ (t - 1)) ∧ ((x45 - x05) ≤ (t - 1))) ∨ ((x45 ≤ x05) ∧ (x05 ≤ x04) ∧ ((x04 - x45) ≥ 1) ∧ ((x04 - x05) ≤ (t - 1)) ∧ ((x05 - x45) ≤ (t - 1))))) : (((x45 - x04) ≥ 1) ∨ (x05 ≤ x04)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x45 - x04) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x05 ≤ x04) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause1685 (t x04 x05 x45 : ℝ) (h : (((x04 ≤ x05) ∧ (x05 ≤ x45) ∧ ((x45 - x04) ≥ 1) ∧ ((x05 - x04) ≤ (t - 1)) ∧ ((x45 - x05) ≤ (t - 1))) ∨ ((x45 ≤ x05) ∧ (x05 ≤ x04) ∧ ((x04 - x45) ≥ 1) ∧ ((x04 - x05) ≤ (t - 1)) ∧ ((x05 - x45) ≤ (t - 1))))) : (((x45 - x04) ≥ 1) ∨ ((x04 - x45) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x45 - x04) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x04 - x45) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause1686 (t x04 x05 x45 : ℝ) (h : (((x04 ≤ x05) ∧ (x05 ≤ x45) ∧ ((x45 - x04) ≥ 1) ∧ ((x05 - x04) ≤ (t - 1)) ∧ ((x45 - x05) ≤ (t - 1))) ∨ ((x45 ≤ x05) ∧ (x05 ≤ x04) ∧ ((x04 - x45) ≥ 1) ∧ ((x04 - x05) ≤ (t - 1)) ∧ ((x05 - x45) ≤ (t - 1))))) : (((x45 - x04) ≥ 1) ∨ ((x04 - x05) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x45 - x04) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x04 - x05) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause1687 (t x04 x05 x45 : ℝ) (h : (((x04 ≤ x05) ∧ (x05 ≤ x45) ∧ ((x45 - x04) ≥ 1) ∧ ((x05 - x04) ≤ (t - 1)) ∧ ((x45 - x05) ≤ (t - 1))) ∨ ((x45 ≤ x05) ∧ (x05 ≤ x04) ∧ ((x04 - x45) ≥ 1) ∧ ((x04 - x05) ≤ (t - 1)) ∧ ((x05 - x45) ≤ (t - 1))))) : (((x45 - x04) ≥ 1) ∨ ((x05 - x45) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x45 - x04) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x05 - x45) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause1688 (t x04 x05 x45 : ℝ) (h : (((x04 ≤ x05) ∧ (x05 ≤ x45) ∧ ((x45 - x04) ≥ 1) ∧ ((x05 - x04) ≤ (t - 1)) ∧ ((x45 - x05) ≤ (t - 1))) ∨ ((x45 ≤ x05) ∧ (x05 ≤ x04) ∧ ((x04 - x45) ≥ 1) ∧ ((x04 - x05) ≤ (t - 1)) ∧ ((x05 - x45) ≤ (t - 1))))) : (((x05 - x04) ≤ (t - 1)) ∨ (x45 ≤ x05)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x05 - x04) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x45 ≤ x05) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause1689 (t x04 x05 x45 : ℝ) (h : (((x04 ≤ x05) ∧ (x05 ≤ x45) ∧ ((x45 - x04) ≥ 1) ∧ ((x05 - x04) ≤ (t - 1)) ∧ ((x45 - x05) ≤ (t - 1))) ∨ ((x45 ≤ x05) ∧ (x05 ≤ x04) ∧ ((x04 - x45) ≥ 1) ∧ ((x04 - x05) ≤ (t - 1)) ∧ ((x05 - x45) ≤ (t - 1))))) : (((x05 - x04) ≤ (t - 1)) ∨ (x05 ≤ x04)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x05 - x04) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x05 ≤ x04) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause1690 (t x04 x05 x45 : ℝ) (h : (((x04 ≤ x05) ∧ (x05 ≤ x45) ∧ ((x45 - x04) ≥ 1) ∧ ((x05 - x04) ≤ (t - 1)) ∧ ((x45 - x05) ≤ (t - 1))) ∨ ((x45 ≤ x05) ∧ (x05 ≤ x04) ∧ ((x04 - x45) ≥ 1) ∧ ((x04 - x05) ≤ (t - 1)) ∧ ((x05 - x45) ≤ (t - 1))))) : (((x05 - x04) ≤ (t - 1)) ∨ ((x04 - x45) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x05 - x04) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x04 - x45) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause1691 (t x04 x05 x45 : ℝ) (h : (((x04 ≤ x05) ∧ (x05 ≤ x45) ∧ ((x45 - x04) ≥ 1) ∧ ((x05 - x04) ≤ (t - 1)) ∧ ((x45 - x05) ≤ (t - 1))) ∨ ((x45 ≤ x05) ∧ (x05 ≤ x04) ∧ ((x04 - x45) ≥ 1) ∧ ((x04 - x05) ≤ (t - 1)) ∧ ((x05 - x45) ≤ (t - 1))))) : (((x05 - x04) ≤ (t - 1)) ∨ ((x04 - x05) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x05 - x04) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x04 - x05) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause1692 (t x04 x05 x45 : ℝ) (h : (((x04 ≤ x05) ∧ (x05 ≤ x45) ∧ ((x45 - x04) ≥ 1) ∧ ((x05 - x04) ≤ (t - 1)) ∧ ((x45 - x05) ≤ (t - 1))) ∨ ((x45 ≤ x05) ∧ (x05 ≤ x04) ∧ ((x04 - x45) ≥ 1) ∧ ((x04 - x05) ≤ (t - 1)) ∧ ((x05 - x45) ≤ (t - 1))))) : (((x05 - x04) ≤ (t - 1)) ∨ ((x05 - x45) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x05 - x04) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x05 - x45) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause1693 (t x04 x05 x45 : ℝ) (h : (((x04 ≤ x05) ∧ (x05 ≤ x45) ∧ ((x45 - x04) ≥ 1) ∧ ((x05 - x04) ≤ (t - 1)) ∧ ((x45 - x05) ≤ (t - 1))) ∨ ((x45 ≤ x05) ∧ (x05 ≤ x04) ∧ ((x04 - x45) ≥ 1) ∧ ((x04 - x05) ≤ (t - 1)) ∧ ((x05 - x45) ≤ (t - 1))))) : (((x45 - x05) ≤ (t - 1)) ∨ (x45 ≤ x05)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x45 - x05) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x45 ≤ x05) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause1694 (t x04 x05 x45 : ℝ) (h : (((x04 ≤ x05) ∧ (x05 ≤ x45) ∧ ((x45 - x04) ≥ 1) ∧ ((x05 - x04) ≤ (t - 1)) ∧ ((x45 - x05) ≤ (t - 1))) ∨ ((x45 ≤ x05) ∧ (x05 ≤ x04) ∧ ((x04 - x45) ≥ 1) ∧ ((x04 - x05) ≤ (t - 1)) ∧ ((x05 - x45) ≤ (t - 1))))) : (((x45 - x05) ≤ (t - 1)) ∨ (x05 ≤ x04)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x45 - x05) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x05 ≤ x04) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause1695 (t x04 x05 x45 : ℝ) (h : (((x04 ≤ x05) ∧ (x05 ≤ x45) ∧ ((x45 - x04) ≥ 1) ∧ ((x05 - x04) ≤ (t - 1)) ∧ ((x45 - x05) ≤ (t - 1))) ∨ ((x45 ≤ x05) ∧ (x05 ≤ x04) ∧ ((x04 - x45) ≥ 1) ∧ ((x04 - x05) ≤ (t - 1)) ∧ ((x05 - x45) ≤ (t - 1))))) : (((x45 - x05) ≤ (t - 1)) ∨ ((x04 - x45) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x45 - x05) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x04 - x45) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause1696 (t x04 x05 x45 : ℝ) (h : (((x04 ≤ x05) ∧ (x05 ≤ x45) ∧ ((x45 - x04) ≥ 1) ∧ ((x05 - x04) ≤ (t - 1)) ∧ ((x45 - x05) ≤ (t - 1))) ∨ ((x45 ≤ x05) ∧ (x05 ≤ x04) ∧ ((x04 - x45) ≥ 1) ∧ ((x04 - x05) ≤ (t - 1)) ∧ ((x05 - x45) ≤ (t - 1))))) : (((x45 - x05) ≤ (t - 1)) ∨ ((x04 - x05) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x45 - x05) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x04 - x05) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause1697 (t x04 x05 x45 : ℝ) (h : (((x04 ≤ x05) ∧ (x05 ≤ x45) ∧ ((x45 - x04) ≥ 1) ∧ ((x05 - x04) ≤ (t - 1)) ∧ ((x45 - x05) ≤ (t - 1))) ∨ ((x45 ≤ x05) ∧ (x05 ≤ x04) ∧ ((x04 - x45) ≥ 1) ∧ ((x04 - x05) ≤ (t - 1)) ∧ ((x05 - x45) ≤ (t - 1))))) : (((x45 - x05) ≤ (t - 1)) ∨ ((x05 - x45) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x45 - x05) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x05 - x45) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause1698 (x34 x46 : ℝ) : ((¬ ((x34 + ((-1) * x46)) ≤ (-1))) ∨ (¬ ((x34 + ((-1) * x46)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x34 + ((-1) * x46)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x34 + ((-1) * x46)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr hh)
  have h := NineTheoryTrial.th100 x34 x46
  exact (fun hh => (Or.elim hh (fun hh => hh u0) (fun zz => ((fun hh => hh u1) zz)))) h

theorem clause1701 (t x34 x36 x46 : ℝ) : (((x34 + ((-1) * x46)) ≥ 1) ∨ ((x34 + ((-1) * x36)) ≤ 0) ∨ (¬ (x34 ≤ x36)) ∨ (¬ (x36 ≤ x46)) ∨ (¬ ((x46 - x34) ≥ 1)) ∨ (¬ ((x36 - x34) ≤ (t - 1))) ∨ (¬ ((x46 - x36) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x34 + ((-1) * x46)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x34 + ((-1) * x36)) ≤ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x34 ≤ x36) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x36 ≤ x46) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x46 - x34) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x36 - x34) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x46 - x36) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th102 t x34 x36 x46
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 (hh).1) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause1702 (t x34 x36 x46 : ℝ) : (((x34 + ((-1) * x36)) ≤ 0) ∨ ((t + ((-1) * x34) + x36) ≥ 1) ∨ (¬ (x34 ≤ x36)) ∨ (¬ (x36 ≤ x46)) ∨ (¬ ((x46 - x34) ≥ 1)) ∨ (¬ ((x36 - x34) ≤ (t - 1))) ∨ (¬ ((x46 - x36) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x34 + ((-1) * x36)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + ((-1) * x34) + x36) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x34 ≤ x36) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x36 ≤ x46) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x46 - x34) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x36 - x34) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x46 - x36) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th102 t x34 x36 x46
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause1705 (t x34 x36 x46 : ℝ) : (((x36 + ((-1) * x46)) ≤ 0) ∨ ((x34 + ((-1) * x36)) ≥ 0) ∨ (¬ (x34 ≤ x36)) ∨ (¬ (x36 ≤ x46)) ∨ (¬ ((x46 - x34) ≥ 1)) ∨ (¬ ((x36 - x34) ≤ (t - 1))) ∨ (¬ ((x46 - x36) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x36 + ((-1) * x46)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x34 + ((-1) * x36)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x34 ≤ x36) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x36 ≤ x46) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x46 - x34) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x36 - x34) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x46 - x36) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th102 t x34 x36 x46
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause1706 (t x34 x36 x46 : ℝ) : (((x34 + ((-1) * x46)) ≥ 1) ∨ ((x36 + ((-1) * x46)) ≤ 0) ∨ (¬ (x34 ≤ x36)) ∨ (¬ (x36 ≤ x46)) ∨ (¬ ((x46 - x34) ≥ 1)) ∨ (¬ ((x36 - x34) ≤ (t - 1))) ∨ (¬ ((x46 - x36) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x34 + ((-1) * x46)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x36 + ((-1) * x46)) ≤ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x34 ≤ x36) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x36 ≤ x46) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x46 - x34) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x36 - x34) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x46 - x36) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th102 t x34 x36 x46
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 ((hh).2).1) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause1709 (t x34 x36 x46 : ℝ) : (((x34 + ((-1) * x46)) ≤ (-1)) ∨ ((x36 + ((-1) * x46)) ≥ 0) ∨ (¬ (x34 ≤ x36)) ∨ (¬ (x36 ≤ x46)) ∨ (¬ ((x46 - x34) ≥ 1)) ∨ (¬ ((x36 - x34) ≤ (t - 1))) ∨ (¬ ((x46 - x36) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x34 + ((-1) * x46)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x36 + ((-1) * x46)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x34 ≤ x36) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x36 ≤ x46) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x46 - x34) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x36 - x34) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x46 - x36) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th102 t x34 x36 x46
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause1710 (t x34 x36 x46 : ℝ) : (((x34 + ((-1) * x46)) ≤ (-1)) ∨ ((x34 + ((-1) * x36)) ≥ 0) ∨ (¬ (x34 ≤ x36)) ∨ (¬ (x36 ≤ x46)) ∨ (¬ ((x46 - x34) ≥ 1)) ∨ (¬ ((x36 - x34) ≤ (t - 1))) ∨ (¬ ((x46 - x36) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x34 + ((-1) * x46)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x34 + ((-1) * x36)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x34 ≤ x36) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x36 ≤ x46) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x46 - x34) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x36 - x34) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x46 - x36) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th102 t x34 x36 x46
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause1711 (t x34 x36 x46 : ℝ) : (((x34 + ((-1) * x46)) ≤ (-1)) ∨ ((x34 + ((-1) * x46)) ≥ 1) ∨ (¬ (x34 ≤ x36)) ∨ (¬ (x36 ≤ x46)) ∨ (¬ ((x46 - x34) ≥ 1)) ∨ (¬ ((x36 - x34) ≤ (t - 1))) ∨ (¬ ((x46 - x36) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x34 + ((-1) * x46)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x34 + ((-1) * x46)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x34 ≤ x36) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x36 ≤ x46) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x46 - x34) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x36 - x34) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x46 - x36) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th102 t x34 x36 x46
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause1713 (t x34 x36 x46 : ℝ) : (((x34 + ((-1) * x46)) ≤ (-1)) ∨ ((t + ((-1) * x36) + x46) ≥ 1) ∨ (¬ (x34 ≤ x36)) ∨ (¬ (x36 ≤ x46)) ∨ (¬ ((x46 - x34) ≥ 1)) ∨ (¬ ((x36 - x34) ≤ (t - 1))) ∨ (¬ ((x46 - x36) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x34 + ((-1) * x46)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + ((-1) * x36) + x46) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x34 ≤ x36) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x36 ≤ x46) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x46 - x34) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x36 - x34) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x46 - x36) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th102 t x34 x36 x46
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause1715 (t x34 x36 x46 : ℝ) : (((t + x34 + ((-1) * x36)) ≥ 1) ∨ ((x34 + ((-1) * x36)) ≥ 0) ∨ (¬ (x34 ≤ x36)) ∨ (¬ (x36 ≤ x46)) ∨ (¬ ((x46 - x34) ≥ 1)) ∨ (¬ ((x36 - x34) ≤ (t - 1))) ∨ (¬ ((x46 - x36) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((t + x34 + ((-1) * x36)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x34 + ((-1) * x36)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x34 ≤ x36) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x36 ≤ x46) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x46 - x34) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x36 - x34) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x46 - x36) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th102 t x34 x36 x46
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause1719 (t x34 x36 x46 : ℝ) : (((t + x36 + ((-1) * x46)) ≥ 1) ∨ ((x36 + ((-1) * x46)) ≥ 0) ∨ (¬ (x34 ≤ x36)) ∨ (¬ (x36 ≤ x46)) ∨ (¬ ((x46 - x34) ≥ 1)) ∨ (¬ ((x36 - x34) ≤ (t - 1))) ∨ (¬ ((x46 - x36) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((t + x36 + ((-1) * x46)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x36 + ((-1) * x46)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x34 ≤ x36) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x36 ≤ x46) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x46 - x34) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x36 - x34) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x46 - x36) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th102 t x34 x36 x46
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 (hh).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause1724 (t x34 x36 x46 : ℝ) : (((x34 + ((-1) * x36)) ≤ 0) ∨ ((x36 + ((-1) * x46)) ≥ 0) ∨ (¬ (x46 ≤ x36)) ∨ (¬ (x36 ≤ x34)) ∨ (¬ ((x34 - x46) ≥ 1)) ∨ (¬ ((x34 - x36) ≤ (t - 1))) ∨ (¬ ((x36 - x46) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x34 + ((-1) * x36)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x36 + ((-1) * x46)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x46 ≤ x36) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x36 ≤ x34) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x34 - x46) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x34 - x36) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x36 - x46) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th102 t x34 x36 x46
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause1726 (t x34 x36 x46 : ℝ) : (((x34 + ((-1) * x46)) ≥ 1) ∨ ((x34 + ((-1) * x36)) ≤ 0) ∨ (¬ (x46 ≤ x36)) ∨ (¬ (x36 ≤ x34)) ∨ (¬ ((x34 - x46) ≥ 1)) ∨ (¬ ((x34 - x36) ≤ (t - 1))) ∨ (¬ ((x36 - x46) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x34 + ((-1) * x46)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x34 + ((-1) * x36)) ≤ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x46 ≤ x36) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x36 ≤ x34) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x34 - x46) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x34 - x36) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x36 - x46) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th102 t x34 x36 x46
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 (hh).1) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause1727 (t x34 x36 x46 : ℝ) : (((x34 + ((-1) * x36)) ≤ 0) ∨ ((t + ((-1) * x34) + x36) ≥ 1) ∨ (¬ (x46 ≤ x36)) ∨ (¬ (x36 ≤ x34)) ∨ (¬ ((x34 - x46) ≥ 1)) ∨ (¬ ((x34 - x36) ≤ (t - 1))) ∨ (¬ ((x36 - x46) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x34 + ((-1) * x36)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + ((-1) * x34) + x36) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x46 ≤ x36) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x36 ≤ x34) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x34 - x46) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x34 - x36) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x36 - x46) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th102 t x34 x36 x46
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause1731 (t x34 x36 x46 : ℝ) : (((x34 + ((-1) * x46)) ≥ 1) ∨ ((x36 + ((-1) * x46)) ≤ 0) ∨ (¬ (x46 ≤ x36)) ∨ (¬ (x36 ≤ x34)) ∨ (¬ ((x34 - x46) ≥ 1)) ∨ (¬ ((x34 - x36) ≤ (t - 1))) ∨ (¬ ((x36 - x46) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x34 + ((-1) * x46)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x36 + ((-1) * x46)) ≤ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x46 ≤ x36) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x36 ≤ x34) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x34 - x46) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x34 - x36) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x36 - x46) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th102 t x34 x36 x46
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 ((hh).2).1) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause1733 (t x34 x36 x46 : ℝ) : (((x36 + ((-1) * x46)) ≤ 0) ∨ ((t + ((-1) * x36) + x46) ≥ 1) ∨ (¬ (x46 ≤ x36)) ∨ (¬ (x36 ≤ x34)) ∨ (¬ ((x34 - x46) ≥ 1)) ∨ (¬ ((x34 - x36) ≤ (t - 1))) ∨ (¬ ((x36 - x46) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x36 + ((-1) * x46)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + ((-1) * x36) + x46) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x46 ≤ x36) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x36 ≤ x34) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x34 - x46) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x34 - x36) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x36 - x46) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th102 t x34 x36 x46
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause1734 (t x34 x36 x46 : ℝ) : (((x34 + ((-1) * x46)) ≤ (-1)) ∨ ((x36 + ((-1) * x46)) ≥ 0) ∨ (¬ (x46 ≤ x36)) ∨ (¬ (x36 ≤ x34)) ∨ (¬ ((x34 - x46) ≥ 1)) ∨ (¬ ((x34 - x36) ≤ (t - 1))) ∨ (¬ ((x36 - x46) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x34 + ((-1) * x46)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x36 + ((-1) * x46)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x46 ≤ x36) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x36 ≤ x34) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x34 - x46) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x34 - x36) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x36 - x46) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th102 t x34 x36 x46
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause1735 (t x34 x36 x46 : ℝ) : (((x34 + ((-1) * x46)) ≤ (-1)) ∨ ((x34 + ((-1) * x36)) ≥ 0) ∨ (¬ (x46 ≤ x36)) ∨ (¬ (x36 ≤ x34)) ∨ (¬ ((x34 - x46) ≥ 1)) ∨ (¬ ((x34 - x36) ≤ (t - 1))) ∨ (¬ ((x36 - x46) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x34 + ((-1) * x46)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x34 + ((-1) * x36)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x46 ≤ x36) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x36 ≤ x34) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x34 - x46) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x34 - x36) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x36 - x46) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th102 t x34 x36 x46
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause1736 (t x34 x36 x46 : ℝ) : (((x34 + ((-1) * x46)) ≤ (-1)) ∨ ((x34 + ((-1) * x46)) ≥ 1) ∨ (¬ (x46 ≤ x36)) ∨ (¬ (x36 ≤ x34)) ∨ (¬ ((x34 - x46) ≥ 1)) ∨ (¬ ((x34 - x36) ≤ (t - 1))) ∨ (¬ ((x36 - x46) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x34 + ((-1) * x46)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x34 + ((-1) * x46)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x46 ≤ x36) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x36 ≤ x34) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x34 - x46) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x34 - x36) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x36 - x46) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th102 t x34 x36 x46
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause1741 (t x34 x36 x46 : ℝ) : (((x34 + ((-1) * x46)) ≥ 1) ∨ ((t + x34 + ((-1) * x36)) ≥ 1) ∨ (¬ (x46 ≤ x36)) ∨ (¬ (x36 ≤ x34)) ∨ (¬ ((x34 - x46) ≥ 1)) ∨ (¬ ((x34 - x36) ≤ (t - 1))) ∨ (¬ ((x36 - x46) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x34 + ((-1) * x46)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + x34 + ((-1) * x36)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x46 ≤ x36) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x36 ≤ x34) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x34 - x46) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x34 - x36) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x36 - x46) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th102 t x34 x36 x46
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 ((((hh).2).2).2).1) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause1744 (t x34 x36 x46 : ℝ) : (((t + x36 + ((-1) * x46)) ≥ 1) ∨ ((x36 + ((-1) * x46)) ≥ 0) ∨ (¬ (x46 ≤ x36)) ∨ (¬ (x36 ≤ x34)) ∨ (¬ ((x34 - x46) ≥ 1)) ∨ (¬ ((x34 - x36) ≤ (t - 1))) ∨ (¬ ((x36 - x46) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((t + x36 + ((-1) * x46)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x36 + ((-1) * x46)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x46 ≤ x36) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x36 ≤ x34) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x34 - x46) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x34 - x36) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x36 - x46) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th102 t x34 x36 x46
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 (hh).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause1799 (t x34 x36 x46 : ℝ) (h : (((x34 ≤ x36) ∧ (x36 ≤ x46) ∧ ((x46 - x34) ≥ 1) ∧ ((x36 - x34) ≤ (t - 1)) ∧ ((x46 - x36) ≤ (t - 1))) ∨ ((x46 ≤ x36) ∧ (x36 ≤ x34) ∧ ((x34 - x46) ≥ 1) ∧ ((x34 - x36) ≤ (t - 1)) ∧ ((x36 - x46) ≤ (t - 1))))) : ((x34 ≤ x36) ∨ (x46 ≤ x36)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x34 ≤ x36) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x46 ≤ x36) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause1800 (t x34 x36 x46 : ℝ) (h : (((x34 ≤ x36) ∧ (x36 ≤ x46) ∧ ((x46 - x34) ≥ 1) ∧ ((x36 - x34) ≤ (t - 1)) ∧ ((x46 - x36) ≤ (t - 1))) ∨ ((x46 ≤ x36) ∧ (x36 ≤ x34) ∧ ((x34 - x46) ≥ 1) ∧ ((x34 - x36) ≤ (t - 1)) ∧ ((x36 - x46) ≤ (t - 1))))) : ((x34 ≤ x36) ∨ (x36 ≤ x34)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x34 ≤ x36) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x36 ≤ x34) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause1801 (t x34 x36 x46 : ℝ) (h : (((x34 ≤ x36) ∧ (x36 ≤ x46) ∧ ((x46 - x34) ≥ 1) ∧ ((x36 - x34) ≤ (t - 1)) ∧ ((x46 - x36) ≤ (t - 1))) ∨ ((x46 ≤ x36) ∧ (x36 ≤ x34) ∧ ((x34 - x46) ≥ 1) ∧ ((x34 - x36) ≤ (t - 1)) ∧ ((x36 - x46) ≤ (t - 1))))) : ((x34 ≤ x36) ∨ ((x34 - x46) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x34 ≤ x36) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x34 - x46) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause1802 (t x34 x36 x46 : ℝ) (h : (((x34 ≤ x36) ∧ (x36 ≤ x46) ∧ ((x46 - x34) ≥ 1) ∧ ((x36 - x34) ≤ (t - 1)) ∧ ((x46 - x36) ≤ (t - 1))) ∨ ((x46 ≤ x36) ∧ (x36 ≤ x34) ∧ ((x34 - x46) ≥ 1) ∧ ((x34 - x36) ≤ (t - 1)) ∧ ((x36 - x46) ≤ (t - 1))))) : ((x34 ≤ x36) ∨ ((x34 - x36) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x34 ≤ x36) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x34 - x36) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause1803 (t x34 x36 x46 : ℝ) (h : (((x34 ≤ x36) ∧ (x36 ≤ x46) ∧ ((x46 - x34) ≥ 1) ∧ ((x36 - x34) ≤ (t - 1)) ∧ ((x46 - x36) ≤ (t - 1))) ∨ ((x46 ≤ x36) ∧ (x36 ≤ x34) ∧ ((x34 - x46) ≥ 1) ∧ ((x34 - x36) ≤ (t - 1)) ∧ ((x36 - x46) ≤ (t - 1))))) : ((x34 ≤ x36) ∨ ((x36 - x46) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x34 ≤ x36) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x36 - x46) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause1804 (t x34 x36 x46 : ℝ) (h : (((x34 ≤ x36) ∧ (x36 ≤ x46) ∧ ((x46 - x34) ≥ 1) ∧ ((x36 - x34) ≤ (t - 1)) ∧ ((x46 - x36) ≤ (t - 1))) ∨ ((x46 ≤ x36) ∧ (x36 ≤ x34) ∧ ((x34 - x46) ≥ 1) ∧ ((x34 - x36) ≤ (t - 1)) ∧ ((x36 - x46) ≤ (t - 1))))) : ((x36 ≤ x46) ∨ (x46 ≤ x36)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x36 ≤ x46) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x46 ≤ x36) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause1805 (t x34 x36 x46 : ℝ) (h : (((x34 ≤ x36) ∧ (x36 ≤ x46) ∧ ((x46 - x34) ≥ 1) ∧ ((x36 - x34) ≤ (t - 1)) ∧ ((x46 - x36) ≤ (t - 1))) ∨ ((x46 ≤ x36) ∧ (x36 ≤ x34) ∧ ((x34 - x46) ≥ 1) ∧ ((x34 - x36) ≤ (t - 1)) ∧ ((x36 - x46) ≤ (t - 1))))) : ((x36 ≤ x46) ∨ (x36 ≤ x34)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x36 ≤ x46) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x36 ≤ x34) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause1806 (t x34 x36 x46 : ℝ) (h : (((x34 ≤ x36) ∧ (x36 ≤ x46) ∧ ((x46 - x34) ≥ 1) ∧ ((x36 - x34) ≤ (t - 1)) ∧ ((x46 - x36) ≤ (t - 1))) ∨ ((x46 ≤ x36) ∧ (x36 ≤ x34) ∧ ((x34 - x46) ≥ 1) ∧ ((x34 - x36) ≤ (t - 1)) ∧ ((x36 - x46) ≤ (t - 1))))) : ((x36 ≤ x46) ∨ ((x34 - x46) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x36 ≤ x46) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x34 - x46) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause1807 (t x34 x36 x46 : ℝ) (h : (((x34 ≤ x36) ∧ (x36 ≤ x46) ∧ ((x46 - x34) ≥ 1) ∧ ((x36 - x34) ≤ (t - 1)) ∧ ((x46 - x36) ≤ (t - 1))) ∨ ((x46 ≤ x36) ∧ (x36 ≤ x34) ∧ ((x34 - x46) ≥ 1) ∧ ((x34 - x36) ≤ (t - 1)) ∧ ((x36 - x46) ≤ (t - 1))))) : ((x36 ≤ x46) ∨ ((x34 - x36) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x36 ≤ x46) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x34 - x36) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause1808 (t x34 x36 x46 : ℝ) (h : (((x34 ≤ x36) ∧ (x36 ≤ x46) ∧ ((x46 - x34) ≥ 1) ∧ ((x36 - x34) ≤ (t - 1)) ∧ ((x46 - x36) ≤ (t - 1))) ∨ ((x46 ≤ x36) ∧ (x36 ≤ x34) ∧ ((x34 - x46) ≥ 1) ∧ ((x34 - x36) ≤ (t - 1)) ∧ ((x36 - x46) ≤ (t - 1))))) : ((x36 ≤ x46) ∨ ((x36 - x46) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x36 ≤ x46) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x36 - x46) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause1809 (t x34 x36 x46 : ℝ) (h : (((x34 ≤ x36) ∧ (x36 ≤ x46) ∧ ((x46 - x34) ≥ 1) ∧ ((x36 - x34) ≤ (t - 1)) ∧ ((x46 - x36) ≤ (t - 1))) ∨ ((x46 ≤ x36) ∧ (x36 ≤ x34) ∧ ((x34 - x46) ≥ 1) ∧ ((x34 - x36) ≤ (t - 1)) ∧ ((x36 - x46) ≤ (t - 1))))) : (((x46 - x34) ≥ 1) ∨ (x46 ≤ x36)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x46 - x34) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x46 ≤ x36) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause1810 (t x34 x36 x46 : ℝ) (h : (((x34 ≤ x36) ∧ (x36 ≤ x46) ∧ ((x46 - x34) ≥ 1) ∧ ((x36 - x34) ≤ (t - 1)) ∧ ((x46 - x36) ≤ (t - 1))) ∨ ((x46 ≤ x36) ∧ (x36 ≤ x34) ∧ ((x34 - x46) ≥ 1) ∧ ((x34 - x36) ≤ (t - 1)) ∧ ((x36 - x46) ≤ (t - 1))))) : (((x46 - x34) ≥ 1) ∨ (x36 ≤ x34)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x46 - x34) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x36 ≤ x34) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause1811 (t x34 x36 x46 : ℝ) (h : (((x34 ≤ x36) ∧ (x36 ≤ x46) ∧ ((x46 - x34) ≥ 1) ∧ ((x36 - x34) ≤ (t - 1)) ∧ ((x46 - x36) ≤ (t - 1))) ∨ ((x46 ≤ x36) ∧ (x36 ≤ x34) ∧ ((x34 - x46) ≥ 1) ∧ ((x34 - x36) ≤ (t - 1)) ∧ ((x36 - x46) ≤ (t - 1))))) : (((x46 - x34) ≥ 1) ∨ ((x34 - x46) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x46 - x34) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x34 - x46) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause1812 (t x34 x36 x46 : ℝ) (h : (((x34 ≤ x36) ∧ (x36 ≤ x46) ∧ ((x46 - x34) ≥ 1) ∧ ((x36 - x34) ≤ (t - 1)) ∧ ((x46 - x36) ≤ (t - 1))) ∨ ((x46 ≤ x36) ∧ (x36 ≤ x34) ∧ ((x34 - x46) ≥ 1) ∧ ((x34 - x36) ≤ (t - 1)) ∧ ((x36 - x46) ≤ (t - 1))))) : (((x46 - x34) ≥ 1) ∨ ((x34 - x36) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x46 - x34) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x34 - x36) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause1813 (t x34 x36 x46 : ℝ) (h : (((x34 ≤ x36) ∧ (x36 ≤ x46) ∧ ((x46 - x34) ≥ 1) ∧ ((x36 - x34) ≤ (t - 1)) ∧ ((x46 - x36) ≤ (t - 1))) ∨ ((x46 ≤ x36) ∧ (x36 ≤ x34) ∧ ((x34 - x46) ≥ 1) ∧ ((x34 - x36) ≤ (t - 1)) ∧ ((x36 - x46) ≤ (t - 1))))) : (((x46 - x34) ≥ 1) ∨ ((x36 - x46) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x46 - x34) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x36 - x46) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause1814 (t x34 x36 x46 : ℝ) (h : (((x34 ≤ x36) ∧ (x36 ≤ x46) ∧ ((x46 - x34) ≥ 1) ∧ ((x36 - x34) ≤ (t - 1)) ∧ ((x46 - x36) ≤ (t - 1))) ∨ ((x46 ≤ x36) ∧ (x36 ≤ x34) ∧ ((x34 - x46) ≥ 1) ∧ ((x34 - x36) ≤ (t - 1)) ∧ ((x36 - x46) ≤ (t - 1))))) : (((x36 - x34) ≤ (t - 1)) ∨ (x46 ≤ x36)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x36 - x34) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x46 ≤ x36) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause1815 (t x34 x36 x46 : ℝ) (h : (((x34 ≤ x36) ∧ (x36 ≤ x46) ∧ ((x46 - x34) ≥ 1) ∧ ((x36 - x34) ≤ (t - 1)) ∧ ((x46 - x36) ≤ (t - 1))) ∨ ((x46 ≤ x36) ∧ (x36 ≤ x34) ∧ ((x34 - x46) ≥ 1) ∧ ((x34 - x36) ≤ (t - 1)) ∧ ((x36 - x46) ≤ (t - 1))))) : (((x36 - x34) ≤ (t - 1)) ∨ (x36 ≤ x34)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x36 - x34) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x36 ≤ x34) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause1816 (t x34 x36 x46 : ℝ) (h : (((x34 ≤ x36) ∧ (x36 ≤ x46) ∧ ((x46 - x34) ≥ 1) ∧ ((x36 - x34) ≤ (t - 1)) ∧ ((x46 - x36) ≤ (t - 1))) ∨ ((x46 ≤ x36) ∧ (x36 ≤ x34) ∧ ((x34 - x46) ≥ 1) ∧ ((x34 - x36) ≤ (t - 1)) ∧ ((x36 - x46) ≤ (t - 1))))) : (((x36 - x34) ≤ (t - 1)) ∨ ((x34 - x46) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x36 - x34) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x34 - x46) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause1817 (t x34 x36 x46 : ℝ) (h : (((x34 ≤ x36) ∧ (x36 ≤ x46) ∧ ((x46 - x34) ≥ 1) ∧ ((x36 - x34) ≤ (t - 1)) ∧ ((x46 - x36) ≤ (t - 1))) ∨ ((x46 ≤ x36) ∧ (x36 ≤ x34) ∧ ((x34 - x46) ≥ 1) ∧ ((x34 - x36) ≤ (t - 1)) ∧ ((x36 - x46) ≤ (t - 1))))) : (((x36 - x34) ≤ (t - 1)) ∨ ((x34 - x36) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x36 - x34) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x34 - x36) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause1818 (t x34 x36 x46 : ℝ) (h : (((x34 ≤ x36) ∧ (x36 ≤ x46) ∧ ((x46 - x34) ≥ 1) ∧ ((x36 - x34) ≤ (t - 1)) ∧ ((x46 - x36) ≤ (t - 1))) ∨ ((x46 ≤ x36) ∧ (x36 ≤ x34) ∧ ((x34 - x46) ≥ 1) ∧ ((x34 - x36) ≤ (t - 1)) ∧ ((x36 - x46) ≤ (t - 1))))) : (((x36 - x34) ≤ (t - 1)) ∨ ((x36 - x46) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x36 - x34) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x36 - x46) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause1819 (t x34 x36 x46 : ℝ) (h : (((x34 ≤ x36) ∧ (x36 ≤ x46) ∧ ((x46 - x34) ≥ 1) ∧ ((x36 - x34) ≤ (t - 1)) ∧ ((x46 - x36) ≤ (t - 1))) ∨ ((x46 ≤ x36) ∧ (x36 ≤ x34) ∧ ((x34 - x46) ≥ 1) ∧ ((x34 - x36) ≤ (t - 1)) ∧ ((x36 - x46) ≤ (t - 1))))) : (((x46 - x36) ≤ (t - 1)) ∨ (x46 ≤ x36)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x46 - x36) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x46 ≤ x36) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause1820 (t x34 x36 x46 : ℝ) (h : (((x34 ≤ x36) ∧ (x36 ≤ x46) ∧ ((x46 - x34) ≥ 1) ∧ ((x36 - x34) ≤ (t - 1)) ∧ ((x46 - x36) ≤ (t - 1))) ∨ ((x46 ≤ x36) ∧ (x36 ≤ x34) ∧ ((x34 - x46) ≥ 1) ∧ ((x34 - x36) ≤ (t - 1)) ∧ ((x36 - x46) ≤ (t - 1))))) : (((x46 - x36) ≤ (t - 1)) ∨ (x36 ≤ x34)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x46 - x36) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x36 ≤ x34) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause1821 (t x34 x36 x46 : ℝ) (h : (((x34 ≤ x36) ∧ (x36 ≤ x46) ∧ ((x46 - x34) ≥ 1) ∧ ((x36 - x34) ≤ (t - 1)) ∧ ((x46 - x36) ≤ (t - 1))) ∨ ((x46 ≤ x36) ∧ (x36 ≤ x34) ∧ ((x34 - x46) ≥ 1) ∧ ((x34 - x36) ≤ (t - 1)) ∧ ((x36 - x46) ≤ (t - 1))))) : (((x46 - x36) ≤ (t - 1)) ∨ ((x34 - x46) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x46 - x36) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x34 - x46) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause1822 (t x34 x36 x46 : ℝ) (h : (((x34 ≤ x36) ∧ (x36 ≤ x46) ∧ ((x46 - x34) ≥ 1) ∧ ((x36 - x34) ≤ (t - 1)) ∧ ((x46 - x36) ≤ (t - 1))) ∨ ((x46 ≤ x36) ∧ (x36 ≤ x34) ∧ ((x34 - x46) ≥ 1) ∧ ((x34 - x36) ≤ (t - 1)) ∧ ((x36 - x46) ≤ (t - 1))))) : (((x46 - x36) ≤ (t - 1)) ∨ ((x34 - x36) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x46 - x36) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x34 - x36) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause1823 (t x34 x36 x46 : ℝ) (h : (((x34 ≤ x36) ∧ (x36 ≤ x46) ∧ ((x46 - x34) ≥ 1) ∧ ((x36 - x34) ≤ (t - 1)) ∧ ((x46 - x36) ≤ (t - 1))) ∨ ((x46 ≤ x36) ∧ (x36 ≤ x34) ∧ ((x34 - x46) ≥ 1) ∧ ((x34 - x36) ≤ (t - 1)) ∧ ((x36 - x46) ≤ (t - 1))))) : (((x46 - x36) ≤ (t - 1)) ∨ ((x36 - x46) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x46 - x36) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x36 - x46) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause1824 (t x45 x46 x56 : ℝ) : (((t + ((-1) * x46)) ≤ 0) ∨ ((t + x45 + ((-1) * x46)) ≥ 1) ∨ (¬ (x56 ≥ 0)) ∨ (¬ ((x45 + ((-1) * x56)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((t + ((-1) * x46)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + x45 + ((-1) * x46)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x56 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x45 + ((-1) * x56)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr hh)))
  have h := NineTheoryTrial.th105 t x45 x46 x56
  exact (fun hh => (fun hh => hh) (hh (And.intro u2 (And.intro u1 (And.intro u3 u0))))) h

theorem clause1827 (t x45 x46 x56 : ℝ) : (((x45 + ((-1) * x56)) ≥ 1) ∨ ((x45 + ((-1) * x46)) ≤ 0) ∨ (¬ (x45 ≤ x46)) ∨ (¬ (x46 ≤ x56)) ∨ (¬ ((x56 - x45) ≥ 1)) ∨ (¬ ((x46 - x45) ≤ (t - 1))) ∨ (¬ ((x56 - x46) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x45 + ((-1) * x56)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x45 + ((-1) * x46)) ≤ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x45 ≤ x46) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x46 ≤ x56) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x56 - x45) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x46 - x45) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x56 - x46) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th107 t x45 x46 x56
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 (hh).1) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause1831 (t x45 x46 x56 : ℝ) : (((x46 + ((-1) * x56)) ≤ 0) ∨ ((x45 + ((-1) * x46)) ≥ 0) ∨ (¬ (x45 ≤ x46)) ∨ (¬ (x46 ≤ x56)) ∨ (¬ ((x56 - x45) ≥ 1)) ∨ (¬ ((x46 - x45) ≤ (t - 1))) ∨ (¬ ((x56 - x46) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x46 + ((-1) * x56)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x45 + ((-1) * x46)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x45 ≤ x46) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x46 ≤ x56) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x56 - x45) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x46 - x45) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x56 - x46) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th107 t x45 x46 x56
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause1832 (t x45 x46 x56 : ℝ) : (((x46 + ((-1) * x56)) ≤ 0) ∨ ((x45 + ((-1) * x56)) ≥ 1) ∨ (¬ (x45 ≤ x46)) ∨ (¬ (x46 ≤ x56)) ∨ (¬ ((x56 - x45) ≥ 1)) ∨ (¬ ((x46 - x45) ≤ (t - 1))) ∨ (¬ ((x56 - x46) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x46 + ((-1) * x56)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x45 + ((-1) * x56)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x45 ≤ x46) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x46 ≤ x56) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x56 - x45) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x46 - x45) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x56 - x46) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th107 t x45 x46 x56
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause1835 (t x45 x46 x56 : ℝ) : (((x45 + ((-1) * x56)) ≤ (-1)) ∨ ((x46 + ((-1) * x56)) ≥ 0) ∨ (¬ (x45 ≤ x46)) ∨ (¬ (x46 ≤ x56)) ∨ (¬ ((x56 - x45) ≥ 1)) ∨ (¬ ((x46 - x45) ≤ (t - 1))) ∨ (¬ ((x56 - x46) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x45 + ((-1) * x56)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x46 + ((-1) * x56)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x45 ≤ x46) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x46 ≤ x56) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x56 - x45) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x46 - x45) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x56 - x46) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th107 t x45 x46 x56
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause1836 (t x45 x46 x56 : ℝ) : (((x45 + ((-1) * x56)) ≤ (-1)) ∨ ((x45 + ((-1) * x46)) ≥ 0) ∨ (¬ (x45 ≤ x46)) ∨ (¬ (x46 ≤ x56)) ∨ (¬ ((x56 - x45) ≥ 1)) ∨ (¬ ((x46 - x45) ≤ (t - 1))) ∨ (¬ ((x56 - x46) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x45 + ((-1) * x56)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x45 + ((-1) * x46)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x45 ≤ x46) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x46 ≤ x56) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x56 - x45) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x46 - x45) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x56 - x46) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th107 t x45 x46 x56
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause1837 (t x45 x46 x56 : ℝ) : (((x45 + ((-1) * x56)) ≥ 1) ∨ ((x45 + ((-1) * x56)) ≤ (-1)) ∨ (¬ (x45 ≤ x46)) ∨ (¬ (x46 ≤ x56)) ∨ (¬ ((x56 - x45) ≥ 1)) ∨ (¬ ((x46 - x45) ≤ (t - 1))) ∨ (¬ ((x56 - x46) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x45 + ((-1) * x56)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x45 + ((-1) * x56)) ≤ (-1)) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x45 ≤ x46) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x46 ≤ x56) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x56 - x45) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x46 - x45) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x56 - x46) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th107 t x45 x46 x56
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 (((hh).2).2).1) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause1838 (t x45 x46 x56 : ℝ) : (((x45 + ((-1) * x56)) ≤ (-1)) ∨ ((t + ((-1) * x45) + x46) ≥ 1) ∨ (¬ (x45 ≤ x46)) ∨ (¬ (x46 ≤ x56)) ∨ (¬ ((x56 - x45) ≥ 1)) ∨ (¬ ((x46 - x45) ≤ (t - 1))) ∨ (¬ ((x56 - x46) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x45 + ((-1) * x56)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + ((-1) * x45) + x46) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x45 ≤ x46) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x46 ≤ x56) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x56 - x45) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x46 - x45) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x56 - x46) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th107 t x45 x46 x56
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause1839 (t x45 x46 x56 : ℝ) : (((x45 + ((-1) * x56)) ≤ (-1)) ∨ ((t + ((-1) * x46) + x56) ≥ 1) ∨ (¬ (x45 ≤ x46)) ∨ (¬ (x46 ≤ x56)) ∨ (¬ ((x56 - x45) ≥ 1)) ∨ (¬ ((x46 - x45) ≤ (t - 1))) ∨ (¬ ((x56 - x46) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x45 + ((-1) * x56)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + ((-1) * x46) + x56) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x45 ≤ x46) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x46 ≤ x56) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x56 - x45) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x46 - x45) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x56 - x46) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th107 t x45 x46 x56
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause1842 (t x45 x46 x56 : ℝ) : (((t + x45 + ((-1) * x46)) ≥ 1) ∨ ((x45 + ((-1) * x56)) ≥ 1) ∨ (¬ (x45 ≤ x46)) ∨ (¬ (x46 ≤ x56)) ∨ (¬ ((x56 - x45) ≥ 1)) ∨ (¬ ((x46 - x45) ≤ (t - 1))) ∨ (¬ ((x56 - x46) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((t + x45 + ((-1) * x46)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x45 + ((-1) * x56)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x45 ≤ x46) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x46 ≤ x56) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x56 - x45) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x46 - x45) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x56 - x46) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th107 t x45 x46 x56
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause1847 (t x45 x46 x56 : ℝ) : (((x45 + ((-1) * x56)) ≥ 1) ∨ ((t + x46 + ((-1) * x56)) ≥ 1) ∨ (¬ (x45 ≤ x46)) ∨ (¬ (x46 ≤ x56)) ∨ (¬ ((x56 - x45) ≥ 1)) ∨ (¬ ((x46 - x45) ≤ (t - 1))) ∨ (¬ ((x56 - x46) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x45 + ((-1) * x56)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + x46 + ((-1) * x56)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x45 ≤ x46) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x46 ≤ x56) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x56 - x45) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x46 - x45) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x56 - x46) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th107 t x45 x46 x56
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 ((((hh).2).2).2).2) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause1852 (t x45 x46 x56 : ℝ) : (((x45 + ((-1) * x56)) ≥ 1) ∨ ((x45 + ((-1) * x46)) ≤ 0) ∨ (¬ (x56 ≤ x46)) ∨ (¬ (x46 ≤ x45)) ∨ (¬ ((x45 - x56) ≥ 1)) ∨ (¬ ((x45 - x46) ≤ (t - 1))) ∨ (¬ ((x46 - x56) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x45 + ((-1) * x56)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x45 + ((-1) * x46)) ≤ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x56 ≤ x46) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x46 ≤ x45) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x45 - x56) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x45 - x46) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x46 - x56) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th107 t x45 x46 x56
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 (hh).1) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause1853 (t x45 x46 x56 : ℝ) : (((x45 + ((-1) * x46)) ≤ 0) ∨ ((t + ((-1) * x45) + x46) ≥ 1) ∨ (¬ (x56 ≤ x46)) ∨ (¬ (x46 ≤ x45)) ∨ (¬ ((x45 - x56) ≥ 1)) ∨ (¬ ((x45 - x46) ≤ (t - 1))) ∨ (¬ ((x46 - x56) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x45 + ((-1) * x46)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + ((-1) * x45) + x46) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x56 ≤ x46) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x46 ≤ x45) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x45 - x56) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x45 - x46) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x46 - x56) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th107 t x45 x46 x56
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause1857 (t x45 x46 x56 : ℝ) : (((x46 + ((-1) * x56)) ≤ 0) ∨ ((x45 + ((-1) * x56)) ≥ 1) ∨ (¬ (x56 ≤ x46)) ∨ (¬ (x46 ≤ x45)) ∨ (¬ ((x45 - x56) ≥ 1)) ∨ (¬ ((x45 - x46) ≤ (t - 1))) ∨ (¬ ((x46 - x56) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x46 + ((-1) * x56)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x45 + ((-1) * x56)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x56 ≤ x46) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x46 ≤ x45) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x45 - x56) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x45 - x46) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x46 - x56) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th107 t x45 x46 x56
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause1860 (t x45 x46 x56 : ℝ) : (((x45 + ((-1) * x56)) ≤ (-1)) ∨ ((x46 + ((-1) * x56)) ≥ 0) ∨ (¬ (x56 ≤ x46)) ∨ (¬ (x46 ≤ x45)) ∨ (¬ ((x45 - x56) ≥ 1)) ∨ (¬ ((x45 - x46) ≤ (t - 1))) ∨ (¬ ((x46 - x56) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x45 + ((-1) * x56)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x46 + ((-1) * x56)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x56 ≤ x46) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x46 ≤ x45) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x45 - x56) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x45 - x46) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x46 - x56) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th107 t x45 x46 x56
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause1861 (t x45 x46 x56 : ℝ) : (((x45 + ((-1) * x56)) ≤ (-1)) ∨ ((x45 + ((-1) * x46)) ≥ 0) ∨ (¬ (x56 ≤ x46)) ∨ (¬ (x46 ≤ x45)) ∨ (¬ ((x45 - x56) ≥ 1)) ∨ (¬ ((x45 - x46) ≤ (t - 1))) ∨ (¬ ((x46 - x56) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x45 + ((-1) * x56)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x45 + ((-1) * x46)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x56 ≤ x46) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x46 ≤ x45) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x45 - x56) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x45 - x46) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x46 - x56) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th107 t x45 x46 x56
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause1862 (t x45 x46 x56 : ℝ) : (((x45 + ((-1) * x56)) ≥ 1) ∨ ((x45 + ((-1) * x56)) ≤ (-1)) ∨ (¬ (x56 ≤ x46)) ∨ (¬ (x46 ≤ x45)) ∨ (¬ ((x45 - x56) ≥ 1)) ∨ (¬ ((x45 - x46) ≤ (t - 1))) ∨ (¬ ((x46 - x56) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x45 + ((-1) * x56)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x45 + ((-1) * x56)) ≤ (-1)) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x56 ≤ x46) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x46 ≤ x45) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x45 - x56) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x45 - x46) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x46 - x56) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th107 t x45 x46 x56
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 (((hh).2).2).1) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause1864 (t x45 x46 x56 : ℝ) : (((x45 + ((-1) * x56)) ≤ (-1)) ∨ ((t + ((-1) * x46) + x56) ≥ 1) ∨ (¬ (x56 ≤ x46)) ∨ (¬ (x46 ≤ x45)) ∨ (¬ ((x45 - x56) ≥ 1)) ∨ (¬ ((x45 - x46) ≤ (t - 1))) ∨ (¬ ((x46 - x56) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x45 + ((-1) * x56)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + ((-1) * x46) + x56) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x56 ≤ x46) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x46 ≤ x45) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x45 - x56) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x45 - x46) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x46 - x56) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th107 t x45 x46 x56
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause1867 (t x45 x46 x56 : ℝ) : (((t + x45 + ((-1) * x46)) ≥ 1) ∨ ((x45 + ((-1) * x56)) ≥ 1) ∨ (¬ (x56 ≤ x46)) ∨ (¬ (x46 ≤ x45)) ∨ (¬ ((x45 - x56) ≥ 1)) ∨ (¬ ((x45 - x46) ≤ (t - 1))) ∨ (¬ ((x46 - x56) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((t + x45 + ((-1) * x46)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x45 + ((-1) * x56)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x56 ≤ x46) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x46 ≤ x45) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x45 - x56) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x45 - x46) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x46 - x56) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th107 t x45 x46 x56
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause1870 (t x45 x46 x56 : ℝ) : (((t + x46 + ((-1) * x56)) ≥ 1) ∨ ((x46 + ((-1) * x56)) ≥ 0) ∨ (¬ (x56 ≤ x46)) ∨ (¬ (x46 ≤ x45)) ∨ (¬ ((x45 - x56) ≥ 1)) ∨ (¬ ((x45 - x46) ≤ (t - 1))) ∨ (¬ ((x46 - x56) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((t + x46 + ((-1) * x56)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x46 + ((-1) * x56)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x56 ≤ x46) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x46 ≤ x45) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x45 - x56) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x45 - x46) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x46 - x56) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th107 t x45 x46 x56
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 (hh).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause1872 (t x45 x46 x56 : ℝ) : (((x45 + ((-1) * x56)) ≥ 1) ∨ ((t + x46 + ((-1) * x56)) ≥ 1) ∨ (¬ (x56 ≤ x46)) ∨ (¬ (x46 ≤ x45)) ∨ (¬ ((x45 - x56) ≥ 1)) ∨ (¬ ((x45 - x46) ≤ (t - 1))) ∨ (¬ ((x46 - x56) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x45 + ((-1) * x56)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + x46 + ((-1) * x56)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x56 ≤ x46) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x46 ≤ x45) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x45 - x56) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x45 - x46) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x46 - x56) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th107 t x45 x46 x56
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 ((((hh).2).2).2).2) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause1925 (t x45 x46 x56 : ℝ) (h : (((x45 ≤ x46) ∧ (x46 ≤ x56) ∧ ((x56 - x45) ≥ 1) ∧ ((x46 - x45) ≤ (t - 1)) ∧ ((x56 - x46) ≤ (t - 1))) ∨ ((x56 ≤ x46) ∧ (x46 ≤ x45) ∧ ((x45 - x56) ≥ 1) ∧ ((x45 - x46) ≤ (t - 1)) ∧ ((x46 - x56) ≤ (t - 1))))) : ((x45 ≤ x46) ∨ (x56 ≤ x46)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x45 ≤ x46) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x56 ≤ x46) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause1926 (t x45 x46 x56 : ℝ) (h : (((x45 ≤ x46) ∧ (x46 ≤ x56) ∧ ((x56 - x45) ≥ 1) ∧ ((x46 - x45) ≤ (t - 1)) ∧ ((x56 - x46) ≤ (t - 1))) ∨ ((x56 ≤ x46) ∧ (x46 ≤ x45) ∧ ((x45 - x56) ≥ 1) ∧ ((x45 - x46) ≤ (t - 1)) ∧ ((x46 - x56) ≤ (t - 1))))) : ((x45 ≤ x46) ∨ (x46 ≤ x45)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x45 ≤ x46) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x46 ≤ x45) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause1927 (t x45 x46 x56 : ℝ) (h : (((x45 ≤ x46) ∧ (x46 ≤ x56) ∧ ((x56 - x45) ≥ 1) ∧ ((x46 - x45) ≤ (t - 1)) ∧ ((x56 - x46) ≤ (t - 1))) ∨ ((x56 ≤ x46) ∧ (x46 ≤ x45) ∧ ((x45 - x56) ≥ 1) ∧ ((x45 - x46) ≤ (t - 1)) ∧ ((x46 - x56) ≤ (t - 1))))) : ((x45 ≤ x46) ∨ ((x45 - x56) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x45 ≤ x46) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x45 - x56) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause1928 (t x45 x46 x56 : ℝ) (h : (((x45 ≤ x46) ∧ (x46 ≤ x56) ∧ ((x56 - x45) ≥ 1) ∧ ((x46 - x45) ≤ (t - 1)) ∧ ((x56 - x46) ≤ (t - 1))) ∨ ((x56 ≤ x46) ∧ (x46 ≤ x45) ∧ ((x45 - x56) ≥ 1) ∧ ((x45 - x46) ≤ (t - 1)) ∧ ((x46 - x56) ≤ (t - 1))))) : ((x45 ≤ x46) ∨ ((x45 - x46) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x45 ≤ x46) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x45 - x46) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause1929 (t x45 x46 x56 : ℝ) (h : (((x45 ≤ x46) ∧ (x46 ≤ x56) ∧ ((x56 - x45) ≥ 1) ∧ ((x46 - x45) ≤ (t - 1)) ∧ ((x56 - x46) ≤ (t - 1))) ∨ ((x56 ≤ x46) ∧ (x46 ≤ x45) ∧ ((x45 - x56) ≥ 1) ∧ ((x45 - x46) ≤ (t - 1)) ∧ ((x46 - x56) ≤ (t - 1))))) : ((x45 ≤ x46) ∨ ((x46 - x56) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x45 ≤ x46) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x46 - x56) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause1930 (t x45 x46 x56 : ℝ) (h : (((x45 ≤ x46) ∧ (x46 ≤ x56) ∧ ((x56 - x45) ≥ 1) ∧ ((x46 - x45) ≤ (t - 1)) ∧ ((x56 - x46) ≤ (t - 1))) ∨ ((x56 ≤ x46) ∧ (x46 ≤ x45) ∧ ((x45 - x56) ≥ 1) ∧ ((x45 - x46) ≤ (t - 1)) ∧ ((x46 - x56) ≤ (t - 1))))) : ((x46 ≤ x56) ∨ (x56 ≤ x46)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x46 ≤ x56) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x56 ≤ x46) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause1931 (t x45 x46 x56 : ℝ) (h : (((x45 ≤ x46) ∧ (x46 ≤ x56) ∧ ((x56 - x45) ≥ 1) ∧ ((x46 - x45) ≤ (t - 1)) ∧ ((x56 - x46) ≤ (t - 1))) ∨ ((x56 ≤ x46) ∧ (x46 ≤ x45) ∧ ((x45 - x56) ≥ 1) ∧ ((x45 - x46) ≤ (t - 1)) ∧ ((x46 - x56) ≤ (t - 1))))) : ((x46 ≤ x56) ∨ (x46 ≤ x45)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x46 ≤ x56) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x46 ≤ x45) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause1932 (t x45 x46 x56 : ℝ) (h : (((x45 ≤ x46) ∧ (x46 ≤ x56) ∧ ((x56 - x45) ≥ 1) ∧ ((x46 - x45) ≤ (t - 1)) ∧ ((x56 - x46) ≤ (t - 1))) ∨ ((x56 ≤ x46) ∧ (x46 ≤ x45) ∧ ((x45 - x56) ≥ 1) ∧ ((x45 - x46) ≤ (t - 1)) ∧ ((x46 - x56) ≤ (t - 1))))) : ((x46 ≤ x56) ∨ ((x45 - x56) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x46 ≤ x56) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x45 - x56) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause1933 (t x45 x46 x56 : ℝ) (h : (((x45 ≤ x46) ∧ (x46 ≤ x56) ∧ ((x56 - x45) ≥ 1) ∧ ((x46 - x45) ≤ (t - 1)) ∧ ((x56 - x46) ≤ (t - 1))) ∨ ((x56 ≤ x46) ∧ (x46 ≤ x45) ∧ ((x45 - x56) ≥ 1) ∧ ((x45 - x46) ≤ (t - 1)) ∧ ((x46 - x56) ≤ (t - 1))))) : ((x46 ≤ x56) ∨ ((x45 - x46) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x46 ≤ x56) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x45 - x46) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause1934 (t x45 x46 x56 : ℝ) (h : (((x45 ≤ x46) ∧ (x46 ≤ x56) ∧ ((x56 - x45) ≥ 1) ∧ ((x46 - x45) ≤ (t - 1)) ∧ ((x56 - x46) ≤ (t - 1))) ∨ ((x56 ≤ x46) ∧ (x46 ≤ x45) ∧ ((x45 - x56) ≥ 1) ∧ ((x45 - x46) ≤ (t - 1)) ∧ ((x46 - x56) ≤ (t - 1))))) : ((x46 ≤ x56) ∨ ((x46 - x56) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x46 ≤ x56) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x46 - x56) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause1935 (t x45 x46 x56 : ℝ) (h : (((x45 ≤ x46) ∧ (x46 ≤ x56) ∧ ((x56 - x45) ≥ 1) ∧ ((x46 - x45) ≤ (t - 1)) ∧ ((x56 - x46) ≤ (t - 1))) ∨ ((x56 ≤ x46) ∧ (x46 ≤ x45) ∧ ((x45 - x56) ≥ 1) ∧ ((x45 - x46) ≤ (t - 1)) ∧ ((x46 - x56) ≤ (t - 1))))) : (((x56 - x45) ≥ 1) ∨ (x56 ≤ x46)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x56 - x45) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x56 ≤ x46) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause1936 (t x45 x46 x56 : ℝ) (h : (((x45 ≤ x46) ∧ (x46 ≤ x56) ∧ ((x56 - x45) ≥ 1) ∧ ((x46 - x45) ≤ (t - 1)) ∧ ((x56 - x46) ≤ (t - 1))) ∨ ((x56 ≤ x46) ∧ (x46 ≤ x45) ∧ ((x45 - x56) ≥ 1) ∧ ((x45 - x46) ≤ (t - 1)) ∧ ((x46 - x56) ≤ (t - 1))))) : (((x56 - x45) ≥ 1) ∨ (x46 ≤ x45)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x56 - x45) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x46 ≤ x45) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause1937 (t x45 x46 x56 : ℝ) (h : (((x45 ≤ x46) ∧ (x46 ≤ x56) ∧ ((x56 - x45) ≥ 1) ∧ ((x46 - x45) ≤ (t - 1)) ∧ ((x56 - x46) ≤ (t - 1))) ∨ ((x56 ≤ x46) ∧ (x46 ≤ x45) ∧ ((x45 - x56) ≥ 1) ∧ ((x45 - x46) ≤ (t - 1)) ∧ ((x46 - x56) ≤ (t - 1))))) : (((x56 - x45) ≥ 1) ∨ ((x45 - x56) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x56 - x45) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x45 - x56) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause1938 (t x45 x46 x56 : ℝ) (h : (((x45 ≤ x46) ∧ (x46 ≤ x56) ∧ ((x56 - x45) ≥ 1) ∧ ((x46 - x45) ≤ (t - 1)) ∧ ((x56 - x46) ≤ (t - 1))) ∨ ((x56 ≤ x46) ∧ (x46 ≤ x45) ∧ ((x45 - x56) ≥ 1) ∧ ((x45 - x46) ≤ (t - 1)) ∧ ((x46 - x56) ≤ (t - 1))))) : (((x56 - x45) ≥ 1) ∨ ((x45 - x46) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x56 - x45) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x45 - x46) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause1939 (t x45 x46 x56 : ℝ) (h : (((x45 ≤ x46) ∧ (x46 ≤ x56) ∧ ((x56 - x45) ≥ 1) ∧ ((x46 - x45) ≤ (t - 1)) ∧ ((x56 - x46) ≤ (t - 1))) ∨ ((x56 ≤ x46) ∧ (x46 ≤ x45) ∧ ((x45 - x56) ≥ 1) ∧ ((x45 - x46) ≤ (t - 1)) ∧ ((x46 - x56) ≤ (t - 1))))) : (((x56 - x45) ≥ 1) ∨ ((x46 - x56) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x56 - x45) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x46 - x56) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause1940 (t x45 x46 x56 : ℝ) (h : (((x45 ≤ x46) ∧ (x46 ≤ x56) ∧ ((x56 - x45) ≥ 1) ∧ ((x46 - x45) ≤ (t - 1)) ∧ ((x56 - x46) ≤ (t - 1))) ∨ ((x56 ≤ x46) ∧ (x46 ≤ x45) ∧ ((x45 - x56) ≥ 1) ∧ ((x45 - x46) ≤ (t - 1)) ∧ ((x46 - x56) ≤ (t - 1))))) : (((x46 - x45) ≤ (t - 1)) ∨ (x56 ≤ x46)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x46 - x45) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x56 ≤ x46) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause1941 (t x45 x46 x56 : ℝ) (h : (((x45 ≤ x46) ∧ (x46 ≤ x56) ∧ ((x56 - x45) ≥ 1) ∧ ((x46 - x45) ≤ (t - 1)) ∧ ((x56 - x46) ≤ (t - 1))) ∨ ((x56 ≤ x46) ∧ (x46 ≤ x45) ∧ ((x45 - x56) ≥ 1) ∧ ((x45 - x46) ≤ (t - 1)) ∧ ((x46 - x56) ≤ (t - 1))))) : (((x46 - x45) ≤ (t - 1)) ∨ (x46 ≤ x45)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x46 - x45) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x46 ≤ x45) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause1942 (t x45 x46 x56 : ℝ) (h : (((x45 ≤ x46) ∧ (x46 ≤ x56) ∧ ((x56 - x45) ≥ 1) ∧ ((x46 - x45) ≤ (t - 1)) ∧ ((x56 - x46) ≤ (t - 1))) ∨ ((x56 ≤ x46) ∧ (x46 ≤ x45) ∧ ((x45 - x56) ≥ 1) ∧ ((x45 - x46) ≤ (t - 1)) ∧ ((x46 - x56) ≤ (t - 1))))) : (((x46 - x45) ≤ (t - 1)) ∨ ((x45 - x56) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x46 - x45) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x45 - x56) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause1943 (t x45 x46 x56 : ℝ) (h : (((x45 ≤ x46) ∧ (x46 ≤ x56) ∧ ((x56 - x45) ≥ 1) ∧ ((x46 - x45) ≤ (t - 1)) ∧ ((x56 - x46) ≤ (t - 1))) ∨ ((x56 ≤ x46) ∧ (x46 ≤ x45) ∧ ((x45 - x56) ≥ 1) ∧ ((x45 - x46) ≤ (t - 1)) ∧ ((x46 - x56) ≤ (t - 1))))) : (((x46 - x45) ≤ (t - 1)) ∨ ((x45 - x46) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x46 - x45) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x45 - x46) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause1944 (t x45 x46 x56 : ℝ) (h : (((x45 ≤ x46) ∧ (x46 ≤ x56) ∧ ((x56 - x45) ≥ 1) ∧ ((x46 - x45) ≤ (t - 1)) ∧ ((x56 - x46) ≤ (t - 1))) ∨ ((x56 ≤ x46) ∧ (x46 ≤ x45) ∧ ((x45 - x56) ≥ 1) ∧ ((x45 - x46) ≤ (t - 1)) ∧ ((x46 - x56) ≤ (t - 1))))) : (((x46 - x45) ≤ (t - 1)) ∨ ((x46 - x56) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x46 - x45) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x46 - x56) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause1945 (t x45 x46 x56 : ℝ) (h : (((x45 ≤ x46) ∧ (x46 ≤ x56) ∧ ((x56 - x45) ≥ 1) ∧ ((x46 - x45) ≤ (t - 1)) ∧ ((x56 - x46) ≤ (t - 1))) ∨ ((x56 ≤ x46) ∧ (x46 ≤ x45) ∧ ((x45 - x56) ≥ 1) ∧ ((x45 - x46) ≤ (t - 1)) ∧ ((x46 - x56) ≤ (t - 1))))) : (((x56 - x46) ≤ (t - 1)) ∨ (x56 ≤ x46)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x56 - x46) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x56 ≤ x46) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause1946 (t x45 x46 x56 : ℝ) (h : (((x45 ≤ x46) ∧ (x46 ≤ x56) ∧ ((x56 - x45) ≥ 1) ∧ ((x46 - x45) ≤ (t - 1)) ∧ ((x56 - x46) ≤ (t - 1))) ∨ ((x56 ≤ x46) ∧ (x46 ≤ x45) ∧ ((x45 - x56) ≥ 1) ∧ ((x45 - x46) ≤ (t - 1)) ∧ ((x46 - x56) ≤ (t - 1))))) : (((x56 - x46) ≤ (t - 1)) ∨ (x46 ≤ x45)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x56 - x46) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x46 ≤ x45) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause1947 (t x45 x46 x56 : ℝ) (h : (((x45 ≤ x46) ∧ (x46 ≤ x56) ∧ ((x56 - x45) ≥ 1) ∧ ((x46 - x45) ≤ (t - 1)) ∧ ((x56 - x46) ≤ (t - 1))) ∨ ((x56 ≤ x46) ∧ (x46 ≤ x45) ∧ ((x45 - x56) ≥ 1) ∧ ((x45 - x46) ≤ (t - 1)) ∧ ((x46 - x56) ≤ (t - 1))))) : (((x56 - x46) ≤ (t - 1)) ∨ ((x45 - x56) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x56 - x46) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x45 - x56) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause1948 (t x45 x46 x56 : ℝ) (h : (((x45 ≤ x46) ∧ (x46 ≤ x56) ∧ ((x56 - x45) ≥ 1) ∧ ((x46 - x45) ≤ (t - 1)) ∧ ((x56 - x46) ≤ (t - 1))) ∨ ((x56 ≤ x46) ∧ (x46 ≤ x45) ∧ ((x45 - x56) ≥ 1) ∧ ((x45 - x46) ≤ (t - 1)) ∧ ((x46 - x56) ≤ (t - 1))))) : (((x56 - x46) ≤ (t - 1)) ∨ ((x45 - x46) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x56 - x46) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x45 - x46) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause1949 (t x45 x46 x56 : ℝ) (h : (((x45 ≤ x46) ∧ (x46 ≤ x56) ∧ ((x56 - x45) ≥ 1) ∧ ((x46 - x45) ≤ (t - 1)) ∧ ((x56 - x46) ≤ (t - 1))) ∨ ((x56 ≤ x46) ∧ (x46 ≤ x45) ∧ ((x45 - x56) ≥ 1) ∧ ((x45 - x46) ≤ (t - 1)) ∧ ((x46 - x56) ≤ (t - 1))))) : (((x56 - x46) ≤ (t - 1)) ∨ ((x46 - x56) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x56 - x46) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x46 - x56) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause1950 (x56 : ℝ) (h : (x56 ≥ 0)) : ((x56 ≥ 0)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x56 ≥ 0) := fun hh => hn hh
  exact u0 h

theorem clause1951 (x02 x24 x25 : ℝ) : ((¬ ((x02 + ((-1) * x25)) ≤ (-1))) ∨ (¬ ((x02 + ((-1) * x24)) ≥ 1)) ∨ (¬ ((x24 + ((-1) * x25)) ≥ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x02 + ((-1) * x25)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x02 + ((-1) * x24)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x24 + ((-1) * x25)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th110 x02 x24 x25
  exact (fun hh => (fun hh => hh u1) (hh (And.intro u0 u2))) h

theorem clause1952 (x02 x24 x25 : ℝ) : (((x02 + ((-1) * x24)) ≤ (-1)) ∨ (¬ ((x02 + ((-1) * x25)) ≤ (-1))) ∨ (¬ ((x24 + ((-1) * x25)) ≥ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x02 + ((-1) * x24)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ((x02 + ((-1) * x25)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x24 + ((-1) * x25)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th113 x02 x24 x25
  exact (fun hh => u0 (hh (And.intro u1 u2))) h

theorem clause1953 (x04 x46 : ℝ) : ((¬ ((x04 + ((-1) * x46)) ≤ (-1))) ∨ (¬ ((x04 + ((-1) * x46)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x04 + ((-1) * x46)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x04 + ((-1) * x46)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr hh)
  have h := NineTheoryTrial.th114 x04 x46
  exact (fun hh => (Or.elim hh (fun hh => hh u0) (fun zz => ((fun hh => hh u1) zz)))) h

theorem clause1954 (t x04 x06 x46 : ℝ) : (((x04 + ((-1) * x06)) ≤ 0) ∨ ((x06 + ((-1) * x46)) ≥ 0) ∨ (¬ (x04 ≤ x06)) ∨ (¬ (x06 ≤ x46)) ∨ (¬ ((x46 - x04) ≥ 1)) ∨ (¬ ((x06 - x04) ≤ (t - 1))) ∨ (¬ ((x46 - x06) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x04 + ((-1) * x06)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x06 + ((-1) * x46)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x04 ≤ x06) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x06 ≤ x46) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x46 - x04) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x06 - x04) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x46 - x06) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th116 t x04 x06 x46
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause1956 (t x04 x06 x46 : ℝ) : (((x04 + ((-1) * x46)) ≥ 1) ∨ ((x04 + ((-1) * x06)) ≤ 0) ∨ (¬ (x04 ≤ x06)) ∨ (¬ (x06 ≤ x46)) ∨ (¬ ((x46 - x04) ≥ 1)) ∨ (¬ ((x06 - x04) ≤ (t - 1))) ∨ (¬ ((x46 - x06) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x04 + ((-1) * x46)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x04 + ((-1) * x06)) ≤ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x04 ≤ x06) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x06 ≤ x46) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x46 - x04) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x06 - x04) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x46 - x06) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th116 t x04 x06 x46
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 (hh).1) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause1960 (t x04 x06 x46 : ℝ) : (((x06 + ((-1) * x46)) ≤ 0) ∨ ((x04 + ((-1) * x06)) ≥ 0) ∨ (¬ (x04 ≤ x06)) ∨ (¬ (x06 ≤ x46)) ∨ (¬ ((x46 - x04) ≥ 1)) ∨ (¬ ((x06 - x04) ≤ (t - 1))) ∨ (¬ ((x46 - x06) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x06 + ((-1) * x46)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x04 + ((-1) * x06)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x04 ≤ x06) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x06 ≤ x46) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x46 - x04) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x06 - x04) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x46 - x06) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th116 t x04 x06 x46
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause1961 (t x04 x06 x46 : ℝ) : (((x04 + ((-1) * x46)) ≥ 1) ∨ ((x06 + ((-1) * x46)) ≤ 0) ∨ (¬ (x04 ≤ x06)) ∨ (¬ (x06 ≤ x46)) ∨ (¬ ((x46 - x04) ≥ 1)) ∨ (¬ ((x06 - x04) ≤ (t - 1))) ∨ (¬ ((x46 - x06) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x04 + ((-1) * x46)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x06 + ((-1) * x46)) ≤ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x04 ≤ x06) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x06 ≤ x46) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x46 - x04) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x06 - x04) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x46 - x06) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th116 t x04 x06 x46
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 ((hh).2).1) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause1964 (t x04 x06 x46 : ℝ) : (((x04 + ((-1) * x46)) ≤ (-1)) ∨ ((x06 + ((-1) * x46)) ≥ 0) ∨ (¬ (x04 ≤ x06)) ∨ (¬ (x06 ≤ x46)) ∨ (¬ ((x46 - x04) ≥ 1)) ∨ (¬ ((x06 - x04) ≤ (t - 1))) ∨ (¬ ((x46 - x06) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x04 + ((-1) * x46)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x06 + ((-1) * x46)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x04 ≤ x06) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x06 ≤ x46) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x46 - x04) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x06 - x04) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x46 - x06) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th116 t x04 x06 x46
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause1965 (t x04 x06 x46 : ℝ) : (((x04 + ((-1) * x46)) ≤ (-1)) ∨ ((x04 + ((-1) * x06)) ≥ 0) ∨ (¬ (x04 ≤ x06)) ∨ (¬ (x06 ≤ x46)) ∨ (¬ ((x46 - x04) ≥ 1)) ∨ (¬ ((x06 - x04) ≤ (t - 1))) ∨ (¬ ((x46 - x06) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x04 + ((-1) * x46)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x04 + ((-1) * x06)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x04 ≤ x06) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x06 ≤ x46) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x46 - x04) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x06 - x04) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x46 - x06) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th116 t x04 x06 x46
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause1966 (t x04 x06 x46 : ℝ) : (((x04 + ((-1) * x46)) ≤ (-1)) ∨ ((x04 + ((-1) * x46)) ≥ 1) ∨ (¬ (x04 ≤ x06)) ∨ (¬ (x06 ≤ x46)) ∨ (¬ ((x46 - x04) ≥ 1)) ∨ (¬ ((x06 - x04) ≤ (t - 1))) ∨ (¬ ((x46 - x06) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x04 + ((-1) * x46)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x04 + ((-1) * x46)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x04 ≤ x06) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x06 ≤ x46) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x46 - x04) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x06 - x04) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x46 - x06) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th116 t x04 x06 x46
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause1968 (t x04 x06 x46 : ℝ) : (((x04 + ((-1) * x46)) ≤ (-1)) ∨ ((t + ((-1) * x06) + x46) ≥ 1) ∨ (¬ (x04 ≤ x06)) ∨ (¬ (x06 ≤ x46)) ∨ (¬ ((x46 - x04) ≥ 1)) ∨ (¬ ((x06 - x04) ≤ (t - 1))) ∨ (¬ ((x46 - x06) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x04 + ((-1) * x46)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + ((-1) * x06) + x46) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x04 ≤ x06) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x06 ≤ x46) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x46 - x04) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x06 - x04) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x46 - x06) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th116 t x04 x06 x46
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause1976 (t x04 x06 x46 : ℝ) : (((x04 + ((-1) * x46)) ≥ 1) ∨ ((t + x06 + ((-1) * x46)) ≥ 1) ∨ (¬ (x04 ≤ x06)) ∨ (¬ (x06 ≤ x46)) ∨ (¬ ((x46 - x04) ≥ 1)) ∨ (¬ ((x06 - x04) ≤ (t - 1))) ∨ (¬ ((x46 - x06) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x04 + ((-1) * x46)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + x06 + ((-1) * x46)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x04 ≤ x06) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x06 ≤ x46) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x46 - x04) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x06 - x04) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x46 - x06) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th116 t x04 x06 x46
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 ((((hh).2).2).2).2) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause1979 (t x04 x06 x46 : ℝ) : (((x04 + ((-1) * x06)) ≤ 0) ∨ ((x06 + ((-1) * x46)) ≥ 0) ∨ (¬ (x46 ≤ x06)) ∨ (¬ (x06 ≤ x04)) ∨ (¬ ((x04 - x46) ≥ 1)) ∨ (¬ ((x04 - x06) ≤ (t - 1))) ∨ (¬ ((x06 - x46) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x04 + ((-1) * x06)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x06 + ((-1) * x46)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x46 ≤ x06) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x06 ≤ x04) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x04 - x46) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x04 - x06) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x06 - x46) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th116 t x04 x06 x46
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause1981 (t x04 x06 x46 : ℝ) : (((x04 + ((-1) * x46)) ≥ 1) ∨ ((x04 + ((-1) * x06)) ≤ 0) ∨ (¬ (x46 ≤ x06)) ∨ (¬ (x06 ≤ x04)) ∨ (¬ ((x04 - x46) ≥ 1)) ∨ (¬ ((x04 - x06) ≤ (t - 1))) ∨ (¬ ((x06 - x46) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x04 + ((-1) * x46)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x04 + ((-1) * x06)) ≤ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x46 ≤ x06) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x06 ≤ x04) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x04 - x46) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x04 - x06) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x06 - x46) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th116 t x04 x06 x46
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 (hh).1) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause1985 (t x04 x06 x46 : ℝ) : (((x06 + ((-1) * x46)) ≤ 0) ∨ ((x04 + ((-1) * x06)) ≥ 0) ∨ (¬ (x46 ≤ x06)) ∨ (¬ (x06 ≤ x04)) ∨ (¬ ((x04 - x46) ≥ 1)) ∨ (¬ ((x04 - x06) ≤ (t - 1))) ∨ (¬ ((x06 - x46) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x06 + ((-1) * x46)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x04 + ((-1) * x06)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x46 ≤ x06) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x06 ≤ x04) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x04 - x46) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x04 - x06) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x06 - x46) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th116 t x04 x06 x46
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause1986 (t x04 x06 x46 : ℝ) : (((x04 + ((-1) * x46)) ≥ 1) ∨ ((x06 + ((-1) * x46)) ≤ 0) ∨ (¬ (x46 ≤ x06)) ∨ (¬ (x06 ≤ x04)) ∨ (¬ ((x04 - x46) ≥ 1)) ∨ (¬ ((x04 - x06) ≤ (t - 1))) ∨ (¬ ((x06 - x46) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x04 + ((-1) * x46)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x06 + ((-1) * x46)) ≤ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x46 ≤ x06) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x06 ≤ x04) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x04 - x46) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x04 - x06) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x06 - x46) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th116 t x04 x06 x46
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 ((hh).2).1) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause1989 (t x04 x06 x46 : ℝ) : (((x04 + ((-1) * x46)) ≤ (-1)) ∨ ((x06 + ((-1) * x46)) ≥ 0) ∨ (¬ (x46 ≤ x06)) ∨ (¬ (x06 ≤ x04)) ∨ (¬ ((x04 - x46) ≥ 1)) ∨ (¬ ((x04 - x06) ≤ (t - 1))) ∨ (¬ ((x06 - x46) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x04 + ((-1) * x46)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x06 + ((-1) * x46)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x46 ≤ x06) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x06 ≤ x04) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x04 - x46) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x04 - x06) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x06 - x46) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th116 t x04 x06 x46
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause1990 (t x04 x06 x46 : ℝ) : (((x04 + ((-1) * x46)) ≤ (-1)) ∨ ((x04 + ((-1) * x06)) ≥ 0) ∨ (¬ (x46 ≤ x06)) ∨ (¬ (x06 ≤ x04)) ∨ (¬ ((x04 - x46) ≥ 1)) ∨ (¬ ((x04 - x06) ≤ (t - 1))) ∨ (¬ ((x06 - x46) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x04 + ((-1) * x46)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x04 + ((-1) * x06)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x46 ≤ x06) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x06 ≤ x04) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x04 - x46) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x04 - x06) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x06 - x46) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th116 t x04 x06 x46
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause1991 (t x04 x06 x46 : ℝ) : (((x04 + ((-1) * x46)) ≤ (-1)) ∨ ((x04 + ((-1) * x46)) ≥ 1) ∨ (¬ (x46 ≤ x06)) ∨ (¬ (x06 ≤ x04)) ∨ (¬ ((x04 - x46) ≥ 1)) ∨ (¬ ((x04 - x06) ≤ (t - 1))) ∨ (¬ ((x06 - x46) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x04 + ((-1) * x46)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x04 + ((-1) * x46)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x46 ≤ x06) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x06 ≤ x04) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x04 - x46) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x04 - x06) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x06 - x46) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th116 t x04 x06 x46
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause1993 (t x04 x06 x46 : ℝ) : (((x04 + ((-1) * x46)) ≤ (-1)) ∨ ((t + ((-1) * x06) + x46) ≥ 1) ∨ (¬ (x46 ≤ x06)) ∨ (¬ (x06 ≤ x04)) ∨ (¬ ((x04 - x46) ≥ 1)) ∨ (¬ ((x04 - x06) ≤ (t - 1))) ∨ (¬ ((x06 - x46) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x04 + ((-1) * x46)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + ((-1) * x06) + x46) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x46 ≤ x06) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x06 ≤ x04) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x04 - x46) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x04 - x06) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x06 - x46) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th116 t x04 x06 x46
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause1999 (t x04 x06 x46 : ℝ) : (((t + x06 + ((-1) * x46)) ≥ 1) ∨ ((x06 + ((-1) * x46)) ≥ 0) ∨ (¬ (x46 ≤ x06)) ∨ (¬ (x06 ≤ x04)) ∨ (¬ ((x04 - x46) ≥ 1)) ∨ (¬ ((x04 - x06) ≤ (t - 1))) ∨ (¬ ((x06 - x46) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((t + x06 + ((-1) * x46)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x06 + ((-1) * x46)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x46 ≤ x06) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x06 ≤ x04) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x04 - x46) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x04 - x06) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x06 - x46) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th116 t x04 x06 x46
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 (hh).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause2054 (t x04 x06 x46 : ℝ) (h : (((x04 ≤ x06) ∧ (x06 ≤ x46) ∧ ((x46 - x04) ≥ 1) ∧ ((x06 - x04) ≤ (t - 1)) ∧ ((x46 - x06) ≤ (t - 1))) ∨ ((x46 ≤ x06) ∧ (x06 ≤ x04) ∧ ((x04 - x46) ≥ 1) ∧ ((x04 - x06) ≤ (t - 1)) ∧ ((x06 - x46) ≤ (t - 1))))) : ((x04 ≤ x06) ∨ (x46 ≤ x06)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x04 ≤ x06) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x46 ≤ x06) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause2055 (t x04 x06 x46 : ℝ) (h : (((x04 ≤ x06) ∧ (x06 ≤ x46) ∧ ((x46 - x04) ≥ 1) ∧ ((x06 - x04) ≤ (t - 1)) ∧ ((x46 - x06) ≤ (t - 1))) ∨ ((x46 ≤ x06) ∧ (x06 ≤ x04) ∧ ((x04 - x46) ≥ 1) ∧ ((x04 - x06) ≤ (t - 1)) ∧ ((x06 - x46) ≤ (t - 1))))) : ((x04 ≤ x06) ∨ (x06 ≤ x04)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x04 ≤ x06) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x06 ≤ x04) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause2056 (t x04 x06 x46 : ℝ) (h : (((x04 ≤ x06) ∧ (x06 ≤ x46) ∧ ((x46 - x04) ≥ 1) ∧ ((x06 - x04) ≤ (t - 1)) ∧ ((x46 - x06) ≤ (t - 1))) ∨ ((x46 ≤ x06) ∧ (x06 ≤ x04) ∧ ((x04 - x46) ≥ 1) ∧ ((x04 - x06) ≤ (t - 1)) ∧ ((x06 - x46) ≤ (t - 1))))) : ((x04 ≤ x06) ∨ ((x04 - x46) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x04 ≤ x06) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x04 - x46) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause2057 (t x04 x06 x46 : ℝ) (h : (((x04 ≤ x06) ∧ (x06 ≤ x46) ∧ ((x46 - x04) ≥ 1) ∧ ((x06 - x04) ≤ (t - 1)) ∧ ((x46 - x06) ≤ (t - 1))) ∨ ((x46 ≤ x06) ∧ (x06 ≤ x04) ∧ ((x04 - x46) ≥ 1) ∧ ((x04 - x06) ≤ (t - 1)) ∧ ((x06 - x46) ≤ (t - 1))))) : ((x04 ≤ x06) ∨ ((x04 - x06) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x04 ≤ x06) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x04 - x06) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause2058 (t x04 x06 x46 : ℝ) (h : (((x04 ≤ x06) ∧ (x06 ≤ x46) ∧ ((x46 - x04) ≥ 1) ∧ ((x06 - x04) ≤ (t - 1)) ∧ ((x46 - x06) ≤ (t - 1))) ∨ ((x46 ≤ x06) ∧ (x06 ≤ x04) ∧ ((x04 - x46) ≥ 1) ∧ ((x04 - x06) ≤ (t - 1)) ∧ ((x06 - x46) ≤ (t - 1))))) : ((x04 ≤ x06) ∨ ((x06 - x46) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x04 ≤ x06) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x06 - x46) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause2059 (t x04 x06 x46 : ℝ) (h : (((x04 ≤ x06) ∧ (x06 ≤ x46) ∧ ((x46 - x04) ≥ 1) ∧ ((x06 - x04) ≤ (t - 1)) ∧ ((x46 - x06) ≤ (t - 1))) ∨ ((x46 ≤ x06) ∧ (x06 ≤ x04) ∧ ((x04 - x46) ≥ 1) ∧ ((x04 - x06) ≤ (t - 1)) ∧ ((x06 - x46) ≤ (t - 1))))) : ((x06 ≤ x46) ∨ (x46 ≤ x06)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x06 ≤ x46) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x46 ≤ x06) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause2060 (t x04 x06 x46 : ℝ) (h : (((x04 ≤ x06) ∧ (x06 ≤ x46) ∧ ((x46 - x04) ≥ 1) ∧ ((x06 - x04) ≤ (t - 1)) ∧ ((x46 - x06) ≤ (t - 1))) ∨ ((x46 ≤ x06) ∧ (x06 ≤ x04) ∧ ((x04 - x46) ≥ 1) ∧ ((x04 - x06) ≤ (t - 1)) ∧ ((x06 - x46) ≤ (t - 1))))) : ((x06 ≤ x46) ∨ (x06 ≤ x04)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x06 ≤ x46) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x06 ≤ x04) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause2061 (t x04 x06 x46 : ℝ) (h : (((x04 ≤ x06) ∧ (x06 ≤ x46) ∧ ((x46 - x04) ≥ 1) ∧ ((x06 - x04) ≤ (t - 1)) ∧ ((x46 - x06) ≤ (t - 1))) ∨ ((x46 ≤ x06) ∧ (x06 ≤ x04) ∧ ((x04 - x46) ≥ 1) ∧ ((x04 - x06) ≤ (t - 1)) ∧ ((x06 - x46) ≤ (t - 1))))) : ((x06 ≤ x46) ∨ ((x04 - x46) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x06 ≤ x46) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x04 - x46) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause2062 (t x04 x06 x46 : ℝ) (h : (((x04 ≤ x06) ∧ (x06 ≤ x46) ∧ ((x46 - x04) ≥ 1) ∧ ((x06 - x04) ≤ (t - 1)) ∧ ((x46 - x06) ≤ (t - 1))) ∨ ((x46 ≤ x06) ∧ (x06 ≤ x04) ∧ ((x04 - x46) ≥ 1) ∧ ((x04 - x06) ≤ (t - 1)) ∧ ((x06 - x46) ≤ (t - 1))))) : ((x06 ≤ x46) ∨ ((x04 - x06) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x06 ≤ x46) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x04 - x06) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause2063 (t x04 x06 x46 : ℝ) (h : (((x04 ≤ x06) ∧ (x06 ≤ x46) ∧ ((x46 - x04) ≥ 1) ∧ ((x06 - x04) ≤ (t - 1)) ∧ ((x46 - x06) ≤ (t - 1))) ∨ ((x46 ≤ x06) ∧ (x06 ≤ x04) ∧ ((x04 - x46) ≥ 1) ∧ ((x04 - x06) ≤ (t - 1)) ∧ ((x06 - x46) ≤ (t - 1))))) : ((x06 ≤ x46) ∨ ((x06 - x46) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x06 ≤ x46) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x06 - x46) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause2064 (t x04 x06 x46 : ℝ) (h : (((x04 ≤ x06) ∧ (x06 ≤ x46) ∧ ((x46 - x04) ≥ 1) ∧ ((x06 - x04) ≤ (t - 1)) ∧ ((x46 - x06) ≤ (t - 1))) ∨ ((x46 ≤ x06) ∧ (x06 ≤ x04) ∧ ((x04 - x46) ≥ 1) ∧ ((x04 - x06) ≤ (t - 1)) ∧ ((x06 - x46) ≤ (t - 1))))) : (((x46 - x04) ≥ 1) ∨ (x46 ≤ x06)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x46 - x04) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x46 ≤ x06) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause2065 (t x04 x06 x46 : ℝ) (h : (((x04 ≤ x06) ∧ (x06 ≤ x46) ∧ ((x46 - x04) ≥ 1) ∧ ((x06 - x04) ≤ (t - 1)) ∧ ((x46 - x06) ≤ (t - 1))) ∨ ((x46 ≤ x06) ∧ (x06 ≤ x04) ∧ ((x04 - x46) ≥ 1) ∧ ((x04 - x06) ≤ (t - 1)) ∧ ((x06 - x46) ≤ (t - 1))))) : (((x46 - x04) ≥ 1) ∨ (x06 ≤ x04)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x46 - x04) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x06 ≤ x04) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause2066 (t x04 x06 x46 : ℝ) (h : (((x04 ≤ x06) ∧ (x06 ≤ x46) ∧ ((x46 - x04) ≥ 1) ∧ ((x06 - x04) ≤ (t - 1)) ∧ ((x46 - x06) ≤ (t - 1))) ∨ ((x46 ≤ x06) ∧ (x06 ≤ x04) ∧ ((x04 - x46) ≥ 1) ∧ ((x04 - x06) ≤ (t - 1)) ∧ ((x06 - x46) ≤ (t - 1))))) : (((x46 - x04) ≥ 1) ∨ ((x04 - x46) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x46 - x04) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x04 - x46) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause2067 (t x04 x06 x46 : ℝ) (h : (((x04 ≤ x06) ∧ (x06 ≤ x46) ∧ ((x46 - x04) ≥ 1) ∧ ((x06 - x04) ≤ (t - 1)) ∧ ((x46 - x06) ≤ (t - 1))) ∨ ((x46 ≤ x06) ∧ (x06 ≤ x04) ∧ ((x04 - x46) ≥ 1) ∧ ((x04 - x06) ≤ (t - 1)) ∧ ((x06 - x46) ≤ (t - 1))))) : (((x46 - x04) ≥ 1) ∨ ((x04 - x06) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x46 - x04) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x04 - x06) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause2068 (t x04 x06 x46 : ℝ) (h : (((x04 ≤ x06) ∧ (x06 ≤ x46) ∧ ((x46 - x04) ≥ 1) ∧ ((x06 - x04) ≤ (t - 1)) ∧ ((x46 - x06) ≤ (t - 1))) ∨ ((x46 ≤ x06) ∧ (x06 ≤ x04) ∧ ((x04 - x46) ≥ 1) ∧ ((x04 - x06) ≤ (t - 1)) ∧ ((x06 - x46) ≤ (t - 1))))) : (((x46 - x04) ≥ 1) ∨ ((x06 - x46) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x46 - x04) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x06 - x46) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause2069 (t x04 x06 x46 : ℝ) (h : (((x04 ≤ x06) ∧ (x06 ≤ x46) ∧ ((x46 - x04) ≥ 1) ∧ ((x06 - x04) ≤ (t - 1)) ∧ ((x46 - x06) ≤ (t - 1))) ∨ ((x46 ≤ x06) ∧ (x06 ≤ x04) ∧ ((x04 - x46) ≥ 1) ∧ ((x04 - x06) ≤ (t - 1)) ∧ ((x06 - x46) ≤ (t - 1))))) : (((x06 - x04) ≤ (t - 1)) ∨ (x46 ≤ x06)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x06 - x04) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x46 ≤ x06) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause2070 (t x04 x06 x46 : ℝ) (h : (((x04 ≤ x06) ∧ (x06 ≤ x46) ∧ ((x46 - x04) ≥ 1) ∧ ((x06 - x04) ≤ (t - 1)) ∧ ((x46 - x06) ≤ (t - 1))) ∨ ((x46 ≤ x06) ∧ (x06 ≤ x04) ∧ ((x04 - x46) ≥ 1) ∧ ((x04 - x06) ≤ (t - 1)) ∧ ((x06 - x46) ≤ (t - 1))))) : (((x06 - x04) ≤ (t - 1)) ∨ (x06 ≤ x04)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x06 - x04) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x06 ≤ x04) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause2071 (t x04 x06 x46 : ℝ) (h : (((x04 ≤ x06) ∧ (x06 ≤ x46) ∧ ((x46 - x04) ≥ 1) ∧ ((x06 - x04) ≤ (t - 1)) ∧ ((x46 - x06) ≤ (t - 1))) ∨ ((x46 ≤ x06) ∧ (x06 ≤ x04) ∧ ((x04 - x46) ≥ 1) ∧ ((x04 - x06) ≤ (t - 1)) ∧ ((x06 - x46) ≤ (t - 1))))) : (((x06 - x04) ≤ (t - 1)) ∨ ((x04 - x46) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x06 - x04) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x04 - x46) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause2072 (t x04 x06 x46 : ℝ) (h : (((x04 ≤ x06) ∧ (x06 ≤ x46) ∧ ((x46 - x04) ≥ 1) ∧ ((x06 - x04) ≤ (t - 1)) ∧ ((x46 - x06) ≤ (t - 1))) ∨ ((x46 ≤ x06) ∧ (x06 ≤ x04) ∧ ((x04 - x46) ≥ 1) ∧ ((x04 - x06) ≤ (t - 1)) ∧ ((x06 - x46) ≤ (t - 1))))) : (((x06 - x04) ≤ (t - 1)) ∨ ((x04 - x06) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x06 - x04) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x04 - x06) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause2073 (t x04 x06 x46 : ℝ) (h : (((x04 ≤ x06) ∧ (x06 ≤ x46) ∧ ((x46 - x04) ≥ 1) ∧ ((x06 - x04) ≤ (t - 1)) ∧ ((x46 - x06) ≤ (t - 1))) ∨ ((x46 ≤ x06) ∧ (x06 ≤ x04) ∧ ((x04 - x46) ≥ 1) ∧ ((x04 - x06) ≤ (t - 1)) ∧ ((x06 - x46) ≤ (t - 1))))) : (((x06 - x04) ≤ (t - 1)) ∨ ((x06 - x46) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x06 - x04) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x06 - x46) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause2074 (t x04 x06 x46 : ℝ) (h : (((x04 ≤ x06) ∧ (x06 ≤ x46) ∧ ((x46 - x04) ≥ 1) ∧ ((x06 - x04) ≤ (t - 1)) ∧ ((x46 - x06) ≤ (t - 1))) ∨ ((x46 ≤ x06) ∧ (x06 ≤ x04) ∧ ((x04 - x46) ≥ 1) ∧ ((x04 - x06) ≤ (t - 1)) ∧ ((x06 - x46) ≤ (t - 1))))) : (((x46 - x06) ≤ (t - 1)) ∨ (x46 ≤ x06)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x46 - x06) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x46 ≤ x06) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause2075 (t x04 x06 x46 : ℝ) (h : (((x04 ≤ x06) ∧ (x06 ≤ x46) ∧ ((x46 - x04) ≥ 1) ∧ ((x06 - x04) ≤ (t - 1)) ∧ ((x46 - x06) ≤ (t - 1))) ∨ ((x46 ≤ x06) ∧ (x06 ≤ x04) ∧ ((x04 - x46) ≥ 1) ∧ ((x04 - x06) ≤ (t - 1)) ∧ ((x06 - x46) ≤ (t - 1))))) : (((x46 - x06) ≤ (t - 1)) ∨ (x06 ≤ x04)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x46 - x06) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x06 ≤ x04) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause2076 (t x04 x06 x46 : ℝ) (h : (((x04 ≤ x06) ∧ (x06 ≤ x46) ∧ ((x46 - x04) ≥ 1) ∧ ((x06 - x04) ≤ (t - 1)) ∧ ((x46 - x06) ≤ (t - 1))) ∨ ((x46 ≤ x06) ∧ (x06 ≤ x04) ∧ ((x04 - x46) ≥ 1) ∧ ((x04 - x06) ≤ (t - 1)) ∧ ((x06 - x46) ≤ (t - 1))))) : (((x46 - x06) ≤ (t - 1)) ∨ ((x04 - x46) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x46 - x06) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x04 - x46) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause2077 (t x04 x06 x46 : ℝ) (h : (((x04 ≤ x06) ∧ (x06 ≤ x46) ∧ ((x46 - x04) ≥ 1) ∧ ((x06 - x04) ≤ (t - 1)) ∧ ((x46 - x06) ≤ (t - 1))) ∨ ((x46 ≤ x06) ∧ (x06 ≤ x04) ∧ ((x04 - x46) ≥ 1) ∧ ((x04 - x06) ≤ (t - 1)) ∧ ((x06 - x46) ≤ (t - 1))))) : (((x46 - x06) ≤ (t - 1)) ∨ ((x04 - x06) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x46 - x06) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x04 - x06) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause2078 (t x04 x06 x46 : ℝ) (h : (((x04 ≤ x06) ∧ (x06 ≤ x46) ∧ ((x46 - x04) ≥ 1) ∧ ((x06 - x04) ≤ (t - 1)) ∧ ((x46 - x06) ≤ (t - 1))) ∨ ((x46 ≤ x06) ∧ (x06 ≤ x04) ∧ ((x04 - x46) ≥ 1) ∧ ((x04 - x06) ≤ (t - 1)) ∧ ((x06 - x46) ≤ (t - 1))))) : (((x46 - x06) ≤ (t - 1)) ∨ ((x06 - x46) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x46 - x06) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x06 - x46) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause2079 (x04 x46 x47 : ℝ) : ((¬ ((x04 + ((-1) * x46)) ≤ (-1))) ∨ (¬ ((x04 + ((-1) * x47)) ≥ 1)) ∨ (¬ ((x46 + ((-1) * x47)) ≤ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x04 + ((-1) * x46)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x04 + ((-1) * x47)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x46 + ((-1) * x47)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th118 x04 x46 x47
  exact (fun hh => (fun hh => hh u2) (hh (And.intro u0 u1))) h

theorem clause2080 (x04 x06 x47 x67 : ℝ) : ((¬ ((x04 + ((-1) * x47)) ≥ 1)) ∨ (¬ ((x04 + ((-1) * x06)) ≤ 0)) ∨ (¬ ((x06 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((x47 + ((-1) * x67)) ≥ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x04 + ((-1) * x47)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x04 + ((-1) * x06)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x06 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x47 + ((-1) * x67)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr hh)))
  have h := NineTheoryTrial.th119 x04 x06 x47 x67
  exact (fun hh => (fun hh => hh u3) (hh (And.intro u0 (And.intro u2 u1)))) h

theorem clause2083 (t x46 x47 x67 : ℝ) : (((x46 + ((-1) * x47)) ≤ 0) ∨ ((x46 + ((-1) * x67)) ≥ 1) ∨ (¬ (x46 ≤ x47)) ∨ (¬ (x47 ≤ x67)) ∨ (¬ ((x67 - x46) ≥ 1)) ∨ (¬ ((x47 - x46) ≤ (t - 1))) ∨ (¬ ((x67 - x47) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x46 + ((-1) * x47)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x46 + ((-1) * x67)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x46 ≤ x47) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x47 ≤ x67) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x67 - x46) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x47 - x46) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x67 - x47) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th121 t x46 x47 x67
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause2087 (t x46 x47 x67 : ℝ) : (((x47 + ((-1) * x67)) ≤ 0) ∨ ((x46 + ((-1) * x47)) ≥ 0) ∨ (¬ (x46 ≤ x47)) ∨ (¬ (x47 ≤ x67)) ∨ (¬ ((x67 - x46) ≥ 1)) ∨ (¬ ((x47 - x46) ≤ (t - 1))) ∨ (¬ ((x67 - x47) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x47 + ((-1) * x67)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x46 + ((-1) * x47)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x46 ≤ x47) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x47 ≤ x67) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x67 - x46) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x47 - x46) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x67 - x47) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th121 t x46 x47 x67
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause2088 (t x46 x47 x67 : ℝ) : (((x47 + ((-1) * x67)) ≤ 0) ∨ ((x46 + ((-1) * x67)) ≥ 1) ∨ (¬ (x46 ≤ x47)) ∨ (¬ (x47 ≤ x67)) ∨ (¬ ((x67 - x46) ≥ 1)) ∨ (¬ ((x47 - x46) ≤ (t - 1))) ∨ (¬ ((x67 - x47) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x47 + ((-1) * x67)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x46 + ((-1) * x67)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x46 ≤ x47) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x47 ≤ x67) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x67 - x46) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x47 - x46) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x67 - x47) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th121 t x46 x47 x67
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause2091 (t x46 x47 x67 : ℝ) : (((x46 + ((-1) * x67)) ≤ (-1)) ∨ ((x47 + ((-1) * x67)) ≥ 0) ∨ (¬ (x46 ≤ x47)) ∨ (¬ (x47 ≤ x67)) ∨ (¬ ((x67 - x46) ≥ 1)) ∨ (¬ ((x47 - x46) ≤ (t - 1))) ∨ (¬ ((x67 - x47) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x46 + ((-1) * x67)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x47 + ((-1) * x67)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x46 ≤ x47) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x47 ≤ x67) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x67 - x46) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x47 - x46) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x67 - x47) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th121 t x46 x47 x67
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause2092 (t x46 x47 x67 : ℝ) : (((x46 + ((-1) * x67)) ≤ (-1)) ∨ ((x46 + ((-1) * x47)) ≥ 0) ∨ (¬ (x46 ≤ x47)) ∨ (¬ (x47 ≤ x67)) ∨ (¬ ((x67 - x46) ≥ 1)) ∨ (¬ ((x47 - x46) ≤ (t - 1))) ∨ (¬ ((x67 - x47) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x46 + ((-1) * x67)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x46 + ((-1) * x47)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x46 ≤ x47) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x47 ≤ x67) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x67 - x46) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x47 - x46) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x67 - x47) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th121 t x46 x47 x67
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause2093 (t x46 x47 x67 : ℝ) : (((x46 + ((-1) * x67)) ≤ (-1)) ∨ ((x46 + ((-1) * x67)) ≥ 1) ∨ (¬ (x46 ≤ x47)) ∨ (¬ (x47 ≤ x67)) ∨ (¬ ((x67 - x46) ≥ 1)) ∨ (¬ ((x47 - x46) ≤ (t - 1))) ∨ (¬ ((x67 - x47) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x46 + ((-1) * x67)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x46 + ((-1) * x67)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x46 ≤ x47) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x47 ≤ x67) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x67 - x46) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x47 - x46) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x67 - x47) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th121 t x46 x47 x67
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause2095 (t x46 x47 x67 : ℝ) : (((x46 + ((-1) * x67)) ≤ (-1)) ∨ ((t + ((-1) * x47) + x67) ≥ 1) ∨ (¬ (x46 ≤ x47)) ∨ (¬ (x47 ≤ x67)) ∨ (¬ ((x67 - x46) ≥ 1)) ∨ (¬ ((x47 - x46) ≤ (t - 1))) ∨ (¬ ((x67 - x47) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x46 + ((-1) * x67)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + ((-1) * x47) + x67) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x46 ≤ x47) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x47 ≤ x67) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x67 - x46) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x47 - x46) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x67 - x47) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th121 t x46 x47 x67
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause2101 (t x46 x47 x67 : ℝ) : (((t + x47 + ((-1) * x67)) ≥ 1) ∨ ((x47 + ((-1) * x67)) ≥ 0) ∨ (¬ (x46 ≤ x47)) ∨ (¬ (x47 ≤ x67)) ∨ (¬ ((x67 - x46) ≥ 1)) ∨ (¬ ((x47 - x46) ≤ (t - 1))) ∨ (¬ ((x67 - x47) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((t + x47 + ((-1) * x67)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x47 + ((-1) * x67)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x46 ≤ x47) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x47 ≤ x67) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x67 - x46) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x47 - x46) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x67 - x47) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th121 t x46 x47 x67
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 (hh).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause2103 (t x46 x47 x67 : ℝ) : (((t + x47 + ((-1) * x67)) ≥ 1) ∨ ((x46 + ((-1) * x67)) ≥ 1) ∨ (¬ (x46 ≤ x47)) ∨ (¬ (x47 ≤ x67)) ∨ (¬ ((x67 - x46) ≥ 1)) ∨ (¬ ((x47 - x46) ≤ (t - 1))) ∨ (¬ ((x67 - x47) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((t + x47 + ((-1) * x67)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x46 + ((-1) * x67)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x46 ≤ x47) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x47 ≤ x67) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x67 - x46) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x47 - x46) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x67 - x47) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th121 t x46 x47 x67
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause2106 (t x46 x47 x67 : ℝ) : (((x46 + ((-1) * x47)) ≤ 0) ∨ ((x47 + ((-1) * x67)) ≥ 0) ∨ (¬ (x67 ≤ x47)) ∨ (¬ (x47 ≤ x46)) ∨ (¬ ((x46 - x67) ≥ 1)) ∨ (¬ ((x46 - x47) ≤ (t - 1))) ∨ (¬ ((x47 - x67) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x46 + ((-1) * x47)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x47 + ((-1) * x67)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x67 ≤ x47) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x47 ≤ x46) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x46 - x67) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x46 - x47) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x47 - x67) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th121 t x46 x47 x67
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause2108 (t x46 x47 x67 : ℝ) : (((x46 + ((-1) * x47)) ≤ 0) ∨ ((x46 + ((-1) * x67)) ≥ 1) ∨ (¬ (x67 ≤ x47)) ∨ (¬ (x47 ≤ x46)) ∨ (¬ ((x46 - x67) ≥ 1)) ∨ (¬ ((x46 - x47) ≤ (t - 1))) ∨ (¬ ((x47 - x67) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x46 + ((-1) * x47)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x46 + ((-1) * x67)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x67 ≤ x47) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x47 ≤ x46) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x46 - x67) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x46 - x47) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x47 - x67) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th121 t x46 x47 x67
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause2112 (t x46 x47 x67 : ℝ) : (((x47 + ((-1) * x67)) ≤ 0) ∨ ((x46 + ((-1) * x47)) ≥ 0) ∨ (¬ (x67 ≤ x47)) ∨ (¬ (x47 ≤ x46)) ∨ (¬ ((x46 - x67) ≥ 1)) ∨ (¬ ((x46 - x47) ≤ (t - 1))) ∨ (¬ ((x47 - x67) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x47 + ((-1) * x67)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x46 + ((-1) * x47)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x67 ≤ x47) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x47 ≤ x46) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x46 - x67) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x46 - x47) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x47 - x67) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th121 t x46 x47 x67
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause2113 (t x46 x47 x67 : ℝ) : (((x47 + ((-1) * x67)) ≤ 0) ∨ ((x46 + ((-1) * x67)) ≥ 1) ∨ (¬ (x67 ≤ x47)) ∨ (¬ (x47 ≤ x46)) ∨ (¬ ((x46 - x67) ≥ 1)) ∨ (¬ ((x46 - x47) ≤ (t - 1))) ∨ (¬ ((x47 - x67) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x47 + ((-1) * x67)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x46 + ((-1) * x67)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x67 ≤ x47) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x47 ≤ x46) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x46 - x67) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x46 - x47) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x47 - x67) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th121 t x46 x47 x67
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause2115 (t x46 x47 x67 : ℝ) : (((x47 + ((-1) * x67)) ≤ 0) ∨ ((t + ((-1) * x47) + x67) ≥ 1) ∨ (¬ (x67 ≤ x47)) ∨ (¬ (x47 ≤ x46)) ∨ (¬ ((x46 - x67) ≥ 1)) ∨ (¬ ((x46 - x47) ≤ (t - 1))) ∨ (¬ ((x47 - x67) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x47 + ((-1) * x67)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + ((-1) * x47) + x67) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x67 ≤ x47) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x47 ≤ x46) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x46 - x67) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x46 - x47) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x47 - x67) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th121 t x46 x47 x67
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause2116 (t x46 x47 x67 : ℝ) : (((x46 + ((-1) * x67)) ≤ (-1)) ∨ ((x47 + ((-1) * x67)) ≥ 0) ∨ (¬ (x67 ≤ x47)) ∨ (¬ (x47 ≤ x46)) ∨ (¬ ((x46 - x67) ≥ 1)) ∨ (¬ ((x46 - x47) ≤ (t - 1))) ∨ (¬ ((x47 - x67) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x46 + ((-1) * x67)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x47 + ((-1) * x67)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x67 ≤ x47) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x47 ≤ x46) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x46 - x67) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x46 - x47) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x47 - x67) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th121 t x46 x47 x67
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause2117 (t x46 x47 x67 : ℝ) : (((x46 + ((-1) * x67)) ≤ (-1)) ∨ ((x46 + ((-1) * x47)) ≥ 0) ∨ (¬ (x67 ≤ x47)) ∨ (¬ (x47 ≤ x46)) ∨ (¬ ((x46 - x67) ≥ 1)) ∨ (¬ ((x46 - x47) ≤ (t - 1))) ∨ (¬ ((x47 - x67) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x46 + ((-1) * x67)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x46 + ((-1) * x47)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x67 ≤ x47) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x47 ≤ x46) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x46 - x67) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x46 - x47) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x47 - x67) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th121 t x46 x47 x67
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause2118 (t x46 x47 x67 : ℝ) : (((x46 + ((-1) * x67)) ≤ (-1)) ∨ ((x46 + ((-1) * x67)) ≥ 1) ∨ (¬ (x67 ≤ x47)) ∨ (¬ (x47 ≤ x46)) ∨ (¬ ((x46 - x67) ≥ 1)) ∨ (¬ ((x46 - x47) ≤ (t - 1))) ∨ (¬ ((x47 - x67) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x46 + ((-1) * x67)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x46 + ((-1) * x67)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x67 ≤ x47) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x47 ≤ x46) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x46 - x67) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x46 - x47) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x47 - x67) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th121 t x46 x47 x67
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause2120 (t x46 x47 x67 : ℝ) : (((x46 + ((-1) * x67)) ≤ (-1)) ∨ ((t + ((-1) * x47) + x67) ≥ 1) ∨ (¬ (x67 ≤ x47)) ∨ (¬ (x47 ≤ x46)) ∨ (¬ ((x46 - x67) ≥ 1)) ∨ (¬ ((x46 - x47) ≤ (t - 1))) ∨ (¬ ((x47 - x67) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x46 + ((-1) * x67)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + ((-1) * x47) + x67) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x67 ≤ x47) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x47 ≤ x46) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x46 - x67) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x46 - x47) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x47 - x67) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th121 t x46 x47 x67
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause2126 (t x46 x47 x67 : ℝ) : (((t + x47 + ((-1) * x67)) ≥ 1) ∨ ((x47 + ((-1) * x67)) ≥ 0) ∨ (¬ (x67 ≤ x47)) ∨ (¬ (x47 ≤ x46)) ∨ (¬ ((x46 - x67) ≥ 1)) ∨ (¬ ((x46 - x47) ≤ (t - 1))) ∨ (¬ ((x47 - x67) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((t + x47 + ((-1) * x67)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x47 + ((-1) * x67)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x67 ≤ x47) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x47 ≤ x46) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x46 - x67) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x46 - x47) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x47 - x67) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th121 t x46 x47 x67
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 (hh).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause2128 (t x46 x47 x67 : ℝ) : (((t + x47 + ((-1) * x67)) ≥ 1) ∨ ((x46 + ((-1) * x67)) ≥ 1) ∨ (¬ (x67 ≤ x47)) ∨ (¬ (x47 ≤ x46)) ∨ (¬ ((x46 - x67) ≥ 1)) ∨ (¬ ((x46 - x47) ≤ (t - 1))) ∨ (¬ ((x47 - x67) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((t + x47 + ((-1) * x67)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x46 + ((-1) * x67)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x67 ≤ x47) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x47 ≤ x46) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x46 - x67) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x46 - x47) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x47 - x67) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th121 t x46 x47 x67
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause2181 (t x46 x47 x67 : ℝ) (h : (((x46 ≤ x47) ∧ (x47 ≤ x67) ∧ ((x67 - x46) ≥ 1) ∧ ((x47 - x46) ≤ (t - 1)) ∧ ((x67 - x47) ≤ (t - 1))) ∨ ((x67 ≤ x47) ∧ (x47 ≤ x46) ∧ ((x46 - x67) ≥ 1) ∧ ((x46 - x47) ≤ (t - 1)) ∧ ((x47 - x67) ≤ (t - 1))))) : ((x46 ≤ x47) ∨ (x67 ≤ x47)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x46 ≤ x47) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x67 ≤ x47) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause2182 (t x46 x47 x67 : ℝ) (h : (((x46 ≤ x47) ∧ (x47 ≤ x67) ∧ ((x67 - x46) ≥ 1) ∧ ((x47 - x46) ≤ (t - 1)) ∧ ((x67 - x47) ≤ (t - 1))) ∨ ((x67 ≤ x47) ∧ (x47 ≤ x46) ∧ ((x46 - x67) ≥ 1) ∧ ((x46 - x47) ≤ (t - 1)) ∧ ((x47 - x67) ≤ (t - 1))))) : ((x46 ≤ x47) ∨ (x47 ≤ x46)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x46 ≤ x47) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x47 ≤ x46) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause2183 (t x46 x47 x67 : ℝ) (h : (((x46 ≤ x47) ∧ (x47 ≤ x67) ∧ ((x67 - x46) ≥ 1) ∧ ((x47 - x46) ≤ (t - 1)) ∧ ((x67 - x47) ≤ (t - 1))) ∨ ((x67 ≤ x47) ∧ (x47 ≤ x46) ∧ ((x46 - x67) ≥ 1) ∧ ((x46 - x47) ≤ (t - 1)) ∧ ((x47 - x67) ≤ (t - 1))))) : ((x46 ≤ x47) ∨ ((x46 - x67) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x46 ≤ x47) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x46 - x67) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause2184 (t x46 x47 x67 : ℝ) (h : (((x46 ≤ x47) ∧ (x47 ≤ x67) ∧ ((x67 - x46) ≥ 1) ∧ ((x47 - x46) ≤ (t - 1)) ∧ ((x67 - x47) ≤ (t - 1))) ∨ ((x67 ≤ x47) ∧ (x47 ≤ x46) ∧ ((x46 - x67) ≥ 1) ∧ ((x46 - x47) ≤ (t - 1)) ∧ ((x47 - x67) ≤ (t - 1))))) : ((x46 ≤ x47) ∨ ((x46 - x47) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x46 ≤ x47) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x46 - x47) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause2185 (t x46 x47 x67 : ℝ) (h : (((x46 ≤ x47) ∧ (x47 ≤ x67) ∧ ((x67 - x46) ≥ 1) ∧ ((x47 - x46) ≤ (t - 1)) ∧ ((x67 - x47) ≤ (t - 1))) ∨ ((x67 ≤ x47) ∧ (x47 ≤ x46) ∧ ((x46 - x67) ≥ 1) ∧ ((x46 - x47) ≤ (t - 1)) ∧ ((x47 - x67) ≤ (t - 1))))) : ((x46 ≤ x47) ∨ ((x47 - x67) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x46 ≤ x47) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x47 - x67) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause2186 (t x46 x47 x67 : ℝ) (h : (((x46 ≤ x47) ∧ (x47 ≤ x67) ∧ ((x67 - x46) ≥ 1) ∧ ((x47 - x46) ≤ (t - 1)) ∧ ((x67 - x47) ≤ (t - 1))) ∨ ((x67 ≤ x47) ∧ (x47 ≤ x46) ∧ ((x46 - x67) ≥ 1) ∧ ((x46 - x47) ≤ (t - 1)) ∧ ((x47 - x67) ≤ (t - 1))))) : ((x47 ≤ x67) ∨ (x67 ≤ x47)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x47 ≤ x67) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x67 ≤ x47) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause2187 (t x46 x47 x67 : ℝ) (h : (((x46 ≤ x47) ∧ (x47 ≤ x67) ∧ ((x67 - x46) ≥ 1) ∧ ((x47 - x46) ≤ (t - 1)) ∧ ((x67 - x47) ≤ (t - 1))) ∨ ((x67 ≤ x47) ∧ (x47 ≤ x46) ∧ ((x46 - x67) ≥ 1) ∧ ((x46 - x47) ≤ (t - 1)) ∧ ((x47 - x67) ≤ (t - 1))))) : ((x47 ≤ x67) ∨ (x47 ≤ x46)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x47 ≤ x67) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x47 ≤ x46) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause2188 (t x46 x47 x67 : ℝ) (h : (((x46 ≤ x47) ∧ (x47 ≤ x67) ∧ ((x67 - x46) ≥ 1) ∧ ((x47 - x46) ≤ (t - 1)) ∧ ((x67 - x47) ≤ (t - 1))) ∨ ((x67 ≤ x47) ∧ (x47 ≤ x46) ∧ ((x46 - x67) ≥ 1) ∧ ((x46 - x47) ≤ (t - 1)) ∧ ((x47 - x67) ≤ (t - 1))))) : ((x47 ≤ x67) ∨ ((x46 - x67) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x47 ≤ x67) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x46 - x67) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause2189 (t x46 x47 x67 : ℝ) (h : (((x46 ≤ x47) ∧ (x47 ≤ x67) ∧ ((x67 - x46) ≥ 1) ∧ ((x47 - x46) ≤ (t - 1)) ∧ ((x67 - x47) ≤ (t - 1))) ∨ ((x67 ≤ x47) ∧ (x47 ≤ x46) ∧ ((x46 - x67) ≥ 1) ∧ ((x46 - x47) ≤ (t - 1)) ∧ ((x47 - x67) ≤ (t - 1))))) : ((x47 ≤ x67) ∨ ((x46 - x47) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x47 ≤ x67) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x46 - x47) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause2190 (t x46 x47 x67 : ℝ) (h : (((x46 ≤ x47) ∧ (x47 ≤ x67) ∧ ((x67 - x46) ≥ 1) ∧ ((x47 - x46) ≤ (t - 1)) ∧ ((x67 - x47) ≤ (t - 1))) ∨ ((x67 ≤ x47) ∧ (x47 ≤ x46) ∧ ((x46 - x67) ≥ 1) ∧ ((x46 - x47) ≤ (t - 1)) ∧ ((x47 - x67) ≤ (t - 1))))) : ((x47 ≤ x67) ∨ ((x47 - x67) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x47 ≤ x67) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x47 - x67) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause2191 (t x46 x47 x67 : ℝ) (h : (((x46 ≤ x47) ∧ (x47 ≤ x67) ∧ ((x67 - x46) ≥ 1) ∧ ((x47 - x46) ≤ (t - 1)) ∧ ((x67 - x47) ≤ (t - 1))) ∨ ((x67 ≤ x47) ∧ (x47 ≤ x46) ∧ ((x46 - x67) ≥ 1) ∧ ((x46 - x47) ≤ (t - 1)) ∧ ((x47 - x67) ≤ (t - 1))))) : (((x67 - x46) ≥ 1) ∨ (x67 ≤ x47)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x67 - x46) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x67 ≤ x47) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause2192 (t x46 x47 x67 : ℝ) (h : (((x46 ≤ x47) ∧ (x47 ≤ x67) ∧ ((x67 - x46) ≥ 1) ∧ ((x47 - x46) ≤ (t - 1)) ∧ ((x67 - x47) ≤ (t - 1))) ∨ ((x67 ≤ x47) ∧ (x47 ≤ x46) ∧ ((x46 - x67) ≥ 1) ∧ ((x46 - x47) ≤ (t - 1)) ∧ ((x47 - x67) ≤ (t - 1))))) : (((x67 - x46) ≥ 1) ∨ (x47 ≤ x46)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x67 - x46) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x47 ≤ x46) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause2193 (t x46 x47 x67 : ℝ) (h : (((x46 ≤ x47) ∧ (x47 ≤ x67) ∧ ((x67 - x46) ≥ 1) ∧ ((x47 - x46) ≤ (t - 1)) ∧ ((x67 - x47) ≤ (t - 1))) ∨ ((x67 ≤ x47) ∧ (x47 ≤ x46) ∧ ((x46 - x67) ≥ 1) ∧ ((x46 - x47) ≤ (t - 1)) ∧ ((x47 - x67) ≤ (t - 1))))) : (((x67 - x46) ≥ 1) ∨ ((x46 - x67) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x67 - x46) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x46 - x67) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause2194 (t x46 x47 x67 : ℝ) (h : (((x46 ≤ x47) ∧ (x47 ≤ x67) ∧ ((x67 - x46) ≥ 1) ∧ ((x47 - x46) ≤ (t - 1)) ∧ ((x67 - x47) ≤ (t - 1))) ∨ ((x67 ≤ x47) ∧ (x47 ≤ x46) ∧ ((x46 - x67) ≥ 1) ∧ ((x46 - x47) ≤ (t - 1)) ∧ ((x47 - x67) ≤ (t - 1))))) : (((x67 - x46) ≥ 1) ∨ ((x46 - x47) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x67 - x46) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x46 - x47) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause2195 (t x46 x47 x67 : ℝ) (h : (((x46 ≤ x47) ∧ (x47 ≤ x67) ∧ ((x67 - x46) ≥ 1) ∧ ((x47 - x46) ≤ (t - 1)) ∧ ((x67 - x47) ≤ (t - 1))) ∨ ((x67 ≤ x47) ∧ (x47 ≤ x46) ∧ ((x46 - x67) ≥ 1) ∧ ((x46 - x47) ≤ (t - 1)) ∧ ((x47 - x67) ≤ (t - 1))))) : (((x67 - x46) ≥ 1) ∨ ((x47 - x67) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x67 - x46) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x47 - x67) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause2196 (t x46 x47 x67 : ℝ) (h : (((x46 ≤ x47) ∧ (x47 ≤ x67) ∧ ((x67 - x46) ≥ 1) ∧ ((x47 - x46) ≤ (t - 1)) ∧ ((x67 - x47) ≤ (t - 1))) ∨ ((x67 ≤ x47) ∧ (x47 ≤ x46) ∧ ((x46 - x67) ≥ 1) ∧ ((x46 - x47) ≤ (t - 1)) ∧ ((x47 - x67) ≤ (t - 1))))) : (((x47 - x46) ≤ (t - 1)) ∨ (x67 ≤ x47)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x47 - x46) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x67 ≤ x47) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause2197 (t x46 x47 x67 : ℝ) (h : (((x46 ≤ x47) ∧ (x47 ≤ x67) ∧ ((x67 - x46) ≥ 1) ∧ ((x47 - x46) ≤ (t - 1)) ∧ ((x67 - x47) ≤ (t - 1))) ∨ ((x67 ≤ x47) ∧ (x47 ≤ x46) ∧ ((x46 - x67) ≥ 1) ∧ ((x46 - x47) ≤ (t - 1)) ∧ ((x47 - x67) ≤ (t - 1))))) : (((x47 - x46) ≤ (t - 1)) ∨ (x47 ≤ x46)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x47 - x46) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x47 ≤ x46) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause2198 (t x46 x47 x67 : ℝ) (h : (((x46 ≤ x47) ∧ (x47 ≤ x67) ∧ ((x67 - x46) ≥ 1) ∧ ((x47 - x46) ≤ (t - 1)) ∧ ((x67 - x47) ≤ (t - 1))) ∨ ((x67 ≤ x47) ∧ (x47 ≤ x46) ∧ ((x46 - x67) ≥ 1) ∧ ((x46 - x47) ≤ (t - 1)) ∧ ((x47 - x67) ≤ (t - 1))))) : (((x47 - x46) ≤ (t - 1)) ∨ ((x46 - x67) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x47 - x46) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x46 - x67) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause2199 (t x46 x47 x67 : ℝ) (h : (((x46 ≤ x47) ∧ (x47 ≤ x67) ∧ ((x67 - x46) ≥ 1) ∧ ((x47 - x46) ≤ (t - 1)) ∧ ((x67 - x47) ≤ (t - 1))) ∨ ((x67 ≤ x47) ∧ (x47 ≤ x46) ∧ ((x46 - x67) ≥ 1) ∧ ((x46 - x47) ≤ (t - 1)) ∧ ((x47 - x67) ≤ (t - 1))))) : (((x47 - x46) ≤ (t - 1)) ∨ ((x46 - x47) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x47 - x46) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x46 - x47) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause2200 (t x46 x47 x67 : ℝ) (h : (((x46 ≤ x47) ∧ (x47 ≤ x67) ∧ ((x67 - x46) ≥ 1) ∧ ((x47 - x46) ≤ (t - 1)) ∧ ((x67 - x47) ≤ (t - 1))) ∨ ((x67 ≤ x47) ∧ (x47 ≤ x46) ∧ ((x46 - x67) ≥ 1) ∧ ((x46 - x47) ≤ (t - 1)) ∧ ((x47 - x67) ≤ (t - 1))))) : (((x47 - x46) ≤ (t - 1)) ∨ ((x47 - x67) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x47 - x46) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x47 - x67) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause2201 (t x46 x47 x67 : ℝ) (h : (((x46 ≤ x47) ∧ (x47 ≤ x67) ∧ ((x67 - x46) ≥ 1) ∧ ((x47 - x46) ≤ (t - 1)) ∧ ((x67 - x47) ≤ (t - 1))) ∨ ((x67 ≤ x47) ∧ (x47 ≤ x46) ∧ ((x46 - x67) ≥ 1) ∧ ((x46 - x47) ≤ (t - 1)) ∧ ((x47 - x67) ≤ (t - 1))))) : (((x67 - x47) ≤ (t - 1)) ∨ (x67 ≤ x47)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x67 - x47) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x67 ≤ x47) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause2202 (t x46 x47 x67 : ℝ) (h : (((x46 ≤ x47) ∧ (x47 ≤ x67) ∧ ((x67 - x46) ≥ 1) ∧ ((x47 - x46) ≤ (t - 1)) ∧ ((x67 - x47) ≤ (t - 1))) ∨ ((x67 ≤ x47) ∧ (x47 ≤ x46) ∧ ((x46 - x67) ≥ 1) ∧ ((x46 - x47) ≤ (t - 1)) ∧ ((x47 - x67) ≤ (t - 1))))) : (((x67 - x47) ≤ (t - 1)) ∨ (x47 ≤ x46)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x67 - x47) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x47 ≤ x46) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause2203 (t x46 x47 x67 : ℝ) (h : (((x46 ≤ x47) ∧ (x47 ≤ x67) ∧ ((x67 - x46) ≥ 1) ∧ ((x47 - x46) ≤ (t - 1)) ∧ ((x67 - x47) ≤ (t - 1))) ∨ ((x67 ≤ x47) ∧ (x47 ≤ x46) ∧ ((x46 - x67) ≥ 1) ∧ ((x46 - x47) ≤ (t - 1)) ∧ ((x47 - x67) ≤ (t - 1))))) : (((x67 - x47) ≤ (t - 1)) ∨ ((x46 - x67) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x67 - x47) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x46 - x67) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause2204 (t x46 x47 x67 : ℝ) (h : (((x46 ≤ x47) ∧ (x47 ≤ x67) ∧ ((x67 - x46) ≥ 1) ∧ ((x47 - x46) ≤ (t - 1)) ∧ ((x67 - x47) ≤ (t - 1))) ∨ ((x67 ≤ x47) ∧ (x47 ≤ x46) ∧ ((x46 - x67) ≥ 1) ∧ ((x46 - x47) ≤ (t - 1)) ∧ ((x47 - x67) ≤ (t - 1))))) : (((x67 - x47) ≤ (t - 1)) ∨ ((x46 - x47) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x67 - x47) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x46 - x47) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause2205 (t x46 x47 x67 : ℝ) (h : (((x46 ≤ x47) ∧ (x47 ≤ x67) ∧ ((x67 - x46) ≥ 1) ∧ ((x47 - x46) ≤ (t - 1)) ∧ ((x67 - x47) ≤ (t - 1))) ∨ ((x67 ≤ x47) ∧ (x47 ≤ x46) ∧ ((x46 - x67) ≥ 1) ∧ ((x46 - x47) ≤ (t - 1)) ∧ ((x47 - x67) ≤ (t - 1))))) : (((x67 - x47) ≤ (t - 1)) ∨ ((x47 - x67) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x67 - x47) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x47 - x67) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause2206 (t x06 x07 x67 : ℝ) : (((x06 + ((-1) * x07)) ≤ 0) ∨ ((x07 + ((-1) * x67)) ≥ 0) ∨ (¬ (x06 ≤ x07)) ∨ (¬ (x07 ≤ x67)) ∨ (¬ ((x67 - x06) ≥ 1)) ∨ (¬ ((x07 - x06) ≤ (t - 1))) ∨ (¬ ((x67 - x07) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x06 + ((-1) * x07)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x07 + ((-1) * x67)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x06 ≤ x07) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x07 ≤ x67) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x67 - x06) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x07 - x06) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x67 - x07) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th124 t x06 x07 x67
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause2213 (t x06 x07 x67 : ℝ) : (((x07 + ((-1) * x67)) ≤ 0) ∨ ((x06 + ((-1) * x67)) ≥ 1) ∨ (¬ (x06 ≤ x07)) ∨ (¬ (x07 ≤ x67)) ∨ (¬ ((x67 - x06) ≥ 1)) ∨ (¬ ((x07 - x06) ≤ (t - 1))) ∨ (¬ ((x67 - x07) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x07 + ((-1) * x67)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x06 + ((-1) * x67)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x06 ≤ x07) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x07 ≤ x67) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x67 - x06) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x07 - x06) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x67 - x07) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th124 t x06 x07 x67
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause2216 (t x06 x07 x67 : ℝ) : (((x06 + ((-1) * x67)) ≤ (-1)) ∨ ((x07 + ((-1) * x67)) ≥ 0) ∨ (¬ (x06 ≤ x07)) ∨ (¬ (x07 ≤ x67)) ∨ (¬ ((x67 - x06) ≥ 1)) ∨ (¬ ((x07 - x06) ≤ (t - 1))) ∨ (¬ ((x67 - x07) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x06 + ((-1) * x67)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x07 + ((-1) * x67)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x06 ≤ x07) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x07 ≤ x67) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x67 - x06) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x07 - x06) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x67 - x07) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th124 t x06 x07 x67
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause2217 (t x06 x07 x67 : ℝ) : (((x06 + ((-1) * x67)) ≤ (-1)) ∨ ((x06 + ((-1) * x07)) ≥ 0) ∨ (¬ (x06 ≤ x07)) ∨ (¬ (x07 ≤ x67)) ∨ (¬ ((x67 - x06) ≥ 1)) ∨ (¬ ((x07 - x06) ≤ (t - 1))) ∨ (¬ ((x67 - x07) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x06 + ((-1) * x67)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x06 + ((-1) * x07)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x06 ≤ x07) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x07 ≤ x67) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x67 - x06) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x07 - x06) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x67 - x07) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th124 t x06 x07 x67
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause2218 (t x06 x07 x67 : ℝ) : (((x06 + ((-1) * x67)) ≤ (-1)) ∨ ((x06 + ((-1) * x67)) ≥ 1) ∨ (¬ (x06 ≤ x07)) ∨ (¬ (x07 ≤ x67)) ∨ (¬ ((x67 - x06) ≥ 1)) ∨ (¬ ((x07 - x06) ≤ (t - 1))) ∨ (¬ ((x67 - x07) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x06 + ((-1) * x67)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x06 + ((-1) * x67)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x06 ≤ x07) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x07 ≤ x67) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x67 - x06) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x07 - x06) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x67 - x07) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th124 t x06 x07 x67
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause2231 (t x06 x07 x67 : ℝ) : (((x06 + ((-1) * x07)) ≤ 0) ∨ ((x07 + ((-1) * x67)) ≥ 0) ∨ (¬ (x67 ≤ x07)) ∨ (¬ (x07 ≤ x06)) ∨ (¬ ((x06 - x67) ≥ 1)) ∨ (¬ ((x06 - x07) ≤ (t - 1))) ∨ (¬ ((x07 - x67) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x06 + ((-1) * x07)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x07 + ((-1) * x67)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x67 ≤ x07) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x07 ≤ x06) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x06 - x67) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x06 - x07) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x07 - x67) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th124 t x06 x07 x67
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause2238 (t x06 x07 x67 : ℝ) : (((x07 + ((-1) * x67)) ≤ 0) ∨ ((x06 + ((-1) * x67)) ≥ 1) ∨ (¬ (x67 ≤ x07)) ∨ (¬ (x07 ≤ x06)) ∨ (¬ ((x06 - x67) ≥ 1)) ∨ (¬ ((x06 - x07) ≤ (t - 1))) ∨ (¬ ((x07 - x67) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x07 + ((-1) * x67)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x06 + ((-1) * x67)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x67 ≤ x07) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x07 ≤ x06) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x06 - x67) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x06 - x07) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x07 - x67) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th124 t x06 x07 x67
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause2241 (t x06 x07 x67 : ℝ) : (((x06 + ((-1) * x67)) ≤ (-1)) ∨ ((x07 + ((-1) * x67)) ≥ 0) ∨ (¬ (x67 ≤ x07)) ∨ (¬ (x07 ≤ x06)) ∨ (¬ ((x06 - x67) ≥ 1)) ∨ (¬ ((x06 - x07) ≤ (t - 1))) ∨ (¬ ((x07 - x67) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x06 + ((-1) * x67)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x07 + ((-1) * x67)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x67 ≤ x07) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x07 ≤ x06) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x06 - x67) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x06 - x07) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x07 - x67) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th124 t x06 x07 x67
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause2242 (t x06 x07 x67 : ℝ) : (((x06 + ((-1) * x67)) ≤ (-1)) ∨ ((x06 + ((-1) * x07)) ≥ 0) ∨ (¬ (x67 ≤ x07)) ∨ (¬ (x07 ≤ x06)) ∨ (¬ ((x06 - x67) ≥ 1)) ∨ (¬ ((x06 - x07) ≤ (t - 1))) ∨ (¬ ((x07 - x67) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x06 + ((-1) * x67)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x06 + ((-1) * x07)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x67 ≤ x07) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x07 ≤ x06) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x06 - x67) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x06 - x07) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x07 - x67) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th124 t x06 x07 x67
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause2243 (t x06 x07 x67 : ℝ) : (((x06 + ((-1) * x67)) ≤ (-1)) ∨ ((x06 + ((-1) * x67)) ≥ 1) ∨ (¬ (x67 ≤ x07)) ∨ (¬ (x07 ≤ x06)) ∨ (¬ ((x06 - x67) ≥ 1)) ∨ (¬ ((x06 - x07) ≤ (t - 1))) ∨ (¬ ((x07 - x67) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x06 + ((-1) * x67)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x06 + ((-1) * x67)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x67 ≤ x07) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x07 ≤ x06) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x06 - x67) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x06 - x07) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x07 - x67) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th124 t x06 x07 x67
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause2306 (t x06 x07 x67 : ℝ) (h : (((x06 ≤ x07) ∧ (x07 ≤ x67) ∧ ((x67 - x06) ≥ 1) ∧ ((x07 - x06) ≤ (t - 1)) ∧ ((x67 - x07) ≤ (t - 1))) ∨ ((x67 ≤ x07) ∧ (x07 ≤ x06) ∧ ((x06 - x67) ≥ 1) ∧ ((x06 - x07) ≤ (t - 1)) ∧ ((x07 - x67) ≤ (t - 1))))) : ((x06 ≤ x07) ∨ (x67 ≤ x07)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x06 ≤ x07) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x67 ≤ x07) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause2307 (t x06 x07 x67 : ℝ) (h : (((x06 ≤ x07) ∧ (x07 ≤ x67) ∧ ((x67 - x06) ≥ 1) ∧ ((x07 - x06) ≤ (t - 1)) ∧ ((x67 - x07) ≤ (t - 1))) ∨ ((x67 ≤ x07) ∧ (x07 ≤ x06) ∧ ((x06 - x67) ≥ 1) ∧ ((x06 - x07) ≤ (t - 1)) ∧ ((x07 - x67) ≤ (t - 1))))) : ((x06 ≤ x07) ∨ (x07 ≤ x06)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x06 ≤ x07) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x07 ≤ x06) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause2308 (t x06 x07 x67 : ℝ) (h : (((x06 ≤ x07) ∧ (x07 ≤ x67) ∧ ((x67 - x06) ≥ 1) ∧ ((x07 - x06) ≤ (t - 1)) ∧ ((x67 - x07) ≤ (t - 1))) ∨ ((x67 ≤ x07) ∧ (x07 ≤ x06) ∧ ((x06 - x67) ≥ 1) ∧ ((x06 - x07) ≤ (t - 1)) ∧ ((x07 - x67) ≤ (t - 1))))) : ((x06 ≤ x07) ∨ ((x06 - x67) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x06 ≤ x07) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x06 - x67) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause2309 (t x06 x07 x67 : ℝ) (h : (((x06 ≤ x07) ∧ (x07 ≤ x67) ∧ ((x67 - x06) ≥ 1) ∧ ((x07 - x06) ≤ (t - 1)) ∧ ((x67 - x07) ≤ (t - 1))) ∨ ((x67 ≤ x07) ∧ (x07 ≤ x06) ∧ ((x06 - x67) ≥ 1) ∧ ((x06 - x07) ≤ (t - 1)) ∧ ((x07 - x67) ≤ (t - 1))))) : ((x06 ≤ x07) ∨ ((x06 - x07) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x06 ≤ x07) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x06 - x07) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause2310 (t x06 x07 x67 : ℝ) (h : (((x06 ≤ x07) ∧ (x07 ≤ x67) ∧ ((x67 - x06) ≥ 1) ∧ ((x07 - x06) ≤ (t - 1)) ∧ ((x67 - x07) ≤ (t - 1))) ∨ ((x67 ≤ x07) ∧ (x07 ≤ x06) ∧ ((x06 - x67) ≥ 1) ∧ ((x06 - x07) ≤ (t - 1)) ∧ ((x07 - x67) ≤ (t - 1))))) : ((x06 ≤ x07) ∨ ((x07 - x67) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x06 ≤ x07) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x07 - x67) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause2311 (t x06 x07 x67 : ℝ) (h : (((x06 ≤ x07) ∧ (x07 ≤ x67) ∧ ((x67 - x06) ≥ 1) ∧ ((x07 - x06) ≤ (t - 1)) ∧ ((x67 - x07) ≤ (t - 1))) ∨ ((x67 ≤ x07) ∧ (x07 ≤ x06) ∧ ((x06 - x67) ≥ 1) ∧ ((x06 - x07) ≤ (t - 1)) ∧ ((x07 - x67) ≤ (t - 1))))) : ((x07 ≤ x67) ∨ (x67 ≤ x07)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x07 ≤ x67) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x67 ≤ x07) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause2312 (t x06 x07 x67 : ℝ) (h : (((x06 ≤ x07) ∧ (x07 ≤ x67) ∧ ((x67 - x06) ≥ 1) ∧ ((x07 - x06) ≤ (t - 1)) ∧ ((x67 - x07) ≤ (t - 1))) ∨ ((x67 ≤ x07) ∧ (x07 ≤ x06) ∧ ((x06 - x67) ≥ 1) ∧ ((x06 - x07) ≤ (t - 1)) ∧ ((x07 - x67) ≤ (t - 1))))) : ((x07 ≤ x67) ∨ (x07 ≤ x06)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x07 ≤ x67) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x07 ≤ x06) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause2313 (t x06 x07 x67 : ℝ) (h : (((x06 ≤ x07) ∧ (x07 ≤ x67) ∧ ((x67 - x06) ≥ 1) ∧ ((x07 - x06) ≤ (t - 1)) ∧ ((x67 - x07) ≤ (t - 1))) ∨ ((x67 ≤ x07) ∧ (x07 ≤ x06) ∧ ((x06 - x67) ≥ 1) ∧ ((x06 - x07) ≤ (t - 1)) ∧ ((x07 - x67) ≤ (t - 1))))) : ((x07 ≤ x67) ∨ ((x06 - x67) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x07 ≤ x67) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x06 - x67) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause2314 (t x06 x07 x67 : ℝ) (h : (((x06 ≤ x07) ∧ (x07 ≤ x67) ∧ ((x67 - x06) ≥ 1) ∧ ((x07 - x06) ≤ (t - 1)) ∧ ((x67 - x07) ≤ (t - 1))) ∨ ((x67 ≤ x07) ∧ (x07 ≤ x06) ∧ ((x06 - x67) ≥ 1) ∧ ((x06 - x07) ≤ (t - 1)) ∧ ((x07 - x67) ≤ (t - 1))))) : ((x07 ≤ x67) ∨ ((x06 - x07) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x07 ≤ x67) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x06 - x07) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause2315 (t x06 x07 x67 : ℝ) (h : (((x06 ≤ x07) ∧ (x07 ≤ x67) ∧ ((x67 - x06) ≥ 1) ∧ ((x07 - x06) ≤ (t - 1)) ∧ ((x67 - x07) ≤ (t - 1))) ∨ ((x67 ≤ x07) ∧ (x07 ≤ x06) ∧ ((x06 - x67) ≥ 1) ∧ ((x06 - x07) ≤ (t - 1)) ∧ ((x07 - x67) ≤ (t - 1))))) : ((x07 ≤ x67) ∨ ((x07 - x67) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x07 ≤ x67) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x07 - x67) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause2316 (t x06 x07 x67 : ℝ) (h : (((x06 ≤ x07) ∧ (x07 ≤ x67) ∧ ((x67 - x06) ≥ 1) ∧ ((x07 - x06) ≤ (t - 1)) ∧ ((x67 - x07) ≤ (t - 1))) ∨ ((x67 ≤ x07) ∧ (x07 ≤ x06) ∧ ((x06 - x67) ≥ 1) ∧ ((x06 - x07) ≤ (t - 1)) ∧ ((x07 - x67) ≤ (t - 1))))) : (((x67 - x06) ≥ 1) ∨ (x67 ≤ x07)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x67 - x06) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x67 ≤ x07) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause2317 (t x06 x07 x67 : ℝ) (h : (((x06 ≤ x07) ∧ (x07 ≤ x67) ∧ ((x67 - x06) ≥ 1) ∧ ((x07 - x06) ≤ (t - 1)) ∧ ((x67 - x07) ≤ (t - 1))) ∨ ((x67 ≤ x07) ∧ (x07 ≤ x06) ∧ ((x06 - x67) ≥ 1) ∧ ((x06 - x07) ≤ (t - 1)) ∧ ((x07 - x67) ≤ (t - 1))))) : (((x67 - x06) ≥ 1) ∨ (x07 ≤ x06)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x67 - x06) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x07 ≤ x06) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause2318 (t x06 x07 x67 : ℝ) (h : (((x06 ≤ x07) ∧ (x07 ≤ x67) ∧ ((x67 - x06) ≥ 1) ∧ ((x07 - x06) ≤ (t - 1)) ∧ ((x67 - x07) ≤ (t - 1))) ∨ ((x67 ≤ x07) ∧ (x07 ≤ x06) ∧ ((x06 - x67) ≥ 1) ∧ ((x06 - x07) ≤ (t - 1)) ∧ ((x07 - x67) ≤ (t - 1))))) : (((x67 - x06) ≥ 1) ∨ ((x06 - x67) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x67 - x06) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x06 - x67) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause2319 (t x06 x07 x67 : ℝ) (h : (((x06 ≤ x07) ∧ (x07 ≤ x67) ∧ ((x67 - x06) ≥ 1) ∧ ((x07 - x06) ≤ (t - 1)) ∧ ((x67 - x07) ≤ (t - 1))) ∨ ((x67 ≤ x07) ∧ (x07 ≤ x06) ∧ ((x06 - x67) ≥ 1) ∧ ((x06 - x07) ≤ (t - 1)) ∧ ((x07 - x67) ≤ (t - 1))))) : (((x67 - x06) ≥ 1) ∨ ((x06 - x07) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x67 - x06) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x06 - x07) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause2320 (t x06 x07 x67 : ℝ) (h : (((x06 ≤ x07) ∧ (x07 ≤ x67) ∧ ((x67 - x06) ≥ 1) ∧ ((x07 - x06) ≤ (t - 1)) ∧ ((x67 - x07) ≤ (t - 1))) ∨ ((x67 ≤ x07) ∧ (x07 ≤ x06) ∧ ((x06 - x67) ≥ 1) ∧ ((x06 - x07) ≤ (t - 1)) ∧ ((x07 - x67) ≤ (t - 1))))) : (((x67 - x06) ≥ 1) ∨ ((x07 - x67) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x67 - x06) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x07 - x67) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause2321 (t x06 x07 x67 : ℝ) (h : (((x06 ≤ x07) ∧ (x07 ≤ x67) ∧ ((x67 - x06) ≥ 1) ∧ ((x07 - x06) ≤ (t - 1)) ∧ ((x67 - x07) ≤ (t - 1))) ∨ ((x67 ≤ x07) ∧ (x07 ≤ x06) ∧ ((x06 - x67) ≥ 1) ∧ ((x06 - x07) ≤ (t - 1)) ∧ ((x07 - x67) ≤ (t - 1))))) : (((x07 - x06) ≤ (t - 1)) ∨ (x67 ≤ x07)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x07 - x06) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x67 ≤ x07) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause2322 (t x06 x07 x67 : ℝ) (h : (((x06 ≤ x07) ∧ (x07 ≤ x67) ∧ ((x67 - x06) ≥ 1) ∧ ((x07 - x06) ≤ (t - 1)) ∧ ((x67 - x07) ≤ (t - 1))) ∨ ((x67 ≤ x07) ∧ (x07 ≤ x06) ∧ ((x06 - x67) ≥ 1) ∧ ((x06 - x07) ≤ (t - 1)) ∧ ((x07 - x67) ≤ (t - 1))))) : (((x07 - x06) ≤ (t - 1)) ∨ (x07 ≤ x06)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x07 - x06) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x07 ≤ x06) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause2323 (t x06 x07 x67 : ℝ) (h : (((x06 ≤ x07) ∧ (x07 ≤ x67) ∧ ((x67 - x06) ≥ 1) ∧ ((x07 - x06) ≤ (t - 1)) ∧ ((x67 - x07) ≤ (t - 1))) ∨ ((x67 ≤ x07) ∧ (x07 ≤ x06) ∧ ((x06 - x67) ≥ 1) ∧ ((x06 - x07) ≤ (t - 1)) ∧ ((x07 - x67) ≤ (t - 1))))) : (((x07 - x06) ≤ (t - 1)) ∨ ((x06 - x67) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x07 - x06) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x06 - x67) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause2324 (t x06 x07 x67 : ℝ) (h : (((x06 ≤ x07) ∧ (x07 ≤ x67) ∧ ((x67 - x06) ≥ 1) ∧ ((x07 - x06) ≤ (t - 1)) ∧ ((x67 - x07) ≤ (t - 1))) ∨ ((x67 ≤ x07) ∧ (x07 ≤ x06) ∧ ((x06 - x67) ≥ 1) ∧ ((x06 - x07) ≤ (t - 1)) ∧ ((x07 - x67) ≤ (t - 1))))) : (((x07 - x06) ≤ (t - 1)) ∨ ((x06 - x07) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x07 - x06) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x06 - x07) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause2325 (t x06 x07 x67 : ℝ) (h : (((x06 ≤ x07) ∧ (x07 ≤ x67) ∧ ((x67 - x06) ≥ 1) ∧ ((x07 - x06) ≤ (t - 1)) ∧ ((x67 - x07) ≤ (t - 1))) ∨ ((x67 ≤ x07) ∧ (x07 ≤ x06) ∧ ((x06 - x67) ≥ 1) ∧ ((x06 - x07) ≤ (t - 1)) ∧ ((x07 - x67) ≤ (t - 1))))) : (((x07 - x06) ≤ (t - 1)) ∨ ((x07 - x67) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x07 - x06) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x07 - x67) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause2326 (t x06 x07 x67 : ℝ) (h : (((x06 ≤ x07) ∧ (x07 ≤ x67) ∧ ((x67 - x06) ≥ 1) ∧ ((x07 - x06) ≤ (t - 1)) ∧ ((x67 - x07) ≤ (t - 1))) ∨ ((x67 ≤ x07) ∧ (x07 ≤ x06) ∧ ((x06 - x67) ≥ 1) ∧ ((x06 - x07) ≤ (t - 1)) ∧ ((x07 - x67) ≤ (t - 1))))) : (((x67 - x07) ≤ (t - 1)) ∨ (x67 ≤ x07)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x67 - x07) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x67 ≤ x07) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause2327 (t x06 x07 x67 : ℝ) (h : (((x06 ≤ x07) ∧ (x07 ≤ x67) ∧ ((x67 - x06) ≥ 1) ∧ ((x07 - x06) ≤ (t - 1)) ∧ ((x67 - x07) ≤ (t - 1))) ∨ ((x67 ≤ x07) ∧ (x07 ≤ x06) ∧ ((x06 - x67) ≥ 1) ∧ ((x06 - x07) ≤ (t - 1)) ∧ ((x07 - x67) ≤ (t - 1))))) : (((x67 - x07) ≤ (t - 1)) ∨ (x07 ≤ x06)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x67 - x07) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x07 ≤ x06) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause2328 (t x06 x07 x67 : ℝ) (h : (((x06 ≤ x07) ∧ (x07 ≤ x67) ∧ ((x67 - x06) ≥ 1) ∧ ((x07 - x06) ≤ (t - 1)) ∧ ((x67 - x07) ≤ (t - 1))) ∨ ((x67 ≤ x07) ∧ (x07 ≤ x06) ∧ ((x06 - x67) ≥ 1) ∧ ((x06 - x07) ≤ (t - 1)) ∧ ((x07 - x67) ≤ (t - 1))))) : (((x67 - x07) ≤ (t - 1)) ∨ ((x06 - x67) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x67 - x07) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x06 - x67) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause2329 (t x06 x07 x67 : ℝ) (h : (((x06 ≤ x07) ∧ (x07 ≤ x67) ∧ ((x67 - x06) ≥ 1) ∧ ((x07 - x06) ≤ (t - 1)) ∧ ((x67 - x07) ≤ (t - 1))) ∨ ((x67 ≤ x07) ∧ (x07 ≤ x06) ∧ ((x06 - x67) ≥ 1) ∧ ((x06 - x07) ≤ (t - 1)) ∧ ((x07 - x67) ≤ (t - 1))))) : (((x67 - x07) ≤ (t - 1)) ∨ ((x06 - x07) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x67 - x07) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x06 - x07) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause2330 (t x06 x07 x67 : ℝ) (h : (((x06 ≤ x07) ∧ (x07 ≤ x67) ∧ ((x67 - x06) ≥ 1) ∧ ((x07 - x06) ≤ (t - 1)) ∧ ((x67 - x07) ≤ (t - 1))) ∨ ((x67 ≤ x07) ∧ (x07 ≤ x06) ∧ ((x06 - x67) ≥ 1) ∧ ((x06 - x07) ≤ (t - 1)) ∧ ((x07 - x67) ≤ (t - 1))))) : (((x67 - x07) ≤ (t - 1)) ∨ ((x07 - x67) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x67 - x07) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x07 - x67) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause2331 (t x04 x06 x45 x46 x67 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x46 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((x04 + ((-1) * x45)) ≤ (-1))) ∨ (¬ ((t + ((-1) * x45) + x46) ≥ 1)) ∨ (¬ ((x04 + ((-1) * x06)) ≥ 0)) ∨ (¬ ((x06 + ((-1) * x67)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x46 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x04 + ((-1) * x45)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((t + ((-1) * x45) + x46) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x04 + ((-1) * x06)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x06 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th129 t x04 x06 x45 x46 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u1 (And.intro u2 (And.intro u5 (And.intro u3 (And.intro u4 u0))))))) h

theorem clause2332 (x06 x46 x67 : ℝ) : ((¬ ((x46 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((x06 + ((-1) * x46)) ≤ 0)) ∨ (¬ ((x06 + ((-1) * x67)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x46 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x06 + ((-1) * x46)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x06 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th130 x06 x46 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u0 (And.intro u1 u2)))) h

theorem clause2333 (t x45 x46 x56 : ℝ) : ((¬ ((x45 + ((-1) * x56)) ≤ (-1))) ∨ ((t + ((-1) * x45) + x46) ≥ 1) ∨ ((t + ((-1) * x56)) ≤ 0) ∨ (¬ (x46 ≥ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x45 + ((-1) * x56)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ¬ ((t + ((-1) * x45) + x46) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : ¬ ((t + ((-1) * x56)) ≤ 0) := fun hh => hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x46 ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr hh)))
  have h := NineTheoryTrial.th131 t x45 x46 x56
  exact (fun hh => (fun hh => hh) (hh (And.intro u2 (And.intro u0 (And.intro u1 u3))))) h

theorem clause2334 (x46 : ℝ) (h : (x46 ≥ 0)) : ((x46 ≥ 0)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x46 ≥ 0) := fun hh => hn hh
  exact u0 h

theorem clause2335 (t x56 : ℝ) : ((¬ ((t + ((-1) * x56)) ≤ 0)) ∨ (t ≤ x56)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((t + ((-1) * x56)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ¬ (t ≤ x56) := fun hh => hn (Or.inr hh)
  have h := NineTheoryTrial.th133 t x56
  exact (fun hh => (fun hh => hh u0) (hh.mp u1)) h

theorem clause2337 (t x56 : ℝ) : ((¬ (t ≤ x56)) ∨ (¬ (x56 < t))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (t ≤ x56) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : (x56 < t) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr hh)
  have h := NineTheoryTrial.th134 t x56
  exact (fun hh => (fun hh => hh u0) (hh.mp u1)) h

theorem clause2339 (t x56 : ℝ) (h : (x56 < t)) : ((x56 < t)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x56 < t) := fun hh => hn hh
  exact u0 h

theorem clause2340 (t x68 : ℝ) : ((¬ ((t + ((-1) * x68)) ≤ 0)) ∨ (t ≤ x68)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((t + ((-1) * x68)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ¬ (t ≤ x68) := fun hh => hn (Or.inr hh)
  have h := NineTheoryTrial.th137 t x68
  exact (fun hh => (fun hh => hh u0) (hh.mp u1)) h

theorem clause2342 (t x68 : ℝ) : ((¬ (t ≤ x68)) ∨ (¬ (x68 < t))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (t ≤ x68) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : (x68 < t) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr hh)
  have h := NineTheoryTrial.th138 t x68
  exact (fun hh => (fun hh => hh u0) (hh.mp u1)) h

theorem clause2344 (t x68 : ℝ) (h : (x68 < t)) : ((x68 < t)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x68 < t) := fun hh => hn hh
  exact u0 h

theorem clause2345 (x36 : ℝ) (h : (x36 ≥ 0)) : ((x36 ≥ 0)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x36 ≥ 0) := fun hh => hn hh
  exact u0 h

theorem clause2346 (x36 x46 x68 : ℝ) : ((¬ ((x36 + ((-1) * x46)) ≥ 0)) ∨ (¬ ((x46 + ((-1) * x68)) ≥ 1)) ∨ (¬ ((x36 + ((-1) * x68)) ≤ (-1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x36 + ((-1) * x46)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x46 + ((-1) * x68)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x36 + ((-1) * x68)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th141 x36 x46 x68
  exact (fun hh => (fun hh => hh) (hh (And.intro u1 (And.intro u2 u0)))) h

theorem clause2347 (t x46 x48 x68 : ℝ) : (((x46 + ((-1) * x48)) ≤ 0) ∨ ((x48 + ((-1) * x68)) ≥ 0) ∨ (¬ (x46 ≤ x48)) ∨ (¬ (x48 ≤ x68)) ∨ (¬ ((x68 - x46) ≥ 1)) ∨ (¬ ((x48 - x46) ≤ (t - 1))) ∨ (¬ ((x68 - x48) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x46 + ((-1) * x48)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x48 + ((-1) * x68)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x46 ≤ x48) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x48 ≤ x68) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x68 - x46) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x48 - x46) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x68 - x48) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th143 t x46 x48 x68
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause2349 (t x46 x48 x68 : ℝ) : (((x46 + ((-1) * x68)) ≥ 1) ∨ ((x46 + ((-1) * x48)) ≤ 0) ∨ (¬ (x46 ≤ x48)) ∨ (¬ (x48 ≤ x68)) ∨ (¬ ((x68 - x46) ≥ 1)) ∨ (¬ ((x48 - x46) ≤ (t - 1))) ∨ (¬ ((x68 - x48) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x46 + ((-1) * x68)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x46 + ((-1) * x48)) ≤ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x46 ≤ x48) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x48 ≤ x68) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x68 - x46) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x48 - x46) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x68 - x48) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th143 t x46 x48 x68
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 (hh).1) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause2350 (t x46 x48 x68 : ℝ) : (((x46 + ((-1) * x48)) ≤ 0) ∨ ((t + ((-1) * x46) + x48) ≥ 1) ∨ (¬ (x46 ≤ x48)) ∨ (¬ (x48 ≤ x68)) ∨ (¬ ((x68 - x46) ≥ 1)) ∨ (¬ ((x48 - x46) ≤ (t - 1))) ∨ (¬ ((x68 - x48) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x46 + ((-1) * x48)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + ((-1) * x46) + x48) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x46 ≤ x48) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x48 ≤ x68) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x68 - x46) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x48 - x46) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x68 - x48) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th143 t x46 x48 x68
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause2354 (t x46 x48 x68 : ℝ) : (((x46 + ((-1) * x68)) ≥ 1) ∨ ((x48 + ((-1) * x68)) ≤ 0) ∨ (¬ (x46 ≤ x48)) ∨ (¬ (x48 ≤ x68)) ∨ (¬ ((x68 - x46) ≥ 1)) ∨ (¬ ((x48 - x46) ≤ (t - 1))) ∨ (¬ ((x68 - x48) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x46 + ((-1) * x68)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x48 + ((-1) * x68)) ≤ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x46 ≤ x48) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x48 ≤ x68) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x68 - x46) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x48 - x46) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x68 - x48) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th143 t x46 x48 x68
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 ((hh).2).1) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause2357 (t x46 x48 x68 : ℝ) : (((x46 + ((-1) * x68)) ≤ (-1)) ∨ ((x48 + ((-1) * x68)) ≥ 0) ∨ (¬ (x46 ≤ x48)) ∨ (¬ (x48 ≤ x68)) ∨ (¬ ((x68 - x46) ≥ 1)) ∨ (¬ ((x48 - x46) ≤ (t - 1))) ∨ (¬ ((x68 - x48) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x46 + ((-1) * x68)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x48 + ((-1) * x68)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x46 ≤ x48) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x48 ≤ x68) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x68 - x46) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x48 - x46) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x68 - x48) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th143 t x46 x48 x68
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause2359 (t x46 x48 x68 : ℝ) : (((x46 + ((-1) * x68)) ≥ 1) ∨ ((x46 + ((-1) * x68)) ≤ (-1)) ∨ (¬ (x46 ≤ x48)) ∨ (¬ (x48 ≤ x68)) ∨ (¬ ((x68 - x46) ≥ 1)) ∨ (¬ ((x48 - x46) ≤ (t - 1))) ∨ (¬ ((x68 - x48) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x46 + ((-1) * x68)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x46 + ((-1) * x68)) ≤ (-1)) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x46 ≤ x48) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x48 ≤ x68) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x68 - x46) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x48 - x46) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x68 - x48) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th143 t x46 x48 x68
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 (((hh).2).2).1) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause2360 (t x46 x48 x68 : ℝ) : (((x46 + ((-1) * x68)) ≤ (-1)) ∨ ((t + ((-1) * x46) + x48) ≥ 1) ∨ (¬ (x46 ≤ x48)) ∨ (¬ (x48 ≤ x68)) ∨ (¬ ((x68 - x46) ≥ 1)) ∨ (¬ ((x48 - x46) ≤ (t - 1))) ∨ (¬ ((x68 - x48) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x46 + ((-1) * x68)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + ((-1) * x46) + x48) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x46 ≤ x48) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x48 ≤ x68) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x68 - x46) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x48 - x46) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x68 - x48) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th143 t x46 x48 x68
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause2361 (t x46 x48 x68 : ℝ) : (((x46 + ((-1) * x68)) ≤ (-1)) ∨ ((t + ((-1) * x48) + x68) ≥ 1) ∨ (¬ (x46 ≤ x48)) ∨ (¬ (x48 ≤ x68)) ∨ (¬ ((x68 - x46) ≥ 1)) ∨ (¬ ((x48 - x46) ≤ (t - 1))) ∨ (¬ ((x68 - x48) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x46 + ((-1) * x68)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + ((-1) * x48) + x68) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x46 ≤ x48) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x48 ≤ x68) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x68 - x46) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x48 - x46) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x68 - x48) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th143 t x46 x48 x68
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause2364 (t x46 x48 x68 : ℝ) : (((x46 + ((-1) * x68)) ≥ 1) ∨ ((t + x46 + ((-1) * x48)) ≥ 1) ∨ (¬ (x46 ≤ x48)) ∨ (¬ (x48 ≤ x68)) ∨ (¬ ((x68 - x46) ≥ 1)) ∨ (¬ ((x48 - x46) ≤ (t - 1))) ∨ (¬ ((x68 - x48) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x46 + ((-1) * x68)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + x46 + ((-1) * x48)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x46 ≤ x48) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x48 ≤ x68) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x68 - x46) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x48 - x46) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x68 - x48) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th143 t x46 x48 x68
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 ((((hh).2).2).2).1) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause2369 (t x46 x48 x68 : ℝ) : (((x46 + ((-1) * x68)) ≥ 1) ∨ ((t + x48 + ((-1) * x68)) ≥ 1) ∨ (¬ (x46 ≤ x48)) ∨ (¬ (x48 ≤ x68)) ∨ (¬ ((x68 - x46) ≥ 1)) ∨ (¬ ((x48 - x46) ≤ (t - 1))) ∨ (¬ ((x68 - x48) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x46 + ((-1) * x68)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + x48 + ((-1) * x68)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x46 ≤ x48) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x48 ≤ x68) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x68 - x46) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x48 - x46) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x68 - x48) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th143 t x46 x48 x68
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 ((((hh).2).2).2).2) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause2372 (t x46 x48 x68 : ℝ) : (((x46 + ((-1) * x48)) ≤ 0) ∨ ((x48 + ((-1) * x68)) ≥ 0) ∨ (¬ (x68 ≤ x48)) ∨ (¬ (x48 ≤ x46)) ∨ (¬ ((x46 - x68) ≥ 1)) ∨ (¬ ((x46 - x48) ≤ (t - 1))) ∨ (¬ ((x48 - x68) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x46 + ((-1) * x48)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x48 + ((-1) * x68)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x68 ≤ x48) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x48 ≤ x46) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x46 - x68) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x46 - x48) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x48 - x68) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th143 t x46 x48 x68
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause2374 (t x46 x48 x68 : ℝ) : (((x46 + ((-1) * x68)) ≥ 1) ∨ ((x46 + ((-1) * x48)) ≤ 0) ∨ (¬ (x68 ≤ x48)) ∨ (¬ (x48 ≤ x46)) ∨ (¬ ((x46 - x68) ≥ 1)) ∨ (¬ ((x46 - x48) ≤ (t - 1))) ∨ (¬ ((x48 - x68) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x46 + ((-1) * x68)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x46 + ((-1) * x48)) ≤ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x68 ≤ x48) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x48 ≤ x46) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x46 - x68) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x46 - x48) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x48 - x68) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th143 t x46 x48 x68
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 (hh).1) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause2375 (t x46 x48 x68 : ℝ) : (((x46 + ((-1) * x48)) ≤ 0) ∨ ((t + ((-1) * x46) + x48) ≥ 1) ∨ (¬ (x68 ≤ x48)) ∨ (¬ (x48 ≤ x46)) ∨ (¬ ((x46 - x68) ≥ 1)) ∨ (¬ ((x46 - x48) ≤ (t - 1))) ∨ (¬ ((x48 - x68) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x46 + ((-1) * x48)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + ((-1) * x46) + x48) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x68 ≤ x48) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x48 ≤ x46) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x46 - x68) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x46 - x48) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x48 - x68) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th143 t x46 x48 x68
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause2379 (t x46 x48 x68 : ℝ) : (((x46 + ((-1) * x68)) ≥ 1) ∨ ((x48 + ((-1) * x68)) ≤ 0) ∨ (¬ (x68 ≤ x48)) ∨ (¬ (x48 ≤ x46)) ∨ (¬ ((x46 - x68) ≥ 1)) ∨ (¬ ((x46 - x48) ≤ (t - 1))) ∨ (¬ ((x48 - x68) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x46 + ((-1) * x68)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x48 + ((-1) * x68)) ≤ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x68 ≤ x48) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x48 ≤ x46) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x46 - x68) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x46 - x48) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x48 - x68) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th143 t x46 x48 x68
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 ((hh).2).1) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause2382 (t x46 x48 x68 : ℝ) : (((x46 + ((-1) * x68)) ≤ (-1)) ∨ ((x48 + ((-1) * x68)) ≥ 0) ∨ (¬ (x68 ≤ x48)) ∨ (¬ (x48 ≤ x46)) ∨ (¬ ((x46 - x68) ≥ 1)) ∨ (¬ ((x46 - x48) ≤ (t - 1))) ∨ (¬ ((x48 - x68) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x46 + ((-1) * x68)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x48 + ((-1) * x68)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x68 ≤ x48) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x48 ≤ x46) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x46 - x68) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x46 - x48) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x48 - x68) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th143 t x46 x48 x68
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause2384 (t x46 x48 x68 : ℝ) : (((x46 + ((-1) * x68)) ≥ 1) ∨ ((x46 + ((-1) * x68)) ≤ (-1)) ∨ (¬ (x68 ≤ x48)) ∨ (¬ (x48 ≤ x46)) ∨ (¬ ((x46 - x68) ≥ 1)) ∨ (¬ ((x46 - x48) ≤ (t - 1))) ∨ (¬ ((x48 - x68) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x46 + ((-1) * x68)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x46 + ((-1) * x68)) ≤ (-1)) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x68 ≤ x48) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x48 ≤ x46) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x46 - x68) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x46 - x48) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x48 - x68) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th143 t x46 x48 x68
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 (((hh).2).2).1) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause2385 (t x46 x48 x68 : ℝ) : (((x46 + ((-1) * x68)) ≤ (-1)) ∨ ((t + ((-1) * x46) + x48) ≥ 1) ∨ (¬ (x68 ≤ x48)) ∨ (¬ (x48 ≤ x46)) ∨ (¬ ((x46 - x68) ≥ 1)) ∨ (¬ ((x46 - x48) ≤ (t - 1))) ∨ (¬ ((x48 - x68) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x46 + ((-1) * x68)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + ((-1) * x46) + x48) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x68 ≤ x48) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x48 ≤ x46) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x46 - x68) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x46 - x48) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x48 - x68) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th143 t x46 x48 x68
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause2386 (t x46 x48 x68 : ℝ) : (((x46 + ((-1) * x68)) ≤ (-1)) ∨ ((t + ((-1) * x48) + x68) ≥ 1) ∨ (¬ (x68 ≤ x48)) ∨ (¬ (x48 ≤ x46)) ∨ (¬ ((x46 - x68) ≥ 1)) ∨ (¬ ((x46 - x48) ≤ (t - 1))) ∨ (¬ ((x48 - x68) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x46 + ((-1) * x68)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + ((-1) * x48) + x68) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x68 ≤ x48) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x48 ≤ x46) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x46 - x68) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x46 - x48) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x48 - x68) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th143 t x46 x48 x68
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause2389 (t x46 x48 x68 : ℝ) : (((x46 + ((-1) * x68)) ≥ 1) ∨ ((t + x46 + ((-1) * x48)) ≥ 1) ∨ (¬ (x68 ≤ x48)) ∨ (¬ (x48 ≤ x46)) ∨ (¬ ((x46 - x68) ≥ 1)) ∨ (¬ ((x46 - x48) ≤ (t - 1))) ∨ (¬ ((x48 - x68) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x46 + ((-1) * x68)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + x46 + ((-1) * x48)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x68 ≤ x48) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x48 ≤ x46) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x46 - x68) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x46 - x48) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x48 - x68) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th143 t x46 x48 x68
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 ((((hh).2).2).2).1) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause2394 (t x46 x48 x68 : ℝ) : (((x46 + ((-1) * x68)) ≥ 1) ∨ ((t + x48 + ((-1) * x68)) ≥ 1) ∨ (¬ (x68 ≤ x48)) ∨ (¬ (x48 ≤ x46)) ∨ (¬ ((x46 - x68) ≥ 1)) ∨ (¬ ((x46 - x48) ≤ (t - 1))) ∨ (¬ ((x48 - x68) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x46 + ((-1) * x68)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + x48 + ((-1) * x68)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x68 ≤ x48) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x48 ≤ x46) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x46 - x68) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x46 - x48) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x48 - x68) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th143 t x46 x48 x68
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 ((((hh).2).2).2).2) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause2447 (t x46 x48 x68 : ℝ) (h : (((x46 ≤ x48) ∧ (x48 ≤ x68) ∧ ((x68 - x46) ≥ 1) ∧ ((x48 - x46) ≤ (t - 1)) ∧ ((x68 - x48) ≤ (t - 1))) ∨ ((x68 ≤ x48) ∧ (x48 ≤ x46) ∧ ((x46 - x68) ≥ 1) ∧ ((x46 - x48) ≤ (t - 1)) ∧ ((x48 - x68) ≤ (t - 1))))) : ((x46 ≤ x48) ∨ (x68 ≤ x48)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x46 ≤ x48) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x68 ≤ x48) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause2448 (t x46 x48 x68 : ℝ) (h : (((x46 ≤ x48) ∧ (x48 ≤ x68) ∧ ((x68 - x46) ≥ 1) ∧ ((x48 - x46) ≤ (t - 1)) ∧ ((x68 - x48) ≤ (t - 1))) ∨ ((x68 ≤ x48) ∧ (x48 ≤ x46) ∧ ((x46 - x68) ≥ 1) ∧ ((x46 - x48) ≤ (t - 1)) ∧ ((x48 - x68) ≤ (t - 1))))) : ((x46 ≤ x48) ∨ (x48 ≤ x46)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x46 ≤ x48) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x48 ≤ x46) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause2449 (t x46 x48 x68 : ℝ) (h : (((x46 ≤ x48) ∧ (x48 ≤ x68) ∧ ((x68 - x46) ≥ 1) ∧ ((x48 - x46) ≤ (t - 1)) ∧ ((x68 - x48) ≤ (t - 1))) ∨ ((x68 ≤ x48) ∧ (x48 ≤ x46) ∧ ((x46 - x68) ≥ 1) ∧ ((x46 - x48) ≤ (t - 1)) ∧ ((x48 - x68) ≤ (t - 1))))) : ((x46 ≤ x48) ∨ ((x46 - x68) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x46 ≤ x48) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x46 - x68) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause2450 (t x46 x48 x68 : ℝ) (h : (((x46 ≤ x48) ∧ (x48 ≤ x68) ∧ ((x68 - x46) ≥ 1) ∧ ((x48 - x46) ≤ (t - 1)) ∧ ((x68 - x48) ≤ (t - 1))) ∨ ((x68 ≤ x48) ∧ (x48 ≤ x46) ∧ ((x46 - x68) ≥ 1) ∧ ((x46 - x48) ≤ (t - 1)) ∧ ((x48 - x68) ≤ (t - 1))))) : ((x46 ≤ x48) ∨ ((x46 - x48) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x46 ≤ x48) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x46 - x48) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause2451 (t x46 x48 x68 : ℝ) (h : (((x46 ≤ x48) ∧ (x48 ≤ x68) ∧ ((x68 - x46) ≥ 1) ∧ ((x48 - x46) ≤ (t - 1)) ∧ ((x68 - x48) ≤ (t - 1))) ∨ ((x68 ≤ x48) ∧ (x48 ≤ x46) ∧ ((x46 - x68) ≥ 1) ∧ ((x46 - x48) ≤ (t - 1)) ∧ ((x48 - x68) ≤ (t - 1))))) : ((x46 ≤ x48) ∨ ((x48 - x68) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x46 ≤ x48) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x48 - x68) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause2452 (t x46 x48 x68 : ℝ) (h : (((x46 ≤ x48) ∧ (x48 ≤ x68) ∧ ((x68 - x46) ≥ 1) ∧ ((x48 - x46) ≤ (t - 1)) ∧ ((x68 - x48) ≤ (t - 1))) ∨ ((x68 ≤ x48) ∧ (x48 ≤ x46) ∧ ((x46 - x68) ≥ 1) ∧ ((x46 - x48) ≤ (t - 1)) ∧ ((x48 - x68) ≤ (t - 1))))) : ((x48 ≤ x68) ∨ (x68 ≤ x48)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x48 ≤ x68) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x68 ≤ x48) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause2453 (t x46 x48 x68 : ℝ) (h : (((x46 ≤ x48) ∧ (x48 ≤ x68) ∧ ((x68 - x46) ≥ 1) ∧ ((x48 - x46) ≤ (t - 1)) ∧ ((x68 - x48) ≤ (t - 1))) ∨ ((x68 ≤ x48) ∧ (x48 ≤ x46) ∧ ((x46 - x68) ≥ 1) ∧ ((x46 - x48) ≤ (t - 1)) ∧ ((x48 - x68) ≤ (t - 1))))) : ((x48 ≤ x68) ∨ (x48 ≤ x46)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x48 ≤ x68) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x48 ≤ x46) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause2454 (t x46 x48 x68 : ℝ) (h : (((x46 ≤ x48) ∧ (x48 ≤ x68) ∧ ((x68 - x46) ≥ 1) ∧ ((x48 - x46) ≤ (t - 1)) ∧ ((x68 - x48) ≤ (t - 1))) ∨ ((x68 ≤ x48) ∧ (x48 ≤ x46) ∧ ((x46 - x68) ≥ 1) ∧ ((x46 - x48) ≤ (t - 1)) ∧ ((x48 - x68) ≤ (t - 1))))) : ((x48 ≤ x68) ∨ ((x46 - x68) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x48 ≤ x68) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x46 - x68) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause2455 (t x46 x48 x68 : ℝ) (h : (((x46 ≤ x48) ∧ (x48 ≤ x68) ∧ ((x68 - x46) ≥ 1) ∧ ((x48 - x46) ≤ (t - 1)) ∧ ((x68 - x48) ≤ (t - 1))) ∨ ((x68 ≤ x48) ∧ (x48 ≤ x46) ∧ ((x46 - x68) ≥ 1) ∧ ((x46 - x48) ≤ (t - 1)) ∧ ((x48 - x68) ≤ (t - 1))))) : ((x48 ≤ x68) ∨ ((x46 - x48) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x48 ≤ x68) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x46 - x48) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause2456 (t x46 x48 x68 : ℝ) (h : (((x46 ≤ x48) ∧ (x48 ≤ x68) ∧ ((x68 - x46) ≥ 1) ∧ ((x48 - x46) ≤ (t - 1)) ∧ ((x68 - x48) ≤ (t - 1))) ∨ ((x68 ≤ x48) ∧ (x48 ≤ x46) ∧ ((x46 - x68) ≥ 1) ∧ ((x46 - x48) ≤ (t - 1)) ∧ ((x48 - x68) ≤ (t - 1))))) : ((x48 ≤ x68) ∨ ((x48 - x68) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x48 ≤ x68) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x48 - x68) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause2457 (t x46 x48 x68 : ℝ) (h : (((x46 ≤ x48) ∧ (x48 ≤ x68) ∧ ((x68 - x46) ≥ 1) ∧ ((x48 - x46) ≤ (t - 1)) ∧ ((x68 - x48) ≤ (t - 1))) ∨ ((x68 ≤ x48) ∧ (x48 ≤ x46) ∧ ((x46 - x68) ≥ 1) ∧ ((x46 - x48) ≤ (t - 1)) ∧ ((x48 - x68) ≤ (t - 1))))) : (((x68 - x46) ≥ 1) ∨ (x68 ≤ x48)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x68 - x46) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x68 ≤ x48) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause2458 (t x46 x48 x68 : ℝ) (h : (((x46 ≤ x48) ∧ (x48 ≤ x68) ∧ ((x68 - x46) ≥ 1) ∧ ((x48 - x46) ≤ (t - 1)) ∧ ((x68 - x48) ≤ (t - 1))) ∨ ((x68 ≤ x48) ∧ (x48 ≤ x46) ∧ ((x46 - x68) ≥ 1) ∧ ((x46 - x48) ≤ (t - 1)) ∧ ((x48 - x68) ≤ (t - 1))))) : (((x68 - x46) ≥ 1) ∨ (x48 ≤ x46)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x68 - x46) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x48 ≤ x46) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause2459 (t x46 x48 x68 : ℝ) (h : (((x46 ≤ x48) ∧ (x48 ≤ x68) ∧ ((x68 - x46) ≥ 1) ∧ ((x48 - x46) ≤ (t - 1)) ∧ ((x68 - x48) ≤ (t - 1))) ∨ ((x68 ≤ x48) ∧ (x48 ≤ x46) ∧ ((x46 - x68) ≥ 1) ∧ ((x46 - x48) ≤ (t - 1)) ∧ ((x48 - x68) ≤ (t - 1))))) : (((x68 - x46) ≥ 1) ∨ ((x46 - x68) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x68 - x46) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x46 - x68) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause2460 (t x46 x48 x68 : ℝ) (h : (((x46 ≤ x48) ∧ (x48 ≤ x68) ∧ ((x68 - x46) ≥ 1) ∧ ((x48 - x46) ≤ (t - 1)) ∧ ((x68 - x48) ≤ (t - 1))) ∨ ((x68 ≤ x48) ∧ (x48 ≤ x46) ∧ ((x46 - x68) ≥ 1) ∧ ((x46 - x48) ≤ (t - 1)) ∧ ((x48 - x68) ≤ (t - 1))))) : (((x68 - x46) ≥ 1) ∨ ((x46 - x48) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x68 - x46) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x46 - x48) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause2461 (t x46 x48 x68 : ℝ) (h : (((x46 ≤ x48) ∧ (x48 ≤ x68) ∧ ((x68 - x46) ≥ 1) ∧ ((x48 - x46) ≤ (t - 1)) ∧ ((x68 - x48) ≤ (t - 1))) ∨ ((x68 ≤ x48) ∧ (x48 ≤ x46) ∧ ((x46 - x68) ≥ 1) ∧ ((x46 - x48) ≤ (t - 1)) ∧ ((x48 - x68) ≤ (t - 1))))) : (((x68 - x46) ≥ 1) ∨ ((x48 - x68) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x68 - x46) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x48 - x68) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause2462 (t x46 x48 x68 : ℝ) (h : (((x46 ≤ x48) ∧ (x48 ≤ x68) ∧ ((x68 - x46) ≥ 1) ∧ ((x48 - x46) ≤ (t - 1)) ∧ ((x68 - x48) ≤ (t - 1))) ∨ ((x68 ≤ x48) ∧ (x48 ≤ x46) ∧ ((x46 - x68) ≥ 1) ∧ ((x46 - x48) ≤ (t - 1)) ∧ ((x48 - x68) ≤ (t - 1))))) : (((x48 - x46) ≤ (t - 1)) ∨ (x68 ≤ x48)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x48 - x46) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x68 ≤ x48) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause2463 (t x46 x48 x68 : ℝ) (h : (((x46 ≤ x48) ∧ (x48 ≤ x68) ∧ ((x68 - x46) ≥ 1) ∧ ((x48 - x46) ≤ (t - 1)) ∧ ((x68 - x48) ≤ (t - 1))) ∨ ((x68 ≤ x48) ∧ (x48 ≤ x46) ∧ ((x46 - x68) ≥ 1) ∧ ((x46 - x48) ≤ (t - 1)) ∧ ((x48 - x68) ≤ (t - 1))))) : (((x48 - x46) ≤ (t - 1)) ∨ (x48 ≤ x46)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x48 - x46) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x48 ≤ x46) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause2464 (t x46 x48 x68 : ℝ) (h : (((x46 ≤ x48) ∧ (x48 ≤ x68) ∧ ((x68 - x46) ≥ 1) ∧ ((x48 - x46) ≤ (t - 1)) ∧ ((x68 - x48) ≤ (t - 1))) ∨ ((x68 ≤ x48) ∧ (x48 ≤ x46) ∧ ((x46 - x68) ≥ 1) ∧ ((x46 - x48) ≤ (t - 1)) ∧ ((x48 - x68) ≤ (t - 1))))) : (((x48 - x46) ≤ (t - 1)) ∨ ((x46 - x68) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x48 - x46) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x46 - x68) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause2465 (t x46 x48 x68 : ℝ) (h : (((x46 ≤ x48) ∧ (x48 ≤ x68) ∧ ((x68 - x46) ≥ 1) ∧ ((x48 - x46) ≤ (t - 1)) ∧ ((x68 - x48) ≤ (t - 1))) ∨ ((x68 ≤ x48) ∧ (x48 ≤ x46) ∧ ((x46 - x68) ≥ 1) ∧ ((x46 - x48) ≤ (t - 1)) ∧ ((x48 - x68) ≤ (t - 1))))) : (((x48 - x46) ≤ (t - 1)) ∨ ((x46 - x48) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x48 - x46) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x46 - x48) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause2466 (t x46 x48 x68 : ℝ) (h : (((x46 ≤ x48) ∧ (x48 ≤ x68) ∧ ((x68 - x46) ≥ 1) ∧ ((x48 - x46) ≤ (t - 1)) ∧ ((x68 - x48) ≤ (t - 1))) ∨ ((x68 ≤ x48) ∧ (x48 ≤ x46) ∧ ((x46 - x68) ≥ 1) ∧ ((x46 - x48) ≤ (t - 1)) ∧ ((x48 - x68) ≤ (t - 1))))) : (((x48 - x46) ≤ (t - 1)) ∨ ((x48 - x68) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x48 - x46) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x48 - x68) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause2467 (t x46 x48 x68 : ℝ) (h : (((x46 ≤ x48) ∧ (x48 ≤ x68) ∧ ((x68 - x46) ≥ 1) ∧ ((x48 - x46) ≤ (t - 1)) ∧ ((x68 - x48) ≤ (t - 1))) ∨ ((x68 ≤ x48) ∧ (x48 ≤ x46) ∧ ((x46 - x68) ≥ 1) ∧ ((x46 - x48) ≤ (t - 1)) ∧ ((x48 - x68) ≤ (t - 1))))) : (((x68 - x48) ≤ (t - 1)) ∨ (x68 ≤ x48)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x68 - x48) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x68 ≤ x48) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause2468 (t x46 x48 x68 : ℝ) (h : (((x46 ≤ x48) ∧ (x48 ≤ x68) ∧ ((x68 - x46) ≥ 1) ∧ ((x48 - x46) ≤ (t - 1)) ∧ ((x68 - x48) ≤ (t - 1))) ∨ ((x68 ≤ x48) ∧ (x48 ≤ x46) ∧ ((x46 - x68) ≥ 1) ∧ ((x46 - x48) ≤ (t - 1)) ∧ ((x48 - x68) ≤ (t - 1))))) : (((x68 - x48) ≤ (t - 1)) ∨ (x48 ≤ x46)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x68 - x48) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x48 ≤ x46) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause2469 (t x46 x48 x68 : ℝ) (h : (((x46 ≤ x48) ∧ (x48 ≤ x68) ∧ ((x68 - x46) ≥ 1) ∧ ((x48 - x46) ≤ (t - 1)) ∧ ((x68 - x48) ≤ (t - 1))) ∨ ((x68 ≤ x48) ∧ (x48 ≤ x46) ∧ ((x46 - x68) ≥ 1) ∧ ((x46 - x48) ≤ (t - 1)) ∧ ((x48 - x68) ≤ (t - 1))))) : (((x68 - x48) ≤ (t - 1)) ∨ ((x46 - x68) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x68 - x48) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x46 - x68) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause2470 (t x46 x48 x68 : ℝ) (h : (((x46 ≤ x48) ∧ (x48 ≤ x68) ∧ ((x68 - x46) ≥ 1) ∧ ((x48 - x46) ≤ (t - 1)) ∧ ((x68 - x48) ≤ (t - 1))) ∨ ((x68 ≤ x48) ∧ (x48 ≤ x46) ∧ ((x46 - x68) ≥ 1) ∧ ((x46 - x48) ≤ (t - 1)) ∧ ((x48 - x68) ≤ (t - 1))))) : (((x68 - x48) ≤ (t - 1)) ∨ ((x46 - x48) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x68 - x48) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x46 - x48) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause2471 (t x46 x48 x68 : ℝ) (h : (((x46 ≤ x48) ∧ (x48 ≤ x68) ∧ ((x68 - x46) ≥ 1) ∧ ((x48 - x46) ≤ (t - 1)) ∧ ((x68 - x48) ≤ (t - 1))) ∨ ((x68 ≤ x48) ∧ (x48 ≤ x46) ∧ ((x46 - x68) ≥ 1) ∧ ((x46 - x48) ≤ (t - 1)) ∧ ((x48 - x68) ≤ (t - 1))))) : (((x68 - x48) ≤ (t - 1)) ∨ ((x48 - x68) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x68 - x48) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x48 - x68) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause2472 (t x14 x46 x47 x67 x68 : ℝ) : ((t ≥ (7 / 2)) ∨ (¬ ((x47 + ((-1) * x67)) ≥ 0)) ∨ (¬ ((x14 + ((-1) * x46)) ≤ (-1))) ∨ (¬ ((t + x67 + ((-1) * x68)) ≥ 1)) ∨ (¬ ((x46 + ((-1) * x68)) ≤ (-1))) ∨ (¬ ((x14 + ((-1) * x47)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inl hh)
  have u1 : ((x47 + ((-1) * x67)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x14 + ((-1) * x46)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((t + x67 + ((-1) * x68)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x46 + ((-1) * x68)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x14 + ((-1) * x47)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th145 t x14 x46 x47 x67 x68
  exact (fun hh => (fun hh => hh) (hh (And.intro u2 (And.intro u5 (And.intro u4 (And.intro u1 (And.intro u3 u0))))))) h

theorem clause2473 (x04 x34 x46 : ℝ) : ((¬ ((x04 + ((-1) * x46)) ≤ (-1))) ∨ (¬ ((x04 + ((-1) * x34)) ≥ 0)) ∨ (¬ ((x34 + ((-1) * x46)) ≥ 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x04 + ((-1) * x46)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x04 + ((-1) * x34)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x34 + ((-1) * x46)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th146 x04 x34 x46
  exact (fun hh => (fun hh => hh) (hh (And.intro u2 (And.intro u0 u1)))) h

theorem clause2475 (t x14 x17 x47 : ℝ) : (((x14 + ((-1) * x17)) ≤ 0) ∨ ((x17 + ((-1) * x47)) ≥ 0) ∨ (¬ (x14 ≤ x17)) ∨ (¬ (x17 ≤ x47)) ∨ (¬ ((x47 - x14) ≥ 1)) ∨ (¬ ((x17 - x14) ≤ (t - 1))) ∨ (¬ ((x47 - x17) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x14 + ((-1) * x17)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x17 + ((-1) * x47)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x14 ≤ x17) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x17 ≤ x47) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x47 - x14) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x17 - x14) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x47 - x17) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th149 t x14 x17 x47
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause2477 (t x14 x17 x47 : ℝ) : (((x14 + ((-1) * x47)) ≥ 1) ∨ ((x14 + ((-1) * x17)) ≤ 0) ∨ (¬ (x14 ≤ x17)) ∨ (¬ (x17 ≤ x47)) ∨ (¬ ((x47 - x14) ≥ 1)) ∨ (¬ ((x17 - x14) ≤ (t - 1))) ∨ (¬ ((x47 - x17) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x14 + ((-1) * x47)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x14 + ((-1) * x17)) ≤ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x14 ≤ x17) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x17 ≤ x47) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x47 - x14) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x17 - x14) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x47 - x17) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th149 t x14 x17 x47
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 (hh).1) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause2481 (t x14 x17 x47 : ℝ) : (((x17 + ((-1) * x47)) ≤ 0) ∨ ((x14 + ((-1) * x17)) ≥ 0) ∨ (¬ (x14 ≤ x17)) ∨ (¬ (x17 ≤ x47)) ∨ (¬ ((x47 - x14) ≥ 1)) ∨ (¬ ((x17 - x14) ≤ (t - 1))) ∨ (¬ ((x47 - x17) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x17 + ((-1) * x47)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x14 + ((-1) * x17)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x14 ≤ x17) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x17 ≤ x47) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x47 - x14) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x17 - x14) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x47 - x17) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th149 t x14 x17 x47
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause2482 (t x14 x17 x47 : ℝ) : (((x14 + ((-1) * x47)) ≥ 1) ∨ ((x17 + ((-1) * x47)) ≤ 0) ∨ (¬ (x14 ≤ x17)) ∨ (¬ (x17 ≤ x47)) ∨ (¬ ((x47 - x14) ≥ 1)) ∨ (¬ ((x17 - x14) ≤ (t - 1))) ∨ (¬ ((x47 - x17) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x14 + ((-1) * x47)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x17 + ((-1) * x47)) ≤ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x14 ≤ x17) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x17 ≤ x47) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x47 - x14) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x17 - x14) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x47 - x17) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th149 t x14 x17 x47
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 ((hh).2).1) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause2485 (t x14 x17 x47 : ℝ) : (((x14 + ((-1) * x47)) ≤ (-1)) ∨ ((x17 + ((-1) * x47)) ≥ 0) ∨ (¬ (x14 ≤ x17)) ∨ (¬ (x17 ≤ x47)) ∨ (¬ ((x47 - x14) ≥ 1)) ∨ (¬ ((x17 - x14) ≤ (t - 1))) ∨ (¬ ((x47 - x17) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x14 + ((-1) * x47)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x17 + ((-1) * x47)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x14 ≤ x17) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x17 ≤ x47) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x47 - x14) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x17 - x14) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x47 - x17) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th149 t x14 x17 x47
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause2486 (t x14 x17 x47 : ℝ) : (((x14 + ((-1) * x47)) ≤ (-1)) ∨ ((x14 + ((-1) * x17)) ≥ 0) ∨ (¬ (x14 ≤ x17)) ∨ (¬ (x17 ≤ x47)) ∨ (¬ ((x47 - x14) ≥ 1)) ∨ (¬ ((x17 - x14) ≤ (t - 1))) ∨ (¬ ((x47 - x17) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x14 + ((-1) * x47)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x14 + ((-1) * x17)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x14 ≤ x17) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x17 ≤ x47) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x47 - x14) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x17 - x14) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x47 - x17) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th149 t x14 x17 x47
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause2487 (t x14 x17 x47 : ℝ) : (((x14 + ((-1) * x47)) ≥ 1) ∨ ((x14 + ((-1) * x47)) ≤ (-1)) ∨ (¬ (x14 ≤ x17)) ∨ (¬ (x17 ≤ x47)) ∨ (¬ ((x47 - x14) ≥ 1)) ∨ (¬ ((x17 - x14) ≤ (t - 1))) ∨ (¬ ((x47 - x17) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x14 + ((-1) * x47)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x14 + ((-1) * x47)) ≤ (-1)) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x14 ≤ x17) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x17 ≤ x47) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x47 - x14) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x17 - x14) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x47 - x17) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th149 t x14 x17 x47
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 (((hh).2).2).1) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause2489 (t x14 x17 x47 : ℝ) : (((x14 + ((-1) * x47)) ≤ (-1)) ∨ ((t + ((-1) * x17) + x47) ≥ 1) ∨ (¬ (x14 ≤ x17)) ∨ (¬ (x17 ≤ x47)) ∨ (¬ ((x47 - x14) ≥ 1)) ∨ (¬ ((x17 - x14) ≤ (t - 1))) ∨ (¬ ((x47 - x17) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x14 + ((-1) * x47)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + ((-1) * x17) + x47) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x14 ≤ x17) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x17 ≤ x47) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x47 - x14) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x17 - x14) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x47 - x17) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th149 t x14 x17 x47
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause2495 (t x14 x17 x47 : ℝ) : (((t + x17 + ((-1) * x47)) ≥ 1) ∨ ((x17 + ((-1) * x47)) ≥ 0) ∨ (¬ (x14 ≤ x17)) ∨ (¬ (x17 ≤ x47)) ∨ (¬ ((x47 - x14) ≥ 1)) ∨ (¬ ((x17 - x14) ≤ (t - 1))) ∨ (¬ ((x47 - x17) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((t + x17 + ((-1) * x47)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x17 + ((-1) * x47)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x14 ≤ x17) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x17 ≤ x47) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x47 - x14) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x17 - x14) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x47 - x17) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th149 t x14 x17 x47
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 (hh).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause2500 (t x14 x17 x47 : ℝ) : (((x14 + ((-1) * x17)) ≤ 0) ∨ ((x17 + ((-1) * x47)) ≥ 0) ∨ (¬ (x47 ≤ x17)) ∨ (¬ (x17 ≤ x14)) ∨ (¬ ((x14 - x47) ≥ 1)) ∨ (¬ ((x14 - x17) ≤ (t - 1))) ∨ (¬ ((x17 - x47) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x14 + ((-1) * x17)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x17 + ((-1) * x47)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x47 ≤ x17) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x17 ≤ x14) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x14 - x47) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x14 - x17) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x17 - x47) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th149 t x14 x17 x47
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause2502 (t x14 x17 x47 : ℝ) : (((x14 + ((-1) * x47)) ≥ 1) ∨ ((x14 + ((-1) * x17)) ≤ 0) ∨ (¬ (x47 ≤ x17)) ∨ (¬ (x17 ≤ x14)) ∨ (¬ ((x14 - x47) ≥ 1)) ∨ (¬ ((x14 - x17) ≤ (t - 1))) ∨ (¬ ((x17 - x47) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x14 + ((-1) * x47)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x14 + ((-1) * x17)) ≤ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x47 ≤ x17) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x17 ≤ x14) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x14 - x47) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x14 - x17) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x17 - x47) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th149 t x14 x17 x47
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 (hh).1) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause2506 (t x14 x17 x47 : ℝ) : (((x17 + ((-1) * x47)) ≤ 0) ∨ ((x14 + ((-1) * x17)) ≥ 0) ∨ (¬ (x47 ≤ x17)) ∨ (¬ (x17 ≤ x14)) ∨ (¬ ((x14 - x47) ≥ 1)) ∨ (¬ ((x14 - x17) ≤ (t - 1))) ∨ (¬ ((x17 - x47) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x17 + ((-1) * x47)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x14 + ((-1) * x17)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x47 ≤ x17) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x17 ≤ x14) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x14 - x47) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x14 - x17) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x17 - x47) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th149 t x14 x17 x47
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause2507 (t x14 x17 x47 : ℝ) : (((x14 + ((-1) * x47)) ≥ 1) ∨ ((x17 + ((-1) * x47)) ≤ 0) ∨ (¬ (x47 ≤ x17)) ∨ (¬ (x17 ≤ x14)) ∨ (¬ ((x14 - x47) ≥ 1)) ∨ (¬ ((x14 - x17) ≤ (t - 1))) ∨ (¬ ((x17 - x47) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x14 + ((-1) * x47)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x17 + ((-1) * x47)) ≤ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x47 ≤ x17) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x17 ≤ x14) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x14 - x47) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x14 - x17) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x17 - x47) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th149 t x14 x17 x47
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 ((hh).2).1) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause2510 (t x14 x17 x47 : ℝ) : (((x14 + ((-1) * x47)) ≤ (-1)) ∨ ((x17 + ((-1) * x47)) ≥ 0) ∨ (¬ (x47 ≤ x17)) ∨ (¬ (x17 ≤ x14)) ∨ (¬ ((x14 - x47) ≥ 1)) ∨ (¬ ((x14 - x17) ≤ (t - 1))) ∨ (¬ ((x17 - x47) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x14 + ((-1) * x47)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x17 + ((-1) * x47)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x47 ≤ x17) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x17 ≤ x14) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x14 - x47) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x14 - x17) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x17 - x47) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th149 t x14 x17 x47
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause2511 (t x14 x17 x47 : ℝ) : (((x14 + ((-1) * x47)) ≤ (-1)) ∨ ((x14 + ((-1) * x17)) ≥ 0) ∨ (¬ (x47 ≤ x17)) ∨ (¬ (x17 ≤ x14)) ∨ (¬ ((x14 - x47) ≥ 1)) ∨ (¬ ((x14 - x17) ≤ (t - 1))) ∨ (¬ ((x17 - x47) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x14 + ((-1) * x47)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x14 + ((-1) * x17)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x47 ≤ x17) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x17 ≤ x14) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x14 - x47) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x14 - x17) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x17 - x47) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th149 t x14 x17 x47
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause2512 (t x14 x17 x47 : ℝ) : (((x14 + ((-1) * x47)) ≥ 1) ∨ ((x14 + ((-1) * x47)) ≤ (-1)) ∨ (¬ (x47 ≤ x17)) ∨ (¬ (x17 ≤ x14)) ∨ (¬ ((x14 - x47) ≥ 1)) ∨ (¬ ((x14 - x17) ≤ (t - 1))) ∨ (¬ ((x17 - x47) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x14 + ((-1) * x47)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x14 + ((-1) * x47)) ≤ (-1)) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x47 ≤ x17) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x17 ≤ x14) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x14 - x47) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x14 - x17) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x17 - x47) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th149 t x14 x17 x47
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 (((hh).2).2).1) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause2514 (t x14 x17 x47 : ℝ) : (((x14 + ((-1) * x47)) ≤ (-1)) ∨ ((t + ((-1) * x17) + x47) ≥ 1) ∨ (¬ (x47 ≤ x17)) ∨ (¬ (x17 ≤ x14)) ∨ (¬ ((x14 - x47) ≥ 1)) ∨ (¬ ((x14 - x17) ≤ (t - 1))) ∨ (¬ ((x17 - x47) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x14 + ((-1) * x47)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + ((-1) * x17) + x47) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x47 ≤ x17) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x17 ≤ x14) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x14 - x47) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x14 - x17) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x17 - x47) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th149 t x14 x17 x47
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause2522 (t x14 x17 x47 : ℝ) : (((x14 + ((-1) * x47)) ≥ 1) ∨ ((t + x17 + ((-1) * x47)) ≥ 1) ∨ (¬ (x47 ≤ x17)) ∨ (¬ (x17 ≤ x14)) ∨ (¬ ((x14 - x47) ≥ 1)) ∨ (¬ ((x14 - x17) ≤ (t - 1))) ∨ (¬ ((x17 - x47) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x14 + ((-1) * x47)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((t + x17 + ((-1) * x47)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x47 ≤ x17) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x17 ≤ x14) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x14 - x47) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x14 - x17) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x17 - x47) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th149 t x14 x17 x47
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u1 ((((hh).2).2).2).2) (fun zz => ((fun hh => u0 (((hh).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause2575 (t x14 x17 x47 : ℝ) (h : (((x14 ≤ x17) ∧ (x17 ≤ x47) ∧ ((x47 - x14) ≥ 1) ∧ ((x17 - x14) ≤ (t - 1)) ∧ ((x47 - x17) ≤ (t - 1))) ∨ ((x47 ≤ x17) ∧ (x17 ≤ x14) ∧ ((x14 - x47) ≥ 1) ∧ ((x14 - x17) ≤ (t - 1)) ∧ ((x17 - x47) ≤ (t - 1))))) : ((x14 ≤ x17) ∨ (x47 ≤ x17)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x14 ≤ x17) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x47 ≤ x17) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause2576 (t x14 x17 x47 : ℝ) (h : (((x14 ≤ x17) ∧ (x17 ≤ x47) ∧ ((x47 - x14) ≥ 1) ∧ ((x17 - x14) ≤ (t - 1)) ∧ ((x47 - x17) ≤ (t - 1))) ∨ ((x47 ≤ x17) ∧ (x17 ≤ x14) ∧ ((x14 - x47) ≥ 1) ∧ ((x14 - x17) ≤ (t - 1)) ∧ ((x17 - x47) ≤ (t - 1))))) : ((x14 ≤ x17) ∨ (x17 ≤ x14)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x14 ≤ x17) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x17 ≤ x14) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause2577 (t x14 x17 x47 : ℝ) (h : (((x14 ≤ x17) ∧ (x17 ≤ x47) ∧ ((x47 - x14) ≥ 1) ∧ ((x17 - x14) ≤ (t - 1)) ∧ ((x47 - x17) ≤ (t - 1))) ∨ ((x47 ≤ x17) ∧ (x17 ≤ x14) ∧ ((x14 - x47) ≥ 1) ∧ ((x14 - x17) ≤ (t - 1)) ∧ ((x17 - x47) ≤ (t - 1))))) : ((x14 ≤ x17) ∨ ((x14 - x47) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x14 ≤ x17) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x14 - x47) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause2578 (t x14 x17 x47 : ℝ) (h : (((x14 ≤ x17) ∧ (x17 ≤ x47) ∧ ((x47 - x14) ≥ 1) ∧ ((x17 - x14) ≤ (t - 1)) ∧ ((x47 - x17) ≤ (t - 1))) ∨ ((x47 ≤ x17) ∧ (x17 ≤ x14) ∧ ((x14 - x47) ≥ 1) ∧ ((x14 - x17) ≤ (t - 1)) ∧ ((x17 - x47) ≤ (t - 1))))) : ((x14 ≤ x17) ∨ ((x14 - x17) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x14 ≤ x17) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x14 - x17) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause2579 (t x14 x17 x47 : ℝ) (h : (((x14 ≤ x17) ∧ (x17 ≤ x47) ∧ ((x47 - x14) ≥ 1) ∧ ((x17 - x14) ≤ (t - 1)) ∧ ((x47 - x17) ≤ (t - 1))) ∨ ((x47 ≤ x17) ∧ (x17 ≤ x14) ∧ ((x14 - x47) ≥ 1) ∧ ((x14 - x17) ≤ (t - 1)) ∧ ((x17 - x47) ≤ (t - 1))))) : ((x14 ≤ x17) ∨ ((x17 - x47) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x14 ≤ x17) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x17 - x47) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause2580 (t x14 x17 x47 : ℝ) (h : (((x14 ≤ x17) ∧ (x17 ≤ x47) ∧ ((x47 - x14) ≥ 1) ∧ ((x17 - x14) ≤ (t - 1)) ∧ ((x47 - x17) ≤ (t - 1))) ∨ ((x47 ≤ x17) ∧ (x17 ≤ x14) ∧ ((x14 - x47) ≥ 1) ∧ ((x14 - x17) ≤ (t - 1)) ∧ ((x17 - x47) ≤ (t - 1))))) : ((x17 ≤ x47) ∨ (x47 ≤ x17)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x17 ≤ x47) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x47 ≤ x17) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause2581 (t x14 x17 x47 : ℝ) (h : (((x14 ≤ x17) ∧ (x17 ≤ x47) ∧ ((x47 - x14) ≥ 1) ∧ ((x17 - x14) ≤ (t - 1)) ∧ ((x47 - x17) ≤ (t - 1))) ∨ ((x47 ≤ x17) ∧ (x17 ≤ x14) ∧ ((x14 - x47) ≥ 1) ∧ ((x14 - x17) ≤ (t - 1)) ∧ ((x17 - x47) ≤ (t - 1))))) : ((x17 ≤ x47) ∨ (x17 ≤ x14)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x17 ≤ x47) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x17 ≤ x14) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause2582 (t x14 x17 x47 : ℝ) (h : (((x14 ≤ x17) ∧ (x17 ≤ x47) ∧ ((x47 - x14) ≥ 1) ∧ ((x17 - x14) ≤ (t - 1)) ∧ ((x47 - x17) ≤ (t - 1))) ∨ ((x47 ≤ x17) ∧ (x17 ≤ x14) ∧ ((x14 - x47) ≥ 1) ∧ ((x14 - x17) ≤ (t - 1)) ∧ ((x17 - x47) ≤ (t - 1))))) : ((x17 ≤ x47) ∨ ((x14 - x47) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x17 ≤ x47) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x14 - x47) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause2583 (t x14 x17 x47 : ℝ) (h : (((x14 ≤ x17) ∧ (x17 ≤ x47) ∧ ((x47 - x14) ≥ 1) ∧ ((x17 - x14) ≤ (t - 1)) ∧ ((x47 - x17) ≤ (t - 1))) ∨ ((x47 ≤ x17) ∧ (x17 ≤ x14) ∧ ((x14 - x47) ≥ 1) ∧ ((x14 - x17) ≤ (t - 1)) ∧ ((x17 - x47) ≤ (t - 1))))) : ((x17 ≤ x47) ∨ ((x14 - x17) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x17 ≤ x47) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x14 - x17) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause2584 (t x14 x17 x47 : ℝ) (h : (((x14 ≤ x17) ∧ (x17 ≤ x47) ∧ ((x47 - x14) ≥ 1) ∧ ((x17 - x14) ≤ (t - 1)) ∧ ((x47 - x17) ≤ (t - 1))) ∨ ((x47 ≤ x17) ∧ (x17 ≤ x14) ∧ ((x14 - x47) ≥ 1) ∧ ((x14 - x17) ≤ (t - 1)) ∧ ((x17 - x47) ≤ (t - 1))))) : ((x17 ≤ x47) ∨ ((x17 - x47) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ (x17 ≤ x47) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x17 - x47) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause2585 (t x14 x17 x47 : ℝ) (h : (((x14 ≤ x17) ∧ (x17 ≤ x47) ∧ ((x47 - x14) ≥ 1) ∧ ((x17 - x14) ≤ (t - 1)) ∧ ((x47 - x17) ≤ (t - 1))) ∨ ((x47 ≤ x17) ∧ (x17 ≤ x14) ∧ ((x14 - x47) ≥ 1) ∧ ((x14 - x17) ≤ (t - 1)) ∧ ((x17 - x47) ≤ (t - 1))))) : (((x47 - x14) ≥ 1) ∨ (x47 ≤ x17)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x47 - x14) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x47 ≤ x17) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause2586 (t x14 x17 x47 : ℝ) (h : (((x14 ≤ x17) ∧ (x17 ≤ x47) ∧ ((x47 - x14) ≥ 1) ∧ ((x17 - x14) ≤ (t - 1)) ∧ ((x47 - x17) ≤ (t - 1))) ∨ ((x47 ≤ x17) ∧ (x17 ≤ x14) ∧ ((x14 - x47) ≥ 1) ∧ ((x14 - x17) ≤ (t - 1)) ∧ ((x17 - x47) ≤ (t - 1))))) : (((x47 - x14) ≥ 1) ∨ (x17 ≤ x14)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x47 - x14) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x17 ≤ x14) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause2587 (t x14 x17 x47 : ℝ) (h : (((x14 ≤ x17) ∧ (x17 ≤ x47) ∧ ((x47 - x14) ≥ 1) ∧ ((x17 - x14) ≤ (t - 1)) ∧ ((x47 - x17) ≤ (t - 1))) ∨ ((x47 ≤ x17) ∧ (x17 ≤ x14) ∧ ((x14 - x47) ≥ 1) ∧ ((x14 - x17) ≤ (t - 1)) ∧ ((x17 - x47) ≤ (t - 1))))) : (((x47 - x14) ≥ 1) ∨ ((x14 - x47) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x47 - x14) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x14 - x47) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause2588 (t x14 x17 x47 : ℝ) (h : (((x14 ≤ x17) ∧ (x17 ≤ x47) ∧ ((x47 - x14) ≥ 1) ∧ ((x17 - x14) ≤ (t - 1)) ∧ ((x47 - x17) ≤ (t - 1))) ∨ ((x47 ≤ x17) ∧ (x17 ≤ x14) ∧ ((x14 - x47) ≥ 1) ∧ ((x14 - x17) ≤ (t - 1)) ∧ ((x17 - x47) ≤ (t - 1))))) : (((x47 - x14) ≥ 1) ∨ ((x14 - x17) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x47 - x14) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x14 - x17) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause2589 (t x14 x17 x47 : ℝ) (h : (((x14 ≤ x17) ∧ (x17 ≤ x47) ∧ ((x47 - x14) ≥ 1) ∧ ((x17 - x14) ≤ (t - 1)) ∧ ((x47 - x17) ≤ (t - 1))) ∨ ((x47 ≤ x17) ∧ (x17 ≤ x14) ∧ ((x14 - x47) ≥ 1) ∧ ((x14 - x17) ≤ (t - 1)) ∧ ((x17 - x47) ≤ (t - 1))))) : (((x47 - x14) ≥ 1) ∨ ((x17 - x47) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x47 - x14) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x17 - x47) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause2590 (t x14 x17 x47 : ℝ) (h : (((x14 ≤ x17) ∧ (x17 ≤ x47) ∧ ((x47 - x14) ≥ 1) ∧ ((x17 - x14) ≤ (t - 1)) ∧ ((x47 - x17) ≤ (t - 1))) ∨ ((x47 ≤ x17) ∧ (x17 ≤ x14) ∧ ((x14 - x47) ≥ 1) ∧ ((x14 - x17) ≤ (t - 1)) ∧ ((x17 - x47) ≤ (t - 1))))) : (((x17 - x14) ≤ (t - 1)) ∨ (x47 ≤ x17)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x17 - x14) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x47 ≤ x17) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause2591 (t x14 x17 x47 : ℝ) (h : (((x14 ≤ x17) ∧ (x17 ≤ x47) ∧ ((x47 - x14) ≥ 1) ∧ ((x17 - x14) ≤ (t - 1)) ∧ ((x47 - x17) ≤ (t - 1))) ∨ ((x47 ≤ x17) ∧ (x17 ≤ x14) ∧ ((x14 - x47) ≥ 1) ∧ ((x14 - x17) ≤ (t - 1)) ∧ ((x17 - x47) ≤ (t - 1))))) : (((x17 - x14) ≤ (t - 1)) ∨ (x17 ≤ x14)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x17 - x14) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x17 ≤ x14) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause2592 (t x14 x17 x47 : ℝ) (h : (((x14 ≤ x17) ∧ (x17 ≤ x47) ∧ ((x47 - x14) ≥ 1) ∧ ((x17 - x14) ≤ (t - 1)) ∧ ((x47 - x17) ≤ (t - 1))) ∨ ((x47 ≤ x17) ∧ (x17 ≤ x14) ∧ ((x14 - x47) ≥ 1) ∧ ((x14 - x17) ≤ (t - 1)) ∧ ((x17 - x47) ≤ (t - 1))))) : (((x17 - x14) ≤ (t - 1)) ∨ ((x14 - x47) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x17 - x14) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x14 - x47) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause2593 (t x14 x17 x47 : ℝ) (h : (((x14 ≤ x17) ∧ (x17 ≤ x47) ∧ ((x47 - x14) ≥ 1) ∧ ((x17 - x14) ≤ (t - 1)) ∧ ((x47 - x17) ≤ (t - 1))) ∨ ((x47 ≤ x17) ∧ (x17 ≤ x14) ∧ ((x14 - x47) ≥ 1) ∧ ((x14 - x17) ≤ (t - 1)) ∧ ((x17 - x47) ≤ (t - 1))))) : (((x17 - x14) ≤ (t - 1)) ∨ ((x14 - x17) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x17 - x14) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x14 - x17) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause2594 (t x14 x17 x47 : ℝ) (h : (((x14 ≤ x17) ∧ (x17 ≤ x47) ∧ ((x47 - x14) ≥ 1) ∧ ((x17 - x14) ≤ (t - 1)) ∧ ((x47 - x17) ≤ (t - 1))) ∨ ((x47 ≤ x17) ∧ (x17 ≤ x14) ∧ ((x14 - x47) ≥ 1) ∧ ((x14 - x17) ≤ (t - 1)) ∧ ((x17 - x47) ≤ (t - 1))))) : (((x17 - x14) ≤ (t - 1)) ∨ ((x17 - x47) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x17 - x14) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x17 - x47) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).1) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause2595 (t x14 x17 x47 : ℝ) (h : (((x14 ≤ x17) ∧ (x17 ≤ x47) ∧ ((x47 - x14) ≥ 1) ∧ ((x17 - x14) ≤ (t - 1)) ∧ ((x47 - x17) ≤ (t - 1))) ∨ ((x47 ≤ x17) ∧ (x17 ≤ x14) ∧ ((x14 - x47) ≥ 1) ∧ ((x14 - x17) ≤ (t - 1)) ∧ ((x17 - x47) ≤ (t - 1))))) : (((x47 - x17) ≤ (t - 1)) ∨ (x47 ≤ x17)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x47 - x17) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x47 ≤ x17) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 (hh).1) zz)))) h

theorem clause2596 (t x14 x17 x47 : ℝ) (h : (((x14 ≤ x17) ∧ (x17 ≤ x47) ∧ ((x47 - x14) ≥ 1) ∧ ((x17 - x14) ≤ (t - 1)) ∧ ((x47 - x17) ≤ (t - 1))) ∨ ((x47 ≤ x17) ∧ (x17 ≤ x14) ∧ ((x14 - x47) ≥ 1) ∧ ((x14 - x17) ≤ (t - 1)) ∧ ((x17 - x47) ≤ (t - 1))))) : (((x47 - x17) ≤ (t - 1)) ∨ (x17 ≤ x14)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x47 - x17) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ (x17 ≤ x14) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) h

theorem clause2597 (t x14 x17 x47 : ℝ) (h : (((x14 ≤ x17) ∧ (x17 ≤ x47) ∧ ((x47 - x14) ≥ 1) ∧ ((x17 - x14) ≤ (t - 1)) ∧ ((x47 - x17) ≤ (t - 1))) ∨ ((x47 ≤ x17) ∧ (x17 ≤ x14) ∧ ((x14 - x47) ≥ 1) ∧ ((x14 - x17) ≤ (t - 1)) ∧ ((x17 - x47) ≤ (t - 1))))) : (((x47 - x17) ≤ (t - 1)) ∨ ((x14 - x47) ≥ 1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x47 - x17) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x14 - x47) ≥ 1) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) h

theorem clause2598 (t x14 x17 x47 : ℝ) (h : (((x14 ≤ x17) ∧ (x17 ≤ x47) ∧ ((x47 - x14) ≥ 1) ∧ ((x17 - x14) ≤ (t - 1)) ∧ ((x47 - x17) ≤ (t - 1))) ∨ ((x47 ≤ x17) ∧ (x17 ≤ x14) ∧ ((x14 - x47) ≥ 1) ∧ ((x14 - x17) ≤ (t - 1)) ∧ ((x17 - x47) ≤ (t - 1))))) : (((x47 - x17) ≤ (t - 1)) ∨ ((x14 - x17) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x47 - x17) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x14 - x17) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 ((((hh).2).2).2).1) zz)))) h

theorem clause2599 (t x14 x17 x47 : ℝ) (h : (((x14 ≤ x17) ∧ (x17 ≤ x47) ∧ ((x47 - x14) ≥ 1) ∧ ((x17 - x14) ≤ (t - 1)) ∧ ((x47 - x17) ≤ (t - 1))) ∨ ((x47 ≤ x17) ∧ (x17 ≤ x14) ∧ ((x14 - x47) ≥ 1) ∧ ((x14 - x17) ≤ (t - 1)) ∧ ((x17 - x47) ≤ (t - 1))))) : (((x47 - x17) ≤ (t - 1)) ∨ ((x17 - x47) ≤ (t - 1))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x47 - x17) ≤ (t - 1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x17 - x47) ≤ (t - 1)) := fun hh => hn (Or.inr hh)
  exact (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 ((((hh).2).2).2).2) zz)))) h

theorem clause2600 (t x03 x06 x34 x36 x67 : ℝ) : ((¬ ((x03 + ((-1) * x34)) ≤ (-1))) ∨ (t ≥ (7 / 2)) ∨ (¬ ((t + ((-1) * x34) + x36) ≥ 1)) ∨ (¬ ((x06 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((x36 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((x03 + ((-1) * x06)) ≥ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x03 + ((-1) * x34)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ¬ (t ≥ (7 / 2)) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : ((t + ((-1) * x34) + x36) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : ((x06 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x36 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x03 + ((-1) * x06)) ≥ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))
  have h := NineTheoryTrial.th151 t x03 x06 x34 x36 x67
  exact (fun hh => (fun hh => hh) (hh (And.intro u1 (And.intro u2 (And.intro u4 (And.intro u5 (And.intro u3 u0))))))) h

theorem clause2601 (x06 x36 x67 : ℝ) : ((¬ ((x06 + ((-1) * x67)) ≥ 1)) ∨ (¬ ((x36 + ((-1) * x67)) ≤ (-1))) ∨ (¬ ((x06 + ((-1) * x36)) ≤ 0))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ((x06 + ((-1) * x67)) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inl hh)
  have u1 : ((x36 + ((-1) * x67)) ≤ (-1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inl hh))
  have u2 : ((x06 + ((-1) * x36)) ≤ 0) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr hh))
  have h := NineTheoryTrial.th152 x06 x36 x67
  exact (fun hh => (fun hh => hh u2) (hh (And.intro u1 u0))) h

theorem clause2602 (t x03 x06 x36 : ℝ) : (((x03 + ((-1) * x06)) ≤ 0) ∨ ((x06 + ((-1) * x36)) ≥ 0) ∨ (¬ (x03 ≤ x06)) ∨ (¬ (x06 ≤ x36)) ∨ (¬ ((x36 - x03) ≥ 1)) ∨ (¬ ((x06 - x03) ≤ (t - 1))) ∨ (¬ ((x36 - x06) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x03 + ((-1) * x06)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x06 + ((-1) * x36)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x03 ≤ x06) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x06 ≤ x36) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x36 - x03) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x06 - x03) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x36 - x06) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th154 t x03 x06 x36
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause2604 (t x03 x06 x36 : ℝ) : (((x03 + ((-1) * x06)) ≤ 0) ∨ ((x03 + ((-1) * x36)) ≥ 1) ∨ (¬ (x03 ≤ x06)) ∨ (¬ (x06 ≤ x36)) ∨ (¬ ((x36 - x03) ≥ 1)) ∨ (¬ ((x06 - x03) ≤ (t - 1))) ∨ (¬ ((x36 - x06) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x03 + ((-1) * x06)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x03 + ((-1) * x36)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x03 ≤ x06) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x06 ≤ x36) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x36 - x03) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x06 - x03) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x36 - x06) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th154 t x03 x06 x36
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause2609 (t x03 x06 x36 : ℝ) : (((x06 + ((-1) * x36)) ≤ 0) ∨ ((x03 + ((-1) * x36)) ≥ 1) ∨ (¬ (x03 ≤ x06)) ∨ (¬ (x06 ≤ x36)) ∨ (¬ ((x36 - x03) ≥ 1)) ∨ (¬ ((x06 - x03) ≤ (t - 1))) ∨ (¬ ((x36 - x06) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x06 + ((-1) * x36)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x03 + ((-1) * x36)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x03 ≤ x06) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x06 ≤ x36) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x36 - x03) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x06 - x03) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x36 - x06) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th154 t x03 x06 x36
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause2612 (t x03 x06 x36 : ℝ) : (((x03 + ((-1) * x36)) ≤ (-1)) ∨ ((x06 + ((-1) * x36)) ≥ 0) ∨ (¬ (x03 ≤ x06)) ∨ (¬ (x06 ≤ x36)) ∨ (¬ ((x36 - x03) ≥ 1)) ∨ (¬ ((x06 - x03) ≤ (t - 1))) ∨ (¬ ((x36 - x06) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x03 + ((-1) * x36)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x06 + ((-1) * x36)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x03 ≤ x06) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x06 ≤ x36) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x36 - x03) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x06 - x03) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x36 - x06) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th154 t x03 x06 x36
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause2613 (t x03 x06 x36 : ℝ) : (((x03 + ((-1) * x36)) ≤ (-1)) ∨ ((x03 + ((-1) * x06)) ≥ 0) ∨ (¬ (x03 ≤ x06)) ∨ (¬ (x06 ≤ x36)) ∨ (¬ ((x36 - x03) ≥ 1)) ∨ (¬ ((x06 - x03) ≤ (t - 1))) ∨ (¬ ((x36 - x06) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x03 + ((-1) * x36)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x03 + ((-1) * x06)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x03 ≤ x06) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x06 ≤ x36) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x36 - x03) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x06 - x03) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x36 - x06) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th154 t x03 x06 x36
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause2614 (t x03 x06 x36 : ℝ) : (((x03 + ((-1) * x36)) ≤ (-1)) ∨ ((x03 + ((-1) * x36)) ≥ 1) ∨ (¬ (x03 ≤ x06)) ∨ (¬ (x06 ≤ x36)) ∨ (¬ ((x36 - x03) ≥ 1)) ∨ (¬ ((x06 - x03) ≤ (t - 1))) ∨ (¬ ((x36 - x06) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x03 + ((-1) * x36)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x03 + ((-1) * x36)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x03 ≤ x06) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x06 ≤ x36) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x36 - x03) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x06 - x03) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x36 - x06) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th154 t x03 x06 x36
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause2624 (t x03 x06 x36 : ℝ) : (((t + x06 + ((-1) * x36)) ≥ 1) ∨ ((x03 + ((-1) * x36)) ≥ 1) ∨ (¬ (x03 ≤ x06)) ∨ (¬ (x06 ≤ x36)) ∨ (¬ ((x36 - x03) ≥ 1)) ∨ (¬ ((x06 - x03) ≤ (t - 1))) ∨ (¬ ((x36 - x06) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((t + x06 + ((-1) * x36)) ≥ 1) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x03 + ((-1) * x36)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x03 ≤ x06) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x06 ≤ x36) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x36 - x03) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x06 - x03) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x36 - x06) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th154 t x03 x06 x36
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 ((((hh).2).2).2).2) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) (hh.mp (Or.inl (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause2627 (t x03 x06 x36 : ℝ) : (((x03 + ((-1) * x06)) ≤ 0) ∨ ((x06 + ((-1) * x36)) ≥ 0) ∨ (¬ (x36 ≤ x06)) ∨ (¬ (x06 ≤ x03)) ∨ (¬ ((x03 - x36) ≥ 1)) ∨ (¬ ((x03 - x06) ≤ (t - 1))) ∨ (¬ ((x06 - x36) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x03 + ((-1) * x06)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x06 + ((-1) * x36)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x36 ≤ x06) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x06 ≤ x03) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x03 - x36) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x03 - x06) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x06 - x36) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th154 t x03 x06 x36
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause2629 (t x03 x06 x36 : ℝ) : (((x03 + ((-1) * x06)) ≤ 0) ∨ ((x03 + ((-1) * x36)) ≥ 1) ∨ (¬ (x36 ≤ x06)) ∨ (¬ (x06 ≤ x03)) ∨ (¬ ((x03 - x36) ≥ 1)) ∨ (¬ ((x03 - x06) ≤ (t - 1))) ∨ (¬ ((x06 - x36) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x03 + ((-1) * x06)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x03 + ((-1) * x36)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x36 ≤ x06) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x06 ≤ x03) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x03 - x36) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x03 - x06) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x06 - x36) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th154 t x03 x06 x36
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (hh).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause2634 (t x03 x06 x36 : ℝ) : (((x06 + ((-1) * x36)) ≤ 0) ∨ ((x03 + ((-1) * x36)) ≥ 1) ∨ (¬ (x36 ≤ x06)) ∨ (¬ (x06 ≤ x03)) ∨ (¬ ((x03 - x36) ≥ 1)) ∨ (¬ ((x03 - x06) ≤ (t - 1))) ∨ (¬ ((x06 - x36) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x06 + ((-1) * x36)) ≤ 0) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x03 + ((-1) * x36)) ≥ 1) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x36 ≤ x06) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x06 ≤ x03) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x03 - x36) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x03 - x06) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x06 - x36) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th154 t x03 x06 x36
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 ((hh).2).1) (fun zz => ((fun hh => u1 (((hh).2).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause2637 (t x03 x06 x36 : ℝ) : (((x03 + ((-1) * x36)) ≤ (-1)) ∨ ((x06 + ((-1) * x36)) ≥ 0) ∨ (¬ (x36 ≤ x06)) ∨ (¬ (x06 ≤ x03)) ∨ (¬ ((x03 - x36) ≥ 1)) ∨ (¬ ((x03 - x06) ≤ (t - 1))) ∨ (¬ ((x06 - x36) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x03 + ((-1) * x36)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x06 + ((-1) * x36)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x36 ≤ x06) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x06 ≤ x03) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x03 - x36) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x03 - x06) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x06 - x36) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th154 t x03 x06 x36
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 (hh).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

theorem clause2638 (t x03 x06 x36 : ℝ) : (((x03 + ((-1) * x36)) ≤ (-1)) ∨ ((x03 + ((-1) * x06)) ≥ 0) ∨ (¬ (x36 ≤ x06)) ∨ (¬ (x06 ≤ x03)) ∨ (¬ ((x03 - x36) ≥ 1)) ∨ (¬ ((x03 - x06) ≤ (t - 1))) ∨ (¬ ((x06 - x36) ≤ (t - 1)))) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : ¬ ((x03 + ((-1) * x36)) ≤ (-1)) := fun hh => hn (Or.inl hh)
  have u1 : ¬ ((x03 + ((-1) * x06)) ≥ 0) := fun hh => hn (Or.inr (Or.inl hh))
  have u2 : (x36 ≤ x06) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inl hh)))
  have u3 : (x06 ≤ x03) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hh))))
  have u4 : ((x03 - x36) ≥ 1) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh)))))
  have u5 : ((x03 - x06) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))))
  have u6 : ((x06 - x36) ≤ (t - 1)) := by
    apply Classical.byContradiction
    intro hh
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh))))))
  have h := NineTheoryTrial.th154 t x03 x06 x36
  exact (fun hh => (fun hh => (Or.elim hh (fun hh => u0 (((hh).2).2).1) (fun zz => ((fun hh => u1 ((hh).2).1) zz)))) (hh.mp (Or.inr (And.intro u2 (And.intro u3 (And.intro u4 (And.intro u5 u6))))))) h

#print axioms clause2638
end NineCNFDirectTrial
