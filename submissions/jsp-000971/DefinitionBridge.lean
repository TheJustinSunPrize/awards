import Counting
import ErdosProblems.Erdos1165.Basic

namespace JSP000971.Bridge
open Finset

 theorem localTime_eq (s : Erdos1165.WalkPath) (n : ℕ) (x : ℤ × ℤ) :
    Erdos1165.localTime s n x = JSP000971.visits s n x := by
  unfold Erdos1165.localTime Erdos1165.localTimePrefix Erdos1165.pathPrefix JSP000971.visits
  apply Finset.card_bij (fun (i : Fin (n + 1)) _ => i.val)
  · intro i hi
    exact mem_filter.mpr ⟨mem_range.mpr i.isLt, (mem_filter.mp hi).2⟩
  · intro i _ j _ hij
    exact Fin.ext hij
  · intro j hj
    obtain ⟨hj, hx⟩ := mem_filter.mp hj
    exact ⟨⟨j, mem_range.mp hj⟩, mem_filter.mpr ⟨mem_univ _, hx⟩, rfl⟩

 theorem visited_eq (s : Erdos1165.WalkPath) (n : ℕ) :
    Erdos1165.visitedSites s n = JSP000971.visited s n := by
  ext x
  simp only [Erdos1165.visitedSites, Erdos1165.visitedPrefix, Erdos1165.pathPrefix,
    JSP000971.visited, mem_image, mem_univ, true_and, mem_range]
  constructor
  · rintro ⟨j, hj⟩
    exact ⟨j, j.isLt, hj⟩
  · rintro ⟨j, hj, hx⟩
    exact ⟨⟨j, hj⟩, hx⟩

 theorem maximum_eq (s : Erdos1165.WalkPath) (n : ℕ) :
    Erdos1165.maxLocalTime s n = JSP000971.maximum s n := by
  change (Erdos1165.visitedSites s n).sup (Erdos1165.localTime s n) = _
  have hf : Erdos1165.localTime s n = JSP000971.visits s n := funext (localTime_eq s n)
  rw [visited_eq, hf]
  rfl

 theorem favorites_eq (s : Erdos1165.WalkPath) (n : ℕ) :
    Erdos1165.favoriteSites s n = JSP000971.favorites s n := by
  change (Erdos1165.visitedSites s n).filter
    (fun x => Erdos1165.localTime s n x = Erdos1165.maxLocalTime s n) = _
  simp_rw [visited_eq, localTime_eq, maximum_eq]
  rfl

 theorem favoriteCount_eq (s : Erdos1165.WalkPath) (n : ℕ) :
    Erdos1165.favoriteCount s n = (JSP000971.favorites s n).card := by
  unfold Erdos1165.favoriteCount
  rw [favorites_eq]

#print axioms favoriteCount_eq
end JSP000971.Bridge
