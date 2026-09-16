import JSP690.Witness

/-!
The witness has no proper colouring with fewer than three colours.
The finite computation is kernel checked with ordinary `decide`.
-/

namespace JSP690

private def binaryColoring (b0 b1 b2 b3 b4 b5 b6 b7 b8 : Bool)
    (v : Vertex 9) : Bool :=
  match v.val with
  | 0 => b0
  | 1 => b1
  | 2 => b2
  | 3 => b3
  | 4 => b4
  | 5 => b5
  | 6 => b6
  | 7 => b7
  | _ => b8

-- Normalize each fixed edge once, before enumerating the 512 colour assignments.
-- These equalities are independently checked by the kernel.
private theorem vertices_7 : edgeVertices (7 : Edge 9) = [0, 1, 2] := by decide

private theorem vertices_259 : edgeVertices (259 : Edge 9) = [0, 1, 8] := by decide

private theorem vertices_133 : edgeVertices (133 : Edge 9) = [0, 2, 7] := by decide

private theorem vertices_41 : edgeVertices (41 : Edge 9) = [0, 3, 5] := by decide

private theorem vertices_137 : edgeVertices (137 : Edge 9) = [0, 3, 7] := by decide

private theorem vertices_265 : edgeVertices (265 : Edge 9) = [0, 3, 8] := by decide

private theorem vertices_81 : edgeVertices (81 : Edge 9) = [0, 4, 6] := by decide

private theorem vertices_145 : edgeVertices (145 : Edge 9) = [0, 4, 7] := by decide

private theorem vertices_273 : edgeVertices (273 : Edge 9) = [0, 4, 8] := by decide

private theorem vertices_97 : edgeVertices (97 : Edge 9) = [0, 5, 6] := by decide

private theorem vertices_38 : edgeVertices (38 : Edge 9) = [1, 2, 5] := by decide

private theorem vertices_70 : edgeVertices (70 : Edge 9) = [1, 2, 6] := by decide

private theorem vertices_266 : edgeVertices (266 : Edge 9) = [1, 3, 8] := by decide

private theorem vertices_274 : edgeVertices (274 : Edge 9) = [1, 4, 8] := by decide

private theorem vertices_98 : edgeVertices (98 : Edge 9) = [1, 5, 6] := by decide

private theorem vertices_140 : edgeVertices (140 : Edge 9) = [2, 3, 7] := by decide

private theorem vertices_148 : edgeVertices (148 : Edge 9) = [2, 4, 7] := by decide

private theorem vertices_100 : edgeVertices (100 : Edge 9) = [2, 5, 6] := by decide

private theorem vertices_168 : edgeVertices (168 : Edge 9) = [3, 5, 7] := by decide

private theorem vertices_296 : edgeVertices (296 : Edge 9) = [3, 5, 8] := by decide

private theorem vertices_208 : edgeVertices (208 : Edge 9) = [4, 6, 7] := by decide

private theorem vertices_336 : edgeVertices (336 : Edge 9) = [4, 6, 8] := by decide

private theorem exists_mem_cons_and {α : Type} (a : α) (l : List α) (p : α → Prop) :
    (∃ u, u ∈ a :: l ∧ p u) ↔ p a ∨ ∃ u, u ∈ l ∧ p u := by
  simp

private theorem exists_mem_nil_and {α : Type} (p : α → Prop) :
    (∃ u, u ∈ ([] : List α) ∧ p u) ↔ False := by
  simp

set_option synthInstance.maxSize 100000 in
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
private theorem no_binary_tuple : ∀ b0 b1 b2 b3 b4 b5 b6 b7 b8 : Bool,
    ¬ ProperColoring witness (binaryColoring b0 b1 b2 b3 b4 b5 b6 b7 b8) := by
  simp only [ProperColoring, witness, List.forall_mem_cons, List.mem_nil_iff, false_implies, forall_const, and_true]
  simp only [vertices_7, vertices_259, vertices_133, vertices_41, vertices_137, vertices_265, vertices_81, vertices_145, vertices_273, vertices_97, vertices_38, vertices_70, vertices_266, vertices_274, vertices_98, vertices_140, vertices_148, vertices_100, vertices_168, vertices_296, vertices_208, vertices_336, exists_mem_cons_and, exists_mem_nil_and, or_false]
  decide

private theorem binaryColoring_roundtrip (c : Vertex 9 → Bool) :
    binaryColoring (c 0) (c 1) (c 2) (c 3) (c 4) (c 5) (c 6) (c 7) (c 8) = c := by
  funext v
  rcases v with ⟨n, hn⟩
  match n with
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl
  | 3 => rfl
  | 4 => rfl
  | 5 => rfl
  | 6 => rfl
  | 7 => rfl
  | 8 => rfl
  | n + 9 => omega

theorem not_bool_colorable : ∀ c : Vertex 9 → Bool, ¬ ProperColoring witness c := by
  intro c hc
  apply no_binary_tuple (c 0) (c 1) (c 2) (c 3) (c 4) (c 5) (c 6) (c 7) (c 8)
  simpa only [binaryColoring_roundtrip] using hc

private def smallColorToBool {j : Nat} (a : Fin j) : Bool :=
  decide (a.val = 0)

private theorem smallColorToBool_injective {j : Nat} (hj : j < 3)
    {a b : Fin j} (h : smallColorToBool a = smallColorToBool b) : a = b := by
  apply Fin.ext
  have hal := a.isLt
  have hbl := b.isLt
  by_cases ha : a.val = 0
  · by_cases hb : b.val = 0
    · omega
    · simp [smallColorToBool, ha, hb] at h
  · by_cases hb : b.val = 0
    · simp [smallColorToBool, ha, hb] at h
    · omega

theorem not_colorable_of_lt_three : ∀ j : Nat, j < 3 → ¬ Colorable witness j := by
  intro j hj h
  obtain ⟨c, hc⟩ := h
  apply not_bool_colorable (fun v => smallColorToBool (c v))
  intro e he
  obtain ⟨u, hu, v, hv, hne⟩ := hc e he
  refine ⟨u, hu, v, hv, ?_⟩
  intro hEq
  exact hne (smallColorToBool_injective hj hEq)

end JSP690
