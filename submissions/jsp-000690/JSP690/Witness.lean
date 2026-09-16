import JSP690.Definitions

/-! The 9-vertex, 22-edge example in Ruiliang Li, arXiv:2512.24850v1,
Section 4, equation (5). Paper vertex i corresponds to Lean vertex i - 1.
Each integer encodes the characteristic bit vector of an unordered edge. -/

namespace JSP690

def witness : Hypergraph 9 :=
  [
    7, -- {1, 2, 3}
    259, -- {1, 2, 9}
    133, -- {1, 3, 8}
    41, -- {1, 4, 6}
    137, -- {1, 4, 8}
    265, -- {1, 4, 9}
    81, -- {1, 5, 7}
    145, -- {1, 5, 8}
    273, -- {1, 5, 9}
    97, -- {1, 6, 7}
    38, -- {2, 3, 6}
    70, -- {2, 3, 7}
    266, -- {2, 4, 9}
    274, -- {2, 5, 9}
    98, -- {2, 6, 7}
    140, -- {3, 4, 8}
    148, -- {3, 5, 8}
    100, -- {3, 6, 7}
    168, -- {4, 6, 8}
    296, -- {4, 6, 9}
    208, -- {5, 7, 8}
    336 -- {5, 7, 9}
  ]

/-- Convert a subset of vertices to its characteristic two-colouring. -/
def maskColor (mask : BitVec 9) (v : Vertex 9) : Fin 2 :=
  if mask.getLsbD v.val then 1 else 0

def threeColor (v : Vertex 9) : Fin 3 :=
  if v.val = 0 then 2 else if v.val < 5 then 0 else 1

/-- Explicit certificate for deleting each edge; unused inputs use colour zero. -/
def edgeDeletionMask (e : Edge 9) : BitVec 9 :=
  match e.toNat with
  | 7 => 480
  | 259 => 92
  | 133 => 90
  | 41 => 452
  | 137 => 308
  | 265 => 178
  | 81 => 420
  | 145 => 332
  | 273 => 202
  | 97 => 30
  | 38 => 62
  | 70 => 94
  | 266 => 458
  | 274 => 434
  | 98 => 482
  | 140 => 460
  | 148 => 436
  | 100 => 484
  | 168 => 186
  | 296 => 316
  | 208 => 218
  | 336 => 348
  | _ => 0

def edgeDeletionColor (e : Edge 9) : Vertex 9 → Fin 2 :=
  maskColor (edgeDeletionMask e)

def vertexDeletionMask (v : Vertex 9) : BitVec 9 :=
  match v.val with
  | 0 => 480
  | 1 => 480
  | 2 => 480
  | 3 => 452
  | 4 => 420
  | 5 => 452
  | 6 => 420
  | 7 => 308
  | 8 => 92
  | _ => 0

def vertexDeletionColor (v : Vertex 9) : Vertex 9 → Fin 2 :=
  maskColor (vertexDeletionMask v)

end JSP690
