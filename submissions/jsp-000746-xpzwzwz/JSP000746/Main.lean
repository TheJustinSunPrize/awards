import JSP000746.Basic
import JSP000746.Resolution

set_option maxRecDepth 10000
set_option maxHeartbeats 0

namespace JSP000746

/-- The fixed DIMACS numbering of the 153 potential edges on `[1,18]`. -/
def edgeProp (G : SimpleGraph ℕ) (i : ℕ) : Prop :=
  match i with
  | 1 => G.Adj 1 2
  | 2 => G.Adj 1 3
  | 3 => G.Adj 1 4
  | 4 => G.Adj 1 5
  | 5 => G.Adj 1 6
  | 6 => G.Adj 1 7
  | 7 => G.Adj 1 8
  | 8 => G.Adj 1 9
  | 9 => G.Adj 1 10
  | 10 => G.Adj 1 11
  | 11 => G.Adj 1 12
  | 12 => G.Adj 1 13
  | 13 => G.Adj 1 14
  | 14 => G.Adj 1 15
  | 15 => G.Adj 1 16
  | 16 => G.Adj 1 17
  | 17 => G.Adj 1 18
  | 18 => G.Adj 2 3
  | 19 => G.Adj 2 4
  | 20 => G.Adj 2 5
  | 21 => G.Adj 2 6
  | 22 => G.Adj 2 7
  | 23 => G.Adj 2 8
  | 24 => G.Adj 2 9
  | 25 => G.Adj 2 10
  | 26 => G.Adj 2 11
  | 27 => G.Adj 2 12
  | 28 => G.Adj 2 13
  | 29 => G.Adj 2 14
  | 30 => G.Adj 2 15
  | 31 => G.Adj 2 16
  | 32 => G.Adj 2 17
  | 33 => G.Adj 2 18
  | 34 => G.Adj 3 4
  | 35 => G.Adj 3 5
  | 36 => G.Adj 3 6
  | 37 => G.Adj 3 7
  | 38 => G.Adj 3 8
  | 39 => G.Adj 3 9
  | 40 => G.Adj 3 10
  | 41 => G.Adj 3 11
  | 42 => G.Adj 3 12
  | 43 => G.Adj 3 13
  | 44 => G.Adj 3 14
  | 45 => G.Adj 3 15
  | 46 => G.Adj 3 16
  | 47 => G.Adj 3 17
  | 48 => G.Adj 3 18
  | 49 => G.Adj 4 5
  | 50 => G.Adj 4 6
  | 51 => G.Adj 4 7
  | 52 => G.Adj 4 8
  | 53 => G.Adj 4 9
  | 54 => G.Adj 4 10
  | 55 => G.Adj 4 11
  | 56 => G.Adj 4 12
  | 57 => G.Adj 4 13
  | 58 => G.Adj 4 14
  | 59 => G.Adj 4 15
  | 60 => G.Adj 4 16
  | 61 => G.Adj 4 17
  | 62 => G.Adj 4 18
  | 63 => G.Adj 5 6
  | 64 => G.Adj 5 7
  | 65 => G.Adj 5 8
  | 66 => G.Adj 5 9
  | 67 => G.Adj 5 10
  | 68 => G.Adj 5 11
  | 69 => G.Adj 5 12
  | 70 => G.Adj 5 13
  | 71 => G.Adj 5 14
  | 72 => G.Adj 5 15
  | 73 => G.Adj 5 16
  | 74 => G.Adj 5 17
  | 75 => G.Adj 5 18
  | 76 => G.Adj 6 7
  | 77 => G.Adj 6 8
  | 78 => G.Adj 6 9
  | 79 => G.Adj 6 10
  | 80 => G.Adj 6 11
  | 81 => G.Adj 6 12
  | 82 => G.Adj 6 13
  | 83 => G.Adj 6 14
  | 84 => G.Adj 6 15
  | 85 => G.Adj 6 16
  | 86 => G.Adj 6 17
  | 87 => G.Adj 6 18
  | 88 => G.Adj 7 8
  | 89 => G.Adj 7 9
  | 90 => G.Adj 7 10
  | 91 => G.Adj 7 11
  | 92 => G.Adj 7 12
  | 93 => G.Adj 7 13
  | 94 => G.Adj 7 14
  | 95 => G.Adj 7 15
  | 96 => G.Adj 7 16
  | 97 => G.Adj 7 17
  | 98 => G.Adj 7 18
  | 99 => G.Adj 8 9
  | 100 => G.Adj 8 10
  | 101 => G.Adj 8 11
  | 102 => G.Adj 8 12
  | 103 => G.Adj 8 13
  | 104 => G.Adj 8 14
  | 105 => G.Adj 8 15
  | 106 => G.Adj 8 16
  | 107 => G.Adj 8 17
  | 108 => G.Adj 8 18
  | 109 => G.Adj 9 10
  | 110 => G.Adj 9 11
  | 111 => G.Adj 9 12
  | 112 => G.Adj 9 13
  | 113 => G.Adj 9 14
  | 114 => G.Adj 9 15
  | 115 => G.Adj 9 16
  | 116 => G.Adj 9 17
  | 117 => G.Adj 9 18
  | 118 => G.Adj 10 11
  | 119 => G.Adj 10 12
  | 120 => G.Adj 10 13
  | 121 => G.Adj 10 14
  | 122 => G.Adj 10 15
  | 123 => G.Adj 10 16
  | 124 => G.Adj 10 17
  | 125 => G.Adj 10 18
  | 126 => G.Adj 11 12
  | 127 => G.Adj 11 13
  | 128 => G.Adj 11 14
  | 129 => G.Adj 11 15
  | 130 => G.Adj 11 16
  | 131 => G.Adj 11 17
  | 132 => G.Adj 11 18
  | 133 => G.Adj 12 13
  | 134 => G.Adj 12 14
  | 135 => G.Adj 12 15
  | 136 => G.Adj 12 16
  | 137 => G.Adj 12 17
  | 138 => G.Adj 12 18
  | 139 => G.Adj 13 14
  | 140 => G.Adj 13 15
  | 141 => G.Adj 13 16
  | 142 => G.Adj 13 17
  | 143 => G.Adj 13 18
  | 144 => G.Adj 14 15
  | 145 => G.Adj 14 16
  | 146 => G.Adj 14 17
  | 147 => G.Adj 14 18
  | 148 => G.Adj 15 16
  | 149 => G.Adj 15 17
  | 150 => G.Adj 15 18
  | 151 => G.Adj 16 17
  | 152 => G.Adj 16 18
  | 153 => G.Adj 17 18
  | _ => False

/-- Barber’s bound: every triangle-free graph has an independent Schur triple in `[1,18]`. -/
theorem independent_schur_triple_le_eighteen (G : SimpleGraph ℕ)
    (hG : G.CliqueFree 3) : HasIndependentSchurTriple G 18 := by
  classical
  by_contra h
  apply resolution (edgeProp G)
  · exact triangle_clause G hG 1 12 18
  · exact triangle_clause G hG 1 6 13
  · exact schur_clause G 18 3 4 h (by decide) (by decide) (by decide)
  · exact triangle_clause G hG 4 11 18
  · exact triangle_clause G hG 1 6 9
  · exact triangle_clause G hG 3 13 14
  · exact triangle_clause G hG 8 9 10
  · exact schur_clause G 18 2 12 h (by decide) (by decide) (by decide)
  · exact triangle_clause G hG 5 6 16
  · exact schur_clause G 18 3 7 h (by decide) (by decide) (by decide)
  · exact triangle_clause G hG 2 11 16
  · exact schur_clause G 18 7 8 h (by decide) (by decide) (by decide)
  · exact triangle_clause G hG 1 5 9
  · exact triangle_clause G hG 3 9 11
  · exact schur_clause G 18 6 8 h (by decide) (by decide) (by decide)
  · exact schur_clause G 18 5 7 h (by decide) (by decide) (by decide)
  · exact triangle_clause G hG 4 7 10
  · exact triangle_clause G hG 1 3 13
  · exact triangle_clause G hG 2 7 16
  · exact schur_clause G 18 1 5 h (by decide) (by decide) (by decide)
  · exact triangle_clause G hG 5 7 8
  · exact triangle_clause G hG 1 5 12
  · exact schur_clause G 18 3 8 h (by decide) (by decide) (by decide)
  · exact triangle_clause G hG 1 14 16
  · exact triangle_clause G hG 6 7 9
  · exact triangle_clause G hG 2 7 10
  · exact schur_clause G 18 1 15 h (by decide) (by decide) (by decide)
  · exact triangle_clause G hG 2 5 6
  · exact triangle_clause G hG 13 14 16
  · exact triangle_clause G hG 2 7 12
  · exact triangle_clause G hG 3 7 11
  · exact triangle_clause G hG 1 5 7
  · exact triangle_clause G hG 16 17 18
  · exact schur_clause G 18 5 13 h (by decide) (by decide) (by decide)
  · exact schur_clause G 18 6 7 h (by decide) (by decide) (by decide)
  · exact triangle_clause G hG 5 11 18
  · exact triangle_clause G hG 3 6 13
  · exact triangle_clause G hG 1 4 7
  · exact triangle_clause G hG 12 13 18
  · exact triangle_clause G hG 5 6 18
  · exact triangle_clause G hG 9 16 17
  · exact triangle_clause G hG 4 5 6
  · exact schur_clause G 18 7 10 h (by decide) (by decide) (by decide)
  · exact triangle_clause G hG 2 11 14
  · exact triangle_clause G hG 6 7 8
  · exact triangle_clause G hG 1 7 9
  · exact triangle_clause G hG 3 13 17
  · exact triangle_clause G hG 1 4 16
  · exact schur_clause G 18 2 10 h (by decide) (by decide) (by decide)
  · exact triangle_clause G hG 8 17 18
  · exact triangle_clause G hG 1 4 11
  · exact triangle_clause G hG 3 4 13
  · exact schur_clause G 18 1 11 h (by decide) (by decide) (by decide)
  · exact schur_clause G 18 8 10 h (by decide) (by decide) (by decide)
  · exact triangle_clause G hG 2 3 7
  · exact triangle_clause G hG 6 7 18
  · exact triangle_clause G hG 3 12 16
  · exact schur_clause G 18 3 6 h (by decide) (by decide) (by decide)
  · exact triangle_clause G hG 1 5 15
  · exact triangle_clause G hG 6 12 17
  · exact triangle_clause G hG 12 14 15
  · exact triangle_clause G hG 1 4 9
  · exact triangle_clause G hG 12 16 18
  · exact triangle_clause G hG 10 12 15
  · exact triangle_clause G hG 6 10 17
  · exact triangle_clause G hG 5 11 12
  · exact triangle_clause G hG 14 16 18
  · exact triangle_clause G hG 3 7 18
  · exact triangle_clause G hG 3 6 17
  · exact triangle_clause G hG 1 9 13
  · exact triangle_clause G hG 2 5 14
  · exact triangle_clause G hG 1 6 16
  · exact triangle_clause G hG 5 12 14
  · exact schur_clause G 18 5 6 h (by decide) (by decide) (by decide)
  · exact schur_clause G 18 2 6 h (by decide) (by decide) (by decide)
  · exact triangle_clause G hG 3 4 6
  · exact triangle_clause G hG 7 11 13
  · exact triangle_clause G hG 5 6 8
  · exact triangle_clause G hG 4 10 11
  · exact triangle_clause G hG 9 15 17
  · exact triangle_clause G hG 3 5 13
  · exact triangle_clause G hG 1 2 15
  · exact schur_clause G 18 8 9 h (by decide) (by decide) (by decide)
  · exact triangle_clause G hG 1 4 10
  · exact triangle_clause G hG 7 13 17
  · exact triangle_clause G hG 4 5 14
  · exact triangle_clause G hG 12 14 16
  · exact schur_clause G 18 3 11 h (by decide) (by decide) (by decide)
  · exact triangle_clause G hG 2 6 15
  · exact triangle_clause G hG 4 9 16
  · exact triangle_clause G hG 1 12 16
  · exact schur_clause G 18 1 13 h (by decide) (by decide) (by decide)
  · exact triangle_clause G hG 3 16 18
  · exact triangle_clause G hG 10 11 14
  · exact triangle_clause G hG 7 8 9
  · exact triangle_clause G hG 6 11 12
  · exact triangle_clause G hG 7 9 11
  · exact triangle_clause G hG 9 13 14
  · exact schur_clause G 18 1 17 h (by decide) (by decide) (by decide)
  · exact triangle_clause G hG 4 5 13
  · exact triangle_clause G hG 3 5 12
  · exact triangle_clause G hG 2 4 9
  · exact triangle_clause G hG 1 10 17
  · exact triangle_clause G hG 2 14 17
  · exact triangle_clause G hG 4 5 7
  · exact triangle_clause G hG 3 8 9
  · exact schur_clause G 18 2 16 h (by decide) (by decide) (by decide)
  · exact triangle_clause G hG 1 11 17
  · exact triangle_clause G hG 2 15 16
  · exact triangle_clause G hG 5 14 17
  · exact schur_clause G 18 1 8 h (by decide) (by decide) (by decide)
  · exact triangle_clause G hG 9 10 15
  · exact triangle_clause G hG 9 14 15
  · exact triangle_clause G hG 2 10 16
  · exact triangle_clause G hG 1 11 15
  · exact triangle_clause G hG 10 12 17
  · exact triangle_clause G hG 1 3 8
  · exact triangle_clause G hG 2 7 9
  · exact triangle_clause G hG 1 5 13
  · exact triangle_clause G hG 1 4 12
  · exact triangle_clause G hG 7 13 18
  · exact triangle_clause G hG 4 6 7
  · exact triangle_clause G hG 1 14 17
  · exact triangle_clause G hG 2 12 13
  · exact schur_clause G 18 6 9 h (by decide) (by decide) (by decide)
  · exact triangle_clause G hG 10 11 17
  · exact triangle_clause G hG 2 3 9
  · exact triangle_clause G hG 6 13 18
  · exact triangle_clause G hG 1 4 8
  · exact triangle_clause G hG 3 7 17
  · exact triangle_clause G hG 15 16 17
  · exact triangle_clause G hG 1 8 14
  · exact triangle_clause G hG 11 15 18
  · exact schur_clause G 18 2 14 h (by decide) (by decide) (by decide)
  · exact triangle_clause G hG 2 6 8
  · exact schur_clause G 18 7 11 h (by decide) (by decide) (by decide)
  · exact triangle_clause G hG 5 7 15
  · exact schur_clause G 18 5 11 h (by decide) (by decide) (by decide)
  · exact triangle_clause G hG 6 8 13
  · exact triangle_clause G hG 2 9 10
  · exact schur_clause G 18 4 13 h (by decide) (by decide) (by decide)
  · exact triangle_clause G hG 2 5 10
  · exact triangle_clause G hG 1 10 12
  · exact triangle_clause G hG 2 13 16
  · exact schur_clause G 18 2 15 h (by decide) (by decide) (by decide)
  · exact triangle_clause G hG 2 8 13
  · exact triangle_clause G hG 1 6 11
  · exact triangle_clause G hG 3 14 18
  · exact triangle_clause G hG 3 8 12
  · exact triangle_clause G hG 6 9 11
  · exact triangle_clause G hG 2 6 12
  · exact triangle_clause G hG 5 15 16
  · exact schur_clause G 18 1 16 h (by decide) (by decide) (by decide)
  · exact schur_clause G 18 5 8 h (by decide) (by decide) (by decide)
  · exact triangle_clause G hG 7 8 17
  · exact triangle_clause G hG 2 3 6
  · exact triangle_clause G hG 8 9 14
  · exact triangle_clause G hG 3 15 17
  · exact triangle_clause G hG 1 3 16
  · exact triangle_clause G hG 5 6 14
  · exact triangle_clause G hG 5 6 15
  · exact triangle_clause G hG 4 11 16
  · exact triangle_clause G hG 2 7 11
  · exact triangle_clause G hG 14 15 17
  · exact triangle_clause G hG 10 17 18
  · exact schur_clause G 18 1 12 h (by decide) (by decide) (by decide)
  · exact triangle_clause G hG 3 9 13
  · exact triangle_clause G hG 11 12 17
  · exact triangle_clause G hG 7 15 17
  · exact schur_clause G 18 1 2 h (by decide) (by decide) (by decide)
  · exact triangle_clause G hG 10 13 18
  · exact triangle_clause G hG 3 9 14
  · exact schur_clause G 18 3 10 h (by decide) (by decide) (by decide)
  · exact triangle_clause G hG 5 10 18
  · exact triangle_clause G hG 7 8 10
  · exact triangle_clause G hG 5 12 15
  · exact triangle_clause G hG 15 17 18
  · exact triangle_clause G hG 6 14 18
  · exact triangle_clause G hG 12 14 17
  · exact triangle_clause G hG 5 6 10
  · exact triangle_clause G hG 1 5 10
  · exact triangle_clause G hG 5 10 11
  · exact triangle_clause G hG 12 15 18
  · exact triangle_clause G hG 4 13 18
  · exact triangle_clause G hG 4 5 15
  · exact triangle_clause G hG 8 14 15
  · exact triangle_clause G hG 2 12 17
  · exact triangle_clause G hG 4 5 17
  · exact triangle_clause G hG 11 14 16
  · exact triangle_clause G hG 3 6 12
  · exact triangle_clause G hG 1 2 13
  · exact schur_clause G 18 4 14 h (by decide) (by decide) (by decide)
  · exact triangle_clause G hG 1 12 15
  · exact triangle_clause G hG 3 12 17
  · exact triangle_clause G hG 8 15 17
  · exact triangle_clause G hG 11 13 18
  · exact triangle_clause G hG 4 9 14
  · exact triangle_clause G hG 2 11 17
  · exact triangle_clause G hG 3 5 15
  · exact triangle_clause G hG 7 8 13
  · exact triangle_clause G hG 2 6 9
  · exact triangle_clause G hG 6 8 18
  · exact schur_clause G 18 7 9 h (by decide) (by decide) (by decide)
  · exact triangle_clause G hG 8 11 18
  · exact triangle_clause G hG 8 11 12
  · exact triangle_clause G hG 5 13 14
  · exact schur_clause G 18 1 7 h (by decide) (by decide) (by decide)
  · exact triangle_clause G hG 1 3 5
  · exact triangle_clause G hG 3 4 14
  · exact triangle_clause G hG 3 6 14
  · exact triangle_clause G hG 7 10 16
  · exact triangle_clause G hG 11 12 14
  · exact schur_clause G 18 1 6 h (by decide) (by decide) (by decide)
  · exact triangle_clause G hG 3 14 15
  · exact triangle_clause G hG 4 13 15
  · exact triangle_clause G hG 3 9 17
  · exact triangle_clause G hG 6 10 15
  · exact triangle_clause G hG 1 9 15
  · exact triangle_clause G hG 6 12 13
  · exact triangle_clause G hG 1 9 17
  · exact triangle_clause G hG 5 8 11
  · exact triangle_clause G hG 2 5 8
  · exact triangle_clause G hG 8 14 17
  · exact triangle_clause G hG 5 6 17
  · exact triangle_clause G hG 2 3 10
  · exact triangle_clause G hG 6 10 14
  · exact triangle_clause G hG 3 10 12
  · exact triangle_clause G hG 9 12 17
  · exact triangle_clause G hG 15 16 18
  · exact triangle_clause G hG 2 13 18
  · exact triangle_clause G hG 1 4 14
  · exact triangle_clause G hG 7 8 12
  · exact triangle_clause G hG 1 11 14
  · exact triangle_clause G hG 3 7 15
  · exact schur_clause G 18 4 6 h (by decide) (by decide) (by decide)
  · exact triangle_clause G hG 8 14 18
  · exact triangle_clause G hG 8 9 11
  · exact triangle_clause G hG 1 3 10
  · exact schur_clause G 18 6 10 h (by decide) (by decide) (by decide)
  · exact triangle_clause G hG 3 7 16
  · exact triangle_clause G hG 7 10 12
  · exact triangle_clause G hG 2 3 13
  · exact triangle_clause G hG 1 13 16
  · exact triangle_clause G hG 1 3 15
  · exact triangle_clause G hG 1 4 6
  · exact triangle_clause G hG 4 5 16
  · exact triangle_clause G hG 5 9 15
  · exact triangle_clause G hG 3 9 16
  · exact triangle_clause G hG 9 15 16
  · exact triangle_clause G hG 4 6 9
  · exact triangle_clause G hG 6 16 18
  · exact triangle_clause G hG 4 9 10
  · exact triangle_clause G hG 6 8 12
  · exact triangle_clause G hG 2 10 17
  · exact triangle_clause G hG 10 13 15
  · exact triangle_clause G hG 3 8 17
  · exact triangle_clause G hG 2 5 12
  · exact triangle_clause G hG 1 2 10
  · exact schur_clause G 18 3 5 h (by decide) (by decide) (by decide)
  · exact triangle_clause G hG 13 14 18
  · exact triangle_clause G hG 5 11 15
  · exact triangle_clause G hG 2 10 14
  · exact triangle_clause G hG 2 6 11
  · exact triangle_clause G hG 6 8 10
  · exact triangle_clause G hG 9 10 11
  · exact triangle_clause G hG 4 5 12
  · exact triangle_clause G hG 1 6 18
  · exact triangle_clause G hG 2 15 18
  · exact triangle_clause G hG 3 5 18
  · exact schur_clause G 18 2 5 h (by decide) (by decide) (by decide)
  · exact triangle_clause G hG 8 15 18
  · exact triangle_clause G hG 4 5 10
  · exact schur_clause G 18 4 5 h (by decide) (by decide) (by decide)
  · exact triangle_clause G hG 12 13 14
  · exact triangle_clause G hG 6 7 11
  · exact triangle_clause G hG 1 8 9
  · exact triangle_clause G hG 7 10 11
  · exact triangle_clause G hG 3 4 8
  · exact triangle_clause G hG 1 8 11
  · exact triangle_clause G hG 3 6 15
  · exact triangle_clause G hG 1 5 11
  · exact triangle_clause G hG 11 13 16
  · exact triangle_clause G hG 1 3 6
  · exact triangle_clause G hG 2 3 14
  · exact triangle_clause G hG 3 12 13
  · exact triangle_clause G hG 9 12 14
  · exact triangle_clause G hG 4 14 17
  · exact triangle_clause G hG 4 6 13
  · exact triangle_clause G hG 10 11 12
  · exact triangle_clause G hG 4 8 9
  · exact triangle_clause G hG 3 5 10
  · exact triangle_clause G hG 2 9 14
  · exact triangle_clause G hG 6 9 16
  · exact triangle_clause G hG 2 9 13
  · exact triangle_clause G hG 2 7 15
  · exact triangle_clause G hG 1 15 17
  · exact triangle_clause G hG 8 9 15
  · exact triangle_clause G hG 4 13 16
  · exact triangle_clause G hG 2 6 7
  · exact triangle_clause G hG 1 3 12
  · exact triangle_clause G hG 1 10 13
  · exact triangle_clause G hG 4 13 14
  · exact triangle_clause G hG 2 7 17
  · exact triangle_clause G hG 7 13 15
  · exact triangle_clause G hG 4 9 12
  · exact triangle_clause G hG 5 12 13
  · exact triangle_clause G hG 4 9 15
  · exact triangle_clause G hG 2 8 9
  · exact triangle_clause G hG 2 6 17
  · exact triangle_clause G hG 6 10 12
  · exact triangle_clause G hG 2 11 15
  · exact triangle_clause G hG 5 6 13
  · exact triangle_clause G hG 4 7 18
  · exact triangle_clause G hG 6 7 17
  · exact triangle_clause G hG 12 15 16
  · exact triangle_clause G hG 3 12 18
  · exact triangle_clause G hG 2 6 18
  · exact triangle_clause G hG 6 9 17
  · exact triangle_clause G hG 8 10 13
  · exact triangle_clause G hG 3 15 16
  · exact triangle_clause G hG 4 11 12
  · exact triangle_clause G hG 3 10 16
  · exact schur_clause G 18 5 10 h (by decide) (by decide) (by decide)
  · exact triangle_clause G hG 1 8 10
  · exact triangle_clause G hG 5 8 17
  · exact triangle_clause G hG 1 6 15
  · exact triangle_clause G hG 7 9 10
  · exact triangle_clause G hG 5 9 10
  · exact triangle_clause G hG 1 4 13
  · exact triangle_clause G hG 3 5 7
  · exact triangle_clause G hG 8 10 15
  · exact triangle_clause G hG 2 9 12
  · exact triangle_clause G hG 4 6 16
  · exact triangle_clause G hG 6 9 10
  · exact triangle_clause G hG 7 12 16
  · exact triangle_clause G hG 1 2 8
  · exact triangle_clause G hG 12 15 17
  · exact triangle_clause G hG 1 5 14
  · exact triangle_clause G hG 5 10 16
  · exact triangle_clause G hG 7 12 18
  · exact schur_clause G 18 2 9 h (by decide) (by decide) (by decide)
  · exact triangle_clause G hG 4 10 17
  · exact triangle_clause G hG 7 10 13
  · exact triangle_clause G hG 1 2 17
  · exact triangle_clause G hG 11 12 15
  · exact triangle_clause G hG 5 6 12
  · exact triangle_clause G hG 6 15 17
  · exact triangle_clause G hG 1 6 12
  · exact triangle_clause G hG 2 14 18
  · exact triangle_clause G hG 9 11 16
  · exact triangle_clause G hG 3 4 9
  · exact triangle_clause G hG 4 6 17
  · exact triangle_clause G hG 1 8 17
  · exact triangle_clause G hG 3 7 12
  · exact triangle_clause G hG 13 14 15
  · exact triangle_clause G hG 4 7 9
  · exact triangle_clause G hG 3 7 9
  · exact triangle_clause G hG 4 5 8
  · exact triangle_clause G hG 2 5 11
  · exact triangle_clause G hG 3 6 11
  · exact triangle_clause G hG 3 6 18
  · exact triangle_clause G hG 7 16 18
  · exact triangle_clause G hG 9 10 12
  · exact triangle_clause G hG 2 4 8
  · exact triangle_clause G hG 1 2 11
  · exact schur_clause G 18 4 8 h (by decide) (by decide) (by decide)
  · exact triangle_clause G hG 5 9 13
  · exact triangle_clause G hG 1 10 16
  · exact triangle_clause G hG 7 9 15
  · exact triangle_clause G hG 1 6 8
  · exact triangle_clause G hG 9 14 17
  · exact triangle_clause G hG 8 12 18
  · exact triangle_clause G hG 1 11 16
  · exact triangle_clause G hG 11 14 15
  · exact triangle_clause G hG 2 3 4
  · exact triangle_clause G hG 5 10 13
  · exact triangle_clause G hG 11 13 14
  · exact schur_clause G 18 6 11 h (by decide) (by decide) (by decide)
  · exact triangle_clause G hG 6 11 15
  · exact triangle_clause G hG 3 4 10
  · exact schur_clause G 18 2 4 h (by decide) (by decide) (by decide)
  · exact triangle_clause G hG 11 12 16
  · exact triangle_clause G hG 1 11 13
  · exact schur_clause G 18 5 9 h (by decide) (by decide) (by decide)
  · exact triangle_clause G hG 1 14 18
  · exact triangle_clause G hG 1 3 9
  · exact triangle_clause G hG 2 3 11
  · exact triangle_clause G hG 3 11 18
  · exact triangle_clause G hG 6 7 12
  · exact triangle_clause G hG 8 13 18
  · exact triangle_clause G hG 5 9 11
  · exact triangle_clause G hG 5 9 12
  · exact triangle_clause G hG 1 12 14
  · exact schur_clause G 18 1 9 h (by decide) (by decide) (by decide)
  · exact triangle_clause G hG 1 2 5
  · exact triangle_clause G hG 2 10 13
  · exact triangle_clause G hG 2 5 16
  · exact triangle_clause G hG 1 2 12
  · exact triangle_clause G hG 1 8 18
  · exact schur_clause G 18 2 7 h (by decide) (by decide) (by decide)
  · exact triangle_clause G hG 1 13 17
  · exact triangle_clause G hG 8 10 14
  · exact triangle_clause G hG 5 6 9
  · exact triangle_clause G hG 6 9 14
  · exact triangle_clause G hG 6 12 15
  · exact triangle_clause G hG 8 13 17
  · exact triangle_clause G hG 13 14 17
  · exact triangle_clause G hG 3 4 15
  · exact triangle_clause G hG 1 5 17
  · exact triangle_clause G hG 1 3 18
  · exact triangle_clause G hG 3 11 16
  · exact triangle_clause G hG 5 16 17
  · exact triangle_clause G hG 1 2 18
  · exact triangle_clause G hG 3 5 8
  · exact triangle_clause G hG 10 11 18
  · exact triangle_clause G hG 8 9 13
  · exact schur_clause G 18 3 12 h (by decide) (by decide) (by decide)
  · exact triangle_clause G hG 1 5 8
  · exact triangle_clause G hG 6 15 18
  · exact triangle_clause G hG 4 12 14
  · exact triangle_clause G hG 5 7 18
  · exact triangle_clause G hG 9 12 13
  · exact triangle_clause G hG 1 9 12
  · exact triangle_clause G hG 2 6 10
  · exact triangle_clause G hG 1 13 15
  · exact triangle_clause G hG 6 17 18
  · exact schur_clause G 18 2 13 h (by decide) (by decide) (by decide)
  · exact triangle_clause G hG 11 12 13
  · exact triangle_clause G hG 4 7 12
  · exact triangle_clause G hG 6 11 16
  · exact triangle_clause G hG 2 11 18
  · exact triangle_clause G hG 2 5 15
  · exact triangle_clause G hG 10 13 16
  · exact triangle_clause G hG 1 8 13
  · exact triangle_clause G hG 5 8 9
  · exact triangle_clause G hG 2 10 18
  · exact triangle_clause G hG 3 8 15
  · exact triangle_clause G hG 2 4 7
  · exact triangle_clause G hG 7 11 16
  · exact triangle_clause G hG 3 11 13
  · exact triangle_clause G hG 3 11 17
  · exact schur_clause G 18 2 8 h (by decide) (by decide) (by decide)
  · exact triangle_clause G hG 10 12 14
  · exact schur_clause G 18 4 7 h (by decide) (by decide) (by decide)
  · exact triangle_clause G hG 1 6 14
  · exact triangle_clause G hG 11 15 17
  · exact triangle_clause G hG 1 16 18
  · exact triangle_clause G hG 7 8 18
  · exact triangle_clause G hG 5 15 17
  · exact triangle_clause G hG 2 6 14
  · exact triangle_clause G hG 1 2 16
  · exact triangle_clause G hG 1 3 7
  · exact triangle_clause G hG 2 4 14
  · exact triangle_clause G hG 2 10 15
  · exact triangle_clause G hG 13 15 16
  · exact triangle_clause G hG 4 12 17
  · exact triangle_clause G hG 7 10 18
  · exact triangle_clause G hG 3 9 15
  · exact triangle_clause G hG 2 6 16
  · exact triangle_clause G hG 6 9 13
  · exact triangle_clause G hG 4 16 18
  · exact triangle_clause G hG 3 4 5
  · exact schur_clause G 18 3 14 h (by decide) (by decide) (by decide)
  · exact triangle_clause G hG 2 12 18
  · exact triangle_clause G hG 9 11 15
  · exact triangle_clause G hG 8 11 17
  · exact triangle_clause G hG 5 7 16
  · exact triangle_clause G hG 2 4 13
  · exact triangle_clause G hG 5 6 7
  · exact triangle_clause G hG 2 3 17
  · exact triangle_clause G hG 5 7 9
  · exact triangle_clause G hG 9 13 16
  · exact triangle_clause G hG 1 2 4
  · exact triangle_clause G hG 11 16 18
  · exact triangle_clause G hG 2 3 16
  · exact triangle_clause G hG 7 9 17
  · exact triangle_clause G hG 1 2 7
  · exact triangle_clause G hG 2 5 17
  · exact triangle_clause G hG 6 13 17
  · exact triangle_clause G hG 6 10 18
  · exact triangle_clause G hG 11 12 18
  · exact triangle_clause G hG 12 13 16
  · exact triangle_clause G hG 3 5 14
  · exact triangle_clause G hG 7 8 11
  · exact triangle_clause G hG 6 15 16
  · exact triangle_clause G hG 1 15 18
  · exact triangle_clause G hG 5 16 18
  · exact triangle_clause G hG 5 8 14
  · exact triangle_clause G hG 2 5 9
  · exact triangle_clause G hG 8 13 15
  · exact triangle_clause G hG 2 8 18
  · exact schur_clause G 18 2 11 h (by decide) (by decide) (by decide)
  · exact triangle_clause G hG 10 12 18
  · exact schur_clause G 18 1 14 h (by decide) (by decide) (by decide)
  · exact triangle_clause G hG 3 10 11
  · exact triangle_clause G hG 13 16 17
  · exact triangle_clause G hG 7 9 13
  · exact triangle_clause G hG 2 7 13
  · exact triangle_clause G hG 1 7 17
  · exact triangle_clause G hG 12 17 18
  · exact triangle_clause G hG 3 10 15
  · exact triangle_clause G hG 3 4 12
  · exact triangle_clause G hG 1 6 10
  · exact triangle_clause G hG 13 15 18
  · exact schur_clause G 18 1 3 h (by decide) (by decide) (by decide)
  · exact schur_clause G 18 4 12 h (by decide) (by decide) (by decide)
  · exact triangle_clause G hG 9 10 16
  · exact schur_clause G 18 2 3 h (by decide) (by decide) (by decide)
  · exact triangle_clause G hG 1 9 11
  · exact triangle_clause G hG 7 11 15
  · exact triangle_clause G hG 11 14 18
  · exact triangle_clause G hG 5 7 11
  · exact triangle_clause G hG 3 10 14
  · exact triangle_clause G hG 4 11 14
  · exact triangle_clause G hG 1 3 14
  · exact triangle_clause G hG 3 10 17
  · exact triangle_clause G hG 2 7 8
  · exact schur_clause G 18 3 9 h (by decide) (by decide) (by decide)
  · exact triangle_clause G hG 6 10 11
  · exact triangle_clause G hG 2 8 15
  · exact schur_clause G 18 3 13 h (by decide) (by decide) (by decide)
  · exact triangle_clause G hG 5 10 17
  · exact triangle_clause G hG 2 5 18
  · exact triangle_clause G hG 2 8 17
  · exact triangle_clause G hG 1 10 18
  · exact triangle_clause G hG 2 14 15
  · exact triangle_clause G hG 7 15 18
  · exact triangle_clause G hG 4 6 15
  · exact triangle_clause G hG 4 12 18
  · exact triangle_clause G hG 5 11 13
  · exact triangle_clause G hG 4 7 16
  · exact triangle_clause G hG 4 10 15
  · exact triangle_clause G hG 4 12 13
  · exact triangle_clause G hG 1 7 11
  · exact triangle_clause G hG 4 6 18
  · exact triangle_clause G hG 1 7 10
  · exact triangle_clause G hG 3 6 7
  · exact schur_clause G 18 4 9 h (by decide) (by decide) (by decide)
  · exact triangle_clause G hG 3 9 10
  · exact triangle_clause G hG 5 13 17
  · exact triangle_clause G hG 3 8 10
  · exact triangle_clause G hG 5 8 15
  · exact triangle_clause G hG 10 11 16
  · exact triangle_clause G hG 2 8 11
  · exact triangle_clause G hG 4 6 12
  · exact triangle_clause G hG 6 8 17
  · exact triangle_clause G hG 12 16 17
  · exact triangle_clause G hG 3 5 11
  · exact schur_clause G 18 1 4 h (by decide) (by decide) (by decide)
  · exact triangle_clause G hG 6 11 18
  · exact triangle_clause G hG 5 9 17
  · exact triangle_clause G hG 2 3 15
  · exact triangle_clause G hG 11 17 18
  · exact triangle_clause G hG 2 16 17
  · exact triangle_clause G hG 4 10 13
  · exact triangle_clause G hG 4 7 8
  · exact triangle_clause G hG 2 8 12
  · exact triangle_clause G hG 4 7 13
  · exact triangle_clause G hG 3 4 11
  · exact schur_clause G 18 4 11 h (by decide) (by decide) (by decide)
  · exact schur_clause G 18 6 12 h (by decide) (by decide) (by decide)
  · exact triangle_clause G hG 2 3 18
  · exact triangle_clause G hG 3 5 17
  · exact schur_clause G 18 1 10 h (by decide) (by decide) (by decide)
  · exact triangle_clause G hG 3 8 14
  · exact triangle_clause G hG 7 11 12
  · exact triangle_clause G hG 4 8 11
  · exact triangle_clause G hG 13 15 17
  · exact triangle_clause G hG 7 10 15
  · exact triangle_clause G hG 8 12 13
  · exact triangle_clause G hG 8 10 11
  · exact triangle_clause G hG 6 8 9
  · exact triangle_clause G hG 5 15 18
  · exact triangle_clause G hG 1 5 16
  · exact schur_clause G 18 4 10 h (by decide) (by decide) (by decide)
  · exact schur_clause G 18 3 15 h (by decide) (by decide) (by decide)
  · exact triangle_clause G hG 5 14 16
  · exact triangle_clause G hG 5 10 12
  · exact triangle_clause G hG 8 12 15
  · exact triangle_clause G hG 10 14 18
  · exact triangle_clause G hG 5 7 13
  · exact triangle_clause G hG 2 3 12
  · exact triangle_clause G hG 4 5 11
  · exact triangle_clause G hG 3 13 15
  · exact triangle_clause G hG 7 16 17
  · exact triangle_clause G hG 11 13 17
  · exact triangle_clause G hG 2 5 13
  · exact triangle_clause G hG 2 11 12
  · exact schur_clause G 18 5 12 h (by decide) (by decide) (by decide)
  · exact triangle_clause G hG 9 11 17
  · exact triangle_clause G hG 2 7 18
  · exact triangle_clause G hG 8 12 17
  · exact triangle_clause G hG 8 11 13
  · exact triangle_clause G hG 5 12 18
  · exact triangle_clause G hG 10 15 16
  · exact triangle_clause G hG 6 12 16
  · exact triangle_clause G hG 5 7 17
  · exact triangle_clause G hG 14 16 17
  · exact triangle_clause G hG 4 8 18
  · exact triangle_clause G hG 2 4 15
  · exact triangle_clause G hG 5 12 16
  · exact triangle_clause G hG 4 12 15

/-- The original existence statement, with positivity, distinctness and standard independence. -/
theorem erdos_895 (G : SimpleGraph ℕ) (hG : G.CliqueFree 3) :
    ∃ a b : ℕ, 0 < a ∧ a < b ∧ a + b ≤ 18 ∧ G.IsIndepSet {a,b,a+b} := by
  obtain ⟨a,b,ha,hab,hN,h₁,h₂,h₃⟩ := independent_schur_triple_le_eighteen G hG
  exact ⟨a,b,ha,hab,hN,independent_triple G h₁ h₂ h₃⟩

end JSP000746
