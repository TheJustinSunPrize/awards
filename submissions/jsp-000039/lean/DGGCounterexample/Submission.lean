import Mathlib

namespace DGG

inductive Node where
  | s | u | v | w | t1 | t2 | t3
  deriving DecidableEq, Repr

inductive Edge where
  | st1 | st2 | su | ut3 | uv | vt1 | vw | wt2 | wt3
  deriving DecidableEq, Repr

inductive Terminal where
  | one | two | three
  deriving DecidableEq, Repr

inductive Choice where
  | E | Z
  deriving DecidableEq, Repr

abbrev Route := Terminal -> Choice

def source : Edge -> Node
  | Edge.st1 => Node.s
  | Edge.st2 => Node.s
  | Edge.su => Node.s
  | Edge.ut3 => Node.u
  | Edge.uv => Node.u
  | Edge.vt1 => Node.v
  | Edge.vw => Node.v
  | Edge.wt2 => Node.w
  | Edge.wt3 => Node.w

def target : Edge -> Node
  | Edge.st1 => Node.t1
  | Edge.st2 => Node.t2
  | Edge.su => Node.u
  | Edge.ut3 => Node.t3
  | Edge.uv => Node.v
  | Edge.vt1 => Node.t1
  | Edge.vw => Node.w
  | Edge.wt2 => Node.t2
  | Edge.wt3 => Node.t3

def terminalNode : Terminal -> Node
  | Terminal.one => Node.t1
  | Terminal.two => Node.t2
  | Terminal.three => Node.t3

def demand : Terminal -> ℚ
  | Terminal.one => 15
  | Terminal.two => 10
  | Terminal.three => 15

def baseFlow : Edge -> ℚ
  | Edge.st1 => 10
  | Edge.st2 => 6
  | Edge.su => 24
  | Edge.ut3 => 10
  | Edge.uv => 14
  | Edge.vt1 => 5
  | Edge.vw => 9
  | Edge.wt2 => 4
  | Edge.wt3 => 5

def capacity (e : Edge) : ℚ := baseFlow e + 15

def route (c1 c2 c3 : Choice) : Route
  | Terminal.one => c1
  | Terminal.two => c2
  | Terminal.three => c3

def routeEEZ : Route := route Choice.E Choice.E Choice.Z
def routeEZE : Route := route Choice.E Choice.Z Choice.E
def routeZEE : Route := route Choice.Z Choice.E Choice.E
def routeEEE : Route := route Choice.E Choice.E Choice.E

def uses (r : Route) (t : Terminal) (e : Edge) : Bool :=
  match t, r t, e with
  | Terminal.one, Choice.E, Edge.st1 => true
  | Terminal.one, Choice.Z, Edge.su => true
  | Terminal.one, Choice.Z, Edge.uv => true
  | Terminal.one, Choice.Z, Edge.vt1 => true
  | Terminal.two, Choice.E, Edge.st2 => true
  | Terminal.two, Choice.Z, Edge.su => true
  | Terminal.two, Choice.Z, Edge.uv => true
  | Terminal.two, Choice.Z, Edge.vw => true
  | Terminal.two, Choice.Z, Edge.wt2 => true
  | Terminal.three, Choice.E, Edge.su => true
  | Terminal.three, Choice.E, Edge.ut3 => true
  | Terminal.three, Choice.Z, Edge.su => true
  | Terminal.three, Choice.Z, Edge.uv => true
  | Terminal.three, Choice.Z, Edge.vw => true
  | Terminal.three, Choice.Z, Edge.wt3 => true
  | _, _, _ => false

def load (r : Route) (e : Edge) : ℚ :=
  (if uses r Terminal.one e then demand Terminal.one else 0) +
  (if uses r Terminal.two e then demand Terminal.two else 0) +
  (if uses r Terminal.three e then demand Terminal.three else 0)

def Feasible (r : Route) : Prop := ∀ e : Edge, load r e ≤ capacity e

def fractionalCost (a b c : ℚ) : ℚ := 10 * a + 6 * b + 10 * c

def routeCost (a b c : ℚ) (r : Route) : ℚ :=
  (if r Terminal.one = Choice.E then 15 * a else 0) +
  (if r Terminal.two = Choice.E then 10 * b else 0) +
  (if r Terminal.three = Choice.E then 15 * c else 0)

theorem conservation_source :
    baseFlow Edge.st1 + baseFlow Edge.st2 + baseFlow Edge.su
      = demand Terminal.one + demand Terminal.two + demand Terminal.three := by
  norm_num [baseFlow, demand]

theorem conservation_u :
    baseFlow Edge.su = baseFlow Edge.ut3 + baseFlow Edge.uv := by
  norm_num [baseFlow]

theorem conservation_v :
    baseFlow Edge.uv = baseFlow Edge.vt1 + baseFlow Edge.vw := by
  norm_num [baseFlow]

theorem conservation_w :
    baseFlow Edge.vw = baseFlow Edge.wt2 + baseFlow Edge.wt3 := by
  norm_num [baseFlow]

theorem sink_one :
    baseFlow Edge.st1 + baseFlow Edge.vt1 = demand Terminal.one := by
  norm_num [baseFlow, demand]

theorem sink_two :
    baseFlow Edge.st2 + baseFlow Edge.wt2 = demand Terminal.two := by
  norm_num [baseFlow, demand]

theorem sink_three :
    baseFlow Edge.ut3 + baseFlow Edge.wt3 = demand Terminal.three := by
  norm_num [baseFlow, demand]

theorem flow_feasible : ∀ e : Edge, baseFlow e ≤ capacity e := by
  intro e
  cases e <;> norm_num [baseFlow, capacity]

theorem Dmax_is_max (t : Terminal) : demand t ≤ 15 := by
  cases t <;> norm_num [demand]

theorem fractionalCost_eq (a b c : ℚ) :
    fractionalCost a b c = 10 * a + 6 * b + 10 * c := rfl

theorem route_ext {r : Route} {c1 c2 c3 : Choice}
    (h1 : r Terminal.one = c1)
    (h2 : r Terminal.two = c2)
    (h3 : r Terminal.three = c3) :
    r = route c1 c2 c3 := by
  funext t
  cases t <;> simp [route, h1, h2, h3]

theorem routeEEZ_data : Feasible routeEEZ ∧
    routeCost a b c routeEEZ = 15 * a + 10 * b := by
  constructor
  · intro e
    cases e <;> norm_num [Feasible, load, uses, routeEEZ, route, capacity, baseFlow, demand]
  · norm_num [routeCost, routeEEZ, route]

theorem routeEZE_data : Feasible routeEZE ∧
    routeCost a b c routeEZE = 15 * a + 15 * c := by
  constructor
  · intro e
    cases e <;> norm_num [Feasible, load, uses, routeEZE, route, capacity, baseFlow, demand]
  · norm_num [routeCost, routeEZE, route]

theorem routeZEE_data : Feasible routeZEE ∧
    routeCost a b c routeZEE = 10 * b + 15 * c := by
  constructor
  · intro e
    cases e <;> norm_num [Feasible, load, uses, routeZEE, route, capacity, baseFlow, demand]
  · norm_num [routeCost, routeZEE, route]

theorem routeEEE_data : Feasible routeEEE ∧
    routeCost a b c routeEEE = 15 * a + 10 * b + 15 * c := by
  constructor
  · intro e
    cases e <;> norm_num [Feasible, load, uses, routeEEE, route, capacity, baseFlow, demand]
  · norm_num [routeCost, routeEEE, route]

theorem feasible_routes (r : Route) :
    Feasible r ↔
      r = routeEEZ ∨ r = routeEZE ∨ r = routeZEE ∨ r = routeEEE := by
  constructor
  · intro h
    rcases h Edge.su with hsu
    rcases h Edge.uv with huv
    rcases h Edge.vw with hvw
    cases h1 : r Terminal.one <;>
      cases h2 : r Terminal.two <;>
      cases h3 : r Terminal.three
    · right; right; right
      exact route_ext h1 h2 h3
    · left
      exact route_ext h1 h2 h3
    · right; left
      exact route_ext h1 h2 h3
    · exfalso
      norm_num [load, uses, capacity, baseFlow, demand, h1, h2, h3] at hvw
    · right; right; left
      exact route_ext h1 h2 h3
    · exfalso
      norm_num [load, uses, capacity, baseFlow, demand, h1, h2, h3] at huv
    · exfalso
      norm_num [load, uses, capacity, baseFlow, demand, h1, h2, h3] at hsu
    · exfalso
      norm_num [load, uses, capacity, baseFlow, demand, h1, h2, h3] at hsu
  · intro h
    rcases h with h | h | h | h
    · rw [h]; exact (routeEEZ_data (a := 0) (b := 0) (c := 0)).left
    · rw [h]; exact (routeEZE_data (a := 0) (b := 0) (c := 0)).left
    · rw [h]; exact (routeZEE_data (a := 0) (b := 0) (c := 0)).left
    · rw [h]; exact (routeEEE_data (a := 0) (b := 0) (c := 0)).left

theorem enum_charged (r : Route) (h : Feasible r) :
    r Terminal.one = Choice.E ∧ r Terminal.two = Choice.E ∨
    r Terminal.one = Choice.E ∧ r Terminal.three = Choice.E ∨
    r Terminal.two = Choice.E ∧ r Terminal.three = Choice.E := by
  rw [feasible_routes] at h
  rcases h with h | h | h | h <;> rw [h] <;> simp [routeEEZ, routeEZE, routeZEE, routeEEE, route]

def pathEdges : Terminal -> Choice -> List Edge
  | Terminal.one, Choice.E => [Edge.st1]
  | Terminal.one, Choice.Z => [Edge.su, Edge.uv, Edge.vt1]
  | Terminal.two, Choice.E => [Edge.st2]
  | Terminal.two, Choice.Z => [Edge.su, Edge.uv, Edge.vw, Edge.wt2]
  | Terminal.three, Choice.E => [Edge.su, Edge.ut3]
  | Terminal.three, Choice.Z => [Edge.su, Edge.uv, Edge.vw, Edge.wt3]

def listedPath (t : Terminal) (p : List Edge) : Prop :=
  p = pathEdges t Choice.E ∨ p = pathEdges t Choice.Z

-- This is the formal path inventory used by the unsplittable model.
theorem path_complete (t : Terminal) (c : Choice) :
    listedPath t (pathEdges t c) := by
  cases t <;> cases c <;> simp [listedPath, pathEdges]

end DGG
