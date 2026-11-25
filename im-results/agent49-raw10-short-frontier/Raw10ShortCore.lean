import Raw10BoxBridge
import FiniteHalting
import WeightedFirstOneCover
import SideCycle

namespace BB6.Agent49Raw10Short
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent50RootFrontier
open BB6Coverage.Agent50SideCycle

/-- 0 is wildcard, 25 is assigned halt, 1..24 index allMoves. -/
def decode (x : Nat) : Option Transition :=
  if x = 0 then none else if x = 25 then some none
  else (allMoves[x-1]?).map some

def table (r : List Nat) : PartialMachine := unpackTable (r.map decode)

inductive Witness where
  | halt (n : Nat)
  | cycle (entry period : Nat) (right : Bool) (boundary : Int)

abbrev Leaf := List Nat × Witness

def check (l : Leaf) : Bool :=
  match l.2 with
  | .halt n => decide (n+1 ≤ 7009) && finiteHaltCheck (table l.1) n
  | .cycle e p r b => decide (0 < p) && fastSideCycleCheck (table l.1) e p r b

theorem check_sound (l : Leaf) (h : check l = true) :
    ∀ m, compatible (table l.1) m → WeightedBound 7014 m := by
  rcases l with ⟨row,w⟩
  cases w with
  | halt n =>
    have hh : n+1 ≤ 7009 ∧ finiteHaltCheck (table row) n = true := by
      simpa [check, Bool.and_eq_true] using h
    intro m hm
    exact weighted_of_margin 7014 m
      ((finiteHaltCheck_sound (table row) n 7009 hh.1 hh.2).sound m hm) (by decide)
  | cycle e p r b =>
    have hh : 0 < p ∧ fastSideCycleCheck (table row) e p r b = true := by
      simpa [check, Bool.and_eq_true] using h
    intro m hm
    exact weighted_of_never 7014 m (fastSideCycleCheck_sound (table row) e p r b hh.1 hh.2 m hm)

def haltC1 : PartialMachine := table [8,0,11,0,0,25,0,0,0,0,0,0]
theorem haltC1_bound : ∀ m, compatible haltC1 m → WeightedBound 8 m := by
  intro m hm
  exact weighted_of_margin 8 m
    ((finiteHaltCheck_sound haltC1 2 3 (by decide) (by decide)).sound m hm) (by decide)

#print axioms check_sound
#print axioms haltC1_bound
end BB6.Agent49Raw10Short
