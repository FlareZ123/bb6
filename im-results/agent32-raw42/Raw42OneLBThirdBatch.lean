import Raw42Cut
/-!
Deterministically discovered, original-source finite side-zipper witnesses
within unresolved Raw42 B1=One.
Proofs are conditional on the three explicit transition assignments;
every remaining transition may be arbitrary, including halt.
The trust boundary is the original Lean kernel: each `by decide` proves a
finite Bool fact and `zipCycle_sound` proves actual nonhalting universally.
Do not count these as accepted results until pinned source CI succeeds.
-/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
namespace BB6.Agent32Raw42OneLBThirdBatch
open BB6Coverage BB6.Agent13BlankDelay BB6Coverage.Agent10ZipAudit
abbrev base : PartialMachine := BB6.Agent32Raw42.child
  ⟨true,false,1⟩

private theorem zipper_cover
    (p : PartialMachine) (e k : Nat) (right : Bool) (boundary : Int)
    (hk : 0 < k) (hc : zipCycle p e k right boundary = true) (B : Nat) :
    Cover (WeightedBound B) p := by
  apply Cover.leaf p
  intro m hm
  exact weighted_never B m (zipCycle_sound p e k right boundary hk hc m hm)

/- OneLB: C1=0LA, A1=0LA -/
namespace Leaf000
abbrev p : PartialMachine :=
  refine (refine base (2, true) (some ⟨false,false,0⟩))
    (0, true) (some ⟨false,false,0⟩)
theorem check : zipCycle p 0 10 false 3 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 0 10 false 3 (by decide) check B
#print axioms cover
end Leaf000

/- OneLB: C1=0LA, A1=0LC -/
namespace Leaf001
abbrev p : PartialMachine :=
  refine (refine base (2, true) (some ⟨false,false,0⟩))
    (0, true) (some ⟨false,false,2⟩)
theorem check : zipCycle p 11 1 false (-1) = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 11 1 false (-1) (by decide) check B
#print axioms cover
end Leaf001

/- OneLB: C1=0LA, A1=0LD -/
namespace Leaf002
abbrev p : PartialMachine :=
  refine (refine base (2, true) (some ⟨false,false,0⟩))
    (0, true) (some ⟨false,false,3⟩)
theorem check : zipCycle p 10 1 false (-2) = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 10 1 false (-2) (by decide) check B
#print axioms cover
end Leaf002

/- OneLB: C1=0LA, A1=0RA -/
namespace Leaf003
abbrev p : PartialMachine :=
  refine (refine base (2, true) (some ⟨false,false,0⟩))
    (0, true) (some ⟨false,true,0⟩)
theorem check : zipCycle p 11 6 false 3 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 11 6 false 3 (by decide) check B
#print axioms cover
end Leaf003

/- OneLB: C1=0LA, A1=0RB -/
namespace Leaf004
abbrev p : PartialMachine :=
  refine (refine base (2, true) (some ⟨false,false,0⟩))
    (0, true) (some ⟨false,true,1⟩)
theorem check : zipCycle p 7 19 true (-1) = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 7 19 true (-1) (by decide) check B
#print axioms cover
end Leaf004

/- OneLB: C1=0LA, A1=0RC -/
namespace Leaf005
abbrev p : PartialMachine :=
  refine (refine base (2, true) (some ⟨false,false,0⟩))
    (0, true) (some ⟨false,true,2⟩)
theorem check : zipCycle p 11 1 false 1 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 11 1 false 1 (by decide) check B
#print axioms cover
end Leaf005

/- OneLB: C1=0LA, A1=0RD -/
namespace Leaf006
abbrev p : PartialMachine :=
  refine (refine base (2, true) (some ⟨false,false,0⟩))
    (0, true) (some ⟨false,true,3⟩)
theorem check : zipCycle p 10 1 false 0 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 10 1 false 0 (by decide) check B
#print axioms cover
end Leaf006

/- OneLB: C1=0LA, A1=1LA -/
namespace Leaf007
abbrev p : PartialMachine :=
  refine (refine base (2, true) (some ⟨false,false,0⟩))
    (0, true) (some ⟨true,false,0⟩)
theorem check : zipCycle p 6 6 false 0 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 6 6 false 0 (by decide) check B
#print axioms cover
end Leaf007

/- OneLB: C1=0LA, A1=1LB -/
namespace Leaf008
abbrev p : PartialMachine :=
  refine (refine base (2, true) (some ⟨false,false,0⟩))
    (0, true) (some ⟨true,false,1⟩)
theorem check : zipCycle p 7 3 false 0 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 7 3 false 0 (by decide) check B
#print axioms cover
end Leaf008

/- OneLB: C1=0LA, A1=1LD -/
namespace Leaf009
abbrev p : PartialMachine :=
  refine (refine base (2, true) (some ⟨false,false,0⟩))
    (0, true) (some ⟨true,false,3⟩)
theorem check : zipCycle p 10 1 false (-2) = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 10 1 false (-2) (by decide) check B
#print axioms cover
end Leaf009

/- OneLB: C1=0LA, A1=1RA -/
namespace Leaf010
abbrev p : PartialMachine :=
  refine (refine base (2, true) (some ⟨false,false,0⟩))
    (0, true) (some ⟨true,true,0⟩)
theorem check : zipCycle p 17 7 false 1 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 17 7 false 1 (by decide) check B
#print axioms cover
end Leaf010

/- OneLB: C1=0LA, A1=1RD -/
namespace Leaf011
abbrev p : PartialMachine :=
  refine (refine base (2, true) (some ⟨false,false,0⟩))
    (0, true) (some ⟨true,true,3⟩)
theorem check : zipCycle p 1 14 false 3 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 1 14 false 3 (by decide) check B
#print axioms cover
end Leaf011

/- OneLB: C1=0LE, E1=0LA -/
namespace Leaf012
abbrev p : PartialMachine :=
  refine (refine base (2, true) (some ⟨false,false,4⟩))
    (4, true) (some ⟨false,false,0⟩)
theorem check : zipCycle p 0 10 false 3 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 0 10 false 3 (by decide) check B
#print axioms cover
end Leaf012

/- OneLB: C1=0LE, E1=0LC -/
namespace Leaf013
abbrev p : PartialMachine :=
  refine (refine base (2, true) (some ⟨false,false,4⟩))
    (4, true) (some ⟨false,false,2⟩)
theorem check : zipCycle p 11 1 false (-1) = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 11 1 false (-1) (by decide) check B
#print axioms cover
end Leaf013

/- OneLB: C1=0LE, E1=0LD -/
namespace Leaf014
abbrev p : PartialMachine :=
  refine (refine base (2, true) (some ⟨false,false,4⟩))
    (4, true) (some ⟨false,false,3⟩)
theorem check : zipCycle p 10 1 false (-2) = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 10 1 false (-2) (by decide) check B
#print axioms cover
end Leaf014

/- OneLB: C1=0LE, E1=0RA -/
namespace Leaf015
abbrev p : PartialMachine :=
  refine (refine base (2, true) (some ⟨false,false,4⟩))
    (4, true) (some ⟨false,true,0⟩)
theorem check : zipCycle p 11 6 false 3 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 11 6 false 3 (by decide) check B
#print axioms cover
end Leaf015

/- OneLB: C1=0LE, E1=0RB -/
namespace Leaf016
abbrev p : PartialMachine :=
  refine (refine base (2, true) (some ⟨false,false,4⟩))
    (4, true) (some ⟨false,true,1⟩)
theorem check : zipCycle p 7 19 true (-1) = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 7 19 true (-1) (by decide) check B
#print axioms cover
end Leaf016

/- OneLB: C1=0LE, E1=0RC -/
namespace Leaf017
abbrev p : PartialMachine :=
  refine (refine base (2, true) (some ⟨false,false,4⟩))
    (4, true) (some ⟨false,true,2⟩)
theorem check : zipCycle p 11 1 false 1 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 11 1 false 1 (by decide) check B
#print axioms cover
end Leaf017

/- OneLB: C1=0LE, E1=0RD -/
namespace Leaf018
abbrev p : PartialMachine :=
  refine (refine base (2, true) (some ⟨false,false,4⟩))
    (4, true) (some ⟨false,true,3⟩)
theorem check : zipCycle p 10 1 false 0 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 10 1 false 0 (by decide) check B
#print axioms cover
end Leaf018

/- OneLB: C1=0LE, E1=1LA -/
namespace Leaf019
abbrev p : PartialMachine :=
  refine (refine base (2, true) (some ⟨false,false,4⟩))
    (4, true) (some ⟨true,false,0⟩)
theorem check : zipCycle p 6 6 false 0 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 6 6 false 0 (by decide) check B
#print axioms cover
end Leaf019

/- OneLB: C1=0LE, E1=1LB -/
namespace Leaf020
abbrev p : PartialMachine :=
  refine (refine base (2, true) (some ⟨false,false,4⟩))
    (4, true) (some ⟨true,false,1⟩)
theorem check : zipCycle p 7 3 false 0 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 7 3 false 0 (by decide) check B
#print axioms cover
end Leaf020

/- OneLB: C1=0LE, E1=1LD -/
namespace Leaf021
abbrev p : PartialMachine :=
  refine (refine base (2, true) (some ⟨false,false,4⟩))
    (4, true) (some ⟨true,false,3⟩)
theorem check : zipCycle p 10 1 false (-2) = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 10 1 false (-2) (by decide) check B
#print axioms cover
end Leaf021

/- OneLB: C1=0LE, E1=1RA -/
namespace Leaf022
abbrev p : PartialMachine :=
  refine (refine base (2, true) (some ⟨false,false,4⟩))
    (4, true) (some ⟨true,true,0⟩)
theorem check : zipCycle p 17 7 false 1 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 17 7 false 1 (by decide) check B
#print axioms cover
end Leaf022

/- OneLB: C1=0LE, E1=1RD -/
namespace Leaf023
abbrev p : PartialMachine :=
  refine (refine base (2, true) (some ⟨false,false,4⟩))
    (4, true) (some ⟨true,true,3⟩)
theorem check : zipCycle p 1 14 false 3 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 1 14 false 3 (by decide) check B
#print axioms cover
end Leaf023

/- OneLB: C1=0LF, F1=0LA -/
namespace Leaf024
abbrev p : PartialMachine :=
  refine (refine base (2, true) (some ⟨false,false,5⟩))
    (5, true) (some ⟨false,false,0⟩)
theorem check : zipCycle p 0 10 false 3 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 0 10 false 3 (by decide) check B
#print axioms cover
end Leaf024

/- OneLB: C1=0LF, F1=0LC -/
namespace Leaf025
abbrev p : PartialMachine :=
  refine (refine base (2, true) (some ⟨false,false,5⟩))
    (5, true) (some ⟨false,false,2⟩)
theorem check : zipCycle p 11 1 false (-1) = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 11 1 false (-1) (by decide) check B
#print axioms cover
end Leaf025

/- OneLB: C1=0LF, F1=0LD -/
namespace Leaf026
abbrev p : PartialMachine :=
  refine (refine base (2, true) (some ⟨false,false,5⟩))
    (5, true) (some ⟨false,false,3⟩)
theorem check : zipCycle p 10 1 false (-2) = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 10 1 false (-2) (by decide) check B
#print axioms cover
end Leaf026

/- OneLB: C1=0LF, F1=0RA -/
namespace Leaf027
abbrev p : PartialMachine :=
  refine (refine base (2, true) (some ⟨false,false,5⟩))
    (5, true) (some ⟨false,true,0⟩)
theorem check : zipCycle p 11 6 false 3 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 11 6 false 3 (by decide) check B
#print axioms cover
end Leaf027

/- OneLB: C1=0LF, F1=0RB -/
namespace Leaf028
abbrev p : PartialMachine :=
  refine (refine base (2, true) (some ⟨false,false,5⟩))
    (5, true) (some ⟨false,true,1⟩)
theorem check : zipCycle p 7 19 true (-1) = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 7 19 true (-1) (by decide) check B
#print axioms cover
end Leaf028

/- OneLB: C1=0LF, F1=0RC -/
namespace Leaf029
abbrev p : PartialMachine :=
  refine (refine base (2, true) (some ⟨false,false,5⟩))
    (5, true) (some ⟨false,true,2⟩)
theorem check : zipCycle p 11 1 false 1 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 11 1 false 1 (by decide) check B
#print axioms cover
end Leaf029

/- OneLB: C1=0LF, F1=0RD -/
namespace Leaf030
abbrev p : PartialMachine :=
  refine (refine base (2, true) (some ⟨false,false,5⟩))
    (5, true) (some ⟨false,true,3⟩)
theorem check : zipCycle p 10 1 false 0 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 10 1 false 0 (by decide) check B
#print axioms cover
end Leaf030

/- OneLB: C1=0LF, F1=1LA -/
namespace Leaf031
abbrev p : PartialMachine :=
  refine (refine base (2, true) (some ⟨false,false,5⟩))
    (5, true) (some ⟨true,false,0⟩)
theorem check : zipCycle p 6 6 false 0 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 6 6 false 0 (by decide) check B
#print axioms cover
end Leaf031

/- OneLB: C1=0LF, F1=1LB -/
namespace Leaf032
abbrev p : PartialMachine :=
  refine (refine base (2, true) (some ⟨false,false,5⟩))
    (5, true) (some ⟨true,false,1⟩)
theorem check : zipCycle p 7 3 false 0 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 7 3 false 0 (by decide) check B
#print axioms cover
end Leaf032

/- OneLB: C1=0LF, F1=1LD -/
namespace Leaf033
abbrev p : PartialMachine :=
  refine (refine base (2, true) (some ⟨false,false,5⟩))
    (5, true) (some ⟨true,false,3⟩)
theorem check : zipCycle p 10 1 false (-2) = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 10 1 false (-2) (by decide) check B
#print axioms cover
end Leaf033

/- OneLB: C1=0LF, F1=1RA -/
namespace Leaf034
abbrev p : PartialMachine :=
  refine (refine base (2, true) (some ⟨false,false,5⟩))
    (5, true) (some ⟨true,true,0⟩)
theorem check : zipCycle p 17 7 false 1 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 17 7 false 1 (by decide) check B
#print axioms cover
end Leaf034

/- OneLB: C1=0LF, F1=1RD -/
namespace Leaf035
abbrev p : PartialMachine :=
  refine (refine base (2, true) (some ⟨false,false,5⟩))
    (5, true) (some ⟨true,true,3⟩)
theorem check : zipCycle p 1 14 false 3 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 1 14 false 3 (by decide) check B
#print axioms cover
end Leaf035

/- OneLB: C1=0RA, A1=0LA -/
namespace Leaf036
abbrev p : PartialMachine :=
  refine (refine base (2, true) (some ⟨false,true,0⟩))
    (0, true) (some ⟨false,false,0⟩)
theorem check : zipCycle p 0 18 true (-1) = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 0 18 true (-1) (by decide) check B
#print axioms cover
end Leaf036

/- OneLB: C1=0RA, A1=0LC -/
namespace Leaf037
abbrev p : PartialMachine :=
  refine (refine base (2, true) (some ⟨false,true,0⟩))
    (0, true) (some ⟨false,false,2⟩)
theorem check : zipCycle p 2 13 false 3 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 2 13 false 3 (by decide) check B
#print axioms cover
end Leaf037

/- OneLB: C1=0RA, A1=0LD -/
namespace Leaf038
abbrev p : PartialMachine :=
  refine (refine base (2, true) (some ⟨false,true,0⟩))
    (0, true) (some ⟨false,false,3⟩)
theorem check : zipCycle p 4 11 false 2 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 4 11 false 2 (by decide) check B
#print axioms cover
end Leaf038

/- OneLB: C1=0RA, A1=0RA -/
namespace Leaf039
abbrev p : PartialMachine :=
  refine (refine base (2, true) (some ⟨false,true,0⟩))
    (0, true) (some ⟨false,true,0⟩)
theorem check : zipCycle p 0 16 true (-1) = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 0 16 true (-1) (by decide) check B
#print axioms cover
end Leaf039

/- OneLB: C1=0RA, A1=0RB -/
namespace Leaf040
abbrev p : PartialMachine :=
  refine (refine base (2, true) (some ⟨false,true,0⟩))
    (0, true) (some ⟨false,true,1⟩)
theorem check : zipCycle p 0 18 true (-1) = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 0 18 true (-1) (by decide) check B
#print axioms cover
end Leaf040

/- OneLB: C1=0RA, A1=0RC -/
namespace Leaf041
abbrev p : PartialMachine :=
  refine (refine base (2, true) (some ⟨false,true,0⟩))
    (0, true) (some ⟨false,true,2⟩)
theorem check : zipCycle p 0 16 true (-1) = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 0 16 true (-1) (by decide) check B
#print axioms cover
end Leaf041

/- OneLB: C1=0RA, A1=1LA -/
namespace Leaf042
abbrev p : PartialMachine :=
  refine (refine base (2, true) (some ⟨false,true,0⟩))
    (0, true) (some ⟨true,false,0⟩)
theorem check : zipCycle p 17 7 false 1 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 17 7 false 1 (by decide) check B
#print axioms cover
end Leaf042

/- OneLB: C1=0RA, A1=1LB -/
namespace Leaf043
abbrev p : PartialMachine :=
  refine (refine base (2, true) (some ⟨false,true,0⟩))
    (0, true) (some ⟨true,false,1⟩)
theorem check : zipCycle p 0 20 true (-1) = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 0 20 true (-1) (by decide) check B
#print axioms cover
end Leaf043

/- OneLB: C1=0RA, A1=1LD -/
namespace Leaf044
abbrev p : PartialMachine :=
  refine (refine base (2, true) (some ⟨false,true,0⟩))
    (0, true) (some ⟨true,false,3⟩)
theorem check : zipCycle p 4 11 false 2 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 4 11 false 2 (by decide) check B
#print axioms cover
end Leaf044

/- OneLB: C1=0RA, A1=1RB -/
namespace Leaf045
abbrev p : PartialMachine :=
  refine (refine base (2, true) (some ⟨false,true,0⟩))
    (0, true) (some ⟨true,true,1⟩)
theorem check : zipCycle p 1 19 true (-1) = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 1 19 true (-1) (by decide) check B
#print axioms cover
end Leaf045

/- OneLB: C1=0RA, A1=1RC -/
namespace Leaf046
abbrev p : PartialMachine :=
  refine (refine base (2, true) (some ⟨false,true,0⟩))
    (0, true) (some ⟨true,true,2⟩)
theorem check : zipCycle p 0 16 true (-1) = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 0 16 true (-1) (by decide) check B
#print axioms cover
end Leaf046

/- OneLB: C1=0RA, A1=1RD -/
namespace Leaf047
abbrev p : PartialMachine :=
  refine (refine base (2, true) (some ⟨false,true,0⟩))
    (0, true) (some ⟨true,true,3⟩)
theorem check : zipCycle p 0 19 true (-1) = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 0 19 true (-1) (by decide) check B
#print axioms cover
end Leaf047

/- OneLB: C1=0RE, E0=0LD -/
namespace Leaf048
abbrev p : PartialMachine :=
  refine (refine base (2, true) (some ⟨false,true,4⟩))
    (4, false) (some ⟨false,false,3⟩)
theorem check : zipCycle p 1 14 false 3 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 1 14 false 3 (by decide) check B
#print axioms cover
end Leaf048

/- OneLB: C1=0RE, E0=0RD -/
namespace Leaf049
abbrev p : PartialMachine :=
  refine (refine base (2, true) (some ⟨false,true,4⟩))
    (4, false) (some ⟨false,true,3⟩)
theorem check : zipCycle p 1 13 true (-1) = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 1 13 true (-1) (by decide) check B
#print axioms cover
end Leaf049

/- OneLB: C1=0RF, F0=0LD -/
namespace Leaf050
abbrev p : PartialMachine :=
  refine (refine base (2, true) (some ⟨false,true,5⟩))
    (5, false) (some ⟨false,false,3⟩)
theorem check : zipCycle p 1 14 false 3 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 1 14 false 3 (by decide) check B
#print axioms cover
end Leaf050

/- OneLB: C1=0RF, F0=0RD -/
namespace Leaf051
abbrev p : PartialMachine :=
  refine (refine base (2, true) (some ⟨false,true,5⟩))
    (5, false) (some ⟨false,true,3⟩)
theorem check : zipCycle p 1 13 true (-1) = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 1 13 true (-1) (by decide) check B
#print axioms cover
end Leaf051

/- OneLB: C1=1LA, A1=0LB -/
namespace Leaf052
abbrev p : PartialMachine :=
  refine (refine base (2, true) (some ⟨true,false,0⟩))
    (0, true) (some ⟨false,false,1⟩)
theorem check : zipCycle p 1 12 false 3 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 1 12 false 3 (by decide) check B
#print axioms cover
end Leaf052

/- OneLB: C1=1LA, A1=0LC -/
namespace Leaf053
abbrev p : PartialMachine :=
  refine (refine base (2, true) (some ⟨true,false,0⟩))
    (0, true) (some ⟨false,false,2⟩)
theorem check : zipCycle p 11 1 false (-1) = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 11 1 false (-1) (by decide) check B
#print axioms cover
end Leaf053

/- OneLB: C1=1LA, A1=0LD -/
namespace Leaf054
abbrev p : PartialMachine :=
  refine (refine base (2, true) (some ⟨true,false,0⟩))
    (0, true) (some ⟨false,false,3⟩)
theorem check : zipCycle p 10 1 false (-2) = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 10 1 false (-2) (by decide) check B
#print axioms cover
end Leaf054

/- OneLB: C1=1LA, A1=0RA -/
namespace Leaf055
abbrev p : PartialMachine :=
  refine (refine base (2, true) (some ⟨true,false,0⟩))
    (0, true) (some ⟨false,true,0⟩)
theorem check : zipCycle p 0 20 true (-1) = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 0 20 true (-1) (by decide) check B
#print axioms cover
end Leaf055

/- OneLB: C1=1LA, A1=0RB -/
namespace Leaf056
abbrev p : PartialMachine :=
  refine (refine base (2, true) (some ⟨true,false,0⟩))
    (0, true) (some ⟨false,true,1⟩)
theorem check : zipCycle p 6 4 false 0 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 6 4 false 0 (by decide) check B
#print axioms cover
end Leaf056

/- OneLB: C1=1LA, A1=0RC -/
namespace Leaf057
abbrev p : PartialMachine :=
  refine (refine base (2, true) (some ⟨true,false,0⟩))
    (0, true) (some ⟨false,true,2⟩)
theorem check : zipCycle p 6 7 false 0 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 6 7 false 0 (by decide) check B
#print axioms cover
end Leaf057

/- OneLB: C1=1LA, A1=1LA -/
namespace Leaf058
abbrev p : PartialMachine :=
  refine (refine base (2, true) (some ⟨true,false,0⟩))
    (0, true) (some ⟨true,false,0⟩)
theorem check : zipCycle p 6 6 false 0 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 6 6 false 0 (by decide) check B
#print axioms cover
end Leaf058

/- OneLB: C1=1LA, A1=1LB -/
namespace Leaf059
abbrev p : PartialMachine :=
  refine (refine base (2, true) (some ⟨true,false,0⟩))
    (0, true) (some ⟨true,false,1⟩)
theorem check : zipCycle p 7 3 false 0 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 7 3 false 0 (by decide) check B
#print axioms cover
end Leaf059

/- OneLB: C1=1LA, A1=1LC -/
namespace Leaf060
abbrev p : PartialMachine :=
  refine (refine base (2, true) (some ⟨true,false,0⟩))
    (0, true) (some ⟨true,false,2⟩)
theorem check : zipCycle p 1 14 false 3 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 1 14 false 3 (by decide) check B
#print axioms cover
end Leaf060

/- OneLB: C1=1LA, A1=1LD -/
namespace Leaf061
abbrev p : PartialMachine :=
  refine (refine base (2, true) (some ⟨true,false,0⟩))
    (0, true) (some ⟨true,false,3⟩)
theorem check : zipCycle p 10 1 false (-2) = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 10 1 false (-2) (by decide) check B
#print axioms cover
end Leaf061

/- OneLB: C1=1LA, A1=1RB -/
namespace Leaf062
abbrev p : PartialMachine :=
  refine (refine base (2, true) (some ⟨true,false,0⟩))
    (0, true) (some ⟨true,true,1⟩)
theorem check : zipCycle p 6 5 false 0 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 6 5 false 0 (by decide) check B
#print axioms cover
end Leaf062

/- OneLB: C1=1LA, A1=1RC -/
namespace Leaf063
abbrev p : PartialMachine :=
  refine (refine base (2, true) (some ⟨true,false,0⟩))
    (0, true) (some ⟨true,true,2⟩)
theorem check : zipCycle p 8 2 false 0 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 8 2 false 0 (by decide) check B
#print axioms cover
end Leaf063

/- OneLB: C1=1LA, A1=1RD -/
namespace Leaf064
abbrev p : PartialMachine :=
  refine (refine base (2, true) (some ⟨true,false,0⟩))
    (0, true) (some ⟨true,true,3⟩)
theorem check : zipCycle p 5 5 false 1 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 5 5 false 1 (by decide) check B
#print axioms cover
end Leaf064

/- OneLB: C1=1LE, E1=0LB -/
namespace Leaf065
abbrev p : PartialMachine :=
  refine (refine base (2, true) (some ⟨true,false,4⟩))
    (4, true) (some ⟨false,false,1⟩)
theorem check : zipCycle p 1 12 false 3 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 1 12 false 3 (by decide) check B
#print axioms cover
end Leaf065

/- OneLB: C1=1LE, E1=0LC -/
namespace Leaf066
abbrev p : PartialMachine :=
  refine (refine base (2, true) (some ⟨true,false,4⟩))
    (4, true) (some ⟨false,false,2⟩)
theorem check : zipCycle p 11 1 false (-1) = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 11 1 false (-1) (by decide) check B
#print axioms cover
end Leaf066

/- OneLB: C1=1LE, E1=0LD -/
namespace Leaf067
abbrev p : PartialMachine :=
  refine (refine base (2, true) (some ⟨true,false,4⟩))
    (4, true) (some ⟨false,false,3⟩)
theorem check : zipCycle p 10 1 false (-2) = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 10 1 false (-2) (by decide) check B
#print axioms cover
end Leaf067

/- OneLB: C1=1LE, E1=0RB -/
namespace Leaf068
abbrev p : PartialMachine :=
  refine (refine base (2, true) (some ⟨true,false,4⟩))
    (4, true) (some ⟨false,true,1⟩)
theorem check : zipCycle p 6 4 false 0 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 6 4 false 0 (by decide) check B
#print axioms cover
end Leaf068

/- OneLB: C1=1LE, E1=1LA -/
namespace Leaf069
abbrev p : PartialMachine :=
  refine (refine base (2, true) (some ⟨true,false,4⟩))
    (4, true) (some ⟨true,false,0⟩)
theorem check : zipCycle p 6 6 false 0 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 6 6 false 0 (by decide) check B
#print axioms cover
end Leaf069

/- OneLB: C1=1LE, E1=1LB -/
namespace Leaf070
abbrev p : PartialMachine :=
  refine (refine base (2, true) (some ⟨true,false,4⟩))
    (4, true) (some ⟨true,false,1⟩)
theorem check : zipCycle p 7 3 false 0 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 7 3 false 0 (by decide) check B
#print axioms cover
end Leaf070

/- OneLB: C1=1LE, E1=1LC -/
namespace Leaf071
abbrev p : PartialMachine :=
  refine (refine base (2, true) (some ⟨true,false,4⟩))
    (4, true) (some ⟨true,false,2⟩)
theorem check : zipCycle p 1 14 false 3 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 1 14 false 3 (by decide) check B
#print axioms cover
end Leaf071

/- OneLB: C1=1LE, E1=1LD -/
namespace Leaf072
abbrev p : PartialMachine :=
  refine (refine base (2, true) (some ⟨true,false,4⟩))
    (4, true) (some ⟨true,false,3⟩)
theorem check : zipCycle p 10 1 false (-2) = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 10 1 false (-2) (by decide) check B
#print axioms cover
end Leaf072

/- OneLB: C1=1LE, E1=1RB -/
namespace Leaf073
abbrev p : PartialMachine :=
  refine (refine base (2, true) (some ⟨true,false,4⟩))
    (4, true) (some ⟨true,true,1⟩)
theorem check : zipCycle p 6 5 false 0 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 6 5 false 0 (by decide) check B
#print axioms cover
end Leaf073

/- OneLB: C1=1LE, E1=1RC -/
namespace Leaf074
abbrev p : PartialMachine :=
  refine (refine base (2, true) (some ⟨true,false,4⟩))
    (4, true) (some ⟨true,true,2⟩)
theorem check : zipCycle p 8 2 false 0 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 8 2 false 0 (by decide) check B
#print axioms cover
end Leaf074

/- OneLB: C1=1LE, E1=1RD -/
namespace Leaf075
abbrev p : PartialMachine :=
  refine (refine base (2, true) (some ⟨true,false,4⟩))
    (4, true) (some ⟨true,true,3⟩)
theorem check : zipCycle p 5 5 false 1 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 5 5 false 1 (by decide) check B
#print axioms cover
end Leaf075

/- OneLB: C1=1LF, F1=0LB -/
namespace Leaf076
abbrev p : PartialMachine :=
  refine (refine base (2, true) (some ⟨true,false,5⟩))
    (5, true) (some ⟨false,false,1⟩)
theorem check : zipCycle p 1 12 false 3 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 1 12 false 3 (by decide) check B
#print axioms cover
end Leaf076

/- OneLB: C1=1LF, F1=0LC -/
namespace Leaf077
abbrev p : PartialMachine :=
  refine (refine base (2, true) (some ⟨true,false,5⟩))
    (5, true) (some ⟨false,false,2⟩)
theorem check : zipCycle p 11 1 false (-1) = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 11 1 false (-1) (by decide) check B
#print axioms cover
end Leaf077

/- OneLB: C1=1LF, F1=0LD -/
namespace Leaf078
abbrev p : PartialMachine :=
  refine (refine base (2, true) (some ⟨true,false,5⟩))
    (5, true) (some ⟨false,false,3⟩)
theorem check : zipCycle p 10 1 false (-2) = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 10 1 false (-2) (by decide) check B
#print axioms cover
end Leaf078

/- OneLB: C1=1LF, F1=0RB -/
namespace Leaf079
abbrev p : PartialMachine :=
  refine (refine base (2, true) (some ⟨true,false,5⟩))
    (5, true) (some ⟨false,true,1⟩)
theorem check : zipCycle p 6 4 false 0 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 6 4 false 0 (by decide) check B
#print axioms cover
end Leaf079

/- OneLB: C1=1LF, F1=1LA -/
namespace Leaf080
abbrev p : PartialMachine :=
  refine (refine base (2, true) (some ⟨true,false,5⟩))
    (5, true) (some ⟨true,false,0⟩)
theorem check : zipCycle p 6 6 false 0 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 6 6 false 0 (by decide) check B
#print axioms cover
end Leaf080

/- OneLB: C1=1LF, F1=1LB -/
namespace Leaf081
abbrev p : PartialMachine :=
  refine (refine base (2, true) (some ⟨true,false,5⟩))
    (5, true) (some ⟨true,false,1⟩)
theorem check : zipCycle p 7 3 false 0 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 7 3 false 0 (by decide) check B
#print axioms cover
end Leaf081

/- OneLB: C1=1LF, F1=1LC -/
namespace Leaf082
abbrev p : PartialMachine :=
  refine (refine base (2, true) (some ⟨true,false,5⟩))
    (5, true) (some ⟨true,false,2⟩)
theorem check : zipCycle p 1 14 false 3 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 1 14 false 3 (by decide) check B
#print axioms cover
end Leaf082

/- OneLB: C1=1LF, F1=1LD -/
namespace Leaf083
abbrev p : PartialMachine :=
  refine (refine base (2, true) (some ⟨true,false,5⟩))
    (5, true) (some ⟨true,false,3⟩)
theorem check : zipCycle p 10 1 false (-2) = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 10 1 false (-2) (by decide) check B
#print axioms cover
end Leaf083

/- OneLB: C1=1LF, F1=1RB -/
namespace Leaf084
abbrev p : PartialMachine :=
  refine (refine base (2, true) (some ⟨true,false,5⟩))
    (5, true) (some ⟨true,true,1⟩)
theorem check : zipCycle p 6 5 false 0 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 6 5 false 0 (by decide) check B
#print axioms cover
end Leaf084

/- OneLB: C1=1LF, F1=1RC -/
namespace Leaf085
abbrev p : PartialMachine :=
  refine (refine base (2, true) (some ⟨true,false,5⟩))
    (5, true) (some ⟨true,true,2⟩)
theorem check : zipCycle p 8 2 false 0 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 8 2 false 0 (by decide) check B
#print axioms cover
end Leaf085

/- OneLB: C1=1LF, F1=1RD -/
namespace Leaf086
abbrev p : PartialMachine :=
  refine (refine base (2, true) (some ⟨true,false,5⟩))
    (5, true) (some ⟨true,true,3⟩)
theorem check : zipCycle p 5 5 false 1 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 5 5 false 1 (by decide) check B
#print axioms cover
end Leaf086

/- OneLB: C1=1RA, A1=0LA -/
namespace Leaf087
abbrev p : PartialMachine :=
  refine (refine base (2, true) (some ⟨true,true,0⟩))
    (0, true) (some ⟨false,false,0⟩)
theorem check : zipCycle p 0 19 false 3 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 0 19 false 3 (by decide) check B
#print axioms cover
end Leaf087

/- OneLB: C1=1RA, A1=0LB -/
namespace Leaf088
abbrev p : PartialMachine :=
  refine (refine base (2, true) (some ⟨true,true,0⟩))
    (0, true) (some ⟨false,false,1⟩)
theorem check : zipCycle p 12 5 false 0 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 12 5 false 0 (by decide) check B
#print axioms cover
end Leaf088

/- OneLB: C1=1RA, A1=0LC -/
namespace Leaf089
abbrev p : PartialMachine :=
  refine (refine base (2, true) (some ⟨true,true,0⟩))
    (0, true) (some ⟨false,false,2⟩)
theorem check : zipCycle p 8 9 false 2 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 8 9 false 2 (by decide) check B
#print axioms cover
end Leaf089

/- OneLB: C1=1RA, A1=0LD -/
namespace Leaf090
abbrev p : PartialMachine :=
  refine (refine base (2, true) (some ⟨true,true,0⟩))
    (0, true) (some ⟨false,false,3⟩)
theorem check : zipCycle p 10 16 false 2 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 10 16 false 2 (by decide) check B
#print axioms cover
end Leaf090

/- OneLB: C1=1RA, A1=0RA -/
namespace Leaf091
abbrev p : PartialMachine :=
  refine (refine base (2, true) (some ⟨true,true,0⟩))
    (0, true) (some ⟨false,true,0⟩)
theorem check : zipCycle p 0 20 true (-2) = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 0 20 true (-2) (by decide) check B
#print axioms cover
end Leaf091

/- OneLB: C1=1RA, A1=0RC -/
namespace Leaf092
abbrev p : PartialMachine :=
  refine (refine base (2, true) (some ⟨true,true,0⟩))
    (0, true) (some ⟨false,true,2⟩)
theorem check : zipCycle p 55 54 true 3 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 55 54 true 3 (by decide) check B
#print axioms cover
end Leaf092

/- OneLB: C1=1RA, A1=1LA -/
namespace Leaf093
abbrev p : PartialMachine :=
  refine (refine base (2, true) (some ⟨true,true,0⟩))
    (0, true) (some ⟨true,false,0⟩)
theorem check : zipCycle p 12 8 false 0 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 12 8 false 0 (by decide) check B
#print axioms cover
end Leaf093

/- OneLB: C1=1RA, A1=1LB -/
namespace Leaf094
abbrev p : PartialMachine :=
  refine (refine base (2, true) (some ⟨true,true,0⟩))
    (0, true) (some ⟨true,false,1⟩)
theorem check : zipCycle p 12 5 false 0 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 12 5 false 0 (by decide) check B
#print axioms cover
end Leaf094

/- OneLB: C1=1RA, A1=1LC -/
namespace Leaf095
abbrev p : PartialMachine :=
  refine (refine base (2, true) (some ⟨true,true,0⟩))
    (0, true) (some ⟨true,false,2⟩)
theorem check : zipCycle p 15 2 false 0 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 15 2 false 0 (by decide) check B
#print axioms cover
end Leaf095

/- OneLB: C1=1RA, A1=1LD -/
namespace Leaf096
abbrev p : PartialMachine :=
  refine (refine base (2, true) (some ⟨true,true,0⟩))
    (0, true) (some ⟨true,false,3⟩)
theorem check : zipCycle p 5 12 false 2 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 5 12 false 2 (by decide) check B
#print axioms cover
end Leaf096

/- OneLB: C1=1RA, A1=1RB -/
namespace Leaf097
abbrev p : PartialMachine :=
  refine (refine base (2, true) (some ⟨true,true,0⟩))
    (0, true) (some ⟨true,true,1⟩)
theorem check : zipCycle p 10 7 false 2 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 10 7 false 2 (by decide) check B
#print axioms cover
end Leaf097

/- OneLB: C1=1RA, A1=1RD -/
namespace Leaf098
abbrev p : PartialMachine :=
  refine (refine base (2, true) (some ⟨true,true,0⟩))
    (0, true) (some ⟨true,true,3⟩)
theorem check : zipCycle p 11 7 false 1 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 11 7 false 1 (by decide) check B
#print axioms cover
end Leaf098

/- OneLB: C1=1RE, E0=0LC -/
namespace Leaf099
abbrev p : PartialMachine :=
  refine (refine base (2, true) (some ⟨true,true,4⟩))
    (4, false) (some ⟨false,false,2⟩)
theorem check : zipCycle p 8 2 false 1 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 8 2 false 1 (by decide) check B
#print axioms cover
end Leaf099

/- OneLB: C1=1RE, E0=0LD -/
namespace Leaf100
abbrev p : PartialMachine :=
  refine (refine base (2, true) (some ⟨true,true,4⟩))
    (4, false) (some ⟨false,false,3⟩)
theorem check : zipCycle p 5 5 false 1 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 5 5 false 1 (by decide) check B
#print axioms cover
end Leaf100

/- OneLB: C1=1RE, E0=1LD -/
namespace Leaf101
abbrev p : PartialMachine :=
  refine (refine base (2, true) (some ⟨true,true,4⟩))
    (4, false) (some ⟨true,false,3⟩)
theorem check : zipCycle p 5 5 false 1 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 5 5 false 1 (by decide) check B
#print axioms cover
end Leaf101

/- OneLB: C1=1RF, F0=0LC -/
namespace Leaf102
abbrev p : PartialMachine :=
  refine (refine base (2, true) (some ⟨true,true,5⟩))
    (5, false) (some ⟨false,false,2⟩)
theorem check : zipCycle p 8 2 false 1 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 8 2 false 1 (by decide) check B
#print axioms cover
end Leaf102

/- OneLB: C1=1RF, F0=0LD -/
namespace Leaf103
abbrev p : PartialMachine :=
  refine (refine base (2, true) (some ⟨true,true,5⟩))
    (5, false) (some ⟨false,false,3⟩)
theorem check : zipCycle p 5 5 false 1 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 5 5 false 1 (by decide) check B
#print axioms cover
end Leaf103

/- OneLB: C1=1RF, F0=1LD -/
namespace Leaf104
abbrev p : PartialMachine :=
  refine (refine base (2, true) (some ⟨true,true,5⟩))
    (5, false) (some ⟨true,false,3⟩)
theorem check : zipCycle p 5 5 false 1 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 5 5 false 1 (by decide) check B
#print axioms cover
end Leaf104

end BB6.Agent32Raw42OneLBThirdBatch
