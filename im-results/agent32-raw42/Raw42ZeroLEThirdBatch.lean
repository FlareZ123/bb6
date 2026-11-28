import Raw42Cut
/-!
Deterministically discovered, original-source finite side-zipper witnesses
within unresolved Raw42 B1=Zer.
Proofs are conditional on the three explicit transition assignments;
every remaining transition may be arbitrary, including halt.
The trust boundary is the original Lean kernel: each `by decide` proves a
finite Bool fact and `zipCycle_sound` proves actual nonhalting universally.
Do not count these as accepted results until pinned source CI succeeds.
-/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
namespace BB6.Agent32Raw42ZeroLEThirdBatch
open BB6Coverage BB6.Agent13BlankDelay BB6Coverage.Agent10ZipAudit
abbrev base : PartialMachine := BB6.Agent32Raw42.child
  ⟨false,false,4⟩

private theorem zipper_cover
    (p : PartialMachine) (e k : Nat) (right : Bool) (boundary : Int)
    (hk : 0 < k) (hc : zipCycle p e k right boundary = true) (B : Nat) :
    Cover (WeightedBound B) p := by
  apply Cover.leaf p
  intro m hm
  exact weighted_never B m (zipCycle_sound p e k right boundary hk hc m hm)

/- ZeroLE: E0=0LB, E1=0LA -/
namespace Leaf000
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨false,false,1⟩))
    (4, true) (some ⟨false,false,0⟩)
theorem check : zipCycle p 0 26 false 3 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 0 26 false 3 (by decide) check B
#print axioms cover
end Leaf000

/- ZeroLE: E0=0LB, E1=0LB -/
namespace Leaf001
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨false,false,1⟩))
    (4, true) (some ⟨false,false,1⟩)
theorem check : zipCycle p 8 18 false 1 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 8 18 false 1 (by decide) check B
#print axioms cover
end Leaf001

/- ZeroLE: E0=0LB, E1=0LC -/
namespace Leaf002
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨false,false,1⟩))
    (4, true) (some ⟨false,false,2⟩)
theorem check : zipCycle p 27 1 false (-3) = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 27 1 false (-3) (by decide) check B
#print axioms cover
end Leaf002

/- ZeroLE: E0=0LB, E1=0LD -/
namespace Leaf003
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨false,false,1⟩))
    (4, true) (some ⟨false,false,3⟩)
theorem check : zipCycle p 26 1 false (-4) = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 26 1 false (-4) (by decide) check B
#print axioms cover
end Leaf003

/- ZeroLE: E0=0LB, E1=0LE -/
namespace Leaf004
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨false,false,1⟩))
    (4, true) (some ⟨false,false,4⟩)
theorem check : zipCycle p 7 19 false 1 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 7 19 false 1 (by decide) check B
#print axioms cover
end Leaf004

/- ZeroLE: E0=0LB, E1=0RB -/
namespace Leaf005
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨false,false,1⟩))
    (4, true) (some ⟨false,true,1⟩)
theorem check : zipCycle p 32 13 true 0 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 32 13 true 0 (by decide) check B
#print axioms cover
end Leaf005

/- ZeroLE: E0=0LB, E1=0RC -/
namespace Leaf006
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨false,false,1⟩))
    (4, true) (some ⟨false,true,2⟩)
theorem check : zipCycle p 27 1 false (-1) = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 27 1 false (-1) (by decide) check B
#print axioms cover
end Leaf006

/- ZeroLE: E0=0LB, E1=0RD -/
namespace Leaf007
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨false,false,1⟩))
    (4, true) (some ⟨false,true,3⟩)
theorem check : zipCycle p 26 1 false (-2) = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 26 1 false (-2) (by decide) check B
#print axioms cover
end Leaf007

/- ZeroLE: E0=0LB, E1=1LA -/
namespace Leaf008
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨false,false,1⟩))
    (4, true) (some ⟨true,false,0⟩)
theorem check : zipCycle p 24 3 false (-2) = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 24 3 false (-2) (by decide) check B
#print axioms cover
end Leaf008

/- ZeroLE: E0=0LB, E1=1LC -/
namespace Leaf009
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨false,false,1⟩))
    (4, true) (some ⟨true,false,2⟩)
theorem check : zipCycle p 8 20 false 1 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 8 20 false 1 (by decide) check B
#print axioms cover
end Leaf009

/- ZeroLE: E0=0LB, E1=1LD -/
namespace Leaf010
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨false,false,1⟩))
    (4, true) (some ⟨true,false,3⟩)
theorem check : zipCycle p 26 1 false (-4) = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 26 1 false (-4) (by decide) check B
#print axioms cover
end Leaf010

/- ZeroLE: E0=0LB, E1=1LE -/
namespace Leaf011
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨false,false,1⟩))
    (4, true) (some ⟨true,false,4⟩)
theorem check : zipCycle p 1 29 false 3 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 1 29 false 3 (by decide) check B
#print axioms cover
end Leaf011

/- ZeroLE: E0=0LB, E1=1RB -/
namespace Leaf012
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨false,false,1⟩))
    (4, true) (some ⟨true,true,1⟩)
theorem check : zipCycle p 32 13 true 0 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 32 13 true 0 (by decide) check B
#print axioms cover
end Leaf012

/- ZeroLE: E0=0LB, E1=1RD -/
namespace Leaf013
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨false,false,1⟩))
    (4, true) (some ⟨true,true,3⟩)
theorem check : zipCycle p 1 30 false 3 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 1 30 false 3 (by decide) check B
#print axioms cover
end Leaf013

/- ZeroLE: E0=0LB, E1=1RE -/
namespace Leaf014
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨false,false,1⟩))
    (4, true) (some ⟨true,true,4⟩)
theorem check : zipCycle p 6 21 false 1 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 6 21 false 1 (by decide) check B
#print axioms cover
end Leaf014

/- ZeroLE: E0=0LF, F0=0LA -/
namespace Leaf015
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨false,false,5⟩))
    (5, false) (some ⟨false,false,0⟩)
theorem check : zipCycle p 0 9 false 3 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 0 9 false 3 (by decide) check B
#print axioms cover
end Leaf015

/- ZeroLE: E0=0LF, F0=0LC -/
namespace Leaf016
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨false,false,5⟩))
    (5, false) (some ⟨false,false,2⟩)
theorem check : zipCycle p 10 1 false (-2) = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 10 1 false (-2) (by decide) check B
#print axioms cover
end Leaf016

/- ZeroLE: E0=0LF, F0=0LD -/
namespace Leaf017
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨false,false,5⟩))
    (5, false) (some ⟨false,false,3⟩)
theorem check : zipCycle p 9 1 false (-3) = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 9 1 false (-3) (by decide) check B
#print axioms cover
end Leaf017

/- ZeroLE: E0=0LF, F0=0LE -/
namespace Leaf018
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨false,false,5⟩))
    (5, false) (some ⟨false,false,4⟩)
theorem check : zipCycle p 7 2 false (-1) = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 7 2 false (-1) (by decide) check B
#print axioms cover
end Leaf018

/- ZeroLE: E0=0LF, F0=0LF -/
namespace Leaf019
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨false,false,5⟩))
    (5, false) (some ⟨false,false,5⟩)
theorem check : zipCycle p 8 1 false (-2) = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 8 1 false (-2) (by decide) check B
#print axioms cover
end Leaf019

/- ZeroLE: E0=0LF, F0=0RC -/
namespace Leaf020
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨false,false,5⟩))
    (5, false) (some ⟨false,true,2⟩)
theorem check : zipCycle p 10 1 false 0 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 10 1 false 0 (by decide) check B
#print axioms cover
end Leaf020

/- ZeroLE: E0=0LF, F0=0RD -/
namespace Leaf021
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨false,false,5⟩))
    (5, false) (some ⟨false,true,3⟩)
theorem check : zipCycle p 9 1 false (-1) = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 9 1 false (-1) (by decide) check B
#print axioms cover
end Leaf021

/- ZeroLE: E0=0LF, F0=0RE -/
namespace Leaf022
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨false,false,5⟩))
    (5, false) (some ⟨false,true,4⟩)
theorem check : zipCycle p 7 2 false (-1) = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 7 2 false (-1) (by decide) check B
#print axioms cover
end Leaf022

/- ZeroLE: E0=0LF, F0=1LD -/
namespace Leaf023
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨false,false,5⟩))
    (5, false) (some ⟨true,false,3⟩)
theorem check : zipCycle p 9 1 false (-3) = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 9 1 false (-3) (by decide) check B
#print axioms cover
end Leaf023

/- ZeroLE: E0=0LF, F0=1LE -/
namespace Leaf024
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨false,false,5⟩))
    (5, false) (some ⟨true,false,4⟩)
theorem check : zipCycle p 7 2 false (-1) = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 7 2 false (-1) (by decide) check B
#print axioms cover
end Leaf024

/- ZeroLE: E0=0LF, F0=1LF -/
namespace Leaf025
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨false,false,5⟩))
    (5, false) (some ⟨true,false,5⟩)
theorem check : zipCycle p 8 1 false (-2) = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 8 1 false (-2) (by decide) check B
#print axioms cover
end Leaf025

/- ZeroLE: E0=0LF, F0=1RB -/
namespace Leaf026
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨false,false,5⟩))
    (5, false) (some ⟨true,true,1⟩)
theorem check : zipCycle p 1 8 false 3 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 1 8 false 3 (by decide) check B
#print axioms cover
end Leaf026

/- ZeroLE: E0=0LF, F0=1RD -/
namespace Leaf027
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨false,false,5⟩))
    (5, false) (some ⟨true,true,3⟩)
theorem check : zipCycle p 1 13 false 3 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 1 13 false 3 (by decide) check B
#print axioms cover
end Leaf027

/- ZeroLE: E0=0RA, C1=0LC -/
namespace Leaf028
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨false,true,0⟩))
    (2, true) (some ⟨false,false,2⟩)
theorem check : zipCycle p 14 1 false 0 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 14 1 false 0 (by decide) check B
#print axioms cover
end Leaf028

/- ZeroLE: E0=0RA, C1=0RB -/
namespace Leaf029
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨false,true,0⟩))
    (2, true) (some ⟨false,true,1⟩)
theorem check : zipCycle p 0 13 true (-1) = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 0 13 true (-1) (by decide) check B
#print axioms cover
end Leaf029

/- ZeroLE: E0=0RA, C1=1LD -/
namespace Leaf030
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨false,true,0⟩))
    (2, true) (some ⟨true,false,3⟩)
theorem check : zipCycle p 5 6 false 2 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 5 6 false 2 (by decide) check B
#print axioms cover
end Leaf030

/- ZeroLE: E0=0RB, E1=0LB -/
namespace Leaf031
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨false,true,1⟩))
    (4, true) (some ⟨false,false,1⟩)
theorem check : zipCycle p 8 18 false 4 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 8 18 false 4 (by decide) check B
#print axioms cover
end Leaf031

/- ZeroLE: E0=0RB, E1=0LC -/
namespace Leaf032
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨false,true,1⟩))
    (4, true) (some ⟨false,false,2⟩)
theorem check : zipCycle p 22 1 false 0 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 22 1 false 0 (by decide) check B
#print axioms cover
end Leaf032

/- ZeroLE: E0=0RB, E1=0LD -/
namespace Leaf033
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨false,true,1⟩))
    (4, true) (some ⟨false,false,3⟩)
theorem check : zipCycle p 21 1 false (-1) = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 21 1 false (-1) (by decide) check B
#print axioms cover
end Leaf033

/- ZeroLE: E0=0RB, E1=0LE -/
namespace Leaf034
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨false,true,1⟩))
    (4, true) (some ⟨false,false,4⟩)
theorem check : zipCycle p 8 46 false 5 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 8 46 false 5 (by decide) check B
#print axioms cover
end Leaf034

/- ZeroLE: E0=0RB, E1=0RB -/
namespace Leaf035
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨false,true,1⟩))
    (4, true) (some ⟨false,true,1⟩)
theorem check : zipCycle p 8 13 true 0 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 8 13 true 0 (by decide) check B
#print axioms cover
end Leaf035

/- ZeroLE: E0=0RB, E1=0RC -/
namespace Leaf036
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨false,true,1⟩))
    (4, true) (some ⟨false,true,2⟩)
theorem check : zipCycle p 22 1 false 2 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 22 1 false 2 (by decide) check B
#print axioms cover
end Leaf036

/- ZeroLE: E0=0RB, E1=0RD -/
namespace Leaf037
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨false,true,1⟩))
    (4, true) (some ⟨false,true,3⟩)
theorem check : zipCycle p 21 1 false 1 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 21 1 false 1 (by decide) check B
#print axioms cover
end Leaf037

/- ZeroLE: E0=0RB, E1=1LA -/
namespace Leaf038
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨false,true,1⟩))
    (4, true) (some ⟨true,false,0⟩)
theorem check : zipCycle p 19 3 false 1 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 19 3 false 1 (by decide) check B
#print axioms cover
end Leaf038

/- ZeroLE: E0=0RB, E1=1LC -/
namespace Leaf039
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨false,true,1⟩))
    (4, true) (some ⟨true,false,2⟩)
theorem check : zipCycle p 8 20 false 4 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 8 20 false 4 (by decide) check B
#print axioms cover
end Leaf039

/- ZeroLE: E0=0RB, E1=1LD -/
namespace Leaf040
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨false,true,1⟩))
    (4, true) (some ⟨true,false,3⟩)
theorem check : zipCycle p 21 1 false (-1) = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 21 1 false (-1) (by decide) check B
#print axioms cover
end Leaf040

/- ZeroLE: E0=0RB, E1=1RB -/
namespace Leaf041
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨false,true,1⟩))
    (4, true) (some ⟨true,true,1⟩)
theorem check : zipCycle p 8 13 true 0 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 8 13 true 0 (by decide) check B
#print axioms cover
end Leaf041

/- ZeroLE: E0=0RE, E1=0LB -/
namespace Leaf042
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨false,true,4⟩))
    (4, true) (some ⟨false,false,1⟩)
theorem check : zipCycle p 1 13 true (-1) = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 1 13 true (-1) (by decide) check B
#print axioms cover
end Leaf042

/- ZeroLE: E0=0RE, E1=0LC -/
namespace Leaf043
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨false,true,4⟩))
    (4, true) (some ⟨false,false,2⟩)
theorem check : zipCycle p 12 1 false 2 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 12 1 false 2 (by decide) check B
#print axioms cover
end Leaf043

/- ZeroLE: E0=0RE, E1=0LD -/
namespace Leaf044
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨false,true,4⟩))
    (4, true) (some ⟨false,false,3⟩)
theorem check : zipCycle p 11 1 false 1 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 11 1 false 1 (by decide) check B
#print axioms cover
end Leaf044

/- ZeroLE: E0=0RE, E1=0LE -/
namespace Leaf045
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨false,true,4⟩))
    (4, true) (some ⟨false,false,4⟩)
theorem check : zipCycle p 14 1 true 2 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 14 1 true 2 (by decide) check B
#print axioms cover
end Leaf045

/- ZeroLE: E0=0RE, E1=0RB -/
namespace Leaf046
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨false,true,4⟩))
    (4, true) (some ⟨false,true,1⟩)
theorem check : zipCycle p 12 1 true 2 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 12 1 true 2 (by decide) check B
#print axioms cover
end Leaf046

/- ZeroLE: E0=0RE, E1=0RD -/
namespace Leaf047
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨false,true,4⟩))
    (4, true) (some ⟨false,true,3⟩)
theorem check : zipCycle p 30 1 false 2 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 30 1 false 2 (by decide) check B
#print axioms cover
end Leaf047

/- ZeroLE: E0=0RE, E1=0RE -/
namespace Leaf048
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨false,true,4⟩))
    (4, true) (some ⟨false,true,4⟩)
theorem check : zipCycle p 12 1 true 4 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 12 1 true 4 (by decide) check B
#print axioms cover
end Leaf048

/- ZeroLE: E0=0RE, E1=1LA -/
namespace Leaf049
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨false,true,4⟩))
    (4, true) (some ⟨true,false,0⟩)
theorem check : zipCycle p 10 3 false 2 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 10 3 false 2 (by decide) check B
#print axioms cover
end Leaf049

/- ZeroLE: E0=0RE, E1=1LC -/
namespace Leaf050
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨false,true,4⟩))
    (4, true) (some ⟨true,false,2⟩)
theorem check : zipCycle p 1 15 true (-1) = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 1 15 true (-1) (by decide) check B
#print axioms cover
end Leaf050

/- ZeroLE: E0=0RE, E1=1LD -/
namespace Leaf051
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨false,true,4⟩))
    (4, true) (some ⟨true,false,3⟩)
theorem check : zipCycle p 11 1 false 1 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 11 1 false 1 (by decide) check B
#print axioms cover
end Leaf051

/- ZeroLE: E0=0RE, E1=1LE -/
namespace Leaf052
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨false,true,4⟩))
    (4, true) (some ⟨true,false,4⟩)
theorem check : zipCycle p 9 2 false 2 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 9 2 false 2 (by decide) check B
#print axioms cover
end Leaf052

/- ZeroLE: E0=0RE, E1=1RB -/
namespace Leaf053
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨false,true,4⟩))
    (4, true) (some ⟨true,true,1⟩)
theorem check : zipCycle p 1 12 true (-1) = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 1 12 true (-1) (by decide) check B
#print axioms cover
end Leaf053

/- ZeroLE: E0=0RE, E1=1RD -/
namespace Leaf054
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨false,true,4⟩))
    (4, true) (some ⟨true,true,3⟩)
theorem check : zipCycle p 13 1 true 1 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 13 1 true 1 (by decide) check B
#print axioms cover
end Leaf054

/- ZeroLE: E0=0RE, E1=1RE -/
namespace Leaf055
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨false,true,4⟩))
    (4, true) (some ⟨true,true,4⟩)
theorem check : zipCycle p 12 1 true 4 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 12 1 true 4 (by decide) check B
#print axioms cover
end Leaf055

/- ZeroLE: E0=0RF, F0=0LC -/
namespace Leaf056
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨false,true,5⟩))
    (5, false) (some ⟨false,false,2⟩)
theorem check : zipCycle p 10 1 false 0 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 10 1 false 0 (by decide) check B
#print axioms cover
end Leaf056

/- ZeroLE: E0=0RF, F0=0LD -/
namespace Leaf057
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨false,true,5⟩))
    (5, false) (some ⟨false,false,3⟩)
theorem check : zipCycle p 9 1 false (-1) = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 9 1 false (-1) (by decide) check B
#print axioms cover
end Leaf057

/- ZeroLE: E0=0RF, F0=0LE -/
namespace Leaf058
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨false,true,5⟩))
    (5, false) (some ⟨false,false,4⟩)
theorem check : zipCycle p 7 2 false 0 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 7 2 false 0 (by decide) check B
#print axioms cover
end Leaf058

/- ZeroLE: E0=0RF, F0=0LF -/
namespace Leaf059
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨false,true,5⟩))
    (5, false) (some ⟨false,false,5⟩)
theorem check : zipCycle p 8 1 false 0 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 8 1 false 0 (by decide) check B
#print axioms cover
end Leaf059

/- ZeroLE: E0=0RF, F0=0RC -/
namespace Leaf060
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨false,true,5⟩))
    (5, false) (some ⟨false,true,2⟩)
theorem check : zipCycle p 1 13 true (-1) = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 1 13 true (-1) (by decide) check B
#print axioms cover
end Leaf060

/- ZeroLE: E0=0RF, F0=0RD -/
namespace Leaf061
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨false,true,5⟩))
    (5, false) (some ⟨false,true,3⟩)
theorem check : zipCycle p 9 1 false 1 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 9 1 false 1 (by decide) check B
#print axioms cover
end Leaf061

/- ZeroLE: E0=0RF, F0=1LD -/
namespace Leaf062
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨false,true,5⟩))
    (5, false) (some ⟨true,false,3⟩)
theorem check : zipCycle p 9 1 false (-1) = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 9 1 false (-1) (by decide) check B
#print axioms cover
end Leaf062

/- ZeroLE: E0=0RF, F0=1LF -/
namespace Leaf063
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨false,true,5⟩))
    (5, false) (some ⟨true,false,5⟩)
theorem check : zipCycle p 8 1 false 0 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 8 1 false 0 (by decide) check B
#print axioms cover
end Leaf063

/- ZeroLE: E0=1LA, E1=0LA -/
namespace Leaf064
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨true,false,0⟩))
    (4, true) (some ⟨false,false,0⟩)
theorem check : zipCycle p 0 11 false 3 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 0 11 false 3 (by decide) check B
#print axioms cover
end Leaf064

/- ZeroLE: E0=1LA, E1=0LB -/
namespace Leaf065
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨true,false,0⟩))
    (4, true) (some ⟨false,false,1⟩)
theorem check : zipCycle p 9 18 false 0 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 9 18 false 0 (by decide) check B
#print axioms cover
end Leaf065

/- ZeroLE: E0=1LA, E1=0LC -/
namespace Leaf066
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨true,false,0⟩))
    (4, true) (some ⟨false,false,2⟩)
theorem check : zipCycle p 12 1 false (-2) = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 12 1 false (-2) (by decide) check B
#print axioms cover
end Leaf066

/- ZeroLE: E0=1LA, E1=0LD -/
namespace Leaf067
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨true,false,0⟩))
    (4, true) (some ⟨false,false,3⟩)
theorem check : zipCycle p 11 1 false (-3) = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 11 1 false (-3) (by decide) check B
#print axioms cover
end Leaf067

/- ZeroLE: E0=1LA, E1=0LE -/
namespace Leaf068
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨true,false,0⟩))
    (4, true) (some ⟨false,false,4⟩)
theorem check : zipCycle p 7 4 false (-1) = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 7 4 false (-1) (by decide) check B
#print axioms cover
end Leaf068

/- ZeroLE: E0=1LA, E1=0RB -/
namespace Leaf069
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨true,false,0⟩))
    (4, true) (some ⟨false,true,1⟩)
theorem check : zipCycle p 22 13 true 0 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 22 13 true 0 (by decide) check B
#print axioms cover
end Leaf069

/- ZeroLE: E0=1LA, E1=0RC -/
namespace Leaf070
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨true,false,0⟩))
    (4, true) (some ⟨false,true,2⟩)
theorem check : zipCycle p 12 1 false 0 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 12 1 false 0 (by decide) check B
#print axioms cover
end Leaf070

/- ZeroLE: E0=1LA, E1=0RD -/
namespace Leaf071
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨true,false,0⟩))
    (4, true) (some ⟨false,true,3⟩)
theorem check : zipCycle p 11 1 false (-1) = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 11 1 false (-1) (by decide) check B
#print axioms cover
end Leaf071

/- ZeroLE: E0=1LA, E1=0RE -/
namespace Leaf072
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨true,false,0⟩))
    (4, true) (some ⟨false,true,4⟩)
theorem check : zipCycle p 7 4 false (-1) = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 7 4 false (-1) (by decide) check B
#print axioms cover
end Leaf072

/- ZeroLE: E0=1LA, E1=1LA -/
namespace Leaf073
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨true,false,0⟩))
    (4, true) (some ⟨true,false,0⟩)
theorem check : zipCycle p 8 3 false (-1) = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 8 3 false (-1) (by decide) check B
#print axioms cover
end Leaf073

/- ZeroLE: E0=1LA, E1=1LC -/
namespace Leaf074
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨true,false,0⟩))
    (4, true) (some ⟨true,false,2⟩)
theorem check : zipCycle p 9 20 false 0 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 9 20 false 0 (by decide) check B
#print axioms cover
end Leaf074

/- ZeroLE: E0=1LA, E1=1LD -/
namespace Leaf075
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨true,false,0⟩))
    (4, true) (some ⟨true,false,3⟩)
theorem check : zipCycle p 11 1 false (-3) = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 11 1 false (-3) (by decide) check B
#print axioms cover
end Leaf075

/- ZeroLE: E0=1LA, E1=1LE -/
namespace Leaf076
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨true,false,0⟩))
    (4, true) (some ⟨true,false,4⟩)
theorem check : zipCycle p 7 4 false (-1) = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 7 4 false (-1) (by decide) check B
#print axioms cover
end Leaf076

/- ZeroLE: E0=1LA, E1=1RB -/
namespace Leaf077
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨true,false,0⟩))
    (4, true) (some ⟨true,true,1⟩)
theorem check : zipCycle p 1 10 false 3 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 1 10 false 3 (by decide) check B
#print axioms cover
end Leaf077

/- ZeroLE: E0=1LA, E1=1RD -/
namespace Leaf078
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨true,false,0⟩))
    (4, true) (some ⟨true,true,3⟩)
theorem check : zipCycle p 1 15 false 3 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 1 15 false 3 (by decide) check B
#print axioms cover
end Leaf078

/- ZeroLE: E0=1LB, C1=0LB -/
namespace Leaf079
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨true,false,1⟩))
    (2, true) (some ⟨false,false,1⟩)
theorem check : zipCycle p 6 4 false 0 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 6 4 false 0 (by decide) check B
#print axioms cover
end Leaf079

/- ZeroLE: E0=1LB, C1=0LC -/
namespace Leaf080
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨true,false,1⟩))
    (2, true) (some ⟨false,false,2⟩)
theorem check : zipCycle p 12 1 false (-2) = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 12 1 false (-2) (by decide) check B
#print axioms cover
end Leaf080

/- ZeroLE: E0=1LB, C1=1LB -/
namespace Leaf081
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨true,false,1⟩))
    (2, true) (some ⟨true,false,1⟩)
theorem check : zipCycle p 6 4 false 0 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 6 4 false 0 (by decide) check B
#print axioms cover
end Leaf081

/- ZeroLE: E0=1LB, C1=1LC -/
namespace Leaf082
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨true,false,1⟩))
    (2, true) (some ⟨true,false,2⟩)
theorem check : zipCycle p 1 15 false 3 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 1 15 false 3 (by decide) check B
#print axioms cover
end Leaf082

/- ZeroLE: E0=1LB, C1=1LD -/
namespace Leaf083
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨true,false,1⟩))
    (2, true) (some ⟨true,false,3⟩)
theorem check : zipCycle p 1 13 false 3 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 1 13 false 3 (by decide) check B
#print axioms cover
end Leaf083

/- ZeroLE: E0=1LB, C1=1RC -/
namespace Leaf084
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨true,false,1⟩))
    (2, true) (some ⟨true,true,2⟩)
theorem check : zipCycle p 2 8 false 3 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 2 8 false 3 (by decide) check B
#print axioms cover
end Leaf084

/- ZeroLE: E0=1LB, C1=1RD -/
namespace Leaf085
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨true,false,1⟩))
    (2, true) (some ⟨true,true,3⟩)
theorem check : zipCycle p 4 6 false 2 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 4 6 false 2 (by decide) check B
#print axioms cover
end Leaf085

/- ZeroLE: E0=1LC, E1=0LA -/
namespace Leaf086
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨true,false,2⟩))
    (4, true) (some ⟨false,false,0⟩)
theorem check : zipCycle p 0 28 false 3 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 0 28 false 3 (by decide) check B
#print axioms cover
end Leaf086

/- ZeroLE: E0=1LC, E1=0LB -/
namespace Leaf087
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨true,false,2⟩))
    (4, true) (some ⟨false,false,1⟩)
theorem check : zipCycle p 10 18 false 1 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 10 18 false 1 (by decide) check B
#print axioms cover
end Leaf087

/- ZeroLE: E0=1LC, E1=0LC -/
namespace Leaf088
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨true,false,2⟩))
    (4, true) (some ⟨false,false,2⟩)
theorem check : zipCycle p 29 1 false (-3) = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 29 1 false (-3) (by decide) check B
#print axioms cover
end Leaf088

/- ZeroLE: E0=1LC, E1=0LD -/
namespace Leaf089
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨true,false,2⟩))
    (4, true) (some ⟨false,false,3⟩)
theorem check : zipCycle p 28 1 false (-4) = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 28 1 false (-4) (by decide) check B
#print axioms cover
end Leaf089

/- ZeroLE: E0=1LC, E1=0LE -/
namespace Leaf090
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨true,false,2⟩))
    (4, true) (some ⟨false,false,4⟩)
theorem check : zipCycle p 7 21 false 1 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 7 21 false 1 (by decide) check B
#print axioms cover
end Leaf090

/- ZeroLE: E0=1LC, E1=0RB -/
namespace Leaf091
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨true,false,2⟩))
    (4, true) (some ⟨false,true,1⟩)
theorem check : zipCycle p 34 13 true 0 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 34 13 true 0 (by decide) check B
#print axioms cover
end Leaf091

/- ZeroLE: E0=1LC, E1=0RC -/
namespace Leaf092
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨true,false,2⟩))
    (4, true) (some ⟨false,true,2⟩)
theorem check : zipCycle p 29 1 false (-1) = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 29 1 false (-1) (by decide) check B
#print axioms cover
end Leaf092

/- ZeroLE: E0=1LC, E1=0RD -/
namespace Leaf093
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨true,false,2⟩))
    (4, true) (some ⟨false,true,3⟩)
theorem check : zipCycle p 28 1 false (-2) = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 28 1 false (-2) (by decide) check B
#print axioms cover
end Leaf093

/- ZeroLE: E0=1LC, E1=1LA -/
namespace Leaf094
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨true,false,2⟩))
    (4, true) (some ⟨true,false,0⟩)
theorem check : zipCycle p 26 3 false (-2) = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 26 3 false (-2) (by decide) check B
#print axioms cover
end Leaf094

/- ZeroLE: E0=1LC, E1=1LC -/
namespace Leaf095
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨true,false,2⟩))
    (4, true) (some ⟨true,false,2⟩)
theorem check : zipCycle p 8 20 false 1 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 8 20 false 1 (by decide) check B
#print axioms cover
end Leaf095

/- ZeroLE: E0=1LC, E1=1LD -/
namespace Leaf096
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨true,false,2⟩))
    (4, true) (some ⟨true,false,3⟩)
theorem check : zipCycle p 28 1 false (-4) = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 28 1 false (-4) (by decide) check B
#print axioms cover
end Leaf096

/- ZeroLE: E0=1LC, E1=1LE -/
namespace Leaf097
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨true,false,2⟩))
    (4, true) (some ⟨true,false,4⟩)
theorem check : zipCycle p 1 33 false 3 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 1 33 false 3 (by decide) check B
#print axioms cover
end Leaf097

/- ZeroLE: E0=1LC, E1=1RB -/
namespace Leaf098
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨true,false,2⟩))
    (4, true) (some ⟨true,true,1⟩)
theorem check : zipCycle p 34 13 true 0 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 34 13 true 0 (by decide) check B
#print axioms cover
end Leaf098

/- ZeroLE: E0=1LC, E1=1RD -/
namespace Leaf099
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨true,false,2⟩))
    (4, true) (some ⟨true,true,3⟩)
theorem check : zipCycle p 1 32 false 3 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 1 32 false 3 (by decide) check B
#print axioms cover
end Leaf099

/- ZeroLE: E0=1LF, F0=0LB -/
namespace Leaf100
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨true,false,5⟩))
    (5, false) (some ⟨false,false,1⟩)
theorem check : zipCycle p 1 11 false 3 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 1 11 false 3 (by decide) check B
#print axioms cover
end Leaf100

/- ZeroLE: E0=1LF, F0=0LC -/
namespace Leaf101
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨true,false,5⟩))
    (5, false) (some ⟨false,false,2⟩)
theorem check : zipCycle p 10 1 false (-2) = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 10 1 false (-2) (by decide) check B
#print axioms cover
end Leaf101

/- ZeroLE: E0=1LF, F0=0LD -/
namespace Leaf102
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨true,false,5⟩))
    (5, false) (some ⟨false,false,3⟩)
theorem check : zipCycle p 9 1 false (-3) = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 9 1 false (-3) (by decide) check B
#print axioms cover
end Leaf102

/- ZeroLE: E0=1LF, F0=0LE -/
namespace Leaf103
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨true,false,5⟩))
    (5, false) (some ⟨false,false,4⟩)
theorem check : zipCycle p 7 2 false (-1) = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 7 2 false (-1) (by decide) check B
#print axioms cover
end Leaf103

/- ZeroLE: E0=1LF, F0=0LF -/
namespace Leaf104
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨true,false,5⟩))
    (5, false) (some ⟨false,false,5⟩)
theorem check : zipCycle p 8 1 false (-2) = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 8 1 false (-2) (by decide) check B
#print axioms cover
end Leaf104

/- ZeroLE: E0=1LF, F0=0RB -/
namespace Leaf105
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨true,false,5⟩))
    (5, false) (some ⟨false,true,1⟩)
theorem check : zipCycle p 6 3 false 0 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 6 3 false 0 (by decide) check B
#print axioms cover
end Leaf105

/- ZeroLE: E0=1LF, F0=1LC -/
namespace Leaf106
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨true,false,5⟩))
    (5, false) (some ⟨true,false,2⟩)
theorem check : zipCycle p 1 13 false 3 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 1 13 false 3 (by decide) check B
#print axioms cover
end Leaf106

/- ZeroLE: E0=1LF, F0=1LD -/
namespace Leaf107
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨true,false,5⟩))
    (5, false) (some ⟨true,false,3⟩)
theorem check : zipCycle p 9 1 false (-3) = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 9 1 false (-3) (by decide) check B
#print axioms cover
end Leaf107

/- ZeroLE: E0=1LF, F0=1LE -/
namespace Leaf108
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨true,false,5⟩))
    (5, false) (some ⟨true,false,4⟩)
theorem check : zipCycle p 7 2 false (-1) = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 7 2 false (-1) (by decide) check B
#print axioms cover
end Leaf108

/- ZeroLE: E0=1LF, F0=1LF -/
namespace Leaf109
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨true,false,5⟩))
    (5, false) (some ⟨true,false,5⟩)
theorem check : zipCycle p 8 1 false (-2) = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 8 1 false (-2) (by decide) check B
#print axioms cover
end Leaf109

/- ZeroLE: E0=1LF, F0=1RD -/
namespace Leaf110
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨true,false,5⟩))
    (5, false) (some ⟨true,true,3⟩)
theorem check : zipCycle p 5 4 false 1 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 5 4 false 1 (by decide) check B
#print axioms cover
end Leaf110

/- ZeroLE: E0=1RA, C1=0LC -/
namespace Leaf111
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨true,true,0⟩))
    (2, true) (some ⟨false,false,2⟩)
theorem check : zipCycle p 15 1 false (-1) = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 15 1 false (-1) (by decide) check B
#print axioms cover
end Leaf111

/- ZeroLE: E0=1RB, E1=0LB -/
namespace Leaf112
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨true,true,1⟩))
    (4, true) (some ⟨false,false,1⟩)
theorem check : zipCycle p 1 22 false 4 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 1 22 false 4 (by decide) check B
#print axioms cover
end Leaf112

/- ZeroLE: E0=1RB, E1=0LD -/
namespace Leaf113
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨true,true,1⟩))
    (4, true) (some ⟨false,false,3⟩)
theorem check : zipCycle p 40 1 false (-4) = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 40 1 false (-4) (by decide) check B
#print axioms cover
end Leaf113

/- ZeroLE: E0=1RB, E1=0LE -/
namespace Leaf114
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨true,true,1⟩))
    (4, true) (some ⟨false,false,4⟩)
theorem check : zipCycle p 1 22 false 4 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 1 22 false 4 (by decide) check B
#print axioms cover
end Leaf114

/- ZeroLE: E0=1RB, E1=0RB -/
namespace Leaf115
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨true,true,1⟩))
    (4, true) (some ⟨false,true,1⟩)
theorem check : zipCycle p 8 13 true 0 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 8 13 true 0 (by decide) check B
#print axioms cover
end Leaf115

/- ZeroLE: E0=1RB, E1=0RC -/
namespace Leaf116
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨true,true,1⟩))
    (4, true) (some ⟨false,true,2⟩)
theorem check : zipCycle p 56 1 false 0 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 56 1 false 0 (by decide) check B
#print axioms cover
end Leaf116

/- ZeroLE: E0=1RB, E1=0RD -/
namespace Leaf117
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨true,true,1⟩))
    (4, true) (some ⟨false,true,3⟩)
theorem check : zipCycle p 37 1 false (-1) = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 37 1 false (-1) (by decide) check B
#print axioms cover
end Leaf117

/- ZeroLE: E0=1RB, E1=1LD -/
namespace Leaf118
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨true,true,1⟩))
    (4, true) (some ⟨true,false,3⟩)
theorem check : zipCycle p 1 24 false 4 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 1 24 false 4 (by decide) check B
#print axioms cover
end Leaf118

/- ZeroLE: E0=1RB, E1=1LE -/
namespace Leaf119
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨true,true,1⟩))
    (4, true) (some ⟨true,false,4⟩)
theorem check : zipCycle p 21 3 false (-1) = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 21 3 false (-1) (by decide) check B
#print axioms cover
end Leaf119

/- ZeroLE: E0=1RB, E1=1RB -/
namespace Leaf120
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨true,true,1⟩))
    (4, true) (some ⟨true,true,1⟩)
theorem check : zipCycle p 8 13 true 0 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 8 13 true 0 (by decide) check B
#print axioms cover
end Leaf120

/- ZeroLE: E0=1RC, E1=0LB -/
namespace Leaf121
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨true,true,2⟩))
    (4, true) (some ⟨false,false,1⟩)
theorem check : zipCycle p 31 18 false 0 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 31 18 false 0 (by decide) check B
#print axioms cover
end Leaf121

/- ZeroLE: E0=1RC, E1=0LD -/
namespace Leaf122
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨true,true,2⟩))
    (4, true) (some ⟨false,false,3⟩)
theorem check : zipCycle p 51 1 false (-5) = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 51 1 false (-5) (by decide) check B
#print axioms cover
end Leaf122

/- ZeroLE: E0=1RC, E1=0LE -/
namespace Leaf123
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨true,true,2⟩))
    (4, true) (some ⟨false,false,4⟩)
theorem check : zipCycle p 32 18 false 0 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 32 18 false 0 (by decide) check B
#print axioms cover
end Leaf123

/- ZeroLE: E0=1RC, E1=0RB -/
namespace Leaf124
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨true,true,2⟩))
    (4, true) (some ⟨false,true,1⟩)
theorem check : zipCycle p 18 13 true 0 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 18 13 true 0 (by decide) check B
#print axioms cover
end Leaf124

/- ZeroLE: E0=1RC, E1=0RD -/
namespace Leaf125
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨true,true,2⟩))
    (4, true) (some ⟨false,true,3⟩)
theorem check : zipCycle p 3 28 false 4 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 3 28 false 4 (by decide) check B
#print axioms cover
end Leaf125

/- ZeroLE: E0=1RC, E1=0RE -/
namespace Leaf126
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨true,true,2⟩))
    (4, true) (some ⟨false,true,4⟩)
theorem check : zipCycle p 19 13 true 0 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 19 13 true 0 (by decide) check B
#print axioms cover
end Leaf126

/- ZeroLE: E0=1RC, E1=1LD -/
namespace Leaf127
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨true,true,2⟩))
    (4, true) (some ⟨true,false,3⟩)
theorem check : zipCycle p 1 57 false 4 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 1 57 false 4 (by decide) check B
#print axioms cover
end Leaf127

/- ZeroLE: E0=1RC, E1=1RB -/
namespace Leaf128
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨true,true,2⟩))
    (4, true) (some ⟨true,true,1⟩)
theorem check : zipCycle p 18 13 true 0 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 18 13 true 0 (by decide) check B
#print axioms cover
end Leaf128

/- ZeroLE: E0=1RC, E1=1RD -/
namespace Leaf129
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨true,true,2⟩))
    (4, true) (some ⟨true,true,3⟩)
theorem check : zipCycle p 73 24 false (-1) = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 73 24 false (-1) (by decide) check B
#print axioms cover
end Leaf129

/- ZeroLE: E0=1RC, E1=1RE -/
namespace Leaf130
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨true,true,2⟩))
    (4, true) (some ⟨true,true,4⟩)
theorem check : zipCycle p 19 13 true 0 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 19 13 true 0 (by decide) check B
#print axioms cover
end Leaf130

/- ZeroLE: E0=1RE, E1=0LB -/
namespace Leaf131
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨true,true,4⟩))
    (4, true) (some ⟨false,false,1⟩)
theorem check : zipCycle p 25 1 true (-3) = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 25 1 true (-3) (by decide) check B
#print axioms cover
end Leaf131

/- ZeroLE: E0=1RE, E1=0LD -/
namespace Leaf132
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨true,true,4⟩))
    (4, true) (some ⟨false,false,3⟩)
theorem check : zipCycle p 14 1 false (-2) = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 14 1 false (-2) (by decide) check B
#print axioms cover
end Leaf132

/- ZeroLE: E0=1RE, E1=0LE -/
namespace Leaf133
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨true,true,4⟩))
    (4, true) (some ⟨false,false,4⟩)
theorem check : zipCycle p 25 1 true (-3) = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 25 1 true (-3) (by decide) check B
#print axioms cover
end Leaf133

/- ZeroLE: E0=1RE, E1=0RB -/
namespace Leaf134
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨true,true,4⟩))
    (4, true) (some ⟨false,true,1⟩)
theorem check : zipCycle p 12 1 true 2 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 12 1 true 2 (by decide) check B
#print axioms cover
end Leaf134

/- ZeroLE: E0=1RE, E1=0RD -/
namespace Leaf135
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨true,true,4⟩))
    (4, true) (some ⟨false,true,3⟩)
theorem check : zipCycle p 35 1 false (-1) = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 35 1 false (-1) (by decide) check B
#print axioms cover
end Leaf135

/- ZeroLE: E0=1RE, E1=0RE -/
namespace Leaf136
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨true,true,4⟩))
    (4, true) (some ⟨false,true,4⟩)
theorem check : zipCycle p 12 1 true 4 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 12 1 true 4 (by decide) check B
#print axioms cover
end Leaf136

/- ZeroLE: E0=1RE, E1=1LD -/
namespace Leaf137
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨true,true,4⟩))
    (4, true) (some ⟨true,false,3⟩)
theorem check : zipCycle p 14 1 false (-2) = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 14 1 false (-2) (by decide) check B
#print axioms cover
end Leaf137

/- ZeroLE: E0=1RE, E1=1LE -/
namespace Leaf138
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨true,true,4⟩))
    (4, true) (some ⟨true,false,4⟩)
theorem check : zipCycle p 12 3 false 0 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 12 3 false 0 (by decide) check B
#print axioms cover
end Leaf138

/- ZeroLE: E0=1RE, E1=1RB -/
namespace Leaf139
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨true,true,4⟩))
    (4, true) (some ⟨true,true,1⟩)
theorem check : zipCycle p 13 13 true 1 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 13 13 true 1 (by decide) check B
#print axioms cover
end Leaf139

/- ZeroLE: E0=1RE, E1=1RD -/
namespace Leaf140
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨true,true,4⟩))
    (4, true) (some ⟨true,true,3⟩)
theorem check : zipCycle p 1 22 false 3 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 1 22 false 3 (by decide) check B
#print axioms cover
end Leaf140

/- ZeroLE: E0=1RE, E1=1RE -/
namespace Leaf141
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨true,true,4⟩))
    (4, true) (some ⟨true,true,4⟩)
theorem check : zipCycle p 12 1 true 4 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 12 1 true 4 (by decide) check B
#print axioms cover
end Leaf141

/- ZeroLE: E0=1RF, F0=0LB -/
namespace Leaf142
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨true,true,5⟩))
    (5, false) (some ⟨false,false,1⟩)
theorem check : zipCycle p 6 3 false 0 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 6 3 false 0 (by decide) check B
#print axioms cover
end Leaf142

/- ZeroLE: E0=1RF, F0=0RC -/
namespace Leaf143
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨true,true,5⟩))
    (5, false) (some ⟨false,true,2⟩)
theorem check : zipCycle p 1 13 true (-1) = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 1 13 true (-1) (by decide) check B
#print axioms cover
end Leaf143

/- ZeroLE: E0=1RF, F0=1LB -/
namespace Leaf144
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨true,true,5⟩))
    (5, false) (some ⟨true,false,1⟩)
theorem check : zipCycle p 6 3 false 0 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 6 3 false 0 (by decide) check B
#print axioms cover
end Leaf144

/- ZeroLE: E0=1RF, F0=1LD -/
namespace Leaf145
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨true,true,5⟩))
    (5, false) (some ⟨true,false,3⟩)
theorem check : zipCycle p 1 12 false 3 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 1 12 false 3 (by decide) check B
#print axioms cover
end Leaf145

/- ZeroLE: E0=1RF, F0=1RD -/
namespace Leaf146
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨true,true,5⟩))
    (5, false) (some ⟨true,true,3⟩)
theorem check : zipCycle p 4 5 false 2 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 4 5 false 2 (by decide) check B
#print axioms cover
end Leaf146

end BB6.Agent32Raw42ZeroLEThirdBatch
