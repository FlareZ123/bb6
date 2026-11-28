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
namespace BB6.Agent32Raw42OneLEThirdBatch
open BB6Coverage BB6.Agent13BlankDelay BB6Coverage.Agent10ZipAudit
abbrev base : PartialMachine := BB6.Agent32Raw42.child
  ⟨true,false,4⟩

private theorem zipper_cover
    (p : PartialMachine) (e k : Nat) (right : Bool) (boundary : Int)
    (hk : 0 < k) (hc : zipCycle p e k right boundary = true) (B : Nat) :
    Cover (WeightedBound B) p := by
  apply Cover.leaf p
  intro m hm
  exact weighted_never B m (zipCycle_sound p e k right boundary hk hc m hm)

/- OneLE: E0=0LA, C1=0LC -/
namespace Leaf000
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨false,false,0⟩))
    (2, true) (some ⟨false,false,2⟩)
theorem check : zipCycle p 14 1 false (-2) = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 14 1 false (-2) (by decide) check B
#print axioms cover
end Leaf000

/- OneLE: E0=0LA, C1=0LD -/
namespace Leaf001
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨false,false,0⟩))
    (2, true) (some ⟨false,false,3⟩)
theorem check : zipCycle p 5 6 false 1 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 5 6 false 1 (by decide) check B
#print axioms cover
end Leaf001

/- OneLE: E0=0LA, C1=0RD -/
namespace Leaf002
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨false,false,0⟩))
    (2, true) (some ⟨false,true,3⟩)
theorem check : zipCycle p 3 8 false 3 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 3 8 false 3 (by decide) check B
#print axioms cover
end Leaf002

/- OneLE: E0=0LA, C1=1LD -/
namespace Leaf003
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨false,false,0⟩))
    (2, true) (some ⟨true,false,3⟩)
theorem check : zipCycle p 5 6 false 1 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 5 6 false 1 (by decide) check B
#print axioms cover
end Leaf003

/- OneLE: E0=0LF, F0=0LC -/
namespace Leaf004
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨false,false,5⟩))
    (5, false) (some ⟨false,false,2⟩)
theorem check : zipCycle p 10 1 false (-2) = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 10 1 false (-2) (by decide) check B
#print axioms cover
end Leaf004

/- OneLE: E0=0LF, F0=0LD -/
namespace Leaf005
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨false,false,5⟩))
    (5, false) (some ⟨false,false,3⟩)
theorem check : zipCycle p 9 1 false (-3) = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 9 1 false (-3) (by decide) check B
#print axioms cover
end Leaf005

/- OneLE: E0=0LF, F0=0LE -/
namespace Leaf006
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨false,false,5⟩))
    (5, false) (some ⟨false,false,4⟩)
theorem check : zipCycle p 7 2 false (-1) = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 7 2 false (-1) (by decide) check B
#print axioms cover
end Leaf006

/- OneLE: E0=0LF, F0=0LF -/
namespace Leaf007
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨false,false,5⟩))
    (5, false) (some ⟨false,false,5⟩)
theorem check : zipCycle p 8 1 false (-2) = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 8 1 false (-2) (by decide) check B
#print axioms cover
end Leaf007

/- OneLE: E0=0LF, F0=0RD -/
namespace Leaf008
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨false,false,5⟩))
    (5, false) (some ⟨false,true,3⟩)
theorem check : zipCycle p 9 1 false (-1) = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 9 1 false (-1) (by decide) check B
#print axioms cover
end Leaf008

/- OneLE: E0=0LF, F0=0RE -/
namespace Leaf009
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨false,false,5⟩))
    (5, false) (some ⟨false,true,4⟩)
theorem check : zipCycle p 7 2 false (-1) = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 7 2 false (-1) (by decide) check B
#print axioms cover
end Leaf009

/- OneLE: E0=0LF, F0=1LD -/
namespace Leaf010
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨false,false,5⟩))
    (5, false) (some ⟨true,false,3⟩)
theorem check : zipCycle p 9 1 false (-3) = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 9 1 false (-3) (by decide) check B
#print axioms cover
end Leaf010

/- OneLE: E0=0LF, F0=1LE -/
namespace Leaf011
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨false,false,5⟩))
    (5, false) (some ⟨true,false,4⟩)
theorem check : zipCycle p 7 2 false (-1) = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 7 2 false (-1) (by decide) check B
#print axioms cover
end Leaf011

/- OneLE: E0=0LF, F0=1LF -/
namespace Leaf012
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨false,false,5⟩))
    (5, false) (some ⟨true,false,5⟩)
theorem check : zipCycle p 8 1 false (-2) = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 8 1 false (-2) (by decide) check B
#print axioms cover
end Leaf012

/- OneLE: E0=0LF, F0=1RC -/
namespace Leaf013
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨false,false,5⟩))
    (5, false) (some ⟨true,true,2⟩)
theorem check : zipCycle p 1 10 false 3 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 1 10 false 3 (by decide) check B
#print axioms cover
end Leaf013

/- OneLE: E0=0RA, A1=0LC -/
namespace Leaf014
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨false,true,0⟩))
    (0, true) (some ⟨false,false,2⟩)
theorem check : zipCycle p 10 1 false 0 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 10 1 false 0 (by decide) check B
#print axioms cover
end Leaf014

/- OneLE: E0=0RA, A1=0LD -/
namespace Leaf015
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨false,true,0⟩))
    (0, true) (some ⟨false,false,3⟩)
theorem check : zipCycle p 9 1 false (-1) = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 9 1 false (-1) (by decide) check B
#print axioms cover
end Leaf015

/- OneLE: E0=0RA, A1=0RC -/
namespace Leaf016
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨false,true,0⟩))
    (0, true) (some ⟨false,true,2⟩)
theorem check : zipCycle p 1 13 true (-1) = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 1 13 true (-1) (by decide) check B
#print axioms cover
end Leaf016

/- OneLE: E0=0RA, A1=0RD -/
namespace Leaf017
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨false,true,0⟩))
    (0, true) (some ⟨false,true,3⟩)
theorem check : zipCycle p 9 1 false 1 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 9 1 false 1 (by decide) check B
#print axioms cover
end Leaf017

/- OneLE: E0=0RA, A1=1LD -/
namespace Leaf018
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨false,true,0⟩))
    (0, true) (some ⟨true,false,3⟩)
theorem check : zipCycle p 9 1 false (-1) = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 9 1 false (-1) (by decide) check B
#print axioms cover
end Leaf018

/- OneLE: E0=0RA, A1=1LE -/
namespace Leaf019
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨false,true,0⟩))
    (0, true) (some ⟨true,false,4⟩)
theorem check : zipCycle p 7 2 false 0 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 7 2 false 0 (by decide) check B
#print axioms cover
end Leaf019

/- OneLE: E0=0RC, C1=0LC -/
namespace Leaf020
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨false,true,2⟩))
    (2, true) (some ⟨false,false,2⟩)
theorem check : zipCycle p 10 1 false 0 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 10 1 false 0 (by decide) check B
#print axioms cover
end Leaf020

/- OneLE: E0=0RC, C1=0LD -/
namespace Leaf021
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨false,true,2⟩))
    (2, true) (some ⟨false,false,3⟩)
theorem check : zipCycle p 9 1 false (-1) = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 9 1 false (-1) (by decide) check B
#print axioms cover
end Leaf021

/- OneLE: E0=0RC, C1=0LE -/
namespace Leaf022
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨false,true,2⟩))
    (2, true) (some ⟨false,false,4⟩)
theorem check : zipCycle p 11 1 false 1 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 11 1 false 1 (by decide) check B
#print axioms cover
end Leaf022

/- OneLE: E0=0RC, C1=0RC -/
namespace Leaf023
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨false,true,2⟩))
    (2, true) (some ⟨false,true,2⟩)
theorem check : zipCycle p 1 13 true (-1) = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 1 13 true (-1) (by decide) check B
#print axioms cover
end Leaf023

/- OneLE: E0=0RC, C1=0RD -/
namespace Leaf024
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨false,true,2⟩))
    (2, true) (some ⟨false,true,3⟩)
theorem check : zipCycle p 9 1 false 1 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 9 1 false 1 (by decide) check B
#print axioms cover
end Leaf024

/- OneLE: E0=0RC, C1=1LB -/
namespace Leaf025
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨false,true,2⟩))
    (2, true) (some ⟨true,false,1⟩)
theorem check : zipCycle p 6 5 false 0 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 6 5 false 0 (by decide) check B
#print axioms cover
end Leaf025

/- OneLE: E0=0RC, C1=1LD -/
namespace Leaf026
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨false,true,2⟩))
    (2, true) (some ⟨true,false,3⟩)
theorem check : zipCycle p 9 1 false (-1) = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 9 1 false (-1) (by decide) check B
#print axioms cover
end Leaf026

/- OneLE: E0=0RC, C1=1LE -/
namespace Leaf027
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨false,true,2⟩))
    (2, true) (some ⟨true,false,4⟩)
theorem check : zipCycle p 7 2 false 0 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 7 2 false 0 (by decide) check B
#print axioms cover
end Leaf027

/- OneLE: E0=0RD, E1=0LB -/
namespace Leaf028
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨false,true,3⟩))
    (4, true) (some ⟨false,false,1⟩)
theorem check : zipCycle p 73 24 false (-2) = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 73 24 false (-2) (by decide) check B
#print axioms cover
end Leaf028

/- OneLE: E0=0RD, E1=0LD -/
namespace Leaf029
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨false,true,3⟩))
    (4, true) (some ⟨false,false,3⟩)
theorem check : zipCycle p 55 1 false (-5) = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 55 1 false (-5) (by decide) check B
#print axioms cover
end Leaf029

/- OneLE: E0=0RD, E1=0LE -/
namespace Leaf030
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨false,true,3⟩))
    (4, true) (some ⟨false,false,4⟩)
theorem check : zipCycle p 36 1 false (-2) = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 36 1 false (-2) (by decide) check B
#print axioms cover
end Leaf030

/- OneLE: E0=0RD, E1=0RE -/
namespace Leaf031
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨false,true,3⟩))
    (4, true) (some ⟨false,true,4⟩)
theorem check : zipCycle p 1 38 true (-2) = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 1 38 true (-2) (by decide) check B
#print axioms cover
end Leaf031

/- OneLE: E0=0RD, E1=1LD -/
namespace Leaf032
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨false,true,3⟩))
    (4, true) (some ⟨true,false,3⟩)
theorem check : zipCycle p 5 28 false 4 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 5 28 false 4 (by decide) check B
#print axioms cover
end Leaf032

/- OneLE: E0=0RD, E1=1RB -/
namespace Leaf033
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨false,true,3⟩))
    (4, true) (some ⟨true,true,1⟩)
theorem check : zipCycle p 31 2 false 1 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 31 2 false 1 (by decide) check B
#print axioms cover
end Leaf033

/- OneLE: E0=0RD, E1=1RD -/
namespace Leaf034
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨false,true,3⟩))
    (4, true) (some ⟨true,true,3⟩)
theorem check : zipCycle p 36 22 false 0 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 36 22 false 0 (by decide) check B
#print axioms cover
end Leaf034

/- OneLE: E0=0RD, E1=1RE -/
namespace Leaf035
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨false,true,3⟩))
    (4, true) (some ⟨true,true,4⟩)
theorem check : zipCycle p 22 13 true 0 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 22 13 true 0 (by decide) check B
#print axioms cover
end Leaf035

/- OneLE: E0=0RE, E1=0LB -/
namespace Leaf036
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨false,true,4⟩))
    (4, true) (some ⟨false,false,1⟩)
theorem check : zipCycle p 73 24 false (-2) = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 73 24 false (-2) (by decide) check B
#print axioms cover
end Leaf036

/- OneLE: E0=0RE, E1=0LC -/
namespace Leaf037
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨false,true,4⟩))
    (4, true) (some ⟨false,false,2⟩)
theorem check : zipCycle p 10 1 false 0 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 10 1 false 0 (by decide) check B
#print axioms cover
end Leaf037

/- OneLE: E0=0RE, E1=0LD -/
namespace Leaf038
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨false,true,4⟩))
    (4, true) (some ⟨false,false,3⟩)
theorem check : zipCycle p 9 1 false (-1) = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 9 1 false (-1) (by decide) check B
#print axioms cover
end Leaf038

/- OneLE: E0=0RE, E1=0LE -/
namespace Leaf039
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨false,true,4⟩))
    (4, true) (some ⟨false,false,4⟩)
theorem check : zipCycle p 16 1 true 2 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 16 1 true 2 (by decide) check B
#print axioms cover
end Leaf039

/- OneLE: E0=0RE, E1=0RC -/
namespace Leaf040
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨false,true,4⟩))
    (4, true) (some ⟨false,true,2⟩)
theorem check : zipCycle p 1 13 true (-1) = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 1 13 true (-1) (by decide) check B
#print axioms cover
end Leaf040

/- OneLE: E0=0RE, E1=0RD -/
namespace Leaf041
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨false,true,4⟩))
    (4, true) (some ⟨false,true,3⟩)
theorem check : zipCycle p 9 1 false 1 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 9 1 false 1 (by decide) check B
#print axioms cover
end Leaf041

/- OneLE: E0=0RE, E1=0RE -/
namespace Leaf042
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨false,true,4⟩))
    (4, true) (some ⟨false,true,4⟩)
theorem check : zipCycle p 12 1 true 4 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 12 1 true 4 (by decide) check B
#print axioms cover
end Leaf042

/- OneLE: E0=0RE, E1=1LA -/
namespace Leaf043
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨false,true,4⟩))
    (4, true) (some ⟨true,false,0⟩)
theorem check : zipCycle p 8 3 false 0 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 8 3 false 0 (by decide) check B
#print axioms cover
end Leaf043

/- OneLE: E0=0RE, E1=1LD -/
namespace Leaf044
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨false,true,4⟩))
    (4, true) (some ⟨true,false,3⟩)
theorem check : zipCycle p 9 1 false (-1) = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 9 1 false (-1) (by decide) check B
#print axioms cover
end Leaf044

/- OneLE: E0=0RE, E1=1LE -/
namespace Leaf045
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨false,true,4⟩))
    (4, true) (some ⟨true,false,4⟩)
theorem check : zipCycle p 7 2 false 0 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 7 2 false 0 (by decide) check B
#print axioms cover
end Leaf045

/- OneLE: E0=0RE, E1=1RD -/
namespace Leaf046
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨false,true,4⟩))
    (4, true) (some ⟨true,true,3⟩)
theorem check : zipCycle p 1 38 false 4 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 1 38 false 4 (by decide) check B
#print axioms cover
end Leaf046

/- OneLE: E0=0RE, E1=1RE -/
namespace Leaf047
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨false,true,4⟩))
    (4, true) (some ⟨true,true,4⟩)
theorem check : zipCycle p 12 1 true 4 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 12 1 true 4 (by decide) check B
#print axioms cover
end Leaf047

/- OneLE: E0=0RF, F1=0LC -/
namespace Leaf048
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨false,true,5⟩))
    (5, true) (some ⟨false,false,2⟩)
theorem check : zipCycle p 10 1 false 0 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 10 1 false 0 (by decide) check B
#print axioms cover
end Leaf048

/- OneLE: E0=0RF, F1=0LD -/
namespace Leaf049
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨false,true,5⟩))
    (5, true) (some ⟨false,false,3⟩)
theorem check : zipCycle p 9 1 false (-1) = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 9 1 false (-1) (by decide) check B
#print axioms cover
end Leaf049

/- OneLE: E0=0RF, F1=0RC -/
namespace Leaf050
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨false,true,5⟩))
    (5, true) (some ⟨false,true,2⟩)
theorem check : zipCycle p 1 13 true (-1) = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 1 13 true (-1) (by decide) check B
#print axioms cover
end Leaf050

/- OneLE: E0=0RF, F1=0RD -/
namespace Leaf051
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨false,true,5⟩))
    (5, true) (some ⟨false,true,3⟩)
theorem check : zipCycle p 9 1 false 1 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 9 1 false 1 (by decide) check B
#print axioms cover
end Leaf051

/- OneLE: E0=0RF, F1=1LD -/
namespace Leaf052
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨false,true,5⟩))
    (5, true) (some ⟨true,false,3⟩)
theorem check : zipCycle p 9 1 false (-1) = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 9 1 false (-1) (by decide) check B
#print axioms cover
end Leaf052

/- OneLE: E0=0RF, F1=1LE -/
namespace Leaf053
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨false,true,5⟩))
    (5, true) (some ⟨true,false,4⟩)
theorem check : zipCycle p 7 2 false 0 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 7 2 false 0 (by decide) check B
#print axioms cover
end Leaf053

/- OneLE: E0=1LA, E1=0LB -/
namespace Leaf054
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨true,false,0⟩))
    (4, true) (some ⟨false,false,1⟩)
theorem check : zipCycle p 1 26 false 3 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 1 26 false 3 (by decide) check B
#print axioms cover
end Leaf054

/- OneLE: E0=1LA, E1=0LC -/
namespace Leaf055
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨true,false,0⟩))
    (4, true) (some ⟨false,false,2⟩)
theorem check : zipCycle p 12 1 false (-2) = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 12 1 false (-2) (by decide) check B
#print axioms cover
end Leaf055

/- OneLE: E0=1LA, E1=0LD -/
namespace Leaf056
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨true,false,0⟩))
    (4, true) (some ⟨false,false,3⟩)
theorem check : zipCycle p 11 1 false (-3) = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 11 1 false (-3) (by decide) check B
#print axioms cover
end Leaf056

/- OneLE: E0=1LA, E1=0LE -/
namespace Leaf057
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨true,false,0⟩))
    (4, true) (some ⟨false,false,4⟩)
theorem check : zipCycle p 7 4 false (-1) = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 7 4 false (-1) (by decide) check B
#print axioms cover
end Leaf057

/- OneLE: E0=1LA, E1=0RB -/
namespace Leaf058
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨true,false,0⟩))
    (4, true) (some ⟨false,true,1⟩)
theorem check : zipCycle p 6 5 false 0 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 6 5 false 0 (by decide) check B
#print axioms cover
end Leaf058

/- OneLE: E0=1LA, E1=0RD -/
namespace Leaf059
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨true,false,0⟩))
    (4, true) (some ⟨false,true,3⟩)
theorem check : zipCycle p 1 14 false 3 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 1 14 false 3 (by decide) check B
#print axioms cover
end Leaf059

/- OneLE: E0=1LA, E1=0RE -/
namespace Leaf060
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨true,false,0⟩))
    (4, true) (some ⟨false,true,4⟩)
theorem check : zipCycle p 18 5 true 2 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 18 5 true 2 (by decide) check B
#print axioms cover
end Leaf060

/- OneLE: E0=1LA, E1=1LA -/
namespace Leaf061
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨true,false,0⟩))
    (4, true) (some ⟨true,false,0⟩)
theorem check : zipCycle p 8 3 false (-1) = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 8 3 false (-1) (by decide) check B
#print axioms cover
end Leaf061

/- OneLE: E0=1LA, E1=1LC -/
namespace Leaf062
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨true,false,0⟩))
    (4, true) (some ⟨true,false,2⟩)
theorem check : zipCycle p 1 30 false 3 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 1 30 false 3 (by decide) check B
#print axioms cover
end Leaf062

/- OneLE: E0=1LA, E1=1LD -/
namespace Leaf063
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨true,false,0⟩))
    (4, true) (some ⟨true,false,3⟩)
theorem check : zipCycle p 11 1 false (-3) = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 11 1 false (-3) (by decide) check B
#print axioms cover
end Leaf063

/- OneLE: E0=1LA, E1=1LE -/
namespace Leaf064
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨true,false,0⟩))
    (4, true) (some ⟨true,false,4⟩)
theorem check : zipCycle p 7 4 false (-1) = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 7 4 false (-1) (by decide) check B
#print axioms cover
end Leaf064

/- OneLE: E0=1LA, E1=1RB -/
namespace Leaf065
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨true,false,0⟩))
    (4, true) (some ⟨true,true,1⟩)
theorem check : zipCycle p 9 2 false (-1) = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 9 2 false (-1) (by decide) check B
#print axioms cover
end Leaf065

/- OneLE: E0=1LA, E1=1RD -/
namespace Leaf066
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨true,false,0⟩))
    (4, true) (some ⟨true,true,3⟩)
theorem check : zipCycle p 5 6 false 1 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 5 6 false 1 (by decide) check B
#print axioms cover
end Leaf066

/- OneLE: E0=1LB, C1=0LB -/
namespace Leaf067
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨true,false,1⟩))
    (2, true) (some ⟨false,false,1⟩)
theorem check : zipCycle p 6 4 false 0 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 6 4 false 0 (by decide) check B
#print axioms cover
end Leaf067

/- OneLE: E0=1LB, C1=0LC -/
namespace Leaf068
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨true,false,1⟩))
    (2, true) (some ⟨false,false,2⟩)
theorem check : zipCycle p 12 1 false (-2) = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 12 1 false (-2) (by decide) check B
#print axioms cover
end Leaf068

/- OneLE: E0=1LB, C1=0RB -/
namespace Leaf069
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨true,false,1⟩))
    (2, true) (some ⟨false,true,1⟩)
theorem check : zipCycle p 6 6 false 0 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 6 6 false 0 (by decide) check B
#print axioms cover
end Leaf069

/- OneLE: E0=1LB, C1=0RC -/
namespace Leaf070
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨true,false,1⟩))
    (2, true) (some ⟨false,true,2⟩)
theorem check : zipCycle p 1 15 true (-2) = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 1 15 true (-2) (by decide) check B
#print axioms cover
end Leaf070

/- OneLE: E0=1LB, C1=0RD -/
namespace Leaf071
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨true,false,1⟩))
    (2, true) (some ⟨false,true,3⟩)
theorem check : zipCycle p 1 10 false 3 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 1 10 false 3 (by decide) check B
#print axioms cover
end Leaf071

/- OneLE: E0=1LB, C1=1LB -/
namespace Leaf072
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨true,false,1⟩))
    (2, true) (some ⟨true,false,1⟩)
theorem check : zipCycle p 6 4 false 0 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 6 4 false 0 (by decide) check B
#print axioms cover
end Leaf072

/- OneLE: E0=1LF, F0=0LC -/
namespace Leaf073
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨true,false,5⟩))
    (5, false) (some ⟨false,false,2⟩)
theorem check : zipCycle p 10 1 false (-2) = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 10 1 false (-2) (by decide) check B
#print axioms cover
end Leaf073

/- OneLE: E0=1LF, F0=0LD -/
namespace Leaf074
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨true,false,5⟩))
    (5, false) (some ⟨false,false,3⟩)
theorem check : zipCycle p 9 1 false (-3) = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 9 1 false (-3) (by decide) check B
#print axioms cover
end Leaf074

/- OneLE: E0=1LF, F0=0LE -/
namespace Leaf075
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨true,false,5⟩))
    (5, false) (some ⟨false,false,4⟩)
theorem check : zipCycle p 7 2 false (-1) = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 7 2 false (-1) (by decide) check B
#print axioms cover
end Leaf075

/- OneLE: E0=1LF, F0=0LF -/
namespace Leaf076
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨true,false,5⟩))
    (5, false) (some ⟨false,false,5⟩)
theorem check : zipCycle p 8 1 false (-2) = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 8 1 false (-2) (by decide) check B
#print axioms cover
end Leaf076

/- OneLE: E0=1LF, F0=0RB -/
namespace Leaf077
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨true,false,5⟩))
    (5, false) (some ⟨false,true,1⟩)
theorem check : zipCycle p 6 3 false 0 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 6 3 false 0 (by decide) check B
#print axioms cover
end Leaf077

/- OneLE: E0=1LF, F0=0RD -/
namespace Leaf078
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨true,false,5⟩))
    (5, false) (some ⟨false,true,3⟩)
theorem check : zipCycle p 1 12 false 3 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 1 12 false 3 (by decide) check B
#print axioms cover
end Leaf078

/- OneLE: E0=1LF, F0=1LD -/
namespace Leaf079
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨true,false,5⟩))
    (5, false) (some ⟨true,false,3⟩)
theorem check : zipCycle p 9 1 false (-3) = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 9 1 false (-3) (by decide) check B
#print axioms cover
end Leaf079

/- OneLE: E0=1LF, F0=1LE -/
namespace Leaf080
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨true,false,5⟩))
    (5, false) (some ⟨true,false,4⟩)
theorem check : zipCycle p 7 2 false (-1) = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 7 2 false (-1) (by decide) check B
#print axioms cover
end Leaf080

/- OneLE: E0=1LF, F0=1LF -/
namespace Leaf081
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨true,false,5⟩))
    (5, false) (some ⟨true,false,5⟩)
theorem check : zipCycle p 8 1 false (-2) = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 8 1 false (-2) (by decide) check B
#print axioms cover
end Leaf081

/- OneLE: E0=1LF, F0=1RD -/
namespace Leaf082
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨true,false,5⟩))
    (5, false) (some ⟨true,true,3⟩)
theorem check : zipCycle p 5 4 false 1 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 5 4 false 1 (by decide) check B
#print axioms cover
end Leaf082

/- OneLE: E0=1RA, A1=0LA -/
namespace Leaf083
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨true,true,0⟩))
    (0, true) (some ⟨false,false,0⟩)
theorem check : zipCycle p 0 10 false 3 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 0 10 false 3 (by decide) check B
#print axioms cover
end Leaf083

/- OneLE: E0=1RA, A1=0LB -/
namespace Leaf084
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨true,true,0⟩))
    (0, true) (some ⟨false,false,1⟩)
theorem check : zipCycle p 6 3 false 0 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 6 3 false 0 (by decide) check B
#print axioms cover
end Leaf084

/- OneLE: E0=1RA, A1=0RC -/
namespace Leaf085
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨true,true,0⟩))
    (0, true) (some ⟨false,true,2⟩)
theorem check : zipCycle p 1 13 true (-1) = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 1 13 true (-1) (by decide) check B
#print axioms cover
end Leaf085

/- OneLE: E0=1RA, A1=1LB -/
namespace Leaf086
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨true,true,0⟩))
    (0, true) (some ⟨true,false,1⟩)
theorem check : zipCycle p 6 3 false 0 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 6 3 false 0 (by decide) check B
#print axioms cover
end Leaf086

/- OneLE: E0=1RA, A1=1LD -/
namespace Leaf087
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨true,true,0⟩))
    (0, true) (some ⟨true,false,3⟩)
theorem check : zipCycle p 1 12 false 3 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 1 12 false 3 (by decide) check B
#print axioms cover
end Leaf087

/- OneLE: E0=1RA, A1=1RD -/
namespace Leaf088
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨true,true,0⟩))
    (0, true) (some ⟨true,true,3⟩)
theorem check : zipCycle p 4 5 false 2 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 4 5 false 2 (by decide) check B
#print axioms cover
end Leaf088

/- OneLE: E0=1RB, E1=0LB -/
namespace Leaf089
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨true,true,1⟩))
    (4, true) (some ⟨false,false,1⟩)
theorem check : zipCycle p 1 12 false 3 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 1 12 false 3 (by decide) check B
#print axioms cover
end Leaf089

/- OneLE: E0=1RB, E1=0LC -/
namespace Leaf090
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨true,true,1⟩))
    (4, true) (some ⟨false,false,2⟩)
theorem check : zipCycle p 11 1 false (-1) = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 11 1 false (-1) (by decide) check B
#print axioms cover
end Leaf090

/- OneLE: E0=1RB, E1=0LD -/
namespace Leaf091
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨true,true,1⟩))
    (4, true) (some ⟨false,false,3⟩)
theorem check : zipCycle p 10 1 false (-2) = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 10 1 false (-2) (by decide) check B
#print axioms cover
end Leaf091

/- OneLE: E0=1RB, E1=0RB -/
namespace Leaf092
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨true,true,1⟩))
    (4, true) (some ⟨false,true,1⟩)
theorem check : zipCycle p 6 4 false 0 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 6 4 false 0 (by decide) check B
#print axioms cover
end Leaf092

/- OneLE: E0=1RB, E1=0RE -/
namespace Leaf093
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨true,true,1⟩))
    (4, true) (some ⟨false,true,4⟩)
theorem check : zipCycle p 1 16 true (-1) = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 1 16 true (-1) (by decide) check B
#print axioms cover
end Leaf093

/- OneLE: E0=1RB, E1=1LA -/
namespace Leaf094
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨true,true,1⟩))
    (4, true) (some ⟨true,false,0⟩)
theorem check : zipCycle p 8 3 false 0 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 8 3 false 0 (by decide) check B
#print axioms cover
end Leaf094

/- OneLE: E0=1RB, E1=1LC -/
namespace Leaf095
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨true,true,1⟩))
    (4, true) (some ⟨true,false,2⟩)
theorem check : zipCycle p 1 14 false 3 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 1 14 false 3 (by decide) check B
#print axioms cover
end Leaf095

/- OneLE: E0=1RB, E1=1LD -/
namespace Leaf096
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨true,true,1⟩))
    (4, true) (some ⟨true,false,3⟩)
theorem check : zipCycle p 10 1 false (-2) = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 10 1 false (-2) (by decide) check B
#print axioms cover
end Leaf096

/- OneLE: E0=1RB, E1=1LE -/
namespace Leaf097
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨true,true,1⟩))
    (4, true) (some ⟨true,false,4⟩)
theorem check : zipCycle p 7 3 false 0 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 7 3 false 0 (by decide) check B
#print axioms cover
end Leaf097

/- OneLE: E0=1RB, E1=1RB -/
namespace Leaf098
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨true,true,1⟩))
    (4, true) (some ⟨true,true,1⟩)
theorem check : zipCycle p 8 2 false 0 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 8 2 false 0 (by decide) check B
#print axioms cover
end Leaf098

/- OneLE: E0=1RB, E1=1RD -/
namespace Leaf099
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨true,true,1⟩))
    (4, true) (some ⟨true,true,3⟩)
theorem check : zipCycle p 5 5 false 1 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 5 5 false 1 (by decide) check B
#print axioms cover
end Leaf099

/- OneLE: E0=1RB, E1=1RE -/
namespace Leaf100
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨true,true,1⟩))
    (4, true) (some ⟨true,true,4⟩)
theorem check : zipCycle p 8 14 true (-1) = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 8 14 true (-1) (by decide) check B
#print axioms cover
end Leaf100

/- OneLE: E0=1RC, C1=0LB -/
namespace Leaf101
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨true,true,2⟩))
    (2, true) (some ⟨false,false,1⟩)
theorem check : zipCycle p 6 3 false 0 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 6 3 false 0 (by decide) check B
#print axioms cover
end Leaf101

/- OneLE: E0=1RC, C1=0LC -/
namespace Leaf102
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨true,true,2⟩))
    (2, true) (some ⟨false,false,2⟩)
theorem check : zipCycle p 11 1 false (-1) = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 11 1 false (-1) (by decide) check B
#print axioms cover
end Leaf102

/- OneLE: E0=1RC, C1=0RC -/
namespace Leaf103
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨true,true,2⟩))
    (2, true) (some ⟨false,true,2⟩)
theorem check : zipCycle p 1 13 true (-1) = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 1 13 true (-1) (by decide) check B
#print axioms cover
end Leaf103

/- OneLE: E0=1RC, C1=1LB -/
namespace Leaf104
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨true,true,2⟩))
    (2, true) (some ⟨true,false,1⟩)
theorem check : zipCycle p 6 3 false 0 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 6 3 false 0 (by decide) check B
#print axioms cover
end Leaf104

/- OneLE: E0=1RC, C1=1LC -/
namespace Leaf105
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨true,true,2⟩))
    (2, true) (some ⟨true,false,2⟩)
theorem check : zipCycle p 1 14 false 3 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 1 14 false 3 (by decide) check B
#print axioms cover
end Leaf105

/- OneLE: E0=1RC, C1=1LD -/
namespace Leaf106
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨true,true,2⟩))
    (2, true) (some ⟨true,false,3⟩)
theorem check : zipCycle p 1 12 false 3 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 1 12 false 3 (by decide) check B
#print axioms cover
end Leaf106

/- OneLE: E0=1RC, C1=1RD -/
namespace Leaf107
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨true,true,2⟩))
    (2, true) (some ⟨true,true,3⟩)
theorem check : zipCycle p 4 5 false 2 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 4 5 false 2 (by decide) check B
#print axioms cover
end Leaf107

/- OneLE: E0=1RE, E1=0LB -/
namespace Leaf108
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨true,true,4⟩))
    (4, true) (some ⟨false,false,1⟩)
theorem check : zipCycle p 6 3 false 0 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 6 3 false 0 (by decide) check B
#print axioms cover
end Leaf108

/- OneLE: E0=1RE, E1=0LD -/
namespace Leaf109
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨true,true,4⟩))
    (4, true) (some ⟨false,false,3⟩)
theorem check : zipCycle p 28 1 false (-4) = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 28 1 false (-4) (by decide) check B
#print axioms cover
end Leaf109

/- OneLE: E0=1RE, E1=0LE -/
namespace Leaf110
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨true,true,4⟩))
    (4, true) (some ⟨false,false,4⟩)
theorem check : zipCycle p 32 1 true (-4) = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 32 1 true (-4) (by decide) check B
#print axioms cover
end Leaf110

/- OneLE: E0=1RE, E1=0RC -/
namespace Leaf111
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨true,true,4⟩))
    (4, true) (some ⟨false,true,2⟩)
theorem check : zipCycle p 1 13 true (-1) = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 1 13 true (-1) (by decide) check B
#print axioms cover
end Leaf111

/- OneLE: E0=1RE, E1=0RE -/
namespace Leaf112
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨true,true,4⟩))
    (4, true) (some ⟨false,true,4⟩)
theorem check : zipCycle p 12 1 true 4 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 12 1 true 4 (by decide) check B
#print axioms cover
end Leaf112

/- OneLE: E0=1RE, E1=1LB -/
namespace Leaf113
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨true,true,4⟩))
    (4, true) (some ⟨true,false,1⟩)
theorem check : zipCycle p 6 3 false 0 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 6 3 false 0 (by decide) check B
#print axioms cover
end Leaf113

/- OneLE: E0=1RE, E1=1LD -/
namespace Leaf114
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨true,true,4⟩))
    (4, true) (some ⟨true,false,3⟩)
theorem check : zipCycle p 1 12 false 3 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 1 12 false 3 (by decide) check B
#print axioms cover
end Leaf114

/- OneLE: E0=1RE, E1=1LE -/
namespace Leaf115
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨true,true,4⟩))
    (4, true) (some ⟨true,false,4⟩)
theorem check : zipCycle p 7 3 false 0 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 7 3 false 0 (by decide) check B
#print axioms cover
end Leaf115

/- OneLE: E0=1RE, E1=1RD -/
namespace Leaf116
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨true,true,4⟩))
    (4, true) (some ⟨true,true,3⟩)
theorem check : zipCycle p 4 5 false 2 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 4 5 false 2 (by decide) check B
#print axioms cover
end Leaf116

/- OneLE: E0=1RE, E1=1RE -/
namespace Leaf117
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨true,true,4⟩))
    (4, true) (some ⟨true,true,4⟩)
theorem check : zipCycle p 12 1 true 4 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 12 1 true 4 (by decide) check B
#print axioms cover
end Leaf117

/- OneLE: E0=1RF, F1=0LB -/
namespace Leaf118
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨true,true,5⟩))
    (5, true) (some ⟨false,false,1⟩)
theorem check : zipCycle p 6 3 false 0 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 6 3 false 0 (by decide) check B
#print axioms cover
end Leaf118

/- OneLE: E0=1RF, F1=0RC -/
namespace Leaf119
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨true,true,5⟩))
    (5, true) (some ⟨false,true,2⟩)
theorem check : zipCycle p 1 13 true (-1) = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 1 13 true (-1) (by decide) check B
#print axioms cover
end Leaf119

/- OneLE: E0=1RF, F1=1LB -/
namespace Leaf120
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨true,true,5⟩))
    (5, true) (some ⟨true,false,1⟩)
theorem check : zipCycle p 6 3 false 0 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 6 3 false 0 (by decide) check B
#print axioms cover
end Leaf120

/- OneLE: E0=1RF, F1=1LD -/
namespace Leaf121
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨true,true,5⟩))
    (5, true) (some ⟨true,false,3⟩)
theorem check : zipCycle p 1 12 false 3 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 1 12 false 3 (by decide) check B
#print axioms cover
end Leaf121

/- OneLE: E0=1RF, F1=1RD -/
namespace Leaf122
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨true,true,5⟩))
    (5, true) (some ⟨true,true,3⟩)
theorem check : zipCycle p 4 5 false 2 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 4 5 false 2 (by decide) check B
#print axioms cover
end Leaf122

end BB6.Agent32Raw42OneLEThirdBatch
