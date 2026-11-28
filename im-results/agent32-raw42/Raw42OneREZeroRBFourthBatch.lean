import Raw42Cut
/-!
One additional independently kernel-checkable layer for the Raw42
B1=1RE, E0=0RB unresolved subchild. Here E1 is the third fixed transition
and its first next fresh queried slot is the fourth fixed transition.
Each certificate leaves THREE unrestricted transition slots, proving
nonhalting of 25^3 raw completions. A finite JS search discovers candidate
witnesses; Lean's zipCycle and zipCycle_sound establish correctness.
-/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
namespace BB6.Agent32Raw42OneREZeroRBFourthBatch
open BB6Coverage BB6.Agent13BlankDelay BB6Coverage.Agent10ZipAudit
abbrev base : PartialMachine :=
  refine (BB6.Agent32Raw42.child ⟨true,true,4⟩) (4,false) (some ⟨false,true,1⟩)
private theorem zipper_cover
    (p : PartialMachine) (e k : Nat) (right : Bool) (boundary : Int)
    (hk : 0 < k) (hc : zipCycle p e k right boundary = true) (B : Nat) :
    Cover (WeightedBound B) p := by
  apply Cover.leaf p
  intro m hm
  exact weighted_never B m (zipCycle_sound p e k right boundary hk hc m hm)

/- E1=0LA, then A1=0LA -/
namespace Leaf000
abbrev p : PartialMachine :=
  refine (refine base (4,true) (some ⟨false,false,0⟩))
    (0, true) (some ⟨false,false,0⟩)
theorem check : zipCycle p 0 11 true 0 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 0 11 true 0 (by decide) check B
#print axioms cover
end Leaf000

/- E1=0LA, then A1=0LB -/
namespace Leaf001
abbrev p : PartialMachine :=
  refine (refine base (4,true) (some ⟨false,false,0⟩))
    (0, true) (some ⟨false,false,1⟩)
theorem check : zipCycle p 1 10 false 3 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 1 10 false 3 (by decide) check B
#print axioms cover
end Leaf001

/- E1=0LA, then A1=0LC -/
namespace Leaf002
abbrev p : PartialMachine :=
  refine (refine base (4,true) (some ⟨false,false,0⟩))
    (0, true) (some ⟨false,false,2⟩)
theorem check : zipCycle p 2 29 false 3 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 2 29 false 3 (by decide) check B
#print axioms cover
end Leaf002

/- E1=0LA, then A1=0LD -/
namespace Leaf003
abbrev p : PartialMachine :=
  refine (refine base (4,true) (some ⟨false,false,0⟩))
    (0, true) (some ⟨false,false,3⟩)
theorem check : zipCycle p 1 15 false 3 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 1 15 false 3 (by decide) check B
#print axioms cover
end Leaf003

/- E1=0LA, then A1=0LE -/
namespace Leaf004
abbrev p : PartialMachine :=
  refine (refine base (4,true) (some ⟨false,false,0⟩))
    (0, true) (some ⟨false,false,4⟩)
theorem check : zipCycle p 1 22 true 0 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 1 22 true 0 (by decide) check B
#print axioms cover
end Leaf004

/- E1=0LA, then A1=0RA -/
namespace Leaf005
abbrev p : PartialMachine :=
  refine (refine base (4,true) (some ⟨false,false,0⟩))
    (0, true) (some ⟨false,true,0⟩)
theorem check : zipCycle p 0 11 true 0 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 0 11 true 0 (by decide) check B
#print axioms cover
end Leaf005

/- E1=0LA, then A1=0RB -/
namespace Leaf006
abbrev p : PartialMachine :=
  refine (refine base (4,true) (some ⟨false,false,0⟩))
    (0, true) (some ⟨false,true,1⟩)
theorem check : zipCycle p 1 21 true 0 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 1 21 true 0 (by decide) check B
#print axioms cover
end Leaf006

/- E1=0LA, then A1=0RC -/
namespace Leaf007
abbrev p : PartialMachine :=
  refine (refine base (4,true) (some ⟨false,false,0⟩))
    (0, true) (some ⟨false,true,2⟩)
theorem check : zipCycle p 1 54 true (-1) = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 1 54 true (-1) (by decide) check B
#print axioms cover
end Leaf007

/- E1=0LA, then A1=0RE -/
namespace Leaf008
abbrev p : PartialMachine :=
  refine (refine base (4,true) (some ⟨false,false,0⟩))
    (0, true) (some ⟨false,true,4⟩)
theorem check : zipCycle p 1 22 true 0 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 1 22 true 0 (by decide) check B
#print axioms cover
end Leaf008

/- E1=0LA, then A1=1LA -/
namespace Leaf009
abbrev p : PartialMachine :=
  refine (refine base (4,true) (some ⟨false,false,0⟩))
    (0, true) (some ⟨true,false,0⟩)
theorem check : zipCycle p 1 24 true 0 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 1 24 true 0 (by decide) check B
#print axioms cover
end Leaf009

/- E1=0LA, then A1=1LC -/
namespace Leaf010
abbrev p : PartialMachine :=
  refine (refine base (4,true) (some ⟨false,false,0⟩))
    (0, true) (some ⟨true,false,2⟩)
theorem check : zipCycle p 1 12 false 3 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 1 12 false 3 (by decide) check B
#print axioms cover
end Leaf010

/- E1=0LA, then A1=1LD -/
namespace Leaf011
abbrev p : PartialMachine :=
  refine (refine base (4,true) (some ⟨false,false,0⟩))
    (0, true) (some ⟨true,false,3⟩)
theorem check : zipCycle p 4 25 false 3 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 4 25 false 3 (by decide) check B
#print axioms cover
end Leaf011

/- E1=0LA, then A1=1LE -/
namespace Leaf012
abbrev p : PartialMachine :=
  refine (refine base (4,true) (some ⟨false,false,0⟩))
    (0, true) (some ⟨true,false,4⟩)
theorem check : zipCycle p 1 24 true 0 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 1 24 true 0 (by decide) check B
#print axioms cover
end Leaf012

/- E1=0LA, then A1=1RA -/
namespace Leaf013
abbrev p : PartialMachine :=
  refine (refine base (4,true) (some ⟨false,false,0⟩))
    (0, true) (some ⟨true,true,0⟩)
theorem check : zipCycle p 0 11 true 0 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 0 11 true 0 (by decide) check B
#print axioms cover
end Leaf013

/- E1=0LA, then A1=1RB -/
namespace Leaf014
abbrev p : PartialMachine :=
  refine (refine base (4,true) (some ⟨false,false,0⟩))
    (0, true) (some ⟨true,true,1⟩)
theorem check : zipCycle p 1 10 true 0 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 1 10 true 0 (by decide) check B
#print axioms cover
end Leaf014

/- E1=0LA, then A1=1RC -/
namespace Leaf015
abbrev p : PartialMachine :=
  refine (refine base (4,true) (some ⟨false,false,0⟩))
    (0, true) (some ⟨true,true,2⟩)
theorem check : zipCycle p 1 20 true 0 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 1 20 true 0 (by decide) check B
#print axioms cover
end Leaf015

/- E1=0LA, then A1=1RD -/
namespace Leaf016
abbrev p : PartialMachine :=
  refine (refine base (4,true) (some ⟨false,false,0⟩))
    (0, true) (some ⟨true,true,3⟩)
theorem check : zipCycle p 1 15 true 0 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 1 15 true 0 (by decide) check B
#print axioms cover
end Leaf016

/- E1=0LA, then A1=1RE -/
namespace Leaf017
abbrev p : PartialMachine :=
  refine (refine base (4,true) (some ⟨false,false,0⟩))
    (0, true) (some ⟨true,true,4⟩)
theorem check : zipCycle p 1 22 true 0 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 1 22 true 0 (by decide) check B
#print axioms cover
end Leaf017

/- E1=0LC, then C1=0LA -/
namespace Leaf018
abbrev p : PartialMachine :=
  refine (refine base (4,true) (some ⟨false,false,2⟩))
    (2, true) (some ⟨false,false,0⟩)
theorem check : zipCycle p 0 11 true 0 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 0 11 true 0 (by decide) check B
#print axioms cover
end Leaf018

/- E1=0LC, then C1=0LB -/
namespace Leaf019
abbrev p : PartialMachine :=
  refine (refine base (4,true) (some ⟨false,false,2⟩))
    (2, true) (some ⟨false,false,1⟩)
theorem check : zipCycle p 1 10 false 3 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 1 10 false 3 (by decide) check B
#print axioms cover
end Leaf019

/- E1=0LC, then C1=0LC -/
namespace Leaf020
abbrev p : PartialMachine :=
  refine (refine base (4,true) (some ⟨false,false,2⟩))
    (2, true) (some ⟨false,false,2⟩)
theorem check : zipCycle p 2 29 false 3 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 2 29 false 3 (by decide) check B
#print axioms cover
end Leaf020

/- E1=0LC, then C1=0LD -/
namespace Leaf021
abbrev p : PartialMachine :=
  refine (refine base (4,true) (some ⟨false,false,2⟩))
    (2, true) (some ⟨false,false,3⟩)
theorem check : zipCycle p 1 15 false 3 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 1 15 false 3 (by decide) check B
#print axioms cover
end Leaf021

/- E1=0LC, then C1=0LE -/
namespace Leaf022
abbrev p : PartialMachine :=
  refine (refine base (4,true) (some ⟨false,false,2⟩))
    (2, true) (some ⟨false,false,4⟩)
theorem check : zipCycle p 1 22 true 0 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 1 22 true 0 (by decide) check B
#print axioms cover
end Leaf022

/- E1=0LC, then C1=0RA -/
namespace Leaf023
abbrev p : PartialMachine :=
  refine (refine base (4,true) (some ⟨false,false,2⟩))
    (2, true) (some ⟨false,true,0⟩)
theorem check : zipCycle p 0 11 true 0 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 0 11 true 0 (by decide) check B
#print axioms cover
end Leaf023

/- E1=0LC, then C1=0RB -/
namespace Leaf024
abbrev p : PartialMachine :=
  refine (refine base (4,true) (some ⟨false,false,2⟩))
    (2, true) (some ⟨false,true,1⟩)
theorem check : zipCycle p 1 21 true 0 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 1 21 true 0 (by decide) check B
#print axioms cover
end Leaf024

/- E1=0LC, then C1=0RC -/
namespace Leaf025
abbrev p : PartialMachine :=
  refine (refine base (4,true) (some ⟨false,false,2⟩))
    (2, true) (some ⟨false,true,2⟩)
theorem check : zipCycle p 1 54 true (-1) = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 1 54 true (-1) (by decide) check B
#print axioms cover
end Leaf025

/- E1=0LC, then C1=0RE -/
namespace Leaf026
abbrev p : PartialMachine :=
  refine (refine base (4,true) (some ⟨false,false,2⟩))
    (2, true) (some ⟨false,true,4⟩)
theorem check : zipCycle p 1 22 true 0 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 1 22 true 0 (by decide) check B
#print axioms cover
end Leaf026

/- E1=0LC, then C1=1LA -/
namespace Leaf027
abbrev p : PartialMachine :=
  refine (refine base (4,true) (some ⟨false,false,2⟩))
    (2, true) (some ⟨true,false,0⟩)
theorem check : zipCycle p 1 24 true 0 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 1 24 true 0 (by decide) check B
#print axioms cover
end Leaf027

/- E1=0LC, then C1=1LB -/
namespace Leaf028
abbrev p : PartialMachine :=
  refine (refine base (4,true) (some ⟨false,false,2⟩))
    (2, true) (some ⟨true,false,1⟩)
theorem check : zipCycle p 15 5 false 1 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 15 5 false 1 (by decide) check B
#print axioms cover
end Leaf028

/- E1=0LC, then C1=1LC -/
namespace Leaf029
abbrev p : PartialMachine :=
  refine (refine base (4,true) (some ⟨false,false,2⟩))
    (2, true) (some ⟨true,false,2⟩)
theorem check : zipCycle p 1 12 false 3 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 1 12 false 3 (by decide) check B
#print axioms cover
end Leaf029

/- E1=0LC, then C1=1LD -/
namespace Leaf030
abbrev p : PartialMachine :=
  refine (refine base (4,true) (some ⟨false,false,2⟩))
    (2, true) (some ⟨true,false,3⟩)
theorem check : zipCycle p 4 25 false 3 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 4 25 false 3 (by decide) check B
#print axioms cover
end Leaf030

/- E1=0LC, then C1=1LE -/
namespace Leaf031
abbrev p : PartialMachine :=
  refine (refine base (4,true) (some ⟨false,false,2⟩))
    (2, true) (some ⟨true,false,4⟩)
theorem check : zipCycle p 1 24 true 0 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 1 24 true 0 (by decide) check B
#print axioms cover
end Leaf031

/- E1=0LC, then C1=1RA -/
namespace Leaf032
abbrev p : PartialMachine :=
  refine (refine base (4,true) (some ⟨false,false,2⟩))
    (2, true) (some ⟨true,true,0⟩)
theorem check : zipCycle p 0 11 true 0 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 0 11 true 0 (by decide) check B
#print axioms cover
end Leaf032

/- E1=0LC, then C1=1RB -/
namespace Leaf033
abbrev p : PartialMachine :=
  refine (refine base (4,true) (some ⟨false,false,2⟩))
    (2, true) (some ⟨true,true,1⟩)
theorem check : zipCycle p 1 10 true 0 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 1 10 true 0 (by decide) check B
#print axioms cover
end Leaf033

/- E1=0LC, then C1=1RC -/
namespace Leaf034
abbrev p : PartialMachine :=
  refine (refine base (4,true) (some ⟨false,false,2⟩))
    (2, true) (some ⟨true,true,2⟩)
theorem check : zipCycle p 1 20 true 0 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 1 20 true 0 (by decide) check B
#print axioms cover
end Leaf034

/- E1=0LC, then C1=1RD -/
namespace Leaf035
abbrev p : PartialMachine :=
  refine (refine base (4,true) (some ⟨false,false,2⟩))
    (2, true) (some ⟨true,true,3⟩)
theorem check : zipCycle p 1 15 true 0 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 1 15 true 0 (by decide) check B
#print axioms cover
end Leaf035

/- E1=0LC, then C1=1RE -/
namespace Leaf036
abbrev p : PartialMachine :=
  refine (refine base (4,true) (some ⟨false,false,2⟩))
    (2, true) (some ⟨true,true,4⟩)
theorem check : zipCycle p 1 22 true 0 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 1 22 true 0 (by decide) check B
#print axioms cover
end Leaf036

/- E1=0LF, then F1=0LA -/
namespace Leaf037
abbrev p : PartialMachine :=
  refine (refine base (4,true) (some ⟨false,false,5⟩))
    (5, true) (some ⟨false,false,0⟩)
theorem check : zipCycle p 0 11 true 0 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 0 11 true 0 (by decide) check B
#print axioms cover
end Leaf037

/- E1=0LF, then F1=0LB -/
namespace Leaf038
abbrev p : PartialMachine :=
  refine (refine base (4,true) (some ⟨false,false,5⟩))
    (5, true) (some ⟨false,false,1⟩)
theorem check : zipCycle p 1 10 false 3 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 1 10 false 3 (by decide) check B
#print axioms cover
end Leaf038

/- E1=0LF, then F1=0LC -/
namespace Leaf039
abbrev p : PartialMachine :=
  refine (refine base (4,true) (some ⟨false,false,5⟩))
    (5, true) (some ⟨false,false,2⟩)
theorem check : zipCycle p 2 29 false 3 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 2 29 false 3 (by decide) check B
#print axioms cover
end Leaf039

/- E1=0LF, then F1=0LD -/
namespace Leaf040
abbrev p : PartialMachine :=
  refine (refine base (4,true) (some ⟨false,false,5⟩))
    (5, true) (some ⟨false,false,3⟩)
theorem check : zipCycle p 1 15 false 3 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 1 15 false 3 (by decide) check B
#print axioms cover
end Leaf040

/- E1=0LF, then F1=0LE -/
namespace Leaf041
abbrev p : PartialMachine :=
  refine (refine base (4,true) (some ⟨false,false,5⟩))
    (5, true) (some ⟨false,false,4⟩)
theorem check : zipCycle p 1 22 true 0 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 1 22 true 0 (by decide) check B
#print axioms cover
end Leaf041

/- E1=0LF, then F1=0RA -/
namespace Leaf042
abbrev p : PartialMachine :=
  refine (refine base (4,true) (some ⟨false,false,5⟩))
    (5, true) (some ⟨false,true,0⟩)
theorem check : zipCycle p 0 11 true 0 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 0 11 true 0 (by decide) check B
#print axioms cover
end Leaf042

/- E1=0LF, then F1=0RB -/
namespace Leaf043
abbrev p : PartialMachine :=
  refine (refine base (4,true) (some ⟨false,false,5⟩))
    (5, true) (some ⟨false,true,1⟩)
theorem check : zipCycle p 1 21 true 0 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 1 21 true 0 (by decide) check B
#print axioms cover
end Leaf043

/- E1=0LF, then F1=0RC -/
namespace Leaf044
abbrev p : PartialMachine :=
  refine (refine base (4,true) (some ⟨false,false,5⟩))
    (5, true) (some ⟨false,true,2⟩)
theorem check : zipCycle p 1 54 true (-1) = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 1 54 true (-1) (by decide) check B
#print axioms cover
end Leaf044

/- E1=0LF, then F1=0RE -/
namespace Leaf045
abbrev p : PartialMachine :=
  refine (refine base (4,true) (some ⟨false,false,5⟩))
    (5, true) (some ⟨false,true,4⟩)
theorem check : zipCycle p 1 22 true 0 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 1 22 true 0 (by decide) check B
#print axioms cover
end Leaf045

/- E1=0LF, then F1=1LA -/
namespace Leaf046
abbrev p : PartialMachine :=
  refine (refine base (4,true) (some ⟨false,false,5⟩))
    (5, true) (some ⟨true,false,0⟩)
theorem check : zipCycle p 1 24 true 0 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 1 24 true 0 (by decide) check B
#print axioms cover
end Leaf046

/- E1=0LF, then F1=1LC -/
namespace Leaf047
abbrev p : PartialMachine :=
  refine (refine base (4,true) (some ⟨false,false,5⟩))
    (5, true) (some ⟨true,false,2⟩)
theorem check : zipCycle p 1 12 false 3 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 1 12 false 3 (by decide) check B
#print axioms cover
end Leaf047

/- E1=0LF, then F1=1LD -/
namespace Leaf048
abbrev p : PartialMachine :=
  refine (refine base (4,true) (some ⟨false,false,5⟩))
    (5, true) (some ⟨true,false,3⟩)
theorem check : zipCycle p 4 25 false 3 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 4 25 false 3 (by decide) check B
#print axioms cover
end Leaf048

/- E1=0LF, then F1=1LE -/
namespace Leaf049
abbrev p : PartialMachine :=
  refine (refine base (4,true) (some ⟨false,false,5⟩))
    (5, true) (some ⟨true,false,4⟩)
theorem check : zipCycle p 1 24 true 0 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 1 24 true 0 (by decide) check B
#print axioms cover
end Leaf049

/- E1=0LF, then F1=1RA -/
namespace Leaf050
abbrev p : PartialMachine :=
  refine (refine base (4,true) (some ⟨false,false,5⟩))
    (5, true) (some ⟨true,true,0⟩)
theorem check : zipCycle p 0 11 true 0 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 0 11 true 0 (by decide) check B
#print axioms cover
end Leaf050

/- E1=0LF, then F1=1RB -/
namespace Leaf051
abbrev p : PartialMachine :=
  refine (refine base (4,true) (some ⟨false,false,5⟩))
    (5, true) (some ⟨true,true,1⟩)
theorem check : zipCycle p 1 10 true 0 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 1 10 true 0 (by decide) check B
#print axioms cover
end Leaf051

/- E1=0LF, then F1=1RC -/
namespace Leaf052
abbrev p : PartialMachine :=
  refine (refine base (4,true) (some ⟨false,false,5⟩))
    (5, true) (some ⟨true,true,2⟩)
theorem check : zipCycle p 1 20 true 0 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 1 20 true 0 (by decide) check B
#print axioms cover
end Leaf052

/- E1=0LF, then F1=1RD -/
namespace Leaf053
abbrev p : PartialMachine :=
  refine (refine base (4,true) (some ⟨false,false,5⟩))
    (5, true) (some ⟨true,true,3⟩)
theorem check : zipCycle p 1 15 true 0 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 1 15 true 0 (by decide) check B
#print axioms cover
end Leaf053

/- E1=0LF, then F1=1RE -/
namespace Leaf054
abbrev p : PartialMachine :=
  refine (refine base (4,true) (some ⟨false,false,5⟩))
    (5, true) (some ⟨true,true,4⟩)
theorem check : zipCycle p 1 22 true 0 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 1 22 true 0 (by decide) check B
#print axioms cover
end Leaf054

/- E1=0RF, then F0=0LA -/
namespace Leaf055
abbrev p : PartialMachine :=
  refine (refine base (4,true) (some ⟨false,true,5⟩))
    (5, false) (some ⟨false,false,0⟩)
theorem check : zipCycle p 0 11 true 0 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 0 11 true 0 (by decide) check B
#print axioms cover
end Leaf055

/- E1=0RF, then F0=0LB -/
namespace Leaf056
abbrev p : PartialMachine :=
  refine (refine base (4,true) (some ⟨false,true,5⟩))
    (5, false) (some ⟨false,false,1⟩)
theorem check : zipCycle p 1 10 true 0 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 1 10 true 0 (by decide) check B
#print axioms cover
end Leaf056

/- E1=0RF, then F0=0LC -/
namespace Leaf057
abbrev p : PartialMachine :=
  refine (refine base (4,true) (some ⟨false,true,5⟩))
    (5, false) (some ⟨false,false,2⟩)
theorem check : zipCycle p 1 20 true 0 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 1 20 true 0 (by decide) check B
#print axioms cover
end Leaf057

/- E1=0RF, then F0=0LD -/
namespace Leaf058
abbrev p : PartialMachine :=
  refine (refine base (4,true) (some ⟨false,true,5⟩))
    (5, false) (some ⟨false,false,3⟩)
theorem check : zipCycle p 1 15 true 0 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 1 15 true 0 (by decide) check B
#print axioms cover
end Leaf058

/- E1=0RF, then F0=0LE -/
namespace Leaf059
abbrev p : PartialMachine :=
  refine (refine base (4,true) (some ⟨false,true,5⟩))
    (5, false) (some ⟨false,false,4⟩)
theorem check : zipCycle p 1 22 true 0 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 1 22 true 0 (by decide) check B
#print axioms cover
end Leaf059

/- E1=0RF, then F0=0RA -/
namespace Leaf060
abbrev p : PartialMachine :=
  refine (refine base (4,true) (some ⟨false,true,5⟩))
    (5, false) (some ⟨false,true,0⟩)
theorem check : zipCycle p 0 11 true 0 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 0 11 true 0 (by decide) check B
#print axioms cover
end Leaf060

/- E1=0RF, then F0=0RB -/
namespace Leaf061
abbrev p : PartialMachine :=
  refine (refine base (4,true) (some ⟨false,true,5⟩))
    (5, false) (some ⟨false,true,1⟩)
theorem check : zipCycle p 1 21 true 0 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 1 21 true 0 (by decide) check B
#print axioms cover
end Leaf061

/- E1=0RF, then F0=0RC -/
namespace Leaf062
abbrev p : PartialMachine :=
  refine (refine base (4,true) (some ⟨false,true,5⟩))
    (5, false) (some ⟨false,true,2⟩)
theorem check : zipCycle p 1 28 true 0 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 1 28 true 0 (by decide) check B
#print axioms cover
end Leaf062

/- E1=0RF, then F0=0RD -/
namespace Leaf063
abbrev p : PartialMachine :=
  refine (refine base (4,true) (some ⟨false,true,5⟩))
    (5, false) (some ⟨false,true,3⟩)
theorem check : zipCycle p 1 23 true 0 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 1 23 true 0 (by decide) check B
#print axioms cover
end Leaf063

/- E1=0RF, then F0=0RE -/
namespace Leaf064
abbrev p : PartialMachine :=
  refine (refine base (4,true) (some ⟨false,true,5⟩))
    (5, false) (some ⟨false,true,4⟩)
theorem check : zipCycle p 1 22 true 0 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 1 22 true 0 (by decide) check B
#print axioms cover
end Leaf064

/- E1=0RF, then F0=0RF -/
namespace Leaf065
abbrev p : PartialMachine :=
  refine (refine base (4,true) (some ⟨false,true,5⟩))
    (5, false) (some ⟨false,true,5⟩)
theorem check : zipCycle p 10 1 true 4 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 10 1 true 4 (by decide) check B
#print axioms cover
end Leaf065

/- E1=0RF, then F0=1LA -/
namespace Leaf066
abbrev p : PartialMachine :=
  refine (refine base (4,true) (some ⟨false,true,5⟩))
    (5, false) (some ⟨true,false,0⟩)
theorem check : zipCycle p 1 24 true 0 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 1 24 true 0 (by decide) check B
#print axioms cover
end Leaf066

/- E1=0RF, then F0=1LC -/
namespace Leaf067
abbrev p : PartialMachine :=
  refine (refine base (4,true) (some ⟨false,true,5⟩))
    (5, false) (some ⟨true,false,2⟩)
theorem check : zipCycle p 1 12 true 0 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 1 12 true 0 (by decide) check B
#print axioms cover
end Leaf067

/- E1=0RF, then F0=1LD -/
namespace Leaf068
abbrev p : PartialMachine :=
  refine (refine base (4,true) (some ⟨false,true,5⟩))
    (5, false) (some ⟨true,false,3⟩)
theorem check : zipCycle p 1 18 true 0 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 1 18 true 0 (by decide) check B
#print axioms cover
end Leaf068

/- E1=0RF, then F0=1LE -/
namespace Leaf069
abbrev p : PartialMachine :=
  refine (refine base (4,true) (some ⟨false,true,5⟩))
    (5, false) (some ⟨true,false,4⟩)
theorem check : zipCycle p 1 24 true 0 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 1 24 true 0 (by decide) check B
#print axioms cover
end Leaf069

/- E1=0RF, then F0=1RA -/
namespace Leaf070
abbrev p : PartialMachine :=
  refine (refine base (4,true) (some ⟨false,true,5⟩))
    (5, false) (some ⟨true,true,0⟩)
theorem check : zipCycle p 0 11 true 0 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 0 11 true 0 (by decide) check B
#print axioms cover
end Leaf070

/- E1=0RF, then F0=1RB -/
namespace Leaf071
abbrev p : PartialMachine :=
  refine (refine base (4,true) (some ⟨false,true,5⟩))
    (5, false) (some ⟨true,true,1⟩)
theorem check : zipCycle p 1 10 true 0 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 1 10 true 0 (by decide) check B
#print axioms cover
end Leaf071

/- E1=0RF, then F0=1RC -/
namespace Leaf072
abbrev p : PartialMachine :=
  refine (refine base (4,true) (some ⟨false,true,5⟩))
    (5, false) (some ⟨true,true,2⟩)
theorem check : zipCycle p 1 20 true 0 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 1 20 true 0 (by decide) check B
#print axioms cover
end Leaf072

/- E1=0RF, then F0=1RD -/
namespace Leaf073
abbrev p : PartialMachine :=
  refine (refine base (4,true) (some ⟨false,true,5⟩))
    (5, false) (some ⟨true,true,3⟩)
theorem check : zipCycle p 1 15 true 0 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 1 15 true 0 (by decide) check B
#print axioms cover
end Leaf073

/- E1=0RF, then F0=1RE -/
namespace Leaf074
abbrev p : PartialMachine :=
  refine (refine base (4,true) (some ⟨false,true,5⟩))
    (5, false) (some ⟨true,true,4⟩)
theorem check : zipCycle p 1 22 true 0 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 1 22 true 0 (by decide) check B
#print axioms cover
end Leaf074

/- E1=0RF, then F0=1RF -/
namespace Leaf075
abbrev p : PartialMachine :=
  refine (refine base (4,true) (some ⟨false,true,5⟩))
    (5, false) (some ⟨true,true,5⟩)
theorem check : zipCycle p 10 1 true 4 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 10 1 true 4 (by decide) check B
#print axioms cover
end Leaf075

/- E1=1LA, then A1=0LB -/
namespace Leaf076
abbrev p : PartialMachine :=
  refine (refine base (4,true) (some ⟨true,false,0⟩))
    (0, true) (some ⟨false,false,1⟩)
theorem check : zipCycle p 1 13 true 0 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 1 13 true 0 (by decide) check B
#print axioms cover
end Leaf076

/- E1=1LA, then A1=0LD -/
namespace Leaf077
abbrev p : PartialMachine :=
  refine (refine base (4,true) (some ⟨true,false,0⟩))
    (0, true) (some ⟨false,false,3⟩)
theorem check : zipCycle p 1 15 false 3 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 1 15 false 3 (by decide) check B
#print axioms cover
end Leaf077

/- E1=1LA, then A1=0RA -/
namespace Leaf078
abbrev p : PartialMachine :=
  refine (refine base (4,true) (some ⟨true,false,0⟩))
    (0, true) (some ⟨false,true,0⟩)
theorem check : zipCycle p 0 12 true 0 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 0 12 true 0 (by decide) check B
#print axioms cover
end Leaf078

/- E1=1LA, then A1=0RB -/
namespace Leaf079
abbrev p : PartialMachine :=
  refine (refine base (4,true) (some ⟨true,false,0⟩))
    (0, true) (some ⟨false,true,1⟩)
theorem check : zipCycle p 1 23 true 0 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 1 23 true 0 (by decide) check B
#print axioms cover
end Leaf079

/- E1=1LA, then A1=0RD -/
namespace Leaf080
abbrev p : PartialMachine :=
  refine (refine base (4,true) (some ⟨true,false,0⟩))
    (0, true) (some ⟨false,true,3⟩)
theorem check : zipCycle p 1 22 true 0 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 1 22 true 0 (by decide) check B
#print axioms cover
end Leaf080

/- E1=1LA, then A1=0RE -/
namespace Leaf081
abbrev p : PartialMachine :=
  refine (refine base (4,true) (some ⟨true,false,0⟩))
    (0, true) (some ⟨false,true,4⟩)
theorem check : zipCycle p 1 25 true 0 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 1 25 true 0 (by decide) check B
#print axioms cover
end Leaf081

/- E1=1LA, then A1=1LA -/
namespace Leaf082
abbrev p : PartialMachine :=
  refine (refine base (4,true) (some ⟨true,false,0⟩))
    (0, true) (some ⟨true,false,0⟩)
theorem check : zipCycle p 15 5 false 1 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 15 5 false 1 (by decide) check B
#print axioms cover
end Leaf082

/- E1=1LA, then A1=1LC -/
namespace Leaf083
abbrev p : PartialMachine :=
  refine (refine base (4,true) (some ⟨true,false,0⟩))
    (0, true) (some ⟨true,false,2⟩)
theorem check : zipCycle p 1 15 true 0 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 1 15 true 0 (by decide) check B
#print axioms cover
end Leaf083

/- E1=1LA, then A1=1LE -/
namespace Leaf084
abbrev p : PartialMachine :=
  refine (refine base (4,true) (some ⟨true,false,0⟩))
    (0, true) (some ⟨true,false,4⟩)
theorem check : zipCycle p 7 4 false 3 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 7 4 false 3 (by decide) check B
#print axioms cover
end Leaf084

/- E1=1LA, then A1=1RA -/
namespace Leaf085
abbrev p : PartialMachine :=
  refine (refine base (4,true) (some ⟨true,false,0⟩))
    (0, true) (some ⟨true,true,0⟩)
theorem check : zipCycle p 0 12 true 0 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 0 12 true 0 (by decide) check B
#print axioms cover
end Leaf085

/- E1=1LA, then A1=1RB -/
namespace Leaf086
abbrev p : PartialMachine :=
  refine (refine base (4,true) (some ⟨true,false,0⟩))
    (0, true) (some ⟨true,true,1⟩)
theorem check : zipCycle p 1 23 true 0 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 1 23 true 0 (by decide) check B
#print axioms cover
end Leaf086

/- E1=1LA, then A1=1RD -/
namespace Leaf087
abbrev p : PartialMachine :=
  refine (refine base (4,true) (some ⟨true,false,0⟩))
    (0, true) (some ⟨true,true,3⟩)
theorem check : zipCycle p 1 24 true 0 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 1 24 true 0 (by decide) check B
#print axioms cover
end Leaf087

/- E1=1LA, then A1=1RE -/
namespace Leaf088
abbrev p : PartialMachine :=
  refine (refine base (4,true) (some ⟨true,false,0⟩))
    (0, true) (some ⟨true,true,4⟩)
theorem check : zipCycle p 9 2 false 3 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 9 2 false 3 (by decide) check B
#print axioms cover
end Leaf088

/- E1=1LC, then C1=0LB -/
namespace Leaf089
abbrev p : PartialMachine :=
  refine (refine base (4,true) (some ⟨true,false,2⟩))
    (2, true) (some ⟨false,false,1⟩)
theorem check : zipCycle p 1 13 true 0 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 1 13 true 0 (by decide) check B
#print axioms cover
end Leaf089

/- E1=1LC, then C1=0LD -/
namespace Leaf090
abbrev p : PartialMachine :=
  refine (refine base (4,true) (some ⟨true,false,2⟩))
    (2, true) (some ⟨false,false,3⟩)
theorem check : zipCycle p 1 15 false 3 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 1 15 false 3 (by decide) check B
#print axioms cover
end Leaf090

/- E1=1LC, then C1=0LE -/
namespace Leaf091
abbrev p : PartialMachine :=
  refine (refine base (4,true) (some ⟨true,false,2⟩))
    (2, true) (some ⟨false,false,4⟩)
theorem check : zipCycle p 1 16 false 3 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 1 16 false 3 (by decide) check B
#print axioms cover
end Leaf091

/- E1=1LC, then C1=0RB -/
namespace Leaf092
abbrev p : PartialMachine :=
  refine (refine base (4,true) (some ⟨true,false,2⟩))
    (2, true) (some ⟨false,true,1⟩)
theorem check : zipCycle p 1 23 true 0 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 1 23 true 0 (by decide) check B
#print axioms cover
end Leaf092

/- E1=1LC, then C1=0RD -/
namespace Leaf093
abbrev p : PartialMachine :=
  refine (refine base (4,true) (some ⟨true,false,2⟩))
    (2, true) (some ⟨false,true,3⟩)
theorem check : zipCycle p 1 22 true 0 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 1 22 true 0 (by decide) check B
#print axioms cover
end Leaf093

/- E1=1LC, then C1=0RE -/
namespace Leaf094
abbrev p : PartialMachine :=
  refine (refine base (4,true) (some ⟨true,false,2⟩))
    (2, true) (some ⟨false,true,4⟩)
theorem check : zipCycle p 1 24 true 0 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 1 24 true 0 (by decide) check B
#print axioms cover
end Leaf094

/- E1=1LC, then C1=1LB -/
namespace Leaf095
abbrev p : PartialMachine :=
  refine (refine base (4,true) (some ⟨true,false,2⟩))
    (2, true) (some ⟨true,false,1⟩)
theorem check : zipCycle p 15 5 false 1 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 15 5 false 1 (by decide) check B
#print axioms cover
end Leaf095

/- E1=1LC, then C1=1LC -/
namespace Leaf096
abbrev p : PartialMachine :=
  refine (refine base (4,true) (some ⟨true,false,2⟩))
    (2, true) (some ⟨true,false,2⟩)
theorem check : zipCycle p 1 15 true 0 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 1 15 true 0 (by decide) check B
#print axioms cover
end Leaf096

/- E1=1LC, then C1=1LE -/
namespace Leaf097
abbrev p : PartialMachine :=
  refine (refine base (4,true) (some ⟨true,false,2⟩))
    (2, true) (some ⟨true,false,4⟩)
theorem check : zipCycle p 7 4 false 3 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 7 4 false 3 (by decide) check B
#print axioms cover
end Leaf097

/- E1=1LC, then C1=1RB -/
namespace Leaf098
abbrev p : PartialMachine :=
  refine (refine base (4,true) (some ⟨true,false,2⟩))
    (2, true) (some ⟨true,true,1⟩)
theorem check : zipCycle p 1 23 true 0 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 1 23 true 0 (by decide) check B
#print axioms cover
end Leaf098

/- E1=1LC, then C1=1RC -/
namespace Leaf099
abbrev p : PartialMachine :=
  refine (refine base (4,true) (some ⟨true,false,2⟩))
    (2, true) (some ⟨true,true,2⟩)
theorem check : zipCycle p 2 10 true 0 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 2 10 true 0 (by decide) check B
#print axioms cover
end Leaf099

/- E1=1LC, then C1=1RD -/
namespace Leaf100
abbrev p : PartialMachine :=
  refine (refine base (4,true) (some ⟨true,false,2⟩))
    (2, true) (some ⟨true,true,3⟩)
theorem check : zipCycle p 1 24 true 0 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 1 24 true 0 (by decide) check B
#print axioms cover
end Leaf100

/- E1=1LC, then C1=1RE -/
namespace Leaf101
abbrev p : PartialMachine :=
  refine (refine base (4,true) (some ⟨true,false,2⟩))
    (2, true) (some ⟨true,true,4⟩)
theorem check : zipCycle p 9 2 false 3 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 9 2 false 3 (by decide) check B
#print axioms cover
end Leaf101

/- E1=1LF, then F1=0LB -/
namespace Leaf102
abbrev p : PartialMachine :=
  refine (refine base (4,true) (some ⟨true,false,5⟩))
    (5, true) (some ⟨false,false,1⟩)
theorem check : zipCycle p 1 13 true 0 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 1 13 true 0 (by decide) check B
#print axioms cover
end Leaf102

/- E1=1LF, then F1=0LD -/
namespace Leaf103
abbrev p : PartialMachine :=
  refine (refine base (4,true) (some ⟨true,false,5⟩))
    (5, true) (some ⟨false,false,3⟩)
theorem check : zipCycle p 1 15 false 3 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 1 15 false 3 (by decide) check B
#print axioms cover
end Leaf103

/- E1=1LF, then F1=0RB -/
namespace Leaf104
abbrev p : PartialMachine :=
  refine (refine base (4,true) (some ⟨true,false,5⟩))
    (5, true) (some ⟨false,true,1⟩)
theorem check : zipCycle p 1 23 true 0 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 1 23 true 0 (by decide) check B
#print axioms cover
end Leaf104

/- E1=1LF, then F1=0RD -/
namespace Leaf105
abbrev p : PartialMachine :=
  refine (refine base (4,true) (some ⟨true,false,5⟩))
    (5, true) (some ⟨false,true,3⟩)
theorem check : zipCycle p 1 22 true 0 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 1 22 true 0 (by decide) check B
#print axioms cover
end Leaf105

/- E1=1LF, then F1=1LC -/
namespace Leaf106
abbrev p : PartialMachine :=
  refine (refine base (4,true) (some ⟨true,false,5⟩))
    (5, true) (some ⟨true,false,2⟩)
theorem check : zipCycle p 1 15 true 0 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 1 15 true 0 (by decide) check B
#print axioms cover
end Leaf106

/- E1=1LF, then F1=1LE -/
namespace Leaf107
abbrev p : PartialMachine :=
  refine (refine base (4,true) (some ⟨true,false,5⟩))
    (5, true) (some ⟨true,false,4⟩)
theorem check : zipCycle p 7 4 false 3 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 7 4 false 3 (by decide) check B
#print axioms cover
end Leaf107

/- E1=1LF, then F1=1RB -/
namespace Leaf108
abbrev p : PartialMachine :=
  refine (refine base (4,true) (some ⟨true,false,5⟩))
    (5, true) (some ⟨true,true,1⟩)
theorem check : zipCycle p 1 23 true 0 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 1 23 true 0 (by decide) check B
#print axioms cover
end Leaf108

/- E1=1LF, then F1=1RD -/
namespace Leaf109
abbrev p : PartialMachine :=
  refine (refine base (4,true) (some ⟨true,false,5⟩))
    (5, true) (some ⟨true,true,3⟩)
theorem check : zipCycle p 1 24 true 0 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 1 24 true 0 (by decide) check B
#print axioms cover
end Leaf109

/- E1=1LF, then F1=1RE -/
namespace Leaf110
abbrev p : PartialMachine :=
  refine (refine base (4,true) (some ⟨true,false,5⟩))
    (5, true) (some ⟨true,true,4⟩)
theorem check : zipCycle p 9 2 false 3 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 9 2 false 3 (by decide) check B
#print axioms cover
end Leaf110

/- E1=1RF, then F0=0LB -/
namespace Leaf111
abbrev p : PartialMachine :=
  refine (refine base (4,true) (some ⟨true,true,5⟩))
    (5, false) (some ⟨false,false,1⟩)
theorem check : zipCycle p 1 23 true 0 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 1 23 true 0 (by decide) check B
#print axioms cover
end Leaf111

/- E1=1RF, then F0=0LD -/
namespace Leaf112
abbrev p : PartialMachine :=
  refine (refine base (4,true) (some ⟨true,true,5⟩))
    (5, false) (some ⟨false,false,3⟩)
theorem check : zipCycle p 1 24 true 0 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 1 24 true 0 (by decide) check B
#print axioms cover
end Leaf112

/- E1=1RF, then F0=0LE -/
namespace Leaf113
abbrev p : PartialMachine :=
  refine (refine base (4,true) (some ⟨true,true,5⟩))
    (5, false) (some ⟨false,false,4⟩)
theorem check : zipCycle p 9 2 false 4 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 9 2 false 4 (by decide) check B
#print axioms cover
end Leaf113

/- E1=1RF, then F0=0RA -/
namespace Leaf114
abbrev p : PartialMachine :=
  refine (refine base (4,true) (some ⟨true,true,5⟩))
    (5, false) (some ⟨false,true,0⟩)
theorem check : zipCycle p 0 11 true 0 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 0 11 true 0 (by decide) check B
#print axioms cover
end Leaf114

/- E1=1RF, then F0=0RB -/
namespace Leaf115
abbrev p : PartialMachine :=
  refine (refine base (4,true) (some ⟨true,true,5⟩))
    (5, false) (some ⟨false,true,1⟩)
theorem check : zipCycle p 1 21 true 0 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 1 21 true 0 (by decide) check B
#print axioms cover
end Leaf115

/- E1=1RF, then F0=0RD -/
namespace Leaf116
abbrev p : PartialMachine :=
  refine (refine base (4,true) (some ⟨true,true,5⟩))
    (5, false) (some ⟨false,true,3⟩)
theorem check : zipCycle p 3 8 true 0 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 3 8 true 0 (by decide) check B
#print axioms cover
end Leaf116

/- E1=1RF, then F0=0RE -/
namespace Leaf117
abbrev p : PartialMachine :=
  refine (refine base (4,true) (some ⟨true,true,5⟩))
    (5, false) (some ⟨false,true,4⟩)
theorem check : zipCycle p 1 22 true 0 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 1 22 true 0 (by decide) check B
#print axioms cover
end Leaf117

/- E1=1RF, then F0=0RF -/
namespace Leaf118
abbrev p : PartialMachine :=
  refine (refine base (4,true) (some ⟨true,true,5⟩))
    (5, false) (some ⟨false,true,5⟩)
theorem check : zipCycle p 10 1 true 4 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 10 1 true 4 (by decide) check B
#print axioms cover
end Leaf118

/- E1=1RF, then F0=1LB -/
namespace Leaf119
abbrev p : PartialMachine :=
  refine (refine base (4,true) (some ⟨true,true,5⟩))
    (5, false) (some ⟨true,false,1⟩)
theorem check : zipCycle p 8 3 true 2 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 8 3 true 2 (by decide) check B
#print axioms cover
end Leaf119

/- E1=1RF, then F0=1LD -/
namespace Leaf120
abbrev p : PartialMachine :=
  refine (refine base (4,true) (some ⟨true,true,5⟩))
    (5, false) (some ⟨true,false,3⟩)
theorem check : zipCycle p 1 26 true 0 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 1 26 true 0 (by decide) check B
#print axioms cover
end Leaf120

/- E1=1RF, then F0=1RA -/
namespace Leaf121
abbrev p : PartialMachine :=
  refine (refine base (4,true) (some ⟨true,true,5⟩))
    (5, false) (some ⟨true,true,0⟩)
theorem check : zipCycle p 0 11 true 0 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 0 11 true 0 (by decide) check B
#print axioms cover
end Leaf121

/- E1=1RF, then F0=1RB -/
namespace Leaf122
abbrev p : PartialMachine :=
  refine (refine base (4,true) (some ⟨true,true,5⟩))
    (5, false) (some ⟨true,true,1⟩)
theorem check : zipCycle p 1 10 true 0 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 1 10 true 0 (by decide) check B
#print axioms cover
end Leaf122

/- E1=1RF, then F0=1RC -/
namespace Leaf123
abbrev p : PartialMachine :=
  refine (refine base (4,true) (some ⟨true,true,5⟩))
    (5, false) (some ⟨true,true,2⟩)
theorem check : zipCycle p 2 9 true 0 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 2 9 true 0 (by decide) check B
#print axioms cover
end Leaf123

/- E1=1RF, then F0=1RD -/
namespace Leaf124
abbrev p : PartialMachine :=
  refine (refine base (4,true) (some ⟨true,true,5⟩))
    (5, false) (some ⟨true,true,3⟩)
theorem check : zipCycle p 1 27 true 0 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 1 27 true 0 (by decide) check B
#print axioms cover
end Leaf124

/- E1=1RF, then F0=1RE -/
namespace Leaf125
abbrev p : PartialMachine :=
  refine (refine base (4,true) (some ⟨true,true,5⟩))
    (5, false) (some ⟨true,true,4⟩)
theorem check : zipCycle p 1 22 true 0 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 1 22 true 0 (by decide) check B
#print axioms cover
end Leaf125

/- E1=1RF, then F0=1RF -/
namespace Leaf126
abbrev p : PartialMachine :=
  refine (refine base (4,true) (some ⟨true,true,5⟩))
    (5, false) (some ⟨true,true,5⟩)
theorem check : zipCycle p 10 1 true 4 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 10 1 true 4 (by decide) check B
#print axioms cover
end Leaf126

end BB6.Agent32Raw42OneREZeroRBFourthBatch
