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
namespace BB6.Agent32Raw42OneREThirdBatch
open BB6Coverage BB6.Agent13BlankDelay BB6Coverage.Agent10ZipAudit
abbrev base : PartialMachine := BB6.Agent32Raw42.child
  ⟨true,true,4⟩

private theorem zipper_cover
    (p : PartialMachine) (e k : Nat) (right : Bool) (boundary : Int)
    (hk : 0 < k) (hc : zipCycle p e k right boundary = true) (B : Nat) :
    Cover (WeightedBound B) p := by
  apply Cover.leaf p
  intro m hm
  exact weighted_never B m (zipCycle_sound p e k right boundary hk hc m hm)

/- OneRE: E0=0LA, A1=0LA -/
namespace Leaf000
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨false,false,0⟩))
    (0, true) (some ⟨false,false,0⟩)
theorem check : zipCycle p 0 26 false 4 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 0 26 false 4 (by decide) check B
#print axioms cover
end Leaf000

/- OneRE: E0=0LA, A1=0LB -/
namespace Leaf001
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨false,false,0⟩))
    (0, true) (some ⟨false,false,1⟩)
theorem check : zipCycle p 37 22 false 0 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 37 22 false 0 (by decide) check B
#print axioms cover
end Leaf001

/- OneRE: E0=0LA, A1=0LC -/
namespace Leaf002
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨false,false,0⟩))
    (0, true) (some ⟨false,false,2⟩)
theorem check : zipCycle p 10 1 false 0 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 10 1 false 0 (by decide) check B
#print axioms cover
end Leaf002

/- OneRE: E0=0LA, A1=0LD -/
namespace Leaf003
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨false,false,0⟩))
    (0, true) (some ⟨false,false,3⟩)
theorem check : zipCycle p 9 1 false -1 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 9 1 false -1 (by decide) check B
#print axioms cover
end Leaf003

/- OneRE: E0=0LA, A1=0LE -/
namespace Leaf004
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨false,false,0⟩))
    (0, true) (some ⟨false,false,4⟩)
theorem check : zipCycle p 0 10 false 3 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 0 10 false 3 (by decide) check B
#print axioms cover
end Leaf004

/- OneRE: E0=0LA, A1=0RC -/
namespace Leaf005
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨false,false,0⟩))
    (0, true) (some ⟨false,true,2⟩)
theorem check : zipCycle p 1 13 true 0 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 1 13 true 0 (by decide) check B
#print axioms cover
end Leaf005

/- OneRE: E0=0LA, A1=0RD -/
namespace Leaf006
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨false,false,0⟩))
    (0, true) (some ⟨false,true,3⟩)
theorem check : zipCycle p 9 1 false 1 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 9 1 false 1 (by decide) check B
#print axioms cover
end Leaf006

/- OneRE: E0=0LA, A1=1LD -/
namespace Leaf007
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨false,false,0⟩))
    (0, true) (some ⟨true,false,3⟩)
theorem check : zipCycle p 9 1 false -1 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 9 1 false -1 (by decide) check B
#print axioms cover
end Leaf007

/- OneRE: E0=0LA, A1=1RC -/
namespace Leaf008
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨false,false,0⟩))
    (0, true) (some ⟨true,true,2⟩)
theorem check : zipCycle p 1 13 true 0 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 1 13 true 0 (by decide) check B
#print axioms cover
end Leaf008

/- OneRE: E0=0LA, A1=1RE -/
namespace Leaf009
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨false,false,0⟩))
    (0, true) (some ⟨true,true,4⟩)
theorem check : zipCycle p 7 2 false 1 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 7 2 false 1 (by decide) check B
#print axioms cover
end Leaf009

/- OneRE: E0=0LC, C1=0LB -/
namespace Leaf010
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨false,false,2⟩))
    (2, true) (some ⟨false,false,1⟩)
theorem check : zipCycle p 37 22 false 0 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 37 22 false 0 (by decide) check B
#print axioms cover
end Leaf010

/- OneRE: E0=0LC, C1=0LC -/
namespace Leaf011
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨false,false,2⟩))
    (2, true) (some ⟨false,false,2⟩)
theorem check : zipCycle p 10 1 false 0 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 10 1 false 0 (by decide) check B
#print axioms cover
end Leaf011

/- OneRE: E0=0LC, C1=0LD -/
namespace Leaf012
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨false,false,2⟩))
    (2, true) (some ⟨false,false,3⟩)
theorem check : zipCycle p 9 1 false -1 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 9 1 false -1 (by decide) check B
#print axioms cover
end Leaf012

/- OneRE: E0=0LC, C1=0LE -/
namespace Leaf013
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨false,false,2⟩))
    (2, true) (some ⟨false,false,4⟩)
theorem check : zipCycle p 11 1 false -1 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 11 1 false -1 (by decide) check B
#print axioms cover
end Leaf013

/- OneRE: E0=0LC, C1=0RB -/
namespace Leaf014
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨false,false,2⟩))
    (2, true) (some ⟨false,true,1⟩)
theorem check : zipCycle p 1 24 true 0 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 1 24 true 0 (by decide) check B
#print axioms cover
end Leaf014

/- OneRE: E0=0LC, C1=0RC -/
namespace Leaf015
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨false,false,2⟩))
    (2, true) (some ⟨false,true,2⟩)
theorem check : zipCycle p 1 13 true 0 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 1 13 true 0 (by decide) check B
#print axioms cover
end Leaf015

/- OneRE: E0=0LC, C1=0RD -/
namespace Leaf016
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨false,false,2⟩))
    (2, true) (some ⟨false,true,3⟩)
theorem check : zipCycle p 9 1 false 1 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 9 1 false 1 (by decide) check B
#print axioms cover
end Leaf016

/- OneRE: E0=0LC, C1=0RE -/
namespace Leaf017
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨false,false,2⟩))
    (2, true) (some ⟨false,true,4⟩)
theorem check : zipCycle p 11 1 false 1 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 11 1 false 1 (by decide) check B
#print axioms cover
end Leaf017

/- OneRE: E0=0LC, C1=1LD -/
namespace Leaf018
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨false,false,2⟩))
    (2, true) (some ⟨true,false,3⟩)
theorem check : zipCycle p 9 1 false -1 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 9 1 false -1 (by decide) check B
#print axioms cover
end Leaf018

/- OneRE: E0=0LC, C1=1LE -/
namespace Leaf019
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨false,false,2⟩))
    (2, true) (some ⟨true,false,4⟩)
theorem check : zipCycle p 11 1 false -1 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 11 1 false -1 (by decide) check B
#print axioms cover
end Leaf019

/- OneRE: E0=0LC, C1=1RB -/
namespace Leaf020
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨false,false,2⟩))
    (2, true) (some ⟨true,true,1⟩)
theorem check : zipCycle p 1 13 true 0 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 1 13 true 0 (by decide) check B
#print axioms cover
end Leaf020

/- OneRE: E0=0LC, C1=1RC -/
namespace Leaf021
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨false,false,2⟩))
    (2, true) (some ⟨true,true,2⟩)
theorem check : zipCycle p 1 13 true 0 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 1 13 true 0 (by decide) check B
#print axioms cover
end Leaf021

/- OneRE: E0=0LC, C1=1RE -/
namespace Leaf022
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨false,false,2⟩))
    (2, true) (some ⟨true,true,4⟩)
theorem check : zipCycle p 7 2 false 1 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 7 2 false 1 (by decide) check B
#print axioms cover
end Leaf022

/- OneRE: E0=0LE, E1=0LB -/
namespace Leaf023
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨false,false,4⟩))
    (4, true) (some ⟨false,false,1⟩)
theorem check : zipCycle p 37 22 false 0 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 37 22 false 0 (by decide) check B
#print axioms cover
end Leaf023

/- OneRE: E0=0LE, E1=0LC -/
namespace Leaf024
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨false,false,4⟩))
    (4, true) (some ⟨false,false,2⟩)
theorem check : zipCycle p 10 1 false 0 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 10 1 false 0 (by decide) check B
#print axioms cover
end Leaf024

/- OneRE: E0=0LE, E1=0LD -/
namespace Leaf025
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨false,false,4⟩))
    (4, true) (some ⟨false,false,3⟩)
theorem check : zipCycle p 9 1 false -1 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 9 1 false -1 (by decide) check B
#print axioms cover
end Leaf025

/- OneRE: E0=0LE, E1=0LE -/
namespace Leaf026
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨false,false,4⟩))
    (4, true) (some ⟨false,false,4⟩)
theorem check : zipCycle p 9 1 false -1 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 9 1 false -1 (by decide) check B
#print axioms cover
end Leaf026

/- OneRE: E0=0LE, E1=0RA -/
namespace Leaf027
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨false,false,4⟩))
    (4, true) (some ⟨false,true,0⟩)
theorem check : zipCycle p 0 12 true 0 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 0 12 true 0 (by decide) check B
#print axioms cover
end Leaf027

/- OneRE: E0=0LE, E1=0RC -/
namespace Leaf028
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨false,false,4⟩))
    (4, true) (some ⟨false,true,2⟩)
theorem check : zipCycle p 1 13 true 0 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 1 13 true 0 (by decide) check B
#print axioms cover
end Leaf028

/- OneRE: E0=0LE, E1=0RD -/
namespace Leaf029
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨false,false,4⟩))
    (4, true) (some ⟨false,true,3⟩)
theorem check : zipCycle p 9 1 false 1 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 9 1 false 1 (by decide) check B
#print axioms cover
end Leaf029

/- OneRE: E0=0LE, E1=0RE -/
namespace Leaf030
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨false,false,4⟩))
    (4, true) (some ⟨false,true,4⟩)
theorem check : zipCycle p 9 1 false 1 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 9 1 false 1 (by decide) check B
#print axioms cover
end Leaf030

/- OneRE: E0=0LE, E1=1LD -/
namespace Leaf031
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨false,false,4⟩))
    (4, true) (some ⟨true,false,3⟩)
theorem check : zipCycle p 9 1 false -1 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 9 1 false -1 (by decide) check B
#print axioms cover
end Leaf031

/- OneRE: E0=0LE, E1=1LE -/
namespace Leaf032
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨false,false,4⟩))
    (4, true) (some ⟨true,false,4⟩)
theorem check : zipCycle p 9 1 false -1 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 9 1 false -1 (by decide) check B
#print axioms cover
end Leaf032

/- OneRE: E0=0LE, E1=1RA -/
namespace Leaf033
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨false,false,4⟩))
    (4, true) (some ⟨true,true,0⟩)
theorem check : zipCycle p 0 12 true 0 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 0 12 true 0 (by decide) check B
#print axioms cover
end Leaf033

/- OneRE: E0=0LE, E1=1RC -/
namespace Leaf034
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨false,false,4⟩))
    (4, true) (some ⟨true,true,2⟩)
theorem check : zipCycle p 1 13 true 0 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 1 13 true 0 (by decide) check B
#print axioms cover
end Leaf034

/- OneRE: E0=0LE, E1=1RE -/
namespace Leaf035
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨false,false,4⟩))
    (4, true) (some ⟨true,true,4⟩)
theorem check : zipCycle p 7 2 false 1 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 7 2 false 1 (by decide) check B
#print axioms cover
end Leaf035

/- OneRE: E0=0LF, F1=0LB -/
namespace Leaf036
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨false,false,5⟩))
    (5, true) (some ⟨false,false,1⟩)
theorem check : zipCycle p 37 22 false 0 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 37 22 false 0 (by decide) check B
#print axioms cover
end Leaf036

/- OneRE: E0=0LF, F1=0LC -/
namespace Leaf037
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨false,false,5⟩))
    (5, true) (some ⟨false,false,2⟩)
theorem check : zipCycle p 10 1 false 0 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 10 1 false 0 (by decide) check B
#print axioms cover
end Leaf037

/- OneRE: E0=0LF, F1=0LD -/
namespace Leaf038
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨false,false,5⟩))
    (5, true) (some ⟨false,false,3⟩)
theorem check : zipCycle p 9 1 false -1 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 9 1 false -1 (by decide) check B
#print axioms cover
end Leaf038

/- OneRE: E0=0LF, F1=0RC -/
namespace Leaf039
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨false,false,5⟩))
    (5, true) (some ⟨false,true,2⟩)
theorem check : zipCycle p 1 13 true 0 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 1 13 true 0 (by decide) check B
#print axioms cover
end Leaf039

/- OneRE: E0=0LF, F1=0RD -/
namespace Leaf040
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨false,false,5⟩))
    (5, true) (some ⟨false,true,3⟩)
theorem check : zipCycle p 9 1 false 1 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 9 1 false 1 (by decide) check B
#print axioms cover
end Leaf040

/- OneRE: E0=0LF, F1=1LD -/
namespace Leaf041
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨false,false,5⟩))
    (5, true) (some ⟨true,false,3⟩)
theorem check : zipCycle p 9 1 false -1 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 9 1 false -1 (by decide) check B
#print axioms cover
end Leaf041

/- OneRE: E0=0LF, F1=1RC -/
namespace Leaf042
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨false,false,5⟩))
    (5, true) (some ⟨true,true,2⟩)
theorem check : zipCycle p 1 13 true 0 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 1 13 true 0 (by decide) check B
#print axioms cover
end Leaf042

/- OneRE: E0=0LF, F1=1RE -/
namespace Leaf043
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨false,false,5⟩))
    (5, true) (some ⟨true,true,4⟩)
theorem check : zipCycle p 7 2 false 1 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 7 2 false 1 (by decide) check B
#print axioms cover
end Leaf043

/- OneRE: E0=0RA, A1=0LB -/
namespace Leaf044
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨false,true,0⟩))
    (0, true) (some ⟨false,false,1⟩)
theorem check : zipCycle p 1 11 true 0 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 1 11 true 0 (by decide) check B
#print axioms cover
end Leaf044

/- OneRE: E0=0RA, A1=0LD -/
namespace Leaf045
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨false,true,0⟩))
    (0, true) (some ⟨false,false,3⟩)
theorem check : zipCycle p 1 13 false 3 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 1 13 false 3 (by decide) check B
#print axioms cover
end Leaf045

/- OneRE: E0=0RA, A1=0LE -/
namespace Leaf046
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨false,true,0⟩))
    (0, true) (some ⟨false,false,4⟩)
theorem check : zipCycle p 0 13 true 0 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 0 13 true 0 (by decide) check B
#print axioms cover
end Leaf046

/- OneRE: E0=0RA, A1=0RA -/
namespace Leaf047
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨false,true,0⟩))
    (0, true) (some ⟨false,true,0⟩)
theorem check : zipCycle p 0 10 true 0 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 0 10 true 0 (by decide) check B
#print axioms cover
end Leaf047

/- OneRE: E0=0RA, A1=0RB -/
namespace Leaf048
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨false,true,0⟩))
    (0, true) (some ⟨false,true,1⟩)
theorem check : zipCycle p 0 11 true 0 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 0 11 true 0 (by decide) check B
#print axioms cover
end Leaf048

/- OneRE: E0=0RA, A1=0RD -/
namespace Leaf049
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨false,true,0⟩))
    (0, true) (some ⟨false,true,3⟩)
theorem check : zipCycle p 1 20 true 0 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 1 20 true 0 (by decide) check B
#print axioms cover
end Leaf049

/- OneRE: E0=0RA, A1=1LC -/
namespace Leaf050
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨false,true,0⟩))
    (0, true) (some ⟨true,false,2⟩)
theorem check : zipCycle p 1 13 true 0 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 1 13 true 0 (by decide) check B
#print axioms cover
end Leaf050

/- OneRE: E0=0RA, A1=1LE -/
namespace Leaf051
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨false,true,0⟩))
    (0, true) (some ⟨true,false,4⟩)
theorem check : zipCycle p 7 2 false 2 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 7 2 false 2 (by decide) check B
#print axioms cover
end Leaf051

/- OneRE: E0=0RA, A1=1RA -/
namespace Leaf052
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨false,true,0⟩))
    (0, true) (some ⟨true,true,0⟩)
theorem check : zipCycle p 0 10 true 0 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 0 10 true 0 (by decide) check B
#print axioms cover
end Leaf052

/- OneRE: E0=0RA, A1=1RB -/
namespace Leaf053
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨false,true,0⟩))
    (0, true) (some ⟨true,true,1⟩)
theorem check : zipCycle p 0 11 true 0 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 0 11 true 0 (by decide) check B
#print axioms cover
end Leaf053

/- OneRE: E0=0RA, A1=1RD -/
namespace Leaf054
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨false,true,0⟩))
    (0, true) (some ⟨true,true,3⟩)
theorem check : zipCycle p 0 12 true 0 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 0 12 true 0 (by decide) check B
#print axioms cover
end Leaf054

/- OneRE: E0=0RB, E1=0LB -/
namespace Leaf055
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨false,true,1⟩))
    (4, true) (some ⟨false,false,1⟩)
theorem check : zipCycle p 1 22 true 0 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 1 22 true 0 (by decide) check B
#print axioms cover
end Leaf055

/- OneRE: E0=0RB, E1=0LD -/
namespace Leaf056
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨false,true,1⟩))
    (4, true) (some ⟨false,false,3⟩)
theorem check : zipCycle p 1 10 false 3 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 1 10 false 3 (by decide) check B
#print axioms cover
end Leaf056

/- OneRE: E0=0RB, E1=0LE -/
namespace Leaf057
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨false,true,1⟩))
    (4, true) (some ⟨false,false,4⟩)
theorem check : zipCycle p 1 22 true 0 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 1 22 true 0 (by decide) check B
#print axioms cover
end Leaf057

/- OneRE: E0=0RB, E1=0RA -/
namespace Leaf058
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨false,true,1⟩))
    (4, true) (some ⟨false,true,0⟩)
theorem check : zipCycle p 0 10 true 0 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 0 10 true 0 (by decide) check B
#print axioms cover
end Leaf058

/- OneRE: E0=0RB, E1=0RB -/
namespace Leaf059
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨false,true,1⟩))
    (4, true) (some ⟨false,true,1⟩)
theorem check : zipCycle p 1 20 true 0 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 1 20 true 0 (by decide) check B
#print axioms cover
end Leaf059

/- OneRE: E0=0RB, E1=0RC -/
namespace Leaf060
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨false,true,1⟩))
    (4, true) (some ⟨false,true,2⟩)
theorem check : zipCycle p 1 23 true 0 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 1 23 true 0 (by decide) check B
#print axioms cover
end Leaf060

/- OneRE: E0=0RB, E1=0RD -/
namespace Leaf061
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨false,true,1⟩))
    (4, true) (some ⟨false,true,3⟩)
theorem check : zipCycle p 1 18 true 0 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 1 18 true 0 (by decide) check B
#print axioms cover
end Leaf061

/- OneRE: E0=0RB, E1=0RE -/
namespace Leaf062
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨false,true,1⟩))
    (4, true) (some ⟨false,true,4⟩)
theorem check : zipCycle p 1 21 true 0 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 1 21 true 0 (by decide) check B
#print axioms cover
end Leaf062

/- OneRE: E0=0RB, E1=1LB -/
namespace Leaf063
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨false,true,1⟩))
    (4, true) (some ⟨true,false,1⟩)
theorem check : zipCycle p 8 2 false 3 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 8 2 false 3 (by decide) check B
#print axioms cover
end Leaf063

/- OneRE: E0=0RB, E1=1LD -/
namespace Leaf064
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨false,true,1⟩))
    (4, true) (some ⟨true,false,3⟩)
theorem check : zipCycle p 1 13 true 0 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 1 13 true 0 (by decide) check B
#print axioms cover
end Leaf064

/- OneRE: E0=0RB, E1=1LE -/
namespace Leaf065
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨false,true,1⟩))
    (4, true) (some ⟨true,false,4⟩)
theorem check : zipCycle p 7 4 false 3 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 7 4 false 3 (by decide) check B
#print axioms cover
end Leaf065

/- OneRE: E0=0RB, E1=1RA -/
namespace Leaf066
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨false,true,1⟩))
    (4, true) (some ⟨true,true,0⟩)
theorem check : zipCycle p 0 10 true 0 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 0 10 true 0 (by decide) check B
#print axioms cover
end Leaf066

/- OneRE: E0=0RB, E1=1RB -/
namespace Leaf067
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨false,true,1⟩))
    (4, true) (some ⟨true,true,1⟩)
theorem check : zipCycle p 1 9 true 0 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 1 9 true 0 (by decide) check B
#print axioms cover
end Leaf067

/- OneRE: E0=0RB, E1=1RC -/
namespace Leaf068
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨false,true,1⟩))
    (4, true) (some ⟨true,true,2⟩)
theorem check : zipCycle p 2 8 true 0 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 2 8 true 0 (by decide) check B
#print axioms cover
end Leaf068

/- OneRE: E0=0RB, E1=1RD -/
namespace Leaf069
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨false,true,1⟩))
    (4, true) (some ⟨true,true,3⟩)
theorem check : zipCycle p 1 26 true 0 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 1 26 true 0 (by decide) check B
#print axioms cover
end Leaf069

/- OneRE: E0=0RB, E1=1RE -/
namespace Leaf070
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨false,true,1⟩))
    (4, true) (some ⟨true,true,4⟩)
theorem check : zipCycle p 1 21 true 0 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 1 21 true 0 (by decide) check B
#print axioms cover
end Leaf070

/- OneRE: E0=0RC, C1=0LB -/
namespace Leaf071
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨false,true,2⟩))
    (2, true) (some ⟨false,false,1⟩)
theorem check : zipCycle p 1 11 true 0 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 1 11 true 0 (by decide) check B
#print axioms cover
end Leaf071

/- OneRE: E0=0RC, C1=0LD -/
namespace Leaf072
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨false,true,2⟩))
    (2, true) (some ⟨false,false,3⟩)
theorem check : zipCycle p 1 13 false 3 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 1 13 false 3 (by decide) check B
#print axioms cover
end Leaf072

/- OneRE: E0=0RC, C1=0LE -/
namespace Leaf073
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨false,true,2⟩))
    (2, true) (some ⟨false,false,4⟩)
theorem check : zipCycle p 1 22 true 0 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 1 22 true 0 (by decide) check B
#print axioms cover
end Leaf073

/- OneRE: E0=0RC, C1=0RB -/
namespace Leaf074
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨false,true,2⟩))
    (2, true) (some ⟨false,true,1⟩)
theorem check : zipCycle p 1 24 true 0 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 1 24 true 0 (by decide) check B
#print axioms cover
end Leaf074

/- OneRE: E0=0RC, C1=0RD -/
namespace Leaf075
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨false,true,2⟩))
    (2, true) (some ⟨false,true,3⟩)
theorem check : zipCycle p 1 20 true 0 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 1 20 true 0 (by decide) check B
#print axioms cover
end Leaf075

/- OneRE: E0=0RC, C1=1LC -/
namespace Leaf076
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨false,true,2⟩))
    (2, true) (some ⟨true,false,2⟩)
theorem check : zipCycle p 1 13 true 0 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 1 13 true 0 (by decide) check B
#print axioms cover
end Leaf076

/- OneRE: E0=0RC, C1=1LE -/
namespace Leaf077
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨false,true,2⟩))
    (2, true) (some ⟨true,false,4⟩)
theorem check : zipCycle p 7 2 false 2 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 7 2 false 2 (by decide) check B
#print axioms cover
end Leaf077

/- OneRE: E0=0RC, C1=1RC -/
namespace Leaf078
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨false,true,2⟩))
    (2, true) (some ⟨true,true,2⟩)
theorem check : zipCycle p 2 8 true 0 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 2 8 true 0 (by decide) check B
#print axioms cover
end Leaf078

/- OneRE: E0=0RC, C1=1RD -/
namespace Leaf079
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨false,true,2⟩))
    (2, true) (some ⟨true,true,3⟩)
theorem check : zipCycle p 1 25 true 0 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 1 25 true 0 (by decide) check B
#print axioms cover
end Leaf079

/- OneRE: E0=0RE, E1=0LB -/
namespace Leaf080
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨false,true,4⟩))
    (4, true) (some ⟨false,false,1⟩)
theorem check : zipCycle p 1 11 true 0 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 1 11 true 0 (by decide) check B
#print axioms cover
end Leaf080

/- OneRE: E0=0RE, E1=0LD -/
namespace Leaf081
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨false,true,4⟩))
    (4, true) (some ⟨false,false,3⟩)
theorem check : zipCycle p 1 13 false 3 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 1 13 false 3 (by decide) check B
#print axioms cover
end Leaf081

/- OneRE: E0=0RE, E1=0LE -/
namespace Leaf082
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨false,true,4⟩))
    (4, true) (some ⟨false,false,4⟩)
theorem check : zipCycle p 12 1 true 2 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 12 1 true 2 (by decide) check B
#print axioms cover
end Leaf082

/- OneRE: E0=0RE, E1=0RB -/
namespace Leaf083
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨false,true,4⟩))
    (4, true) (some ⟨false,true,1⟩)
theorem check : zipCycle p 10 1 true 4 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 10 1 true 4 (by decide) check B
#print axioms cover
end Leaf083

/- OneRE: E0=0RE, E1=0RD -/
namespace Leaf084
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨false,true,4⟩))
    (4, true) (some ⟨false,true,3⟩)
theorem check : zipCycle p 1 20 true 0 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 1 20 true 0 (by decide) check B
#print axioms cover
end Leaf084

/- OneRE: E0=0RE, E1=0RE -/
namespace Leaf085
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨false,true,4⟩))
    (4, true) (some ⟨false,true,4⟩)
theorem check : zipCycle p 10 1 true 4 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 10 1 true 4 (by decide) check B
#print axioms cover
end Leaf085

/- OneRE: E0=0RE, E1=1LC -/
namespace Leaf086
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨false,true,4⟩))
    (4, true) (some ⟨true,false,2⟩)
theorem check : zipCycle p 1 13 true 0 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 1 13 true 0 (by decide) check B
#print axioms cover
end Leaf086

/- OneRE: E0=0RE, E1=1LE -/
namespace Leaf087
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨false,true,4⟩))
    (4, true) (some ⟨true,false,4⟩)
theorem check : zipCycle p 7 2 false 2 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 7 2 false 2 (by decide) check B
#print axioms cover
end Leaf087

/- OneRE: E0=0RE, E1=1RB -/
namespace Leaf088
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨false,true,4⟩))
    (4, true) (some ⟨true,true,1⟩)
theorem check : zipCycle p 10 1 true 4 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 10 1 true 4 (by decide) check B
#print axioms cover
end Leaf088

/- OneRE: E0=0RE, E1=1RD -/
namespace Leaf089
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨false,true,4⟩))
    (4, true) (some ⟨true,true,3⟩)
theorem check : zipCycle p 11 1 true 3 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 11 1 true 3 (by decide) check B
#print axioms cover
end Leaf089

/- OneRE: E0=0RE, E1=1RE -/
namespace Leaf090
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨false,true,4⟩))
    (4, true) (some ⟨true,true,4⟩)
theorem check : zipCycle p 10 1 true 4 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 10 1 true 4 (by decide) check B
#print axioms cover
end Leaf090

/- OneRE: E0=0RF, F1=0LB -/
namespace Leaf091
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨false,true,5⟩))
    (5, true) (some ⟨false,false,1⟩)
theorem check : zipCycle p 1 11 true 0 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 1 11 true 0 (by decide) check B
#print axioms cover
end Leaf091

/- OneRE: E0=0RF, F1=0LD -/
namespace Leaf092
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨false,true,5⟩))
    (5, true) (some ⟨false,false,3⟩)
theorem check : zipCycle p 1 13 false 3 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 1 13 false 3 (by decide) check B
#print axioms cover
end Leaf092

/- OneRE: E0=0RF, F1=0RD -/
namespace Leaf093
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨false,true,5⟩))
    (5, true) (some ⟨false,true,3⟩)
theorem check : zipCycle p 1 20 true 0 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 1 20 true 0 (by decide) check B
#print axioms cover
end Leaf093

/- OneRE: E0=0RF, F1=1LC -/
namespace Leaf094
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨false,true,5⟩))
    (5, true) (some ⟨true,false,2⟩)
theorem check : zipCycle p 1 13 true 0 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 1 13 true 0 (by decide) check B
#print axioms cover
end Leaf094

/- OneRE: E0=0RF, F1=1LE -/
namespace Leaf095
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨false,true,5⟩))
    (5, true) (some ⟨true,false,4⟩)
theorem check : zipCycle p 7 2 false 2 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 7 2 false 2 (by decide) check B
#print axioms cover
end Leaf095

/- OneRE: E0=1LA, A1=0LC -/
namespace Leaf096
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨true,false,0⟩))
    (0, true) (some ⟨false,false,2⟩)
theorem check : zipCycle p 10 1 false 0 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 10 1 false 0 (by decide) check B
#print axioms cover
end Leaf096

/- OneRE: E0=1LA, A1=0LD -/
namespace Leaf097
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨true,false,0⟩))
    (0, true) (some ⟨false,false,3⟩)
theorem check : zipCycle p 9 1 false -1 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 9 1 false -1 (by decide) check B
#print axioms cover
end Leaf097

/- OneRE: E0=1LA, A1=0RA -/
namespace Leaf098
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨true,false,0⟩))
    (0, true) (some ⟨false,true,0⟩)
theorem check : zipCycle p 0 12 true 0 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 0 12 true 0 (by decide) check B
#print axioms cover
end Leaf098

/- OneRE: E0=1LA, A1=0RD -/
namespace Leaf099
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨true,false,0⟩))
    (0, true) (some ⟨false,true,3⟩)
theorem check : zipCycle p 1 15 true 0 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 1 15 true 0 (by decide) check B
#print axioms cover
end Leaf099

/- OneRE: E0=1LA, A1=1LD -/
namespace Leaf100
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨true,false,0⟩))
    (0, true) (some ⟨true,false,3⟩)
theorem check : zipCycle p 9 1 false -1 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 9 1 false -1 (by decide) check B
#print axioms cover
end Leaf100

/- OneRE: E0=1LA, A1=1RA -/
namespace Leaf101
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨true,false,0⟩))
    (0, true) (some ⟨true,true,0⟩)
theorem check : zipCycle p 0 12 true 0 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 0 12 true 0 (by decide) check B
#print axioms cover
end Leaf101

/- OneRE: E0=1LA, A1=1RD -/
namespace Leaf102
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨true,false,0⟩))
    (0, true) (some ⟨true,true,3⟩)
theorem check : zipCycle p 5 4 false 1 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 5 4 false 1 (by decide) check B
#print axioms cover
end Leaf102

/- OneRE: E0=1LB, E1=0LB -/
namespace Leaf103
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨true,false,1⟩))
    (4, true) (some ⟨false,false,1⟩)
theorem check : zipCycle p 6 4 false 1 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 6 4 false 1 (by decide) check B
#print axioms cover
end Leaf103

/- OneRE: E0=1LB, E1=0LD -/
namespace Leaf104
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨true,false,1⟩))
    (4, true) (some ⟨false,false,3⟩)
theorem check : zipCycle p 42 26 false 0 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 42 26 false 0 (by decide) check B
#print axioms cover
end Leaf104

/- OneRE: E0=1LB, E1=0RB -/
namespace Leaf105
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨true,false,1⟩))
    (4, true) (some ⟨false,true,1⟩)
theorem check : zipCycle p 1 22 true 0 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 1 22 true 0 (by decide) check B
#print axioms cover
end Leaf105

/- OneRE: E0=1LB, E1=0RD -/
namespace Leaf106
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨true,false,1⟩))
    (4, true) (some ⟨false,true,3⟩)
theorem check : zipCycle p 1 13 true 0 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 1 13 true 0 (by decide) check B
#print axioms cover
end Leaf106

/- OneRE: E0=1LB, E1=1LB -/
namespace Leaf107
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨true,false,1⟩))
    (4, true) (some ⟨true,false,1⟩)
theorem check : zipCycle p 8 2 false 1 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 8 2 false 1 (by decide) check B
#print axioms cover
end Leaf107

/- OneRE: E0=1LB, E1=1RB -/
namespace Leaf108
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨true,false,1⟩))
    (4, true) (some ⟨true,true,1⟩)
theorem check : zipCycle p 1 11 true 0 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 1 11 true 0 (by decide) check B
#print axioms cover
end Leaf108

/- OneRE: E0=1LB, E1=1RD -/
namespace Leaf109
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨true,false,1⟩))
    (4, true) (some ⟨true,true,3⟩)
theorem check : zipCycle p 10 11 true 1 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 10 11 true 1 (by decide) check B
#print axioms cover
end Leaf109

/- OneRE: E0=1LB, E1=1RE -/
namespace Leaf110
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨true,false,1⟩))
    (4, true) (some ⟨true,true,4⟩)
theorem check : zipCycle p 11 3 true 3 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 11 3 true 3 (by decide) check B
#print axioms cover
end Leaf110

/- OneRE: E0=1LC, C1=0LC -/
namespace Leaf111
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨true,false,2⟩))
    (2, true) (some ⟨false,false,2⟩)
theorem check : zipCycle p 10 1 false 0 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 10 1 false 0 (by decide) check B
#print axioms cover
end Leaf111

/- OneRE: E0=1LC, C1=0LD -/
namespace Leaf112
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨true,false,2⟩))
    (2, true) (some ⟨false,false,3⟩)
theorem check : zipCycle p 9 1 false -1 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 9 1 false -1 (by decide) check B
#print axioms cover
end Leaf112

/- OneRE: E0=1LC, C1=0RC -/
namespace Leaf113
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨true,false,2⟩))
    (2, true) (some ⟨false,true,2⟩)
theorem check : zipCycle p 13 1 false 5 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 13 1 false 5 (by decide) check B
#print axioms cover
end Leaf113

/- OneRE: E0=1LC, C1=0RD -/
namespace Leaf114
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨true,false,2⟩))
    (2, true) (some ⟨false,true,3⟩)
theorem check : zipCycle p 1 15 true 0 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 1 15 true 0 (by decide) check B
#print axioms cover
end Leaf114

/- OneRE: E0=1LC, C1=1LD -/
namespace Leaf115
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨true,false,2⟩))
    (2, true) (some ⟨true,false,3⟩)
theorem check : zipCycle p 9 1 false -1 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 9 1 false -1 (by decide) check B
#print axioms cover
end Leaf115

/- OneRE: E0=1LC, C1=1RC -/
namespace Leaf116
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨true,false,2⟩))
    (2, true) (some ⟨true,true,2⟩)
theorem check : zipCycle p 2 10 true 0 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 2 10 true 0 (by decide) check B
#print axioms cover
end Leaf116

/- OneRE: E0=1LC, C1=1RD -/
namespace Leaf117
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨true,false,2⟩))
    (2, true) (some ⟨true,true,3⟩)
theorem check : zipCycle p 5 4 false 1 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 5 4 false 1 (by decide) check B
#print axioms cover
end Leaf117

/- OneRE: E0=1LE, E1=0LC -/
namespace Leaf118
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨true,false,4⟩))
    (4, true) (some ⟨false,false,2⟩)
theorem check : zipCycle p 10 1 false 0 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 10 1 false 0 (by decide) check B
#print axioms cover
end Leaf118

/- OneRE: E0=1LE, E1=0LD -/
namespace Leaf119
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨true,false,4⟩))
    (4, true) (some ⟨false,false,3⟩)
theorem check : zipCycle p 9 1 false -1 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 9 1 false -1 (by decide) check B
#print axioms cover
end Leaf119

/- OneRE: E0=1LE, E1=0LE -/
namespace Leaf120
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨true,false,4⟩))
    (4, true) (some ⟨false,false,4⟩)
theorem check : zipCycle p 9 1 false -1 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 9 1 false -1 (by decide) check B
#print axioms cover
end Leaf120

/- OneRE: E0=1LE, E1=0RB -/
namespace Leaf121
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨true,false,4⟩))
    (4, true) (some ⟨false,true,1⟩)
theorem check : zipCycle p 10 3 true 2 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 10 3 true 2 (by decide) check B
#print axioms cover
end Leaf121

/- OneRE: E0=1LE, E1=0RD -/
namespace Leaf122
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨true,false,4⟩))
    (4, true) (some ⟨false,true,3⟩)
theorem check : zipCycle p 1 15 true 0 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 1 15 true 0 (by decide) check B
#print axioms cover
end Leaf122

/- OneRE: E0=1LE, E1=0RE -/
namespace Leaf123
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨true,false,4⟩))
    (4, true) (some ⟨false,true,4⟩)
theorem check : zipCycle p 12 1 false 4 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 12 1 false 4 (by decide) check B
#print axioms cover
end Leaf123

/- OneRE: E0=1LE, E1=1LD -/
namespace Leaf124
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨true,false,4⟩))
    (4, true) (some ⟨true,false,3⟩)
theorem check : zipCycle p 9 1 false -1 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 9 1 false -1 (by decide) check B
#print axioms cover
end Leaf124

/- OneRE: E0=1LE, E1=1LE -/
namespace Leaf125
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨true,false,4⟩))
    (4, true) (some ⟨true,false,4⟩)
theorem check : zipCycle p 9 1 false -1 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 9 1 false -1 (by decide) check B
#print axioms cover
end Leaf125

/- OneRE: E0=1LE, E1=1RB -/
namespace Leaf126
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨true,false,4⟩))
    (4, true) (some ⟨true,true,1⟩)
theorem check : zipCycle p 10 3 true 2 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 10 3 true 2 (by decide) check B
#print axioms cover
end Leaf126

/- OneRE: E0=1LE, E1=1RD -/
namespace Leaf127
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨true,false,4⟩))
    (4, true) (some ⟨true,true,3⟩)
theorem check : zipCycle p 5 4 false 1 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 5 4 false 1 (by decide) check B
#print axioms cover
end Leaf127

/- OneRE: E0=1LE, E1=1RE -/
namespace Leaf128
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨true,false,4⟩))
    (4, true) (some ⟨true,true,4⟩)
theorem check : zipCycle p 10 3 true 2 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 10 3 true 2 (by decide) check B
#print axioms cover
end Leaf128

/- OneRE: E0=1LF, F1=0LC -/
namespace Leaf129
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨true,false,5⟩))
    (5, true) (some ⟨false,false,2⟩)
theorem check : zipCycle p 10 1 false 0 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 10 1 false 0 (by decide) check B
#print axioms cover
end Leaf129

/- OneRE: E0=1LF, F1=0LD -/
namespace Leaf130
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨true,false,5⟩))
    (5, true) (some ⟨false,false,3⟩)
theorem check : zipCycle p 9 1 false -1 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 9 1 false -1 (by decide) check B
#print axioms cover
end Leaf130

/- OneRE: E0=1LF, F1=0RD -/
namespace Leaf131
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨true,false,5⟩))
    (5, true) (some ⟨false,true,3⟩)
theorem check : zipCycle p 1 15 true 0 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 1 15 true 0 (by decide) check B
#print axioms cover
end Leaf131

/- OneRE: E0=1LF, F1=1LD -/
namespace Leaf132
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨true,false,5⟩))
    (5, true) (some ⟨true,false,3⟩)
theorem check : zipCycle p 9 1 false -1 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 9 1 false -1 (by decide) check B
#print axioms cover
end Leaf132

/- OneRE: E0=1LF, F1=1RD -/
namespace Leaf133
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨true,false,5⟩))
    (5, true) (some ⟨true,true,3⟩)
theorem check : zipCycle p 5 4 false 1 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 5 4 false 1 (by decide) check B
#print axioms cover
end Leaf133

/- OneRE: E0=1RA, A1=0LA -/
namespace Leaf134
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨true,true,0⟩))
    (0, true) (some ⟨false,false,0⟩)
theorem check : zipCycle p 0 11 false 3 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 0 11 false 3 (by decide) check B
#print axioms cover
end Leaf134

/- OneRE: E0=1RA, A1=0LB -/
namespace Leaf135
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨true,true,0⟩))
    (0, true) (some ⟨false,false,1⟩)
theorem check : zipCycle p 0 14 true 0 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 0 14 true 0 (by decide) check B
#print axioms cover
end Leaf135

/- OneRE: E0=1RA, A1=0LD -/
namespace Leaf136
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨true,true,0⟩))
    (0, true) (some ⟨false,false,3⟩)
theorem check : zipCycle p 0 15 true 0 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 0 15 true 0 (by decide) check B
#print axioms cover
end Leaf136

/- OneRE: E0=1RA, A1=0RA -/
namespace Leaf137
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨true,true,0⟩))
    (0, true) (some ⟨false,true,0⟩)
theorem check : zipCycle p 0 10 true 0 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 0 10 true 0 (by decide) check B
#print axioms cover
end Leaf137

/- OneRE: E0=1RA, A1=0RB -/
namespace Leaf138
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨true,true,0⟩))
    (0, true) (some ⟨false,true,1⟩)
theorem check : zipCycle p 0 11 true 0 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 0 11 true 0 (by decide) check B
#print axioms cover
end Leaf138

/- OneRE: E0=1RA, A1=0RD -/
namespace Leaf139
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨true,true,0⟩))
    (0, true) (some ⟨false,true,3⟩)
theorem check : zipCycle p 1 9 true 0 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 1 9 true 0 (by decide) check B
#print axioms cover
end Leaf139

/- OneRE: E0=1RA, A1=1LD -/
namespace Leaf140
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨true,true,0⟩))
    (0, true) (some ⟨true,false,3⟩)
theorem check : zipCycle p 5 4 false 2 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 5 4 false 2 (by decide) check B
#print axioms cover
end Leaf140

/- OneRE: E0=1RA, A1=1RA -/
namespace Leaf141
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨true,true,0⟩))
    (0, true) (some ⟨true,true,0⟩)
theorem check : zipCycle p 0 10 true 0 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 0 10 true 0 (by decide) check B
#print axioms cover
end Leaf141

/- OneRE: E0=1RA, A1=1RB -/
namespace Leaf142
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨true,true,0⟩))
    (0, true) (some ⟨true,true,1⟩)
theorem check : zipCycle p 0 11 true 0 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 0 11 true 0 (by decide) check B
#print axioms cover
end Leaf142

/- OneRE: E0=1RA, A1=1RD -/
namespace Leaf143
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨true,true,0⟩))
    (0, true) (some ⟨true,true,3⟩)
theorem check : zipCycle p 0 12 true 0 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 0 12 true 0 (by decide) check B
#print axioms cover
end Leaf143

/- OneRE: E0=1RB, E1=0LB -/
namespace Leaf144
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨true,true,1⟩))
    (4, true) (some ⟨false,false,1⟩)
theorem check : zipCycle p 1 11 true 0 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 1 11 true 0 (by decide) check B
#print axioms cover
end Leaf144

/- OneRE: E0=1RB, E1=0LD -/
namespace Leaf145
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨true,true,1⟩))
    (4, true) (some ⟨false,false,3⟩)
theorem check : zipCycle p 1 12 true 0 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 1 12 true 0 (by decide) check B
#print axioms cover
end Leaf145

/- OneRE: E0=1RB, E1=0LE -/
namespace Leaf146
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨true,true,1⟩))
    (4, true) (some ⟨false,false,4⟩)
theorem check : zipCycle p 1 13 false 3 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 1 13 false 3 (by decide) check B
#print axioms cover
end Leaf146

/- OneRE: E0=1RB, E1=0RA -/
namespace Leaf147
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨true,true,1⟩))
    (4, true) (some ⟨false,true,0⟩)
theorem check : zipCycle p 0 10 true 0 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 0 10 true 0 (by decide) check B
#print axioms cover
end Leaf147

/- OneRE: E0=1RB, E1=0RB -/
namespace Leaf148
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨true,true,1⟩))
    (4, true) (some ⟨false,true,1⟩)
theorem check : zipCycle p 1 20 true 0 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 1 20 true 0 (by decide) check B
#print axioms cover
end Leaf148

/- OneRE: E0=1RB, E1=0RD -/
namespace Leaf149
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨true,true,1⟩))
    (4, true) (some ⟨false,true,3⟩)
theorem check : zipCycle p 3 7 true 0 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 3 7 true 0 (by decide) check B
#print axioms cover
end Leaf149

/- OneRE: E0=1RB, E1=0RE -/
namespace Leaf150
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨true,true,1⟩))
    (4, true) (some ⟨false,true,4⟩)
theorem check : zipCycle p 1 10 true 0 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 1 10 true 0 (by decide) check B
#print axioms cover
end Leaf150

/- OneRE: E0=1RB, E1=1LB -/
namespace Leaf151
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨true,true,1⟩))
    (4, true) (some ⟨true,false,1⟩)
theorem check : zipCycle p 8 2 false 3 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 8 2 false 3 (by decide) check B
#print axioms cover
end Leaf151

/- OneRE: E0=1RB, E1=1LD -/
namespace Leaf152
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨true,true,1⟩))
    (4, true) (some ⟨true,false,3⟩)
theorem check : zipCycle p 1 14 true 0 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 1 14 true 0 (by decide) check B
#print axioms cover
end Leaf152

/- OneRE: E0=1RB, E1=1LE -/
namespace Leaf153
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨true,true,1⟩))
    (4, true) (some ⟨true,false,4⟩)
theorem check : zipCycle p 10 5 false 2 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 10 5 false 2 (by decide) check B
#print axioms cover
end Leaf153

/- OneRE: E0=1RB, E1=1RA -/
namespace Leaf154
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨true,true,1⟩))
    (4, true) (some ⟨true,true,0⟩)
theorem check : zipCycle p 0 10 true 0 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 0 10 true 0 (by decide) check B
#print axioms cover
end Leaf154

/- OneRE: E0=1RB, E1=1RB -/
namespace Leaf155
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨true,true,1⟩))
    (4, true) (some ⟨true,true,1⟩)
theorem check : zipCycle p 1 9 true 0 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 1 9 true 0 (by decide) check B
#print axioms cover
end Leaf155

/- OneRE: E0=1RB, E1=1RC -/
namespace Leaf156
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨true,true,1⟩))
    (4, true) (some ⟨true,true,2⟩)
theorem check : zipCycle p 2 8 true 0 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 2 8 true 0 (by decide) check B
#print axioms cover
end Leaf156

/- OneRE: E0=1RB, E1=1RD -/
namespace Leaf157
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨true,true,1⟩))
    (4, true) (some ⟨true,true,3⟩)
theorem check : zipCycle p 1 15 true 0 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 1 15 true 0 (by decide) check B
#print axioms cover
end Leaf157

/- OneRE: E0=1RB, E1=1RE -/
namespace Leaf158
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨true,true,1⟩))
    (4, true) (some ⟨true,true,4⟩)
theorem check : zipCycle p 1 10 true 0 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 1 10 true 0 (by decide) check B
#print axioms cover
end Leaf158

/- OneRE: E0=1RC, C1=0LB -/
namespace Leaf159
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨true,true,2⟩))
    (2, true) (some ⟨false,false,1⟩)
theorem check : zipCycle p 2 12 true 0 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 2 12 true 0 (by decide) check B
#print axioms cover
end Leaf159

/- OneRE: E0=1RC, C1=0LC -/
namespace Leaf160
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨true,true,2⟩))
    (2, true) (some ⟨false,false,2⟩)
theorem check : zipCycle p 12 1 false 0 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 12 1 false 0 (by decide) check B
#print axioms cover
end Leaf160

/- OneRE: E0=1RC, C1=0LD -/
namespace Leaf161
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨true,true,2⟩))
    (2, true) (some ⟨false,false,3⟩)
theorem check : zipCycle p 1 13 true 0 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 1 13 true 0 (by decide) check B
#print axioms cover
end Leaf161

/- OneRE: E0=1RC, C1=0RB -/
namespace Leaf162
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨true,true,2⟩))
    (2, true) (some ⟨false,true,1⟩)
theorem check : zipCycle p 2 9 true 0 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 2 9 true 0 (by decide) check B
#print axioms cover
end Leaf162

/- OneRE: E0=1RC, C1=0RD -/
namespace Leaf163
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨true,true,2⟩))
    (2, true) (some ⟨false,true,3⟩)
theorem check : zipCycle p 1 9 true 0 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 1 9 true 0 (by decide) check B
#print axioms cover
end Leaf163

/- OneRE: E0=1RC, C1=1LD -/
namespace Leaf164
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨true,true,2⟩))
    (2, true) (some ⟨true,false,3⟩)
theorem check : zipCycle p 5 4 false 2 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 5 4 false 2 (by decide) check B
#print axioms cover
end Leaf164

/- OneRE: E0=1RC, C1=1RB -/
namespace Leaf165
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨true,true,2⟩))
    (2, true) (some ⟨true,true,1⟩)
theorem check : zipCycle p 2 9 true 0 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 2 9 true 0 (by decide) check B
#print axioms cover
end Leaf165

/- OneRE: E0=1RC, C1=1RC -/
namespace Leaf166
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨true,true,2⟩))
    (2, true) (some ⟨true,true,2⟩)
theorem check : zipCycle p 2 8 true 0 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 2 8 true 0 (by decide) check B
#print axioms cover
end Leaf166

/- OneRE: E0=1RC, C1=1RD -/
namespace Leaf167
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨true,true,2⟩))
    (2, true) (some ⟨true,true,3⟩)
theorem check : zipCycle p 2 10 true 0 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 2 10 true 0 (by decide) check B
#print axioms cover
end Leaf167

/- OneRE: E0=1RE, E1=0LB -/
namespace Leaf168
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨true,true,4⟩))
    (4, true) (some ⟨false,false,1⟩)
theorem check : zipCycle p 13 1 true 3 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 13 1 true 3 (by decide) check B
#print axioms cover
end Leaf168

/- OneRE: E0=1RE, E1=0LD -/
namespace Leaf169
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨true,true,4⟩))
    (4, true) (some ⟨false,false,3⟩)
theorem check : zipCycle p 16 1 true 2 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 16 1 true 2 (by decide) check B
#print axioms cover
end Leaf169

/- OneRE: E0=1RE, E1=0LE -/
namespace Leaf170
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨true,true,4⟩))
    (4, true) (some ⟨false,false,4⟩)
theorem check : zipCycle p 20 1 true -2 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 20 1 true -2 (by decide) check B
#print axioms cover
end Leaf170

/- OneRE: E0=1RE, E1=0RB -/
namespace Leaf171
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨true,true,4⟩))
    (4, true) (some ⟨false,true,1⟩)
theorem check : zipCycle p 10 1 true 4 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 10 1 true 4 (by decide) check B
#print axioms cover
end Leaf171

/- OneRE: E0=1RE, E1=0RD -/
namespace Leaf172
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨true,true,4⟩))
    (4, true) (some ⟨false,true,3⟩)
theorem check : zipCycle p 1 9 true 0 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 1 9 true 0 (by decide) check B
#print axioms cover
end Leaf172

/- OneRE: E0=1RE, E1=0RE -/
namespace Leaf173
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨true,true,4⟩))
    (4, true) (some ⟨false,true,4⟩)
theorem check : zipCycle p 10 1 true 4 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 10 1 true 4 (by decide) check B
#print axioms cover
end Leaf173

/- OneRE: E0=1RE, E1=1LB -/
namespace Leaf174
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨true,true,4⟩))
    (4, true) (some ⟨true,false,1⟩)
theorem check : zipCycle p 8 2 false 2 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 8 2 false 2 (by decide) check B
#print axioms cover
end Leaf174

/- OneRE: E0=1RE, E1=1LD -/
namespace Leaf175
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨true,true,4⟩))
    (4, true) (some ⟨true,false,3⟩)
theorem check : zipCycle p 5 4 false 2 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 5 4 false 2 (by decide) check B
#print axioms cover
end Leaf175

/- OneRE: E0=1RE, E1=1LE -/
namespace Leaf176
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨true,true,4⟩))
    (4, true) (some ⟨true,false,4⟩)
theorem check : zipCycle p 9 3 false 1 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 9 3 false 1 (by decide) check B
#print axioms cover
end Leaf176

/- OneRE: E0=1RE, E1=1RB -/
namespace Leaf177
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨true,true,4⟩))
    (4, true) (some ⟨true,true,1⟩)
theorem check : zipCycle p 10 1 true 4 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 10 1 true 4 (by decide) check B
#print axioms cover
end Leaf177

/- OneRE: E0=1RE, E1=1RD -/
namespace Leaf178
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨true,true,4⟩))
    (4, true) (some ⟨true,true,3⟩)
theorem check : zipCycle p 11 1 true 3 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 11 1 true 3 (by decide) check B
#print axioms cover
end Leaf178

/- OneRE: E0=1RE, E1=1RE -/
namespace Leaf179
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨true,true,4⟩))
    (4, true) (some ⟨true,true,4⟩)
theorem check : zipCycle p 10 1 true 4 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 10 1 true 4 (by decide) check B
#print axioms cover
end Leaf179

/- OneRE: E0=1RF, F1=0RD -/
namespace Leaf180
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨true,true,5⟩))
    (5, true) (some ⟨false,true,3⟩)
theorem check : zipCycle p 1 9 true 0 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 1 9 true 0 (by decide) check B
#print axioms cover
end Leaf180

/- OneRE: E0=1RF, F1=1LD -/
namespace Leaf181
abbrev p : PartialMachine :=
  refine (refine base (4, false) (some ⟨true,true,5⟩))
    (5, true) (some ⟨true,false,3⟩)
theorem check : zipCycle p 5 4 false 2 = true := by decide
theorem cover (B : Nat) : Cover (WeightedBound B) p :=
  zipper_cover p 5 4 false 2 (by decide) check B
#print axioms cover
end Leaf181

end BB6.Agent32Raw42OneREThirdBatch
