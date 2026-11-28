import FiniteHalting
import WeightedFirstOneCover

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-!
Twelve Raw34 D1=1RD descendant cylinders with an assigned HALT
encountered on the genuine blank execution before any unassigned move.
The per-leaf table includes explicit some none halt assignments.
This file is an original-source Lean proof candidate and is NOT claimed
kernel-accepted until its exact dependency closure is compiled.
-/

namespace BB6.Agent23Raw34D1RDHalters
open BB6Coverage BB6.Agent13BlankDelay

def fromList (xs : List (Option Transition)) : PartialMachine := fun s =>
  (xs[2*s.1.val+s.2.toNat]?).getD none

/-! Leaf 0: upstream open index 0, assigned HALT at C1.
    Its unassigned slots are not queried before the halt. -/
def p0 : PartialMachine := fromList [
  some (some ⟨true,true,1⟩),
  none,
  some (some ⟨true,true,2⟩),
  none,
  some (some ⟨false,true,3⟩),
  some none,
  some (some ⟨true,false,2⟩),
  some (some ⟨true,true,3⟩),
  none,
  none,
  none,
  none]

theorem p0_check : finiteHaltCheck p0 7 = true := by
  decide +kernel

theorem p0_weighted :
    Cover (WeightedBound 18) p0 := by
  apply Cover.leaf
  intro m hm
  exact weighted_of_margin 18 m
    ((finiteHaltCheck_sound p0 7 13 (by decide) p0_check).sound m hm)
    (by decide)

#print axioms p0_weighted

/-! Leaf 1: upstream open index 1, assigned HALT at A1.
    Its unassigned slots are not queried before the halt. -/
def p1 : PartialMachine := fromList [
  some (some ⟨true,true,1⟩),
  some none,
  some (some ⟨true,true,2⟩),
  none,
  some (some ⟨false,true,3⟩),
  some (some ⟨false,false,0⟩),
  some (some ⟨true,false,2⟩),
  some (some ⟨true,true,3⟩),
  none,
  none,
  none,
  none]

theorem p1_check : finiteHaltCheck p1 11 = true := by
  decide +kernel

theorem p1_weighted :
    Cover (WeightedBound 18) p1 := by
  apply Cover.leaf
  intro m hm
  exact weighted_of_margin 18 m
    ((finiteHaltCheck_sound p1 11 13 (by decide) p1_check).sound m hm)
    (by decide)

#print axioms p1_weighted

/-! Leaf 2: upstream open index 13, assigned HALT at E0.
    Its unassigned slots are not queried before the halt. -/
def p2 : PartialMachine := fromList [
  some (some ⟨true,true,1⟩),
  none,
  some (some ⟨true,true,2⟩),
  none,
  some (some ⟨false,true,3⟩),
  some (some ⟨false,false,4⟩),
  some (some ⟨true,false,2⟩),
  some (some ⟨true,true,3⟩),
  some none,
  none,
  none,
  none]

theorem p2_check : finiteHaltCheck p2 8 = true := by
  decide +kernel

theorem p2_weighted :
    Cover (WeightedBound 18) p2 := by
  apply Cover.leaf
  intro m hm
  exact weighted_of_margin 18 m
    ((finiteHaltCheck_sound p2 8 13 (by decide) p2_check).sound m hm)
    (by decide)

#print axioms p2_weighted

/-! Leaf 3: upstream open index 37, assigned HALT at A1.
    Its unassigned slots are not queried before the halt. -/
def p3 : PartialMachine := fromList [
  some (some ⟨true,true,1⟩),
  some none,
  some (some ⟨true,true,2⟩),
  none,
  some (some ⟨false,true,3⟩),
  some (some ⟨false,true,0⟩),
  some (some ⟨true,false,2⟩),
  some (some ⟨true,true,3⟩),
  none,
  none,
  none,
  none]

theorem p3_check : finiteHaltCheck p3 8 = true := by
  decide +kernel

theorem p3_weighted :
    Cover (WeightedBound 18) p3 := by
  apply Cover.leaf
  intro m hm
  exact weighted_of_margin 18 m
    ((finiteHaltCheck_sound p3 8 13 (by decide) p3_check).sound m hm)
    (by decide)

#print axioms p3_weighted

/-! Leaf 4: upstream open index 47, assigned HALT at B1.
    Its unassigned slots are not queried before the halt. -/
def p4 : PartialMachine := fromList [
  some (some ⟨true,true,1⟩),
  none,
  some (some ⟨true,true,2⟩),
  some none,
  some (some ⟨false,true,3⟩),
  some (some ⟨false,true,1⟩),
  some (some ⟨true,false,2⟩),
  some (some ⟨true,true,3⟩),
  none,
  none,
  none,
  none]

theorem p4_check : finiteHaltCheck p4 8 = true := by
  decide +kernel

theorem p4_weighted :
    Cover (WeightedBound 18) p4 := by
  apply Cover.leaf
  intro m hm
  exact weighted_of_margin 18 m
    ((finiteHaltCheck_sound p4 8 13 (by decide) p4_check).sound m hm)
    (by decide)

#print axioms p4_weighted

/-! Leaf 5: upstream open index 57, assigned HALT at E1.
    Its unassigned slots are not queried before the halt. -/
def p5 : PartialMachine := fromList [
  some (some ⟨true,true,1⟩),
  none,
  some (some ⟨true,true,2⟩),
  none,
  some (some ⟨false,true,3⟩),
  some (some ⟨false,true,4⟩),
  some (some ⟨true,false,2⟩),
  some (some ⟨true,true,3⟩),
  none,
  some none,
  none,
  none]

theorem p5_check : finiteHaltCheck p5 8 = true := by
  decide +kernel

theorem p5_weighted :
    Cover (WeightedBound 18) p5 := by
  apply Cover.leaf
  intro m hm
  exact weighted_of_margin 18 m
    ((finiteHaltCheck_sound p5 8 13 (by decide) p5_check).sound m hm)
    (by decide)

#print axioms p5_weighted

/-! Leaf 6: upstream open index 69, assigned HALT at B1.
    Its unassigned slots are not queried before the halt. -/
def p6 : PartialMachine := fromList [
  some (some ⟨true,true,1⟩),
  none,
  some (some ⟨true,true,2⟩),
  some none,
  some (some ⟨false,true,3⟩),
  some (some ⟨true,false,0⟩),
  some (some ⟨true,false,2⟩),
  some (some ⟨true,true,3⟩),
  none,
  none,
  none,
  none]

theorem p6_check : finiteHaltCheck p6 9 = true := by
  decide +kernel

theorem p6_weighted :
    Cover (WeightedBound 18) p6 := by
  apply Cover.leaf
  intro m hm
  exact weighted_of_margin 18 m
    ((finiteHaltCheck_sound p6 9 13 (by decide) p6_check).sound m hm)
    (by decide)

#print axioms p6_weighted

/-! Leaf 7: upstream open index 89, assigned HALT at B1.
    Its unassigned slots are not queried before the halt. -/
def p7 : PartialMachine := fromList [
  some (some ⟨true,true,1⟩),
  none,
  some (some ⟨true,true,2⟩),
  some none,
  some (some ⟨false,true,3⟩),
  some (some ⟨true,false,1⟩),
  some (some ⟨true,false,2⟩),
  some (some ⟨true,true,3⟩),
  none,
  none,
  none,
  none]

theorem p7_check : finiteHaltCheck p7 10 = true := by
  decide +kernel

theorem p7_weighted :
    Cover (WeightedBound 18) p7 := by
  apply Cover.leaf
  intro m hm
  exact weighted_of_margin 18 m
    ((finiteHaltCheck_sound p7 10 13 (by decide) p7_check).sound m hm)
    (by decide)

#print axioms p7_weighted

/-! Leaf 8: upstream open index 102, assigned HALT at E0.
    Its unassigned slots are not queried before the halt. -/
def p8 : PartialMachine := fromList [
  some (some ⟨true,true,1⟩),
  none,
  some (some ⟨true,true,2⟩),
  none,
  some (some ⟨false,true,3⟩),
  some (some ⟨true,false,4⟩),
  some (some ⟨true,false,2⟩),
  some (some ⟨true,true,3⟩),
  some none,
  none,
  none,
  none]

theorem p8_check : finiteHaltCheck p8 8 = true := by
  decide +kernel

theorem p8_weighted :
    Cover (WeightedBound 18) p8 := by
  apply Cover.leaf
  intro m hm
  exact weighted_of_margin 18 m
    ((finiteHaltCheck_sound p8 8 13 (by decide) p8_check).sound m hm)
    (by decide)

#print axioms p8_weighted

/-! Leaf 9: upstream open index 127, assigned HALT at A1.
    Its unassigned slots are not queried before the halt. -/
def p9 : PartialMachine := fromList [
  some (some ⟨true,true,1⟩),
  some none,
  some (some ⟨true,true,2⟩),
  none,
  some (some ⟨false,true,3⟩),
  some (some ⟨true,true,0⟩),
  some (some ⟨true,false,2⟩),
  some (some ⟨true,true,3⟩),
  none,
  none,
  none,
  none]

theorem p9_check : finiteHaltCheck p9 8 = true := by
  decide +kernel

theorem p9_weighted :
    Cover (WeightedBound 18) p9 := by
  apply Cover.leaf
  intro m hm
  exact weighted_of_margin 18 m
    ((finiteHaltCheck_sound p9 8 13 (by decide) p9_check).sound m hm)
    (by decide)

#print axioms p9_weighted

/-! Leaf 10: upstream open index 139, assigned HALT at B1.
    Its unassigned slots are not queried before the halt. -/
def p10 : PartialMachine := fromList [
  some (some ⟨true,true,1⟩),
  none,
  some (some ⟨true,true,2⟩),
  some none,
  some (some ⟨false,true,3⟩),
  some (some ⟨true,true,1⟩),
  some (some ⟨true,false,2⟩),
  some (some ⟨true,true,3⟩),
  none,
  none,
  none,
  none]

theorem p10_check : finiteHaltCheck p10 8 = true := by
  decide +kernel

theorem p10_weighted :
    Cover (WeightedBound 18) p10 := by
  apply Cover.leaf
  intro m hm
  exact weighted_of_margin 18 m
    ((finiteHaltCheck_sound p10 8 13 (by decide) p10_check).sound m hm)
    (by decide)

#print axioms p10_weighted

/-! Leaf 11: upstream open index 150, assigned HALT at E1.
    Its unassigned slots are not queried before the halt. -/
def p11 : PartialMachine := fromList [
  some (some ⟨true,true,1⟩),
  none,
  some (some ⟨true,true,2⟩),
  none,
  some (some ⟨false,true,3⟩),
  some (some ⟨true,true,4⟩),
  some (some ⟨true,false,2⟩),
  some (some ⟨true,true,3⟩),
  none,
  some none,
  none,
  none]

theorem p11_check : finiteHaltCheck p11 8 = true := by
  decide +kernel

theorem p11_weighted :
    Cover (WeightedBound 18) p11 := by
  apply Cover.leaf
  intro m hm
  exact weighted_of_margin 18 m
    ((finiteHaltCheck_sound p11 8 13 (by decide) p11_check).sound m hm)
    (by decide)

#print axioms p11_weighted

end BB6.Agent23Raw34D1RDHalters
