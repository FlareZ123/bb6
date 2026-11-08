import W4JuncOne
import Lean.Elab.Tactic.Omega

namespace BB429W4CZeroEvents

open BB429OddExcursion BB429SourceE1Return BB429SourceE1Delta
open BB429FinishScanEDelta BB429JuncHeadExcursion BB429W4JuncOne

/-- A five-step fixed B/1 right frontier extension ends at C/0 with the
    entire right tape blank, independently of the left half-tape. -/
theorem b1_to_czero5 (left : List Bool) :
  runWithDelta 5 (z 1 left true [false,true]) =
    some (z 2 (ones 5 ++ left) false [], 5) := by
  rfl

/-- Fourteen exact steps from the C/1 S_E return similarly reach C/0,
    ten cells to the right, with blank right half-tape. -/
theorem c1_to_czero14 (left : List Bool) :
  runWithDelta 14 (z 2 left true sigma) =
    some (z 2 (([true,false,true] ++ ones 7) ++ left) false [], 10) := by
  rfl

/-- First deterministic C/0 visit, three positions strictly to the right
    of the input Junc(0,v,1)'s final marked cell. -/
theorem junc0_w1_first_czero (v : Nat) :
  runWithDelta (2*v+31) (junc 0 v 1) =
    some (z 2 (ones 5 ++ (pairs01 (v+3) ++ ones 5)) false [],
      ((2*v+7 : Nat) : Int)) := by
  have hfirst := junc0_to_B_delta v 1 (by omega)
  have htail := b1_to_czero5 (pairs01 (v+3) ++ ones 5)
  have htime : 2*v+31 = (2*v+26)+5 := by omega
  rw [htime, runWithDelta_add, hfirst]
  simp only [Option.bind_some]
  have hr : ones (1-1) ++ [false,true] = [false,true] := by rfl
  rw [hr, htail]
  simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq]
  constructor
  · trivial
  · omega

/-- The second C/0 visit inside the S_E return occurs exactly fourteen
    steps after the E/1 revisited cell, for *every* E parameter. -/
theorem sourceScanE_revisit_czero14 (b : Nat) :
  runWithDelta (crossTime b+15) (sourceScanE b sigma) =
    some (z 2 (([true,false,true] ++ ones 7) ++ finalLeft b) false [], 10) := by
  have hret := sourceScanE_e1_revisit_delta b sigma
  have htail := c1_to_czero14 (finalLeft b)
  rw [show crossTime b+15 = (crossTime b+1)+14 by omega,
    runWithDelta_add, hret]
  simp only [Option.bind_some]
  rw [htail]
  simp only [Option.map_some]
  rfl

/-- Second deterministic C/0 visit for every Junc(0,v,1), six cells to
    the right of its rightmost initially marked cell. Again its entire
    right tape is blank; it cannot be the fatal C/01 event. -/
theorem junc0_w1_second_czero (v : Nat) :
  runWithDelta (2*v+42+(crossTime (v+2)+15)) (junc 0 v 1) =
    some (z 2 (([true,false,true] ++ ones 7) ++ finalLeft (v+2)) false [],
      ((2*v+10 : Nat) : Int)) := by
  have hfirst := junc0_w1_to_scanE v
  have htail := sourceScanE_revisit_czero14 (v+2)
  rw [runWithDelta_add, hfirst]
  simp only [Option.bind_some]
  rw [htail]
  simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq]
  constructor
  · trivial
  · omega

#print axioms b1_to_czero5
#print axioms c1_to_czero14
#print axioms junc0_w1_first_czero
#print axioms sourceScanE_revisit_czero14
#print axioms junc0_w1_second_czero

end BB429W4CZeroEvents
