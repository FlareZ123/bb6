import W4JuncMax
import W4JuncOne
import Lean.Elab.Tactic.Omega

namespace BB429W4JuncSecondMax

open BB429OddExcursion BB429SourceE1Return BB429SourceE1Delta
open BB429FinishScanEDelta BB429JuncHeadExcursion
open BB429W4HeadMax BB429W4JuncMax BB429W4JuncOne

/-- Exact full-prefix head maximum at the B/1 gate of a zero-left
    right-one Junc, rather than only at the first subsequent C/0 visit. -/
theorem junc0_w1_to_b1_max (v : Nat) :
    runWithMax (2*v+26) (junc 0 v 1) =
      some (z 1 (pairs01 (v+3) ++ ones 5) true [false,true],
        ((2*v+2 : Nat) : Int), ((2*v+2 : Nat) : Int)) := by
  have hprep := junc0_prep20_max v 1
  have hshift := shift_B01_max (v+2) (ones 5) [false,true]
  have hinput : z 1 (ones 5) false
      (true :: (pairs01 (v+2) ++ ones 1 ++ [false,true])) =
    z 1 (ones 5) false
      (true :: (pairs01 (v+2) ++ (true :: [false,true]))) := by
    simp [ones, List.append_assoc]
  have htime : 2*v+26 = 20 + 2*((v+2)+1) := by omega
  rw [htime, runWithMax_add, hprep]
  simp only [Option.bind_some]
  rw [hinput, hshift]
  simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq]
  constructor
  · trivial
  · constructor <;> simp [Int.max_def] <;> omega

/-- The exact sixteen-step B/1 excursion visits at most six cells to
    the right of its entry point, including the D/0 immediately following
    the first C/0 event. -/
theorem b1_to_scanE_16_max (v : Nat) :
    runWithMax 16 (z 1 (pairs01 (v+3) ++ ones 5) true [false,true]) =
      some (sourceScanE (v+2) sigma, -2, 6) := by
  rfl

/-- The original right-one Junc reaches S_E at offset 2v and with maximum
    head displacement 2v+8 over every primitive step in its prefix. -/
theorem junc0_w1_to_scanE_max (v : Nat) :
    runWithMax (2*v+42) (junc 0 v 1) =
      some (sourceScanE (v+2) sigma,
        ((2*v : Nat) : Int), ((2*v+8 : Nat) : Int)) := by
  have hB := junc0_w1_to_b1_max v
  have htail := b1_to_scanE_16_max v
  rw [show 2*v+42 = (2*v+26)+16 by omega, runWithMax_add, hB]
  simp only [Option.bind_some]
  rw [htail]
  simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq]
  constructor
  · trivial
  · constructor <;> simp [Int.max_def] <;> omega

/-- The full fourteen-step C/1-to-C/0 continuation is bounded above by
    its own terminal head displacement +10. -/
theorem c1_to_czero14_max (left : List Bool) :
    runWithMax 14 (z 2 left true sigma) =
      some (z 2 (([true,false,true] ++ ones 7) ++ left) false [], 10, 10) := by
  rfl

/-- For every middle parameter, the second explicit C/0 visit is a true
    record-right event: maximum head position at every earlier primitive
    step equals the C/0 endpoint position 2v+10, and its right stack
    is completely blank. -/
theorem junc0_w1_second_czero_max (v : Nat) :
    runWithMax (2*v+42+(crossTime (v+2)+15)) (junc 0 v 1) =
      some (z 2 (([true,false,true] ++ ones 7) ++ finalLeft (v+2)) false [],
        ((2*v+10 : Nat) : Int), ((2*v+10 : Nat) : Int)) := by
  have hfirst := junc0_w1_to_scanE_max v
  have hret := sourceScanE_e1_max (v+2) sigma
  have htail := c1_to_czero14_max (finalLeft (v+2))
  have htime : 2*v+42+(crossTime (v+2)+15) =
      (2*v+42)+((crossTime (v+2)+1)+14) := by omega
  rw [htime, runWithMax_add, hfirst]
  simp only [Option.bind_some]
  rw [runWithMax_add, hret]
  simp only [Option.bind_some]
  rw [htail]
  simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq]
  constructor
  · trivial
  · constructor <;> simp [Int.max_def] <;> omega

#print axioms junc0_w1_to_b1_max
#print axioms b1_to_scanE_16_max
#print axioms junc0_w1_to_scanE_max
#print axioms c1_to_czero14_max
#print axioms junc0_w1_second_czero_max

end BB429W4JuncSecondMax
