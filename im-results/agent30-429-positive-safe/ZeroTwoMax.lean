import ZeroTwoGate
import W4JuncMax
import W4HeadPrefix
import Lean.Elab.Tactic.Omega

set_option maxRecDepth 8192
set_option maxHeartbeats 30000000

namespace BB429ZeroTwoMax

open BB429OddExcursion BB429SourceE1Return BB429SourceE1Delta
open BB429FinishScanEDelta BB429JuncHeadExcursion
open BB429W4HeadMax BB429W4HeadPrefix BB429W4JuncMax

/-- The complete nine-instruction suffix from the w=2 B/1 boundary
    reaches the first harmless C/0, with exact maximal head displacement
    +5 attained at that endpoint. Every earlier intermediate instruction
    has a head coordinate no greater than the final C/0. -/
theorem b1_w2_to_czero9_max (tail : List Bool) :
    runWithMax 9 (z 1 (false :: true :: tail) true [true,false,true]) =
      some (z 2 (([true,false] ++ ones 5) ++ tail) false [], 5, 5) := by
  rfl

/-- All ordinary instructions of the long initial B/0, C/1 sweep have
    exact maximum displacement 2v+2, uniformly in the middle parameter. -/
theorem junc0_w2_to_B1_max (v : Nat) :
    runWithMax (2*v+26) (junc 0 v 2) =
      some (z 1 (pairs01 (v+3) ++ ones 5) true [true,false,true],
        ((2*v+2 : Nat) : Int), ((2*v+2 : Nat) : Int)) := by
  have hprep := junc0_prep20_max v 2
  have hshift := shift_B01_max (v+2) (ones 5) [true,false,true]
  have hinput : z 1 (ones 5) false
      (true :: (pairs01 (v+2) ++ ones 2 ++ [false,true])) =
    z 1 (ones 5) false
      (true :: (pairs01 (v+2) ++ (true :: [true,false,true]))) := by
    simp [ones, List.append_assoc]
  have htime : 2*v+26 = 20 + 2*((v+2)+1) := by omega
  rw [htime, runWithMax_add, hprep]
  simp only [Option.bind_some]
  rw [hinput, hshift]
  simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq]
  constructor
  · trivial
  · constructor <;> simp [Int.max_def] <;> omega

/-- Every primitive prefix before the very first C/0 in a zero-u w=2
    Junc is bounded above by that first C/0 head coordinate.
    In particular, the first gate is at an exact *local head record*. -/
theorem junc0_w2_first_czero_max (v : Nat) :
    runWithMax (2*v+35) (junc 0 v 2) =
      some (z 2 (([true,false] ++ ones 5) ++
          (pairs01 (v+2) ++ ones 5)) false [],
        ((2*v+7 : Nat) : Int), ((2*v+7 : Nat) : Int)) := by
  have hfirst := junc0_w2_to_B1_max v
  have htail := b1_w2_to_czero9_max (pairs01 (v+2) ++ ones 5)
  have hleft : pairs01 (v+3) ++ ones 5 =
      false :: true :: (pairs01 (v+2) ++ ones 5) := by rfl
  have htime : 2*v+35 = (2*v+26)+9 := by omega
  rw [htime, runWithMax_add, hfirst]
  simp only [Option.bind_some]
  rw [hleft, htail]
  simp only [Option.map_some,Option.some.injEq,Prod.mk.injEq]
  constructor
  · trivial
  · constructor <;> simp [Int.max_def] <;> omega

/-- Formal all-primitive-prefix relative head record, using the generic
    maximum monitor's proved prefix semantics. -/
theorem junc0_w2_all_prefixes_le_first_gate (v t : Nat)
    (ht : t ≤ 2*v+35) (p : Zipper × Int × Int)
    (hp : runWithMax t (junc 0 v 2) = some p) :
    p.2.1 ≤ ((2*v+7 : Nat) : Int) := by
  have hsum : t+(2*v+35-t) = 2*v+35 := by omega
  have hfull := junc0_w2_first_czero_max v
  rw [← hsum] at hfull
  have hbound :=
    runWithMax_prefix_le t (2*v+35-t) (junc 0 v 2) p hp
      (z 2 (([true,false] ++ ones 5) ++ (pairs01 (v+2) ++ ones 5))
        false [], ((2*v+7 : Nat) : Int), ((2*v+7 : Nat) : Int))
      hfull
  exact hbound

#print axioms b1_w2_to_czero9_max
#print axioms junc0_w2_to_B1_max
#print axioms junc0_w2_first_czero_max
#print axioms junc0_w2_all_prefixes_le_first_gate

end BB429ZeroTwoMax
