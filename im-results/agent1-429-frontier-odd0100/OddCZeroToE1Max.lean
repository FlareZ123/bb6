import OddCZeroToE1
import CZeroHeadFrontier
import Lean.Elab.Tactic.Omega

set_option maxRecDepth 8192
set_option maxHeartbeats 30000000

namespace BB429OddCZeroToE1Max
open BB429OddExcursion BB429CZeroEvenReturn
open BB429CZeroHeadFrontier BB429W4HeadMax

private theorem odd_c3_max (m : Nat) (tail : List Bool) :
  runWithMax 3 (z 2 (true :: ones (2*m) ++ (false :: tail)) false []) =
    some (z 0 (ones (2*m) ++ (false :: tail)) true [false,true],-1,1) := by rfl

private theorem a3_to_e1_max (tail r : List Bool) :
  runWithMax 3 (z 0 (false :: tail) true r) =
    some (z 4 tail true (true :: r),-1,0) := by rfl

/-- The unbounded odd-run parser visits no head right of entry+1,
    ending 2m+2 cells to the left at E/1 with a known right word. -/
theorem odd_C0_to_E1_head_max (m : Nat) (tail : List Bool) :
  runWithMax (2*m+6)
    (z 2 (ones (2*m+1) ++ (false :: tail)) false []) =
  some (z 4 tail true (true :: tens m ++ [false,true]),
      -((2*m+2:Nat):Int),1) := by
  have hs : ones (2*m+1) ++ (false :: tail) =
      true :: ones (2*m) ++ (false :: tail) := by
    change List.replicate (2*m+1) true ++ (false :: tail) =
      true :: List.replicate (2*m) true ++ (false :: tail)
    rw [List.replicate_succ]
  have h0 := odd_c3_max m tail
  have h1 := af_pairs_max_uniform m (false :: tail) [false,true]
  have h2 := a3_to_e1_max tail (tens m ++ [false,true])
  rw [show 2*m+6=3+(2*m+3) by omega,runWithMax_add,hs,h0]
  simp only [Option.bind_some]
  rw [runWithMax_add,h1]
  simp only [Option.bind_some]
  rw [h2]
  simp only [Option.map_some,Option.some.injEq,Prod.mk.injEq]
  constructor
  · rfl
  constructor <;> simp [Int.max_def] <;> omega

#print axioms odd_C0_to_E1_head_max
end BB429OddCZeroToE1Max
