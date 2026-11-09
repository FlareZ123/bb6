import FrontierOdd0100Source
import CZeroHeadFrontier
import Lean.Elab.Tactic.Omega

set_option maxRecDepth 8192
set_option maxHeartbeats 30000000

namespace BB429Odd0100Max
open BB429OddExcursion BB429CZeroEvenReturn
open BB429Odd0100Source BB429CZeroHeadFrontier BB429W4HeadMax

private theorem c3_max (m : Nat) (tail : List Bool) :
  runWithMax 3 (z 2 (true :: ones (2*m) ++
    [false,true,false,false] ++ tail) false []) =
  some (z 0 (ones (2*m) ++ [false,true,false,false] ++ tail)
    true [false,true],-1,1) := by rfl

private theorem turn14_max (tail r : List Bool) :
  runWithMax 14 (z 0 ([false,true,false,false] ++ tail) true r) =
  some (z 0 ([true,true,true,true] ++ tail) false r,0,0) := by rfl

private theorem finish4_max (l : List Bool) :
  runWithMax 4 (z 0 l false [false,true]) =
  some (z 2 ([true,false,true,true] ++ l) false [],4,4) := by rfl

/-- The 4m+21-step odd-0100 section reaches a new right record exactly +3.
    No primitive intermediate head position exceeds that final record. -/
theorem odd_0100_all_head_max (m : Nat) (tail : List Bool) :
  runWithMax (4*m+21)
    (z 2 (ones (2*m) ++ [true,false,true,false,false] ++ tail) false []) =
  some (z 2 ([true,false] ++ ones (2*m+6) ++ tail) false [],3,3) := by
  have hstart : ones (2*m) ++ [true,false,true,false,false] ++ tail =
    true :: ones (2*m) ++ [false,true,false,false] ++ tail := by
    simpa [ones] using shift_one m ([false,true,false,false] ++ tail)
  have h0 := c3_max m tail
  have h1 := af_pairs_max_uniform m ([false,true,false,false] ++ tail) [false,true]
  have h2 := turn14_max tail (tens m ++ [false,true])
  have h3 := ar_pairs_max_uniform m ([true,true,true,true] ++ tail) [false,true]
  have h4 := finish4_max (ones (2*m) ++ ([true,true,true,true] ++ tail))
  rw [show 4*m+21=3+(2*m+(14+(2*m+4))) by omega,
    runWithMax_add,hstart,h0]
  simp only [Option.bind_some]
  rw [runWithMax_add]
  simp only [List.append_assoc]
  rw [h1]
  simp only [Option.bind_some]
  rw [runWithMax_add,h2]
  simp only [Option.bind_some]
  rw [runWithMax_add,h3]
  simp only [Option.bind_some]
  rw [h4]
  simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq]
  constructor
  · have hw : [true,true] ++ ones (2*m) ++ [true,true,true,true] =
        ones (2*m+6) := by
      change List.replicate 2 true ++ List.replicate (2*m) true ++
        List.replicate 4 true = List.replicate (2*m+6) true
      rw [List.append_assoc, List.replicate_append_replicate,
        List.replicate_append_replicate]
      congr 1
      omega
    have hh := congrArg (fun v : List Bool => v ++ tail) hw
    exact congrArg (fun l => z 2 l false []) (by simpa [ones,List.append_assoc] using hh)
  constructor <;> simp [Int.max_def] <;> omega

#print axioms odd_0100_all_head_max
end BB429Odd0100Max
