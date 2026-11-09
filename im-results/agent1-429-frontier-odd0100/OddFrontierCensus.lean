import FrontierOdd0100Source
import OddCZeroToE1
import CZeroCensus
import Lean.Elab.Tactic.Omega

set_option maxRecDepth 8192
set_option maxHeartbeats 30000000

namespace BB429OddFrontierCensus
open BB429OddExcursion BB429CZeroEvenReturn
open BB429Odd0100Source BB429CZeroCensus

private theorem c3_count (m : Nat) (tail : List Bool) :
  runCount 3 (z 2 (true :: ones (2*m) ++
    [false,true,false,false] ++ tail) false []) =
  some (z 0 (ones (2*m) ++ [false,true,false,false] ++ tail)
    true [false,true],1) := by rfl

private theorem turn14_count (tail r : List Bool) :
  runCount 14 (z 0 ([false,true,false,false] ++ tail) true r) =
  some (z 0 ([true,true,true,true] ++ tail) false r,0) := by rfl

private theorem finish4_count (l : List Bool) :
  runCount 4 (z 0 l false [false,true]) =
  some (z 2 ([true,false,true,true] ++ l) false [],0) := by rfl

/-- The odd-0100 return is the NEXT C/0 instruction start, with
    no C/0 at any intermediate primitive instruction start. -/
theorem odd_0100_exact_one_czero (m : Nat) (tail : List Bool) :
  runCount (4*m+21)
    (z 2 (ones (2*m) ++ [true,false,true,false,false] ++ tail) false []) =
  some (z 2 ([true,false] ++ ones (2*m+6) ++ tail) false [],1) := by
  have hstart : ones (2*m) ++ [true,false,true,false,false] ++ tail =
    true :: ones (2*m) ++ [false,true,false,false] ++ tail := by
    simpa [ones] using shift_one m ([false,true,false,false] ++ tail)
  have h0 := c3_count m tail
  have h1 := af_pairs_no_czero m ([false,true,false,false] ++ tail) [false,true]
  have h2 := turn14_count tail (tens m ++ [false,true])
  have h3 := ar_pairs_no_czero m ([true,true,true,true] ++ tail) [false,true]
  have h4 := finish4_count (ones (2*m) ++ ([true,true,true,true] ++ tail))
  rw [show 4*m+21=3+(2*m+(14+(2*m+4))) by omega,
    runCount_add,hstart,h0]
  simp only [Option.bind_some]
  rw [runCount_add]
  simp only [List.append_assoc]
  rw [h1]
  simp only [Option.bind_some]
  rw [runCount_add,h2]
  simp only [Option.bind_some]
  rw [runCount_add,h3]
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
  · rfl

private theorem a3_to_e1_count (tail r : List Bool) :
  runCount 3 (z 0 (false :: tail) true r) =
  some (z 4 tail true (true :: r),0) := by rfl

/-- Every C/0 with an odd left run and a following zero has no
    further C/0 before the exact E/1 section. -/
theorem odd_to_E1_exact_one_czero (m : Nat) (tail : List Bool) :
  runCount (2*m+6)
    (z 2 (ones (2*m+1) ++ (false :: tail)) false []) =
  some (z 4 tail true (true :: tens m ++ [false,true]),1) := by
  have hs : ones (2*m+1) ++ (false :: tail) =
      true :: ones (2*m) ++ (false :: tail) := by
    change List.replicate (2*m+1) true ++ (false :: tail) =
      true :: List.replicate (2*m) true ++ (false :: tail)
    rw [List.replicate_succ]
  rw [show 2*m+6=3+(2*m+3) by omega,runCount_add,hs]
  have h0 : runCount 3 (z 2 (true :: ones (2*m) ++ (false :: tail)) false []) =
    some (z 0 (ones (2*m) ++ (false :: tail)) true [false,true],1) := by rfl
  rw [h0]
  simp only [Option.bind_some]
  rw [runCount_add,af_pairs_no_czero]
  simp only [Option.bind_some]
  rw [a3_to_e1_count]
  rfl

#print axioms odd_0100_exact_one_czero
#print axioms odd_to_E1_exact_one_czero
end BB429OddFrontierCensus
