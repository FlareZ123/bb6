import W2EvenTail72
import W2CZeroTailMax
import W4JuncSecondMax
import Lean.Elab.Tactic.Omega

set_option maxHeartbeats 30000000
set_option maxRecDepth 8192

namespace BB429W2EvenJuncMax

open BB429OddExcursion BB429SourceE1Return BB429SourceE1Delta
open BB429FinishScanEDelta BB429JuncHeadExcursion
open BB429W4HeadMax BB429W4JuncSecondMax BB429W2CZeroTailMax
open BB429W2EvenTail72

/-- Original-table six-step post-C/0 excursion for arbitrary untouched left
    tail, with sharp +1 head overshoot and net displacement -2. -/
theorem c0_to_e1_general_max (left : List Bool) :
  runWithMax 6 (z 2 (([true,false,true] ++ ones 7) ++ left) false []) =
    some (z 4 (ones 8 ++ left) true [true,false,true],-2,1) := by rfl

/-- The complete EVEN right-one zero-left Junc return, for every middle
    parameter 2k including zero, has a sharp all-primitive-prefix maximum
    4k+11. Its final position is nine cells to the left of entry.
    The unique rightmost visit lies one step after the second C/0 event. -/
theorem junc0_even_w1_full_max (k : Nat) :
    runWithMax (22*k+203) (junc 0 (2*k) 1) =
      some (junc 2 4 (4*k+9), -9, ((4*k+11 : Nat) : Int)) := by
  have hfirst := junc0_w1_second_czero_max (2*k)
  have htime : 2*(2*k)+42+(crossTime ((2*k)+2)+15) = 18*k+112 := by
    rw [show 2*k+2=2*(k+1) by omega,crossTime_even]
    omega
  rw [htime] at hfirst
  have h6 := c0_to_e1_general_max (finalLeft (2*k+2))
  have he := e1_sweep_max (4*k+13) (pairs01 2 ++ ones 5) [true,false,true]
  have hleft : ones 8 ++ finalLeft (2*k+2) =
      ones (4*k+13) ++ pairs01 2 ++ ones 5 := by
    rw [show 2*k+2=2*(k+1) by omega, finalLeft_even]
    rw [show 4*(k+1)+1=4*k+5 by omega]
    change ones 8 ++ (ones (4*k+5) ++ pairs01 2 ++ ones 5) = _
    calc
      ones 8 ++ (ones (4*k+5) ++ pairs01 2 ++ ones 5) =
        (ones 8 ++ ones (4*k+5)) ++ pairs01 2 ++ ones 5 := by
          simp [List.append_assoc]
      _ = ones (4*k+13) ++ pairs01 2 ++ ones 5 := by
        rw [← BB429FinishScanEDelta.ones_add]
        rw [show 8+(4*k+5)=4*k+13 by omega]
  have htail := even_E1_tail72_max k
  rw [show 22*k+203=(18*k+112)+(6+((4*k+13)+72)) by omega,
      runWithMax_add,hfirst]
  simp only [Option.bind_some]
  rw [runWithMax_add,h6]
  simp only [Option.bind_some]
  rw [hleft, List.append_assoc (ones (4*k+13)) (pairs01 2) (ones 5),
      runWithMax_add,he]
  simp only [Option.bind_some]
  rw [htail]
  simp only [Option.map_some,Option.some.injEq,Prod.mk.injEq]
  constructor
  · trivial
  · constructor <;> simp [Int.max_def] <;> omega

#print axioms c0_to_e1_general_max
#print axioms junc0_even_w1_full_max

end BB429W2EvenJuncMax
