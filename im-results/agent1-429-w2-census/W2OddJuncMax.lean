import W2CZeroTailMax
import W4JuncSecondMax
import Lean.Elab.Tactic.Omega

set_option maxHeartbeats 30000000
set_option maxRecDepth 8192

namespace BB429W2OddJuncMax

open BB429OddExcursion BB429SourceE1Return BB429SourceE1Delta
open BB429FinishScanEDelta BB429JuncHeadExcursion
open BB429W4HeadMax BB429W4JuncSecondMax BB429W2CZeroTailMax

/-- Entire ODD right-one Junc return with exact primitive-step maximum.
    The second C/0 gate is at 4k+12; the following C/0 instruction makes
    the sole one-cell record extension 4k+13. The rest of the return is
    confined to the established frontier, for every k. -/
theorem junc0_odd_w1_full_max (k : Nat) :
    runWithMax (22*k+126) (junc 0 (2*k+1) 1) =
      some (junc 0 0 (4*k+16), -6, ((4*k+13 : Nat) : Int)) := by
  have hfirst := junc0_w1_second_czero_max (2*k+1)
  have htime : 2*(2*k+1)+42+(crossTime ((2*k+1)+2)+15) = 18*k+88 := by
    rw [show (2*k+1)+2=2*(k+1)+1 by omega, crossTime_odd]
    omega
  rw [htime] at hfirst
  have hleft : ([true,false,true] ++ ones 7) ++ finalLeft ((2*k+1)+2) =
      true::false::ones (2*(2*k+3)+14) := by
    rw [show (2*k+1)+2=2*(k+1)+1 by omega, finalLeft_odd]
    change true::false::(true :: (ones 7 ++ ones (4*(k+1)+8))) =
      true::false::ones (2*(2*k+3)+14)
    congr 2
    change ones 1 ++ (ones 7 ++ ones (4*(k+1)+8)) =
       ones (2*(2*k+3)+14)
    rw [← ones_add 7 (4*(k+1)+8),
        ← ones_add 1 (7+(4*(k+1)+8))]
    congr 1
    omega
  rw [hleft] at hfirst
  have htail := c0_tail_max (2*k+3)
  have hparam : 2*(2*k+3)+14=4*k+20 := by omega
  have hnum : 2*(2*k+3)+32=4*k+38 := by omega
  rw [hparam] at hfirst
  rw [hparam,hnum] at htail
  rw [show 22*k+126=(18*k+88)+(4*k+38) by omega,
      runWithMax_add,hfirst]
  simp only [Option.bind_some]
  rw [htail]
  simp only [Option.map_some,Option.some.injEq,Prod.mk.injEq]
  constructor
  · congr 1
    omega
  · constructor <;> simp [Int.max_def] <;> omega

#print axioms junc0_odd_w1_full_max

end BB429W2OddJuncMax
