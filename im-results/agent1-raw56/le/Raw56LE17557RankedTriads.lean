import Raw56LE17557FrameMachine
import Raw56LE17557LocalSweeps

namespace BB6.Agent1Raw56.LE17557RankedTriads
open BB6Coverage
open BB6Coverage.Agent31Pump
open BB6.Agent1Raw56.LE17557Base
open BB6.Agent1Raw56.LE17557FrameSchedule
open BB6.Agent1Raw56.LE17557FrameMachine
open BB6.Agent1Raw56.LE17557LocalSweeps

/-- The physical second-right-run parameter of a rank-r normal source triad is
    exactly six cells longer than the abstract frame runway it creates. -/
theorem normalB_eq_frameCost_add6 (r : Nat) :
    normalB r = lowCost (frame r) + 6 := by
  have h := normal_push_eq_frame_cost r
  have hg := normalB_ge6 r
  omega

/-- Source/abstract bridge for a rank-r normal action.  The original six-state
    machine executes the exact normal A triad with second right run normalB r,
    and the newly-created finite left zero runway has precisely
    lowCost(frame r) cells beyond the scanned head.  Thus the concrete rewrite
    pushes exactly the frame size used by the well-founded abstract executor. -/
theorem A_ranked_normal
    (r a c z : Nat) (L R : List Bool) :
    run0 p (a + lowCost (frame r) + 2*c + 35)
      ⟨0, false :: L,
        rep [true] (a+1) ++ [false] ++
        rep [true] (normalB r) ++ [false] ++
        rep [true] (c+1) ++ rep [false] (z+2) ++ R⟩ =
      some
      ⟨0,
        rep [false] (lowCost (frame r)+1) ++ rep [true] (a+3) ++ L,
        [true,true,false] ++ rep [true] (c+6) ++
          rep [false] z ++ R⟩ := by
  have hb := normalB_eq_frameCost_add6 r
  have h := A_triad_normal a (lowCost (frame r)) c z L R
  simpa [hb] using h

/-- The concrete normal source action therefore inherits the exact rank
    residue guard required by the frame schedule. -/
theorem A_ranked_normal_secondRun_mod8 (r : Nat) :
    normalB r % 8 = 5 := normalB_mod8 r

#print axioms normalB_eq_frameCost_add6
#print axioms A_ranked_normal
#print axioms A_ranked_normal_secondRun_mod8
end BB6.Agent1Raw56.LE17557RankedTriads
