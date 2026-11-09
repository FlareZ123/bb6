import W2OddEvents
import BB429DeltaPhysicalBridge
import Lean.Elab.Tactic.Omega

set_option maxHeartbeats 30000000
set_option maxRecDepth 8192

namespace BB429W2OddPhysical
open BB429OddExcursion BB429SourceE1Return BB429SourceE1Delta
open BB429FinishScanEDelta BB429W2OddEvent
open BB429PhysicalBridge BB429DeltaPhysicalBridge BB6Coverage BB429PhysicalFrontier

/-- Every physical original #429 tape represented by the odd v>=3
    right-two Junc reaches its second C/0 at an explicit time and
    absolute head position. The scanned cell and whole right tail are
    physically blank, so this C/0 cannot immediately cause halting. -/
theorem odd_second_physical (k : Nat) (c : Config)
    (hrep : Represents (junc 0 (2*k+3) 2) c) :
    ∃ c', BB6Coverage.run target429 (26*k+163) c = some c' ∧
      c'.state.val=2 ∧ c'.tape c'.head=false ∧
      c'.tape (c'.head+1)=false ∧ c'.head=c.head+((4*k+17 : Nat):Int) := by
  obtain ⟨c',hr,hs,hd⟩ :=
    source_runWithDelta_rep (26*k+163) (junc 0 (2*k+3) 2) c hrep
       (z 2 (ones 5 ++ (pairs01 ((2*k+7)+3) ++ ones 5)) false [])
       ((4*k+17:Nat):Int) (odd_w2_second_gate_delta k)
  rcases hs with ⟨hstate,hcur,hl,hrr⟩
  refine ⟨c',hr,hstate,hcur,?_,hd⟩
  have hnext := hrr 0
  change c'.tape (c'.head + 1) = false at hnext
  exact hnext

/-- The third C/0 of the same unbounded odd right-two source family
    is likewise physically nonfatal and occurs three cells farther right. -/
theorem odd_third_physical (k : Nat) (c : Config)
    (hrep : Represents (junc 0 (2*k+3) 2) c) :
    ∃ c', BB6Coverage.run target429 (40*k+260) c = some c' ∧
      c'.state.val=2 ∧ c'.tape c'.head=false ∧
      c'.tape (c'.head+1)=false ∧ c'.head=c.head+((4*k+20 : Nat):Int) := by
  obtain ⟨c',hr,hs,hd⟩ :=
    source_runWithDelta_rep (40*k+260) (junc 0 (2*k+3) 2) c hrep
       (z 2 (([true,false,true] ++ ones 7) ++ finalLeft ((2*k+7)+2)) false [])
       ((4*k+20:Nat):Int) (odd_w2_third_gate_delta k)
  rcases hs with ⟨hstate,hcur,hl,hrr⟩
  refine ⟨c',hr,hstate,hcur,?_,hd⟩
  have hnext := hrr 0
  change c'.tape (c'.head + 1) = false at hnext
  exact hnext

#print axioms odd_second_physical
#print axioms odd_third_physical

end BB429W2OddPhysical
