import Nov26SourceCore
import BusyBeaver.BB6.NonHalt.M_1RB1LE_1RC0RB_1LD1RC_1LA1LE_1LF0LA_1LCHHH
import BusyBeaver.BB6.NonHalt.M_1RB0RD_1RC0LF_1LA0LB_HHH1RE_1LB1RA_0LC0RA

namespace BB6.Agent10Nov26
open BB6Coverage BB6.ConjectureBridge
set_option maxHeartbeats 0

/-- Raw139; pinned upstream ordinary-row leaf. -/
def n14 : Machine := literal [some ⟨true,true,1⟩, some ⟨true,false,4⟩, some ⟨true,true,2⟩, some ⟨false,true,1⟩, some ⟨true,false,3⟩, some ⟨true,true,2⟩, some ⟨true,false,0⟩, some ⟨true,false,4⟩, some ⟨true,false,5⟩, some ⟨false,false,0⟩, some ⟨true,false,2⟩, none]
theorem n14_eq : toAgent8 BusyBeaver.M_1RB1LE_1RC0RB_1LD1RC_1LA1LE_1LF0LA_1LCHHH.machine = n14 := by
  funext slot
  rcases slot with ⟨q,b⟩
  fin_cases q <;> cases b <;> rfl
theorem n14_never : NeverHalts n14 := by
  rw [← n14_eq]
  exact source_never BusyBeaver.M_1RB1LE_1RC0RB_1LD1RC_1LA1LE_1LF0LA_1LCHHH.machine BusyBeaver.M_1RB1LE_1RC0RB_1LD1RC_1LA1LE_1LF0LA_1LCHHH.is_not_halt
theorem n14_cover : Cover NeverHalts (leaf n14) :=
  Cover.leaf _ (all_completions_never _ n14_never)
#print axioms n14_eq
#print axioms n14_never
#print axioms n14_cover

/-- Raw13; pinned upstream ordinary-row leaf. -/
def n10 : Machine := literal [some ⟨true,true,1⟩, some ⟨false,true,3⟩, some ⟨true,true,2⟩, some ⟨false,false,5⟩, some ⟨true,false,0⟩, some ⟨false,false,1⟩, none, some ⟨true,true,4⟩, some ⟨true,false,1⟩, some ⟨true,true,0⟩, some ⟨false,false,2⟩, some ⟨false,true,0⟩]
theorem n10_eq : toAgent8 BusyBeaver.M_1RB0RD_1RC0LF_1LA0LB_HHH1RE_1LB1RA_0LC0RA.machine = n10 := by
  funext slot
  rcases slot with ⟨q,b⟩
  fin_cases q <;> cases b <;> rfl
theorem n10_never : NeverHalts n10 := by
  rw [← n10_eq]
  exact source_never BusyBeaver.M_1RB0RD_1RC0LF_1LA0LB_HHH1RE_1LB1RA_0LC0RA.machine BusyBeaver.M_1RB0RD_1RC0LF_1LA0LB_HHH1RE_1LB1RA_0LC0RA.is_not_halt
theorem n10_cover : Cover NeverHalts (leaf n10) :=
  Cover.leaf _ (all_completions_never _ n10_never)
#print axioms n10_eq
#print axioms n10_never
#print axioms n10_cover

end BB6.Agent10Nov26
