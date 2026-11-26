import Nov26SourceCore
import BusyBeaver.BB6.NonHalt.M_1RB0LE_1RC0LB_1RD0RC_1LA1RC_HHH1LF_1LB1LD
import BusyBeaver.BB6.NonHalt.M_1RB0LE_1RCHHH_1RD1RE_1LA0RF_0RC0LA_0LC0RB

namespace BB6.Agent10Nov26
open BB6Coverage BB6.ConjectureBridge
set_option maxHeartbeats 0

/-- Raw140; pinned upstream ordinary-row leaf. -/
def n4 : Machine := literal [some ⟨true,true,1⟩, some ⟨false,false,4⟩, some ⟨true,true,2⟩, some ⟨false,false,1⟩, some ⟨true,true,3⟩, some ⟨false,true,2⟩, some ⟨true,false,0⟩, some ⟨true,true,2⟩, none, some ⟨true,false,5⟩, some ⟨true,false,1⟩, some ⟨true,false,3⟩]
theorem n4_eq : toAgent8 BusyBeaver.M_1RB0LE_1RC0LB_1RD0RC_1LA1RC_HHH1LF_1LB1LD.machine = n4 := by
  funext slot
  rcases slot with ⟨q,b⟩
  fin_cases q <;> cases b <;> rfl
theorem n4_never : NeverHalts n4 := by
  rw [← n4_eq]
  exact source_never BusyBeaver.M_1RB0LE_1RC0LB_1RD0RC_1LA1RC_HHH1LF_1LB1LD.machine BusyBeaver.M_1RB0LE_1RC0LB_1RD0RC_1LA1RC_HHH1LF_1LB1LD.is_not_halt
theorem n4_cover : Cover NeverHalts (leaf n4) :=
  Cover.leaf _ (all_completions_never _ n4_never)
#print axioms n4_eq
#print axioms n4_never
#print axioms n4_cover

/-- Raw140; pinned upstream ordinary-row leaf. -/
def n5 : Machine := literal [some ⟨true,true,1⟩, some ⟨false,false,4⟩, some ⟨true,true,2⟩, none, some ⟨true,true,3⟩, some ⟨true,true,4⟩, some ⟨true,false,0⟩, some ⟨false,true,5⟩, some ⟨false,true,2⟩, some ⟨false,false,0⟩, some ⟨false,false,2⟩, some ⟨false,true,1⟩]
theorem n5_eq : toAgent8 BusyBeaver.M_1RB0LE_1RCHHH_1RD1RE_1LA0RF_0RC0LA_0LC0RB.machine = n5 := by
  funext slot
  rcases slot with ⟨q,b⟩
  fin_cases q <;> cases b <;> rfl
theorem n5_never : NeverHalts n5 := by
  rw [← n5_eq]
  exact source_never BusyBeaver.M_1RB0LE_1RCHHH_1RD1RE_1LA0RF_0RC0LA_0LC0RB.machine BusyBeaver.M_1RB0LE_1RCHHH_1RD1RE_1LA0RF_0RC0LA_0LC0RB.is_not_halt
theorem n5_cover : Cover NeverHalts (leaf n5) :=
  Cover.leaf _ (all_completions_never _ n5_never)
#print axioms n5_eq
#print axioms n5_never
#print axioms n5_cover

end BB6.Agent10Nov26
