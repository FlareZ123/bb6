import Nov26SourceCore
import BusyBeaver.BB6.NonHalt.M_1RB0LF_1LC0LA_1RA0RD_HHH1RE_1LA1RC_0LB0RC
import BusyBeaver.BB6.NonHalt.M_1RB0LF_1LC0LD_1RD1LB_HHH1RE_0RA1RE_1LA0LE

namespace BB6.Agent10Nov26
open BB6Coverage BB6.ConjectureBridge
set_option maxHeartbeats 0

/-- Raw10; pinned upstream ordinary-row leaf. -/
def n6 : Machine := literal [some ⟨true,true,1⟩, some ⟨false,false,5⟩, some ⟨true,false,2⟩, some ⟨false,false,0⟩, some ⟨true,true,0⟩, some ⟨false,true,3⟩, none, some ⟨true,true,4⟩, some ⟨true,false,0⟩, some ⟨true,true,2⟩, some ⟨false,false,1⟩, some ⟨false,true,2⟩]
theorem n6_eq : toAgent8 BusyBeaver.M_1RB0LF_1LC0LA_1RA0RD_HHH1RE_1LA1RC_0LB0RC.machine = n6 := by
  funext slot
  rcases slot with ⟨q,b⟩
  fin_cases q <;> cases b <;> rfl
theorem n6_never : NeverHalts n6 := by
  rw [← n6_eq]
  exact source_never BusyBeaver.M_1RB0LF_1LC0LA_1RA0RD_HHH1RE_1LA1RC_0LB0RC.machine BusyBeaver.M_1RB0LF_1LC0LA_1RA0RD_HHH1RE_1LA1RC_0LB0RC.is_not_halt
theorem n6_cover : Cover NeverHalts (leaf n6) :=
  Cover.leaf _ (all_completions_never _ n6_never)
#print axioms n6_eq
#print axioms n6_never
#print axioms n6_cover

/-- Raw10; pinned upstream ordinary-row leaf. -/
def n7 : Machine := literal [some ⟨true,true,1⟩, some ⟨false,false,5⟩, some ⟨true,false,2⟩, some ⟨false,false,3⟩, some ⟨true,true,3⟩, some ⟨true,false,1⟩, none, some ⟨true,true,4⟩, some ⟨false,true,0⟩, some ⟨true,true,4⟩, some ⟨true,false,0⟩, some ⟨false,false,4⟩]
theorem n7_eq : toAgent8 BusyBeaver.M_1RB0LF_1LC0LD_1RD1LB_HHH1RE_0RA1RE_1LA0LE.machine = n7 := by
  funext slot
  rcases slot with ⟨q,b⟩
  fin_cases q <;> cases b <;> rfl
theorem n7_never : NeverHalts n7 := by
  rw [← n7_eq]
  exact source_never BusyBeaver.M_1RB0LF_1LC0LD_1RD1LB_HHH1RE_0RA1RE_1LA0LE.machine BusyBeaver.M_1RB0LF_1LC0LD_1RD1LB_HHH1RE_0RA1RE_1LA0LE.is_not_halt
theorem n7_cover : Cover NeverHalts (leaf n7) :=
  Cover.leaf _ (all_completions_never _ n7_never)
#print axioms n7_eq
#print axioms n7_never
#print axioms n7_cover

end BB6.Agent10Nov26
