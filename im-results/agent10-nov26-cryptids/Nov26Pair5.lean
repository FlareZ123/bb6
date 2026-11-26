import Nov26SourceCore
import BusyBeaver.BB6.NonHalt.M_1RB0LA_1LC1RF_HHH1LD_1RE0LA_1RA0RB_1RE0RF
import BusyBeaver.BB6.NonHalt.M_1RB0LD_1LC0RD_1LA0LC_1RE0LB_1RB1RF_0LDHHH

namespace BB6.Agent10Nov26
open BB6Coverage BB6.ConjectureBridge
set_option maxHeartbeats 0

/-- Raw10; pinned upstream ordinary-row leaf. -/
def n1 : Machine := literal [some ⟨true,true,1⟩, some ⟨false,false,0⟩, some ⟨true,false,2⟩, some ⟨true,true,5⟩, none, some ⟨true,false,3⟩, some ⟨true,true,4⟩, some ⟨false,false,0⟩, some ⟨true,true,0⟩, some ⟨false,true,1⟩, some ⟨true,true,4⟩, some ⟨false,true,5⟩]
theorem n1_eq : toAgent8 BusyBeaver.M_1RB0LA_1LC1RF_HHH1LD_1RE0LA_1RA0RB_1RE0RF.machine = n1 := by
  funext slot
  rcases slot with ⟨q,b⟩
  fin_cases q <;> cases b <;> rfl
theorem n1_never : NeverHalts n1 := by
  rw [← n1_eq]
  exact source_never BusyBeaver.M_1RB0LA_1LC1RF_HHH1LD_1RE0LA_1RA0RB_1RE0RF.machine BusyBeaver.M_1RB0LA_1LC1RF_HHH1LD_1RE0LA_1RA0RB_1RE0RF.is_not_halt
theorem n1_cover : Cover NeverHalts (leaf n1) :=
  Cover.leaf _ (all_completions_never _ n1_never)
#print axioms n1_eq
#print axioms n1_never
#print axioms n1_cover

/-- Raw10; pinned upstream ordinary-row leaf. -/
def n3 : Machine := literal [some ⟨true,true,1⟩, some ⟨false,false,3⟩, some ⟨true,false,2⟩, some ⟨false,true,3⟩, some ⟨true,false,0⟩, some ⟨false,false,2⟩, some ⟨true,true,4⟩, some ⟨false,false,1⟩, some ⟨true,true,1⟩, some ⟨true,true,5⟩, some ⟨false,false,3⟩, none]
theorem n3_eq : toAgent8 BusyBeaver.M_1RB0LD_1LC0RD_1LA0LC_1RE0LB_1RB1RF_0LDHHH.machine = n3 := by
  funext slot
  rcases slot with ⟨q,b⟩
  fin_cases q <;> cases b <;> rfl
theorem n3_never : NeverHalts n3 := by
  rw [← n3_eq]
  exact source_never BusyBeaver.M_1RB0LD_1LC0RD_1LA0LC_1RE0LB_1RB1RF_0LDHHH.machine BusyBeaver.M_1RB0LD_1LC0RD_1LA0LC_1RE0LB_1RB1RF_0LDHHH.is_not_halt
theorem n3_cover : Cover NeverHalts (leaf n3) :=
  Cover.leaf _ (all_completions_never _ n3_never)
#print axioms n3_eq
#print axioms n3_never
#print axioms n3_cover

end BB6.Agent10Nov26
