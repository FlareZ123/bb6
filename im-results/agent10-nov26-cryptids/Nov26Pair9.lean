import Nov26SourceCore
import BusyBeaver.BB6.NonHalt.M_1RB1LF_0RC0RB_0LD1RB_1LE0LB_0LA1LC_0LBHHH
import BusyBeaver.BB6.NonHalt.M_1RB1RC_0LC1RE_1RA0LD_1LB0RD_0RFHHH_0RA0RF

namespace BB6.Agent10Nov26
open BB6Coverage BB6.ConjectureBridge
set_option maxHeartbeats 0

/-- Raw9; pinned upstream ordinary-row leaf. -/
def n15 : Machine := literal [some ⟨true,true,1⟩, some ⟨true,false,5⟩, some ⟨false,true,2⟩, some ⟨false,true,1⟩, some ⟨false,false,3⟩, some ⟨true,true,1⟩, some ⟨true,false,4⟩, some ⟨false,false,1⟩, some ⟨false,false,0⟩, some ⟨true,false,2⟩, some ⟨false,false,1⟩, none]
theorem n15_eq : toAgent8 BusyBeaver.M_1RB1LF_0RC0RB_0LD1RB_1LE0LB_0LA1LC_0LBHHH.machine = n15 := by
  funext slot
  rcases slot with ⟨q,b⟩
  fin_cases q <;> cases b <;> rfl
theorem n15_never : NeverHalts n15 := by
  rw [← n15_eq]
  exact source_never BusyBeaver.M_1RB1LF_0RC0RB_0LD1RB_1LE0LB_0LA1LC_0LBHHH.machine BusyBeaver.M_1RB1LF_0RC0RB_0LD1RB_1LE0LB_0LA1LC_0LBHHH.is_not_halt
theorem n15_cover : Cover NeverHalts (leaf n15) :=
  Cover.leaf _ (all_completions_never _ n15_never)
#print axioms n15_eq
#print axioms n15_never
#print axioms n15_cover

/-- Raw8; pinned upstream ordinary-row leaf. -/
def n17 : Machine := literal [some ⟨true,true,1⟩, some ⟨true,true,2⟩, some ⟨false,false,2⟩, some ⟨true,true,4⟩, some ⟨true,true,0⟩, some ⟨false,false,3⟩, some ⟨true,false,1⟩, some ⟨false,true,3⟩, some ⟨false,true,5⟩, none, some ⟨false,true,0⟩, some ⟨false,true,5⟩]
theorem n17_eq : toAgent8 BusyBeaver.M_1RB1RC_0LC1RE_1RA0LD_1LB0RD_0RFHHH_0RA0RF.machine = n17 := by
  funext slot
  rcases slot with ⟨q,b⟩
  fin_cases q <;> cases b <;> rfl
theorem n17_never : NeverHalts n17 := by
  rw [← n17_eq]
  exact source_never BusyBeaver.M_1RB1RC_0LC1RE_1RA0LD_1LB0RD_0RFHHH_0RA0RF.machine BusyBeaver.M_1RB1RC_0LC1RE_1RA0LD_1LB0RD_0RFHHH_0RA0RF.is_not_halt
theorem n17_cover : Cover NeverHalts (leaf n17) :=
  Cover.leaf _ (all_completions_never _ n17_never)
#print axioms n17_eq
#print axioms n17_never
#print axioms n17_cover

end BB6.Agent10Nov26
