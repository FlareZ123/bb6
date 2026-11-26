import Nov26SourceCore
import BusyBeaver.BB6.NonHalt.M_1RB0RA_1RC0RD_1RD0LC_1LE1RA_HHH1LF_1RB0LC
import BusyBeaver.BB6.NonHalt.M_1RB0RF_1RC0LD_1RD0RA_1LB1LE_0LB0RE_0RDHHH

namespace BB6.Agent10Nov26
open BB6Coverage BB6.ConjectureBridge
set_option maxHeartbeats 0

/-- Raw140; pinned upstream ordinary-row leaf. -/
def n8 : Machine := literal [some ⟨true,true,1⟩, some ⟨false,true,0⟩, some ⟨true,true,2⟩, some ⟨false,true,3⟩, some ⟨true,true,3⟩, some ⟨false,false,2⟩, some ⟨true,false,4⟩, some ⟨true,true,0⟩, none, some ⟨true,false,5⟩, some ⟨true,true,1⟩, some ⟨false,false,2⟩]
theorem n8_eq : toAgent8 BusyBeaver.M_1RB0RA_1RC0RD_1RD0LC_1LE1RA_HHH1LF_1RB0LC.machine = n8 := by
  funext slot
  rcases slot with ⟨q,b⟩
  fin_cases q <;> cases b <;> rfl
theorem n8_never : NeverHalts n8 := by
  rw [← n8_eq]
  exact source_never BusyBeaver.M_1RB0RA_1RC0RD_1RD0LC_1LE1RA_HHH1LF_1RB0LC.machine BusyBeaver.M_1RB0RA_1RC0RD_1RD0LC_1LE1RA_HHH1LF_1RB0LC.is_not_halt
theorem n8_cover : Cover NeverHalts (leaf n8) :=
  Cover.leaf _ (all_completions_never _ n8_never)
#print axioms n8_eq
#print axioms n8_never
#print axioms n8_cover

/-- Raw140; pinned upstream ordinary-row leaf. -/
def n12 : Machine := literal [some ⟨true,true,1⟩, some ⟨false,true,5⟩, some ⟨true,true,2⟩, some ⟨false,false,3⟩, some ⟨true,true,3⟩, some ⟨false,true,0⟩, some ⟨true,false,1⟩, some ⟨true,false,4⟩, some ⟨false,false,1⟩, some ⟨false,true,4⟩, some ⟨false,true,3⟩, none]
theorem n12_eq : toAgent8 BusyBeaver.M_1RB0RF_1RC0LD_1RD0RA_1LB1LE_0LB0RE_0RDHHH.machine = n12 := by
  funext slot
  rcases slot with ⟨q,b⟩
  fin_cases q <;> cases b <;> rfl
theorem n12_never : NeverHalts n12 := by
  rw [← n12_eq]
  exact source_never BusyBeaver.M_1RB0RF_1RC0LD_1RD0RA_1LB1LE_0LB0RE_0RDHHH.machine BusyBeaver.M_1RB0RF_1RC0LD_1RD0RA_1LB1LE_0LB0RE_0RDHHH.is_not_halt
theorem n12_cover : Cover NeverHalts (leaf n12) :=
  Cover.leaf _ (all_completions_never _ n12_never)
#print axioms n12_eq
#print axioms n12_never
#print axioms n12_cover

end BB6.Agent10Nov26
