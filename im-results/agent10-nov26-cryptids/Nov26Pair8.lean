import Nov26SourceCore
import BusyBeaver.BB6.NonHalt.M_1RB0LD_0RC1RD_1LA1RA_1LE0LE_1RF0LA_0RAHHH
import BusyBeaver.BB6.NonHalt.M_1RB1LC_0RC0RB_1LD0LA_1LEHHH_1LF1RA_1LA1LC

namespace BB6.Agent10Nov26
open BB6Coverage BB6.ConjectureBridge
set_option maxHeartbeats 0

/-- Raw9; pinned upstream ordinary-row leaf. -/
def n2 : Machine := literal [some ⟨true,true,1⟩, some ⟨false,false,3⟩, some ⟨false,true,2⟩, some ⟨true,true,3⟩, some ⟨true,false,0⟩, some ⟨true,true,0⟩, some ⟨true,false,4⟩, some ⟨false,false,4⟩, some ⟨true,true,5⟩, some ⟨false,false,0⟩, some ⟨false,true,0⟩, none]
theorem n2_eq : toAgent8 BusyBeaver.M_1RB0LD_0RC1RD_1LA1RA_1LE0LE_1RF0LA_0RAHHH.machine = n2 := by
  funext slot
  rcases slot with ⟨q,b⟩
  fin_cases q <;> cases b <;> rfl
theorem n2_never : NeverHalts n2 := by
  rw [← n2_eq]
  exact source_never BusyBeaver.M_1RB0LD_0RC1RD_1LA1RA_1LE0LE_1RF0LA_0RAHHH.machine BusyBeaver.M_1RB0LD_0RC1RD_1LA1RA_1LE0LE_1RF0LA_0RAHHH.is_not_halt
theorem n2_cover : Cover NeverHalts (leaf n2) :=
  Cover.leaf _ (all_completions_never _ n2_never)
#print axioms n2_eq
#print axioms n2_never
#print axioms n2_cover

/-- Raw9; pinned upstream ordinary-row leaf. -/
def n13 : Machine := literal [some ⟨true,true,1⟩, some ⟨true,false,2⟩, some ⟨false,true,2⟩, some ⟨false,true,1⟩, some ⟨true,false,3⟩, some ⟨false,false,0⟩, some ⟨true,false,4⟩, none, some ⟨true,false,5⟩, some ⟨true,true,0⟩, some ⟨true,false,0⟩, some ⟨true,false,2⟩]
theorem n13_eq : toAgent8 BusyBeaver.M_1RB1LC_0RC0RB_1LD0LA_1LEHHH_1LF1RA_1LA1LC.machine = n13 := by
  funext slot
  rcases slot with ⟨q,b⟩
  fin_cases q <;> cases b <;> rfl
theorem n13_never : NeverHalts n13 := by
  rw [← n13_eq]
  exact source_never BusyBeaver.M_1RB1LC_0RC0RB_1LD0LA_1LEHHH_1LF1RA_1LA1LC.machine BusyBeaver.M_1RB1LC_0RC0RB_1LD0LA_1LEHHH_1LF1RA_1LA1LC.is_not_halt
theorem n13_cover : Cover NeverHalts (leaf n13) :=
  Cover.leaf _ (all_completions_never _ n13_never)
#print axioms n13_eq
#print axioms n13_never
#print axioms n13_cover

end BB6.Agent10Nov26
