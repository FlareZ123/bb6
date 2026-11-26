import Nov26SourceCore
import BusyBeaver.BB6.NonHalt.M_1RB0RE_1LC0RA_1RF0RD_HHH1LE_0LB1LE_1LE1RC
import BusyBeaver.BB6.NonHalt.M_1RB1RE_1LC0RA_1LA0LD_1LB0LF_0RB0LE_0LAHHH

namespace BB6.Agent10Nov26
open BB6Coverage BB6.ConjectureBridge
set_option maxHeartbeats 0

/-- Raw10; pinned upstream ordinary-row leaf. -/
def n11 : Machine := literal [some ⟨true,true,1⟩, some ⟨false,true,4⟩, some ⟨true,false,2⟩, some ⟨false,true,0⟩, some ⟨true,true,5⟩, some ⟨false,true,3⟩, none, some ⟨true,false,4⟩, some ⟨false,false,1⟩, some ⟨true,false,4⟩, some ⟨true,false,4⟩, some ⟨true,true,2⟩]
theorem n11_eq : toAgent8 BusyBeaver.M_1RB0RE_1LC0RA_1RF0RD_HHH1LE_0LB1LE_1LE1RC.machine = n11 := by
  funext slot
  rcases slot with ⟨q,b⟩
  fin_cases q <;> cases b <;> rfl
theorem n11_never : NeverHalts n11 := by
  rw [← n11_eq]
  exact source_never BusyBeaver.M_1RB0RE_1LC0RA_1RF0RD_HHH1LE_0LB1LE_1LE1RC.machine BusyBeaver.M_1RB0RE_1LC0RA_1RF0RD_HHH1LE_0LB1LE_1LE1RC.is_not_halt
theorem n11_cover : Cover NeverHalts (leaf n11) :=
  Cover.leaf _ (all_completions_never _ n11_never)
#print axioms n11_eq
#print axioms n11_never
#print axioms n11_cover

/-- Raw10; pinned upstream ordinary-row leaf. -/
def n18 : Machine := literal [some ⟨true,true,1⟩, some ⟨true,true,4⟩, some ⟨true,false,2⟩, some ⟨false,true,0⟩, some ⟨true,false,0⟩, some ⟨false,false,3⟩, some ⟨true,false,1⟩, some ⟨false,false,5⟩, some ⟨false,true,1⟩, some ⟨false,false,4⟩, some ⟨false,false,0⟩, none]
theorem n18_eq : toAgent8 BusyBeaver.M_1RB1RE_1LC0RA_1LA0LD_1LB0LF_0RB0LE_0LAHHH.machine = n18 := by
  funext slot
  rcases slot with ⟨q,b⟩
  fin_cases q <;> cases b <;> rfl
theorem n18_never : NeverHalts n18 := by
  rw [← n18_eq]
  exact source_never BusyBeaver.M_1RB1RE_1LC0RA_1LA0LD_1LB0LF_0RB0LE_0LAHHH.machine BusyBeaver.M_1RB1RE_1LC0RA_1LA0LD_1LB0LF_0RB0LE_0LAHHH.is_not_halt
theorem n18_cover : Cover NeverHalts (leaf n18) :=
  Cover.leaf _ (all_completions_never _ n18_never)
#print axioms n18_eq
#print axioms n18_never
#print axioms n18_cover

end BB6.Agent10Nov26
