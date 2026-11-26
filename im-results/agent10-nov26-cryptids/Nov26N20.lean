import Nov26SourceCore
import BusyBeaver.BB6.NonHalt.M_1RB1LA_1RC0LE_1RD0LF_0LA0RD_1LC0LE_HHH0RE

namespace BB6.Agent10Nov26
open BB6Coverage BB6.ConjectureBridge
set_option maxHeartbeats 0

/-- Raw140; existing upstream nonhalting proof F068, with its unique halt row erased. -/
def n20 : Machine := literal [some ⟨true,true,1⟩, some ⟨true,false,0⟩, some ⟨true,true,2⟩, some ⟨false,false,4⟩, some ⟨true,true,3⟩, some ⟨false,false,5⟩, some ⟨false,false,0⟩, some ⟨false,true,3⟩, some ⟨true,false,2⟩, some ⟨false,false,4⟩, none, some ⟨false,true,4⟩]
theorem n20_eq :
    toAgent8 BusyBeaver.M_1RB1LA_1RC0LE_1RD0LF_0LA0RD_1LC0LE_HHH0RE.machine = n20 := by
  funext slot
  rcases slot with ⟨q,b⟩
  fin_cases q <;> cases b <;> rfl
theorem n20_never : NeverHalts n20 := by
  rw [← n20_eq]
  exact source_never
    BusyBeaver.M_1RB1LA_1RC0LE_1RD0LF_0LA0RD_1LC0LE_HHH0RE.machine
    BusyBeaver.M_1RB1LA_1RC0LE_1RD0LF_0LA0RD_1LC0LE_HHH0RE.is_not_halt
theorem n20_cover : Cover NeverHalts (leaf n20) :=
  Cover.leaf _ (all_completions_never _ n20_never)
#print axioms n20_eq
#print axioms n20_never
#print axioms n20_cover

end BB6.Agent10Nov26
