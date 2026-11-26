import Nov26SourceCore
import BusyBeaver.BB6.NonHalt.M_1RB0LC_1RC0RA_1RD0RF_0LEHHH_1LB1LA_1LD1RA

namespace BB6.Agent10Nov26
open BB6Coverage BB6.ConjectureBridge
set_option maxHeartbeats 0

/-- Raw140; existing upstream nonhalting proof F262, with its unique halt row erased. -/
def n19 : Machine := literal [some ⟨true,true,1⟩, some ⟨false,false,2⟩, some ⟨true,true,2⟩, some ⟨false,true,0⟩, some ⟨true,true,3⟩, some ⟨false,true,5⟩, some ⟨false,false,4⟩, none, some ⟨true,false,1⟩, some ⟨true,false,0⟩, some ⟨true,false,3⟩, some ⟨true,true,0⟩]
theorem n19_eq :
    toAgent8 BusyBeaver.M_1RB0LC_1RC0RA_1RD0RF_0LEHHH_1LB1LA_1LD1RA.machine = n19 := by
  funext slot
  rcases slot with ⟨q,b⟩
  fin_cases q <;> cases b <;> rfl
theorem n19_never : NeverHalts n19 := by
  rw [← n19_eq]
  exact source_never
    BusyBeaver.M_1RB0LC_1RC0RA_1RD0RF_0LEHHH_1LB1LA_1LD1RA.machine
    BusyBeaver.M_1RB0LC_1RC0RA_1RD0RF_0LEHHH_1LB1LA_1LD1RA.is_not_halt
theorem n19_cover : Cover NeverHalts (leaf n19) :=
  Cover.leaf _ (all_completions_never _ n19_never)
#print axioms n19_eq
#print axioms n19_never
#print axioms n19_cover

end BB6.Agent10Nov26
