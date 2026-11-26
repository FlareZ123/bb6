import Nov26SourceCore
import BusyBeaver.BB6.NonHalt.M_1RB1LF_1RC1RB_1RD0RB_0LE0LF_HHH1LD_0LE1LA
import BusyBeaver.BB6.NonHalt.M_1RB0RC_1RCHHH_1LD1RE_1LE0LD_1RA0LF_0RC0RB

namespace BB6.Agent10Nov26
open BB6Coverage BB6.ConjectureBridge
set_option maxHeartbeats 0

/-- Raw140; pinned upstream ordinary-row leaf. -/
def n16 : Machine := literal [some ⟨true,true,1⟩, some ⟨true,false,5⟩, some ⟨true,true,2⟩, some ⟨true,true,1⟩, some ⟨true,true,3⟩, some ⟨false,true,1⟩, some ⟨false,false,4⟩, some ⟨false,false,5⟩, none, some ⟨true,false,3⟩, some ⟨false,false,4⟩, some ⟨true,false,0⟩]
theorem n16_eq : toAgent8 BusyBeaver.M_1RB1LF_1RC1RB_1RD0RB_0LE0LF_HHH1LD_0LE1LA.machine = n16 := by
  funext slot
  rcases slot with ⟨q,b⟩
  fin_cases q <;> cases b <;> rfl
theorem n16_never : NeverHalts n16 := by
  rw [← n16_eq]
  exact source_never BusyBeaver.M_1RB1LF_1RC1RB_1RD0RB_0LE0LF_HHH1LD_0LE1LA.machine BusyBeaver.M_1RB1LF_1RC1RB_1RD0RB_0LE0LF_HHH1LD_0LE1LA.is_not_halt
theorem n16_cover : Cover NeverHalts (leaf n16) :=
  Cover.leaf _ (all_completions_never _ n16_never)
#print axioms n16_eq
#print axioms n16_never
#print axioms n16_cover

/-- Raw139; pinned upstream ordinary-row leaf. -/
def n9 : Machine := literal [some ⟨true,true,1⟩, some ⟨false,true,2⟩, some ⟨true,true,2⟩, none, some ⟨true,false,3⟩, some ⟨true,true,4⟩, some ⟨true,false,4⟩, some ⟨false,false,3⟩, some ⟨true,true,0⟩, some ⟨false,false,5⟩, some ⟨false,true,2⟩, some ⟨false,true,1⟩]
theorem n9_eq : toAgent8 BusyBeaver.M_1RB0RC_1RCHHH_1LD1RE_1LE0LD_1RA0LF_0RC0RB.machine = n9 := by
  funext slot
  rcases slot with ⟨q,b⟩
  fin_cases q <;> cases b <;> rfl
theorem n9_never : NeverHalts n9 := by
  rw [← n9_eq]
  exact source_never BusyBeaver.M_1RB0RC_1RCHHH_1LD1RE_1LE0LD_1RA0LF_0RC0RB.machine BusyBeaver.M_1RB0RC_1RCHHH_1LD1RE_1LE0LD_1RA0LF_0RC0RB.is_not_halt
theorem n9_cover : Cover NeverHalts (leaf n9) :=
  Cover.leaf _ (all_completions_never _ n9_never)
#print axioms n9_eq
#print axioms n9_never
#print axioms n9_cover

end BB6.Agent10Nov26
