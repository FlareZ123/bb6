import CryptidsTapeAdapter
import BusyBeaver.Bridge
import BusyBeaver.BB6.NonHalt.M_1RB1LD_1RC0RB_1LA0RE_1LC1LE_1LF0LA_0REHHH
import BusyBeaver.BB6.NonHalt.M_1RB1LD_1RC0RB_1LA1RE_1LF0LA_1LA0RD_1LCHHH

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent46Raw13UpstreamSource
open BB6Coverage

def source1 : ConjectureMachines.Machine 6 2 := BusyBeaver.M_1RB1LD_1RC0RB_1LA0RE_1LC1LE_1LF0LA_0REHHH.machine

def candidate1 : Machine := fun s => ([some ⟨true, true, 1⟩, some ⟨true, false, 3⟩, some ⟨true, true, 2⟩, some ⟨false, true, 1⟩, some ⟨true, false, 0⟩, some ⟨false, true, 4⟩, some ⟨true, false, 2⟩, some ⟨true, false, 4⟩, some ⟨true, false, 5⟩, some ⟨false, false, 0⟩, some ⟨false, true, 4⟩, none] : List (Option Move))[2*s.1.val+s.2.toNat]?.getD none

theorem original_eq_candidate1 : BB6.ConjectureBridge.toAgent8 source1 = candidate1 := by
  funext slot
  rcases slot with ⟨q,b⟩
  fin_cases q <;> cases b <;> rfl

theorem candidate_never1 : NeverHalts candidate1 := by
  rw [← original_eq_candidate1]
  exact BB6.ConjectureBridge.not_halts_to_agent8 source1
    ((ConjectureMachines.isNotHalt_toBB_iff_not_halts source1).mp
      (by simpa [source1] using BusyBeaver.M_1RB1LD_1RC0RB_1LA0RE_1LC1LE_1LF0LA_0REHHH.is_not_halt))

#print axioms original_eq_candidate1
#print axioms candidate_never1

def source2 : ConjectureMachines.Machine 6 2 := BusyBeaver.M_1RB1LD_1RC0RB_1LA1RE_1LF0LA_1LA0RD_1LCHHH.machine

def candidate2 : Machine := fun s => ([some ⟨true, true, 1⟩, some ⟨true, false, 3⟩, some ⟨true, true, 2⟩, some ⟨false, true, 1⟩, some ⟨true, false, 0⟩, some ⟨true, true, 4⟩, some ⟨true, false, 5⟩, some ⟨false, false, 0⟩, some ⟨true, false, 0⟩, some ⟨false, true, 3⟩, some ⟨true, false, 2⟩, none] : List (Option Move))[2*s.1.val+s.2.toNat]?.getD none

theorem original_eq_candidate2 : BB6.ConjectureBridge.toAgent8 source2 = candidate2 := by
  funext slot
  rcases slot with ⟨q,b⟩
  fin_cases q <;> cases b <;> rfl

theorem candidate_never2 : NeverHalts candidate2 := by
  rw [← original_eq_candidate2]
  exact BB6.ConjectureBridge.not_halts_to_agent8 source2
    ((ConjectureMachines.isNotHalt_toBB_iff_not_halts source2).mp
      (by simpa [source2] using BusyBeaver.M_1RB1LD_1RC0RB_1LA1RE_1LF0LA_1LA0RD_1LCHHH.is_not_halt))

#print axioms original_eq_candidate2
#print axioms candidate_never2

end BB6.Agent46Raw13UpstreamSource
