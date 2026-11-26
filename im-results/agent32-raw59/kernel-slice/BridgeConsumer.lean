import Raw59BridgeSlice
import BlockFAR2

open BB6Coverage
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace BB6.Agent32SlicePilot

def literal : PartialMachine := fun slot =>
  ([some (some ⟨true,true,1⟩), some (some ⟨true,false,1⟩),
    some (some ⟨true,true,2⟩), some (some ⟨false,false,1⟩),
    some (some ⟨false,true,3⟩), some (some ⟨false,true,5⟩),
    some (some ⟨true,false,3⟩), some (some ⟨true,true,4⟩),
    some (some ⟨true,true,3⟩), some (some ⟨true,false,0⟩),
    none, some (some ⟨true,true,0⟩)] : List (Option Transition))[2*slot.1.val+slot.2.toNat]?.getD none

theorem exact_table : literal = A32Raw59BridgeSlice.BB6.Agent32Raw59LB1Block194.table := by
  funext slot
  rcases slot with ⟨q,b⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> cases b <;> rfl

theorem never (m : Machine) (hm : compatible literal m) : NeverHalts m := by
  rw [exact_table] at hm
  exact A32Raw59BridgeSlice.BB6.Agent32Raw59LB1Block194.never m hm

#print axioms exact_table
#print axioms never
end BB6.Agent32SlicePilot
