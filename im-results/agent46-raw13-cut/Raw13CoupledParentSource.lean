import Raw13Coupled3
import CryptidsTapeAdapter
import BusyBeaver.Bridge
import BusyBeaver.BB6.NonHalt.M_1RB1LD_1RC0RB_1LA1RE_1LF0LA_1LA0RD_1LCHHH

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent46Raw13CoupledParent
open BB6Coverage BB6.Agent13BlankDelay

def source : ConjectureMachines.Machine 6 2 := BusyBeaver.M_1RB1LD_1RC0RB_1LA1RE_1LF0LA_1LA0RD_1LCHHH.machine

theorem literal_published_eq : BB6.ConjectureBridge.toAgent8 source = published := by
  funext s
  rcases s with ⟨q,b⟩
  fin_cases q <;> cases b <;> rfl

theorem published_never : NeverHalts published := by
  rw [← literal_published_eq]
  exact BB6.ConjectureBridge.not_halts_to_agent8 source
    ((ConjectureMachines.isNotHalt_toBB_iff_not_halts source).mp
      (by simpa [source] using BusyBeaver.M_1RB1LD_1RC0RB_1LA1RE_1LF0LA_1LA0RD_1LCHHH.is_not_halt))

theorem unconditional_bound (m : Machine) (hm : compatible parent m) :
    WeightedBound 134 m := bound published_never m hm

theorem three_hole_bound (m : Machine) (hm : compatible BB6.Agent46Raw13Coupled3.parent m) :
    WeightedBound 134 m := BB6.Agent46Raw13Coupled3.bound published_never m hm

theorem three_hole_exact_threshold (B : Nat) :
    (∀ m, compatible BB6.Agent46Raw13Coupled3.parent m → WeightedBound B m) ↔ 134 ≤ B :=
  BB6.Agent46Raw13Coupled3.exact_threshold published_never B

#print axioms literal_published_eq
#print axioms published_never
#print axioms unconditional_bound
#print axioms three_hole_bound
#print axioms three_hole_exact_threshold
end BB6.Agent46Raw13CoupledParent
