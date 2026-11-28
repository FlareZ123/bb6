import Raw13Coupled6
import CryptidsTapeAdapter
import BusyBeaver.Bridge
import BusyBeaver.BB6.NonHalt.M_1RB1LD_1RC0RB_1LA1RE_1LF0LA_1LA0RD_1LCHHH

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent46Raw13Coupled6
open BB6Coverage BB6.Agent13BlankDelay

def cryptidsSource : ConjectureMachines.Machine 6 2 :=
  BusyBeaver.M_1RB1LD_1RC0RB_1LA1RE_1LF0LA_1LA0RD_1LCHHH.machine

theorem cryptids_literal_eq :
    BB6.ConjectureBridge.toAgent8 cryptidsSource =
      BB6.Agent46Raw13CoupledParent.published := by
  funext s
  rcases s with ⟨q,b⟩
  fin_cases q <;> cases b <;> rfl

theorem published_never_source :
    NeverHalts BB6.Agent46Raw13CoupledParent.published := by
  rw [← cryptids_literal_eq]
  exact BB6.ConjectureBridge.not_halts_to_agent8 cryptidsSource
    ((ConjectureMachines.isNotHalt_toBB_iff_not_halts cryptidsSource).mp
      (by
        simpa [cryptidsSource] using
          BusyBeaver.M_1RB1LD_1RC0RB_1LA1RE_1LF0LA_1LA0RD_1LCHHH.is_not_halt))

theorem unconditional_bound (m : Machine) (hm : compatible parent m) :
    WeightedBound B m :=
  bound published_never_source m hm

theorem unconditional_exact_threshold (N : Nat) :
    (∀ m, compatible parent m → WeightedBound N m) ↔ B ≤ N :=
  exact_threshold published_never_source N

#print axioms cryptids_literal_eq
#print axioms published_never_source
#print axioms unconditional_bound
#print axioms unconditional_exact_threshold
end BB6.Agent46Raw13Coupled6
