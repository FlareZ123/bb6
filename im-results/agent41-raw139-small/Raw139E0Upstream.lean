import Raw139SmallPair
import CryptidsTapeAdapter
import WeightedNonhaltLeafAdapter
import BusyBeaver.Bridge
import BusyBeaver.BB6.NonHalt.M_1RB0LE_1RC0RC_1LD0RB_1LA0LE_1LD1LF_1LDHHH

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace BB6.Agent41Raw139E0Upstream
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent47WeightedHalt
open BB6.Agent41Raw139Small BB6.Agent41Raw139SmallPlus BB6.Agent41Raw139SmallPair

def source : ConjectureMachines.Machine 6 2 :=
  BusyBeaver.M_1RB0LE_1RC0RC_1LD0RB_1LA0LE_1LD1LF_1LDHHH.machine

def original : Machine := BB6.ConjectureBridge.toAgent8 source

theorem original_never : NeverHalts original :=
  BB6.ConjectureBridge.not_halts_to_agent8 source
    ((ConjectureMachines.isNotHalt_toBB_iff_not_halts source).mp
      (by simpa [source] using
        BusyBeaver.M_1RB0LE_1RC0RC_1LD0RB_1LA0LE_1LD1LF_1LDHHH.is_not_halt))

def upstreamTable : PartialMachine := forgetHaltRows original

theorem upstreamTable_never : ∀ m, compatible upstreamTable m → NeverHalts m :=
  forgetHaltRows_all_completions_neverHalt original original_never

def e0Remaining := removeTable upstreamTable e0ResidualsPair
def parentRemaining := removeTable upstreamTable residualsPair

theorem e0_count : e0Remaining.length = 2 := by decide
theorem e0_mass : rawMass e0Remaining = 50 := by decide
theorem parent_count : parentRemaining.length = 77 := by decide
theorem parent_mass : rawMass parentRemaining = 4793671925 := by decide

theorem e0_contract_final :
    ∀ m, compatible e0Parent m →
      WeightedBound 512 m ∨ ∃ e ∈ e0Remaining, compatible e.2 m := by
  intro m hm
  exact removeTable_sound 512 upstreamTable upstreamTable_never
    e0ResidualsPair m (e0_contract_pair m hm)

theorem parent_contract_final :
    ∀ m, compatible BB6.Agent41Raw139Small.parent m →
      WeightedBound 512 m ∨ ∃ e ∈ parentRemaining, compatible e.2 m := by
  intro m hm
  exact removeTable_sound 512 upstreamTable upstreamTable_never
    residualsPair m (parent_contract_pair m hm)

#print axioms original_never
#print axioms upstreamTable_never
#print axioms e0_count
#print axioms e0_mass
#print axioms parent_count
#print axioms parent_mass
#print axioms e0_contract_final
#print axioms parent_contract_final
end BB6.Agent41Raw139E0Upstream
