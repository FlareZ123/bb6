import Machine623Path
import CryptidsTapeAdapter
import BusyBeaver.BB6.M_1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_HHH0LA

namespace BB6.Agent8Machine623

/-- The exact unmodified original Cryptids BB6 #623 transition table,
    rooted at the source's designated blank A state. -/
def source : ConjectureMachines.Machine 6 2 :=
  BusyBeaver.M_1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_HHH0LA.machine

def original : BB6Coverage.Machine :=
  BB6.ConjectureBridge.toAgent8 source

/-- Genuine upstream-source-to-raw-model table equality, all twelve
    symbol/state rows including the unique halting input F/0. -/
theorem original_eq_machine623 : original = BB6Coverage.machine623 := by
  funext slot
  rcases slot with ⟨q,b⟩
  fin_cases q <;> cases b <;> rfl

/-- Every source-compatible completion of the first eleven genuinely
    reached inputs survives the first 54 physical primitive moves. -/
theorem source_machine_54_moves :
    (BB6Coverage.run original 54 BB6Coverage.blank).isSome = true := by
  rw [original_eq_machine623]
  exact BB6Coverage.machine623_uniform_54 BB6Coverage.machine623
    (BB6Coverage.machine623Prefix_compatible 11)

#print axioms original_eq_machine623
#print axioms source_machine_54_moves

end BB6.Agent8Machine623
