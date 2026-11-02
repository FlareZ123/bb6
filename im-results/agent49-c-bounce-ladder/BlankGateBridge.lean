import Agent46CBridge
import SectionReach

namespace BB6.Agent49

/-- Original-source accelerated Machine C blank orbit halts exactly if the
    authenticated two-counter section reaches one of three exponential gates. -/
theorem blank_halts_iff_reachable_power_gate :
    BB6.CReachBridge.RunHalts ↔
      ∃ s : Pair, SecReach s ∧ SectionGate s.1 s.2 :=
  BB6.Agent46.blank_halts_iff_arithmetic.trans section_halt_iff_reachable_gate

#print axioms blank_halts_iff_reachable_power_gate
end BB6.Agent49
