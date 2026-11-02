import CSourceBridge
import FinalGate

namespace BB6.CStrongBridge

/-- The strongest published local modular gate characterization, now transported
    to actual blank-tape halting of upstream Cryptids' exact Turing machine. -/
theorem raw_halts_iff_mod8_gates :
    BusyBeaver.IsHalt CSourceBridge.Source.target ↔
      ((∃ j : Nat, 1 ≤ j ∧ j % 4 ≠ 1 ∧ j % 8 ≠ 4 ∧
          BB6CLine.Reach (2*j+1,3*j+4,0)) ∨
       (∃ n : Nat, 1 ≤ n ∧ BB6CLine.Reach (0,4*n,24*n+23))) :=
  CSourceBridge.raw_halts_iff_reachable_stop.trans
    BB6CLine.stops_iff_mod8_gates

#print axioms raw_halts_iff_mod8_gates
end BB6.CStrongBridge
