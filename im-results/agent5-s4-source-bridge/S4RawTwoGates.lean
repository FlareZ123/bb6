import S4Hazard
import S4UpstreamBridge

namespace S4SourceBridge

/-- Source-authentic halting criterion, conditional on successful compilation against
    unmodified pinned Cryptids imports. This theorem requires the whole source-mirrored
    S4 chain and the original source bridge, each audited at the imported revision. -/
theorem original_machine_halts_iff_two_exceptional_gates :
    BusyBeaver.IsHalt
      BusyBeaver.M_1RB0LD_1LC1RD_0LE1LA_0RB1RD_HHH0LF_1RA1LF.target ↔
    (∃ n s, (n % 8 = 4 ∨ n % 8 = 7) ∧
      S4.reducedRun (9 + n) [42,12,8,5] = some s ∧ S4.reduced s = none) :=
  original_machine_halts_iff_model.trans S4.blank_halts_iff_two_exceptional_gates

#print axioms S4SourceBridge.original_machine_halts_iff_two_exceptional_gates

end S4SourceBridge
