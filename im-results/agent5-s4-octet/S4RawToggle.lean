import S4RawOctet
import S4Toggle

namespace S4SourceBridge

/-- Original six-state blank-tape S4 halting is equivalent to failure of the
    stable two-octet triple carry transducer on its exact genuine root. -/
theorem original_machine_halts_iff_three_drains :
    BusyBeaver.IsHalt
      BusyBeaver.M_1RB0LD_1LC1RD_0LE1LA_0RB1RD_HHH0LF_1RA1LF.target ↔
    ∃ n, S4Toggle.prun n [301,650,645,322,163,160] = none := by
  exact original_machine_halts_iff_octet_tail.trans S4Toggle.halt_iff_prun

#print axioms original_machine_halts_iff_three_drains
end S4SourceBridge
