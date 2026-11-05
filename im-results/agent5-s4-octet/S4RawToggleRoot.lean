import S4RawToggle
import S4ToggleRoot

namespace S4SourceBridge

/-- Exact, true-blank, infinite-horizon raw S4 halting criterion.
    All potential first failures in the stable P regime occur in
    10 of the 16 modulo-16 prefix phases. No phase is asserted reachable
    at the failing gate: this remains an open problem. -/
theorem original_machine_halts_iff_ten_phases :
    BusyBeaver.IsHalt
      BusyBeaver.M_1RB0LD_1LC1RD_0LE1LA_0RB1RD_HHH0LF_1RA1LF.target ↔
    ∃ n T,
       S4Toggle.prun (7+n) S4ToggleRoot.root =
         some ((S4TogglePair.pairRun n).1::(S4TogglePair.pairRun n).2::T) ∧
       S4ToggleRoot.DangerPhase (n%16) ∧
       S4Toggle.P ((S4TogglePair.pairRun n).1::(S4TogglePair.pairRun n).2::T)=none := by
  exact original_machine_halts_iff_three_drains.trans
    S4ToggleRoot.rooted_halt_iff_ten_phases

#print axioms original_machine_halts_iff_ten_phases
end S4SourceBridge
