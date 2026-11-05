import S4RawToggle
import S4TripleRoot

namespace S4SourceBridge

/-- The original blank six-state S4 halts exactly if its authentic
    triple-drain orbit reaches a failure at one of 12 modulo-32 phases.
    All other 20 phase classes are uniformly safe for arbitrary suffixes.
    This theorem makes no reachability assertion for a failing suffix. -/
theorem original_machine_halts_iff_twelve_of_thirtytwo :
    BusyBeaver.IsHalt
      BusyBeaver.M_1RB0LD_1LC1RD_0LE1LA_0RB1RD_HHH0LF_1RA1LF.target ↔
    ∃ n T,
       S4Toggle.prun (23+n) S4TripleRoot.root =
         some ((S4TripleHead.tripleRun n).1::(S4TripleHead.tripleRun n).2.1::
              (S4TripleHead.tripleRun n).2.2::T) ∧
       S4TripleRoot.DangerPhase (n%32) ∧
       S4Toggle.P ((S4TripleHead.tripleRun n).1::(S4TripleHead.tripleRun n).2.1::
              (S4TripleHead.tripleRun n).2.2::T)=none := by
  exact original_machine_halts_iff_three_drains.trans
    S4TripleRoot.rooted_halt_iff_twelve_phases

#print axioms original_machine_halts_iff_twelve_of_thirtytwo
end S4SourceBridge
