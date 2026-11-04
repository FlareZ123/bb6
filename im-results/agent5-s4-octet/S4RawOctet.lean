import S4RawCompact
import S4Octet

namespace S4SourceBridge

theorem compactRun_eq_octetRun (n : Nat) (T : List Nat) :
    compactRun n T = S4Octet.run n T := by
  have hf : _root_.compactNext = S4Power.F := by
    funext s
    exact ((S4Power.F_eq_source s).trans (S4Length.F_eq_original s)).symm
  induction n with
  | zero => rfl
  | succ n ih =>
      change (compactRun n T).bind _root_.compactNext =
        (S4Octet.run n T).bind S4Power.F
      rw [ih, hf]

/-- Complete reduction from the unchanged original six-state Turing machine
    to one eight-return (256 source-epoch) tail transducer Q. The exact
    halting decision remains the existence of an unsuccessful Q iterate. -/
theorem original_machine_halts_iff_octet_tail :
    BusyBeaver.IsHalt
      BusyBeaver.M_1RB0LD_1LC1RD_0LE1LA_0RB1RD_HHH0LF_1RA1LF.target ↔
    ∃ n, S4Octet.qrun n [481,133,28,25] = none := by
  calc
    BusyBeaver.IsHalt
        BusyBeaver.M_1RB0LD_1LC1RD_0LE1LA_0RB1RD_HHH0LF_1RA1LF.target ↔
        (∃ n, S4.reducedRun n [42,12,8,5] = none) :=
          original_machine_halts_iff_model.trans S4.blank_halts_iff_reduced
    _ ↔ (∃ n, S4Octet.run n [42,12,8,5] = none) := by
      simp only [← compactRun_eq_reducedRun, compactRun_eq_octetRun]
    _ ↔ (∃ n, S4Octet.qrun n [481,133,28,25] = none) :=
      S4Octet.halt_iff_qrun

#print axioms compactRun_eq_octetRun
#print axioms original_machine_halts_iff_octet_tail
end S4SourceBridge
