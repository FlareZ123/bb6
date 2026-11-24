import Agent41FatalSpectrumRegisters
import Agent49FullFailureSpectrumSource

namespace BB6.Agent41SpectrumRegisters
open BB6.Agent49FullSpectrum
open BusyBeaver.M_1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_HHH0LA

theorem badAll_recurrence : Recurrence badAll := by
  intro a b
  rw [badAll]

theorem source_mask_exact (a b d : Nat) :
    drainB a b d = none ↔ (masks b).mid.testBit a = true := by
  rw [drain_none_iff_badAll]
  rw [(masks_correct badAll badAll_recurrence b a).2.1]

#print axioms source_mask_exact
end BB6.Agent41SpectrumRegisters
