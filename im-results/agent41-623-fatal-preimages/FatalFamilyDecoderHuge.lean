import FatalFamilyDigitDecoderSource

namespace BB6.Agent41FatalInverseSource
open BB6.Agent41FatalInverse
open BB6.Agent49ParitySource
open BusyBeaver.M_1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_HHH0LA
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

theorem googol_left : leftCandidate (10^100-1)=none := by decide +kernel
theorem googol_right : rightCandidate (10^100-1)=none := by decide +kernel

theorem googol_excluded : ∀ i, run i≠some (.D (targetX (10^100-1)) (targetY (10^100-1))) :=
  root_decoder_excluded _ (by decide +kernel) (by decide +kernel) googol_left googol_right

#print axioms googol_left
#print axioms googol_right
#print axioms googol_excluded
end BB6.Agent41FatalInverseSource
