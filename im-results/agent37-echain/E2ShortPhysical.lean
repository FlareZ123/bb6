import Lean.Elab.Tactic.Omega
import BoundaryPadding
import E2ShortPositive

set_option maxRecDepth 8192
set_option maxHeartbeats 12000000

namespace BB6.Agent37ShortEPhysical

open CryptidBoundary BB6.Agent31PacketSource
open BB6.BoundaryPadding

/-- Terminal zeros at the right of a prepared packet are physical blanks,
    regardless of whether they appear in its finite list. -/
private theorem zeroPad (T a q p : Nat) :
    ObsEq
      (run T (packet a q p [false,true]))
      (run T (packet a q p [false,true,false,false])) := by
  simpa [packet,word,List.append_assoc,List.replicate] using
    (source_pad T 0 2 (packet a q p [false,true]))

/-- Physical source semantics removes the two *explicit* zeros required by
    the uniform positive-q local turn. This covers the genuine implicit
    blank tail 01, not only a fabricated zero-padded finite list. -/
theorem e_two_short_implicit_blank (k q : Nat) :
    ObsEq
      (run (12*k*k+49*k+64+4*(q+1))
        (packet (3*k+4) (q+1) 2 [false,true]))
      (packet (8*k+5) 0 (2*(q+1)+2)
        (false :: List.replicate 8 true)) := by
  have hp := zeroPad
    (12*k*k+49*k+64+4*(q+1)) (3*k+4) (q+1) 2
  rw [BB6.Agent37ShortEPositive.e_two_short_positive k q []] at hp
  exact hp

#print axioms zeroPad
#print axioms e_two_short_implicit_blank

end BB6.Agent37ShortEPhysical
