import Lean.Elab.Tactic.Omega
import ExceptionalEMarkerResidual
import MarkerOneSource
import PacketSource

set_option maxRecDepth 8192
set_option maxHeartbeats 15000000

namespace BB6.Agent37EOneModNineMarker

open CryptidBoundary BB6.Agent31PacketSource
open BB6.BoundaryPadding BB6.Padding

/-- The marked E2 cylinder k≡1 mod9 has a universal and explicit
    *one E edge -> A* route.  This is stronger than merely narrowing
    it to p≡1 modulo 3: it works for all Q, including Q=0,1 mod3. -/
theorem marked_one_mod_nine_regular (u Q : Nat) :
    ∃ T a r b,
      ObsEq
        (run T (BB6.Agent37EMarkerResidual.marked (9*u+1) Q))
        (BB6.Agent2BoundaryBZero.regularSection a r b) := by
  let m : Nat := 24*u+3
  let j : Nat := 64*u+10
  have hin : 3*m+4 = 8*(9*u+1)+5 := by dsimp [m]; omega
  have hout : 8*m+9 = 3*j+3 := by dsimp [m,j]; omega
  have hfirst : run (12*m*m+49*m+58)
      (BB6.Agent37EMarkerResidual.marked (9*u+1) Q) =
      packet (3*j+3) 2 (2*Q+3)
        BB6.Agent2PacketP2Reset.marker := by
    have he := e_packet m 0 (2*Q+3) BB6.Agent2PacketP2Reset.marker
    have hp : (2*Q+3)+3=2*Q+6 := by omega
    simpa only [BB6.Agent37EMarkerResidual.marked,
      Nat.zero_add,hin,hout,hp] using he
  obtain ⟨S,a,r,b,hA⟩ :=
    BB6.Agent35MarkerOne.a_marker_regular j 2 (2*Q+3)
  refine ⟨12*m*m+49*m+58+S,a,r,b,?_⟩
  rw [run_add,hfirst]
  simpa [BB6.Agent35MarkerOne.marker] using hA

#print axioms marked_one_mod_nine_regular

end BB6.Agent37EOneModNineMarker
