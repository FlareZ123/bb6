import Lean.Elab.Tactic.Omega
import EOneModNineMarker
import ExceptionalEMarkerResidual
import MarkerOneSource
import PacketSource

set_option maxRecDepth 8192
set_option maxHeartbeats 16000000

namespace BB6.Agent37EKernel27AClosures

open CryptidBoundary BB6.Agent31PacketSource
open BB6.BoundaryPadding BB6.Padding

/-- Every k=27v+22 marked E2 packet, regardless of Q, traverses
    exactly E -> E -> A before the universally source-certified A
    marker terminal. This is a nontrivial full all-natural cylinder. -/
theorem marked_22_mod_27_regular (v Q : Nat) :
    ∃ T a q b, ObsEq
      (run T (BB6.Agent37EMarkerResidual.marked (27*v+22) Q))
      (BB6.Agent2BoundaryBZero.regularSection a q b) := by
  let m1 : Nat := 72*v+59
  let m2 : Nat := 192*v+159
  let ka : Nat := 512*v+426
  let t1 : Nat := 12*m1*m1+49*m1+58
  let t2 : Nat := 12*m2*m2+49*m2+70
  have hin : 3*m1+4=8*(27*v+22)+5 := by dsimp [m1]; omega
  have hmid : 8*m1+9=3*m2+4 := by dsimp [m1,m2]; omega
  have hout : 8*m2+9=3*ka+3 := by dsimp [m2,ka]; omega
  have hp : (2*Q+3)+3=2*Q+6 := by omega
  have hfirst : run t1
      (BB6.Agent37EMarkerResidual.marked (27*v+22) Q) =
      packet (3*m2+4) 2 (2*Q+3)
        BB6.Agent2PacketP2Reset.marker := by
    have h := e_packet m1 0 (2*Q+3) BB6.Agent2PacketP2Reset.marker
    simpa only [t1, BB6.Agent37EMarkerResidual.marked,
      hin,hmid,hp,Nat.zero_add] using h
  have hsecond : run t2
      (packet (3*m2+4) 2 (2*Q+3)
        BB6.Agent2PacketP2Reset.marker) =
      packet (3*ka+3) 4 (2*Q)
        BB6.Agent2PacketP2Reset.marker := by
    have h := e_packet m2 2 (2*Q) BB6.Agent2PacketP2Reset.marker
    simpa only [t2,hout] using h
  obtain ⟨S,a,q,b,hA⟩ :=
    BB6.Agent35MarkerOne.a_marker_regular ka 4 (2*Q)
  refine ⟨t1+t2+S,a,q,b,?_⟩
  rw [show t1+t2+S=t1+(t2+S) by omega,
    run_add,hfirst,run_add,hsecond]
  simpa [BB6.Agent35MarkerOne.marker] using hA

/-- Every k=27v+25 marked E2 packet, regardless of Q, traverses
    E -> B -> A before the universally certified A marker terminal. -/
theorem marked_25_mod_27_regular (v Q : Nat) :
    ∃ T a q b, ObsEq
      (run T (BB6.Agent37EMarkerResidual.marked (27*v+25) Q))
      (BB6.Agent2BoundaryBZero.regularSection a q b) := by
  let m : Nat := 72*v+67
  let n : Nat := 192*v+181
  let ka : Nat := 512*v+485
  let tE : Nat := 12*m*m+49*m+58
  let tB : Nat := 12*n*n+49*n+40
  have hin : 3*m+4=8*(27*v+25)+5 := by dsimp [m]; omega
  have hmid : 8*m+9=3*n+2 := by dsimp [m,n]; omega
  have hout : 8*n+10=3*ka+3 := by dsimp [n,ka]; omega
  have hp : (2*Q+3)+3=2*Q+6 := by omega
  have hfirst : run tE
      (BB6.Agent37EMarkerResidual.marked (27*v+25) Q) =
      packet (3*n+2) 2 (2*Q+3)
        BB6.Agent2PacketP2Reset.marker := by
    have h := e_packet m 0 (2*Q+3) BB6.Agent2PacketP2Reset.marker
    simpa only [tE,BB6.Agent37EMarkerResidual.marked,
      hin,hmid,hp,Nat.zero_add] using h
  have hsecond : run tB
      (packet (3*n+2) 2 (2*Q+3)
        BB6.Agent2PacketP2Reset.marker) =
      packet (3*ka+3) 1 (2*Q+3)
        BB6.Agent2PacketP2Reset.marker := by
    have h := b_packet n 1 (2*Q+3) BB6.Agent2PacketP2Reset.marker
    simpa only [tB,hout] using h
  obtain ⟨S,a,q,b,hA⟩ :=
    BB6.Agent35MarkerOne.a_marker_regular ka 1 (2*Q+3)
  refine ⟨tE+tB+S,a,q,b,?_⟩
  rw [show tE+tB+S=tE+(tB+S) by omega,
    run_add,hfirst,run_add,hsecond]
  simpa [BB6.Agent35MarkerOne.marker] using hA

#print axioms marked_22_mod_27_regular
#print axioms marked_25_mod_27_regular

end BB6.Agent37EKernel27AClosures
