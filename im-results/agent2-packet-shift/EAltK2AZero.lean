import Lean.Elab.Tactic.Omega
import MarkerZeroAZero
import EAltPacketCompose

namespace BB6.Agent2EAltK2AZero
open CryptidBoundary BB6.Agent31PacketSource
open BB6.BoundaryPadding
open BB6.Agent2BoundaryBZero
set_option maxHeartbeats 10000000

/-- The new E-to-zero-marker theorem followed by the arbitrary-depth
    original A p=0 terminal covers k≡2 mod3 and q≡0 mod3 for every
    positive alternating 11-marker depth. -/
theorem e_two_k2_q0_regular (t u r : Nat) :
    ∃ T a markerPairs b,
      ObsEq
        (run T
          (packet (3*(3*t+2)+4) (3*u) 2
            (BB6.Agent2MarkerTower.marker (r+1))))
        (regularSection a markerPairs b) := by
  let ka : Nat := 8*t+6
  have ha : 8*(3*t+2)+5 = 3*ka+3 := by dsimp [ka]; omega
  have hp : 2*(3*u)+6 = 3*(2*u+2) := by omega
  obtain ⟨Ta,a,z,b,hA⟩ :=
    BB6.Agent2MarkerZeroAZero.aZeroRegular ka 0 (2*u+2) (r+2)
  have hE := BB6.Agent2EAltPacketCompose.e_two_to_zero
    (3*t+2) (3*u) r
  rw [ha,hp] at hE
  refine ⟨(12*(3*t+2)*(3*t+2)+49*(3*t+2)+68+
    4*(3*u)+6*r)+Ta,a,z,b,?_⟩
  rw [run_add,hE]
  exact hA

#print axioms e_two_k2_q0_regular
end BB6.Agent2EAltK2AZero
