import Lean.Elab.Tactic.Omega
import EChainBEEAReentry

set_option maxHeartbeats 40000000
set_option maxRecDepth 16384

namespace BB6.Agent37EChain169Split

open CryptidBoundary BB6.Agent31PacketSource
open BB6.Agent37EChain BB6.Agent37EChainBExit
open BB6.Agent2PacketP2Reset BB6.Agent35K4Shapes
open BB6.Agent37EChainDoubleBReentry
open BB6.Agent37EChainBEEAReentry

/-- Exact source-prefix time for the middle ternary child of the previously
    uncovered k ≡ 169 (mod 243) P2-reset class. -/
def time729_412 (s Q : Nat) : Nat :=
  (eTwoTime (729*s+412) Q + chainTime 1 (486*s+275) 0) +
    (bTime (5184*s+2933) +
      (bTime (13824*s+7824) +
        (eTime (36864*s+20866) 0 +
          bTime (98304*s+55645))))

/-- The class k=729*s+412 is forced through
    reset → E → B → B → E → B and lands on the universal A-marker family. -/
theorem prefix729_412 (s Q : Nat) :
    run (time729_412 s Q)
      (packet (3*(729*s+412)+4) Q 2
        (false :: List.replicate 6 true)) =
      packet (3*(262144*s+148389)+3) 1 (2*Q)
        BB6.Agent35K4Shapes.marker := by
  have hreset :=
    reset_one_E (729*s+412) (486*s+275) Q
      (by omega) (by omega)
  have h1 :
      1+32*(486*s+275) = 3*(5184*s+2933)+2 := by
    omega
  have h2 :
      8*(5184*s+2933)+10 = 3*(13824*s+7824)+2 := by
    omega
  have h3 :
      8*(13824*s+7824)+10 = 3*(36864*s+20866)+4 := by
    omega
  have h4 :
      8*(36864*s+20866)+9 = 3*(98304*s+55645)+2 := by
    omega
  have h5 :
      8*(98304*s+55645)+10 = 3*(262144*s+148389)+3 := by
    omega
  have hb1 :
      run (bTime (5184*s+2933))
        (packet (3*(5184*s+2933)+2) 2 (2*Q+3)
          BB6.Agent35K4Shapes.marker) =
      packet (8*(5184*s+2933)+10) 1 (2*Q+3)
        BB6.Agent35K4Shapes.marker :=
    BB6.Agent31PacketSource.b_packet
      (5184*s+2933) 1 (2*Q+3) BB6.Agent35K4Shapes.marker
  have hb2 :
      run (bTime (13824*s+7824))
        (packet (3*(13824*s+7824)+2) 1 (2*Q+3)
          BB6.Agent35K4Shapes.marker) =
      packet (8*(13824*s+7824)+10) 0 (2*Q+3)
        BB6.Agent35K4Shapes.marker :=
    BB6.Agent31PacketSource.b_packet
      (13824*s+7824) 0 (2*Q+3) BB6.Agent35K4Shapes.marker
  have he :
      run (eTime (36864*s+20866) 0)
        (packet (3*(36864*s+20866)+4) 0 (2*Q+3)
          BB6.Agent35K4Shapes.marker) =
      packet (8*(36864*s+20866)+9) 2 (2*Q)
        BB6.Agent35K4Shapes.marker :=
    BB6.Agent31PacketSource.e_packet
      (36864*s+20866) 0 (2*Q) BB6.Agent35K4Shapes.marker
  have hb3 :
      run (bTime (98304*s+55645))
        (packet (3*(98304*s+55645)+2) 2 (2*Q)
          BB6.Agent35K4Shapes.marker) =
      packet (8*(98304*s+55645)+10) 1 (2*Q)
        BB6.Agent35K4Shapes.marker :=
    BB6.Agent31PacketSource.b_packet
      (98304*s+55645) 1 (2*Q) BB6.Agent35K4Shapes.marker
  unfold time729_412
  rw [run_add,hreset,run_add,h1,run_add,hb1,h2,
    run_add,hb2,h3,run_add,he,h4,hb3,h5]

/-- A new infinite source-connected regular reentry cylinder inside the
    external 107-call terminal route: every k=729*s+412 P2 reset packet,
    for arbitrary Q, returns to a canonical DRegular source section.
    This is a prepared-packet theorem; it does not assert blank-root reachability. -/
theorem reset729_412_source_reentry (s Q : Nat) :
    ∃ (T a q b : Nat),
      ObsEq
        (run T (packet (3*(729*s+412)+4) Q 2
          (false :: List.replicate 6 true)))
        (DRegularSource.sourceSection ⟨a,q,b⟩) ∧
      DRegular.Canon ⟨a,q,b⟩ := by
  apply finish_A_to_source
    (packet (3*(729*s+412)+4) Q 2
      (false :: List.replicate 6 true))
    (262144*s+148389) 1 (2*Q)
  exact ⟨time729_412 s Q, prefix729_412 s Q⟩

#print axioms prefix729_412
#print axioms reset729_412_source_reentry

end BB6.Agent37EChain169Split
