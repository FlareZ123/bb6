import Lean.Elab.Tactic.Omega
import EChainDoubleBReentry
import PacketP2ResetSource

set_option maxHeartbeats 40000000
set_option maxRecDepth 16384

namespace BB6.Agent37EChainBEEAReentry

open CryptidBoundary BB6.Agent31PacketSource
open BB6.Agent37EChain BB6.Agent37EChainBExit
open BB6.Agent2PacketP2Reset BB6.Agent35K4Shapes
open BB6.Agent37EChainDoubleBReentry

def eTime (k q : Nat) : Nat := 12*k*k+49*k+58+6*q

/-- P2 reset followed by the first E-chain step.  The quotient h is
    exposed so the residue-specific B/E continuations can share it. -/
theorem reset_one_E (k h Q : Nat) (hh : 1 ≤ h)
    (hk : 2*k+1=3*h) :
    run (eTwoTime k Q + chainTime 1 h 0)
      (packet (3*k+4) Q 2 (false :: List.replicate 6 true)) =
      packet (1+32*h) 2 (2*Q+3) BB6.Agent35K4Shapes.marker := by
  have hprefix : 8*k+5=1+4*3*h := by
    calc
      8*k+5=4*(2*k+1)+1 := by omega
      _=4*(3*h)+1 := by rw [hk]
      _=1+4*3*h := by omega
  have hm : BB6.Agent2PacketP2Reset.marker =
      BB6.Agent35K4Shapes.marker := by decide
  have hreset :
      run (eTwoTime k Q)
        (packet (3*k+4) Q 2 (false :: List.replicate 6 true)) =
      packet (1+4*3*h) 0 (2*Q+6)
        BB6.Agent35K4Shapes.marker := by
    rw [e_two_reset,hprefix,hm]
  have hchain :
      run (chainTime 1 h 0)
        (packet (1+4*3*h) 0 (3+(2*Q+3))
          BB6.Agent35K4Shapes.marker) =
      packet (1+32*h) 2 (2*Q+3)
        BB6.Agent35K4Shapes.marker := by
    simpa [chainTime] using
      (BB6.Agent37EChain.chain_return 1 h 0 (2*Q+3)
        BB6.Agent35K4Shapes.marker hh)
  calc
    run (eTwoTime k Q + chainTime 1 h 0)
        (packet (3*k+4) Q 2 (false :: List.replicate 6 true)) =
      run (chainTime 1 h 0)
        (run (eTwoTime k Q)
          (packet (3*k+4) Q 2 (false :: List.replicate 6 true)) := by
            rw [run_add]
    _ = packet (1+32*h) 2 (2*Q+3)
        BB6.Agent35K4Shapes.marker := by rw [hreset,hchain]

/-- Turn a source-certified A-marker prefix into a canonical
    DRegularSource section, carrying the unary floor needed by padding. -/
theorem finish_A_to_source (c : Cfg) (ka q p : Nat)
    (hprefix : ∃ T, run T c =
      packet (3*ka+3) q p BB6.Agent35K4Shapes.marker) :
    ∃ (T a q' b : Nat),
      ObsEq (run T c) (DRegularSource.sourceSection ⟨a,q',b⟩) ∧
      DRegular.Canon ⟨a,q',b⟩ := by
  obtain ⟨Tp,hp⟩ := hprefix
  obtain ⟨ta,n,hA,hn⟩ :=
    BB6.Agent37EChainDoubleBReentry.all_A_marker_returns_floor ka q p
  let floor := 2*(4*ka+3)+5
  have hf : regularEndpointFloor c floor := by
    refine ⟨Tp+ta,n,?_ ,hn⟩
    rw [run_add,hp]
    exact hA
  exact regularEndpointFloor_sourceSection c floor
    (by dsimp [floor]; omega) hf

/-- k=243*t+88: one E, B, B, E, then the universal A-marker return. -/
def time243_88 (t Q : Nat) : Nat :=
  (eTwoTime (243*t+88) Q + chainTime 1 (162*t+59) 0) +
    (bTime (1728*t+629) +
      (bTime (4608*t+1680) + eTime (12288*t+4482) 0))

theorem prefix243_88 (t Q : Nat) :
    run (time243_88 t Q)
      (packet (3*(243*t+88)+4) Q 2
        (false :: List.replicate 6 true)) =
      packet (3*(32768*t+11954)+3) 2 (2*Q)
        BB6.Agent35K4Shapes.marker := by
  have hreset := reset_one_E (243*t+88) (162*t+59) Q
    (by omega) (by omega)
  have h1 : 1+32*(162*t+59)=3*(1728*t+629)+2 := by omega
  have h2 : 8*(1728*t+629)+10=3*(4608*t+1680)+2 := by omega
  have h3 : 8*(4608*t+1680)+10=3*(12288*t+4482)+4 := by omega
  have h4 : 8*(12288*t+4482)+9=3*(32768*t+11954)+3 := by omega
  have hb1 :
      run (bTime (1728*t+629))
        (packet (3*(1728*t+629)+2) 2 (2*Q+3)
          BB6.Agent35K4Shapes.marker) =
      packet (8*(1728*t+629)+10) 1 (2*Q+3)
        BB6.Agent35K4Shapes.marker :=
    BB6.Agent31PacketSource.b_packet (1728*t+629) 1 (2*Q+3)
      BB6.Agent35K4Shapes.marker
  have hb2 :
      run (bTime (4608*t+1680))
        (packet (3*(4608*t+1680)+2) 1 (2*Q+3)
          BB6.Agent35K4Shapes.marker) =
      packet (8*(4608*t+1680)+10) 0 (2*Q+3)
        BB6.Agent35K4Shapes.marker :=
    BB6.Agent31PacketSource.b_packet (4608*t+1680) 0 (2*Q+3)
      BB6.Agent35K4Shapes.marker
  have he :
      run (eTime (12288*t+4482) 0)
        (packet (3*(12288*t+4482)+4) 0 (2*Q+3)
          BB6.Agent35K4Shapes.marker) =
      packet (8*(12288*t+4482)+9) 2 (2*Q)
        BB6.Agent35K4Shapes.marker :=
    BB6.Agent31PacketSource.e_packet (12288*t+4482) 0 (2*Q)
      BB6.Agent35K4Shapes.marker
  unfold time243_88
  rw [run_add,hreset,run_add,h1,run_add,hb1,h2,
    run_add,hb2,h3,he,h4]
  rfl

theorem reset243_88_source_reentry (t Q : Nat) :
    ∃ (T a q b : Nat),
      ObsEq
        (run T (packet (3*(243*t+88)+4) Q 2
          (false :: List.replicate 6 true)))
        (DRegularSource.sourceSection ⟨a,q,b⟩) ∧
      DRegular.Canon ⟨a,q,b⟩ := by
  apply finish_A_to_source
    (packet (3*(243*t+88)+4) Q 2
      (false :: List.replicate 6 true))
    (32768*t+11954) 2 (2*Q)
  exact ⟨time243_88 t Q,prefix243_88 t Q⟩

/-- k=243*t+97: one E, B, E, E, then A. -/
def time243_97 (t Q : Nat) : Nat :=
  (eTwoTime (243*t+97) Q + chainTime 1 (162*t+65) 0) +
    (bTime (1728*t+693) +
      (eTime (4608*t+1850) 1 + eTime (12288*t+4935) 3))

theorem prefix243_97 (t Q : Nat) (hQ : 2 ≤ Q) :
    run (time243_97 t Q)
      (packet (3*(243*t+97)+4) Q 2
        (false :: List.replicate 6 true)) =
      packet (3*(32768*t+13162)+3) 5 (2*Q-3)
        BB6.Agent35K4Shapes.marker := by
  have hreset := reset_one_E (243*t+97) (162*t+65) Q
    (by omega) (by omega)
  have h1 : 1+32*(162*t+65)=3*(1728*t+693)+2 := by omega
  have h2 : 8*(1728*t+693)+10=3*(4608*t+1850)+4 := by omega
  have h3 : 8*(4608*t+1850)+9=3*(12288*t+4935)+4 := by omega
  have h4 : 8*(12288*t+4935)+9=3*(32768*t+13162)+3 := by omega
  have hb :
      run (bTime (1728*t+693))
        (packet (3*(1728*t+693)+2) 2 (2*Q+3)
          BB6.Agent35K4Shapes.marker) =
      packet (8*(1728*t+693)+10) 1 (2*Q+3)
        BB6.Agent35K4Shapes.marker :=
    BB6.Agent31PacketSource.b_packet (1728*t+693) 1 (2*Q+3)
      BB6.Agent35K4Shapes.marker
  have he1 :
      run (eTime (4608*t+1850) 1)
        (packet (3*(4608*t+1850)+4) 1 (2*Q+3)
          BB6.Agent35K4Shapes.marker) =
      packet (8*(4608*t+1850)+9) 3 (2*Q)
        BB6.Agent35K4Shapes.marker :=
    BB6.Agent31PacketSource.e_packet (4608*t+1850) 1 (2*Q)
      BB6.Agent35K4Shapes.marker
  have he2 :
      run (eTime (12288*t+4935) 3)
        (packet (3*(12288*t+4935)+4) 3 (2*Q)
          BB6.Agent35K4Shapes.marker) =
      packet (8*(12288*t+4935)+9) 5 (2*Q-3)
        BB6.Agent35K4Shapes.marker := by
    have hP : 2*Q-3+3=2*Q := by omega
    simpa [hP] using
      (BB6.Agent31PacketSource.e_packet (12288*t+4935) 3
        (2*Q-3) BB6.Agent35K4Shapes.marker)
  unfold time243_97
  rw [run_add,hreset,run_add,h1,run_add,hb,h2,
    run_add,he1,h3,he2,h4]
  rfl

theorem reset243_97_source_reentry (t Q : Nat) (hQ : 2 ≤ Q) :
    ∃ (T a q b : Nat),
      ObsEq
        (run T (packet (3*(243*t+97)+4) Q 2
          (false :: List.replicate 6 true)))
        (DRegularSource.sourceSection ⟨a,q,b⟩) ∧
      DRegular.Canon ⟨a,q,b⟩ := by
  apply finish_A_to_source
    (packet (3*(243*t+97)+4) Q 2
      (false :: List.replicate 6 true))
    (32768*t+13162) 5 (2*Q-3)
  exact ⟨time243_97 t Q,prefix243_97 t Q hQ⟩

/-- k=243*t+124: one E, B, E, B, then A. -/
def time243_124 (t Q : Nat) : Nat :=
  (eTwoTime (243*t+124) Q + chainTime 1 (162*t+83) 0) +
    (bTime (1728*t+885) +
      (eTime (4608*t+2362) 1 + bTime (12288*t+6301)))

theorem prefix243_124 (t Q : Nat) :
    run (time243_124 t Q)
      (packet (3*(243*t+124)+4) Q 2
        (false :: List.replicate 6 true)) =
      packet (3*(32768*t+16805)+3) 2 (2*Q)
        BB6.Agent35K4Shapes.marker := by
  have hreset := reset_one_E (243*t+124) (162*t+83) Q
    (by omega) (by omega)
  have h1 : 1+32*(162*t+83)=3*(1728*t+885)+2 := by omega
  have h2 : 8*(1728*t+885)+10=3*(4608*t+2362)+4 := by omega
  have h3 : 8*(4608*t+2362)+9=3*(12288*t+6301)+2 := by omega
  have h4 : 8*(12288*t+6301)+10=3*(32768*t+16805)+3 := by omega
  have hb1 :
      run (bTime (1728*t+885))
        (packet (3*(1728*t+885)+2) 2 (2*Q+3)
          BB6.Agent35K4Shapes.marker) =
      packet (8*(1728*t+885)+10) 1 (2*Q+3)
        BB6.Agent35K4Shapes.marker :=
    BB6.Agent31PacketSource.b_packet (1728*t+885) 1 (2*Q+3)
      BB6.Agent35K4Shapes.marker
  have he :
      run (eTime (4608*t+2362) 1)
        (packet (3*(4608*t+2362)+4) 1 (2*Q+3)
          BB6.Agent35K4Shapes.marker) =
      packet (8*(4608*t+2362)+9) 3 (2*Q)
        BB6.Agent35K4Shapes.marker :=
    BB6.Agent31PacketSource.e_packet (4608*t+2362) 1 (2*Q)
      BB6.Agent35K4Shapes.marker
  have hb2 :
      run (bTime (12288*t+6301))
        (packet (3*(12288*t+6301)+2) 3 (2*Q)
          BB6.Agent35K4Shapes.marker) =
      packet (8*(12288*t+6301)+10) 2 (2*Q)
        BB6.Agent35K4Shapes.marker :=
    BB6.Agent31PacketSource.b_packet (12288*t+6301) 2 (2*Q)
      BB6.Agent35K4Shapes.marker
  unfold time243_124
  rw [run_add,hreset,run_add,h1,run_add,hb1,h2,
    run_add,he,h3,hb2,h4]
  rfl

theorem reset243_124_source_reentry (t Q : Nat) :
    ∃ (T a q b : Nat),
      ObsEq
        (run T (packet (3*(243*t+124)+4) Q 2
          (false :: List.replicate 6 true)))
        (DRegularSource.sourceSection ⟨a,q,b⟩) ∧
      DRegular.Canon ⟨a,q,b⟩ := by
  apply finish_A_to_source
    (packet (3*(243*t+124)+4) Q 2
      (false :: List.replicate 6 true))
    (32768*t+16805) 2 (2*Q)
  exact ⟨time243_124 t Q,prefix243_124 t Q⟩

#print axioms reset_one_E
#print axioms finish_A_to_source
#print axioms reset243_88_source_reentry
#print axioms reset243_97_source_reentry
#print axioms reset243_124_source_reentry

end BB6.Agent37EChainBEEAReentry
