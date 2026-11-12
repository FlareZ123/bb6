import Lean.Elab.Tactic.Omega
import ExceptionalE7SecondSafe
import EChainBEExit

namespace BB6.Agent37EERootBEA
open CryptidBoundary BB6.Agent31PacketSource
open BB6.Agent37EChain BB6.Agent37EChainBExit
open BB6.Agent2PacketP2Reset BB6.Agent2E7SecondSafe
open BB6.BoundaryPadding BB6.Agent2BoundaryBZero

set_option maxHeartbeats 16000000
set_option maxRecDepth 8192

private def fixedTail : List Bool := false :: List.replicate 6 true

private theorem markerEq :
    BB6.Agent2PacketP2Reset.marker = BB6.Agent35K4Shapes.marker := by
  decide

/-- An infinite subfamily of Agent 2's q=4 exceptional E/E source sections
    returns to a physical regularSection for u ≡ 1647 (mod 2187).  The path
    is two B edges, one E edge, the original E,p=2 reset, then the
    source-certified B->E->A corridor. -/
theorem q4_exceptional_EE_BEA_section (m : Nat) :
    ∃ (T a q b : Nat),
      ObsEq (run T
        (BB6.Agent2E7SecondSafe.sourceStart (2187*m+1647) 4))
        (BB6.Agent2BoundaryBZero.regularSection a q b) := by
  let z : Nat := 81*m+61
  let u : Nat := 2187*m+1647
  let k0 : Nat := 1728*z+53
  let k1 : Nat := 4608*z+144
  let k2 : Nat := 12288*z+386
  let k3 : Nat := 32768*z+1031
  let h : Nat := 1769472*m+1333253
  let t : Nat := 2097152*m+1580151
  have hu : u=27*z := by
    dsimp [u,z]
    simp only [Nat.mul_add]
    omega
  have hA0 : 192*u+161=3*k0+2 := by
    dsimp [u,z,k0]
    simp only [Nat.mul_add]
    omega
  have hB1 : 8*k0+10=3*k1+2 := by
    dsimp [k0,k1]
    simp only [Nat.mul_add]
    omega
  have hB2 : 8*k1+10=3*k2+4 := by
    dsimp [k1,k2]
    simp only [Nat.mul_add]
    omega
  have hE : 8*k2+9=3*k3+4 := by
    dsimp [k2,k3]
    simp only [Nat.mul_add]
    omega
  have hReset : 8*k3+5=1+4*3*h := by
    dsimp [k3,h,z]
    simp only [Nat.mul_add]
    omega
  have hBEA : 1+4*8*h=27*t+20 := by
    dsimp [h,t]
    simp only [Nat.mul_add]
    omega
  have houter : 8*(24*u+19)+9=192*u+161 := by
    simp only [Nat.mul_add]
    omega
  have hEE0 :=
    BB6.Agent2E7SecondSafe.exceptional_EE_packet u 4 (by omega)
  have hEE :
      ObsEq
        (run (BB6.Agent2E7SecondSafe.eTime u 4 +
          BB6.Agent2E7SecondSafe.middleTime u)
          (BB6.Agent2E7SecondSafe.sourceStart u 4))
        (packet (3*k0+2) 2 5 fixedTail) := by
    have hshape :
        ObsEq
          (run (BB6.Agent2E7SecondSafe.eTime u 4 +
            BB6.Agent2E7SecondSafe.middleTime u)
            (BB6.Agent2E7SecondSafe.sourceStart u 4))
          (packet (192*u+161) 2 5 fixedTail) := by
      simpa [BB6.Agent2E7SecondSafe.sourceStart,
        BB6.Agent2E7SecondSafe.secondOutput,
        fixedTail, houter, packet, word, CryptidBoundary.packetThree,
        BB6.Agent2E7SecondSafe.suffix2, CryptidBoundary.oppairs] using hEE0
    simpa [hA0] using hshape
  have hb1eq :
      run (BB6.Agent37EChainBExit.bTime k0)
        (packet (3*k0+2) 2 5 fixedTail) =
      packet (3*k1+2) 1 5 fixedTail := by
    have hb := BB6.Agent31PacketSource.b_packet k0 1 5 fixedTail
    simpa [BB6.Agent37EChainBExit.bTime, hB1] using hb
  have hb1 :
      ObsEq
        (run (BB6.Agent37EChainBExit.bTime k0)
          (packet (3*k0+2) 2 5 fixedTail))
        (packet (3*k1+2) 1 5 fixedTail) := by
    rw [hb1eq]
    exact BB6.Padding.cfgEq_refl _
  have hb2eq :
      run (BB6.Agent37EChainBExit.bTime k1)
        (packet (3*k1+2) 1 5 fixedTail) =
      packet (3*k2+4) 0 5 fixedTail := by
    have hb := BB6.Agent31PacketSource.b_packet k1 0 5 fixedTail
    simpa [BB6.Agent37EChainBExit.bTime, hB2] using hb
  have hb2 :
      ObsEq
        (run (BB6.Agent37EChainBExit.bTime k1)
          (packet (3*k1+2) 1 5 fixedTail))
        (packet (3*k2+4) 0 5 fixedTail) := by
    rw [hb2eq]
    exact BB6.Padding.cfgEq_refl _
  have heq :
      run (BB6.Agent37EChain.eTime k2 0)
        (packet (3*k2+4) 0 5 fixedTail) =
      packet (3*k3+4) 2 2 fixedTail := by
    have he := BB6.Agent31PacketSource.e_packet k2 0 2 fixedTail
    simpa [BB6.Agent37EChain.eTime, hE] using he
  have he :
      ObsEq
        (run (BB6.Agent37EChain.eTime k2 0)
          (packet (3*k2+4) 0 5 fixedTail))
        (packet (3*k3+4) 2 2 fixedTail) := by
    rw [heq]
    exact BB6.Padding.cfgEq_refl _
  have hresetEq :
      run (BB6.Agent2PacketP2Reset.eTwoTime k3 2)
        (packet (3*k3+4) 2 2 fixedTail) =
      packet (1+4*3^1*h) 0 (3*1+(3+4))
        BB6.Agent35K4Shapes.marker := by
    have hr := BB6.Agent2PacketP2Reset.e_two_reset k3 2
    simpa [BB6.Agent2PacketP2Reset.eTwoTime, hReset, markerEq] using hr
  have hreset :
      ObsEq
        (run (BB6.Agent2PacketP2Reset.eTwoTime k3 2)
          (packet (3*k3+4) 2 2 fixedTail))
        (packet (1+4*3^1*h) 0 (3*1+(3+4))
          BB6.Agent35K4Shapes.marker) := by
    rw [hresetEq]
    exact BB6.Padding.cfgEq_refl _
  let T0 : Nat :=
    BB6.Agent2E7SecondSafe.eTime u 4 +
      BB6.Agent2E7SecondSafe.middleTime u
  let T1 : Nat := T0 + BB6.Agent37EChainBExit.bTime k0
  let T2 : Nat := T1 + BB6.Agent37EChainBExit.bTime k1
  let T3 : Nat := T2 + BB6.Agent37EChain.eTime k2 0
  let T4 : Nat := T3 + BB6.Agent2PacketP2Reset.eTwoTime k3 2
  have h1 :
      ObsEq (run T1 (BB6.Agent2E7SecondSafe.sourceStart u 4))
        (packet (3*k1+2) 1 5 fixedTail) :=
    BB6.BoundaryPadding.source_chain T0
      (BB6.Agent37EChainBExit.bTime k0)
      (BB6.Agent2E7SecondSafe.sourceStart u 4)
      (packet (3*k0+2) 2 5 fixedTail)
      (packet (3*k1+2) 1 5 fixedTail) hEE hb1
  have h2 :
      ObsEq (run T2 (BB6.Agent2E7SecondSafe.sourceStart u 4))
        (packet (3*k2+4) 0 5 fixedTail) :=
    BB6.BoundaryPadding.source_chain T1
      (BB6.Agent37EChainBExit.bTime k1)
      (BB6.Agent2E7SecondSafe.sourceStart u 4)
      (packet (3*k1+2) 1 5 fixedTail)
      (packet (3*k2+4) 0 5 fixedTail) h1 hb2
  have h3 :
      ObsEq (run T3 (BB6.Agent2E7SecondSafe.sourceStart u 4))
        (packet (3*k3+4) 2 2 fixedTail) :=
    BB6.BoundaryPadding.source_chain T2
      (BB6.Agent37EChain.eTime k2 0)
      (BB6.Agent2E7SecondSafe.sourceStart u 4)
      (packet (3*k2+4) 0 5 fixedTail)
      (packet (3*k3+4) 2 2 fixedTail) h2 he
  have h4 :
      ObsEq (run T4 (BB6.Agent2E7SecondSafe.sourceStart u 4))
        (packet (1+4*3^1*h) 0 (3*1+(3+4))
          BB6.Agent35K4Shapes.marker) :=
    BB6.BoundaryPadding.source_chain T3
      (BB6.Agent2PacketP2Reset.eTwoTime k3 2)
      (BB6.Agent2E7SecondSafe.sourceStart u 4)
      (packet (3*k3+4) 2 2 fixedTail)
      (packet (1+4*3^1*h) 0 (3*1+(3+4))
        BB6.Agent35K4Shapes.marker) h3 hreset
  obtain ⟨Ttail,a,q',b,htail⟩ :=
    BB6.Agent37EChainBEExit.chain_B_E_A_reentry
      1 h t 0 4 (by omega) (by omega) (by simpa using hBEA)
  exact ⟨T4+Ttail,a,q',b,
    BB6.BoundaryPadding.source_chain T4 Ttail
      (BB6.Agent2E7SecondSafe.sourceStart u 4)
      (packet (1+4*3^1*h) 0 (3*1+(3+4))
        BB6.Agent35K4Shapes.marker)
      (BB6.Agent2BoundaryBZero.regularSection a q' b)
      h4 htail⟩

#print axioms q4_exceptional_EE_BEA_section
end BB6.Agent37EERootBEA
