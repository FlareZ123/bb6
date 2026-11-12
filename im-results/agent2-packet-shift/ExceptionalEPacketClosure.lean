import Lean.Elab.Tactic.Omega
import EFirstAPacket
import ExceptionalE7SecondSafe
import PacketSafeReentry
import AP2PacketBoundarySource
import PacketP2ReentryOrE

set_option maxHeartbeats 100000000
set_option maxRecDepth 55000

namespace BB6.Agent2ExceptionalEPacketClosure

open CryptidBoundary BB6.BoundaryPadding BB6.Padding
open BB6.Agent31PacketSource

def fixedTail : List Bool := BB6.Agent2PacketOneReentry.fixedTail

/-- The first E/A exceptional family produces a packet with p=2q.
    Whenever q is not 1 modulo 3, the universal safe-packet normalizer
    closes it to a regular section in finite primitive source time. -/
theorem exceptional_EA_safe_reentry (t q : Nat) (hq : 2 ≤ q)
    (hclass : q % 3 ≠ 1) :
    ∃ T a q' b,
      ObsEq
        (run (BB6.Agent2EFirstAPacket.duration t q + T)
          (DRegularSource.sourceSection ⟨9*t+10,q,1⟩))
        (BB6.Agent2BoundaryBZero.regularSection a q' b) := by
  let c : BB6.Agent31PacketRank.Packet := ⟨24*t+21,0,2*q⟩
  have hEA0 := BB6.Agent2EFirstAPacket.exceptional_EA_packet t q hq
  have hEA : ObsEq
      (run (BB6.Agent2EFirstAPacket.duration t q)
        (DRegularSource.sourceSection ⟨9*t+10,q,1⟩))
      (packet c.a c.q c.p fixedTail) := by
    simpa [BB6.Agent2EFirstAPacket.sourceStart,
      BB6.Agent2EFirstAPacket.packetOutput,c,fixedTail,
      BB6.Agent2EFirstAPacket.fixedTail] using hEA0
  have ha : c.a ≥ 4 := by simp [c]; omega
  have hp : c.p % 3 ≠ 2 := by
    dsimp [c]
    omega
  obtain ⟨T,a,q',b,hpacket⟩ :=
    BB6.Agent2PacketSafeReentry.all_safe_packets_regular c ha hp
  exact ⟨T,a,q',b,
    source_chain (BB6.Agent2EFirstAPacket.duration t q) T
      (DRegularSource.sourceSection ⟨9*t+10,q,1⟩)
      (packet c.a c.q c.p fixedTail)
      (BB6.Agent2BoundaryBZero.regularSection a q' b) hEA hpacket⟩

/-- The E/A exceptional family is closed for every q≥2. The q≡1
    residue is the A-terminal p=2 mod 3 case, handled by the universal
    original-source 110111 packet boundary. -/
theorem exceptional_EA_all_reentry (t q : Nat) (hq : 2 ≤ q) :
    ∃ T a q' b,
      ObsEq
        (run T (DRegularSource.sourceSection ⟨9*t+10,q,1⟩))
        (BB6.Agent2BoundaryBZero.regularSection a q' b) := by
  by_cases hclass : q % 3 ≠ 1
  · exact exceptional_EA_safe_reentry t q hq hclass
  · have hqmod : q % 3 = 1 := by omega
    let r : Nat := (2*q-2)/3
    let k : Nat := 8*t+6
    let c : BB6.Agent31PacketRank.Packet := ⟨24*t+21,0,2*q⟩
    have hEA0 := BB6.Agent2EFirstAPacket.exceptional_EA_packet t q hq
    have hEA : ObsEq
        (run (BB6.Agent2EFirstAPacket.duration t q)
          (DRegularSource.sourceSection ⟨9*t+10,q,1⟩))
        (packet c.a c.q c.p fixedTail) := by
      simpa [BB6.Agent2EFirstAPacket.sourceStart,
        BB6.Agent2EFirstAPacket.packetOutput,c,fixedTail,
        BB6.Agent2EFirstAPacket.fixedTail] using hEA0
    have hk : 3*k+3=24*t+21 := by dsimp [k]; omega
    have hr : 3*r+2=2*q := by dsimp [r]; omega
    have hshape : packet c.a c.q c.p fixedTail =
        BB6.Agent2AP2PacketBoundary.input k 0 r := by
      simp [c,k,r,BB6.Agent2AP2PacketBoundary.input,
        BB6.Agent2AP2PacketBoundary.fixedTail,
        packet,word,fixedTail,hk,hr]
    have hAP2 :=
      BB6.Agent2AP2PacketBoundary.a_p2_packet_reentry k 0 r
    let a : Nat :=
      2*(4*k+3+CryptidA.wordInc
        (BB6.Agent2AP2PacketBoundary.words 0 r))+5
    have hendpoint :
        BB6.Agent2AP2PacketBoundary.endpoint k 0 r =
          BB6.Agent2BoundaryBZero.regularSection a 3 3 := by
      simp [a,BB6.Agent2AP2PacketBoundary.endpoint,
        BB6.Agent2BoundaryBZero.regularSection]
    have hA2 : ObsEq
        (run (BB6.Agent2AP2PacketBoundary.sourceTime k 0 r)
          (packet c.a c.q c.p fixedTail))
        (BB6.Agent2BoundaryBZero.regularSection a 3 3) := by
      rw [hshape,hAP2,hendpoint]
      exact BB6.Padding.cfgEq_refl _
    exact ⟨BB6.Agent2EFirstAPacket.duration t q +
        BB6.Agent2AP2PacketBoundary.sourceTime k 0 r,
      a,3,3,
      source_chain (BB6.Agent2EFirstAPacket.duration t q)
        (BB6.Agent2AP2PacketBoundary.sourceTime k 0 r)
        (DRegularSource.sourceSection ⟨9*t+10,q,1⟩)
        (packet c.a c.q c.p fixedTail)
        (BB6.Agent2BoundaryBZero.regularSection a 3 3) hEA hA2⟩

/-- The second E/E exceptional family produces a packet with p=2q-3.
    For q not 1 modulo 3, its original-source orbit also returns to
    the regular section language after finitely many primitive steps. -/
theorem exceptional_EE_safe_reentry (u q : Nat) (hq : 3 ≤ q)
    (hclass : q % 3 ≠ 1) :
    ∃ T a q' b,
      ObsEq
        (run (BB6.Agent2E7SecondSafe.eTime u q +
          BB6.Agent2E7SecondSafe.middleTime u + T)
          (DRegularSource.sourceSection ⟨27*u+25,q,1⟩))
        (BB6.Agent2BoundaryBZero.regularSection a q' b) := by
  let c : BB6.Agent31PacketRank.Packet := ⟨192*u+161,2,2*q-3⟩
  have hEE0 := BB6.Agent2E7SecondSafe.exceptional_EE_packet u q hq
  have ha0 : 8*(24*u+19)+9=192*u+161 := by omega
  have hEE : ObsEq
      (run (BB6.Agent2E7SecondSafe.eTime u q +
        BB6.Agent2E7SecondSafe.middleTime u)
        (DRegularSource.sourceSection ⟨27*u+25,q,1⟩))
      (packet c.a c.q c.p fixedTail) := by
    simpa [BB6.Agent2E7SecondSafe.sourceStart,
      BB6.Agent2E7SecondSafe.secondOutput,c,fixedTail,ha0,
      packet,word,CryptidBoundary.packetThree,
      BB6.Agent2E7SecondSafe.suffix2,CryptidBoundary.oppairs] using hEE0
  have ha : c.a ≥ 4 := by simp [c]; omega
  have hp : c.p % 3 ≠ 2 := by
    dsimp [c]
    omega
  obtain ⟨T,a,q',b,hpacket⟩ :=
    BB6.Agent2PacketSafeReentry.all_safe_packets_regular c ha hp
  exact ⟨T,a,q',b,
    source_chain
      (BB6.Agent2E7SecondSafe.eTime u q +
        BB6.Agent2E7SecondSafe.middleTime u) T
      (DRegularSource.sourceSection ⟨27*u+25,q,1⟩)
      (packet c.a c.q c.p fixedTail)
      (BB6.Agent2BoundaryBZero.regularSection a q' b) hEE hpacket⟩

#print axioms exceptional_EA_safe_reentry
#print axioms exceptional_EA_all_reentry
/-- The complete E/E exceptional family is now reduced for every q≥3:
    it either returns to regular L, or reaches the canonical E2 marker packet.
    The q≡1 residue is handled by the source-connected p≡2 reduction. -/
theorem exceptional_EE_all_reentry_or_reset (u q : Nat) (hq : 3 ≤ q) :
    (∃ T a q' b,
      ObsEq
        (run T (DRegularSource.sourceSection ⟨27*u+25,q,1⟩))
        (BB6.Agent2BoundaryBZero.regularSection a q' b)) ∨
    (∃ T k q2,
      ObsEq
        (run T (DRegularSource.sourceSection ⟨27*u+25,q,1⟩))
        (packet (8*k+5) 0 (2*q2+6)
          BB6.Agent2PacketP2Reset.marker)) := by
  by_cases hclass : q % 3 ≠ 1
  · obtain ⟨T,a,q',b,h⟩ := exceptional_EE_safe_reentry u q hq hclass
    exact Or.inl ⟨T,a,q',b,h⟩
  · have hqmod : q % 3 = 1 := by omega
    let c : BB6.Agent31PacketRank.Packet := ⟨192*u+161,2,2*q-3⟩
    have hEE0 := BB6.Agent2E7SecondSafe.exceptional_EE_packet u q hq
    have ha0 : 8*(24*u+19)+9=192*u+161 := by omega
    have hEE : ObsEq
        (run (BB6.Agent2E7SecondSafe.eTime u q +
          BB6.Agent2E7SecondSafe.middleTime u)
          (DRegularSource.sourceSection ⟨27*u+25,q,1⟩))
        (packet c.a c.q c.p fixedTail) := by
      simpa [BB6.Agent2E7SecondSafe.sourceStart,
        BB6.Agent2E7SecondSafe.secondOutput,c,fixedTail,ha0,
        packet,word,CryptidBoundary.packetThree,
        BB6.Agent2E7SecondSafe.suffix2,CryptidBoundary.oppairs] using hEE0
    have ha : c.a ≥ 4 := by simp [c]; omega
    have hp : c.p % 3 = 2 := by
      dsimp [c]
      omega
    rcases BB6.Agent2PacketP2ReentryOrE.p2_packet_reentry_or_reset
        c ha hp with hL | hR
    · rcases hL with ⟨T,a,q',b,hEq⟩
      have hP2 : ObsEq (run T (packet c.a c.q c.p fixedTail))
          (BB6.Agent2BoundaryBZero.regularSection a q' b) := by
        rw [hEq]
        exact BB6.Padding.cfgEq_refl _
      exact Or.inl ⟨BB6.Agent2E7SecondSafe.eTime u q +
          BB6.Agent2E7SecondSafe.middleTime u + T,
        a,q',b,
        source_chain
          (BB6.Agent2E7SecondSafe.eTime u q +
            BB6.Agent2E7SecondSafe.middleTime u) T
          (DRegularSource.sourceSection ⟨27*u+25,q,1⟩)
          (packet c.a c.q c.p fixedTail)
          (BB6.Agent2BoundaryBZero.regularSection a q' b) hEE hP2⟩
    · rcases hR with ⟨T,k,q2,hEq⟩
      have hP2 : ObsEq (run T (packet c.a c.q c.p fixedTail))
          (packet (8*k+5) 0 (2*q2+6)
            BB6.Agent2PacketP2Reset.marker) := by
        rw [hEq]
        exact BB6.Padding.cfgEq_refl _
      exact Or.inr ⟨BB6.Agent2E7SecondSafe.eTime u q +
          BB6.Agent2E7SecondSafe.middleTime u + T,
        k,q2,
        source_chain
          (BB6.Agent2E7SecondSafe.eTime u q +
            BB6.Agent2E7SecondSafe.middleTime u) T
          (DRegularSource.sourceSection ⟨27*u+25,q,1⟩)
          (packet c.a c.q c.p fixedTail)
          (packet (8*k+5) 0 (2*q2+6)
            BB6.Agent2PacketP2Reset.marker) hEE hP2⟩

#print axioms exceptional_EE_safe_reentry
#print axioms exceptional_EE_all_reentry_or_reset

end BB6.Agent2ExceptionalEPacketClosure
