import Lean.Elab.Tactic.Omega
import EFirstAPacket
import ExceptionalE7SecondSafe
import PacketSafeReentry

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
#print axioms exceptional_EE_safe_reentry

end BB6.Agent2ExceptionalEPacketClosure
