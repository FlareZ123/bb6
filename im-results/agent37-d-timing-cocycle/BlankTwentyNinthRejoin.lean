import Lean.Elab.Tactic.Omega
import BlankTwentyEighthRejoin
import EFirstAPacket
import PacketZeroBoundarySource
import DRegularFast

set_option maxHeartbeats 100000000
set_option maxRecDepth 55000

namespace BB6.Agent2TwentyNinthRoot

open CryptidBoundary BB6.BoundaryPadding BB6.Padding
open BB6.Agent31PacketSource

def seed29 : DRegular.L := BB6.Agent2TwentyEighthRoot.seed29

def terminal6443 : DRegular.L :=
  (BB6.DRegularFast.fastRun 6443 seed29).getD ⟨9,0,0⟩

def t29 : Nat := (terminal6443.a-10)/9

theorem terminal6443_certificate :
    DRegular.run 6443 seed29 = some ⟨9*t29+10,6,1⟩ ∧
      t29 % 27 = 22 := by
  have hcanon : DRegular.Canon seed29 := by
    constructor
    · dsimp [seed29, BB6.Agent2TwentyEighthRoot.seed29]
      omega
    · left
      norm_num [seed29, BB6.Agent2TwentyEighthRoot.seed29]
  rw [BB6.DRegularFast.fastRun_correct 6443 seed29 hcanon]
  decide

theorem terminal6443_exact :
    DRegular.run 6443 seed29 = some ⟨9*t29+10,6,1⟩ :=
  terminal6443_certificate.1

theorem t29_mod27 : t29 % 27 = 22 :=
  terminal6443_certificate.2

def exception29Time (T22 Tnorm24 Tnorm27 : Nat) : Nat :=
  BB6.Agent2TwentyEighthRoot.reentry28Time T22 Tnorm24 Tnorm27 +
    DRegular.accumulated 6443 seed29

/-- Extend the source-certified twenty-eighth reentry through the next
    exact D-regular segment. -/
theorem blank_twenty_ninth_exception_from (T22 Tnorm24 Tnorm27 : Nat)
    (h28 : ObsEq
      (run (BB6.Agent2TwentyEighthRoot.reentry28Time
        T22 Tnorm24 Tnorm27) blank)
      (DRegularSource.sourceSection seed29)) :
    ObsEq (run (exception29Time T22 Tnorm24 Tnorm27) blank)
      (DRegularSource.sourceSection ⟨9*t29+10,6,1⟩) := by
  apply BB6.Agent25RootChain.extend_regular blank
    (BB6.Agent2TwentyEighthRoot.reentry28Time T22 Tnorm24 Tnorm27)
    6443 seed29 ⟨9*t29+10,6,1⟩
  · constructor
    · dsimp [seed29, BB6.Agent2TwentyEighthRoot.seed29]
      omega
    · left
      norm_num [seed29, BB6.Agent2TwentyEighthRoot.seed29]
  · exact terminal6443_exact
  · exact h28

theorem blank_twenty_ninth_exception :
    ∃ T22 Tnorm24 Tnorm27,
      ObsEq (run (exception29Time T22 Tnorm24 Tnorm27) blank)
        (DRegularSource.sourceSection ⟨9*t29+10,6,1⟩) := by
  obtain ⟨T22,Tnorm24,Tnorm27,h28⟩ :=
    BB6.Agent2TwentyEighthRoot.blank_twenty_eighth_reentry
  exact ⟨T22,Tnorm24,Tnorm27,
    blank_twenty_ninth_exception_from T22 Tnorm24 Tnorm27 h28⟩

def packet29 : BB6.Agent31PacketRank.Packet :=
  ⟨24*t29+21,0,12⟩

def k29 : Nat := (packet29.a-3)/3
def r29 : Nat := packet29.p/3

def seed30 : DRegular.L :=
  ⟨BB6.Agent2PacketZeroBoundary.aZeroUnary k29 0 r29,0,0⟩

def aZeroTime29 : Nat :=
  BB6.Agent2PacketZeroBoundary.aZeroCost k29 0 r29

def reentry29Time (T22 Tnorm24 Tnorm27 : Nat) : Nat :=
  exception29Time T22 Tnorm24 Tnorm27 +
    (BB6.Agent2EFirstAPacket.duration t29 6 + aZeroTime29)

/-- The q=6 E-first packet has p=12=3*4; the original A-zero
    boundary returns it to the pure-unary seed30. -/
theorem blank_twenty_ninth_reentry :
    ∃ T22 Tnorm24 Tnorm27,
      ObsEq (run (reentry29Time T22 Tnorm24 Tnorm27) blank)
        (DRegularSource.sourceSection seed30) := by
  obtain ⟨T22,Tnorm24,Tnorm27,h29⟩ := blank_twenty_ninth_exception
  have hEA0 :=
    BB6.Agent2EFirstAPacket.exceptional_EA_packet t29 6 (by omega)
  have hEA : ObsEq
      (run (BB6.Agent2EFirstAPacket.duration t29 6)
        (DRegularSource.sourceSection ⟨9*t29+10,6,1⟩))
      (packet packet29.a packet29.q packet29.p
        BB6.Agent2EFirstAPacket.fixedTail) := by
    simpa [BB6.Agent2EFirstAPacket.duration,
      BB6.Agent2EFirstAPacket.sourceStart,
      BB6.Agent2EFirstAPacket.packetOutput,
      packet29, BB6.Agent2EFirstAPacket.fixedTail] using hEA0
  have htarget :
      (⟨[],false,List.replicate seed30.a true,5⟩ : Cfg) =
        DRegularSource.sourceSection seed30 := by
    have hreg :=
      BB6.Agent2TwentyThirdRoot.regularSection_sourceSection
        seed30.a 0 0 (by
          dsimp [seed30,BB6.Agent2PacketZeroBoundary.aZeroUnary]
          omega)
    simpa [seed30,BB6.Agent2BoundaryBZero.regularSection,
      CryptidBoundary.oppairs] using hreg
  have hA0 :=
    BB6.Agent2PacketZeroBoundary.a_zero_boundary k29 0 r29
  have hA : ObsEq
      (run aZeroTime29
        (packet packet29.a packet29.q packet29.p
          BB6.Agent2EFirstAPacket.fixedTail))
      (DRegularSource.sourceSection seed30) := by
    have hshape :
        packet packet29.a packet29.q packet29.p
          BB6.Agent2EFirstAPacket.fixedTail =
        packet (3*k29+3) 0 (3*r29)
          BB6.Agent2EFirstAPacket.fixedTail := by
      have ha : packet29.a = 3*k29+3 := by
        have hamin : packet29.a ≥ 3 := by simp [packet29]; omega
        dsimp [k29]
        omega
      have hp : packet29.p = 3*r29 := by
        simp [r29,packet29]
      rw [ha,hp]
    rw [hshape]
    rw [BB6.Agent2PacketZeroBoundary.a_zero_boundary k29 0 r29]
    rw [htarget]
    exact BB6.Padding.cfgEq_refl _
  have hroot : ObsEq
      (run (BB6.Agent2EFirstAPacket.duration t29 6 + aZeroTime29)
        (DRegularSource.sourceSection ⟨9*t29+10,6,1⟩))
      (DRegularSource.sourceSection seed30) := by
    exact source_chain (BB6.Agent2EFirstAPacket.duration t29 6)
      aZeroTime29
      (DRegularSource.sourceSection ⟨9*t29+10,6,1⟩)
      (packet packet29.a packet29.q packet29.p
        BB6.Agent2EFirstAPacket.fixedTail)
      (DRegularSource.sourceSection seed30) hEA hA
  exact ⟨T22,Tnorm24,Tnorm27,
    source_chain (exception29Time T22 Tnorm24 Tnorm27)
      (BB6.Agent2EFirstAPacket.duration t29 6 + aZeroTime29)
      blank
      (DRegularSource.sourceSection ⟨9*t29+10,6,1⟩)
      (DRegularSource.sourceSection seed30) h29 hroot⟩

#print axioms terminal6443_exact
#print axioms t29_mod27
#print axioms blank_twenty_ninth_exception
#print axioms blank_twenty_ninth_reentry

end BB6.Agent2TwentyNinthRoot
