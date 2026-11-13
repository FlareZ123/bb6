import Lean.Elab.Tactic.Omega
import BlankTwentyNinthRejoin
import EFirstAPacket
import AOnePacketBoundarySource
import DRegularFast

set_option maxHeartbeats 100000000
set_option maxRecDepth 55000

namespace BB6.Agent2ThirtiethRoot

open CryptidBoundary BB6.BoundaryPadding BB6.Padding
open BB6.Agent31PacketSource

def seed30 : DRegular.L := BB6.Agent2TwentyNinthRoot.seed30

def terminal2613 : DRegular.L :=
  (BB6.DRegularFast.fastRun 2613 seed30).getD ⟨9,0,0⟩

def t30 : Nat := (terminal2613.a-10)/9

theorem terminal2613_certificate :
    DRegular.run 2613 seed30 = some ⟨9*t30+10,8,1⟩ ∧
      t30 % 27 = 22 := by
  have hcanon : DRegular.Canon seed30 := by
    constructor
    · dsimp [seed30, BB6.Agent2TwentyNinthRoot.seed30,
        BB6.Agent2PacketZeroBoundary.aZeroUnary]
      omega
    · right
      rfl
  rw [BB6.DRegularFast.fastRun_correct 2613 seed30 hcanon]
  decide

theorem terminal2613_exact :
    DRegular.run 2613 seed30 = some ⟨9*t30+10,8,1⟩ :=
  terminal2613_certificate.1

theorem t30_mod27 : t30 % 27 = 22 :=
  terminal2613_certificate.2

def exception30Time (T22 Tnorm24 Tnorm27 : Nat) : Nat :=
  BB6.Agent2TwentyNinthRoot.reentry29Time T22 Tnorm24 Tnorm27 +
    DRegular.accumulated 2613 seed30

/-- Extend the source-certified twenty-ninth reentry through the next
    exact D-regular segment. -/
theorem blank_thirtieth_exception_from (T22 Tnorm24 Tnorm27 : Nat)
    (h29 : ObsEq
      (run (BB6.Agent2TwentyNinthRoot.reentry29Time
        T22 Tnorm24 Tnorm27) blank)
      (DRegularSource.sourceSection seed30)) :
    ObsEq (run (exception30Time T22 Tnorm24 Tnorm27) blank)
      (DRegularSource.sourceSection ⟨9*t30+10,8,1⟩) := by
  apply BB6.Agent25RootChain.extend_regular blank
    (BB6.Agent2TwentyNinthRoot.reentry29Time T22 Tnorm24 Tnorm27)
    2613 seed30 ⟨9*t30+10,8,1⟩
  · constructor
    · dsimp [seed30, BB6.Agent2TwentyNinthRoot.seed30,
        BB6.Agent2PacketZeroBoundary.aZeroUnary]
      omega
    · right
      rfl
  · exact terminal2613_exact
  · exact h29

theorem blank_thirtieth_exception :
    ∃ T22 Tnorm24 Tnorm27,
      ObsEq (run (exception30Time T22 Tnorm24 Tnorm27) blank)
        (DRegularSource.sourceSection ⟨9*t30+10,8,1⟩) := by
  obtain ⟨T22,Tnorm24,Tnorm27,h29⟩ :=
    BB6.Agent2TwentyNinthRoot.blank_twenty_ninth_reentry
  exact ⟨T22,Tnorm24,Tnorm27,
    blank_thirtieth_exception_from T22 Tnorm24 Tnorm27 h29⟩

def packet30 : BB6.Agent31PacketRank.Packet :=
  ⟨24*t30+21,0,16⟩

def k30 : Nat := (packet30.a-3)/3
def r30 : Nat := (packet30.p-1)/3

def seed31 : DRegular.L :=
  ⟨BB6.Agent2AOneBoundary.aUnary k30 0 r30,0,0⟩

def aOneTime30 : Nat :=
  BB6.Agent2AOneBoundary.aCost k30 0 r30

theorem packet30_a_eq : packet30.a = 3*k30+3 := by
  have ha : packet30.a ≥ 3 := by simp [packet30]; omega
  dsimp [k30]
  omega

theorem packet30_p_eq : packet30.p = 3*r30+1 := by
  dsimp [r30,packet30]
  omega

def reentry30Time (T22 Tnorm24 Tnorm27 : Nat) : Nat :=
  exception30Time T22 Tnorm24 Tnorm27 +
    (BB6.Agent2EFirstAPacket.duration t30 8 + aOneTime30)

/-- The q=8 E-first packet has p=16=3*5+1; the original A-one
    boundary returns it to the pure-unary seed31. -/
theorem blank_thirtieth_reentry :
    ∃ T22 Tnorm24 Tnorm27,
      ObsEq (run (reentry30Time T22 Tnorm24 Tnorm27) blank)
        (DRegularSource.sourceSection seed31) := by
  obtain ⟨T22,Tnorm24,Tnorm27,h30⟩ := blank_thirtieth_exception
  have hEA0 :=
    BB6.Agent2EFirstAPacket.exceptional_EA_packet t30 8 (by omega)
  have hEA : ObsEq
      (run (BB6.Agent2EFirstAPacket.duration t30 8)
        (DRegularSource.sourceSection ⟨9*t30+10,8,1⟩))
      (packet packet30.a packet30.q packet30.p
        BB6.Agent2EFirstAPacket.fixedTail) := by
    simpa [BB6.Agent2EFirstAPacket.duration,
      BB6.Agent2EFirstAPacket.sourceStart,
      BB6.Agent2EFirstAPacket.packetOutput,
      packet30, BB6.Agent2EFirstAPacket.fixedTail] using hEA0
  have htarget :
      (⟨[],false,List.replicate seed31.a true,5⟩ : Cfg) =
        DRegularSource.sourceSection seed31 := by
    have hreg :=
      BB6.Agent2TwentyThirdRoot.regularSection_sourceSection
        seed31.a 0 0 (by
          dsimp [seed31,BB6.Agent2AOneBoundary.aUnary]
          omega)
    simpa [seed31,BB6.Agent2BoundaryBZero.regularSection,
      CryptidBoundary.oppairs] using hreg
  have hA0 :=
    BB6.Agent2AOneBoundary.a_p1_boundary k30 0 r30
  have hA : ObsEq
      (run aOneTime30
        (packet packet30.a packet30.q packet30.p
          BB6.Agent2EFirstAPacket.fixedTail))
      (DRegularSource.sourceSection seed31) := by
    have hshape :
        packet packet30.a packet30.q packet30.p
          BB6.Agent2EFirstAPacket.fixedTail =
        packet (3*k30+3) 0 (3*r30+1)
          BB6.Agent2EFirstAPacket.fixedTail := by
      rw [packet30_a_eq,packet30_p_eq]
      rfl
    rw [hshape]
    simpa [aOneTime30,seed31,htarget,
      BB6.Agent2EFirstAPacket.fixedTail] using hA0
  have hroot : ObsEq
      (run (BB6.Agent2EFirstAPacket.duration t30 8 + aOneTime30)
        (DRegularSource.sourceSection ⟨9*t30+10,8,1⟩))
      (DRegularSource.sourceSection seed31) := by
    exact source_chain (BB6.Agent2EFirstAPacket.duration t30 8)
      aOneTime30
      (DRegularSource.sourceSection ⟨9*t30+10,8,1⟩)
      (packet packet30.a packet30.q packet30.p
        BB6.Agent2EFirstAPacket.fixedTail)
      (DRegularSource.sourceSection seed31) hEA hA
  exact ⟨T22,Tnorm24,Tnorm27,
    source_chain (exception30Time T22 Tnorm24 Tnorm27)
      (BB6.Agent2EFirstAPacket.duration t30 8 + aOneTime30)
      blank
      (DRegularSource.sourceSection ⟨9*t30+10,8,1⟩)
      (DRegularSource.sourceSection seed31) h30 hroot⟩

#print axioms terminal2613_exact
#print axioms t30_mod27
#print axioms blank_thirtieth_exception
#print axioms blank_thirtieth_reentry

end BB6.Agent2ThirtiethRoot
