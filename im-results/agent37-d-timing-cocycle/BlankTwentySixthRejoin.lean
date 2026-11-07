import Lean.Elab.Tactic.Omega
import BlankTwentyFifthRejoin
import EFirstAPacket
import AOnePacketBoundarySource

set_option maxHeartbeats 100000000
set_option maxRecDepth 55000

namespace BB6.Agent2TwentySixthRoot

open CryptidBoundary BB6.BoundaryPadding BB6.Padding
open BB6.Agent31PacketSource

def seed26 : DRegular.L :=
  ⟨64*BB6.Agent2TwentyFifthRoot.t25+33,1,5⟩

def terminal8516 : DRegular.L :=
  (DRegular.run 8516 seed26).getD ⟨9,0,0⟩

def t26 : Nat := (terminal8516.a-10)/9

theorem terminal8516_certificate :
    DRegular.run 8516 seed26 = some ⟨9*t26+10,8,1⟩ ∧
      t26 % 27 = 25 := by
  decide

theorem terminal8516_exact :
    DRegular.run 8516 seed26 = some ⟨9*t26+10,8,1⟩ :=
  terminal8516_certificate.1

theorem t26_mod27 : t26 % 27 = 25 :=
  terminal8516_certificate.2

def exception26Time : Nat :=
  BB6.Agent2TwentyFifthRoot.reentry25Time +
    DRegular.accumulated 8516 seed26

/-- The twenty-sixth exceptional input is reached from the blank tape. -/
theorem blank_twenty_sixth_exception :
    ObsEq (run exception26Time blank)
      (DRegularSource.sourceSection ⟨9*t26+10,8,1⟩) := by
  apply BB6.Agent25RootChain.extend_regular blank
    BB6.Agent2TwentyFifthRoot.reentry25Time
    8516 seed26 ⟨9*t26+10,8,1⟩
  · constructor
    · change 64*BB6.Agent2TwentyFifthRoot.t25+33 ≥ 2
      omega
    · left
      change (1 : Nat) ≠ 0
      omega
  · exact terminal8516_exact
  · exact BB6.Agent2TwentyFifthRoot.blank_twenty_fifth_reentry

def packet26 : BB6.Agent31PacketRank.Packet :=
  ⟨24*t26+21,0,16⟩

def k26 : Nat := (packet26.a-3)/3
def r26 : Nat := (packet26.p-1)/3

def seed27 : DRegular.L :=
  ⟨BB6.Agent2AOneBoundary.aUnary k26 0 r26,0,0⟩

def aOneTime26 : Nat :=
  BB6.Agent2AOneBoundary.aCost k26 0 r26

theorem packet26_a_eq : packet26.a = 3*k26+3 := by
  have ha : packet26.a ≥ 3 := by simp [packet26]; omega
  dsimp [k26]
  omega

theorem packet26_p_eq : packet26.p = 3*r26+1 := by
  dsimp [r26,packet26]
  omega

/-- The E-first return for a=9*t+10 reaches an A,p=1 packet when q=8.
    The original A-code source theorem then returns to a pure-unary
    regular section, extending the blank-root orbit through episode 26. -/
theorem blank_twenty_sixth_reentry :
    ObsEq
      (run (exception26Time +
        (BB6.Agent2EFirstAPacket.duration t26 8 + aOneTime26)) blank)
      (DRegularSource.sourceSection seed27) := by
  have hE0 :=
    BB6.Agent2EFirstAPacket.exceptional_EA_packet t26 8 (by omega)
  have hE :
      ObsEq
        (run (BB6.Agent2EFirstAPacket.duration t26 8)
          (DRegularSource.sourceSection ⟨9*t26+10,8,1⟩))
        (packet packet26.a packet26.q packet26.p
          BB6.Agent2EFirstAPacket.fixedTail) := by
    simpa [BB6.Agent2EFirstAPacket.duration,
      BB6.Agent2EFirstAPacket.sourceStart,
      BB6.Agent2EFirstAPacket.packetOutput,
      packet26, BB6.Agent2EFirstAPacket.fixedTail] using hE0
  have htarget :
      (⟨[],false,List.replicate seed27.a true,5⟩ : Cfg) =
        DRegularSource.sourceSection seed27 := by
    have hreg :=
      BB6.Agent2TwentyThirdRoot.regularSection_sourceSection
        seed27.a 0 0 (by dsimp [seed27,BB6.Agent2AOneBoundary.aUnary]; omega)
    simpa [seed27,BB6.Agent2BoundaryBZero.regularSection,
      CryptidBoundary.oppairs] using hreg
  have hA0 :=
    BB6.Agent2AOneBoundary.a_p1_boundary k26 0 r26
  have hA : ObsEq
      (run aOneTime26
        (packet packet26.a packet26.q packet26.p
          BB6.Agent2EFirstAPacket.fixedTail))
      (DRegularSource.sourceSection seed27) := by
    have hshape :
        packet packet26.a packet26.q packet26.p
          BB6.Agent2EFirstAPacket.fixedTail =
        packet (3*k26+3) 0 (3*r26+1)
          BB6.Agent2EFirstAPacket.fixedTail := by
      rw [packet26_a_eq,packet26_p_eq]
      rfl
    rw [hshape]
    simpa [aOneTime26,seed27,htarget,BB6.Agent2EFirstAPacket.fixedTail] using hA0
  have hroot :
      ObsEq
        (run (BB6.Agent2EFirstAPacket.duration t26 8 + aOneTime26)
          (DRegularSource.sourceSection ⟨9*t26+10,8,1⟩))
        (DRegularSource.sourceSection seed27) := by
    exact source_chain
      (BB6.Agent2EFirstAPacket.duration t26 8) aOneTime26
      (DRegularSource.sourceSection ⟨9*t26+10,8,1⟩)
      (packet packet26.a packet26.q packet26.p
        BB6.Agent2EFirstAPacket.fixedTail)
      (DRegularSource.sourceSection seed27) hE hA
  exact source_chain exception26Time
    (BB6.Agent2EFirstAPacket.duration t26 8 + aOneTime26)
    blank
    (DRegularSource.sourceSection ⟨9*t26+10,8,1⟩)
    (DRegularSource.sourceSection seed27)
    blank_twenty_sixth_exception hroot

#print axioms terminal8516_exact
#print axioms t26_mod27
#print axioms blank_twenty_sixth_exception
#print axioms blank_twenty_sixth_reentry

end BB6.Agent2TwentySixthRoot
