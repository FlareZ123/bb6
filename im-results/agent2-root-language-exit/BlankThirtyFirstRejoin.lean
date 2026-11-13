import Lean.Elab.Tactic.Omega
import Seed31FirstStopCertificate
import EFirstAPacket
import AOnePacketBoundarySource
import DRegularFast

set_option maxHeartbeats 100000000
set_option maxRecDepth 55000

namespace BB6.Agent2ThirtyFirstRejoin

open CryptidBoundary BB6.BoundaryPadding BB6.Padding
open BB6.Agent31PacketSource
open BB6.Agent2ThirtiethRoot
open BB6.Agent2ThirtyFirstCertificate
open BB6.Agent2ThirtyFirstProbe

/-- The exact first exceptional state returned by the Seed31 probe. -/
def terminal12267 : DRegular.L := firstExceptionFromSeed31.2

/-- The quotient parameter in the q=8 E/A source shape. -/
def t31 : Nat := (terminal12267.a-10)/9

theorem t31_spec :
    terminal12267.a = 9*t31+10 ∧
      t31 % 27 = 2 ∧
      terminal12267.q = 8 ∧
      terminal12267.b = 1 := by
  rcases firstExceptionFromSeed31_shape with ⟨t,ha,ht,hq,hb⟩
  have htEq : t = t31 := by
    dsimp [t31,terminal12267]
    rw [ha]
    omega
  subst t
  exact ⟨by simpa [terminal12267] using ha, ht,
    by simpa [terminal12267] using hq,
    by simpa [terminal12267] using hb⟩

theorem terminal12267_shape :
    terminal12267 = ⟨9*t31+10,8,1⟩ := by
  cases terminal12267 with
  | mk a q b =>
      rcases t31_spec with ⟨ha,ht,hq,hb⟩
      simp_all

/-- The q=8 E-first packet has p=16=3*5+1. -/
def packet31 : BB6.Agent31PacketRank.Packet :=
  ⟨24*t31+21,0,16⟩

def k31 : Nat := (packet31.a-3)/3
def r31 : Nat := (packet31.p-1)/3

def seed32 : DRegular.L :=
  ⟨BB6.Agent2AOneBoundary.aUnary k31 0 r31,0,0⟩

def aOneTime31 : Nat :=
  BB6.Agent2AOneBoundary.aCost k31 0 r31

theorem packet31_a_eq : packet31.a = 3*k31+3 := by
  have ha : packet31.a ≥ 3 := by simp [packet31]; omega
  dsimp [k31]
  omega

theorem packet31_p_eq : packet31.p = 3*r31+1 := by
  dsimp [r31,packet31]
  omega

theorem seed32_a_formula : seed32.a = 64*t31+117 := by
  dsimp [seed32,k31,r31,packet31,
    BB6.Agent2AOneBoundary.aUnary,BB6.Agent2AOneBoundary.aWords]
  simp [CryptidA.wordInc]
  omega

theorem seed32_canon : DRegular.Canon seed32 := by
  constructor
  · rw [seed32_a_formula]
    omega
  · right
    rfl

def exception31Time (T22 Tnorm24 Tnorm27 : Nat) : Nat :=
  reentry30Time T22 Tnorm24 Tnorm27 +
    DRegular.accumulated firstExceptionFromSeed31.1 seed31

def reentry31Time (T22 Tnorm24 Tnorm27 : Nat) : Nat :=
  exception31Time T22 Tnorm24 Tnorm27 +
    (BB6.Agent2EFirstAPacket.duration t31 8 + aOneTime31)

/-- The exact first-stop certificate extends the blank root through the
    12,267-step regular segment to the q=8 exceptional source section. -/
theorem blank_thirty_first_exception :
    ∃ T22 Tnorm24 Tnorm27,
      ObsEq (run (exception31Time T22 Tnorm24 Tnorm27) blank)
        (DRegularSource.sourceSection terminal12267) := by
  obtain ⟨T22,Tnorm24,Tnorm27,h31⟩ :=
    blank_thirty_first_prefix firstExceptionFromSeed31_bound
  exact ⟨T22,Tnorm24,Tnorm27,by
    simpa [exception31Time,terminal12267] using h31⟩

/-- The actual q=8 first exception returns through EFirstAPacket and the
    original A-one boundary to a new pure-unary regular seed. -/
theorem blank_thirty_first_reentry :
    ∃ T22 Tnorm24 Tnorm27,
      ObsEq (run (reentry31Time T22 Tnorm24 Tnorm27) blank)
        (DRegularSource.sourceSection seed32) := by
  obtain ⟨T22,Tnorm24,Tnorm27,h31⟩ := blank_thirty_first_exception
  have hEA0 :=
    BB6.Agent2EFirstAPacket.exceptional_EA_packet t31 8 (by omega)
  have hEA : ObsEq
      (run (BB6.Agent2EFirstAPacket.duration t31 8)
        (DRegularSource.sourceSection terminal12267))
      (packet packet31.a packet31.q packet31.p
        BB6.Agent2EFirstAPacket.fixedTail) := by
    simpa [BB6.Agent2EFirstAPacket.duration,
      BB6.Agent2EFirstAPacket.sourceStart,
      BB6.Agent2EFirstAPacket.packetOutput,
      packet31,BB6.Agent2EFirstAPacket.fixedTail,
      terminal12267_shape] using hEA0
  have htarget :
      (⟨[],false,List.replicate seed32.a true,5⟩ : Cfg) =
        DRegularSource.sourceSection seed32 := by
    have hreg :=
      BB6.Agent2TwentyThirdRoot.regularSection_sourceSection
        seed32.a 0 0 (by rw [seed32_a_formula]; omega)
    simpa [seed32,BB6.Agent2BoundaryBZero.regularSection,
      CryptidBoundary.oppairs] using hreg
  have hA0 :=
    BB6.Agent2AOneBoundary.a_p1_boundary k31 0 r31
  have hA : ObsEq
      (run aOneTime31
        (packet packet31.a packet31.q packet31.p
          BB6.Agent2EFirstAPacket.fixedTail))
      (DRegularSource.sourceSection seed32) := by
    have hshape :
        packet packet31.a packet31.q packet31.p
          BB6.Agent2EFirstAPacket.fixedTail =
        packet (3*k31+3) 0 (3*r31+1)
          BB6.Agent2EFirstAPacket.fixedTail := by
      rw [packet31_a_eq,packet31_p_eq]
      rfl
    rw [hshape]
    simpa [aOneTime31,seed32,htarget,
      BB6.Agent2EFirstAPacket.fixedTail] using hA0
  have hroot : ObsEq
      (run (BB6.Agent2EFirstAPacket.duration t31 8 + aOneTime31)
        (DRegularSource.sourceSection terminal12267))
      (DRegularSource.sourceSection seed32) := by
    exact source_chain (BB6.Agent2EFirstAPacket.duration t31 8)
      aOneTime31
      (DRegularSource.sourceSection terminal12267)
      (packet packet31.a packet31.q packet31.p
        BB6.Agent2EFirstAPacket.fixedTail)
      (DRegularSource.sourceSection seed32) hEA hA
  exact ⟨T22,Tnorm24,Tnorm27,
    source_chain (exception31Time T22 Tnorm24 Tnorm27)
      (BB6.Agent2EFirstAPacket.duration t31 8 + aOneTime31)
      blank
      (DRegularSource.sourceSection terminal12267)
      (DRegularSource.sourceSection seed32) h31 hroot⟩

#print axioms firstExceptionFromSeed31_signature
#print axioms firstExceptionFromSeed31_sound_actual
#print axioms blank_thirty_first_exception
#print axioms blank_thirty_first_reentry

end BB6.Agent2ThirtyFirstRejoin
