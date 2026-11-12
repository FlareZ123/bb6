import Lean.Elab.Tactic.Omega
import BlankTwentySixthRejoin
import ExceptionalE7SecondSafe
import PacketNormalizeSource
import PacketZeroBoundarySource
import DRegularFast

set_option maxHeartbeats 100000000
set_option maxRecDepth 55000

namespace BB6.Agent2TwentySeventhRoot

open CryptidBoundary BB6.BoundaryPadding BB6.Padding
open BB6.Agent31PacketSource

/-- The pure-unary regular seed produced by the twenty-sixth source return. -/
def seed27 : DRegular.L := BB6.Agent2TwentySixthRoot.seed27

/-- Exact endpoint after 1,684 regular sections from the twenty-sixth reentry. -/
def terminal1684 : DRegular.L :=
  (BB6.DRegularFast.fastRun 1684 seed27).getD ⟨9,0,0⟩

def t27 : Nat := (terminal1684.a-7)/9

theorem terminal1684_certificate :
    DRegular.run 1684 seed27 = some ⟨9*t27+7,9,1⟩ ∧
      t27 % 27 = 8 := by
  have hcanon : DRegular.Canon seed27 := by
    constructor
    · dsimp [seed27, BB6.Agent2TwentySixthRoot.seed27,
        BB6.Agent2AOneBoundary.aUnary]
      omega
    · right
      rfl
  rw [BB6.DRegularFast.fastRun_correct 1684 seed27 hcanon]
  decide

theorem terminal1684_exact :
    DRegular.run 1684 seed27 = some ⟨9*t27+7,9,1⟩ :=
  terminal1684_certificate.1

theorem t27_mod27 : t27 % 27 = 8 :=
  terminal1684_certificate.2

def u27 : Nat := (t27-2)/3

theorem t27_eq_three_u27_add_two : t27 = 3*u27+2 := by
  have h := t27_mod27
  dsimp [u27]
  omega

def exception27Time (T22 Tnorm24 : Nat) : Nat :=
  BB6.Agent2TwentySixthRoot.reentry26Time T22 Tnorm24 +
    DRegular.accumulated 1684 seed27

/-- Extend any witnessed twenty-sixth reentry through the next exact
    D-regular run. -/
theorem blank_twenty_seventh_exception_from (T22 Tnorm24 : Nat)
    (h26 : ObsEq
      (run (BB6.Agent2TwentySixthRoot.reentry26Time T22 Tnorm24) blank)
      (DRegularSource.sourceSection seed27)) :
    ObsEq (run (exception27Time T22 Tnorm24) blank)
      (DRegularSource.sourceSection ⟨9*t27+7,9,1⟩) := by
  apply BB6.Agent25RootChain.extend_regular blank
    (BB6.Agent2TwentySixthRoot.reentry26Time T22 Tnorm24)
    1684 seed27 ⟨9*t27+7,9,1⟩
  · constructor
    · dsimp [seed27, BB6.Agent2TwentySixthRoot.seed27,
        BB6.Agent2AOneBoundary.aUnary]
      omega
    · right
      rfl
  · exact terminal1684_exact
  · exact h26

theorem blank_twenty_seventh_exception :
    ∃ T22 Tnorm24,
      ObsEq (run (exception27Time T22 Tnorm24) blank)
        (DRegularSource.sourceSection ⟨9*t27+7,9,1⟩) := by
  obtain ⟨T22,Tnorm24,h26⟩ :=
    BB6.Agent2TwentySixthRoot.blank_twenty_sixth_reentry
  exact ⟨T22,Tnorm24,
    blank_twenty_seventh_exception_from T22 Tnorm24 h26⟩

def packet27 : BB6.Agent31PacketRank.Packet :=
  ⟨192*u27+161,2,15⟩

def normalized27 : BB6.Agent31PacketRank.Packet :=
  (BB6.Agent31PacketRank.normalizeWithCount packet27).2

theorem normalized27_certificate :
    normalized27.a % 3 = 0 ∧
      normalized27.q = 1 ∧ normalized27.p = 15 := by
  decide

def k27 : Nat := (normalized27.a-3)/3
def r27 : Nat := normalized27.p/3

theorem normalized27_a_eq : normalized27.a = 3*k27+3 := by
  have hamin : normalized27.a ≥ 3 := by
    have h := BB6.Agent2PacketSafe.normalize_amin packet27
      (by simp [packet27]; omega)
    omega
  dsimp [k27]
  omega

theorem normalized27_p_eq : normalized27.p = 3*r27 := by
  have hp := normalized27_certificate.2.2
  simp [r27,hp]

/-- The one-edge B normalization leaves an A,p=15 terminal; its
    original-source A-code boundary returns to this pure-unary seed. -/
def seed28 : DRegular.L :=
  ⟨BB6.Agent2PacketZeroBoundary.aZeroUnary k27 normalized27.q r27,0,0⟩

def zeroBoundary27Time : Nat :=
  BB6.Agent2PacketZeroBoundary.aZeroCost k27 normalized27.q r27

def fixedTail : List Bool := false :: List.replicate 6 true

def reentry27Time (T22 Tnorm24 Tnorm27 : Nat) : Nat :=
  exception27Time T22 Tnorm24 +
    (BB6.Agent2E7SecondSafe.eTime u27 9 +
      BB6.Agent2E7SecondSafe.middleTime u27 +
      (Tnorm27 + zeroBoundary27Time))

private theorem secondOutput_eq_packet27 :
    BB6.Agent2E7SecondSafe.secondOutput u27 9 =
      packet packet27.a packet27.q packet27.p fixedTail := by
  have ha : 8*(24*u27+19)+9=192*u27+161 := by omega
  simp [BB6.Agent2E7SecondSafe.secondOutput,packet27,fixedTail,ha,
    packet,word,CryptidBoundary.packetThree,
    BB6.Agent2E7SecondSafe.suffix2,CryptidBoundary.oppairs]

/-- The two original-source E returns from the 27th exception produce
    M(192*u+161,2,15;0 1^6). -/
theorem blank_twenty_seventh_reentry :
    ∃ T22 Tnorm24 Tnorm27,
      ObsEq (run (reentry27Time T22 Tnorm24 Tnorm27) blank)
        (DRegularSource.sourceSection seed28) := by
  obtain ⟨T22,Tnorm24,h27⟩ := blank_twenty_seventh_exception
  obtain ⟨Tnorm27,hraw⟩ :=
    BB6.Agent2PacketNormalizeSource.normalized_original_source
      packet27 (by simp [packet27]; omega) fixedTail
  have hfirst : ObsEq
      (run Tnorm27 (packet packet27.a packet27.q packet27.p fixedTail))
      (packet normalized27.a normalized27.q normalized27.p fixedTail) := by
    change run Tnorm27
      (packet packet27.a packet27.q packet27.p fixedTail) =
      packet normalized27.a normalized27.q normalized27.p fixedTail at hraw
    rw [hraw]
    exact BB6.Padding.cfgEq_refl _
  have hshape :
      packet normalized27.a normalized27.q normalized27.p fixedTail =
        packet (3*k27+3) normalized27.q (3*r27) fixedTail := by
    rw [normalized27_a_eq,normalized27_p_eq]
  have htarget :
      (⟨[],false,List.replicate seed28.a true,5⟩ : Cfg) =
        DRegularSource.sourceSection seed28 := by
    have hreg :=
      BB6.Agent2TwentyThirdRoot.regularSection_sourceSection
        seed28.a 0 0 (by
          dsimp [seed28,BB6.Agent2PacketZeroBoundary.aZeroUnary]
          omega)
    simpa [seed28,BB6.Agent2BoundaryBZero.regularSection,
      CryptidBoundary.oppairs] using hreg
  have hA : ObsEq
      (run zeroBoundary27Time
        (packet normalized27.a normalized27.q normalized27.p fixedTail))
      (DRegularSource.sourceSection seed28) := by
    rw [hshape]
    rw [BB6.Agent2PacketZeroBoundary.a_zero_boundary k27 normalized27.q r27]
    rw [htarget]
    exact BB6.Padding.cfgEq_refl _
  have hpacket : ObsEq
      (run (Tnorm27+zeroBoundary27Time)
        (packet packet27.a packet27.q packet27.p fixedTail))
      (DRegularSource.sourceSection seed28) := by
    exact source_chain Tnorm27 zeroBoundary27Time
      (packet packet27.a packet27.q packet27.p fixedTail)
      (packet normalized27.a normalized27.q normalized27.p fixedTail)
      (DRegularSource.sourceSection seed28) hfirst hA
  have hidx : 27*u27+25 = 9*t27+7 := by
    rw [t27_eq_three_u27_add_two]
    omega
  have hEE0 :=
    BB6.Agent2E7SecondSafe.exceptional_EE_packet u27 9 (by omega)
  have hEE : ObsEq
      (run (BB6.Agent2E7SecondSafe.eTime u27 9 +
        BB6.Agent2E7SecondSafe.middleTime u27)
        (DRegularSource.sourceSection ⟨9*t27+7,9,1⟩))
      (packet packet27.a packet27.q packet27.p fixedTail) := by
    simpa [BB6.Agent2E7SecondSafe.sourceStart,hidx,
      secondOutput_eq_packet27] using hEE0
  have hroot : ObsEq
      (run (BB6.Agent2E7SecondSafe.eTime u27 9 +
        BB6.Agent2E7SecondSafe.middleTime u27 +
        (Tnorm27+zeroBoundary27Time))
        (DRegularSource.sourceSection ⟨9*t27+7,9,1⟩))
      (DRegularSource.sourceSection seed28) := by
    exact source_chain
      (BB6.Agent2E7SecondSafe.eTime u27 9 +
        BB6.Agent2E7SecondSafe.middleTime u27)
      (Tnorm27+zeroBoundary27Time)
      (DRegularSource.sourceSection ⟨9*t27+7,9,1⟩)
      (packet packet27.a packet27.q packet27.p fixedTail)
      (DRegularSource.sourceSection seed28) hEE hpacket
  exact ⟨T22,Tnorm24,Tnorm27,
    source_chain (exception27Time T22 Tnorm24)
      (BB6.Agent2E7SecondSafe.eTime u27 9 +
        BB6.Agent2E7SecondSafe.middleTime u27 +
        (Tnorm27+zeroBoundary27Time))
      blank
      (DRegularSource.sourceSection ⟨9*t27+7,9,1⟩)
      (DRegularSource.sourceSection seed28) h27 hroot⟩

#print axioms terminal1684_exact
#print axioms t27_mod27
#print axioms blank_twenty_seventh_exception
#print axioms normalized27_certificate
#print axioms blank_twenty_seventh_reentry

end BB6.Agent2TwentySeventhRoot
