import Lean.Elab.Tactic.Omega
import BlankTwentyThirdRejoin
import ExceptionalE7SecondSafe
import PacketNormalizeSource
import PacketZeroBoundarySource

set_option maxHeartbeats 100000000
set_option maxRecDepth 55000

namespace BB6.Agent2TwentyFourthRoot

open CryptidBoundary BB6.BoundaryPadding BB6.Padding
open BB6.Agent31PacketSource

def seed24 : DRegular.L :=
  ⟨64*BB6.Agent2TwentyThirdRoot.t23+21,1,5⟩

def terminal4510 : DRegular.L :=
  (DRegular.run 4510 seed24).getD ⟨9,0,0⟩

def t24 : Nat := (terminal4510.a-7)/9

theorem terminal4510_certificate :
    DRegular.run 4510 seed24 = some ⟨9*t24+7,6,1⟩ ∧
      t24 % 27 = 17 := by
  decide

theorem terminal4510_exact :
    DRegular.run 4510 seed24 = some ⟨9*t24+7,6,1⟩ :=
  terminal4510_certificate.1

theorem t24_mod27 : t24 % 27 = 17 :=
  terminal4510_certificate.2

def u24 : Nat := (t24-2)/3

theorem t24_eq_three_u24_add_two : t24 = 3*u24+2 := by
  have h := t24_mod27
  dsimp [u24]
  omega

def exception24Time : Nat :=
  BB6.Agent2TwentyThirdRoot.reentry23Time +
    DRegular.accumulated 4510 seed24

/-- The twenty-fourth exceptional input is reached from the blank tape. -/
theorem blank_twenty_fourth_exception :
    ObsEq (run exception24Time blank)
      (DRegularSource.sourceSection ⟨9*t24+7,6,1⟩) := by
  apply BB6.Agent25RootChain.extend_regular blank
    BB6.Agent2TwentyThirdRoot.reentry23Time
    4510 seed24 ⟨9*t24+7,6,1⟩
  · constructor
    · change 64*BB6.Agent2TwentyThirdRoot.t23+21 ≥ 2
      omega
    · left
      change (1 : Nat) ≠ 0
      omega
  · exact terminal4510_exact
  · exact BB6.Agent2TwentyThirdRoot.blank_twenty_third_reentry

def packet24 : BB6.Agent31PacketRank.Packet :=
  ⟨192*u24+161,2,9⟩

def normalized24 : BB6.Agent31PacketRank.Packet :=
  (BB6.Agent31PacketRank.normalizeWithCount packet24).2

theorem normalized24_certificate :
    normalized24.a % 3 = 0 ∧ normalized24.q = 1 ∧ normalized24.p = 9 := by
  decide

def k24 : Nat := (normalized24.a-3)/3
def r24 : Nat := normalized24.p/3

theorem normalized24_a_eq : normalized24.a = 3*k24+3 := by
  have hamin : normalized24.a ≥ 3 := by
    have h := BB6.Agent2PacketSafe.normalize_amin packet24
      (by simp [packet24]; omega)
    omega
  dsimp [k24]
  omega

theorem normalized24_p_eq : normalized24.p = 3*r24 := by
  have hp := normalized24_certificate.2.2
  simp [r24, hp]

def seed25 : DRegular.L :=
  ⟨BB6.Agent2PacketZeroBoundary.aZeroUnary k24 normalized24.q r24,0,0⟩

def zeroBoundary24Time : Nat :=
  BB6.Agent2PacketZeroBoundary.aZeroCost k24 normalized24.q r24

noncomputable def normalizer24Time : Nat :=
  Classical.choose
    (BB6.Agent2PacketNormalizeSource.normalized_original_source
      packet24 (by simp [packet24]; omega) fixedTail)

theorem normalizer24_exact :
    run normalizer24Time
      (packet packet24.a packet24.q packet24.p fixedTail) =
    packet normalized24.a normalized24.q normalized24.p fixedTail := by
  simpa [normalizer24Time, normalized24] using
    (Classical.choose_spec
      (BB6.Agent2PacketNormalizeSource.normalized_original_source
        packet24 (by simp [packet24]; omega) fixedTail))

private theorem secondOutput_eq_packet24 :
    BB6.Agent2E7SecondSafe.secondOutput u24 6 =
      packet packet24.a packet24.q packet24.p fixedTail := by
  have ha : 8*(24*u24+19)+9=192*u24+161 := by omega
  simp [BB6.Agent2E7SecondSafe.secondOutput,packet24,fixedTail,ha,
    packet,word,CryptidBoundary.packetThree,
    BB6.Agent2E7SecondSafe.suffix2,CryptidBoundary.oppairs]

def reentry24Time : Nat :=
  exception24Time +
    (BB6.Agent2E7SecondSafe.eTime u24 6 +
      BB6.Agent2E7SecondSafe.middleTime u24 +
      (normalizer24Time + zeroBoundary24Time))

/-- The two E returns produce the fixed-tail packet with p=9.  Its
    one B normalization edge reaches an A,p=9 boundary, which closes
    through the zero-packet source theorem to an explicit pure-unary seed. -/
theorem blank_twenty_fourth_reentry :
    ObsEq (run reentry24Time blank) (DRegularSource.sourceSection seed25) := by
  have hidx : 27*u24+25 = 9*t24+7 := by
    rw [t24_eq_three_u24_add_two]
    omega
  have hstart :
      BB6.Agent2E7SecondSafe.sourceStart u24 6 =
        DRegularSource.sourceSection ⟨9*t24+7,6,1⟩ := by
    simp [BB6.Agent2E7SecondSafe.sourceStart,hidx]
  have hEE0 :=
    BB6.Agent2E7SecondSafe.exceptional_EE_packet u24 6 (by omega)
  have hEE :
      ObsEq
        (run (BB6.Agent2E7SecondSafe.eTime u24 6 +
          BB6.Agent2E7SecondSafe.middleTime u24)
          (DRegularSource.sourceSection ⟨9*t24+7,6,1⟩))
        (packet packet24.a packet24.q packet24.p fixedTail) := by
    simpa [BB6.Agent2E7SecondSafe.sourceStart,hidx,
      secondOutput_eq_packet24] using hEE0
  have hfirst : ObsEq
      (run normalizer24Time
        (packet packet24.a packet24.q packet24.p fixedTail))
      (packet normalized24.a normalized24.q normalized24.p fixedTail) := by
    rw [normalizer24_exact]
    exact BB6.Padding.cfgEq_refl _
  have hshape :
      packet normalized24.a normalized24.q normalized24.p fixedTail =
        packet (3*k24+3) normalized24.q (3*r24) fixedTail := by
    rw [normalized24_a_eq, normalized24_p_eq]
  have htarget :
      (⟨[],false,List.replicate seed25.a true,5⟩ : Cfg) =
        DRegularSource.sourceSection seed25 := by
    have hreg :=
      BB6.Agent2TwentyThirdRoot.regularSection_sourceSection
        seed25.a 0 0 (by dsimp [seed25]; omega)
    simpa [seed25,BB6.Agent2BoundaryBZero.regularSection,
      CryptidBoundary.oppairs] using hreg
  have hA : ObsEq
      (run zeroBoundary24Time
        (packet normalized24.a normalized24.q normalized24.p fixedTail))
      (DRegularSource.sourceSection seed25) := by
    rw [hshape]
    rw [BB6.Agent2PacketZeroBoundary.a_zero_boundary k24 normalized24.q r24]
    rw [htarget]
    exact BB6.Padding.cfgEq_refl _
  have hpacket : ObsEq
      (run (normalizer24Time+zeroBoundary24Time)
        (packet packet24.a packet24.q packet24.p fixedTail))
      (DRegularSource.sourceSection seed25) := by
    exact source_chain normalizer24Time zeroBoundary24Time
      (packet packet24.a packet24.q packet24.p fixedTail)
      (packet normalized24.a normalized24.q normalized24.p fixedTail)
      (DRegularSource.sourceSection seed25) hfirst hA
  have hroot : ObsEq
      (run (BB6.Agent2E7SecondSafe.eTime u24 6 +
        BB6.Agent2E7SecondSafe.middleTime u24 +
        (normalizer24Time+zeroBoundary24Time))
        (DRegularSource.sourceSection ⟨9*t24+7,6,1⟩))
      (DRegularSource.sourceSection seed25) := by
    exact source_chain
      (BB6.Agent2E7SecondSafe.eTime u24 6 +
        BB6.Agent2E7SecondSafe.middleTime u24)
      (normalizer24Time+zeroBoundary24Time)
      (DRegularSource.sourceSection ⟨9*t24+7,6,1⟩)
      (packet packet24.a packet24.q packet24.p fixedTail)
      (DRegularSource.sourceSection seed25) hEE hpacket
  exact source_chain exception24Time
    (BB6.Agent2E7SecondSafe.eTime u24 6 +
      BB6.Agent2E7SecondSafe.middleTime u24 +
      (normalizer24Time+zeroBoundary24Time))
    blank
    (DRegularSource.sourceSection ⟨9*t24+7,6,1⟩)
    (DRegularSource.sourceSection seed25)
    blank_twenty_fourth_exception
    (by simpa [hstart] using hroot)

#print axioms terminal4510_exact
#print axioms t24_mod27
#print axioms blank_twenty_fourth_exception
#print axioms blank_twenty_fourth_reentry

end BB6.Agent2TwentyFourthRoot
