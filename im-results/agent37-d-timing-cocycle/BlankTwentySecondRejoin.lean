import Lean.Elab.Tactic.Omega
import BlankTwentyFirstRejoin
import ExceptionalE7SecondSafe
import PacketNormalizeSource
import BoundaryBZero

set_option maxHeartbeats 100000000
set_option maxRecDepth 55000

namespace BB6.Agent2TwentySecondRoot

open CryptidBoundary BB6.BoundaryPadding BB6.Padding
open BB6.Agent31PacketSource

/-- Seed supplied by the twenty-first source-certified reentry. -/
def seed22 : DRegular.L :=
  ⟨64*BB6.Agent2TwentyFirstRoot.t21+33,1,5⟩

/-- Exact endpoint after 730 regular sections from the twenty-first reentry. -/
def terminal730 : DRegular.L :=
  (DRegular.run 730 seed22).getD ⟨9,0,0⟩

def t22 : Nat := (terminal730.a-7)/9

theorem terminal730_certificate :
    DRegular.run 730 seed22 = some ⟨9*t22+7,8,1⟩ ∧
      t22 % 27 = 14 := by
  decide

theorem terminal730_exact :
    DRegular.run 730 seed22 = some ⟨9*t22+7,8,1⟩ :=
  terminal730_certificate.1

theorem t22_mod27 : t22 % 27 = 14 :=
  terminal730_certificate.2

def u22 : Nat := (t22-2)/3

theorem t22_eq_three_u22_add_two : t22 = 3*u22+2 := by
  have h := t22_mod27
  dsimp [u22]
  omega

def exception22Time : Nat :=
  BB6.Agent2TwentyFirstRoot.reentry21Time +
    DRegular.accumulated 730 seed22

/-- The twenty-second exceptional input is reached from the genuine blank
    tape, conditional on the preceding source-certified chain. -/
theorem blank_twentysecond_exception :
    BB6.BoundaryPadding.ObsEq (run exception22Time blank)
      (DRegularSource.sourceSection ⟨9*t22+7,8,1⟩) := by
  apply BB6.Agent25RootChain.extend_regular blank
    BB6.Agent2TwentyFirstRoot.reentry21Time
    730 seed22 ⟨9*t22+7,8,1⟩
  · constructor
    · change 64*BB6.Agent2TwentyFirstRoot.t21+33 ≥ 2
      omega
    · left
      change (1 : Nat) ≠ 0
      omega
  · exact terminal730_exact
  · exact BB6.Agent2TwentyFirstRoot.blank_twentyfirst_reentry

def fixedTail : List Bool := false :: List.replicate 6 true

def packet22 : BB6.Agent31PacketRank.Packet :=
  ⟨192*u22+161,2,13⟩

def normalized22 : BB6.Agent31PacketRank.Packet :=
  (BB6.Agent31PacketRank.normalizeWithCount packet22).2

theorem normalized22_p : normalized22.p = 1 := by
  decide

theorem normalized22_q : normalized22.q = 8 := by
  decide

private theorem secondOutput_eq_packet22 :
    BB6.Agent2E7SecondSafe.secondOutput u22 8 =
      packet packet22.a packet22.q packet22.p fixedTail := by
  have ha : 8*(24*u22+19)+9=192*u22+161 := by omega
  simp [BB6.Agent2E7SecondSafe.secondOutput,packet22,fixedTail,ha,
    packet,word,CryptidBoundary.packetThree,
    BB6.Agent2E7SecondSafe.suffix2,CryptidBoundary.oppairs]

/-- The fixed-tail packet normalizer has a six-edge endpoint with p=1.
    BoundaryBZero.e_one_regular identifies that endpoint with a regular
    section, giving an explicit root reentry rather than an existential one. -/
theorem blank_twentysecond_reentry :
    ∃ T,
      BB6.BoundaryPadding.ObsEq
        (run (exception22Time +
          (BB6.Agent2E7SecondSafe.eTime u22 8 +
            BB6.Agent2E7SecondSafe.middleTime u22 + T)) blank)
        (BB6.Agent2BoundaryBZero.regularSection
          normalized22.a (normalized22.q+2) 5) := by
  obtain ⟨T,hraw⟩ :=
    BB6.Agent2PacketNormalizeSource.normalized_original_source
      packet22 (by simp [packet22]; omega) fixedTail
  have hfirst : BB6.BoundaryPadding.ObsEq
      (run T (packet packet22.a packet22.q packet22.p fixedTail))
      (packet normalized22.a normalized22.q normalized22.p fixedTail) := by
    change run T
      (packet packet22.a packet22.q packet22.p fixedTail) =
      packet normalized22.a normalized22.q normalized22.p fixedTail at hraw
    rw [hraw]
    exact BB6.Padding.cfgEq_refl _
  have hterminal : BB6.BoundaryPadding.ObsEq
      (run 0 (packet normalized22.a normalized22.q normalized22.p fixedTail))
      (BB6.Agent2BoundaryBZero.regularSection
        normalized22.a (normalized22.q+2) 5) := by
    rw [normalized22_p]
    rw [BB6.Agent2BoundaryBZero.e_one_regular normalized22.a normalized22.q]
    exact BB6.Padding.cfgEq_refl _
  have hpacket : BB6.BoundaryPadding.ObsEq
      (run T (packet packet22.a packet22.q packet22.p fixedTail))
      (BB6.Agent2BoundaryBZero.regularSection
        normalized22.a (normalized22.q+2) 5) := by
    exact source_chain T 0
      (packet packet22.a packet22.q packet22.p fixedTail)
      (packet normalized22.a normalized22.q normalized22.p fixedTail)
      (BB6.Agent2BoundaryBZero.regularSection
        normalized22.a (normalized22.q+2) 5)
      hfirst hterminal
  have hEE : BB6.BoundaryPadding.ObsEq
      (run (BB6.Agent2E7SecondSafe.eTime u22 8 +
        BB6.Agent2E7SecondSafe.middleTime u22)
        (BB6.Agent2E7SecondSafe.sourceStart u22 8))
      (packet packet22.a packet22.q packet22.p fixedTail) := by
    rw [secondOutput_eq_packet22]
    exact BB6.Agent2E7SecondSafe.exceptional_EE_packet u22 8 (by omega)
  have hroot : BB6.BoundaryPadding.ObsEq
      (run (BB6.Agent2E7SecondSafe.eTime u22 8 +
        BB6.Agent2E7SecondSafe.middleTime u22 + T)
        (BB6.Agent2E7SecondSafe.sourceStart u22 8))
      (BB6.Agent2BoundaryBZero.regularSection
        normalized22.a (normalized22.q+2) 5) := by
    exact source_chain
      (BB6.Agent2E7SecondSafe.eTime u22 8 +
        BB6.Agent2E7SecondSafe.middleTime u22) T
      (BB6.Agent2E7SecondSafe.sourceStart u22 8)
      (packet packet22.a packet22.q packet22.p fixedTail)
      (BB6.Agent2BoundaryBZero.regularSection
        normalized22.a (normalized22.q+2) 5)
      hEE hpacket
  have hidx : 27*u22+25 = 9*t22+7 := by
    rw [t22_eq_three_u22_add_two]
    omega
  have hstart :
      BB6.Agent2E7SecondSafe.sourceStart u22 8 =
        DRegularSource.sourceSection ⟨9*t22+7,8,1⟩ := by
    simp [BB6.Agent2E7SecondSafe.sourceStart,hidx]
  rw [hstart] at hroot
  exact ⟨T,
    source_chain exception22Time
      (BB6.Agent2E7SecondSafe.eTime u22 8 +
        BB6.Agent2E7SecondSafe.middleTime u22 + T)
      blank
      (DRegularSource.sourceSection ⟨9*t22+7,8,1⟩)
      (BB6.Agent2BoundaryBZero.regularSection
        normalized22.a (normalized22.q+2) 5)
      blank_twentysecond_exception hroot⟩

#print axioms terminal730_exact
#print axioms t22_mod27
#print axioms normalized22_p
#print axioms normalized22_q
#print axioms blank_twentysecond_exception
#print axioms blank_twentysecond_reentry

end BB6.Agent2TwentySecondRoot
