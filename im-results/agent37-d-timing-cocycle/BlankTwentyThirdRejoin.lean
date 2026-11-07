import Lean.Elab.Tactic.Omega
import BlankTwentySecondRejoin
import ExceptionalBGeneral

set_option maxHeartbeats 100000000
set_option maxRecDepth 55000

namespace BB6.Agent2TwentyThirdRoot

open CryptidBoundary BB6.BoundaryPadding BB6.Padding

def reentry22Time (T22 : Nat) : Nat :=
  BB6.Agent2TwentySecondRoot.exception22Time +
    (BB6.Agent2E7SecondSafe.eTime BB6.Agent2TwentySecondRoot.u22 8 +
      BB6.Agent2E7SecondSafe.middleTime BB6.Agent2TwentySecondRoot.u22 +
      T22)

private theorem regularSection_sourceSection (a q b : Nat) (ha : 2 ≤ a) :
    BB6.Agent2BoundaryBZero.regularSection a q b =
      DRegularSource.sourceSection ⟨a,q,b⟩ := by
  simp only [BB6.Agent2BoundaryBZero.regularSection,
    DRegularSource.sourceSection, CryptidBoundary.init]
  have hrepAdd (m n : Nat) :
      List.replicate (m+n) true =
        List.replicate m true ++ List.replicate n true := by
    induction m with
    | zero => simp
    | succ m ih =>
      rw [show Nat.succ m + n = (m+n)+1 by omega]
      rw [List.replicate_succ]
      rw [ih]
      rw [← List.cons_append]
      rw [← List.replicate_succ]
  have hrep : List.replicate a true =
      [true,true] ++ List.replicate (a-2) true := by
    rw [show a = 2+(a-2) by omega, hrepAdd]
    simp
  rw [hrep]
  simp [List.append_assoc]

def seed23 : DRegular.L :=
  ⟨BB6.Agent2TwentySecondRoot.normalized22.a,
    BB6.Agent2TwentySecondRoot.normalized22.q+2,5⟩

def terminal3636 : DRegular.L :=
  (DRegular.run 3636 seed23).getD ⟨9,0,0⟩

def t23 : Nat := (terminal3636.a-4)/9

theorem terminal3636_certificate :
    DRegular.run 3636 seed23 = some ⟨9*t23+4,2,1⟩ ∧
      t23 % 27 = 21 := by
  decide

theorem terminal3636_exact :
    DRegular.run 3636 seed23 = some ⟨9*t23+4,2,1⟩ :=
  terminal3636_certificate.1

theorem t23_mod27 : t23 % 27 = 21 :=
  terminal3636_certificate.2

def exception23Time (T22 : Nat) : Nat :=
  reentry22Time T22 + DRegular.accumulated 3636 seed23

/-- Extend any witnessed twenty-second reentry through the next D-regular run. -/
theorem blank_twenty_third_exception_from (T22 : Nat)
    (h22 : ObsEq (run (reentry22Time T22) blank)
      (BB6.Agent2BoundaryBZero.regularSection
        BB6.Agent2TwentySecondRoot.normalized22.a
        (BB6.Agent2TwentySecondRoot.normalized22.q+2) 5)) :
    ObsEq (run (exception23Time T22) blank)
      (DRegularSource.sourceSection ⟨9*t23+4,2,1⟩) := by
  have hamin : BB6.Agent2TwentySecondRoot.normalized22.a ≥ 4 :=
    BB6.Agent2PacketSafe.normalize_amin
      BB6.Agent2TwentySecondRoot.packet22
      (by simp [BB6.Agent2TwentySecondRoot.packet22]; omega)
  have h22source : ObsEq (run (reentry22Time T22) blank)
      (DRegularSource.sourceSection seed23) := by
    rw [← regularSection_sourceSection
      BB6.Agent2TwentySecondRoot.normalized22.a
      (BB6.Agent2TwentySecondRoot.normalized22.q+2) 5 (by omega)]
    exact h22
  apply BB6.Agent25RootChain.extend_regular blank (reentry22Time T22)
    3636 seed23 ⟨9*t23+4,2,1⟩
  · constructor
    · change BB6.Agent2TwentySecondRoot.normalized22.a ≥ 2
      omega
    · left
      change (BB6.Agent2TwentySecondRoot.normalized22.q+2) ≠ 0
      omega
  · exact terminal3636_exact
  · exact h22source

def packet23Time : Nat :=
  BB6.Agent32EAll.duration (3*t23) 1 +
    BB6.Agent25BGeneral.bCost t23

def reentry23Time (T22 : Nat) : Nat :=
  exception23Time T22 + packet23Time

/-- The q=2 exceptional B return closes the twenty-third root episode. -/
theorem blank_twenty_third_reentry :
    ∃ T22, ObsEq (run (reentry23Time T22) blank)
      (DRegularSource.sourceSection ⟨64*t23+21,1,5⟩) := by
  obtain ⟨T22,h22⟩ :=
    BB6.Agent2TwentySecondRoot.blank_twentysecond_reentry
  have h23 := blank_twenty_third_exception_from T22 h22
  have hEB :
      ObsEq
        (run packet23Time
          (DRegularSource.sourceSection ⟨9*t23+4,2,1⟩))
        (DRegularSource.sourceSection ⟨64*t23+21,1,5⟩) := by
    simpa [packet23Time] using
      (BB6.Agent25BGeneral.exceptional_EB_general t23 0)
  exact ⟨T22, source_chain (exception23Time T22) packet23Time blank
    (DRegularSource.sourceSection ⟨9*t23+4,2,1⟩)
    (DRegularSource.sourceSection ⟨64*t23+21,1,5⟩) h23 hEB⟩

#print axioms terminal3636_exact
#print axioms t23_mod27
#print axioms blank_twenty_third_exception_from
#print axioms blank_twenty_third_reentry

end BB6.Agent2TwentyThirdRoot
