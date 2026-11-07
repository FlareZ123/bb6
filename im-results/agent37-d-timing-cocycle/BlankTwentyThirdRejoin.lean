import Lean.Elab.Tactic.Omega
import BlankTwentySecondRejoin
import ExceptionalBGeneral

set_option maxHeartbeats 100000000
set_option maxRecDepth 55000

namespace BB6.Agent2TwentyThirdRoot

open CryptidBoundary BB6.BoundaryPadding BB6.Padding

noncomputable def normalization22Time : Nat :=
  Classical.choose BB6.Agent2TwentySecondRoot.blank_twentysecond_reentry

def reentry22Time : Nat :=
  BB6.Agent2TwentySecondRoot.exception22Time +
    (BB6.Agent2E7SecondSafe.eTime BB6.Agent2TwentySecondRoot.u22 8 +
      BB6.Agent2E7SecondSafe.middleTime BB6.Agent2TwentySecondRoot.u22 +
      normalization22Time)

theorem blank_twentysecond_reentry_chosen :
    ObsEq (run reentry22Time blank)
      (BB6.Agent2BoundaryBZero.regularSection
        BB6.Agent2TwentySecondRoot.normalized22.a
        (BB6.Agent2TwentySecondRoot.normalized22.q+2) 5) := by
  simpa [reentry22Time, normalization22Time] using
    (Classical.choose_spec BB6.Agent2TwentySecondRoot.blank_twentysecond_reentry)

theorem regularSection_sourceSection (a q b : Nat) (ha : 2 ≤ a) :
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

def exception23Time : Nat :=
  reentry22Time + DRegular.accumulated 3636 seed23

/-- The twenty-third exceptional input is reached from the blank tape. -/
theorem blank_twenty_third_exception :
    ObsEq (run exception23Time blank)
      (DRegularSource.sourceSection ⟨9*t23+4,2,1⟩) := by
  have hamin : BB6.Agent2TwentySecondRoot.normalized22.a ≥ 4 :=
    BB6.Agent2PacketSafe.normalize_amin
      BB6.Agent2TwentySecondRoot.packet22
      (by simp [BB6.Agent2TwentySecondRoot.packet22]; omega)
  have h22source : ObsEq (run reentry22Time blank)
      (DRegularSource.sourceSection seed23) := by
    rw [← regularSection_sourceSection
      BB6.Agent2TwentySecondRoot.normalized22.a
      (BB6.Agent2TwentySecondRoot.normalized22.q+2) 5 (by omega)]
    exact blank_twentysecond_reentry_chosen
  apply BB6.Agent25RootChain.extend_regular blank reentry22Time
    3636 seed23 ⟨9*t23+4,2,1⟩
  · constructor
    · change BB6.Agent2TwentySecondRoot.normalized22.a ≥ 2
      omega
    · left
      change (5 : Nat) ≠ 0
      omega
  · exact terminal3636_exact
  · exact h22source

def packet23Time : Nat :=
  BB6.Agent32EAll.duration (3*t23) 1 +
    BB6.Agent25BGeneral.bCost t23

def reentry23Time : Nat := exception23Time + packet23Time

/-- The q=2 exceptional B return closes the twenty-third root episode. -/
theorem blank_twenty_third_reentry :
    ObsEq (run reentry23Time blank)
      (DRegularSource.sourceSection ⟨64*t23+21,1,5⟩) := by
  have hEB :
      ObsEq
        (run packet23Time
          (DRegularSource.sourceSection ⟨9*t23+4,2,1⟩))
        (DRegularSource.sourceSection ⟨64*t23+21,1,5⟩) := by
    simpa [packet23Time] using
      (BB6.Agent25BGeneral.exceptional_EB_general t23 0)
  exact source_chain exception23Time packet23Time blank
    (DRegularSource.sourceSection ⟨9*t23+4,2,1⟩)
    (DRegularSource.sourceSection ⟨64*t23+21,1,5⟩)
    blank_twenty_third_exception hEB

#print axioms terminal3636_exact
#print axioms t23_mod27
#print axioms blank_twenty_third_exception
#print axioms blank_twenty_third_reentry

end BB6.Agent2TwentyThirdRoot
