import Lean.Elab.Tactic.Omega
import BlankTwentyFirstRejoin
import ExceptionalE7SecondSafe

set_option maxHeartbeats 100000000
set_option maxRecDepth 55000

namespace BB6.Agent2TwentySecondRoot

open CryptidBoundary BB6.BoundaryPadding BB6.Padding

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

/-- The t=3u+2, q=8 exceptional E input has a two-return original-source
    reduction to the safe fixed-tail packet family. The existing universal
    packet theorem then returns it to regular L. -/
theorem blank_twentysecond_reentry :
    ∃ T a q b,
      BB6.BoundaryPadding.ObsEq
        (run (exception22Time +
          (BB6.Agent2E7SecondSafe.eTime u22 8 +
            BB6.Agent2E7SecondSafe.middleTime u22 + T)) blank)
        (BB6.Agent2BoundaryBZero.regularSection a q b) := by
  obtain ⟨T,a,q,b,hsafe⟩ :=
    BB6.Agent2E7SecondSafe.exceptional_EE_safe u22 8 (by omega) (by decide)
  have hidx : 27*u22+25 = 9*t22+7 := by
    rw [t22_eq_three_u22_add_two]
    omega
  have hstart :
      BB6.Agent2E7SecondSafe.sourceStart u22 8 =
        DRegularSource.sourceSection ⟨9*t22+7,8,1⟩ := by
    simp [BB6.Agent2E7SecondSafe.sourceStart,hidx]
  rw [hstart] at hsafe
  exact ⟨T,a,q,b,
    source_chain exception22Time
      (BB6.Agent2E7SecondSafe.eTime u22 8 +
        BB6.Agent2E7SecondSafe.middleTime u22 + T)
      blank
      (DRegularSource.sourceSection ⟨9*t22+7,8,1⟩)
      (BB6.Agent2BoundaryBZero.regularSection a q b)
      blank_twentysecond_exception hsafe⟩

#print axioms terminal730_exact
#print axioms t22_mod27
#print axioms blank_twentysecond_exception
#print axioms blank_twentysecond_reentry

end BB6.Agent2TwentySecondRoot
