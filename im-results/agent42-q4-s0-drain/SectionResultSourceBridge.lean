import CostRecurrence
import SectionResultThreeCycleModel

/-!
# Bridge the isolated SectionResult model to the source recurrence

The arithmetic model in SectionResultThreeCycleModel.lean was deliberately
copied from CostRecurrence.lean to permit a lightweight standalone proof.
This module proves that its v2 and SectionResult cost fields agree with the
actual definitions in namespace BB6ChampionArithmetic, then transports the
q4 even-width cost identity to the source recurrence.

This is only a source-definition bridge. In CostRecurrence.lean,
proposedIncrementCost is explicitly a candidate cost, not yet a proved
primitive-run length. Nothing here certifies the TM63 machine itinerary.
-/

namespace BB6ChampionArithmetic

theorem v2_eq_sectionResultModel (n : Nat) :
    BB6ChampionArithmetic.v2 n = BB6SectionResultModel.v2 n := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
      by_cases hsmall : n ≤ 1
      · simp [BB6ChampionArithmetic.v2, BB6SectionResultModel.v2, hsmall]
      · by_cases heven : n % 2 = 0
        · have hlt : n / 2 < n := by omega
          simpa [BB6ChampionArithmetic.v2, BB6SectionResultModel.v2,
            hsmall, heven] using congrArg Nat.succ (ih (n / 2) hlt)
        · simp [BB6ChampionArithmetic.v2, BB6SectionResultModel.v2,
            hsmall, heven]

theorem proposedIncrementCost_eq_sectionResultModel
    (m n a b : Nat) :
    BB6ChampionArithmetic.proposedIncrementCost m n a b =
      BB6SectionResultModel.proposedIncrementCost m n a b := by
  simp [BB6ChampionArithmetic.proposedIncrementCost,
    BB6SectionResultModel.proposedIncrementCost,
    v2_eq_sectionResultModel]

theorem nextMarker_eq_sectionResultModel (m : Nat) :
    BB6ChampionArithmetic.nextMarker m =
      BB6SectionResultModel.nextMarker m := rfl

theorem nextExponent_eq_sectionResultModel (m a b : Nat) :
    BB6ChampionArithmetic.nextExponent m a b =
      BB6SectionResultModel.nextExponent m a b := rfl

theorem nextRight_eq_sectionResultModel (b : Nat) :
    BB6ChampionArithmetic.nextRight b =
      BB6SectionResultModel.nextRight b := rfl

/-- The cost field of the source SectionResult recursion agrees with the
    separately checked recurrence model for every input. -/
theorem sectionResult_cost_eq_sectionResultModel
    (n m a b : Nat) :
    (BB6ChampionArithmetic.sectionResult n m a b).cost =
      (BB6SectionResultModel.sectionResult n m a b).cost := by
  induction n generalizing m a b with
  | zero => rfl
  | succ n ih =>
      simp only [BB6ChampionArithmetic.sectionResult,
        BB6SectionResultModel.sectionResult]
      rw [nextMarker_eq_sectionResultModel,
        nextExponent_eq_sectionResultModel,
        nextRight_eq_sectionResultModel]
      rw [proposedIncrementCost_eq_sectionResultModel, ih]

/-- The even-width q4 cost identity now applies to the actual
    BB6ChampionArithmetic.sectionResult definition, not only to its copy. -/
theorem source_q4_terminal_cost_even
    (A L U R : Nat) (hA : 2 ≤ A) (hL : L % 2 = 0) :
    (BB6ChampionArithmetic.sectionResult
      (2^A*(2^(L+2)-1)-3) 0 U R).cost =
      31*(2^A*(2^(L+2)-1)-3) - 12*(A+L) +
        BB6SectionResultModel.rawSum
          (2^A*(2^(L+2)-1)-3) 0 U R := by
  rw [sectionResult_cost_eq_sectionResultModel]
  exact BB6SectionResultModel.sectionResult_q4_terminal_cost_even
    A L U R hA hL

#print axioms v2_eq_sectionResultModel
#print axioms proposedIncrementCost_eq_sectionResultModel
#print axioms sectionResult_cost_eq_sectionResultModel
#print axioms source_q4_terminal_cost_even

end BB6ChampionArithmetic
