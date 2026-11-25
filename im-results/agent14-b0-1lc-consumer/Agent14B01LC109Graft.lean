import Agent14B01LCGraft
import MixedBound109Composition

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent14B01LC109Graft

open BB6Coverage
open BB6.Agent13BlankDelay
open BB6.Agent13MixedBound109
open BB6.Agent47Combined109
open BB6.Agent31FourHoleRoster
open BB6.Agent14B01LCGraft

abbrev Parent : PartialMachine := BB6.Agent14B01LCGraft.Parent
abbrev B : Nat := championScore

def parentAudit : FrontierAudit (WeightedBound B) Parent :=
  witnessAudit B (Nat.le_of_lt champion_score_gt_7014)

/-- The 109-entry residual roster with exactly the B0=1LC parent removed.
    That parent is replaced by the proof-carrying 65-witness audit. -/
def otherRoster : List (List Move × PartialMachine) :=
  reducedRoster.filter fun e => !(sameTable e.2 Parent)

theorem otherRoster_count : otherRoster.length = 108 := by
  decide

theorem otherRoster_mem_of_ne {e : List Move × PartialMachine}
    (he : e ∈ reducedRoster) (hne : e.2 ≠ Parent) :
    e ∈ otherRoster := by
  apply List.mem_filter.mpr
  refine ⟨he, ?_⟩
  cases h : sameTable e.2 Parent with
  | false => simp [otherRoster, h]
  | true => exact False.elim (hne (sameTable_sound h))

/-- Exact replacement of one of the 109 champion-score obligations:
    every root completion is either already safe at the attained score,
    extends one of the other 108 residuals, or lies in the explicit
    complement of the 65-certificate B0=1LC audit. -/
theorem refinedRootDichotomy (m : Machine)
    (hm : compatible BB6.Agent50TNFPilot.root m) :
    WeightedBound B m ∨
      (∃ e ∈ otherRoster, compatible e.2 m) ∨
      parentAudit.open m := by
  rcases reduced_sound m hm with h7014 | hResidual
  · exact Or.inl (weightedBound_mono
      (Nat.le_of_lt champion_score_gt_7014) h7014)
  · rcases hResidual with ⟨e, he, hcompat⟩
    cases hsame : sameTable e.2 Parent with
    | true =>
        have hEq : e.2 = Parent := sameTable_sound hsame
        have hParent : compatible Parent m := by
          simpa [hEq] using hcompat
        rcases witnessAudit_exhaustive
            (Nat.le_of_lt champion_score_gt_7014) m hParent with hB | hOpen
        · exact Or.inl hB
        · exact Or.inr (Or.inr hOpen)
    | false =>
        have hne : e.2 ≠ Parent := by
          intro hEq
          rw [hEq] at hsame
          have hRefl : sameTable Parent Parent = true := by decide
          rw [hRefl] at hsame
          contradiction
        exact Or.inr (Or.inl
          ⟨e, otherRoster_mem_of_ne he hne, hcompat⟩)

/-- If the other 108 cylinders are covered at the attained score and the
    explicit B0=1LC complement is closed, the existing mixed-bound consumer
    yields the full first-one root Cover. -/
theorem cover_of_108_and_parentAudit
    (hLeaves : ∀ e ∈ otherRoster, Cover (WeightedBound B) e.2)
    (hNoOpen : ∀ m, compatible Parent m → ¬ parentAudit.open m) :
    Cover (WeightedBound B) BB6.Agent50TNFPilot.root := by
  apply cover_of_reduced_roster_at_champion_score
  intro e he
  cases hsame : sameTable e.2 Parent with
  | true =>
      have hEq : e.2 = Parent := sameTable_sound hsame
      subst e
      exact FrontierAudit.close parentAudit hNoOpen
  | false =>
      have hne : e.2 ≠ Parent := by
        intro hEq
        rw [hEq] at hsame
        have hRefl : sameTable Parent Parent = true := by decide
        rw [hRefl] at hsame
        contradiction
      exact hLeaves e (otherRoster_mem_of_ne he hne)

/-- Conditional exact BB(6) theorem with the same champion attainment as the
    109-roster result, but with the B0=1LC obligation refined into 65
    certified cylinders and its explicitly retained complement. -/
theorem exact_from_108_and_parentAudit
    (hLeaves : ∀ e ∈ otherRoster, Cover (WeightedBound B) e.2)
    (hNoOpen : ∀ m, compatible Parent m → ¬ parentAudit.open m) :
    BB6.Coverage.ExactBB6 B := by
  apply exact_from_reduced_roster_at_champion_score
  intro e he
  cases hsame : sameTable e.2 Parent with
  | true =>
      have hEq : e.2 = Parent := sameTable_sound hsame
      subst e
      exact FrontierAudit.close parentAudit hNoOpen
  | false =>
      have hne : e.2 ≠ Parent := by
        intro hEq
        rw [hEq] at hsame
        have hRefl : sameTable Parent Parent = true := by decide
        rw [hRefl] at hsame
        contradiction
      exact hLeaves e (otherRoster_mem_of_ne he hne)

#print axioms otherRoster_count
#print axioms otherRoster_mem_of_ne
#print axioms refinedRootDichotomy
#print axioms cover_of_108_and_parentAudit
#print axioms exact_from_108_and_parentAudit

end BB6.Agent14B01LC109Graft
