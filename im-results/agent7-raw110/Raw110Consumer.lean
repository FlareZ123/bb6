import Raw110ParentConsumer
import Canonical78Roster

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent7Raw110
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent31ThreeHole
open BB6.Agent10ZipAudit BB6.Agent47PartialAudit
open BB6.Agent47Canonical78

/-- Exact table comparison; no address-string matching or assumed
    equivalence between the classifier and source roster. -/
theorem p110_mem : ∃ e ∈ roster, e.2 = p110 := by
  have h : roster.any (fun e => tableOK e.2 p110) = true := by decide
  obtain ⟨e,he,hcheck⟩ := List.any_eq_true.mp h
  exact ⟨e,he,tableOK_sound _ _ hcheck⟩

noncomputable def otherRoster : List (List Move × PartialMachine) :=
  roster.filter fun e => !(tableOK e.2 p110)

theorem otherRoster_count : otherRoster.length = 77 := by decide

/-- Consume the entire raw110 parent in the accepted canonical78 interface.
    The other 77 canonical representatives keep their original quotient
    semantics. This form composes with other independent roster grafts. -/
theorem canonical78_cover_of_deepCut (kids : Move → PartialAudit)
    (hk : ∀ mv, partialCheck 7014 (child110 mv) (kids mv) = true)
    (B : Nat) (hB : 7014 ≤ B)
    (hOther : ∀ e ∈ otherRoster, Cover (WeightedBound B) e.2)
    (hLeaves : ∀ e ∈ deepResiduals kids, Cover (WeightedBound B) e.2) :
    Cover (WeightedBound B) BB6.CoverageAdapter.firstOneCylinder := by
  apply BB6.Agent47Canonical78.cover_at_target B hB
  intro e he
  cases h : tableOK e.2 p110 with
  | true =>
    rw [tableOK_sound _ _ h]
    exact cover_of_deepCut kids hk B hB hLeaves
  | false =>
    exact hOther e (List.mem_filter.mpr ⟨he, by simp [h]⟩)

theorem exact_of_deepCut (kids : Move → PartialAudit)
    (hk : ∀ mv, partialCheck 7014 (child110 mv) (kids mv) = true)
    (B : Nat) (hB : 7014 ≤ B)
    (hOther : ∀ e ∈ otherRoster, Cover (WeightedBound B) e.2)
    (hLeaves : ∀ e ∈ deepResiduals kids, Cover (WeightedBound B) e.2)
    (champ : ∃ m : BB6.Coverage.RawMachine,
      BB6.Coverage.HaltsAt (BB6.Coverage.tickRaw m) B) :
    BB6.Coverage.ExactBB6 B :=
  exact_from_weighted_first_one B (by omega)
    (canonical78_cover_of_deepCut kids hk B hB hOther hLeaves) champ

#print axioms p110_mem
#print axioms otherRoster_count
#print axioms canonical78_cover_of_deepCut
#print axioms exact_of_deepCut
end BB6.Agent7Raw110
