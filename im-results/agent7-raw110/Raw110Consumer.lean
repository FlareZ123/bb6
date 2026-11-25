import Raw110Base
import Canonical78Roster

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent7Raw110
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent31ThreeHole
open BB6.Agent10ZipAudit BB6.Agent47PartialAudit
open BB6.Agent47Canonical78

/-- The parent partition is independent of the particular certificate search:
    every ordinary C1 child must have a checked partial audit, while the
    first-hole query theorem covers the halt at C1. -/
def deepCut (kids : Move → PartialAudit) : PartialAudit :=
  .split 7 (2,true) kids

theorem deepCut_checked (kids : Move → PartialAudit)
    (hk : ∀ mv, partialCheck 7014 (child110 mv) (kids mv) = true) :
    partialCheck 7014 p110 (deepCut kids) = true := by
  change (zipQueryOK 7014 p110 7 (2,true) &&
    allMoves (fun mv => partialCheck 7014 (child110 mv) (kids mv))) = true
  simp only [Bool.and_eq_true]
  exact ⟨query110, allMoves_of _ hk⟩

def deepResiduals (kids : Move → PartialAudit) :
    List (List Move × PartialMachine) :=
  partialResiduals p110 (deepCut kids)

theorem deepCut_sound (kids : Move → PartialAudit)
    (hk : ∀ mv, partialCheck 7014 (child110 mv) (kids mv) = true) :
    ∀ m, compatible p110 m → WeightedBound 7014 m ∨
      ∃ e ∈ deepResiduals kids, compatible e.2 m :=
  partialSound 7014 p110 (deepCut kids) p110_root p110_nohalt
    (deepCut_checked kids hk)

/-- Only the early bound is lifted. Every retained descendant must have
    its own cover at the actual target score B. -/
theorem cover_of_deepCut (kids : Move → PartialAudit)
    (hk : ∀ mv, partialCheck 7014 (child110 mv) (kids mv) = true)
    (B : Nat) (hB : 7014 ≤ B)
    (hLeaves : ∀ e ∈ deepResiduals kids, Cover (WeightedBound B) e.2) :
    Cover (WeightedBound B) p110 := by
  refine Cover.leaf _ ?_
  intro m hm
  rcases deepCut_sound kids hk m hm with hb | ⟨e, he, hc⟩
  · intro k d h1 h2
    exact Nat.le_trans (hb k d h1 h2) hB
  · exact (hLeaves e he).sound m hc

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

#print axioms deepCut_sound
#print axioms cover_of_deepCut
#print axioms p110_mem
#print axioms otherRoster_count
#print axioms canonical78_cover_of_deepCut
#print axioms exact_of_deepCut
end BB6.Agent7Raw110
