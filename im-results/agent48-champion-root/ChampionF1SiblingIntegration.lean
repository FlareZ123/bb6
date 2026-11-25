import F0SiblingIntegrationExtended
import ChampionF1OneLFCover
import ChampionF1ZeroRD

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace BB6.Agent48F1Integration

open BB6Coverage
open BB6.Agent13BlankDelay
open BB6.Agent6ChampionResidual
open BB6.Agent31ChampionParentIntegration
open BB6.Agent31FourHoleRoster
open BB6.Agent6F0.Integration
open BB6.Agent41F0Extended
open BB6.Agent47Canonical78
open BB6Coverage.FAR

/-- The first of the two newly closed depth-five siblings is the exact
    F/1 = 1LF child of the source-replayed champion path. -/
theorem oneLF_is_depth5_sibling :
    sameTable BB6.Agent48F1OneLF.parent
      (championChild 5 ⟨true,false,5⟩) = true := by
  decide [BB6.Agent48F1OneLF.parent, championChild, championParent,
    championHole, championP5, championP4, championP3, championP2,
    championP1, championResidual, championRootAfterB, refine, root]

/-- The second newly closed depth-five sibling is exactly F/1 = 0RD. -/
theorem zeroRD_is_depth5_sibling :
    sameTable BB6.Agent48F1ZeroRD.ctr
      (championChild 5 ⟨false,true,3⟩) = true := by
  decide [BB6.Agent48F1ZeroRD.ctr, championChild, championParent,
    championHole, championP5, championP4, championP3, championP2,
    championP1, championResidual, championRootAfterB, refine, root]

/-- Lift the 126-bound three-hole certificate to any larger weighted target. -/
theorem cover_oneLF (B : Nat) (hB : 126 ≤ B) :
    Cover (WeightedBound B) BB6.Agent48F1OneLF.parent := by
  refine Cover.leaf _ ?_
  intro m hm k d hk hd
  exact Nat.le_trans
    (BB6.Agent48F1OneLF.all_completions_weighted m hm k d hk hd) hB

/-- The F/1 = 0RD sibling is nonhalting for every compatible completion. -/
theorem cover_zeroRD (B : Nat) :
    Cover (WeightedBound B) BB6.Agent48F1ZeroRD.ctr :=
  BB6.Agent48F1ZeroRD.cover B

def parentOneLF (p : PartialMachine) : Bool :=
  sameTable p BB6.Agent48F1OneLF.parent

def parentZeroRD (p : PartialMachine) : Bool :=
  sameTable p BB6.Agent48F1ZeroRD.ctr

/-- Remove exactly these two complete depth-five cylinders from the
    already source-composed 112-leaf raw139 frontier. -/
def refineResidualF1 (e : List Move × PartialMachine) :
    Option (List Move × PartialMachine) :=
  if parentOneLF e.2 then none
  else if parentZeroRD e.2 then none
  else some e

noncomputable def remainingF1Extended :
    List (List Move × PartialMachine) :=
  remainingExtended.filterMap refineResidualF1

theorem remainingF1Extended_count :
    remainingF1Extended.length = 110 := by
  decide

theorem removedF1_count :
    remainingExtended.length - remainingF1Extended.length = 2 := by
  decide

/-- Every one of the 112 earlier obligations is either one of the two new
    closed siblings or remains explicitly in the 110-entry frontier. -/
theorem cover_remainingExtended
    (hLeaves : ∀ e ∈ remainingF1Extended,
      Cover (WeightedBound championScore) e.2)
    (e : List Move × PartialMachine)
    (he : e ∈ remainingExtended) :
    Cover (WeightedBound championScore) e.2 := by
  by_cases hLF : parentOneLF e.2 = true
  · have heq : e.2 = BB6.Agent48F1OneLF.parent := sameTable_sound hLF
    rw [heq]
    exact cover_oneLF championScore (by omega)
  · by_cases hRD : parentZeroRD e.2 = true
    · have heq : e.2 = BB6.Agent48F1ZeroRD.ctr := sameTable_sound hRD
      rw [heq]
      exact cover_zeroRD championScore
    · have hMem : e ∈ remainingF1Extended := by
        unfold remainingF1Extended
        apply List.mem_filterMap.mpr
        refine ⟨e, he, ?_⟩
        simp [refineResidualF1, parentOneLF, parentZeroRD, hLF, hRD]
      exact hLeaves e hMem

theorem refined_residual_cover
    (hLeaves : ∀ e ∈ remainingF1Extended,
      Cover (WeightedBound championScore) e.2) :
    Cover (WeightedBound championScore) championResidual :=
  BB6.Agent41F0Extended.refined_residual_cover
    (fun e he => cover_remainingExtended hLeaves e he)

/-- Conditional exact BB(6) composition with 77 nonchampion canonical
    representatives and 110 refined raw139 leaves. -/
theorem exact_from_remainingF1Extended
    (hOther : ∀ e ∈ BB6.Agent47Canonical78.roster,
      e.2 ≠ championResidual → Cover (WeightedBound championScore) e.2)
    (hLeaves : ∀ e ∈ remainingF1Extended,
      Cover (WeightedBound championScore) e.2) :
    BB6.Coverage.ExactBB6 championScore :=
  BB6.Agent41F0Extended.exact_from_remainingExtended hOther
    (fun e he => cover_remainingExtended hLeaves e he)

#print axioms oneLF_is_depth5_sibling
#print axioms zeroRD_is_depth5_sibling
#print axioms cover_oneLF
#print axioms cover_zeroRD
#print axioms remainingF1Extended_count
#print axioms removedF1_count
#print axioms cover_remainingExtended
#print axioms refined_residual_cover
#print axioms exact_from_remainingF1Extended

end BB6.Agent48F1Integration
