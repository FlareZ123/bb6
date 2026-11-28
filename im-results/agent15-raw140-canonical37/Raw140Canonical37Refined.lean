import Raw47AfterRaw112Conditional
import Raw140ThreeHoleCut

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-!
Conditional global refinement of the accepted Raw39 -> Raw112 -> Raw47 lineage
through the source-checked Raw140 three-hole decomposition.

Raw47 remains an explicit whole-parent premise here.  Raw140 is checked to occur
exactly once in the resulting 37-roster, then replaced by the exact residual
frontier exported by BB6.Agent10Raw140ThreeHole.
-/

namespace BB6.Agent15Raw140Canonical37Refined

open BB6Coverage BB6.Agent13BlankDelay BB6.Agent50TNFPilot
open BB6.Agent31FourHoleFrontier BB6.Agent31FourHoleRoster
open BB6.Agent47CanonicalFrontier BB6.Agent47CanonicalRefinement
open BB6.Agent31StableParentBatch
open BB6ChampionArithmetic

abbrev p47 : PartialMachine :=
  BB6.Agent9Raw47AfterRaw112Conditional.p47

noncomputable abbrev baseRoster :=
  BB6.Agent9Raw47AfterRaw112Conditional.roster37

def p140 : PartialMachine :=
  FAR.fromCodes [7,24,11,12,15,1,6,18,4,17,24,24]

abbrev removedParents : List PartialMachine := [p140]

theorem p140_count37 :
    (baseRoster.filter (fun e => sameTable e.2 p140)).length = 1 := by
  decide

theorem p140_root :
    p140 initialSlot = some (some ⟨true,true,1⟩) := by
  decide

theorem p140_cut_parent_agreement :
    p140 = BB6.Agent10Raw140ThreeHole.parent :=
  sameTable_sound (by decide)

theorem base_sound_at (B : Nat) (hFloor : 6766859 ≤ B)
    (h47 : Cover (WeightedBound 6766859) p47) :
    ∀ m, compatible root m →
      WeightedBound B m ∨
        ∃ e ∈ baseRoster, TNFQuotientCompatible e.2 m := by
  intro m hm
  rcases BB6.Agent9Raw47AfterRaw112Conditional.conditional_sound h47 m hm with
    hsmall | hrest
  · exact Or.inl (fun k d hk hd => Nat.le_trans (hsmall k d hk hd) hFloor)
  · exact Or.inr hrest

theorem p140_cover_at (B : Nat) (hCut : 10010 ≤ B)
    (hResidual : ∀ e ∈ BB6.Agent10Raw140ThreeHole.remaining,
      Cover (WeightedBound B) e.2) :
    Cover (WeightedBound B) p140 := by
  rw [p140_cut_parent_agreement]
  exact BB6.Agent10Raw140ThreeHole.cover hCut hResidual

theorem parents_root :
    ∀ p ∈ removedParents,
      p initialSlot = some (some ⟨true,true,1⟩) := by
  intro p hp
  have he : p = p140 := by simpa [removedParents] using hp
  subst p
  exact p140_root

theorem parents_cover_at (B : Nat) (hCut : 10010 ≤ B)
    (hResidual : ∀ e ∈ BB6.Agent10Raw140ThreeHole.remaining,
      Cover (WeightedBound B) e.2) :
    ∀ p ∈ removedParents, Cover (WeightedBound B) p := by
  intro p hp
  have he : p = p140 := by simpa [removedParents] using hp
  subst p
  exact p140_cover_at B hCut hResidual

noncomputable def roster36 := removeParents removedParents baseRoster

theorem count36 : roster36.length = 36 := by
  decide

theorem raw140_removed :
    (roster36.filter (fun e => sameTable e.2 p140)).length = 0 := by
  decide

theorem raw47_remains_removed :
    (roster36.filter (fun e => sameTable e.2 p47)).length = 0 := by
  decide

theorem refined_sound_at (B : Nat) (hFloor : 6766859 ≤ B)
    (hCut : 10010 ≤ B)
    (h47 : Cover (WeightedBound 6766859) p47)
    (hResidual : ∀ e ∈ BB6.Agent10Raw140ThreeHole.remaining,
      Cover (WeightedBound B) e.2) :
    ∀ m, compatible root m →
      WeightedBound B m ∨
        ∃ e ∈ roster36, TNFQuotientCompatible e.2 m := by
  apply removeParents_sound (parents := removedParents)
    (roster := baseRoster)
    (base_sound_at B hFloor h47)
    parents_root (parents_cover_at B hCut hResidual)

theorem conditional_exact_at_champion_score
    (h47 : Cover (WeightedBound 6766859) p47)
    (hRaw140 : ∀ e ∈ BB6.Agent10Raw140ThreeHole.remaining,
      Cover (WeightedBound (proposedTM63Moves + 7)) e.2)
    (hLeaves : ∀ e ∈ roster36,
      Cover (WeightedBound (proposedTM63Moves + 7)) e.2) :
    BB6.Coverage.ExactBB6 (proposedTM63Moves + 7) := by
  have hFloor :
      6766859 ≤ proposedTM63Moves + 7 :=
    BB6.Agent38ChampionThreshold.champion_score_ge_6766859
  have hCut : 10010 ≤ proposedTM63Moves + 7 := by omega
  exact exact_from_quotient_roster (by omega) hFloor
    (refined_sound_at (proposedTM63Moves + 7) hFloor hCut h47 hRaw140)
    hLeaves BB6Coverage.Agent48DirectRoot.champion_raw_witness

#print axioms p140_count37
#print axioms p140_cut_parent_agreement
#print axioms count36
#print axioms raw140_removed
#print axioms raw47_remains_removed
#print axioms refined_sound_at
#print axioms conditional_exact_at_champion_score

end BB6.Agent15Raw140Canonical37Refined
