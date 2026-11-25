import Raw10BoxCore
import Box18to24Source
import WeightedFirstOneCover
import WeightedTNFQueueOrbit
import TNFPilot

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent49Box18to24Bridge

abbrev Parent := BB6.Agent13CrossRouteHeldLeaf109.firstOneB0_1LC
abbrev ParentRemainder := BB6.Agent49BoxBridge.raw10Remainder

/-- The seven source-checked rectangles are consumed inside the existing
    raw10 parent Cover. Every other raw10 remainder rectangle is retained
    explicitly through the `closedMatch = false` premise. -/
theorem raw10_cover_after_boxes18to24 (B : Nat) (hB : 7014 ≤ B)
    (hHeld : ∀ m : BB6Coverage.Machine,
      BB6Coverage.compatible BB6.Agent49BoxBridge.held m →
        BB6.Agent13BlankDelay.WeightedBound B m)
    (hRest : ∀ b ∈ ParentRemainder,
      BB6.Agent49Box18to24.closedMatch b = false →
        ∀ m : BB6Coverage.Machine,
          BB6.Agent49Box.Fits b m →
            BB6.Agent13BlankDelay.WeightedBound B m) :
    BB6Coverage.Cover (BB6.Agent13BlankDelay.WeightedBound B) Parent := by
  exact BB6.Agent49BoxBridge.raw10_cover B hB hHeld
    (fun r hr m hm =>
      BB6.Agent49Box18to24.residual_without_18to24 B (by omega)
        hRest r hr m hm)

/-- Generic root-level consumer. Instantiate `roster`, `hroot`, and
    `hParent` with the accepted post-raw114 77-entry interface. The theorem
    does not import its legacy FourHoleData build chain: roster soundness and
    exact parent membership remain explicit inputs. -/
theorem exact_from_raw10_boxes18to24 (B : Nat) (hB : 7014 ≤ B)
    (roster : List (List BB6Coverage.Move × BB6Coverage.PartialMachine))
    (hroot : ∀ m : BB6Coverage.Machine,
      BB6Coverage.compatible BB6.Agent50TNFPilot.root m →
        BB6.Agent13BlankDelay.WeightedBound 7014 m ∨
        ∃ e ∈ roster, BB6.Agent13BlankDelay.TNFQuotientCompatible e.2 m)
    (hParent : ∃ e ∈ roster, e.2 = Parent)
    (hHeld : ∀ m : BB6Coverage.Machine,
      BB6Coverage.compatible BB6.Agent49BoxBridge.held m →
        BB6.Agent13BlankDelay.WeightedBound B m)
    (hRest : ∀ b ∈ ParentRemainder,
      BB6.Agent49Box18to24.closedMatch b = false →
        ∀ m : BB6Coverage.Machine,
          BB6.Agent49Box.Fits b m →
            BB6.Agent13BlankDelay.WeightedBound B m)
    (hOther : ∀ e ∈ roster, e.2 ≠ Parent →
      BB6Coverage.Cover (BB6.Agent13BlankDelay.WeightedBound B) e.2)
    (champ : ∃ m : BB6.Coverage.RawMachine,
      BB6.Coverage.HaltsAt (BB6.Coverage.tickRaw m) B) :
    BB6.Coverage.ExactBB6 B := by
  obtain ⟨eParent, heParent, hParentEq⟩ := hParent
  have hParentLeaf :
      BB6Coverage.Cover (BB6.Agent13BlankDelay.WeightedBound B) eParent.2 := by
    rw [hParentEq]
    exact raw10_cover_after_boxes18to24 B hB hHeld hRest
  have hLeaves : ∀ e ∈ roster,
      BB6Coverage.Cover (BB6.Agent13BlankDelay.WeightedBound B) e.2 := by
    intro e he
    by_cases h : e.2 = Parent
    · have heq : e.2 = eParent.2 := h.trans hParentEq.symm
      rw [heq]
      exact hParentLeaf
    · exact hOther e he h
  have hRootCover :
      BB6Coverage.Cover (BB6.Agent13BlankDelay.WeightedBound B)
        BB6.CoverageAdapter.firstOneCylinder := by
    refine BB6Coverage.Cover.leaf _ ?_
    intro m hm
    have hmr : BB6Coverage.compatible BB6.Agent50TNFPilot.root m := by
      simpa [BB6.Agent50TNFPilot.root] using hm
    rcases hroot m hmr with hb | ⟨entry, he, e, he0, hc⟩
    · intro k d hk hd
      exact Nat.le_trans (hb k d hk hd) hB
    · have hz := BB6.Agent13BlankDelay.firstOne_terminal _
        BB6.Agent13BlankDelay.firstOneCylinder_root_action m hm
      exact BB6.Agent13BlankDelay.weighted_rename_back B e m he0 hz
        ((hLeaves entry he).sound _ hc)
  exact BB6.Agent13BlankDelay.exact_from_weighted_first_one B (by omega)
    hRootCover champ

#print axioms raw10_cover_after_boxes18to24
#print axioms exact_from_raw10_boxes18to24

end BB6.Agent49Box18to24Bridge
