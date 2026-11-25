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

/-- Literal machine layout shared with the hard-root crosswalk:
    slot (q,b) is stored at index 2*q+b; none is a halt. -/
def literalMachine (xs : List BB6Coverage.Transition) : BB6Coverage.Machine :=
  fun s => xs[2*s.1.val + (if s.2 then 1 else 0)]?.getD none

/-- The D0 seed from the raw10 hard-root crosswalk. Its only halt is F1. -/
def D0 : BB6Coverage.Machine :=
  literalMachine [
    some ⟨true,true,1⟩, some ⟨false,true,4⟩,
    some ⟨true,false,2⟩, some ⟨false,true,0⟩,
    some ⟨true,false,0⟩, some ⟨true,false,3⟩,
    some ⟨true,false,2⟩, some ⟨true,false,5⟩,
    some ⟨false,false,2⟩, some ⟨false,false,1⟩,
    some ⟨true,false,4⟩, none
  ]

/-- The D0 one-halt leaf: F1 is unassigned, all other rows remain fixed. -/
def D0Leaf : BB6Coverage.PartialMachine :=
  fun s => match D0 s with
  | none => none
  | some mv => some (some mv)

theorem D0_halt_only : ∀ s, D0 s = none ↔ s = (5,true) := by decide

theorem D0_parent : BB6Coverage.compatible Parent D0 := by decide

theorem D0_fits_rect18 :
    BB6.Agent49Box.Fits (BB6.Agent49Box18to24.rect 18) D0 := by decide

theorem rect18_F1_unrestricted :
    ∀ t : BB6Coverage.Transition,
      t ∈ BB6.Agent49Box18to24.rect 18 (5,true) := by decide

/-- Every completion of the D0 one-halt leaf lies in the A1=18
    rectangle; the rectangle leaves F1 unrestricted. -/
theorem D0Leaf_fits_rect18 (m : BB6Coverage.Machine)
    (hm : BB6Coverage.compatible D0Leaf m) :
    BB6.Agent49Box.Fits (BB6.Agent49Box18to24.rect 18) m := by
  intro s
  by_cases hs : s = (5,true)
  · subst s
    exact rect18_F1_unrestricted (m (5,true))
  · have hnot : D0 s ≠ none := by
      intro h
      exact hs ((D0_halt_only s).mp h)
    have hp : D0Leaf s = some (D0 s) := by
      simp [D0Leaf, hnot]
    have hms : m s = D0 s := hm s (D0 s) hp
    simpa [hms] using D0_fits_rect18 s

/-- Source-accepted bound for the entire D0 one-halt leaf, not just
    its single halt-default completion. -/
theorem D0_leaf_cover_598 :
    BB6Coverage.Cover (BB6.Agent13BlankDelay.WeightedBound 598) D0Leaf := by
  refine BB6Coverage.Cover.leaf _ ?_
  intro m hm
  exact BB6.Agent49Box18to24.rectBound 18 (by decide) m
    (D0Leaf_fits_rect18 m hm)

/-- The D0 leaf is genuinely inside the B0=1LC parent. -/
theorem D0Leaf_parent :
    ∀ m, BB6Coverage.compatible D0Leaf m →
      BB6Coverage.compatible Parent m := by
  intro m hm s t hp
  have hD0 : D0 s = t := D0_parent s t hp
  cases t with
  | none =>
      have hs : s = (5,true) := (D0_halt_only s).mp hD0
      subst s
      have hpar : Parent (5,true) = none := by decide
      simp [hpar] at hp
  | some mv =>
      have hnot : D0 s ≠ none := by simp [hD0]
      have hleaf : D0Leaf s = some (D0 s) := by simp [D0Leaf, hnot]
      have hms : m s = D0 s := hm s (D0 s) hleaf
      simpa [hD0] using hms

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
#print axioms D0_parent
#print axioms D0_leaf_cover_598
#print axioms D0Leaf_parent
#print axioms exact_from_raw10_boxes18to24

end BB6.Agent49Box18to24Bridge
