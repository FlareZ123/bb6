import Raw73Bound
import CanonicalRosterRefinement

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent21Raw73Cut
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent47CanonicalFrontier BB6.Agent47CanonicalRefinement

noncomputable def cut (roster : List (List Move × PartialMachine)) :=
  graftRoster BB6.Agent21Raw73.parent [] roster

theorem cut_sound {C : Nat} (hC : 7014 ≤ C)
    {root : PartialMachine} {roster : List (List Move × PartialMachine)}
    (hs : ∀ m, compatible root m → WeightedBound C m ∨
      ∃ e ∈ roster, TNFQuotientCompatible e.2 m) :
    ∀ m, compatible root m → WeightedBound C m ∨
      ∃ e ∈ cut roster, TNFQuotientCompatible e.2 m := by
  unfold cut
  apply graftRoster_sound BB6.Agent21Raw73.parent_root hs
  intro m hm
  exact Or.inl (fun k d hk hd =>
    Nat.le_trans (BB6.Agent21Raw73.all_completions m hm k d hk hd) hC)

theorem canonical_count : (cut canonicalRemainingRoster).length = 95 := by decide
#print axioms cut_sound
#print axioms canonical_count
end BB6.Agent21Raw73Cut
