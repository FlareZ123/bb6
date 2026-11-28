import Raw83Raw85Canonical37AfterRaw39
import Raw112ClosedCover

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-!
Source-level successor for the authentic accepted Canonical39 lineage:
after independently source-consuming whole parents Raw83 and Raw85, consume
the complete Raw112 six-hole parent at weighted bound 100000. This source
is only staged; a 36-residual claim requires an authenticated source run.
-/

namespace BB6.Agent9Raw83Raw85Raw112Canonical36AfterRaw39

open BB6Coverage BB6.Agent13BlankDelay BB6.Agent50TNFPilot
open BB6.Agent31FourHoleFrontier BB6.Agent31FourHoleRoster
open BB6.Agent47CanonicalFrontier BB6.Agent47CanonicalRefinement
open BB6.Agent31StableParentBatch
open BB6ChampionArithmetic

noncomputable abbrev baseRoster :=
  BB6.Agent9Raw83Raw85Canonical37AfterRaw39.roster37
abbrev p112 : PartialMachine := BB6.Agent47Raw112.parent
abbrev removedParents : List PartialMachine := [p112]

theorem p112_count37 :
    (baseRoster.filter (fun e => sameTable e.2 p112)).length = 1 := by decide

theorem p112_root :
    p112 initialSlot = some (some ⟨true,true,1⟩) := by decide

theorem p112_cover :
    Cover (WeightedBound 6766859) p112 := by
  apply Cover.leaf
  intro m hm k d hk hd
  exact Nat.le_trans
    (BB6.Agent47Raw112.parent_cover.sound m hm k d hk hd)
    (by decide : 100000 ≤ 6766859)

theorem parents_root :
    ∀ p ∈ removedParents,
      p initialSlot = some (some ⟨true,true,1⟩) := by
  intro p hp
  have he : p = p112 := by simpa [removedParents] using hp
  subst p
  exact p112_root

theorem parents_cover :
    ∀ p ∈ removedParents, Cover (WeightedBound 6766859) p := by
  intro p hp
  have he : p = p112 := by simpa [removedParents] using hp
  subst p
  exact p112_cover

noncomputable def roster36 := removeParents removedParents baseRoster

theorem count36 : roster36.length = 36 := by decide

theorem raw112_removed :
    (roster36.filter (fun e => sameTable e.2 p112)).length = 0 := by decide

theorem sound_integrated :
    ∀ m, compatible root m →
      WeightedBound 6766859 m ∨
        ∃ e ∈ roster36, TNFQuotientCompatible e.2 m := by
  apply removeParents_sound (parents := removedParents)
    (roster := baseRoster)
    BB6.Agent9Raw83Raw85Canonical37AfterRaw39.sound_integrated
    parents_root parents_cover

theorem exact_at_champion_score
    (hLeaves : ∀ e ∈ roster36,
      Cover (WeightedBound (proposedTM63Moves + 7)) e.2) :
    BB6.Coverage.ExactBB6 (proposedTM63Moves + 7) :=
  exact_from_quotient_roster (by omega)
    BB6.Agent38ChampionThreshold.champion_score_ge_6766859
    sound_integrated hLeaves
    BB6Coverage.Agent48DirectRoot.champion_raw_witness

#print axioms p112_count37
#print axioms p112_cover
#print axioms count36
#print axioms raw112_removed
#print axioms sound_integrated
#print axioms exact_at_champion_score

end BB6.Agent9Raw83Raw85Raw112Canonical36AfterRaw39
