import Canonical38Raw39Raw47Direct
import A10Raw83Exact

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-!
Serial successor of the authenticated direct Raw39+Raw47 Canonical38 lineage.
Raw83 is independently source-accepted at exact weighted maximum 514; this
module checks its exact membership in that concrete 38-roster, consumes its
Cover, and leaves exactly 37 quotient Cover obligations.
-/

namespace BB6.Agent11Canonical37Raw83

open BB6Coverage BB6.Agent13BlankDelay BB6.Agent50TNFPilot
open BB6.Agent31FourHoleFrontier BB6.Agent31FourHoleRoster
open BB6.Agent31StableParentBatch
open BB6ChampionArithmetic

abbrev p83 : PartialMachine :=
  refine (pathEnd root 2 (path.take 6)).1 (5,true) (some ⟨false,true,0⟩)

noncomputable abbrev baseRoster :=
  BB6.Agent3Canonical38Raw39Raw47Direct.roster38

noncomputable def roster37 : List (Nat × PartialMachine) :=
  removeParents [p83] baseRoster

theorem p83_root :
    p83 initialSlot = some (some ⟨true,true,1⟩) := by
  decide

theorem p83_count38 :
    (baseRoster.filter (fun e => sameTable e.2 p83)).length = 1 := by
  decide

theorem count37 : roster37.length = 37 := by
  decide

theorem p83_removed :
    (roster37.filter (fun e => sameTable e.2 p83)).length = 0 := by
  decide

theorem p83_source_eq : p83 = BB6.Agent10Raw83.parent :=
  sameTable_sound (by decide)

theorem p83_cover_at_champion :
    Cover (WeightedBound (proposedTM63Moves + 7)) p83 := by
  rw [p83_source_eq]
  refine Cover.leaf _ ?_
  intro m hm k d hk hd
  exact Nat.le_trans
    (BB6.Agent10Raw83.all_completions m hm k d hk hd) (by omega)

theorem parents_root :
    ∀ p ∈ [p83], p initialSlot = some (some ⟨true,true,1⟩) := by
  intro p hp
  simp only [List.mem_singleton] at hp
  subst p
  exact p83_root

theorem parents_cover :
    ∀ p ∈ [p83],
      Cover (WeightedBound (proposedTM63Moves + 7)) p := by
  intro p hp
  simp only [List.mem_singleton] at hp
  subst p
  exact p83_cover_at_champion

theorem sound37_at_champion :
    ∀ m, compatible root m →
      WeightedBound (proposedTM63Moves + 7) m ∨
        ∃ e ∈ roster37, TNFQuotientCompatible e.2 m := by
  apply removeParents_sound (parents := [p83]) (roster := baseRoster)
    BB6.Agent3Canonical38Raw39Raw47Direct.sound38_at_champion
    parents_root parents_cover

theorem exact_at_champion_score
    (hLeaves : ∀ e ∈ roster37,
      Cover (WeightedBound (proposedTM63Moves + 7)) e.2) :
    BB6.Coverage.ExactBB6 (proposedTM63Moves + 7) :=
  exact_from_quotient_roster (by omega) (Nat.le_refl _)
    sound37_at_champion hLeaves
    BB6Coverage.Agent48DirectRoot.champion_raw_witness

#print axioms p83_root
#print axioms p83_count38
#print axioms count37
#print axioms p83_removed
#print axioms p83_source_eq
#print axioms p83_cover_at_champion
#print axioms sound37_at_champion
#print axioms exact_at_champion_score

end BB6.Agent11Canonical37Raw83
