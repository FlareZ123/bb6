import Canonical53FourSharpAfterRaw124
import Raw106ParentCover
import Raw79ParentCover
import A10Raw83Exact
import Raw85Bound
import Raw69Bound
import Raw73Bound
import Raw78Bound

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent2Canonical46SevenReady

open BB6Coverage BB6.Agent13BlankDelay BB6.Agent50TNFPilot
open BB6.Agent31FourHoleFrontier BB6.Agent31FourHoleRoster
open BB6.Agent47CanonicalFrontier BB6.Agent47CanonicalRefinement
open BB6.Agent31StableParentBatch
open BB6ChampionArithmetic

abbrev p106 : PartialMachine := BB6.Agent10Raw106.p106
abbrev p79 : PartialMachine := BB6.Agent10Raw79.p79
abbrev p83 : PartialMachine := BB6.Agent10Raw83.parent
abbrev p85 : PartialMachine := BB6.Agent21Raw85.parent
abbrev p69 : PartialMachine := BB6.Agent21Raw69.parent
abbrev p73 : PartialMachine := BB6.Agent21Raw73.parent
abbrev p78 : PartialMachine := BB6.Agent21Raw78.parent

abbrev readyParents : List PartialMachine :=
  [p106, p79, p83, p85, p69, p73, p78]

theorem p106_count53 :
    (BB6.Agent2Canonical53FourSharp.roster53.filter
      (fun e => sameTable e.2 p106)).length = 1 := by decide
theorem p79_count53 :
    (BB6.Agent2Canonical53FourSharp.roster53.filter
      (fun e => sameTable e.2 p79)).length = 1 := by decide
theorem p83_count53 :
    (BB6.Agent2Canonical53FourSharp.roster53.filter
      (fun e => sameTable e.2 p83)).length = 1 := by decide
theorem p85_count53 :
    (BB6.Agent2Canonical53FourSharp.roster53.filter
      (fun e => sameTable e.2 p85)).length = 1 := by decide
theorem p69_count53 :
    (BB6.Agent2Canonical53FourSharp.roster53.filter
      (fun e => sameTable e.2 p69)).length = 1 := by decide
theorem p73_count53 :
    (BB6.Agent2Canonical53FourSharp.roster53.filter
      (fun e => sameTable e.2 p73)).length = 1 := by decide
theorem p78_count53 :
    (BB6.Agent2Canonical53FourSharp.roster53.filter
      (fun e => sameTable e.2 p78)).length = 1 := by decide

theorem parents_pairwise_distinct :
    List.Pairwise (fun p q => sameTable p q = false) readyParents := by decide

theorem p106_root :
    p106 initialSlot = some (some ⟨true,true,1⟩) :=
  BB6.Agent10Raw106.p106_root
theorem p79_root :
    p79 initialSlot = some (some ⟨true,true,1⟩) :=
  BB6.Agent10Raw79.p79_root
theorem p83_root :
    p83 initialSlot = some (some ⟨true,true,1⟩) := by decide
theorem p85_root :
    p85 initialSlot = some (some ⟨true,true,1⟩) :=
  BB6.Agent21Raw85.parent_root
theorem p69_root :
    p69 initialSlot = some (some ⟨true,true,1⟩) :=
  BB6.Agent21Raw69.parent_root
theorem p73_root :
    p73 initialSlot = some (some ⟨true,true,1⟩) :=
  BB6.Agent21Raw73.parent_root
theorem p78_root :
    p78 initialSlot = some (some ⟨true,true,1⟩) :=
  BB6.Agent21Raw78.parent_root

theorem p106_cover : Cover (WeightedBound 6766859) p106 := by
  apply Cover.leaf
  intro m hm k d hk hd
  exact Nat.le_trans
    (BB6.Agent10Raw106.parent_cover.sound m hm k d hk hd)
    (by decide : 253 ≤ 6766859)

theorem p79_cover : Cover (WeightedBound 6766859) p79 := by
  apply Cover.leaf
  intro m hm k d hk hd
  exact Nat.le_trans
    (BB6.Agent10Raw79.parent_cover.sound m hm k d hk hd)
    (by decide : 2354 ≤ 6766859)

theorem p83_cover : Cover (WeightedBound 6766859) p83 := by
  apply Cover.leaf
  intro m hm k d hk hd
  exact Nat.le_trans
    (BB6.Agent10Raw83.all_completions m hm k d hk hd)
    (by decide : 514 ≤ 6766859)

theorem p85_cover : Cover (WeightedBound 6766859) p85 := by
  apply Cover.leaf
  intro m hm k d hk hd
  exact Nat.le_trans
    (BB6.Agent21Raw85.all_completions m hm k d hk hd)
    (by decide : 7014 ≤ 6766859)

theorem p69_cover : Cover (WeightedBound 6766859) p69 := by
  apply Cover.leaf
  intro m hm k d hk hd
  exact Nat.le_trans
    (BB6.Agent21Raw69.all_completions m hm k d hk hd)
    (by decide : 7014 ≤ 6766859)

theorem p73_cover : Cover (WeightedBound 6766859) p73 := by
  apply Cover.leaf
  intro m hm k d hk hd
  exact Nat.le_trans
    (BB6.Agent21Raw73.all_completions m hm k d hk hd)
    (by decide : 7014 ≤ 6766859)

theorem p78_cover : Cover (WeightedBound 6766859) p78 := by
  apply Cover.leaf
  intro m hm k d hk hd
  exact Nat.le_trans
    (BB6.Agent21Raw78.all_completions m hm k d hk hd)
    (by decide : 7014 ≤ 6766859)

theorem parents_root :
    ∀ p ∈ readyParents, p initialSlot = some (some ⟨true,true,1⟩) := by
  intro p hp
  simp only [readyParents, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact p106_root
  · exact p79_root
  · exact p83_root
  · exact p85_root
  · exact p69_root
  · exact p73_root
  · exact p78_root

theorem parents_cover :
    ∀ p ∈ readyParents, Cover (WeightedBound 6766859) p := by
  intro p hp
  simp only [readyParents, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact p106_cover
  · exact p79_cover
  · exact p83_cover
  · exact p85_cover
  · exact p69_cover
  · exact p73_cover
  · exact p78_cover

noncomputable def roster46 :=
  removeParents readyParents BB6.Agent2Canonical53FourSharp.roster53

theorem count46 : roster46.length = 46 := by decide

theorem all_ready_parents_removed :
    ∀ p ∈ readyParents,
      (roster46.filter (fun e => sameTable e.2 p)).length = 0 := by
  intro p hp
  simp only [readyParents, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem raw59_retained :
    (roster46.filter
      (fun e => sameTable e.2 BB6.Agent31Canonical59Membership.p59)).length = 1 := by
  decide

theorem sound_integrated :
    ∀ m, compatible root m →
      WeightedBound 6766859 m ∨
        ∃ e ∈ roster46, TNFQuotientCompatible e.2 m := by
  apply removeParents_sound (parents := readyParents)
    (roster := BB6.Agent2Canonical53FourSharp.roster53)
    BB6.Agent2Canonical53FourSharp.sound_integrated
    parents_root parents_cover

theorem exact_at_target (B : Nat) (hB : 6766859 ≤ B)
    (hLeaves : ∀ e ∈ roster46, Cover (WeightedBound B) e.2)
    (champ : ∃ m : BB6.Coverage.RawMachine,
      BB6.Coverage.HaltsAt (BB6.Coverage.tickRaw m) B) :
    BB6.Coverage.ExactBB6 B :=
  exact_from_quotient_roster (by omega) hB sound_integrated hLeaves champ

theorem exact_at_champion_score
    (hLeaves : ∀ e ∈ roster46,
      Cover (WeightedBound (proposedTM63Moves + 7)) e.2) :
    BB6.Coverage.ExactBB6 (proposedTM63Moves + 7) :=
  exact_at_target (proposedTM63Moves + 7)
    BB6.Agent38ChampionThreshold.champion_score_ge_6766859
    hLeaves
    BB6Coverage.Agent48DirectRoot.champion_raw_witness

#print axioms p106_count53
#print axioms p79_count53
#print axioms p83_count53
#print axioms p85_count53
#print axioms p69_count53
#print axioms p73_count53
#print axioms p78_count53
#print axioms parents_pairwise_distinct
#print axioms p106_cover
#print axioms p79_cover
#print axioms p83_cover
#print axioms p85_cover
#print axioms p69_cover
#print axioms p73_cover
#print axioms p78_cover
#print axioms count46
#print axioms all_ready_parents_removed
#print axioms raw59_retained
#print axioms sound_integrated
#print axioms exact_at_target
#print axioms exact_at_champion_score

end BB6.Agent2Canonical46SevenReady
