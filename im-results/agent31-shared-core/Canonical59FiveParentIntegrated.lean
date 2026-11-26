import Canonical59FiveParentMembership
import Raw58Exact
import Raw59ParentCover
import Raw108Closed
import Raw115Data
import Raw119Data
import TM63RawUpperInterface
import ChampionScoreLowerBound

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent31Canonical59FiveParentIntegrated

open BB6Coverage BB6.Agent13BlankDelay BB6.Agent50TNFPilot
open BB6.Agent47CanonicalRefinement
open BB6.Agent31StableParentBatch
open BB6.Agent31Canonical59Membership
open BB6ChampionArithmetic

/-- The source-certified parent definitions are matched to the five exact
    table literals whose unique Canonical64 membership was preflighted. -/
abbrev p58Source : PartialMachine := BB6.Agent4Raw58SharpComposition.p58
abbrev p59Source : PartialMachine := BB6.Agent32Raw59.p59
abbrev p108Source : PartialMachine := BB6.Agent10Raw108Root.parent
abbrev p115Source : PartialMachine := BB6.Agent47Raw115.parent
abbrev p119Source : PartialMachine := BB6.Agent10Raw119.parent

theorem p58_source_eq : p58 = p58Source :=
  sameTable_sound (by decide)

theorem p59_source_eq : p59 = p59Source :=
  sameTable_sound (by decide)

theorem p108_source_eq : p108 = p108Source :=
  sameTable_sound (by decide)

theorem p115_source_eq : p115 = p115Source :=
  sameTable_sound (by decide)

theorem p119_source_eq : p119 = p119Source :=
  sameTable_sound (by decide)

/-- Raw58 has the accepted exact parent bound 3,055,746. -/
theorem p58_cover : Cover (WeightedBound 6766859) p58 := by
  rw [p58_source_eq]
  exact BB6.Agent4Raw58Exact.coverRaw58 6766859 (by decide)

/-- Raw59 uses the already accepted conservative parent bound 4,200,000;
    its sharper local search is unnecessary for this common floor. -/
theorem p59_cover : Cover (WeightedBound 6766859) p59 := by
  rw [p59_source_eq]
  exact liftCover (by decide) BB6.Agent32Raw59UpgradeAll.cover

/-- Raw108's source-accepted universal parent bound is 4,136,180. -/
theorem p108_cover : Cover (WeightedBound 6766859) p108 := by
  rw [p108_source_eq]
  refine Cover.leaf _ ?_
  intro m hm k d hk hd
  exact Nat.le_trans
    (BB6.Agent10Raw108Closed.all_closed m hm k d hk hd) (by decide)

/-- Raw115's complete source-accepted parent bound is 7,014. -/
theorem p115_cover : Cover (WeightedBound 6766859) p115 := by
  rw [p115_source_eq]
  refine Cover.leaf _ ?_
  intro m hm k d hk hd
  exact Nat.le_trans
    (BB6.Agent47Raw115.all_completions m hm k d hk hd) (by decide)

/-- Raw119's complete source-accepted parent bound is 572. -/
theorem p119_cover : Cover (WeightedBound 6766859) p119 := by
  rw [p119_source_eq]
  refine Cover.leaf _ ?_
  intro m hm k d hk hd
  exact Nat.le_trans
    (BB6.Agent10Raw119.all_completions m hm k d hk hd) (by decide)

/-- Every member of the five-parent list has its own independently accepted
    original-source Cover, lifted to the canonical common score floor. -/
theorem parents_cover :
    ∀ p ∈ parents, Cover (WeightedBound 6766859) p := by
  intro p hp
  simp only [parents, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl
  · exact p58_cover
  · exact p59_cover
  · exact p108_cover
  · exact p115_cover
  · exact p119_cover

/-- Directly consume the five certified E1 cylinders from the exact
    Canonical64 roster. No intermediate Canonical63/62 roster is introduced;
    every nonmatching quotient representative remains in roster59. -/
theorem sound59_integrated :
    ∀ m, compatible root m →
      WeightedBound 6766859 m ∨
        ∃ e ∈ roster59, TNFQuotientCompatible e.2 m := by
  apply removeParents_sound
    (parents := parents)
    (roster := BB6.Agent3Canonical64Raw120.roster64)
    BB6.Agent3Canonical64Raw120.sound64_integrated
    parents_root
    parents_cover

/-- Conditional exactness at any target above the champion score, assuming
    Covers only for the 59 exact retained Canonical64 representatives. -/
theorem exact_at_target (B : Nat) (hB : 6766859 ≤ B)
    (hLeaves : ∀ e ∈ roster59, Cover (WeightedBound B) e.2)
    (champ : ∃ m : BB6.Coverage.RawMachine,
      BB6.Coverage.HaltsAt (BB6.Coverage.tickRaw m) B) :
    BB6.Coverage.ExactBB6 B :=
  exact_from_quotient_roster (by omega) hB sound59_integrated hLeaves champ

/-- The existing source-accepted blank-start champion witness and score lower
    bound now give the fixed-score BB(6) consumer with 59 remaining Covers. -/
theorem exact_at_champion_score
    (hLeaves : ∀ e ∈ roster59,
      Cover (WeightedBound (proposedTM63Moves + 7)) e.2) :
    BB6.Coverage.ExactBB6 (proposedTM63Moves + 7) :=
  exact_at_target (proposedTM63Moves + 7)
    BB6.Agent38ChampionThreshold.champion_score_ge_6766859
    hLeaves
    BB6Coverage.Agent48DirectRoot.champion_raw_witness

#print axioms p58_source_eq
#print axioms p59_source_eq
#print axioms p108_source_eq
#print axioms p115_source_eq
#print axioms p119_source_eq
#print axioms p58_cover
#print axioms p59_cover
#print axioms p108_cover
#print axioms p115_cover
#print axioms p119_cover
#print axioms parents_cover
#print axioms sound59_integrated
#print axioms exact_at_target
#print axioms exact_at_champion_score

end BB6.Agent31Canonical59FiveParentIntegrated
