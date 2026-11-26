import Canonical64Raw120Integrated
import Canonical68StableBatch
import Raw112ClosedCover
import Raw58Exact

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent4Canonical62Raw112Raw58

open BB6Coverage BB6.Agent13BlankDelay BB6.Agent50TNFPilot
open BB6.Agent31StableParentBatch
open BB6.Agent3Canonical64Raw120
open BB6.Agent31FourHoleFrontier BB6.Agent31FourHoleRoster
open BB6.Agent47CanonicalFrontier BB6.Agent47CanonicalRefinement

/-- The independently source-audited Raw112 parent. -/
abbrev p112 : PartialMachine := BB6.Agent47Raw112.parent

/-- The independently source-audited Raw58 E1=0RA parent. -/
abbrev p58 : PartialMachine := BB6.Agent4Raw58SharpComposition.p58

/-- Both parents are removed simultaneously from the exact accepted
    Canonical64 roster, avoiding a competing 63-entry intermediate roster. -/
def parents : List PartialMachine := [p112, p58]

noncomputable def roster62 := removeParents parents roster64

theorem p112_root :
    p112 initialSlot = some (some ⟨true,true,1⟩) := by
  decide

theorem p58_root :
    p58 initialSlot = some (some ⟨true,true,1⟩) := by
  decide

theorem parents_distinct : p112 ≠ p58 := by
  decide

theorem p112_count :
    (roster64.filter (fun e => sameTable e.2 p112)).length = 1 := by
  decide

theorem p58_count :
    (roster64.filter (fun e => sameTable e.2 p58)).length = 1 := by
  decide

theorem count62 : roster62.length = 62 := by
  decide

theorem parents_root :
    ∀ p ∈ parents, p initialSlot = some (some ⟨true,true,1⟩) := by
  intro p hp
  simp only [parents, List.mem_cons, List.mem_singleton] at hp
  rcases hp with h | h
  · cases h
    exact p112_root
  · cases h
    exact p58_root

/-- Lift the independently accepted Raw112 parent Cover to the common
    Canonical64 weighted floor. -/
theorem raw112_cover : Cover (WeightedBound 6766859) p112 :=
  liftCover (by decide) BB6.Agent47Raw112.parent_cover

/-- Lift the sharp Raw58 parent Cover to the same common weighted floor. -/
theorem raw58_cover : Cover (WeightedBound 6766859) p58 :=
  liftCover (by decide)
    (BB6.Agent4Raw58Exact.coverRaw58 3055746 (by decide))

theorem parents_cover :
    ∀ p ∈ parents, Cover (WeightedBound 6766859) p := by
  intro p hp
  simp only [parents, List.mem_cons, List.mem_singleton] at hp
  rcases hp with h | h
  · cases h
    exact raw112_cover
  · cases h
    exact raw58_cover

/-- The two independently certified parent cylinders are consumed in one
    quotient-preserving step from the accepted Canonical64 theorem. -/
theorem sound62_integrated :
    ∀ m, compatible root m →
      WeightedBound 6766859 m ∨
        ∃ e ∈ roster62, TNFQuotientCompatible e.2 m := by
  exact removeParents_sound
    (parents := parents)
    (roster := roster64)
    sound64_integrated
    parents_root
    parents_cover

/-- Generic exactness interface: only the 62 retained quotient Covers and an
    attaining blank-start witness remain as hypotheses. -/
theorem exact_at_target62 (B : Nat) (hB : 6766859 ≤ B)
    (hLeaves : ∀ e ∈ roster62, Cover (WeightedBound B) e.2)
    (champ : ∃ m : BB6.Coverage.RawMachine,
      BB6.Coverage.HaltsAt (BB6.Coverage.tickRaw m) B) :
    BB6.Coverage.ExactBB6 B :=
  exact_from_quotient_roster (by omega) hB sound62_integrated hLeaves champ

#print axioms p112_root
#print axioms p58_root
#print axioms parents_distinct
#print axioms p112_count
#print axioms p58_count
#print axioms count62
#print axioms raw112_cover
#print axioms raw58_cover
#print axioms sound62_integrated
#print axioms exact_at_target62

end BB6.Agent4Canonical62Raw112Raw58
