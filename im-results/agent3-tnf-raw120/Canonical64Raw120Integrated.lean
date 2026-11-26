import Canonical65Integrated
import Raw120Complete
import Raw120ExactLower

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent3Canonical64Raw120
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent50TNFPilot
open BB6.Agent31FourHoleFrontier BB6.Agent31FourHoleRoster
open BB6.Agent47CanonicalFrontier BB6.Agent47CanonicalRefinement
open BB6.Agent31StableParentBatch BB6.Agent31Canonical65AfterThree

abbrev p120 := BB6.Agent3Raw120.p120

/-- Sharp weighted parent bound, including incoming blank delay and halt tick. -/
theorem raw120_exact (T : Nat) :
    (∀ m, compatible p120 m → WeightedBound T m) ↔ 224707 ≤ T := by
  constructor
  · exact BB6.Agent3Raw120ExactLower.raw120_lower T
  · intro h m hm k d hk hd
    exact Nat.le_trans (BB6.Agent3Raw120Complete.allRaw120 m hm k d hk hd) h

theorem p120_root :
    p120 initialSlot = some (some ⟨true,true,1⟩) := by decide

theorem p120_count :
    (roster65.filter (fun e => sameTable e.2 p120)).length = 1 := by decide

noncomputable def roster64 := removeParents [p120] roster65

theorem count64 : roster64.length = 64 := by decide

theorem sound64_integrated :
    ∀ m, compatible root m →
      WeightedBound 6766859 m ∨
        ∃ e ∈ roster64, TNFQuotientCompatible e.2 m := by
  apply removeParents_sound (parents := [p120]) (roster := roster65)
    BB6.Agent31Canonical65Integrated.sound65_integrated
  · intro p hp
    simp only [List.mem_singleton] at hp
    subst p
    exact p120_root
  · intro p hp
    simp only [List.mem_singleton] at hp
    subst p
    exact BB6.Agent3Raw120Complete.coverRaw120 6766859 (by decide)

/-- The remaining 64 quotient Covers and attaining witness are explicit. -/
theorem exact_at_target (B : Nat) (hB : 6766859 ≤ B)
    (hLeaves : ∀ e ∈ roster64, Cover (WeightedBound B) e.2)
    (champ : ∃ m : BB6.Coverage.RawMachine,
      BB6.Coverage.HaltsAt (BB6.Coverage.tickRaw m) B) :
    BB6.Coverage.ExactBB6 B :=
  exact_from_quotient_roster (by omega) hB sound64_integrated hLeaves champ

#print axioms raw120_exact
#print axioms p120_root
#print axioms p120_count
#print axioms count64
#print axioms sound64_integrated
#print axioms exact_at_target

end BB6.Agent3Canonical64Raw120
