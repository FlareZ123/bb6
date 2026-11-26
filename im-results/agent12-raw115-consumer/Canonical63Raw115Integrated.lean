import Canonical64Raw120Integrated
import Raw115Data

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent12Canonical63Raw115
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent50TNFPilot
open BB6.Agent31FourHoleFrontier BB6.Agent31FourHoleRoster
open BB6.Agent47CanonicalFrontier BB6.Agent47CanonicalRefinement
open BB6.Agent31StableParentBatch BB6.Agent31Canonical65AfterThree
open BB6.Agent3Canonical64Raw120

abbrev p115 := BB6.Agent47Raw115.parent

theorem cover115 (B : Nat) (hB : 7014 ≤ B) :
    Cover (WeightedBound B) p115 :=
  Cover.leaf _ (fun m hm k d hk hd =>
    Nat.le_trans (BB6.Agent47Raw115.all_completions m hm k d hk hd) hB)

theorem p115_root :
    p115 initialSlot = some (some ⟨true,true,1⟩) :=
  BB6.Agent47Raw115.parent_root

theorem p115_count :
    (roster64.filter (fun e => sameTable e.2 p115)).length = 1 := by decide

noncomputable def roster63 := removeParents [p115] roster64

theorem count63 : roster63.length = 63 := by decide

theorem sound63_integrated :
    ∀ m, compatible root m →
      WeightedBound 6766859 m ∨
        ∃ e ∈ roster63, TNFQuotientCompatible e.2 m := by
  apply removeParents_sound (parents := [p115]) (roster := roster64)
    sound64_integrated
  · intro p hp
    simp only [List.mem_singleton] at hp
    subst p
    exact p115_root
  · intro p hp
    simp only [List.mem_singleton] at hp
    subst p
    exact cover115 6766859 (by decide)

theorem exact_at_target (B : Nat) (hB : 6766859 ≤ B)
    (hLeaves : ∀ e ∈ roster63, Cover (WeightedBound B) e.2)
    (champ : ∃ m : BB6.Coverage.RawMachine,
      BB6.Coverage.HaltsAt (BB6.Coverage.tickRaw m) B) :
    BB6.Coverage.ExactBB6 B :=
  exact_from_quotient_roster (by omega) hB sound63_integrated hLeaves champ

#print axioms cover115
#print axioms p115_root
#print axioms p115_count
#print axioms count63
#print axioms sound63_integrated
#print axioms exact_at_target

end BB6.Agent12Canonical63Raw115
