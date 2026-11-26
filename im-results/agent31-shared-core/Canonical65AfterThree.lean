import Canonical68StableBatch
import Raw71Data
import Raw77Data
import Raw81Data

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent31Canonical65AfterThree
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent50TNFPilot
open BB6.Agent47CanonicalFrontier BB6.Agent47CanonicalRefinement
open BB6.Agent31StableParentBatch

abbrev p71 := BB6.Agent10Raw71.p71
abbrev p77 := BB6.Agent10Raw77.p77
abbrev p81 := BB6.Agent10Raw81.p81

def extraParents : List PartialMachine := [p71, p77, p81]

theorem extra_roots : ∀ p ∈ extraParents, p initialSlot = some (some ⟨true,true,1⟩) := by
  intro p hp
  simp only [extraParents, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl
  · exact BB6.Agent10Raw71.p71_root
  · exact BB6.Agent10Raw77.p77_root
  · exact BB6.Agent10Raw81.p81_root

theorem extra_covers {B : Nat} (hB : 7014 ≤ B) :
    ∀ p ∈ extraParents, Cover (WeightedBound B) p := by
  intro p hp
  simp only [extraParents, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl
  · exact liftCover (by omega) (Cover.leaf _ BB6.Agent10Raw71.all71)
  · exact liftCover hB (Cover.leaf _ BB6.Agent10Raw77.all77)
  · exact liftCover hB (Cover.leaf _ BB6.Agent10Raw81.all81)

noncomputable def roster65 := removeParents extraParents roster68

theorem count65 : roster65.length = 65 := by decide

/-- Consume the three independently proved five-hole parents on the actual
68 roster. This takes the preceding dichotomy as an explicit premise and
does not import the other eight generated certificate closures. -/
theorem sound65 {B : Nat} (hB : 7014 ≤ B)
    (h68 : ∀ m, compatible root m → WeightedBound B m ∨
      ∃ e ∈ roster68, TNFQuotientCompatible e.2 m) :
    ∀ m, compatible root m → WeightedBound B m ∨
      ∃ e ∈ roster65, TNFQuotientCompatible e.2 m :=
  removeParents_sound h68 extra_roots (extra_covers hB)

theorem exact_at_target (B : Nat) (hB : 7014 ≤ B)
    (h68 : ∀ m, compatible root m → WeightedBound B m ∨
      ∃ e ∈ roster68, TNFQuotientCompatible e.2 m)
    (hLeaves : ∀ e ∈ roster65, Cover (WeightedBound B) e.2)
    (champ : ∃ m : BB6.Coverage.RawMachine,
      BB6.Coverage.HaltsAt (BB6.Coverage.tickRaw m) B) :
    BB6.Coverage.ExactBB6 B :=
  exact_from_quotient_roster (by omega) (Nat.le_refl B)
    (sound65 hB h68) hLeaves champ

#print axioms extra_roots
#print axioms extra_covers
#print axioms count65
#print axioms sound65
#print axioms exact_at_target

end BB6.Agent31Canonical65AfterThree
