import Canonical64Raw120Integrated

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent31Canonical59Membership

open BB6Coverage BB6.Agent13BlankDelay BB6.Agent50TNFPilot
open BB6.Agent31FourHoleFrontier BB6.Agent31FourHoleRoster
open BB6.Agent47CanonicalFrontier BB6.Agent47CanonicalRefinement
open BB6.Agent31StableParentBatch

/-- The five source-certified E1 parents, expressed independently from their
    proof artifacts so their exact membership can be checked before any large
    parent closure is downloaded. All share the canonical first-one prefix. -/
abbrev e1Base : PartialMachine := (pathEnd root 2 (path.take 4)).1

/-- Raw58: E1 = 0RA. -/
abbrev p58 : PartialMachine :=
  refine e1Base (4,true) (some ⟨false,true,0⟩)

/-- Raw59: E1 = 1LA. -/
abbrev p59 : PartialMachine :=
  refine e1Base (4,true) (some ⟨true,false,0⟩)

/-- Raw108: E1 = 1LB. -/
abbrev p108 : PartialMachine :=
  refine e1Base (4,true) (some ⟨true,false,1⟩)

/-- Raw115: E1 = 0RD. -/
abbrev p115 : PartialMachine :=
  refine e1Base (4,true) (some ⟨false,true,3⟩)

/-- Raw119: E1 = 0RE. -/
abbrev p119 : PartialMachine :=
  refine e1Base (4,true) (some ⟨false,true,4⟩)

/-- Raw113: E1 = 1RC. This candidate is checked separately from the five
    parents defining roster59. -/
abbrev p113 : PartialMachine :=
  refine e1Base (4,true) (some ⟨true,true,2⟩)

def parents : List PartialMachine := [p58,p59,p108,p115,p119]

noncomputable def roster59 :=
  removeParents parents BB6.Agent3Canonical64Raw120.roster64

/-- Each proposed parent occurs exactly once in the accepted Canonical64
    roster. These are exact table-membership checks, not index guesses. -/
theorem p58_count64 :
    (BB6.Agent3Canonical64Raw120.roster64.filter
      (fun e => sameTable e.2 p58)).length = 1 := by decide

theorem p59_count64 :
    (BB6.Agent3Canonical64Raw120.roster64.filter
      (fun e => sameTable e.2 p59)).length = 1 := by decide

theorem p108_count64 :
    (BB6.Agent3Canonical64Raw120.roster64.filter
      (fun e => sameTable e.2 p108)).length = 1 := by decide

theorem p115_count64 :
    (BB6.Agent3Canonical64Raw120.roster64.filter
      (fun e => sameTable e.2 p115)).length = 1 := by decide

theorem p119_count64 :
    (BB6.Agent3Canonical64Raw120.roster64.filter
      (fun e => sameTable e.2 p119)).length = 1 := by decide

/-- Raw113 is a unique exact member of Canonical64. -/
theorem p113_count64 :
    (BB6.Agent3Canonical64Raw120.roster64.filter
      (fun e => sameTable e.2 p113)).length = 1 := by decide

theorem p113_root :
    p113 initialSlot = some (some ⟨true,true,1⟩) := by decide

/-- The five exact, distinct parent matches leave 59 representatives. -/
theorem count59 : roster59.length = 59 := by decide

theorem parents_root :
    ∀ p ∈ parents, p initialSlot = some (some ⟨true,true,1⟩) := by
  intro p hp
  simp only [parents, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl <;> decide

#print axioms p58_count64
#print axioms p59_count64
#print axioms p108_count64
#print axioms p115_count64
#print axioms p119_count64
#print axioms p113_count64
#print axioms p113_root
#print axioms count59
#print axioms parents_root

end BB6.Agent31Canonical59Membership
