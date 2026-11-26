import Canonical64Raw120Integrated

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent31Canonical58Membership

open BB6Coverage BB6.Agent13BlankDelay BB6.Agent50TNFPilot
open BB6.Agent31FourHoleFrontier BB6.Agent31FourHoleRoster
open BB6.Agent47CanonicalFrontier BB6.Agent47CanonicalRefinement
open BB6.Agent31StableParentBatch

/-- The six source-certified E1 parents, expressed independently from their
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

/-- Raw113: E1 = 1RC. -/
abbrev p113 : PartialMachine :=
  refine e1Base (4,true) (some ⟨true,true,2⟩)

/-- Raw115: E1 = 0RD. -/
abbrev p115 : PartialMachine :=
  refine e1Base (4,true) (some ⟨false,true,3⟩)

/-- Raw119: E1 = 0RE. -/
abbrev p119 : PartialMachine :=
  refine e1Base (4,true) (some ⟨false,true,4⟩)

def parents : List PartialMachine := [p58,p59,p108,p113,p115,p119]

noncomputable def roster58 :=
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

theorem p113_count64 :
    (BB6.Agent3Canonical64Raw120.roster64.filter
      (fun e => sameTable e.2 p113)).length = 1 := by decide

theorem p115_count64 :
    (BB6.Agent3Canonical64Raw120.roster64.filter
      (fun e => sameTable e.2 p115)).length = 1 := by decide

theorem p119_count64 :
    (BB6.Agent3Canonical64Raw120.roster64.filter
      (fun e => sameTable e.2 p119)).length = 1 := by decide

/-- The six exact, distinct parent matches leave 58 representatives. -/
theorem count58 : roster58.length = 58 := by decide

theorem parents_root :
    ∀ p ∈ parents, p initialSlot = some (some ⟨true,true,1⟩) := by
  intro p hp
  simp only [parents, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> decide

#print axioms p58_count64
#print axioms p59_count64
#print axioms p108_count64
#print axioms p113_count64
#print axioms p115_count64
#print axioms p119_count64
#print axioms count58
#print axioms parents_root

end BB6.Agent31Canonical58Membership
