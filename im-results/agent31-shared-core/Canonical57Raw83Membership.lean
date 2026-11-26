import Raw83Canonical58Membership

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent31Canonical57Membership

open BB6.Agent31FourHoleFrontier BB6.Agent31FourHoleRoster
open BB6.Agent31StableParentBatch
open BB6.Agent31Canonical58Membership
open BB6.Agent29Raw83Canonical58Membership

/-- The source-accepted Raw83 four-hole parent in the exact quotient table
    language used by the accepted Canonical58 roster. -/
abbrev p83 : PartialMachine :=
  BB6.Agent29Raw83Canonical58Membership.p83

/-- Remove Raw83 from the already integrated 58-entry residual roster. -/
noncomputable def roster57 : List (Nat × PartialMachine) :=
  removeParents [p83] BB6.Agent31Canonical58Membership.roster58

/-- Raw83 occurs exactly once after the six existing parent removals. -/
theorem p83_count58 :
    (BB6.Agent31Canonical58Membership.roster58.filter
      (fun e => sameTable e.2 p83)).length = 1 :=
  BB6.Agent29Raw83Canonical58Membership.p83_exact_count58

/-- Raw83 is table-distinct from every one of the six integrated parents. -/
theorem p83_distinct_from_six :
    ∀ p ∈ BB6.Agent31Canonical58Membership.parents,
      sameTable p p83 = false :=
  BB6.Agent29Raw83Canonical58Membership.p83_exact_distinct_from_six

/-- The seven-parent sequential quotient has exactly 57 residual entries. -/
theorem count57 : roster57.length = 57 := by
  decide

theorem p83_root :
    p83 initialSlot = some (some ⟨true,true,1⟩) :=
  BB6.Agent29Raw83Canonical58Membership.p83_root

#print axioms p83_count58
#print axioms p83_distinct_from_six
#print axioms count57
#print axioms p83_root

end BB6.Agent31Canonical57Membership
