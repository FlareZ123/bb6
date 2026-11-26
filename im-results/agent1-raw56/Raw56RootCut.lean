import CanonicalPartial
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent1Raw56Root
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent31ThreeHole BB6.Agent10ZipAudit
open BB6.Agent48PrefixAudit BB6.Agent47PartialAudit BB6.Agent19CanonicalPartial
open BB6.Agent47CanonicalFrontier BB6.Agent50TNFPilot BB6.Agent31FourHoleRoster

/-- The authentic seven-hole D1=1LE sibling. -/
def parent : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,false,4⟩)
  | _,_ => none

def e1RE : PartialMachine := refine parent (4,true) (some ⟨false,true,4⟩)

theorem parent_root : parent initialSlot = some (some ⟨true,true,1⟩) := by decide
theorem parent_nohalt : weightedTNFNoAssignedHalt parent := by
  intro s; rcases s with ⟨q,b⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> cases b <;> decide
theorem parent_support : TNFSupport parent 5 := supportOK_sound _ _ (by decide)

def rootTree : PartialAudit := .split 6 (4,true) (byPartialMove [
  .unresolved,
  .unresolved,
  .closed (.cycle 8 1 false 0),
  .closed (.cycle 7 1 false (-1)),
  .unresolved,
  .unresolved,
  .unresolved,
  .unresolved,
  .unresolved,
  .unresolved,
  .unresolved,
  .unresolved,
  .unresolved,
  .unresolved,
  .unresolved,
  .closed (.cycle 7 1 false (-1)),
  .unresolved,
  .unresolved,
  .unresolved,
  .unresolved,
  .unresolved,
  .closed (.cycle 5 2 true 0),
  .unresolved,
  .unresolved
])

theorem checked : canonicalCheck 7014 parent 5 rootTree = true := by decide
def remaining20 := canonicalResiduals parent 5 rootTree
theorem count20 : remaining20.length = 20 := by decide

/-- The first undefined query and all four cycle branches are checked against
the original machine semantics. The other twenty ordinary assignments are explicit. -/
theorem sound20 : ∀ m, TNFQuotientCompatible parent m →
    WeightedBound 7014 m ∨ ∃ e ∈ remaining20, TNFQuotientCompatible e.2 m :=
  canonicalSound 7014 parent 5 rootTree (by decide) parent_support parent_root parent_nohalt checked

def remaining19 := remaining20.filter (fun e => !sameTable e.2 e1RE)
theorem count19 : remaining19.length = 19 := by decide

/-- Consume exactly the E1=0RE child, preserving the other nineteen
canonical representatives. This theorem is conditional on the child proof. -/
theorem sound19 (hRE : ∀ m, TNFQuotientCompatible e1RE m → WeightedBound 7014 m) :
    ∀ m, TNFQuotientCompatible parent m →
      WeightedBound 7014 m ∨ ∃ e ∈ remaining19, TNFQuotientCompatible e.2 m := by
  intro m hm
  rcases sound20 m hm with hb | ⟨e,he,hq⟩
  · exact Or.inl hb
  · by_cases hmatch : sameTable e.2 e1RE = true
    · have heq : e.2 = e1RE := sameTable_sound hmatch
      exact Or.inl (hRE m (heq ▸ hq))
    · exact Or.inr ⟨e,List.mem_filter.mpr ⟨he,by simp [hmatch]⟩,hq⟩

#print axioms checked
#print axioms count20
#print axioms sound20
#print axioms count19
#print axioms sound19
end BB6.Agent1Raw56Root
