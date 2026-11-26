import Raw40A1RCBase
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent19Raw40.RootCut
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent31ThreeHole BB6.Agent10ZipAudit BB6.Agent48PrefixAudit BB6.Agent47PartialAudit BB6.Agent19CanonicalPartial BB6.Agent47CanonicalFrontier BB6.Agent50TNFPilot

/-- The original seven-hole Raw40 parent, before A1 is assigned. -/
def p : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,false,0⟩)
  | _,_ => none

def tree : PartialAudit := .split 6 (0,true) (byPartialMove [
  .unresolved,
  .unresolved,
  .closed (.cycle 8 1 false (0)),
  .closed (.cycle 7 1 false (-1)),
  .unresolved,
  .unresolved,
  .closed (.cycle 0 10 true (0)),
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
  .closed (.cycle 0 10 true (0)),
  .unresolved,
  .unresolved,
  .closed (.cycle 5 2 true (0)),
  .unresolved,
  .unresolved])

theorem root : p initialSlot = some (some ⟨true,true,1⟩) := by decide
theorem nohalt : weightedTNFNoAssignedHalt p := by
  intro s; rcases s with ⟨q,b⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> cases b <;> decide
theorem supported : TNFSupport p 4 := supportOK_sound _ _ (by decide)
theorem checked : canonicalCheck 5729 p 4 tree = true := by decide

def before := canonicalResiduals p 4 tree
def remaining := before.filter fun e => !(A1RC.equalTable e.2 A1RC.p)
theorem before_count : before.length = 14 := by decide
theorem remaining_count : remaining.length = 13 := by decide

theorem root_entries : remaining.all (fun e => decide (e.2 initialSlot = some (some ⟨true,true,1⟩))) = true := by decide

/-- Exactly one of the fourteen six-hole canonical children is eliminated by the A1RC proof. -/
theorem sound (hRC : ∀ m, TNFQuotientCompatible A1RC.p m → WeightedBound 5729 m) :
    ∀ m, TNFQuotientCompatible p m → WeightedBound 5729 m ∨ ∃ e ∈ remaining, TNFQuotientCompatible e.2 m := by
  intro m hm
  rcases canonicalSound 5729 p 4 tree (by decide) supported root nohalt checked m hm with hb | ⟨e,he,hq⟩
  · exact Or.inl hb
  · by_cases h : A1RC.equalTable e.2 A1RC.p = true
    · exact Or.inl (hRC m (A1RC.equalTable_sound _ _ h ▸ hq))
    · exact Or.inr ⟨e,by simp [remaining,before,he,h],hq⟩

/-- The remaining thirteen covers are exactly the obligations of this coarse Raw40 cut. -/
theorem cover {B : Nat} (hB : 5729 ≤ B)
    (hRC : ∀ m, TNFQuotientCompatible A1RC.p m → WeightedBound 5729 m)
    (hRest : ∀ e ∈ remaining, Cover (WeightedBound B) e.2) : Cover (WeightedBound B) p := by
  apply Cover.leaf
  intro m hm
  rcases sound hRC m (compatible_quotient hm) with hb | ⟨e,he,hq⟩
  · intro k d hk hd; exact Nat.le_trans (hb k d hk hd) hB
  · have hf := of_decide_eq_true (List.all_eq_true.mp root_entries e he)
    exact quotientSafe hf (hRest e he).sound m hq

#print axioms remaining_count
#print axioms sound
#print axioms cover
end BB6.Agent19Raw40.RootCut
