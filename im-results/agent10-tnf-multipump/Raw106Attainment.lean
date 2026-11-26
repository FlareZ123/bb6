import Raw106Base

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent10Raw106
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent8TNFPath
open BB6.Agent50TNFPilot BB6.Agent31ThreeHole BB6.Agent10ZipAudit

/-- Exact five-hole parent, independent of the TNF path encoding. -/
def literalParent : PartialMachine := fun s =>
  match s.1.val, s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,true,5⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,true => some (some ⟨false,false,1⟩)
  | _,_ => none

theorem parent_eq_literal : p106 = literalParent := by
  funext s
  rcases s with ⟨q,b⟩
  have hq : q=0 ∨ q=1 ∨ q=2 ∨ q=3 ∨ q=4 ∨ q=5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> cases b <;> decide

/-- 1RBHHH_1RC1RF_0RD1RA_1LD1RE_1RC0LB_1LF0LE. -/
def attainingMachine : Machine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some ⟨true,true,1⟩
  | 0,true => none
  | 1,false => some ⟨true,true,2⟩
  | 1,true => some ⟨true,true,5⟩
  | 2,false => some ⟨false,true,3⟩
  | 2,true => some ⟨true,true,0⟩
  | 3,false => some ⟨true,false,3⟩
  | 3,true => some ⟨true,true,4⟩
  | 4,false => some ⟨true,true,2⟩
  | 4,true => some ⟨false,false,1⟩
  | 5,false => some ⟨true,false,5⟩
  | 5,true => some ⟨false,false,4⟩
  | _,_ => none

theorem attainingCompatible : compatible p106 attainingMachine := by
  rw [parent_eq_literal]
  intro s t ht
  rcases s with ⟨q,b⟩
  have hq : q=0 ∨ q=1 ∨ q=2 ∨ q=3 ∨ q=4 ∨ q=5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> cases b <;> first | exact Option.some.inj ht | contradiction

theorem attainingHalts : HaltsAfter attainingMachine 252 := by
  constructor
  · rfl
  · rfl

theorem attainingDelay : 0 ∈ delays (zeroNext attainingMachine) 0 := by decide

#print axioms parent_eq_literal
#print axioms attainingCompatible
#print axioms attainingHalts
#print axioms attainingDelay
end BB6.Agent10Raw106
