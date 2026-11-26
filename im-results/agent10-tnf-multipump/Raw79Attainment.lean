import Raw79Base

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent10Raw79
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent8TNFPath
open BB6.Agent50TNFPilot BB6.Agent31ThreeHole BB6.Agent10ZipAudit

/-- Exact five-hole parent, independent of the TNF path encoding. -/
def literalParent : PartialMachine := fun s =>
  match s.1.val, s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,false,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,true => some (some ⟨false,false,1⟩)
  | _,_ => none

theorem parent_eq_literal : p79 = literalParent := by
  funext s
  rcases s with ⟨q,b⟩
  have hq : q=0 ∨ q=1 ∨ q=2 ∨ q=3 ∨ q=4 ∨ q=5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> cases b <;> decide

/-- 1RB0LF_1RC1LE_0RD0RB_1LD1RE_0LA0LB_0REHHH. -/
def attainingMachine : Machine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some ⟨true,true,1⟩
  | 0,true => some ⟨false,false,5⟩
  | 1,false => some ⟨true,true,2⟩
  | 1,true => some ⟨true,false,4⟩
  | 2,false => some ⟨false,true,3⟩
  | 2,true => some ⟨false,true,1⟩
  | 3,false => some ⟨true,false,3⟩
  | 3,true => some ⟨true,true,4⟩
  | 4,false => some ⟨false,false,0⟩
  | 4,true => some ⟨false,false,1⟩
  | 5,false => some ⟨false,true,4⟩
  | 5,true => none
  | _,_ => none

theorem attainingCompatible : compatible p79 attainingMachine := by
  rw [parent_eq_literal]
  intro s t ht
  rcases s with ⟨q,b⟩
  have hq : q=0 ∨ q=1 ∨ q=2 ∨ q=3 ∨ q=4 ∨ q=5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> cases b <;> first | exact Option.some.inj ht | contradiction

def attainingPartial : PartialMachine := fun s =>
  if s = (5,true) then none else some (attainingMachine s)

theorem attainingHalts : HaltsAfter attainingMachine 2351 := by
  have hread : (knownRun attainingPartial 2351).map readSlot = some (5,true) := by
    rw [← BB6Coverage.Agent10ZipAudit.zipRead_eq]
    rfl
  have hc : compatible (refine attainingPartial (5,true) none) attainingMachine := by
    intro s t ht
    by_cases hs : s = (5,true)
    · subst s
      exact Option.some.inj ht
    · exact Option.some.inj (by simpa [refine,attainingPartial,hs] using ht)
  cases hr : knownRun attainingPartial 2351 with
  | none => simp [hr] at hread
  | some c =>
    have hs : readSlot c = (5,true) := by simpa [hr] using hread
    apply first_hole_halts attainingPartial 2351 c hr
    · rw [hs]; rfl
    · simpa [hs] using hc

theorem attainingDelay : 2 ∈ delays (zeroNext attainingMachine) 0 := by decide

#print axioms parent_eq_literal
#print axioms attainingCompatible
#print axioms attainingHalts
#print axioms attainingDelay
end BB6.Agent10Raw79
