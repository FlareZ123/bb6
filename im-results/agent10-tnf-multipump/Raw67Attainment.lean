import Raw67Base

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent10Raw67
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent8TNFPath
open BB6.Agent50TNFPilot BB6.Agent31ThreeHole BB6.Agent10ZipAudit

/-- Exact five-hole parent, independent of the TNF path encoding. -/
def literalParent : PartialMachine := fun s =>
  match s.1.val, s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,false,1⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,true => some (some ⟨false,false,1⟩)
  | _,_ => none

theorem parent_eq_literal : p67 = literalParent := by
  funext s
  rcases s with ⟨q,b⟩
  have hq : q=0 ∨ q=1 ∨ q=2 ∨ q=3 ∨ q=4 ∨ q=5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> cases b <;> decide

/-- 1RB0RC_1RC1LB_0RD0RF_1LD1RE_HHH0LB_1RA0LD. -/
def attainingMachine : Machine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some ⟨true,true,1⟩
  | 0,true => some ⟨false,true,2⟩
  | 1,false => some ⟨true,true,2⟩
  | 1,true => some ⟨true,false,1⟩
  | 2,false => some ⟨false,true,3⟩
  | 2,true => some ⟨false,true,5⟩
  | 3,false => some ⟨true,false,3⟩
  | 3,true => some ⟨true,true,4⟩
  | 4,false => none
  | 4,true => some ⟨false,false,1⟩
  | 5,false => some ⟨true,true,0⟩
  | 5,true => some ⟨false,false,3⟩
  | _,_ => none

theorem attainingCompatible : compatible p67 attainingMachine := by
  rw [parent_eq_literal]
  intro s t ht
  rcases s with ⟨q,b⟩
  have hq : q=0 ∨ q=1 ∨ q=2 ∨ q=3 ∨ q=4 ∨ q=5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> cases b <;> first | exact Option.some.inj ht | contradiction

def attainingPartial : PartialMachine := fun s =>
  if s = (4,false) then none else some (attainingMachine s)

theorem attainingHalts : HaltsAfter attainingMachine 807 := by
  have hread : (knownRun attainingPartial 807).map readSlot = some (4,false) := by
    rw [← BB6Coverage.Agent10ZipAudit.zipRead_eq]
    rfl
  have hc : compatible (refine attainingPartial (4,false) none) attainingMachine := by
    intro s t ht
    by_cases hs : s = (4,false)
    · subst s
      exact Option.some.inj ht
    · exact Option.some.inj (by simpa [refine,attainingPartial,hs] using ht)
  cases hr : knownRun attainingPartial 807 with
  | none => simp [hr] at hread
  | some c =>
    have hs : readSlot c = (4,false) := by simpa [hr] using hread
    apply first_hole_halts attainingPartial 807 c hr
    · rw [hs]; rfl
    · simpa [hs] using hc

theorem attainingDelay : 0 ∈ delays (zeroNext attainingMachine) 0 := by decide

#print axioms parent_eq_literal
#print axioms attainingCompatible
#print axioms attainingHalts
#print axioms attainingDelay
end BB6.Agent10Raw67
