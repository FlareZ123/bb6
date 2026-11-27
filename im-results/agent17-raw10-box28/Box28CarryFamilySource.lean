import Box28CarryFamily
import Box33SourceBridge

namespace BB6.Agent17.Box28CarryFamilySource
open BB6Coverage
set_option linter.constructorNameAsVariable false
abbrev project := BB6.Agent13.Box33Source.project false

/-- All twelve slots of the two sweep machines. -/
def partialTable (alt : Bool) (e : Box28CarryFamily.Entry) : PartialMachine := fun s =>
  match s with
  | (0,false) => some (some ⟨true,true,1⟩)
  | (0,true) => some (some ⟨true,true,if alt then 5 else 4⟩)
  | (1,false) => some (some ⟨true,false,2⟩)
  | (2,false) => some (some ⟨true,false,2⟩)
  | (2,true) => some (some ⟨false,false,3⟩)
  | (3,false) => some (some ⟨false,true,4⟩)
  | (3,true) => some (some ⟨true,false,3⟩)
  | (4,false) => some (some (match e with
    | .c => ⟨true,true,2⟩
    | .d => ⟨false,true,3⟩
    | .e => ⟨false,true,4⟩))
  | (4,true) => some (some ⟨true,true,5⟩)
  | (5,false) => some (some ⟨true,true,0⟩)
  | (5,true) => some (some ⟨true,true,2⟩)
  | _ => none

def plannedStep (alt : Bool) (e : Box28CarryFamily.Entry) (z : Config) : Option Config :=
  (partialTable alt e (readSlot z)).bind fun t => t.map (applyMove z)

theorem planned_project (alt : Bool) (e : Box28CarryFamily.Entry) (z : Config) :
    (plannedStep alt e z).map project = Box28CarryFamily.step alt e (project z) := by
  rcases z with ⟨s,h,t⟩
  have hs : s=0 ∨ s=1 ∨ s=2 ∨ s=3 ∨ s=4 ∨ s=5 := by omega
  rcases hs with rfl|rfl|rfl|rfl|rfl|rfl <;> cases hb : t h <;> cases alt <;> cases e <;>
    simp only [plannedStep,readSlot,partialTable,hb,Option.bind_some,Option.bind_none,Option.map_some,Option.map_none]
  all_goals
    unfold project
    try rw [BB6.Agent13.Box33Source.project_applyMove]
    simp only [BB6.Agent13.Box33Source.project, hb]
    rfl

-- Successful local steps never need a completion's unspecified entries.
theorem step_sound (alt : Bool) (e : Box28CarryFamily.Entry) (m : Machine) (hm : compatible (partialTable alt e) m) (z : Config)
    (c : C9Pair.Config) (hc : Box28CarryFamily.step alt e (project z) = some c) :
    ∃ d, rawStep m z = some d ∧ project d = c := by
  rw [← planned_project] at hc
  unfold plannedStep at hc
  cases hp : partialTable alt e (readSlot z) with
  | none => simp [hp] at hc
  | some t =>
    cases t with
    | none => simp [hp] at hc
    | some mv =>
      refine ⟨applyMove z mv, ?_, ?_⟩
      · simp [rawStep,hm _ _ hp]
      · simpa [hp] using hc

theorem run_sound (alt : Bool) (e : Box28CarryFamily.Entry) (m : Machine) (hm : compatible (partialTable alt e) m) (n : Nat)
    (z : Config) (c : C9Pair.Config) (hc : Box28CarryFamily.run alt e n (project z) = some c) :
    ∃ d, run m n z = some d ∧ project d = c := by
  induction n generalizing c with
  | zero => exact ⟨z,rfl,by simpa only [Box28CarryFamily.run_zero,Option.some.injEq] using hc⟩
  | succ n ih =>
    rw [Box28CarryFamily.run_add alt e n 1] at hc
    cases hp : Box28CarryFamily.run alt e n (project z) with
    | none => simp [hp] at hc
    | some a =>
      obtain ⟨d,hd,hproj⟩ := ih a hp
      have hs : Box28CarryFamily.step alt e (project d) = some c := by
        simpa only [hp,Option.bind_some,Box28CarryFamily.run_one,hproj] using hc
      obtain ⟨d',hd',hproj'⟩ := step_sound alt e m hm d c hs
      exact ⟨d',by simp [run,hd,hd'],hproj'⟩

theorem compatible_never (alt : Bool) (e : Box28CarryFamily.Entry) (m : Machine) (hm : compatible (partialTable alt e) m) : NeverHalts m := by
  intro n
  have hn : Box28CarryFamily.run alt e n (project blank) ≠ none := by
    exact Box28CarryFamily.never_blank alt e n
  cases hc : Box28CarryFamily.run alt e n (project blank) with
  | none => exact False.elim (hn hc)
  | some c =>
    obtain ⟨d,hd,_⟩ := run_sound alt e m hm n blank c hc
    simp [hd]

#print axioms compatible_never
end BB6.Agent17.Box28CarryFamilySource
