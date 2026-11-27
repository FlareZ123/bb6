import Box28Mod5Sweep
import Box33SourceBridge

namespace BB6.Agent17.Box28Mod5SweepSource
open BB6Coverage
abbrev project := BB6.Agent13.Box33Source.project false

/-- All twelve slots of the two sweep machines. -/
def partialTable (alt : Bool) : PartialMachine := fun s =>
  match s with
  | (0,false) => some (some ⟨true,true,1⟩)
  | (0,true) => some (some ⟨true,true,5⟩)
  | (1,false) => some (some ⟨true,false,2⟩)
  | (1,true) => some (some ⟨false,false,3⟩)
  | (2,false) => some (some ⟨true,false,2⟩)
  | (2,true) => some (some ⟨false,false,3⟩)
  | (3,false) => some (some ⟨false,true,0⟩)
  | (3,true) => some (some ⟨true,false,5⟩)
  | (4,false) => some none
  | (4,true) => some (some ⟨false,true,if alt then 2 else 1⟩)
  | (5,false) => some (some ⟨true,true,0⟩)
  | (5,true) => some (some ⟨true,true,4⟩)
  | _ => none

def plannedStep (alt : Bool) (z : Config) : Option Config :=
  (partialTable alt (readSlot z)).bind fun t => t.map (applyMove z)

theorem planned_project (alt : Bool) (z : Config) :
    (plannedStep alt z).map project = Box28Mod5Sweep.step alt (project z) := by
  rcases z with ⟨s,h,t⟩
  have hs : s=0 ∨ s=1 ∨ s=2 ∨ s=3 ∨ s=4 ∨ s=5 := by omega
  rcases hs with rfl|rfl|rfl|rfl|rfl|rfl <;> cases hb : t h <;> cases alt <;>
    simp only [plannedStep,readSlot,partialTable,hb,Option.bind_some,Option.bind_none,Option.map_some,Option.map_none]
  all_goals
    unfold project
    try rw [BB6.Agent13.Box33Source.project_applyMove]
    simp only [BB6.Agent13.Box33Source.project, hb]
    rfl

-- Successful local steps never need a completion's unspecified entries.
theorem step_sound (alt : Bool) (m : Machine) (hm : compatible (partialTable alt) m) (z : Config)
    (c : C9Pair.Config) (hc : Box28Mod5Sweep.step alt (project z) = some c) :
    ∃ d, rawStep m z = some d ∧ project d = c := by
  rw [← planned_project] at hc
  unfold plannedStep at hc
  cases hp : partialTable alt (readSlot z) with
  | none => simp [hp] at hc
  | some t =>
    cases t with
    | none => simp [hp] at hc
    | some mv =>
      refine ⟨applyMove z mv, ?_, ?_⟩
      · simp [rawStep,hm _ _ hp]
      · simpa [hp] using hc

theorem run_sound (alt : Bool) (m : Machine) (hm : compatible (partialTable alt) m) (n : Nat)
    (z : Config) (c : C9Pair.Config) (hc : Box28Mod5Sweep.run alt n (project z) = some c) :
    ∃ d, run m n z = some d ∧ project d = c := by
  induction n generalizing c with
  | zero => exact ⟨z,rfl,by simpa [Box28Mod5Sweep.run] using hc⟩
  | succ n ih =>
    rw [Box28Mod5Sweep.run_add alt n 1] at hc
    cases hp : Box28Mod5Sweep.run alt n (project z) with
    | none => simp [hp] at hc
    | some a =>
      obtain ⟨d,hd,hproj⟩ := ih a hp
      have hs : Box28Mod5Sweep.step alt (project d) = some c := by
        simpa [hp,Box28Mod5Sweep.run,hproj] using hc
      obtain ⟨d',hd',hproj'⟩ := step_sound alt m hm d c hs
      exact ⟨d',by simp [run,hd,hd'],hproj'⟩

theorem compatible_never (alt : Bool) (m : Machine) (hm : compatible (partialTable alt) m) : NeverHalts m := by
  intro n
  have hn : Box28Mod5Sweep.run alt n (project blank) ≠ none := by
    exact Box28Mod5Sweep.never_blank alt n
  cases hc : Box28Mod5Sweep.run alt n (project blank) with
  | none => exact False.elim (hn hc)
  | some c =>
    obtain ⟨d,hd,_⟩ := run_sound alt m hm n blank c hc
    simp [hd]

#print axioms compatible_never
end BB6.Agent17.Box28Mod5SweepSource
