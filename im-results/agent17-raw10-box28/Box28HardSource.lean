import Box28Base4
import Box33SourceBridge

namespace BB6.Agent17.Box28HardSource
open BB6Coverage
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
abbrev project := BB6.Agent13.Box33Source.project false

def counterTable (alt : Bool) : Machine := fun s =>
  match s with
  | (0,false) => some ⟨true,true,1⟩
  | (0,true) => none
  | (1,false) => some ⟨true,false,2⟩
  | (1,true) => some ⟨true,true,5⟩
  | (2,false) => some ⟨true,false,2⟩
  | (2,true) => some ⟨false,false,3⟩
  | (3,false) => some ⟨false,true,3⟩
  | (3,true) => some ⟨false,false,4⟩
  | (4,false) => some ⟨false,true,5⟩
  | (4,true) => some ⟨false,false,if alt then 4 else 2⟩
  | (5,false) => some ⟨true,false,4⟩
  | (5,true) => some ⟨true,true,0⟩
  | _ => none

theorem counter_step (alt : Bool) (z : Config) :
    (rawStep (counterTable alt) z).map project =
      Box28Base4.step alt (project z) := by
  rcases z with ⟨s,h,t⟩
  have hs : s=0 ∨ s=1 ∨ s=2 ∨ s=3 ∨ s=4 ∨ s=5 := by omega
  rcases hs with rfl|rfl|rfl|rfl|rfl|rfl <;> cases hb : t h <;> cases alt <;>
    simp only [rawStep,readSlot,counterTable,hb,Option.map_some,Option.map_none]
  all_goals
    simp only [project, BB6.Agent13.Box33Source.project_applyMove]
    simp [Box28Base4.step,BB6.Agent13.Box33Source.project,BB6.Agent13.Box33Source.q,
      BB6.Agent13.Box33Source.perm,hb] <;> rfl

theorem counter_run (alt : Bool) (n : Nat) (z : Config) :
    (run (counterTable alt) n z).map project = Box28Base4.run alt n (project z) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Box28Base4.run_add alt n 1,← ih]
    simp only [run]
    cases h : run (counterTable alt) n z with
    | none => rfl
    | some c =>
      simp only [Option.bind_some,Option.map_some]
      rw [counter_step]
      simp [Box28Base4.run]

theorem counter_never (alt : Bool) : NeverHalts (counterTable alt) := by
  intro n
  have h := counter_run alt n blank
  have hblank : project blank = Box28Base4.blank := rfl
  rw [hblank] at h
  cases he : run (counterTable alt) n blank with
  | none => exact False.elim (Box28Base4.never_blank alt n (by simpa [he] using h.symm))
  | some c => rfl

def counterPartial (alt : Bool) : PartialMachine := fun s => some (counterTable alt s)
theorem counter_compatible_never (alt : Bool) (m : Machine)
    (hm : compatible (counterPartial alt) m) : NeverHalts m := by
  have he : m = counterTable alt := funext fun s => hm s _ rfl
  rw [he]
  exact counter_never alt

#print axioms counter_compatible_never
end BB6.Agent17.Box28HardSource
