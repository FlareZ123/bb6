import Box28D16V17Pump
import Box33SourceBridge

namespace BB6.Agent17.Box28D16V17PumpSource
open BB6Coverage
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
abbrev project := BB6.Agent13.Box33Source.project false

def table : Machine := fun s =>
  match s with
  | (0,false) => some ⟨true,true,1⟩
  | (0,true) => some ⟨false,true,2⟩
  | (1,false) => some ⟨true,false,2⟩
  | (1,true) => some ⟨false,true,5⟩
  | (2,false) => some ⟨true,false,2⟩
  | (2,true) => some ⟨false,false,3⟩
  | (3,false) => some ⟨true,true,3⟩
  | (3,true) => some ⟨false,false,4⟩
  | (4,false) => some ⟨true,true,4⟩
  | (4,true) => some ⟨true,true,0⟩
  | (5,false) => none
  | (5,true) => some ⟨true,true,2⟩
  | _ => none

theorem map_step (z : Config) :
    (rawStep table z).map project = Box28D16V17Pump.step (project z) := by
  rcases z with ⟨s,h,t⟩
  have hs : s=0 ∨ s=1 ∨ s=2 ∨ s=3 ∨ s=4 ∨ s=5 := by omega
  rcases hs with rfl|rfl|rfl|rfl|rfl|rfl <;> cases hb : t h <;>
    simp only [rawStep,readSlot,table,hb,Option.map_some,Option.map_none]
  all_goals
    simp only [project, BB6.Agent13.Box33Source.project_applyMove]
    simp [Box28D16V17Pump.step,BB6.Agent13.Box33Source.project,BB6.Agent13.Box33Source.q,
      BB6.Agent13.Box33Source.perm,hb] <;> rfl

theorem map_run (n : Nat) (z : Config) :
    (run table n z).map project = Box28D16V17Pump.run n (project z) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Box28D16V17Pump.run_add n 1,← ih]
    simp only [run]
    cases h : run table n z with
    | none => rfl
    | some c =>
      simp only [Option.bind_some,Option.map_some]
      rw [map_step]
      simp [Box28D16V17Pump.run]

theorem never : NeverHalts table := by
  intro n
  have h := map_run n blank
  have hb : project blank = Box28D16V17Pump.blank := rfl
  rw [hb] at h
  cases he : run table n blank with
  | none => exact False.elim (Box28D16V17Pump.never_blank n (by simpa [he] using h.symm))
  | some c => rfl

def partialTable : PartialMachine := fun s => some (table s)
theorem compatible_never (m : Machine) (hm : compatible partialTable m) : NeverHalts m := by
  have he : m = table := funext fun s => hm s _ rfl
  rw [he]
  exact never

#print axioms compatible_never
end BB6.Agent17.Box28D16V17PumpSource
