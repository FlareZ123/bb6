import Box33Growth
import Box33SourceBridge

namespace BB6.Agent13.Box33GrowthSource
open BB6Coverage
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
def p : PartialMachine := fun s =>
  match s with
  | (0,false) => some (some ⟨true,true,1⟩)
  | (1,false) => some (some ⟨true,false,2⟩)
  | (2,false) => some (some ⟨false,false,0⟩)
  | (2,true) => some (some ⟨false,false,3⟩)
  | (3,false) => some (some ⟨true,true,3⟩)
  | (3,true) => some (some ⟨false,true,2⟩)
  | _ => none
def table : Machine := fun s => (p s).getD none
abbrev project := Box33Source.project false

theorem project_step (z : Config) :
    (rawStep table z).map project = Box33Growth.step (project z) := by
  rcases z with ⟨s,h,t⟩
  have hs : s=0 ∨ s=1 ∨ s=2 ∨ s=3 ∨ s=4 ∨ s=5 := by omega
  rcases hs with rfl|rfl|rfl|rfl|rfl|rfl <;> cases hb : t h <;>
    simp only [rawStep,readSlot,table,p,hb,Option.getD_some,Option.getD_none,Option.map_some,Option.map_none]
  all_goals
    simp only [project,Box33Source.project_applyMove]
    simp [Box33Growth.step,Box33Source.project,Box33Source.q,Box33Source.perm,hb] <;> rfl

theorem project_run (n : Nat) (z : Config) :
    (run table n z).map project = Box33Growth.run n (project z) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Box33Growth.run_add n 1,← ih]
    simp only [run]
    cases h : run table n z with
    | none => rfl
    | some c =>
      simp only [Option.bind_some,Option.map_some]
      rw [project_step]
      simp [Box33Growth.run]

theorem never_total : NeverHalts table := by
  intro n
  have h := project_run n blank
  have hblank : project blank = Box33Growth.blank := rfl
  rw [hblank] at h
  cases he : run table n blank with
  | none => exact False.elim (Box33Growth.never_blank n (by simpa [he] using h.symm))
  | some c => rfl

theorem compatible_never (m : Machine) (hm : compatible p m) : NeverHalts m := by
  intro n
  have h : run table n blank = run m n blank := by
    apply run_agrees_on_prefix
    intro k hk d hd
    have hn := never_total (k+1)
    have hne : table (readSlot d) ≠ none := by
      intro he
      simp [run,hd,rawStep,he] at hn
    have hp : p (readSlot d) = some (table (readSlot d)) := by
      cases he : p (readSlot d) with
      | none => exact False.elim (hne (by simp [table,he]))
      | some t => simp [table,he]
    exact (hm _ _ hp).symm
  rw [← h]
  exact never_total n

#print axioms compatible_never
end BB6.Agent13.Box33GrowthSource
