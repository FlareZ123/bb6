import Box28EraseScan
import Box28CarryGateSource

namespace BB6.Agent17.Box28EraseScanSource
open BB6Coverage BB6.Agent17.Box28EraseScan
open BB6.Agent17.Box28CarryFamily (Gate localBlank)
open BB6.Agent17.Box28CarryGateSource (sourceGate)
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
abbrev project := BB6.Agent13.Box33Source.project false

def target (s : Bool) : Fin 6 := if s then 5 else 4
def markMove (m : Mark) : Move :=
  match m with
  | .a w => ⟨w,true,0⟩
  | .b => ⟨true,true,1⟩
  | .scan s w => ⟨w,true,target s⟩

def baseTable (p : Params) : PartialMachine := fun s =>
  match s with
  | (0,false) => some (some ⟨true,true,1⟩)
  | (1,false) => some (some ⟨true,false,2⟩)
  | (2,true) => some (some ⟨false,false,3⟩)
  | (3,false) => some (some ⟨false,true,4⟩)
  | (3,true) => some (some ⟨false,false,3⟩)
  | (4,false) => some (some ⟨(p.z false).2,true,target (p.z false).1⟩)
  | (5,false) => some (some ⟨(p.z true).2,true,target (p.z true).1⟩)
  | (4,true) => some (some (markMove (p.o false)))
  | (5,true) => some (some (markMove (p.o true)))
  | _ => none

theorem target_state (s : Bool) : BB6.Agent13.Box33Source.q false (target s) = q s := by
  cases s <;> rfl

theorem mark_action (m : Mark) (c : C9Pair.Config) :
    BB6.Agent17.Box28CarryGateSource.action (some (markMove m)) c = some (markStep m c) := by
  cases m <;> simp [markMove,markStep,BB6.Agent17.Box28CarryGateSource.action,target_state,BB6.Agent13.Box33Source.q]

theorem project_step (p : Params) (m : Machine) (hm : compatible (baseTable p) m)
    (z : BB6Coverage.Config) :
    (rawStep m z).map project = stepCore p (sourceGate m (0,true))
      (sourceGate m (1,true)) (sourceGate m (2,false)) (project z) := by
  rw [BB6.Agent17.Box28CarryGateSource.raw_project]
  have hA0 := hm (0,false) (some ⟨true,true,1⟩) rfl
  have hB0 := hm (1,false) (some ⟨true,false,2⟩) rfl
  have hC1 := hm (2,true) (some ⟨false,false,3⟩) rfl
  have hD0 := hm (3,false) (some ⟨false,true,4⟩) rfl
  have hD1 := hm (3,true) (some ⟨false,false,3⟩) rfl
  have hE0 := hm (4,false) (some ⟨(p.z false).2,true,target (p.z false).1⟩) rfl
  have hF0 := hm (5,false) (some ⟨(p.z true).2,true,target (p.z true).1⟩) rfl
  have hE1 := hm (4,true) (some (markMove (p.o false))) rfl
  have hF1 := hm (5,true) (some (markMove (p.o true))) rfl
  rcases z with ⟨s,h,t⟩
  have hs : s=0 ∨ s=1 ∨ s=2 ∨ s=3 ∨ s=4 ∨ s=5 := by omega
  rcases hs with rfl|rfl|rfl|rfl|rfl|rfl <;> cases hb : t h <;>
    simp only [readSlot,hb,hA0,hB0,hC1,hD0,hD1,hE0,hF0,hE1,hF1]
  all_goals
    unfold project
    simp only [BB6.Agent13.Box33Source.project,hb]
    first
    | rfl
    | solve | simp [mark_action,stepCore]
    | simp [BB6.Agent17.Box28CarryGateSource.action,target_state,stepCore,BB6.Agent13.Box33Source.q]

theorem project_run (p : Params) (m : Machine) (hm : compatible (baseTable p) m)
    (n : Nat) (z : BB6Coverage.Config) :
    (BB6Coverage.run m n z).map project = runCore p (sourceGate m (0,true))
      (sourceGate m (1,true)) (sourceGate m (2,false)) n (project z) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [runCore_add,← ih]
      simp only [BB6Coverage.run]
      cases h : BB6Coverage.run m n z with
      | none => rfl
      | some c =>
        simp only [Option.bind_some,Option.map_some]
        change (rawStep m c).map project = (stepCore p _ _ _ (project c)).bind some
        rw [project_step p m hm]
        cases stepCore p (sourceGate m (0,true)) (sourceGate m (1,true)) (sourceGate m (2,false)) (project c) <;> rfl

theorem compatible_never (p : Params) (m : Machine) (hm : compatible (baseTable p) m) :
    NeverHalts m := by
  intro n
  have h := project_run p m hm n blank
  change (BB6Coverage.run m n blank).map project = runCore p (sourceGate m (0,true))
    (sourceGate m (1,true)) (sourceGate m (2,false)) n localBlank at h
  have hn := never_blank p (sourceGate m (0,true)) (sourceGate m (1,true)) (sourceGate m (2,false)) n
  cases hr : BB6Coverage.run m n blank with
  | none => exact False.elim (hn (by simpa [hr] using h.symm))
  | some c => simp [hr]

#print axioms compatible_never
end BB6.Agent17.Box28EraseScanSource
