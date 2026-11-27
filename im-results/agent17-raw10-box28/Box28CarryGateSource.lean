import Box28CarryFamily
import Box33SourceBridge

namespace BB6.Agent17.Box28CarryGateSource
open BB6Coverage
open BB6.Agent17.Box28CarryFamily
open BB6.Agent13.Box33BinaryCounter (zeros zero_head zero_pop zero_push rep rep_add ones ones_succ)
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.constructorNameAsVariable false
abbrev project := BB6.Agent13.Box33Source.project false

/-- The ten recurrent slots. B1 and E0 are deliberately unspecified. -/
def baseTable (two : Bool) : PartialMachine := fun s =>
  match s with
  | (0,false) => some (some ⟨true,true,1⟩)
  | (0,true) => some (some ⟨true,true,if two then 5 else 4⟩)
  | (1,false) => some (some ⟨true,false,2⟩)
  | (2,false) => some (some ⟨true,false,2⟩)
  | (2,true) => some (some ⟨false,false,3⟩)
  | (3,false) => some (some ⟨false,true,4⟩)
  | (3,true) => some (some ⟨true,false,3⟩)
  | (4,true) => some (some ⟨true,true,5⟩)
  | (5,false) => some (some ⟨true,true,0⟩)
  | (5,true) => some (some ⟨true,true,2⟩)
  | _ => none

def action (t : Option Move) (c : C9Pair.Config) : Option C9Pair.Config :=
  t.map fun mv => if mv.right then C9Pair.right (BB6.Agent13.Box33Source.q false mv.next) mv.write c
                  else C9Pair.left (BB6.Agent13.Box33Source.q false mv.next) mv.write c
def sourceGate (m : Machine) (s : Slot) : Gate := action (m s)

theorem raw_project (m : Machine) (z : BB6Coverage.Config) :
    (rawStep m z).map project = action (m (readSlot z)) (project z) := by
  unfold rawStep action
  cases h : m (readSlot z) with
  | none => rfl
  | some mv =>
    simp only [Option.map_some]
    exact congrArg some (BB6.Agent13.Box33Source.project_applyMove false z mv)

theorem project_step (two : Bool) (m : Machine) (hm : compatible (baseTable two) m)
    (z : BB6Coverage.Config) :
    (rawStep m z).map project =
      stepCore two (sourceGate m (1,true)) (sourceGate m (4,false)) (project z) := by
  rw [raw_project]
  have hA0 := hm (0,false) (some ⟨true,true,1⟩) rfl
  have hA1 := hm (0,true) (some ⟨true,true,if two then 5 else 4⟩) rfl
  have hB0 := hm (1,false) (some ⟨true,false,2⟩) rfl
  have hC0 := hm (2,false) (some ⟨true,false,2⟩) rfl
  have hC1 := hm (2,true) (some ⟨false,false,3⟩) rfl
  have hD0 := hm (3,false) (some ⟨false,true,4⟩) rfl
  have hD1 := hm (3,true) (some ⟨true,false,3⟩) rfl
  have hE1 := hm (4,true) (some ⟨true,true,5⟩) rfl
  have hF0 := hm (5,false) (some ⟨true,true,0⟩) rfl
  have hF1 := hm (5,true) (some ⟨true,true,2⟩) rfl
  rcases z with ⟨s,h,t⟩
  have hs : s=0 ∨ s=1 ∨ s=2 ∨ s=3 ∨ s=4 ∨ s=5 := by omega
  rcases hs with rfl|rfl|rfl|rfl|rfl|rfl <;> cases hb : t h <;> cases two <;>
    simp only [readSlot,hb,hA0,hA1,hB0,hC0,hC1,hD0,hD1,hE1,hF0,hF1] <;> rfl

theorem project_run (two : Bool) (m : Machine) (hm : compatible (baseTable two) m)
    (n : Nat) (z : BB6Coverage.Config) :
    (BB6Coverage.run m n z).map project =
      runCore two (sourceGate m (1,true)) (sourceGate m (4,false)) n (project z) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [runCore_add,← ih]
    simp only [BB6Coverage.run]
    cases h : BB6Coverage.run m n z with
    | none => rfl
    | some c =>
      simp only [Option.bind_some,Option.map_some,runCore_one]
      exact project_step two m hm c

theorem from3 (m : Machine) (hm : compatible (baseTable false) m)
    (j : Nat) (s : C9Pair.Stream)
    (hs : runCore false (sourceGate m (1,true)) (sourceGate m (4,false)) j localBlank = some (Eroot 0 s))
    (hw : Word3 s) : NeverHalts m := by
  intro n
  have h := project_run false m hm n blank
  change (BB6Coverage.run m n blank).map project =
    runCore false (sourceGate m (1,true)) (sourceGate m (4,false)) n localBlank at h
  have hn := never_from3 _ _ j s hs hw n
  cases hr : BB6Coverage.run m n blank with
  | none => exact False.elim (hn (by simpa [hr] using h.symm))
  | some c => simp [hr]

theorem from2 (m : Machine) (hm : compatible (baseTable true) m)
    (j : Nat) (s : C9Pair.Stream)
    (hs : runCore true (sourceGate m (1,true)) (sourceGate m (4,false)) j localBlank = some (Froot 1 s))
    (hw : Word2 s) : NeverHalts m := by
  intro n
  have h := project_run true m hm n blank
  change (BB6Coverage.run m n blank).map project =
    runCore true (sourceGate m (1,true)) (sourceGate m (4,false)) n localBlank at h
  have hn := never_from2 _ _ j s hs hw n
  cases hr : BB6Coverage.run m n blank with
  | none => exact False.elim (hn (by simpa [hr] using h.symm))
  | some c => simp [hr]

#print axioms from3
#print axioms from2
end BB6.Agent17.Box28CarryGateSource
