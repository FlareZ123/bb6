import Box28TransducerModel
import Box28CarryRectangle

namespace BB6.Agent17.Box28TransducerSource
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent13.Box17
open BB6.Agent17.Box28Transducer BB6.Agent17.Box28TransducerModel
open BB6.Agent17.Box28CarryFamily (Gate localBlank)
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.constructorNameAsVariable false
set_option linter.unusedSimpArgs false
abbrev project := BB6.Agent13.Box33Source.project false

def target (s : S) : Fin 6 := if s=0 then 0 else if s=1 then 4 else 5
theorem target_state : ∀ s : S, BB6.Agent13.Box33Source.q false (target s) = state s := by decide

/-- All five rightward scan transitions are independently parameterized;
    B1 is completely unrestricted. -/
def baseTable (p : Params) : PartialMachine := fun s =>
  match s with
  | (0,false) => some (some ⟨true,true,1⟩)
  | (0,true) => some (some ⟨wr p.o.a,true,target (dst p.o.a)⟩)
  | (1,false) => some (some ⟨true,false,2⟩)
  | (2,false) => some (some ⟨true,false,2⟩)
  | (2,true) => some (some ⟨false,false,3⟩)
  | (3,false) => some (some ⟨false,true,4⟩)
  | (3,true) => some (some ⟨true,false,3⟩)
  | (4,false) => some (some ⟨wr p.ze,true,target (dst p.ze)⟩)
  | (4,true) => some (some ⟨wr p.o.e,true,target (dst p.o.e)⟩)
  | (5,false) => some (some ⟨wr p.zf,true,target (dst p.zf)⟩)
  | (5,true) => some (some ⟨wr p.o.f,true,target (dst p.o.f)⟩)
  | _ => none

abbrev action := BB6.Agent17.Box28CarryGateSource.action
abbrev sourceGate := BB6.Agent17.Box28CarryGateSource.sourceGate

theorem project_step (p : Params) (m : Machine) (hm : compatible (baseTable p) m)
    (z : BB6Coverage.Config) :
    (rawStep m z).map project = stepCore p (sourceGate m (1,true)) (project z) := by
  rw [BB6.Agent17.Box28CarryGateSource.raw_project]
  have hA0 := hm (0,false) (some ⟨true,true,1⟩) rfl
  have hA1 := hm (0,true) (some ⟨wr p.o.a,true,target (dst p.o.a)⟩) rfl
  have hB0 := hm (1,false) (some ⟨true,false,2⟩) rfl
  have hC0 := hm (2,false) (some ⟨true,false,2⟩) rfl
  have hC1 := hm (2,true) (some ⟨false,false,3⟩) rfl
  have hD0 := hm (3,false) (some ⟨false,true,4⟩) rfl
  have hD1 := hm (3,true) (some ⟨true,false,3⟩) rfl
  have hE0 := hm (4,false) (some ⟨wr p.ze,true,target (dst p.ze)⟩) rfl
  have hE1 := hm (4,true) (some ⟨wr p.o.e,true,target (dst p.o.e)⟩) rfl
  have hF0 := hm (5,false) (some ⟨wr p.zf,true,target (dst p.zf)⟩) rfl
  have hF1 := hm (5,true) (some ⟨wr p.o.f,true,target (dst p.o.f)⟩) rfl
  rcases z with ⟨s,h,t⟩
  have hs : s=0 ∨ s=1 ∨ s=2 ∨ s=3 ∨ s=4 ∨ s=5 := by omega
  rcases hs with rfl|rfl|rfl|rfl|rfl|rfl <;> cases hb : t h <;>
    simp only [readSlot,hb,hA0,hA1,hB0,hC0,hC1,hD0,hD1,hE0,hE1,hF0,hF1]
  all_goals
    unfold project
    simp only [BB6.Agent13.Box33Source.project,hb]
    first
    | rfl
    | (simp [BB6.Agent17.Box28CarryGateSource.action,target_state] <;> rfl)

theorem project_run (p : Params) (m : Machine) (hm : compatible (baseTable p) m)
    (n : Nat) (z : BB6Coverage.Config) :
    (BB6Coverage.run m n z).map project =
      runCore p (sourceGate m (1,true)) n (project z) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [runCore_add,← ih]
    simp only [BB6Coverage.run]
    cases h : BB6Coverage.run m n z with
    | none => rfl
    | some c =>
      simp only [Option.bind_some,Option.map_some,runCore_one]
      exact project_step p m hm c

theorem compatible_never (p : Params) (m : Machine) (hm : compatible (baseTable p) m)
    (hg : safeCert p = true) : NeverHalts m := by
  intro n
  have h := project_run p m hm n blank
  change (BB6Coverage.run m n blank).map project =
    runCore p (sourceGate m (1,true)) n localBlank at h
  have hn := never_blank p (sourceGate m (1,true)) hg n
  cases hr : BB6Coverage.run m n blank with
  | none =>
    rw [hr] at h
    exact False.elim (hn h.symm)
  | some c => simp [hr]

def finiteOK (p : Params) : Bool :=
  match blankCost p with
  | none => false
  | some n => leafCheck 51 #[] (baseTable p) (.last 3 n)

theorem codeCases (c : Code) : c=0 ∨ c=1 ∨ c=2 ∨ c=3 ∨ c=4 ∨ c=5 := by
  revert c
  decide

def check (a e f ze zf : Code) : Prop :=
  safeCert ⟨⟨a,e,f⟩,ze,zf⟩ = true ∨ finiteOK ⟨⟨a,e,f⟩,ze,zf⟩ = true

instance (a e f ze zf : Code) : Decidable (check a e f ze zf) := by
  unfold check
  infer_instance

/-- Check six independent batches, each split into 36 small kernel reductions.
    No native_decide or external oracle. -/
theorem check0 : ∀ e f ze zf : Code, check 0 e f ze zf := by
  intro e f
  rcases codeCases e with h|h|h|h|h|h <;> subst e <;>
    rcases codeCases f with h|h|h|h|h|h <;> subst f <;> decide +kernel

theorem check1 : ∀ e f ze zf : Code, check 1 e f ze zf := by
  intro e f
  rcases codeCases e with h|h|h|h|h|h <;> subst e <;>
    rcases codeCases f with h|h|h|h|h|h <;> subst f <;> decide +kernel

theorem check2 : ∀ e f ze zf : Code, check 2 e f ze zf := by
  intro e f
  rcases codeCases e with h|h|h|h|h|h <;> subst e <;>
    rcases codeCases f with h|h|h|h|h|h <;> subst f <;> decide +kernel

theorem check3 : ∀ e f ze zf : Code, check 3 e f ze zf := by
  intro e f
  rcases codeCases e with h|h|h|h|h|h <;> subst e <;>
    rcases codeCases f with h|h|h|h|h|h <;> subst f <;> decide +kernel

theorem check4 : ∀ e f ze zf : Code, check 4 e f ze zf := by
  intro e f
  rcases codeCases e with h|h|h|h|h|h <;> subst e <;>
    rcases codeCases f with h|h|h|h|h|h <;> subst f <;> decide +kernel

theorem check5 : ∀ e f ze zf : Code, check 5 e f ze zf := by
  intro e f
  rcases codeCases e with h|h|h|h|h|h <;> subst e <;>
    rcases codeCases f with h|h|h|h|h|h <;> subst f <;> decide +kernel

theorem all_checks : ∀ a e f ze zf : Code,
    safeCert ⟨⟨a,e,f⟩,ze,zf⟩ = true ∨ finiteOK ⟨⟨a,e,f⟩,ze,zf⟩ = true := by
  intro a
  rcases codeCases a with h|h|h|h|h|h <;> subst a
  · exact check0
  · exact check1
  · exact check2
  · exact check3
  · exact check4
  · exact check5

theorem rectangle_bound (p : Params) (m : Machine) (hm : compatible (baseTable p) m) :
    WeightedBound 51 m := by
  rcases p with ⟨⟨a,e,f⟩,ze,zf⟩
  rcases all_checks a e f ze zf with hg | hf
  · apply weighted_of_never
    exact compatible_never _ m hm hg
  · cases hc : blankCost ⟨⟨a,e,f⟩,ze,zf⟩ with
    | none => simp [finiteOK,hc] at hf
    | some n =>
      have hcheck : leafCheck 51 #[] (baseTable ⟨⟨a,e,f⟩,ze,zf⟩) (.last 3 n) = true := by
        simpa [finiteOK,hc] using hf
      apply leafCheck_sound 51 #[] ?_ _ (.last 3 n) hcheck m hm
      intro i q h
      simp at h

theorem rectangle_mono (B : Nat) (hB : 51 ≤ B) (p : Params) (m : Machine)
    (hm : compatible (baseTable p) m) : WeightedBound B m := by
  intro k d hk hd
  exact Nat.le_trans (rectangle_bound p m hm k d hk hd) hB

def maxParams : Params := ⟨⟨3,5,0⟩,1,1⟩
def maxRow : PartialMachine := refine (baseTable maxParams) (1,true) none
def maxMachine : Machine := fun s => (maxRow s).getD none

theorem max_compatible : compatible maxRow maxMachine := by
  intro s t h
  simp [maxMachine,h]

theorem max_base_check : ∀ (q : Fin 6) (b : Bool),
    (baseTable maxParams (q,b)).isSome = true →
    maxRow (q,b) = baseTable maxParams (q,b) := by decide

theorem max_base : compatible (baseTable maxParams) maxMachine := by
  intro s t h
  have he := max_base_check s.1 s.2 (by simp [h])
  exact max_compatible s t (he.trans h)

theorem max_halts : HaltsAfter maxMachine 50 :=
  zipHalt_sound maxRow 50 (by decide) maxMachine max_compatible

#print axioms compatible_never
#print axioms all_checks
#print axioms rectangle_bound
#print axioms max_halts
#print axioms max_base
end BB6.Agent17.Box28TransducerSource
