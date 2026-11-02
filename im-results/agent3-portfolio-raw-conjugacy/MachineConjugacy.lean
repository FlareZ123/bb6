import Std
import Lean.Elab.Tactic.Omega

namespace BB6.Portfolio

inductive Dir where
  | L | R
  deriving DecidableEq, Repr

def Dir.dx : Dir → Int
  | .L => -1
  | .R => 1

def Dir.mirror : Dir → Dir
  | .L => .R
  | .R => .L

theorem Dir.mirror_dx (d : Dir) : d.mirror.dx = -d.dx := by
  cases d <;> simp [Dir.mirror, Dir.dx]

abbrev State := Fin 6
abbrev Instruction := Bool × Dir × State
abbrev Machine := State → Bool → Option Instruction

structure Cfg where
  state : State
  head : Int
  tape : Int → Bool

def updateTape (t : Int → Bool) (h : Int) (w : Bool) : Int → Bool :=
  fun i => if i = h then w else t i

def step (M : Machine) (c : Cfg) : Option Cfg :=
  match M c.state (c.tape c.head) with
  | none => none
  | some (w,d,s) => some ⟨s, c.head+d.dx, updateTape c.tape c.head w⟩

def run (M : Machine) : Nat → Option Cfg → Option Cfg
  | 0, c => c
  | n+1, c => (run M n c).bind (step M)

def blank (s : State) : Cfg := ⟨s, 0, fun _ => false⟩

def haltsFrom (M : Machine) (s : State) : Prop :=
  ∃ n c, run M n (some (blank s)) = some c ∧ step M c = none

/-- Invert the physical tape axis, not just the direction labels. -/
def reflectCfg (c : Cfg) : Cfg :=
  ⟨c.state, -c.head, fun i => c.tape (-i)⟩

def reflectMachine (M : Machine) : Machine :=
  fun s bit => (M s bit).map fun (w,d,q) => (w,d.mirror,q)

theorem reflect_update (t : Int → Bool) (h : Int) (w : Bool) :
    (fun i => updateTape t h w (-i)) =
    updateTape (fun i => t (-i)) (-h) w := by
  funext i
  by_cases p : -i = h
  · have q : i = -h := by omega
    simp [updateTape, q]
  · have q : i ≠ -h := by omega
    simp [updateTape, p, q]

theorem reflect_step (M : Machine) (c : Cfg) :
    step (reflectMachine M) (reflectCfg c) =
    (step M c).map reflectCfg := by
  cases h : M c.state (c.tape c.head) with
  | none => simp [step,reflectMachine,reflectCfg,h]
  | some instr =>
    rcases instr with ⟨w,d,s⟩
    have hhead : -c.head + d.mirror.dx = -(c.head + d.dx) := by
      cases d <;> simp [Dir.mirror,Dir.dx] <;> omega
    simp [step, reflectMachine, reflectCfg, h, hhead, reflect_update]
theorem reflect_cfg_twice (c : Cfg) : reflectCfg (reflectCfg c) = c := by
  cases c with
  | mk s h t =>
    simp [reflectCfg]

theorem reflect_machine_twice (M : Machine) :
    reflectMachine (reflectMachine M) = M := by
  funext s b
  cases h : M s b with
  | none => simp [reflectMachine, h]
  | some i =>
    rcases i with ⟨w,d,q⟩
    cases d <;> simp [reflectMachine, h, Dir.mirror]

/-- Explicit bijection of all six running states. -/
structure StatePerm where
  toFun : State → State
  invFun : State → State
  left_inv : ∀ s, invFun (toFun s) = s
  right_inv : ∀ s, toFun (invFun s) = s

instance : CoeFun StatePerm (fun _ => State → State) := ⟨StatePerm.toFun⟩

def StatePerm.symm (e : StatePerm) : StatePerm :=
  ⟨e.invFun, e.toFun, e.right_inv, e.left_inv⟩

@[simp] theorem StatePerm.symm_apply_apply (e : StatePerm) (s : State) :
    e.symm (e s) = s := e.left_inv s

@[simp] theorem StatePerm.apply_symm_apply (e : StatePerm) (s : State) :
    e (e.symm s) = s := e.right_inv s

/-- Permute machine state identifiers and transport the entire configuration. -/
def renameCfg (e : StatePerm) (c : Cfg) : Cfg :=
  ⟨e c.state, c.head, c.tape⟩

def renameMachine (e : StatePerm) (M : Machine) : Machine :=
  fun s bit => (M (e.symm s) bit).map fun (w,d,q) => (w,d,e q)

theorem rename_step (M : Machine) (e : StatePerm) (c : Cfg) :
    step (renameMachine e M) (renameCfg e c) =
    (step M c).map (renameCfg e) := by
  cases h : M c.state (c.tape c.head) with
  | none => simp [step,renameMachine,renameCfg,h]
  | some instr =>
    rcases instr with ⟨w,d,q⟩
    simp [step,renameMachine,renameCfg,h]

theorem rename_cfg_roundtrip (e : StatePerm) (c : Cfg) :
    renameCfg e.symm (renameCfg e c) = c := by
  cases c
  simp [renameCfg]

theorem rename_machine_roundtrip (e : StatePerm) (M : Machine) :
    renameMachine e.symm (renameMachine e M) = M := by
  funext s b
  cases h : M s b with
  | none => simp [renameMachine,h]
  | some instr =>
    rcases instr with ⟨w,d,q⟩
    simp [renameMachine,h]

/-- A reusable run-level transport principle for arbitrary raw machines. -/
theorem run_transport (M N : Machine) (f : Cfg → Cfg)
    (hf : ∀ c, step N (f c) = (step M c).map f)
    (n : Nat) (initial : Option Cfg) :
    run N n (initial.map f) = (run M n initial).map f := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [run, ih]
    cases h : run M n initial with
    | none => simp
    | some c => simp [hf]

theorem halts_transport_forward (M N : Machine) (f : Cfg → Cfg)
    (hf : ∀ c, step N (f c) = (step M c).map f)
    (s t : State) (hb : f (blank s) = blank t)
    (h : haltsFrom M s) : haltsFrom N t := by
  obtain ⟨n,c,hr,hs⟩ := h
  have hrun := run_transport M N f hf n (some (blank s))
  simp only [Option.map_some,hb,hr] at hrun
  refine ⟨n,f c,hrun,?_⟩
  rw [hf,hs]
  rfl

theorem reflect_halts_iff (M : Machine) (s : State) :
    haltsFrom (reflectMachine M) s ↔ haltsFrom M s := by
  constructor
  · intro h
    have hh := halts_transport_forward (reflectMachine M)
      (reflectMachine (reflectMachine M)) reflectCfg
      (reflect_step (reflectMachine M)) s s (by simp [reflectCfg,blank]) h
    simpa only [reflect_machine_twice] using hh
  · intro h
    exact halts_transport_forward M (reflectMachine M) reflectCfg
      (reflect_step M) s s (by simp [reflectCfg,blank]) h

theorem rename_halts_iff (M : Machine) (e : StatePerm) (s : State) :
    haltsFrom (renameMachine e M) (e s) ↔ haltsFrom M s := by
  constructor
  · intro h
    have hh := halts_transport_forward (renameMachine e M)
      (renameMachine e.symm (renameMachine e M)) (renameCfg e.symm)
      (rename_step (renameMachine e M) e.symm) (e s) s
      (by simp [renameCfg,blank]) h
    simpa only [rename_machine_roundtrip] using hh
  · intro h
    exact halts_transport_forward M (renameMachine e M) (renameCfg e)
      (rename_step M e) s (e s) (by rfl) h

/-- Complete proof transport under state renaming and optional mirror. The
    initial state is always mapped explicitly to its renamed coordinate. -/
theorem relabel_reflect_halts_iff (M : Machine) (e : StatePerm)
    (mirror : Bool) (s : State) :
    haltsFrom (renameMachine e (if mirror then reflectMachine M else M)) (e s)
      ↔ haltsFrom M s := by
  cases mirror with
  | false => simpa using rename_halts_iff M e s
  | true =>
      simpa using (Iff.trans (rename_halts_iff (reflectMachine M) e s)
        (reflect_halts_iff M s))

/-- Exactly n live steps followed by an undefined transition. -/
def haltsAt (M : Machine) (s : State) (n : Nat) : Prop :=
  ∃ c, run M n (some (blank s))=some c ∧ step M c=none

theorem haltsAt_transport_forward (M N : Machine) (f : Cfg → Cfg)
    (hf : ∀ c, step N (f c)=(step M c).map f)
    (s t : State) (hb : f (blank s)=blank t) (n : Nat)
    (h : haltsAt M s n) : haltsAt N t n := by
  obtain ⟨c,hr,hs⟩ := h
  have hrun := run_transport M N f hf n (some (blank s))
  simp only [Option.map_some,hb,hr] at hrun
  exact ⟨f c,hrun,by rw [hf,hs]; rfl⟩

theorem reflect_haltsAt_iff (M : Machine) (s : State) (n : Nat) :
    haltsAt (reflectMachine M) s n ↔ haltsAt M s n := by
  constructor
  · intro h
    have hh := haltsAt_transport_forward (reflectMachine M)
      (reflectMachine (reflectMachine M)) reflectCfg
      (reflect_step (reflectMachine M)) s s (by simp [reflectCfg,blank]) n h
    simpa only [reflect_machine_twice] using hh
  · intro h
    exact haltsAt_transport_forward M (reflectMachine M) reflectCfg
      (reflect_step M) s s (by simp [reflectCfg,blank]) n h

theorem rename_haltsAt_iff (M : Machine) (e : StatePerm) (s : State) (n : Nat) :
    haltsAt (renameMachine e M) (e s) n ↔ haltsAt M s n := by
  constructor
  · intro h
    have hh := haltsAt_transport_forward (renameMachine e M)
      (renameMachine e.symm (renameMachine e M)) (renameCfg e.symm)
      (rename_step (renameMachine e M) e.symm) (e s) s
      (by simp [renameCfg,blank]) n h
    simpa only [rename_machine_roundtrip] using hh
  · intro h
    exact haltsAt_transport_forward M (renameMachine e M) (renameCfg e)
      (rename_step M e) s (e s) (by rfl) n h

theorem relabel_reflect_haltsAt_iff (M : Machine) (e : StatePerm)
    (mirror : Bool) (s : State) (n : Nat) :
    haltsAt (renameMachine e (if mirror then reflectMachine M else M)) (e s) n
      ↔ haltsAt M s n := by
  cases mirror with
  | false => simpa using rename_haltsAt_iff M e s n
  | true =>
      simpa using (Iff.trans (rename_haltsAt_iff (reflectMachine M) e s n)
        (reflect_haltsAt_iff M s n))

#print axioms reflect_step
#print axioms rename_step
#print axioms run_transport
#print axioms relabel_reflect_halts_iff
#print axioms relabel_reflect_haltsAt_iff
end BB6.Portfolio
