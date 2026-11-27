import SweepPumping
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace BB6Coverage.Agent6SweepTrace
open BB6Coverage BB6Coverage.Agent31Pump

/-- Finite-window simulator: refuse even a read of an implicit blank, including
    the extra cell consumed by a right move. A successful finite-window trace
    is thus a literal identity in arbitrary untouched left and right tails. -/
def strictStep (p : PartialMachine) (z : Z0) : Option Z0 :=
  match z.l with
  | [] => none
  | a::L => match p (z.q,a) with
    | some (some mv) => if mv.right then
        match z.r with
        | [] => none
        | b::R => some ⟨mv.next,b::mv.write::L,R⟩
      else some ⟨mv.next,L,mv.write::z.r⟩
    | _ => none

def strictRun (p : PartialMachine) : Nat → Z0 → Option Z0
  | 0,z => some z
  | n+1,z => (strictStep p z).bind (strictRun p n)

def extend (z : Z0) (L R : List Bool) : Z0 := ⟨z.q,z.l++L,z.r++R⟩

theorem step_extend (p : PartialMachine) (z z' : Z0) (L R : List Bool)
    (h : strictStep p z = some z') :
    step0 p (extend z L R) = some (extend z' L R) := by
  rcases z with ⟨q,l,r⟩
  cases l with
  | nil => simp [strictStep] at h
  | cons a l =>
    cases hp : p (q,a) with
    | none => simp [strictStep,hp] at h
    | some t =>
      cases t with
      | none => simp [strictStep,hp] at h
      | some mv =>
        cases hr : mv.right with
        | false =>
          simp [strictStep,hp,hr] at h
          subst z'
          simp [step0,extend,move0,hp,hr]
        | true =>
          cases r with
          | nil => simp [strictStep,hp,hr] at h
          | cons b r =>
            simp [strictStep,hp,hr] at h
            subst z'
            simp [step0,extend,move0,hp,hr]

theorem run_extend (p : PartialMachine) (n : Nat) (z z' : Z0) (L R : List Bool)
    (h : strictRun p n z = some z') :
    run0 p n (extend z L R) = some (extend z' L R) := by
  induction n generalizing z with
  | zero => cases Option.some.inj h; rfl
  | succ n ih =>
    cases hs : strictStep p z with
    | none => simp [strictRun,hs] at h
    | some t =>
      have ht : strictRun p n t = some z' := by simpa only [strictRun,hs,Option.bind_some] using h
      rw [run0,step_extend p z t L R hs]
      exact ih t ht

def removePrefix (pre xs : List Bool) : Option (List Bool) :=
  if xs.take pre.length = pre then some (xs.drop pre.length) else none

theorem removePrefix_sound {pre xs rest : List Bool}
    (h : removePrefix pre xs = some rest) : xs = pre ++ rest := by
  unfold removePrefix at h
  split at h
  next ht =>
    have hr : xs.drop pre.length = rest := Option.some.inj h
    calc
      xs = xs.take pre.length ++ xs.drop pre.length := (List.take_append_drop _ _).symm
      _ = pre ++ rest := by rw [ht,hr]
  next => contradiction

inductive Action where
  | raw (k : Nat)
  | left (lp rp I O : List Bool) (k n : Nat)
  | right (lp rp I O : List Bool) (k n : Nat)

def applyAction (p : PartialMachine) (z : Z0) : Action → Option (Nat × Z0)
  | .raw k => (run0 p k z).map fun z' => (k,z')
  | .left lp rp I O k n =>
    if strictRun p k ⟨z.q,lp++I,rp⟩ = some ⟨z.q,lp,rp++O⟩ then
      match removePrefix (lp++rep I n) z.l, removePrefix rp z.r with
      | some L, some R => some (k*n,⟨z.q,lp++L,rp++rep O n++R⟩)
      | _,_ => none
    else none
  | .right lp rp I O k n =>
    if strictRun p k ⟨z.q,lp,rp++I⟩ = some ⟨z.q,lp++O,rp⟩ then
      match removePrefix lp z.l, removePrefix (rp++rep I n) z.r with
      | some L,some R => some (k*n,⟨z.q,lp++rep O n++L,rp++R⟩)
      | _,_ => none
    else none

theorem action_sound (p : PartialMachine) (z z' : Z0) (a : Action) (k : Nat)
    (h : applyAction p z a = some (k,z')) : run0 p k z = some z' := by
  cases a with
  | raw t =>
    cases hr : run0 p t z with
    | none => simp [applyAction,hr] at h
    | some u => simp [applyAction,hr] at h; obtain ⟨rfl,rfl⟩ := h; exact hr
  | left lp rp I O t n =>
    simp only [applyAction] at h
    split at h
    next hs =>
      cases hl : removePrefix (lp++rep I n) z.l <;> cases hr : removePrefix rp z.r <;> simp [hl,hr] at h
      next L R =>
        obtain ⟨rfl,rfl⟩ := h
        have hL := removePrefix_sound hl
        have hR := removePrefix_sound hr
        have one : ∀ X Y, run0 p t ⟨z.q,lp++I++X,rp++Y⟩ = some ⟨z.q,lp++X,rp++O++Y⟩ := by
          intro X Y
          exact run_extend p t _ _ X Y hs
        have H := sweepL p z.q lp rp I O t one n L R
        cases z with
        | mk q l r =>
          dsimp at hL hR ⊢ H
          rw [hL,hR]
          simpa only [List.append_assoc] using H
    next => contradiction
  | right lp rp I O t n =>
    simp only [applyAction] at h
    split at h
    next hs =>
      cases hl : removePrefix lp z.l <;> cases hr : removePrefix (rp++rep I n) z.r <;> simp [hl,hr] at h
      next L R =>
        obtain ⟨rfl,rfl⟩ := h
        have hL := removePrefix_sound hl
        have hR := removePrefix_sound hr
        have one : ∀ X Y, run0 p t ⟨z.q,lp++X,rp++I++Y⟩ = some ⟨z.q,lp++O++X,rp++Y⟩ := by
          intro X Y
          exact run_extend p t _ _ X Y hs
        have H := sweepR p z.q lp rp I O t one n L R
        cases z with
        | mk q l r =>
          dsimp at hL hR ⊢ H
          rw [hL,hR]
          simpa only [List.append_assoc] using H
    next => contradiction

def eval (p : PartialMachine) : List Action → Z0 → Option (Nat × Z0)
  | [],z => some (0,z)
  | a::as,z => match applyAction p z a with
    | none => none
    | some (n,t) => (eval p as t).map fun (m,u) => (n+m,u)

theorem eval_sound (p : PartialMachine) (as : List Action) (z z' : Z0) (n : Nat)
    (h : eval p as z = some (n,z')) : run0 p n z = some z' := by
  induction as generalizing z n with
  | nil => simp [eval] at h; obtain ⟨rfl,rfl⟩ := h; rfl
  | cons a as ih =>
    cases ha : applyAction p z a with
    | none => simp [eval,ha] at h
    | some v =>
      rcases v with ⟨k,t⟩
      cases hs : eval p as t with
      | none => simp [eval,ha,hs] at h
      | some v =>
        rcases v with ⟨m,u⟩
        simp [eval,ha,hs] at h
        obtain ⟨rfl,rfl⟩ := h
        exact join0 (action_sound p z t a k ha) (ih t m hs)

#print axioms eval_sound
end BB6Coverage.Agent6SweepTrace
