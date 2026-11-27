import Agent46AutoPump

set_option maxHeartbeats 0
namespace BB6Coverage.Agent31Pump.Auto.OpenLeft
open BB6Coverage Agent31Pump Auto

/-- A protected tail can be arbitrary; a primitive action must not inspect it.
    All existing whole-block transfers already operate on arbitrary tails. -/
def Word.attach (w : Auto.Word) (tail : List Bool) : Auto.Word :=
  match w with
  | .lit xs => .lit (xs ++ tail)
  | .periodic pre block post => .periodic pre block (attach post tail)

theorem attach_eval (w : Auto.Word) (tail : List Bool) (n : Nat) :
    (Word.attach w tail).eval n = w.eval n ++ tail := by
  induction w with
  | lit => rfl
  | periodic pre block post ih => simp [Word.attach,Auto.Word.eval,ih,List.append_assoc]

theorem attach_push (w : Auto.Word) (xs tail : List Bool) :
    Word.attach (w.push xs) tail = (Word.attach w tail).push xs := by
  cases w <;> simp [Word.attach,Auto.Word.push,List.append_assoc]

def protectedPop : Auto.Word → Option (Bool × Auto.Word)
  | .lit [] => none
  | w => w.pop

theorem protectedPop_attach {w : Auto.Word} {a : Bool} {r : Auto.Word}
    (h : protectedPop w = some (a,r)) (tail : List Bool) :
    (Word.attach w tail).pop = some (a,Word.attach r tail) := by
  cases w with
  | lit xs =>
    cases xs with
    | nil => contradiction
    | cons x xs =>
      simp only [protectedPop,Auto.Word.pop,Option.some.injEq,Prod.mk.injEq] at h
      obtain ⟨rfl,rfl⟩ := h
      rfl
  | periodic pre block post =>
    cases pre with
    | nil => contradiction
    | cons x pre =>
      simp only [protectedPop,Auto.Word.pop,Option.some.injEq,Prod.mk.injEq] at h
      obtain ⟨rfl,rfl⟩ := h
      rfl

def attachZ (z : PZ) (tail : List Bool) : PZ := ⟨z.q,Word.attach z.l tail,z.r⟩
def attachResult (r : Result) (tail : List Bool) : Result := ⟨attachZ r.z tail,r.a,r.b⟩
def attachOp (op : Action) (tail : List Bool) : Action :=
  match op with
  | .step => .step
  | .right lp rp I O L R k => .right lp rp I O (Word.attach L tail) R k
  | .left lp rp I O L R k => .left lp rp I O (Word.attach L tail) R k

def step (p : PartialMachine) (z : PZ) : Option PZ :=
  match protectedPop z.l with
  | none => none
  | some (a,l) =>
    match (p (z.q,a)).bind id with
    | none => none
    | some mv =>
      if mv.right then
        match z.r.pop with
        | none => none
        | some (b,r) => some ⟨mv.next,l.push [b,mv.write],r⟩
      else some ⟨mv.next,l,z.r.push [mv.write]⟩

theorem step_attach (p : PartialMachine) {z y : PZ} (h : step p z = some y)
    (tail : List Bool) : pstep p (attachZ z tail) = some (attachZ y tail) := by
  unfold step at h
  unfold pstep attachZ
  cases hl : protectedPop z.l with
  | none => simp [hl] at h
  | some pair =>
    rcases pair with ⟨a,l⟩
    simp only [hl] at h
    rw [protectedPop_attach hl tail]
    cases hm : (p (z.q,a)).bind id with
    | none => simp [hm] at h
    | some mv =>
      simp only [hm] at h ⊢
      cases hd : mv.right with
      | false =>
        simp [hd] at h
        subst y
        rfl
      | true =>
        simp only [hd,ite_true] at h ⊢
        cases hr : z.r.pop with
        | none => simp [hr] at h
        | some pair =>
          rcases pair with ⟨b,r⟩
          simp [hr] at h
          subst y
          simp [attach_push]

def action (p : PartialMachine) (op : Action) (z : PZ) : Option Result :=
  match op with
  | .step => (step p z).map fun y => ⟨y,0,1⟩
  | op => Auto.action p op z

theorem action_attach (p : PartialMachine) (op : Action) {z : PZ} {out : Result}
    (h : action p op z = some out) (tail : List Bool) :
    Auto.action p (attachOp op tail) (attachZ z tail) = some (attachResult out tail) := by
  cases op with
  | step =>
    simp only [action] at h
    cases hs : step p z with
    | none => simp [hs] at h
    | some y =>
      simp [hs] at h
      subst out
      simp [attachOp,Auto.action,step_attach p hs tail,attachResult]
  | right lp rp I O L R k =>
    simp only [action,Auto.action] at h
    split at h
    next hc =>
      simp only [Option.some.injEq] at h
      subst out
      simp [attachOp,Auto.action,attachZ,attachResult,hc.1,hc.2.1,hc.2.2,Word.attach,attach_push]
    next => simp at h
  | left lp rp I O L R k =>
    simp only [action,Auto.action] at h
    split at h
    next hc =>
      simp only [Option.some.injEq] at h
      subst out
      simp [attachOp,Auto.action,attachZ,attachResult,hc.1,hc.2.1,hc.2.2,Word.attach,attach_push]
    next => simp at h

theorem action_sound (p : PartialMachine) (op : Action) {z : PZ} {out : Result}
    (h : action p op z = some out) (n : Nat) (tail : List Bool) :
    run0 p (out.a*n+out.b) ((attachZ z tail).eval n) = some ((attachZ out.z tail).eval n) := by
  exact Auto.action_sound p (attachOp op tail) (action_attach p op h tail) n

def traceRun (p : PartialMachine) : List Action → PZ → Option Result
  | [],z => some ⟨z,0,0⟩
  | op::ops,z => do
    let a ← action p op z
    let b ← traceRun p ops a.z
    return ⟨b.z,a.a+b.a,a.b+b.b⟩

theorem traceRun_sound (p : PartialMachine) (ops : List Action) {z : PZ} {out : Result}
    (h : traceRun p ops z = some out) (n : Nat) (tail : List Bool) :
    run0 p (out.a*n+out.b) ((attachZ z tail).eval n) = some ((attachZ out.z tail).eval n) := by
  induction ops generalizing z out with
  | nil => simp [traceRun] at h; subst out; simp [run0]
  | cons op ops ih =>
    simp only [traceRun] at h
    cases ha : action p op z with
    | none => simp [ha] at h
    | some a =>
      simp only [ha] at h
      cases hb : traceRun p ops a.z with
      | none => simp [hb] at h
      | some b =>
        simp [hb] at h
        subst out
        have hh := join0 (action_sound p op ha n tail) (ih hb)
        simpa [Nat.add_mul,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using hh

theorem attachZ_eval (z : PZ) (n : Nat) (tail : List Bool) :
    (attachZ z tail).eval n = ⟨z.q,z.l.eval n ++ tail,z.r.eval n⟩ := by
  simp [attachZ,PZ.eval,attach_eval]

theorem norm_attachZ_eval (z : PZ) (n : Nat) (tail : List Bool) :
    (attachZ z.norm tail).eval n = (attachZ z tail).eval n := by
  simp [attachZ_eval,PZ.norm,Word.norm_sound]

#print axioms traceRun_sound
end BB6Coverage.Agent31Pump.Auto.OpenLeft
