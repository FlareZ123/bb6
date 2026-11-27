import Agent46AutoPump

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace BB6Coverage.Agent31Pump.Tails
open BB6Coverage Agent31Pump
/-- A finite sequence of parametric repeated blocks, with either of two independent exponents. -/
inductive Word where
  | lit (xs : List Bool)
  | tail (pre : List Bool) (tag : Bool)
  | periodic (pre block : List Bool) (tag : Bool) (post : Word)
  deriving DecidableEq, Repr

def Word.eval (w : Word) (n m : Nat) (X Y : List Bool) : List Bool :=
  match w with
  | .lit xs => xs
  | .tail pre tag => pre ++ (if tag then Y else X)
  | .periodic pre block tag post => pre ++ rep block (if tag then m else n) ++ post.eval n m X Y

def Word.pop : Word → Option (Bool × Word)
  | .lit [] => some (false,.lit [])
  | .lit (a::xs) => some (a,.lit xs)
  | .tail [] _ => none
  | .tail (a::xs) tag => some (a,.tail xs tag)
  | .periodic [] _ _ _ => none
  | .periodic (a::xs) b tag s => some (a,.periodic xs b tag s)

def Word.push (xs : List Bool) : Word → Word
  | .lit ys => .lit (xs++ys)
  | .tail pre tag => .tail (xs++pre) tag
  | .periodic pre b tag s => .periodic (xs++pre) b tag s

theorem Word.pop_sound {w : Word} {a : Bool} {r : Word}
    (h : w.pop = some (a,r)) (n m : Nat) (X Y : List Bool) :
    (w.eval n m X Y).headD false = a ∧ (w.eval n m X Y).tail = r.eval n m X Y := by
  cases w with
  | lit xs => cases xs <;> simp [Word.pop] at h <;> obtain ⟨rfl,rfl⟩ := h <;> simp [Word.eval]
  | tail pre tag => cases pre <;> simp [Word.pop] at h <;> obtain ⟨rfl,rfl⟩ := h <;> simp [Word.eval]
  | periodic pre b tag s => cases pre <;> simp [Word.pop] at h
                         <;> obtain ⟨rfl,rfl⟩ := h <;> simp [Word.eval]

theorem Word.push_sound (xs : List Bool) (w : Word) (n m : Nat) (X Y : List Bool) :
    (w.push xs).eval n m X Y = xs ++ w.eval n m X Y := by
  cases w <;> simp [Word.push,Word.eval,List.append_assoc]

structure PZ where
  q : Fin 6
  l : Word
  r : Word
  deriving DecidableEq, Repr

def PZ.eval (z : PZ) (n m : Nat) (X Y : List Bool) : Z0 := ⟨z.q,z.l.eval n m X Y,z.r.eval n m X Y⟩

/-- A primitive step that does not need to inspect an unknown exponent. -/
def pstep (p : PartialMachine) (z : PZ) : Option PZ :=
  match z.l.pop with
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

theorem pstep_sound (p : PartialMachine) {z z' : PZ} (h : pstep p z = some z') (n m : Nat) (X Y : List Bool) :
    step0 p (z.eval n m X Y) = some (z'.eval n m X Y) := by
  unfold pstep at h
  cases hl : z.l.pop with
  | none => simp [hl] at h
  | some pair =>
    rcases pair with ⟨a,l⟩
    simp only [hl] at h
    obtain ⟨ha,ht⟩ := Word.pop_sound hl n m X Y
    cases hm : (p (z.q,a)).bind id with
    | none => simp [hm] at h
    | some mv =>
      simp only [hm] at h
      cases hd : mv.right
      · simp [hd] at h
        subst z'
        unfold step0 PZ.eval
        simp only [ha,hm,Option.map_some,move0,hd,ht,Word.push_sound,List.singleton_append]
        rfl
      · simp [hd] at h
        cases hr : z.r.pop with
        | none => simp [hr] at h
        | some pair =>
          rcases pair with ⟨b,r⟩
          simp [hr] at h
          subst z'
          obtain ⟨hb,htr⟩ := Word.pop_sound hr n m X Y
          unfold step0 PZ.eval
          simp only [ha,hm,Option.map_some,move0,hd,ite_true,ht,hb,htr,Word.push_sound,List.cons_append,List.nil_append]

/-- A block of symbolic primitive steps, avoiding long lists of singleton actions. -/
def pRun (p : PartialMachine) : Nat → PZ → Option PZ
  | 0,z => some z
  | k+1,z => (pstep p z).bind (pRun p k)

theorem pRun_sound (p : PartialMachine) (k : Nat) {z z' : PZ}
    (h : pRun p k z = some z') (n m : Nat) (X Y : List Bool) :
    run0 p k (z.eval n m X Y) = some (z'.eval n m X Y) := by
  induction k generalizing z with
  | zero => simp [pRun] at h; subst z'; rfl
  | succ k ih =>
    simp only [pRun] at h
    cases hs : pstep p z with
    | none => simp [hs] at h
    | some y =>
      simp only [hs,Option.bind_some] at h
      simp only [run0,pstep_sound p hs n m X Y,Option.bind_some]
      exact ih h

inductive Action where
  | steps (k : Nat)
  | right (lp rp I O : List Bool) (tag : Bool) (L R : Word) (k : Nat)
  | left (lp rp I O : List Bool) (tag : Bool) (L R : Word) (k : Nat)
  deriving DecidableEq, Repr

structure Result where
  z : PZ
  a : Nat
  b : Nat
  c : Nat
  deriving DecidableEq, Repr

def action (p : PartialMachine) (op : Action) (z : PZ) : Option Result :=
  match op with
  | .steps k => (pRun p k z).map fun y => ⟨y,0,0,k⟩
  | .right lp rp I O tag L R k =>
    if z.l = L.push lp ∧ z.r = .periodic rp I tag R ∧
        Auto.knownRun p k ⟨z.q,lp,rp++I⟩ = some ⟨z.q,lp++O,rp⟩ then
      some ⟨⟨z.q,.periodic lp O tag L,R.push rp⟩,if tag then 0 else k,if tag then k else 0,0⟩
    else none
  | .left lp rp I O tag L R k =>
    if z.l = .periodic lp I tag L ∧ z.r = R.push rp ∧
        Auto.knownRun p k ⟨z.q,lp++I,rp⟩ = some ⟨z.q,lp,rp++O⟩ then
      some ⟨⟨z.q,L.push lp,.periodic rp O tag R⟩,if tag then 0 else k,if tag then k else 0,0⟩
    else none

theorem action_sound (p : PartialMachine) (op : Action) {z : PZ} {out : Result}
    (h : action p op z = some out) (n m : Nat) (X Y : List Bool) :
    run0 p (out.a*n+out.b*m+out.c) (z.eval n m X Y) = some (out.z.eval n m X Y) := by
  cases op with
  | steps k =>
    simp only [action] at h
    cases hs : pRun p k z with
    | none => simp [hs] at h
    | some y =>
      simp [hs] at h
      subst out
      simpa using pRun_sound p k hs n m X Y
  | right lp rp I O tag L R k =>
    simp only [action] at h
    split at h
    next hc =>
      simp only [Option.some.injEq] at h
      subst out
      have one (L R : List Bool) : run0 p k ⟨z.q,lp++L,rp++I++R⟩ =
          some ⟨z.q,lp++O++L,rp++R⟩ := by
        simpa [Auto.extend] using Auto.knownRun_sound p k hc.2.2 L R
      cases tag with
      | false => simpa [PZ.eval,Word.eval,hc.1,hc.2.1,Word.push_sound] using (sweepR p z.q lp rp I O k one n (L.eval n m X Y) (R.eval n m X Y))
      | true => simpa [PZ.eval,Word.eval,hc.1,hc.2.1,Word.push_sound] using (sweepR p z.q lp rp I O k one m (L.eval n m X Y) (R.eval n m X Y))
    next => simp at h
  | left lp rp I O tag L R k =>
    simp only [action] at h
    split at h
    next hc =>
      simp only [Option.some.injEq] at h
      subst out
      have one (L R : List Bool) : run0 p k ⟨z.q,lp++I++L,rp++R⟩ =
          some ⟨z.q,lp++L,rp++O++R⟩ := by
        simpa [Auto.extend] using Auto.knownRun_sound p k hc.2.2 L R
      cases tag with
      | false => simpa [PZ.eval,Word.eval,hc.1,hc.2.1,Word.push_sound] using (sweepL p z.q lp rp I O k one n (L.eval n m X Y) (R.eval n m X Y))
      | true => simpa [PZ.eval,Word.eval,hc.1,hc.2.1,Word.push_sound] using (sweepL p z.q lp rp I O k one m (L.eval n m X Y) (R.eval n m X Y))
    next => simp at h

def traceRun (p : PartialMachine) : List Action → PZ → Option Result
  | [],z => some ⟨z,0,0,0⟩
  | op::ops,z => do
    let a ← action p op z
    let b ← traceRun p ops a.z
    return ⟨b.z,a.a+b.a,a.b+b.b,a.c+b.c⟩

theorem traceRun_sound (p : PartialMachine) (ops : List Action) {z : PZ} {out : Result}
    (h : traceRun p ops z = some out) (n m : Nat) (X Y : List Bool) :
    run0 p (out.a*n+out.b*m+out.c) (z.eval n m X Y) = some (out.z.eval n m X Y) := by
  induction ops generalizing z out with
  | nil => simp [traceRun] at h; subst out; simp [run0]
  | cons op ops ih =>
    simp only [traceRun] at h
    cases ha : action p op z with
    | none => simp [ha] at h
    | some a =>
      simp only [ha,Option.bind_some] at h
      cases hb : traceRun p ops a.z with
      | none => simp [hb] at h
      | some b =>
        simp [hb] at h
        subst out
        have hh := join0 (action_sound p op ha n m X Y) (ih hb)
        simpa [Nat.add_mul,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using hh

def Word.normWith (pre0 : List Bool) : Word → Word
  | .lit xs => .lit (pre0++xs)
  | .tail pre tag => .tail (pre0++pre) tag
  | .periodic p b tag s =>
    let f := Auto.normAux (pre0++p).reverse b.reverse []
    .periodic f.pre f.block tag (s.normWith f.moved)

theorem Word.normWith_sound (w : Word) (pre0 : List Bool) (n m : Nat) (X Y : List Bool) :
    (w.normWith pre0).eval n m X Y = pre0 ++ w.eval n m X Y := by
  induction w generalizing pre0 with
  | lit => rfl
  | tail => simp [Word.normWith,Word.eval,List.append_assoc]
  | periodic p b tag s ih =>
    simp only [Word.normWith,Word.eval,ih]
    change (Auto.normAux (pre0++p).reverse b.reverse []).eval (if tag then m else n) (s.eval n m X Y) = _
    rw [Auto.normAux_sound,List.reverse_reverse,List.reverse_reverse]
    simp only [List.nil_append,List.append_assoc]

def Word.norm (w : Word) : Word := w.normWith []

theorem Word.norm_sound (w : Word) (n m : Nat) (X Y : List Bool) : w.norm.eval n m X Y = w.eval n m X Y := by
  simp [Word.norm,Word.normWith_sound]

def PZ.norm (z : PZ) : PZ := ⟨z.q,z.l.norm,z.r.norm⟩

theorem PZ.norm_sound (z : PZ) (n m : Nat) (X Y : List Bool) : z.norm.eval n m X Y = z.eval n m X Y := by
  simp [PZ.norm,PZ.eval,Word.norm_sound]

structure Cert where
  source : PZ
  target : PZ
  ops : List Action
  a : Nat
  b : Nat
  c : Nat
  deriving DecidableEq, Repr

def check (p : PartialMachine) (c : Cert) : Bool :=
  match traceRun p c.ops c.source with
  | none => false
  | some out => decide (out.a=c.a ∧ out.b=c.b ∧ out.c=c.c ∧ out.z.norm=c.target.norm)

theorem check_sound (p : PartialMachine) (c : Cert) (h : check p c = true) (n m : Nat) (X Y : List Bool) :
    run0 p (c.a*n+c.b*m+c.c) (c.source.eval n m X Y) = some (c.target.eval n m X Y) := by
  unfold check at h
  cases hr : traceRun p c.ops c.source with
  | none => simp [hr] at h
  | some out =>
    simp only [hr,decide_eq_true_eq] at h
    have hs := traceRun_sound p c.ops hr n m X Y
    have hn := congrArg (fun z : PZ => z.eval n m X Y) h.2.2.2
    rw [PZ.norm_sound,PZ.norm_sound] at hn
    rw [h.1,h.2.1,h.2.2.1,hn] at hs
    exact hs


#print axioms check_sound
end BB6Coverage.Agent31Pump.Tails
