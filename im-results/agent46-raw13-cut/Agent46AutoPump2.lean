import Agent46AutoPump

namespace BB6Coverage.Agent31Pump.Auto2
open BB6Coverage.Agent31Pump.Auto (knownRun knownRun_sound extend normAux normAux_sound Frame rep_add)
open BB6Coverage Agent31Pump

/-- A finite sequence of parametric repeated blocks, with either of two independent exponents. -/
inductive Word where
  | lit (xs : List Bool)
  | periodic (pre block : List Bool) (idx : Bool) (post : Word)
  deriving DecidableEq, Repr

def Word.eval (w : Word) (n m : Nat) : List Bool :=
  match w with
  | .lit xs => xs
  | .periodic pre block idx post => pre ++ rep block (if idx then m else n) ++ post.eval n m

def Word.pop : Word → Option (Bool × Word)
  | .lit [] => some (false,.lit [])
  | .lit (a::xs) => some (a,.lit xs)
  | .periodic [] _ _ _ => none
  | .periodic (a::xs) b i s => some (a,.periodic xs b i s)

def Word.push (xs : List Bool) : Word → Word
  | .lit ys => .lit (xs++ys)
  | .periodic pre b i s => .periodic (xs++pre) b i s

theorem Word.pop_sound {w : Word} {a : Bool} {r : Word}
    (h : w.pop = some (a,r)) (n m : Nat) :
    (w.eval n m).headD false = a ∧ (w.eval n m).tail = r.eval n m := by
  cases w with
  | lit xs => cases xs <;> simp [Word.pop] at h <;> obtain ⟨rfl,rfl⟩ := h <;> simp [Word.eval]
  | periodic pre b i s => cases pre <;> simp [Word.pop] at h
                         <;> obtain ⟨rfl,rfl⟩ := h <;> simp [Word.eval]

theorem Word.push_sound (xs : List Bool) (w : Word) (n m : Nat) :
    (w.push xs).eval n m = xs ++ w.eval n m := by
  cases w <;> simp [Word.push,Word.eval,List.append_assoc]

structure PZ where
  q : Fin 6
  l : Word
  r : Word
  deriving DecidableEq, Repr

def PZ.eval (z : PZ) (n m : Nat) : Z0 := ⟨z.q,z.l.eval n m,z.r.eval n m⟩

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

theorem pstep_sound (p : PartialMachine) {z z' : PZ} (h : pstep p z = some z') (n m : Nat) :
    step0 p (z.eval n m) = some (z'.eval n m) := by
  unfold pstep at h
  cases hl : z.l.pop with
  | none => simp [hl] at h
  | some pair =>
    rcases pair with ⟨a,l⟩
    simp only [hl] at h
    obtain ⟨ha,ht⟩ := Word.pop_sound hl n m
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
          obtain ⟨hb,htr⟩ := Word.pop_sound hr n m
          unfold step0 PZ.eval
          simp only [ha,hm,Option.map_some,move0,hd,ite_true,ht,hb,htr,Word.push_sound,List.cons_append,List.nil_append]

/-- An action consumes one symbolic primitive or transfers every copy of
    the unknown repeated word, using an explicitly checked local trace. -/
inductive Action where
  | step
  | right (lp rp I O : List Bool) (L R : Word) (idx : Bool) (k : Nat)
  | left (lp rp I O : List Bool) (L R : Word) (idx : Bool) (k : Nat)
  deriving DecidableEq, Repr

structure Result where
  z : PZ
  a : Nat
  b : Nat
  c : Nat
  deriving DecidableEq, Repr

def action (p : PartialMachine) (op : Action) (z : PZ) : Option Result :=
  match op with
  | .step => (pstep p z).map fun y => ⟨y,0,0,1⟩
  | .right lp rp I O L R idx k =>
    if z.l = L.push lp ∧ z.r = .periodic rp I idx R ∧
        knownRun p k ⟨z.q,lp,rp++I⟩ = some ⟨z.q,lp++O,rp⟩ then
      some ⟨⟨z.q,.periodic lp O idx L,R.push rp⟩,if idx then 0 else k,if idx then k else 0,0⟩
    else none
  | .left lp rp I O L R idx k =>
    if z.l = .periodic lp I idx L ∧ z.r = R.push rp ∧
        knownRun p k ⟨z.q,lp++I,rp⟩ = some ⟨z.q,lp,rp++O⟩ then
      some ⟨⟨z.q,L.push lp,.periodic rp O idx R⟩,if idx then 0 else k,if idx then k else 0,0⟩
    else none

theorem action_sound (p : PartialMachine) (op : Action) {z : PZ} {out : Result}
    (h : action p op z = some out) (n m : Nat) :
    run0 p (out.a*n+out.b*m+out.c) (z.eval n m) = some (out.z.eval n m) := by
  cases op with
  | step =>
    simp only [action] at h
    cases hs : pstep p z with
    | none => simp [hs] at h
    | some y =>
      simp [hs] at h
      subst out
      simp [run0,pstep_sound p hs n m]
  | right lp rp I O L R idx k =>
    simp only [action] at h
    split at h
    next hc =>
      simp only [Option.some.injEq] at h
      subst out
      have one (L R : List Bool) : run0 p k ⟨z.q,lp++L,rp++I++R⟩ =
          some ⟨z.q,lp++O++L,rp++R⟩ := by
        simpa [extend] using knownRun_sound p k hc.2.2 L R
      cases idx
      · simpa [PZ.eval,Word.eval,hc.1,hc.2.1,Word.push_sound] using
          sweepR p z.q lp rp I O k one n (L.eval n m) (R.eval n m)
      · simpa [PZ.eval,Word.eval,hc.1,hc.2.1,Word.push_sound] using
          sweepR p z.q lp rp I O k one m (L.eval n m) (R.eval n m)
    next => simp at h
  | left lp rp I O L R idx k =>
    simp only [action] at h
    split at h
    next hc =>
      simp only [Option.some.injEq] at h
      subst out
      have one (L R : List Bool) : run0 p k ⟨z.q,lp++I++L,rp++R⟩ =
          some ⟨z.q,lp++L,rp++O++R⟩ := by
        simpa [extend] using knownRun_sound p k hc.2.2 L R
      cases idx
      · simpa [PZ.eval,Word.eval,hc.1,hc.2.1,Word.push_sound] using
          sweepL p z.q lp rp I O k one n (L.eval n m) (R.eval n m)
      · simpa [PZ.eval,Word.eval,hc.1,hc.2.1,Word.push_sound] using
          sweepL p z.q lp rp I O k one m (L.eval n m) (R.eval n m)
    next => simp at h

def traceRun (p : PartialMachine) : List Action → PZ → Option Result
  | [],z => some ⟨z,0,0,0⟩
  | op::ops,z => do
    let a ← action p op z
    let b ← traceRun p ops a.z
    return ⟨b.z,a.a+b.a,a.b+b.b,a.c+b.c⟩

theorem traceRun_sound (p : PartialMachine) (ops : List Action) {z : PZ} {out : Result}
    (h : traceRun p ops z = some out) (n m : Nat) :
    run0 p (out.a*n+out.b*m+out.c) (z.eval n m) = some (out.z.eval n m) := by
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
        have hh := join0 (action_sound p op ha n m) (ih hb)
        simpa [Nat.add_mul,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using hh


def Word.normWith (pre0 : List Bool) : Word → Word
  | .lit xs => .lit (pre0++xs)
  | .periodic p b i s =>
    let f := normAux (pre0++p).reverse b.reverse []
    .periodic f.pre f.block i (s.normWith f.moved)

theorem Word.normWith_sound (w : Word) (pre0 : List Bool) (n m : Nat) :
    (w.normWith pre0).eval n m = pre0 ++ w.eval n m := by
  induction w generalizing pre0 with
  | lit => rfl
  | periodic p b i s ih =>
    simp only [Word.normWith,Word.eval,ih]
    change (normAux (pre0++p).reverse b.reverse []).eval (if i then m else n) (s.eval n m) = _
    rw [normAux_sound,List.reverse_reverse,List.reverse_reverse]
    simp only [List.nil_append,List.append_assoc]

def Word.norm (w : Word) : Word := w.normWith []
theorem Word.norm_sound (w : Word) (n m : Nat) : w.norm.eval n m = w.eval n m := by
  simp [Word.norm,Word.normWith_sound]
def PZ.norm (z : PZ) : PZ := ⟨z.q,z.l.norm,z.r.norm⟩
theorem PZ.norm_sound (z : PZ) (n m : Nat) : z.norm.eval n m = z.eval n m := by
  simp [PZ.norm,PZ.eval,Word.norm_sound]
structure Cert where
  first : PZ
  last : PZ
  ops : List Action
  a : Nat
  b : Nat
  c : Nat
  deriving DecidableEq, Repr

def check (p : PartialMachine) (c : Cert) : Bool :=
  match traceRun p c.ops c.first with
  | none => false
  | some out => decide (out.a=c.a ∧ out.b=c.b ∧ out.c=c.c ∧ out.z.norm=c.last.norm)

theorem sound (p : PartialMachine) (c : Cert) (h : check p c = true) (n m : Nat) :
    run0 p (c.a*n+c.b*m+c.c) (c.first.eval n m) = some (c.last.eval n m) := by
  unfold check at h
  cases hr : traceRun p c.ops c.first with
  | none => simp [hr] at h
  | some out =>
    simp only [hr,decide_eq_true_eq] at h
    have hs := traceRun_sound p c.ops hr n m
    have hn := congrArg (fun z : PZ => z.eval n m) h.2.2.2
    rw [PZ.norm_sound,PZ.norm_sound] at hn
    rw [h.1,h.2.1,h.2.2.1,hn] at hs
    exact hs
#print axioms sound
end BB6Coverage.Agent31Pump.Auto2
