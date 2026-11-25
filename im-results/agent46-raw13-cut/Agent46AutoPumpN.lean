import Agent46AutoPump

namespace BB6Coverage.Agent31Pump.AutoN
open BB6Coverage.Agent31Pump.Auto (knownRun knownRun_sound extend normAux normAux_sound Frame rep_add)
open BB6Coverage Agent31Pump

/-- A finite sequence of parametric repeated blocks, with independently indexed exponents. -/
inductive Word where
  | lit (xs : List Bool)
  | periodic (pre block : List Bool) (idx : Nat) (post : Word)
  deriving DecidableEq, Repr

def Word.eval (w : Word) (ns : Nat → Nat) : List Bool :=
  match w with
  | .lit xs => xs
  | .periodic pre block idx post => pre ++ rep block (ns idx) ++ post.eval ns

def Word.pop : Word → Option (Bool × Word)
  | .lit [] => some (false,.lit [])
  | .lit (a::xs) => some (a,.lit xs)
  | .periodic [] _ _ _ => none
  | .periodic (a::xs) b i s => some (a,.periodic xs b i s)

def Word.push (xs : List Bool) : Word → Word
  | .lit ys => .lit (xs++ys)
  | .periodic pre b i s => .periodic (xs++pre) b i s

theorem Word.pop_sound {w : Word} {a : Bool} {r : Word}
    (h : w.pop = some (a,r)) (ns : Nat → Nat) :
    (w.eval ns).headD false = a ∧ (w.eval ns).tail = r.eval ns := by
  cases w with
  | lit xs => cases xs <;> simp [Word.pop] at h <;> obtain ⟨rfl,rfl⟩ := h <;> simp [Word.eval]
  | periodic pre b i s => cases pre <;> simp [Word.pop] at h
                         <;> obtain ⟨rfl,rfl⟩ := h <;> simp [Word.eval]

theorem Word.push_sound (xs : List Bool) (w : Word) (ns : Nat → Nat) :
    (w.push xs).eval ns = xs ++ w.eval ns := by
  cases w <;> simp [Word.push,Word.eval,List.append_assoc]

structure PZ where
  q : Fin 6
  l : Word
  r : Word
  deriving DecidableEq, Repr

def PZ.eval (z : PZ) (ns : Nat → Nat) : Z0 := ⟨z.q,z.l.eval ns,z.r.eval ns⟩

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

theorem pstep_sound (p : PartialMachine) {z z' : PZ} (h : pstep p z = some z') (ns : Nat → Nat) :
    step0 p (z.eval ns) = some (z'.eval ns) := by
  unfold pstep at h
  cases hl : z.l.pop with
  | none => simp [hl] at h
  | some pair =>
    rcases pair with ⟨a,l⟩
    simp only [hl] at h
    obtain ⟨ha,ht⟩ := Word.pop_sound hl ns
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
          obtain ⟨hb,htr⟩ := Word.pop_sound hr ns
          unfold step0 PZ.eval
          simp only [ha,hm,Option.map_some,move0,hd,ite_true,ht,hb,htr,Word.push_sound,List.cons_append,List.nil_append]

/-- An action consumes one symbolic primitive or transfers every copy of
    the unknown repeated word, using an explicitly checked local trace. -/
inductive Action where
  | step
  | right (lp rp I O : List Bool) (L R : Word) (idx : Nat) (k : Nat)
  | left (lp rp I O : List Bool) (L R : Word) (idx : Nat) (k : Nat)
  deriving DecidableEq, Repr

structure Result where
  z : PZ
  costs : List (Nat × Nat)
  c : Nat
  deriving DecidableEq, Repr

def action (p : PartialMachine) (op : Action) (z : PZ) : Option Result :=
  match op with
  | .step => (pstep p z).map fun y => ⟨y,[],1⟩
  | .right lp rp I O L R idx k =>
    if z.l = L.push lp ∧ z.r = .periodic rp I idx R ∧
        knownRun p k ⟨z.q,lp,rp++I⟩ = some ⟨z.q,lp++O,rp⟩ then
      some ⟨⟨z.q,.periodic lp O idx L,R.push rp⟩,[(idx,k)],0⟩
    else none
  | .left lp rp I O L R idx k =>
    if z.l = .periodic lp I idx L ∧ z.r = R.push rp ∧
        knownRun p k ⟨z.q,lp++I,rp⟩ = some ⟨z.q,lp,rp++O⟩ then
      some ⟨⟨z.q,L.push lp,.periodic rp O idx R⟩,[(idx,k)],0⟩
    else none

def evalCosts (cs : List (Nat × Nat)) (ns : Nat → Nat) : Nat :=
  (cs.map fun c => c.2 * ns c.1).sum

theorem action_sound (p : PartialMachine) (op : Action) {z : PZ} {out : Result}
    (h : action p op z = some out) (ns : Nat → Nat) :
    run0 p (evalCosts out.costs ns+out.c) (z.eval ns) = some (out.z.eval ns) := by
  cases op with
  | step =>
    simp only [action] at h
    cases hs : pstep p z with
    | none => simp [hs] at h
    | some y =>
      simp [hs] at h
      subst out
      simp [run0,pstep_sound p hs ns,evalCosts]
  | right lp rp I O L R idx k =>
    simp only [action] at h
    split at h
    next hc =>
      simp only [Option.some.injEq] at h
      subst out
      have one (L R : List Bool) : run0 p k ⟨z.q,lp++L,rp++I++R⟩ =
          some ⟨z.q,lp++O++L,rp++R⟩ := by
        simpa [extend] using knownRun_sound p k hc.2.2 L R
      simpa [PZ.eval,Word.eval,hc.1,hc.2.1,Word.push_sound,evalCosts] using
        sweepR p z.q lp rp I O k one (ns idx) (L.eval ns) (R.eval ns)
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
      simpa [PZ.eval,Word.eval,hc.1,hc.2.1,Word.push_sound,evalCosts] using
        sweepL p z.q lp rp I O k one (ns idx) (L.eval ns) (R.eval ns)
    next => simp at h

def traceRun (p : PartialMachine) : List Action → PZ → Option Result
  | [],z => some ⟨z,[],0⟩
  | op::ops,z => do
    let a ← action p op z
    let b ← traceRun p ops a.z
    return ⟨b.z,a.costs++b.costs,a.c+b.c⟩

theorem traceRun_sound (p : PartialMachine) (ops : List Action) {z : PZ} {out : Result}
    (h : traceRun p ops z = some out) (ns : Nat → Nat) :
    run0 p (evalCosts out.costs ns+out.c) (z.eval ns) = some (out.z.eval ns) := by
  induction ops generalizing z out with
  | nil => simp [traceRun] at h; subst out; simp [run0,evalCosts]
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
        have hh := join0 (action_sound p op ha ns) (ih hb)
        simpa [evalCosts,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using hh


def Word.normWith (pre0 : List Bool) : Word → Word
  | .lit xs => .lit (pre0++xs)
  | .periodic p b i s =>
    let f := normAux (pre0++p).reverse b.reverse []
    .periodic f.pre f.block i (s.normWith f.moved)

theorem Word.normWith_sound (w : Word) (pre0 : List Bool) (ns : Nat → Nat) :
    (w.normWith pre0).eval ns = pre0 ++ w.eval ns := by
  induction w generalizing pre0 with
  | lit => rfl
  | periodic p b i s ih =>
    simp only [Word.normWith,Word.eval,ih]
    change (normAux (pre0++p).reverse b.reverse []).eval (ns i) (s.eval ns) = _
    rw [normAux_sound,List.reverse_reverse,List.reverse_reverse]
    simp only [List.nil_append,List.append_assoc]

def Word.norm (w : Word) : Word := w.normWith []
theorem Word.norm_sound (w : Word) (ns : Nat → Nat) : w.norm.eval ns = w.eval ns := by
  simp [Word.norm,Word.normWith_sound]
def PZ.norm (z : PZ) : PZ := ⟨z.q,z.l.norm,z.r.norm⟩
theorem PZ.norm_sound (z : PZ) (ns : Nat → Nat) : z.norm.eval ns = z.eval ns := by
  simp [PZ.norm,PZ.eval,Word.norm_sound]
structure Cert where
  first : PZ
  last : PZ
  ops : List Action
  costs : List (Nat × Nat)
  c : Nat
  deriving DecidableEq, Repr

def check (p : PartialMachine) (c : Cert) : Bool :=
  match traceRun p c.ops c.first with
  | none => false
  | some out => decide (out.costs=c.costs ∧ out.c=c.c ∧ out.z.norm=c.last.norm)

theorem sound (p : PartialMachine) (c : Cert) (h : check p c = true) (ns : Nat → Nat) :
    run0 p (evalCosts c.costs ns+c.c) (c.first.eval ns) = some (c.last.eval ns) := by
  unfold check at h
  cases hr : traceRun p c.ops c.first with
  | none => simp [hr] at h
  | some out =>
    simp only [hr,decide_eq_true_eq] at h
    have hs := traceRun_sound p c.ops hr ns
    have hn := congrArg (fun z : PZ => z.eval ns) h.2.2
    rw [PZ.norm_sound,PZ.norm_sound] at hn
    rw [h.1,h.2.1,hn] at hs
    exact hs
#print axioms sound
end BB6Coverage.Agent31Pump.AutoN
