import SweepPumping

namespace BB6Coverage.Agent31Pump.Auto
open BB6Coverage Agent31Pump

/-- A finite sequence of parametric repeated blocks, all sharing one exponent. -/
inductive Word where
  | lit (xs : List Bool)
  | periodic (pre block : List Bool) (post : Word)
  deriving DecidableEq, Repr

def Word.eval (w : Word) (n : Nat) : List Bool :=
  match w with
  | .lit xs => xs
  | .periodic pre block post => pre ++ rep block n ++ post.eval n

def Word.pop : Word → Option (Bool × Word)
  | .lit [] => some (false,.lit [])
  | .lit (a::xs) => some (a,.lit xs)
  | .periodic [] _ _ => none
  | .periodic (a::xs) b s => some (a,.periodic xs b s)

def Word.push (xs : List Bool) : Word → Word
  | .lit ys => .lit (xs++ys)
  | .periodic pre b s => .periodic (xs++pre) b s

theorem Word.pop_sound {w : Word} {a : Bool} {r : Word}
    (h : w.pop = some (a,r)) (n : Nat) :
    (w.eval n).headD false = a ∧ (w.eval n).tail = r.eval n := by
  cases w with
  | lit xs => cases xs <;> simp [Word.pop] at h <;> obtain ⟨rfl,rfl⟩ := h <;> simp [Word.eval]
  | periodic pre b s => cases pre <;> simp [Word.pop] at h
                         <;> obtain ⟨rfl,rfl⟩ := h <;> simp [Word.eval]

theorem Word.push_sound (xs : List Bool) (w : Word) (n : Nat) :
    (w.push xs).eval n = xs ++ w.eval n := by
  cases w <;> simp [Word.push,Word.eval,List.append_assoc]

structure PZ where
  q : Fin 6
  l : Word
  r : Word
  deriving DecidableEq, Repr

def PZ.eval (z : PZ) (n : Nat) : Z0 := ⟨z.q,z.l.eval n,z.r.eval n⟩

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

theorem pstep_sound (p : PartialMachine) {z z' : PZ} (h : pstep p z = some z') (n : Nat) :
    step0 p (z.eval n) = some (z'.eval n) := by
  unfold pstep at h
  cases hl : z.l.pop with
  | none => simp [hl] at h
  | some pair =>
    rcases pair with ⟨a,l⟩
    simp only [hl] at h
    obtain ⟨ha,ht⟩ := Word.pop_sound hl n
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
          obtain ⟨hb,htr⟩ := Word.pop_sound hr n
          unfold step0 PZ.eval
          simp only [ha,hm,Option.map_some,move0,hd,ite_true,ht,hb,htr,Word.push_sound,List.cons_append,List.nil_append]

/-- Finite execution with two unknown tails: touching either unknown tail
    is rejected, so the returned computation lifts to every pair of tails. -/
def knownStep (p : PartialMachine) (z : Z0) : Option Z0 :=
  match z.l with
  | [] => none
  | a::l =>
    match (p (z.q,a)).bind id with
    | none => none
    | some mv =>
      if mv.right then
        match z.r with
        | [] => none
        | b::r => some ⟨mv.next,b::mv.write::l,r⟩
      else some ⟨mv.next,l,mv.write::z.r⟩

def extend (z : Z0) (L R : List Bool) : Z0 := ⟨z.q,z.l++L,z.r++R⟩

theorem knownStep_sound (p : PartialMachine) {z z' : Z0}
    (h : knownStep p z = some z') (L R : List Bool) :
    step0 p (extend z L R) = some (extend z' L R) := by
  rcases z with ⟨q,l,r⟩
  cases l with
  | nil => simp [knownStep] at h
  | cons a l =>
    simp only [knownStep] at h
    cases hm : (p (q,a)).bind id with
    | none => simp [hm] at h
    | some mv =>
      simp only [hm] at h
      cases hd : mv.right
      · simp [hd] at h
        subst z'
        simp [step0,move0,extend,hm,hd]
      · simp [hd] at h
        cases r with
        | nil => simp at h
        | cons b r =>
          simp at h
          subst z'
          simp [step0,move0,extend,hm,hd]

def knownRun (p : PartialMachine) : Nat → Z0 → Option Z0
  | 0,z => some z
  | n+1,z => (knownStep p z).bind (knownRun p n)

theorem knownRun_sound (p : PartialMachine) (k : Nat) {z z' : Z0}
    (h : knownRun p k z = some z') (L R : List Bool) :
    run0 p k (extend z L R) = some (extend z' L R) := by
  induction k generalizing z with
  | zero => simp [knownRun] at h; subst z'; rfl
  | succ k ih =>
    simp only [knownRun] at h
    cases hs : knownStep p z with
    | none => simp [hs] at h
    | some t =>
      simp only [hs,Option.bind_some] at h
      simp only [run0,knownStep_sound p hs L R,Option.bind_some]
      exact ih h

/-- An action consumes one symbolic primitive or transfers every copy of
    the unknown repeated word, using an explicitly checked local trace. -/
inductive Action where
  | step
  | right (lp rp I O : List Bool) (L R : Word) (k : Nat)
  | left (lp rp I O : List Bool) (L R : Word) (k : Nat)
  deriving DecidableEq, Repr

structure Result where
  z : PZ
  a : Nat
  b : Nat
  deriving DecidableEq, Repr

def action (p : PartialMachine) (op : Action) (z : PZ) : Option Result :=
  match op with
  | .step => (pstep p z).map fun y => ⟨y,0,1⟩
  | .right lp rp I O L R k =>
    if z.l = L.push lp ∧ z.r = .periodic rp I R ∧
        knownRun p k ⟨z.q,lp,rp++I⟩ = some ⟨z.q,lp++O,rp⟩ then
      some ⟨⟨z.q,.periodic lp O L,R.push rp⟩,k,0⟩
    else none
  | .left lp rp I O L R k =>
    if z.l = .periodic lp I L ∧ z.r = R.push rp ∧
        knownRun p k ⟨z.q,lp++I,rp⟩ = some ⟨z.q,lp,rp++O⟩ then
      some ⟨⟨z.q,L.push lp,.periodic rp O R⟩,k,0⟩
    else none

theorem action_sound (p : PartialMachine) (op : Action) {z : PZ} {out : Result}
    (h : action p op z = some out) (n : Nat) :
    run0 p (out.a*n+out.b) (z.eval n) = some (out.z.eval n) := by
  cases op with
  | step =>
    simp only [action] at h
    cases hs : pstep p z with
    | none => simp [hs] at h
    | some y =>
      simp [hs] at h
      subst out
      simp [run0,pstep_sound p hs n]
  | right lp rp I O L R k =>
    simp only [action] at h
    split at h
    next hc =>
      simp only [Option.some.injEq] at h
      subst out
      have one (L R : List Bool) : run0 p k ⟨z.q,lp++L,rp++I++R⟩ =
          some ⟨z.q,lp++O++L,rp++R⟩ := by
        simpa [extend] using knownRun_sound p k hc.2.2 L R
      simpa [PZ.eval,Word.eval,hc.1,hc.2.1,Word.push_sound] using
        sweepR p z.q lp rp I O k one n (L.eval n) (R.eval n)
    next => simp at h
  | left lp rp I O L R k =>
    simp only [action] at h
    split at h
    next hc =>
      simp only [Option.some.injEq] at h
      subst out
      have one (L R : List Bool) : run0 p k ⟨z.q,lp++I++L,rp++R⟩ =
          some ⟨z.q,lp++L,rp++O++R⟩ := by
        simpa [extend] using knownRun_sound p k hc.2.2 L R
      simpa [PZ.eval,Word.eval,hc.1,hc.2.1,Word.push_sound] using
        sweepL p z.q lp rp I O k one n (L.eval n) (R.eval n)
    next => simp at h

def traceRun (p : PartialMachine) : List Action → PZ → Option Result
  | [],z => some ⟨z,0,0⟩
  | op::ops,z => do
    let a ← action p op z
    let b ← traceRun p ops a.z
    return ⟨b.z,a.a+b.a,a.b+b.b⟩

theorem traceRun_sound (p : PartialMachine) (ops : List Action) {z : PZ} {out : Result}
    (h : traceRun p ops z = some out) (n : Nat) :
    run0 p (out.a*n+out.b) (z.eval n) = some (out.z.eval n) := by
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
        have hh := join0 (action_sound p op ha n) (ih hb)
        simpa [Nat.add_mul,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using hh

/-- Rotate a repeated block to remove a matching bit from its pre0.
    Reversed pre0 and repeated word make the recursion structurally decreasing. -/
structure Frame where
  pre : List Bool
  block : List Bool
  moved : List Bool
  deriving DecidableEq, Repr

def normAux : List Bool → List Bool → List Bool → Frame
  | a::pre,b::block,moved =>
    if a=b then normAux pre (block++[b]) (b::moved)
    else ⟨(a::pre).reverse,(b::block).reverse,moved⟩
  | pre,block,moved => ⟨pre.reverse,block.reverse,moved⟩

def Frame.eval (f : Frame) (n : Nat) (tail : List Bool) : List Bool :=
  f.pre ++ rep f.block n ++ (f.moved ++ tail)

theorem normAux_sound (pre block moved tail : List Bool) (n : Nat) :
    (normAux pre block moved).eval n tail = pre.reverse ++ rep block.reverse n ++ (moved++tail) := by
  induction pre generalizing block moved with
  | nil => rfl
  | cons a pre ih =>
    cases block with
    | nil => rfl
    | cons b block =>
      simp only [normAux]
      split
      next h =>
        subst a
        rw [ih]
        simp only [List.reverse_append,List.reverse_cons,List.reverse_nil,List.nil_append]
        simp only [List.append_assoc]
        rw [← List.append_assoc [b] (rep (block.reverse ++ [b]) n) (moved++tail),rotate b block.reverse n]
        simp only [List.append_assoc,List.cons_append,List.nil_append]
      next => rfl

def Word.normWith (pre0 : List Bool) : Word → Word
  | .lit xs => .lit (pre0++xs)
  | .periodic p b s =>
    let f := normAux (pre0++p).reverse b.reverse []
    .periodic f.pre f.block (s.normWith f.moved)

theorem Word.normWith_sound (w : Word) (pre0 : List Bool) (n : Nat) :
    (w.normWith pre0).eval n = pre0 ++ w.eval n := by
  induction w generalizing pre0 with
  | lit => rfl
  | periodic p b s ih =>
    simp only [Word.normWith,Word.eval,ih]
    change (normAux (pre0++p).reverse b.reverse []).eval n (s.eval n) = _
    rw [normAux_sound,List.reverse_reverse,List.reverse_reverse]
    simp only [List.nil_append,List.append_assoc]

def Word.norm (w : Word) : Word := w.normWith []

theorem Word.norm_sound (w : Word) (n : Nat) : w.norm.eval n = w.eval n := by
  simp [Word.norm,Word.normWith_sound]

def PZ.norm (z : PZ) : PZ := ⟨z.q,z.l.norm,z.r.norm⟩

theorem PZ.norm_sound (z : PZ) (n : Nat) : z.norm.eval n = z.eval n := by
  simp [PZ.norm,PZ.eval,Word.norm_sound]

theorem rep_add (b : List Bool) (d n : Nat) : rep b d ++ rep b n = rep b (d+n) := by
  induction d with
  | zero => simp [rep]
  | succ d ih => simp only [rep,List.append_assoc,ih,show d+1+n=d+n+1 by omega]

def Word.grow (w : Word) (d : Nat) : Word :=
  match w with
  | .lit xs => .lit xs
  | .periodic p b s => .periodic (p++rep b d) b (s.grow d)

theorem Word.grow_sound (w : Word) (d n : Nat) : (w.grow d).eval n = w.eval (d+n) := by
  induction w with
  | lit => rfl
  | periodic p b s ih =>
    simp only [Word.grow,Word.eval,ih]
    rw [List.append_assoc p (rep b d) (rep b n),rep_add]

def PZ.grow (z : PZ) (d : Nat) : PZ := ⟨z.q,z.l.grow d,z.r.grow d⟩

theorem PZ.grow_sound (z : PZ) (d n : Nat) : (z.grow d).eval n = z.eval (d+n) := by
  simp [PZ.grow,PZ.eval,Word.grow_sound]

structure Cert where
  entry : Nat
  family : PZ
  increment : Nat
  ops : List Action
  a : Nat
  b : Nat
  deriving DecidableEq, Repr

def check (p : PartialMachine) (c : Cert) : Bool :=
  decide (0 < c.b ∧ run0 p c.entry ⟨0,[],[]⟩ = some (c.family.eval 0)) &&
  match traceRun p c.ops c.family with
  | none => false
  | some out => decide (out.a=c.a ∧ out.b=c.b ∧ out.z.norm=(c.family.grow c.increment).norm)

theorem check_growth (p : PartialMachine) (c : Cert) (h : check p c = true) (n : Nat) :
    run0 p (c.a*n+c.b) (c.family.eval n) = some (c.family.eval (c.increment+n)) := by
  simp only [check,Bool.and_eq_true,decide_eq_true_eq] at h
  cases hr : traceRun p c.ops c.family with
  | none => simp [hr] at h
  | some out =>
    simp only [hr,decide_eq_true_eq] at h
    have hs := traceRun_sound p c.ops hr n
    have hn := congrArg (fun z : PZ => z.eval n) h.2.2.2
    rw [PZ.norm_sound,PZ.norm_sound,PZ.grow_sound] at hn
    rw [h.2.1,h.2.2.1,hn] at hs
    exact hs

theorem check_first (p : PartialMachine) (c : Cert) (h : check p c = true) :
    run0 p c.entry ⟨0,[],[]⟩ = some (c.family.eval 0) := by
  simp only [check,Bool.and_eq_true,decide_eq_true_eq] at h
  exact h.1.2

theorem check_positive (p : PartialMachine) (c : Cert) (h : check p c = true) : 0<c.b := by
  simp only [check,Bool.and_eq_true,decide_eq_true_eq] at h
  exact h.1.1

/-- The checked trace supplies live prefixes of unbounded length in every
    compatible completion of the original machine. -/
theorem check_never (p : PartialMachine) (c : Cert) (h : check p c = true)
    (m : Machine) (hm : compatible p m) : NeverHalts m := by
  apply never_of_growth p (fun k => c.family.eval (c.increment*k)) c.entry
    (fun k => c.a*(c.increment*k)+c.b) _ _ _ m hm
  · simpa using check_first p c h
  · intro k
    have hb := check_positive p c h
    omega
  · intro k
    simpa only [Nat.mul_succ,Nat.add_comm] using check_growth p c h (c.increment*k)

#print axioms check_growth
#print axioms check_never
end BB6Coverage.Agent31Pump.Auto
