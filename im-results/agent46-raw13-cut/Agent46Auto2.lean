import Agent46AutoPump

namespace BB6Coverage.Agent31Pump.Auto2
open BB6Coverage Agent31Pump

/-- A finite sequence of parametric repeated blocks, each selecting one of two independent exponents. -/
inductive Word where
  | lit (xs : List Bool)
  | periodic (pre block : List Bool) (v : Bool) (post : Word)
  deriving DecidableEq, Repr

def Word.eval (w : Word) (n : Bool → Nat) : List Bool :=
  match w with
  | .lit xs => xs
  | .periodic pre block v post => pre ++ rep block (n v) ++ post.eval n

def Word.pop : Word → Option (Bool × Word)
  | .lit [] => some (false,.lit [])
  | .lit (a::xs) => some (a,.lit xs)
  | .periodic [] _ _ _ => none
  | .periodic (a::xs) b v s => some (a,.periodic xs b v s)

def Word.push (xs : List Bool) : Word → Word
  | .lit ys => .lit (xs++ys)
  | .periodic pre b v s => .periodic (xs++pre) b v s

theorem Word.pop_sound {w : Word} {a : Bool} {r : Word}
    (h : w.pop = some (a,r)) (n : Bool → Nat) :
    (w.eval n).headD false = a ∧ (w.eval n).tail = r.eval n := by
  cases w with
  | lit xs => cases xs <;> simp [Word.pop] at h <;> obtain ⟨rfl,rfl⟩ := h <;> simp [Word.eval]
  | periodic pre b v s => cases pre <;> simp [Word.pop] at h
                         <;> obtain ⟨rfl,rfl⟩ := h <;> simp [Word.eval]

theorem Word.push_sound (xs : List Bool) (w : Word) (n : Bool → Nat) :
    (w.push xs).eval n = xs ++ w.eval n := by
  cases w <;> simp [Word.push,Word.eval,List.append_assoc]

structure PZ where
  q : Fin 6
  l : Word
  r : Word
  deriving DecidableEq, Repr

def PZ.eval (z : PZ) (n : Bool → Nat) : Z0 := ⟨z.q,z.l.eval n,z.r.eval n⟩

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

theorem pstep_sound (p : PartialMachine) {z z' : PZ} (h : pstep p z = some z') (n : Bool → Nat) :
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

/-- An action consumes one symbolic primitive or transfers every copy of
    the unknown repeated word, using an explicitly checked local trace. -/
inductive Action where
  | step
  | right (lp rp I O : List Bool) (L R : Word) (v : Bool) (k : Nat)
  | left (lp rp I O : List Bool) (L R : Word) (v : Bool) (k : Nat)
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
  | .right lp rp I O L R v k =>
    if z.l = L.push lp ∧ z.r = .periodic rp I v R ∧
        Auto.knownRun p k ⟨z.q,lp,rp++I⟩ = some ⟨z.q,lp++O,rp⟩ then
      some ⟨⟨z.q,.periodic lp O v L,R.push rp⟩,if v then 0 else k,if v then k else 0,0⟩
    else none
  | .left lp rp I O L R v k =>
    if z.l = .periodic lp I v L ∧ z.r = R.push rp ∧
        Auto.knownRun p k ⟨z.q,lp++I,rp⟩ = some ⟨z.q,lp,rp++O⟩ then
      some ⟨⟨z.q,L.push lp,.periodic rp O v R⟩,if v then 0 else k,if v then k else 0,0⟩
    else none

theorem action_sound (p : PartialMachine) (op : Action) {z : PZ} {out : Result}
    (h : action p op z = some out) (n : Bool → Nat) :
    run0 p (out.a*n false+out.b*n true+out.c) (z.eval n) = some (out.z.eval n) := by
  cases op with
  | step =>
    simp only [action] at h
    cases hs : pstep p z with
    | none => simp [hs] at h
    | some y =>
      simp [hs] at h
      subst out
      simp [run0,pstep_sound p hs n]
  | right lp rp I O L R v k =>
    simp only [action] at h
    split at h
    next hc =>
      simp only [Option.some.injEq] at h
      subst out
      have one (L R : List Bool) : run0 p k ⟨z.q,lp++L,rp++I++R⟩ =
          some ⟨z.q,lp++O++L,rp++R⟩ := by
        simpa [Auto.extend] using Auto.knownRun_sound p k hc.2.2 L R
      have hh := sweepR p z.q lp rp I O k one (n v) (L.eval n) (R.eval n)
      cases v <;> simpa [PZ.eval,Word.eval,hc.1,hc.2.1,Word.push_sound] using hh
    next => simp at h
  | left lp rp I O L R v k =>
    simp only [action] at h
    split at h
    next hc =>
      simp only [Option.some.injEq] at h
      subst out
      have one (L R : List Bool) : run0 p k ⟨z.q,lp++I++L,rp++R⟩ =
          some ⟨z.q,lp++L,rp++O++R⟩ := by
        simpa [Auto.extend] using Auto.knownRun_sound p k hc.2.2 L R
      have hh := sweepL p z.q lp rp I O k one (n v) (L.eval n) (R.eval n)
      cases v <;> simpa [PZ.eval,Word.eval,hc.1,hc.2.1,Word.push_sound] using hh
    next => simp at h

def traceRun (p : PartialMachine) : List Action → PZ → Option Result
  | [],z => some ⟨z,0,0,0⟩
  | op::ops,z => do
    let a ← action p op z
    let b ← traceRun p ops a.z
    return ⟨b.z,a.a+b.a,a.b+b.b,a.c+b.c⟩

theorem traceRun_sound (p : PartialMachine) (ops : List Action) {z : PZ} {out : Result}
    (h : traceRun p ops z = some out) (n : Bool → Nat) :
    run0 p (out.a*n false+out.b*n true+out.c) (z.eval n) = some (out.z.eval n) := by
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

def Word.normWith (pre0 : List Bool) : Word → Word
  | .lit xs => .lit (pre0++xs)
  | .periodic p b v s =>
    let f := Auto.normAux (pre0++p).reverse b.reverse []
    .periodic f.pre f.block v (s.normWith f.moved)

theorem Word.normWith_sound (w : Word) (pre0 : List Bool) (n : Bool → Nat) :
    (w.normWith pre0).eval n = pre0 ++ w.eval n := by
  induction w generalizing pre0 with
  | lit => rfl
  | periodic p b v s ih =>
    simp only [Word.normWith,Word.eval,ih]
    change (Auto.normAux (pre0++p).reverse b.reverse []).eval (n v) (s.eval n) = _
    rw [Auto.normAux_sound,List.reverse_reverse,List.reverse_reverse]
    simp only [List.nil_append,List.append_assoc]

def Word.norm (w : Word) : Word := w.normWith []

theorem Word.norm_sound (w : Word) (n : Bool → Nat) : w.norm.eval n = w.eval n := by
  simp [Word.norm,Word.normWith_sound]

def PZ.norm (z : PZ) : PZ := ⟨z.q,z.l.norm,z.r.norm⟩

theorem PZ.norm_sound (z : PZ) (n : Bool → Nat) : z.norm.eval n = z.eval n := by
  simp [PZ.norm,PZ.eval,Word.norm_sound]

def Word.grow (w : Word) (d : Bool → Nat) : Word :=
  match w with
  | .lit xs => .lit xs
  | .periodic p b v s => .periodic (p++rep b (d v)) b v (s.grow d)

theorem Word.grow_sound (w : Word) (d n : Bool → Nat) : (w.grow d).eval n = w.eval (fun v => d v+n v) := by
  induction w with
  | lit => rfl
  | periodic p b v s ih =>
    simp only [Word.grow,Word.eval,ih]
    rw [List.append_assoc p (rep b (d v)) (rep b (n v)),Auto.rep_add]

def PZ.grow (z : PZ) (d : Bool → Nat) : PZ := ⟨z.q,z.l.grow d,z.r.grow d⟩

theorem PZ.grow_sound (z : PZ) (d n : Bool → Nat) : (z.grow d).eval n = z.eval (fun v => d v+n v) := by
  simp [PZ.grow,PZ.eval,Word.grow_sound]


/-- A trace between two independently parameterized configurations. -/
structure Macro where
  src : PZ
  dst : PZ
  ops : List Action
  a : Nat
  b : Nat
  c : Nat
  deriving DecidableEq, Repr

def Macro.check (p : PartialMachine) (m : Macro) : Bool :=
  match traceRun p m.ops m.src with
  | none => false
  | some out => decide (out.a=m.a ∧ out.b=m.b ∧ out.c=m.c ∧ out.z.norm=m.dst.norm)

theorem Macro.sound (p : PartialMachine) (m : Macro) (h : m.check p = true) (n : Bool → Nat) :
    run0 p (m.a*n false+m.b*n true+m.c) (m.src.eval n) = some (m.dst.eval n) := by
  unfold Macro.check at h
  cases hr : traceRun p m.ops m.src with
  | none => simp [hr] at h
  | some out =>
    simp only [hr,decide_eq_true_eq] at h
    have hs := traceRun_sound p m.ops hr n
    have hn := congrArg (fun z : PZ => z.eval n) h.2.2.2
    rw [PZ.norm_sound,PZ.norm_sound] at hn
    rw [h.1,h.2.1,h.2.2.1,hn] at hs
    exact hs

def drainCost (a b d : Nat) : Nat → Nat → Nat
  | 0,_ => 0
  | k+1,m => a*m+b+drainCost a b d k (m+d)

/-- A checked two-counter transfer can be iterated to drain the first
    counter exactly while increasing the second. -/
theorem drain (p : PartialMachine) (F : Nat → Nat → Z0) (a b d : Nat)
    (h : ∀ k m, run0 p (a*m+b) (F (k+1) m) = some (F k (m+d))) (k m : Nat) :
    run0 p (drainCost a b d k m) (F k m) = some (F 0 (m+d*k)) := by
  induction k generalizing m with
  | zero => simp [drainCost,run0]
  | succ k ih =>
    have hh := join0 (h k m) (ih (m+d))
    simpa [drainCost,Nat.mul_succ,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using hh

theorem rep_mul (b : List Bool) (k n : Nat) : rep (rep b k) n = rep b (k*n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [rep,ih,Auto.rep_add,Nat.mul_succ,Nat.add_comm]

#print axioms Macro.sound
#print axioms drain

def mapOrbit (g : Nat → Nat) (start : Nat) : Nat → Nat
  | 0 => start
  | k+1 => g (mapOrbit g start k)

theorem mapOrbit_data (p : PartialMachine) (F : Nat → Z0) (g cost : Nat → Nat) (entry start : Nat)
    (first : run0 p entry ⟨0,[],[]⟩ = some (F start))
    (positive : ∀ n, 0 < cost n)
    (growth : ∀ n, run0 p (cost n) (F n) = some (F (g n))) :
    run0 p entry ⟨0,[],[]⟩ = some (F (mapOrbit g start 0)) ∧
    (∀ k, 0 < cost (mapOrbit g start k)) ∧
    (∀ k, run0 p (cost (mapOrbit g start k)) (F (mapOrbit g start k)) = some (F (mapOrbit g start (k+1)))) :=
  ⟨first,fun k => positive _,fun k => growth _⟩

theorem never_of_map (p : PartialMachine) (F : Nat → Z0) (g cost : Nat → Nat) (entry start : Nat)
    (first : run0 p entry ⟨0,[],[]⟩ = some (F start))
    (positive : ∀ n, 0 < cost n)
    (growth : ∀ n, run0 p (cost n) (F n) = some (F (g n)))
    (m : Machine) (hm : compatible p m) : NeverHalts m := by
  obtain ⟨h1,h2,h3⟩ := mapOrbit_data p F g cost entry start first positive growth
  exact never_of_growth p (fun k => F (mapOrbit g start k)) entry (fun k => cost (mapOrbit g start k)) h1 h2 h3 m hm
#print axioms never_of_map
end BB6Coverage.Agent31Pump.Auto2
