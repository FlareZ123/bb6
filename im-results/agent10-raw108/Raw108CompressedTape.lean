import SweepPumping
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent10CompressedTape
open BB6Coverage BB6Coverage.Agent31Pump

structure Pat where
  a : Bool
  b : Bool
  c : Bool
  deriving DecidableEq, Repr

def Pat.rot (p : Pat) : Pat := ⟨p.b,p.c,p.a⟩
def Pat.word (p : Pat) : List Bool := [p.a,p.b,p.c]
def word (p : Pat) : Nat → List Bool
  | 0 => []
  | n+1 => p.a :: word p.rot n

theorem word_3 (p : Pat) (n : Nat) : word p (3*n) = rep p.word n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [show 3*(n+1)=3*n+1+1+1 by omega]
    simp only [word,Pat.rot,rep,Pat.word,List.cons_append,List.nil_append]
    exact congrArg (fun l => p.a::p.b::p.c::l) ih

theorem word_split (p : Pat) (k n : Nat) : word p (3*k+n) = rep p.word k ++ word p n := by
  induction k with
  | zero => simp [rep]
  | succ k ih =>
    rw [show 3*(k+1)+n=3*k+n+1+1+1 by omega]
    simp only [word,Pat.rot,rep,Pat.word,List.cons_append,List.nil_append,List.append_assoc]
    exact congrArg (fun l => p.a::p.b::p.c::l) ih

inductive Tape where
  | nil
  | run (p : Pat) (n : Nat) (tail : Tape)
  deriving DecidableEq, Repr

def expand : Tape → List Bool
  | .nil => []
  | .run p n t => word p n ++ expand t

def seg (p : Pat) (n : Nat) (t : Tape) : Tape := if n=0 then t else .run p n t

theorem expand_seg (p : Pat) (n : Nat) (t : Tape) : expand (seg p n t) = word p n ++ expand t := by
  cases n <;> simp [seg,expand,word]

def pop : Tape → Option (Bool × Tape)
  | .nil => none
  | .run p 0 t => pop t
  | .run p (n+1) t => some (p.a,seg p.rot n t)

theorem pop_some (t : Tape) (b : Bool) (r : Tape) (h : pop t = some (b,r)) : expand t = b::expand r := by
  induction t with
  | nil => simp [pop] at h
  | run p n t ih =>
    cases n with
    | zero => simpa [expand,word] using ih (by simpa [pop] using h)
    | succ n =>
      simp only [pop,Option.some.injEq,Prod.mk.injEq] at h
      obtain ⟨rfl,rfl⟩ := h
      simp [expand,word,expand_seg]

theorem pop_none (t : Tape) (h : pop t = none) : expand t = [] := by
  induction t with
  | nil => rfl
  | run p n t ih => cases n <;> simp_all [pop,expand,word]

def popD (t : Tape) : Bool × Tape := (pop t).getD (false,.nil)

theorem popD_head (t : Tape) : (popD t).1 = (expand t).headD false := by
  cases h : pop t with
  | none => simp [popD,h,pop_none t h]
  | some v => rcases v with ⟨b,r⟩; simp [popD,h,pop_some t b r h]

theorem popD_tail (t : Tape) : expand (popD t).2 = (expand t).tail := by
  cases h : pop t with
  | none => simp [popD,h,pop_none t h,expand]
  | some v => rcases v with ⟨b,r⟩; simp [popD,h,pop_some t b r h]

def push (b : Bool) (t : Tape) : Tape :=
  match t with
  | .run p 1 r => .run ⟨b,p.a,false⟩ 2 r
  | .run p 2 r => .run ⟨b,p.a,p.b⟩ 3 r
  | .run p (n+3) r => if b=p.c then .run ⟨b,p.a,p.b⟩ (n+4) r else .run ⟨b,false,false⟩ 1 t
  | _ => .run ⟨b,false,false⟩ 1 t

theorem push_sound (b : Bool) (t : Tape) : expand (push b t) = b::expand t := by
  cases t with
  | nil => rfl
  | run p n r =>
    cases n with
    | zero => rfl
    | succ n =>
      cases n with
      | zero => rfl
      | succ n =>
        cases n with
        | zero => rfl
        | succ n =>
          simp only [push]
          split
          · rename_i hb; subst b; cases p; rfl
          · rfl

def pop3 (t : Tape) : Option (Pat × Tape) :=
  match pop t with
  | none => none
  | some (a,u) => match pop u with
    | none => none
    | some (b,v) => match pop v with
      | none => none
      | some (c,w) => some (⟨a,b,c⟩,w)

theorem pop3_sound (t : Tape) (p : Pat) (r : Tape) (h : pop3 t = some (p,r)) : expand t = p.word ++ expand r := by
  unfold pop3 at h
  cases h1 : pop t with
  | none => simp [h1] at h
  | some u =>
    rcases u with ⟨a,u⟩
    simp only [h1] at h
    cases h2 : pop u with
    | none => simp [h2] at h
    | some v =>
      rcases v with ⟨b,v⟩
      simp only [h2] at h
      cases h3 : pop v with
      | none => simp [h3] at h
      | some w =>
        rcases w with ⟨c,w⟩
        simp only [h3,Option.some.injEq,Prod.mk.injEq] at h
        obtain ⟨rfl,rfl⟩ := h
        rw [pop_some t a u h1,pop_some u b v h2,pop_some v c w h3]
        rfl

/-- Consume any number of equal triples, skipping a whole periodic run at once. -/
def strip (p : Pat) : Nat → Tape → Nat × Tape
  | 0,t => (0,t)
  | fuel+1,t =>
    match t with
    | .run q n r =>
      if q=p && n≥3 then
        let k := n/3
        let (m,u) := strip p fuel (seg p (n%3) r)
        (k+m,u)
      else
        match pop3 t with
        | some (q,u) => if q=p then let (m,v) := strip p fuel u; (m+1,v) else (0,t)
        | none => (0,t)
    | .nil => (0,t)

theorem rep_add (p : List Bool) (m n : Nat) : rep p (m+n) = rep p m ++ rep p n := by
  induction m with
  | zero => simp [rep]
  | succ m ih => rw [show m+1+n=m+n+1 by omega]; simp only [rep,ih,List.append_assoc]

theorem strip_sound (p : Pat) (fuel : Nat) (t : Tape) :
    rep p.word (strip p fuel t).1 ++ expand (strip p fuel t).2 = expand t := by
  induction fuel generalizing t with
  | zero => simp [strip,rep]
  | succ f ih =>
    cases t with
    | nil => simp [strip,rep]
    | run q n r =>
      simp only [strip]
      split
      · rename_i h
        have hq : q=p := by
          simp only [Bool.and_eq_true,decide_eq_true_eq] at h
          exact h.1
        subst q
        simp only [rep_add,List.append_assoc,ih,expand_seg,expand]
        rw [← List.append_assoc,← word_split]
        congr 2
        omega
      · split
        · rename_i q' u hu
          split
          · rename_i hq; subst q'
            simp only [rep,rep_snoc,List.append_assoc]
            rw [ih]
            exact (pop3_sound _ _ _ hu).symm
          · simp [rep]
        · simp [rep]


structure Cfg where
  q : Fin 6
  l : Tape
  r : Tape
  deriving DecidableEq, Repr

def project (c : Cfg) : Z0 := ⟨c.q,expand c.l,expand c.r⟩

def step (p : PartialMachine) (z : Cfg) : Option Cfg :=
  let (b,l) := popD z.l
  let (a,r) := popD z.r
  ((p (z.q,b)).bind id).map fun mv =>
    if mv.right then ⟨mv.next,push a (push mv.write l),r⟩
    else ⟨mv.next,l,push mv.write z.r⟩

theorem step_sound (p : PartialMachine) (z : Cfg) :
    (step p z).map project = step0 p (project z) := by
  simp only [step,step0,project,popD_head,Option.map_map]
  cases h : (p (z.q,(expand z.l).headD false)).bind id with
  | none => rfl
  | some mv =>
    cases hr : mv.right <;> simp [h,hr,move0,project,push_sound,popD_head,popD_tail]

#print axioms strip_sound
#print axioms step_sound
end BB6.Agent10CompressedTape
