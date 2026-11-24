import SparseZipper

set_option maxRecDepth 20000
set_option maxHeartbeats 0
namespace BB6Coverage.Agent47SweepCert
open BB6Coverage Agent50Zipper

def M (p : PartialMachine) (k : Nat) (q q' : Fin 6) (l r l' r' : List Bool) : Prop :=
  ∀ h : Int, ∃ n h', k ≤ n ∧ zrun p n ⟨q,h,l,r⟩ = some ⟨q',h',l',r'⟩
variable {p : PartialMachine}
theorem M.then {k : Nat} {q u v : Fin 6} {l r s t l' r' : List Bool}
    (H : M p k q u l r s t) (G : M p 0 u v s t l' r') : M p k q v l r l' r' := by
  intro h
  obtain ⟨n,h',hn,hr⟩ := H h
  obtain ⟨m,h'',_,hs⟩ := G h'
  exact ⟨n+m,h'',by omega,join hr hs⟩
theorem M.refl (q : Fin 6) (l r : List Bool) : M p 0 q q l r l r := by
  intro h; exact ⟨0,h,Nat.le_refl _,rfl⟩

def rep (w : List Bool) : Nat → List Bool
  | 0 => []
  | n+1 => w ++ rep w n

theorem rep_snoc (w : List Bool) (n : Nat) : rep w n ++ w = w ++ rep w n := by
  induction n with
  | zero => simp [rep]
  | succ n ih => simp only [rep,List.append_assoc,ih]

theorem leftIter (q : Fin 6) (P X Q Y : List Bool)
    (H : ∀ L R, M p 0 q q (P++X++L) (Q++R) (P++L) (Q++Y++R))
    (n : Nat) (L R : List Bool) :
    M p 0 q q (P++rep X n++L) (Q++R) (P++L) (Q++rep Y n++R) := by
  induction n generalizing R with
  | zero => simpa [rep] using (M.refl (p:=p) q (P++L) (Q++R))
  | succ n ih =>
    have h1 := H (rep X n++L) R
    have h2 := ih (Y++R)
    simp only [List.append_assoc] at h1 h2
    have h := h1.then h2
    simpa only [rep,List.append_assoc,← List.append_assoc (rep Y n) Y R,rep_snoc] using h

theorem rightIter (q : Fin 6) (P X Q Y : List Bool)
    (H : ∀ L R, M p 0 q q (Q++R) (P++X++L) (Q++Y++R) (P++L))
    (n : Nat) (L R : List Bool) :
    M p 0 q q (Q++R) (P++rep X n++L) (Q++rep Y n++R) (P++L) := by
  induction n generalizing R with
  | zero => simpa [rep] using (M.refl (p:=p) q (Q++R) (P++L))
  | succ n ih =>
    have h1 := H (rep X n++L) R
    have h2 := ih (Y++R)
    simp only [List.append_assoc] at h1 h2
    have h := h1.then h2
    simpa only [rep,List.append_assoc,← List.append_assoc (rep Y n) Y R,rep_snoc] using h

/-- Literal cells, repeated blocks, and two opaque arbitrary tails. The
symbolic simulator refuses to inspect any nonliteral token. -/
inductive Tok where
  | bit (b : Bool)
  | repeat (w : List Bool)
  | tailL
  | tailR
  deriving DecidableEq, Repr
abbrev Word := List Tok

def evalTok (n : Nat) (L R : List Bool) : Tok → List Bool
  | .bit b => [b]
  | .repeat w => rep w n
  | .tailL => L
  | .tailR => R

def evalW (n : Nat) (L R : List Bool) : Word → List Bool
  | [] => []
  | b::w => evalTok n L R b ++ evalW n L R w

def lit (w : List Bool) : Word := w.map Tok.bit

theorem eval_append (n : Nat) (L R : List Bool) (x y : Word) :
    evalW n L R (x++y) = evalW n L R x ++ evalW n L R y := by
  induction x with
  | nil => rfl
  | cons b w ih => simp only [List.cons_append,evalW,List.append_assoc,ih]

theorem eval_lit (n : Nat) (L R w : List Bool) : evalW n L R (lit w) = w := by
  induction w with
  | nil => rfl
  | cons b w ih => simp [lit,evalW,evalTok] at *; exact ih

theorem eval_cons_repeat (n : Nat) (L R x : List Bool) (w : Word) :
    evalW n L R (.repeat x :: w) = rep x n ++ evalW n L R w := rfl

structure S where
  q : Fin 6
  l : Word
  r : Word
  deriving DecidableEq, Repr

def evalS (n : Nat) (L R : List Bool) (s : S) (h : Int) : Z :=
  ⟨s.q,h,evalW n L R s.l,evalW n L R s.r⟩

def wread : Word → Option Bool
  | [] => some false
  | .bit b :: _ => some b
  | _ => none

def wtail : Word → Option Word
  | [] => some []
  | .bit _ :: w => some w
  | _ => none

theorem wread_sound (n : Nat) (L R : List Bool) (w : Word) (b : Bool)
    (h : wread w = some b) : (evalW n L R w).headD false = b := by
  cases w with
  | nil => simp [wread,evalW] at h ⊢; exact h
  | cons t w => cases t <;> simp [wread,evalW,evalTok] at h ⊢; exact h

theorem wtail_sound (n : Nat) (L R : List Bool) (w v : Word)
    (h : wtail w = some v) : (evalW n L R w).tail = evalW n L R v := by
  cases w with
  | nil => simp [wtail] at h; subst v; rfl
  | cons t w => cases t <;> simp [wtail,evalW,evalTok] at h ⊢; rw [h]

def sstep (p : PartialMachine) (s : S) : Option S := do
  let b ← wread s.l
  let l ← wtail s.l
  let mv ← (p (s.q,b)).bind id
  if mv.right then
    let c ← wread s.r
    let r ← wtail s.r
    pure ⟨mv.next,.bit c :: .bit mv.write :: l,r⟩
  else
    pure ⟨mv.next,l,.bit mv.write :: s.r⟩

theorem sstep_sound (p : PartialMachine) (n : Nat) (L R : List Bool) (s t : S)
    (hs : sstep p s = some t) (h : Int) :
    ∃ h', step p (evalS n L R s h) = some (evalS n L R t h') := by
  cases hb : wread s.l with
  | none => simp [sstep,hb] at hs
  | some b =>
    cases hl : wtail s.l with
    | none => simp [sstep,hb,hl] at hs
    | some l =>
      cases hm : (p (s.q,b)).bind id with
      | none => simp [sstep,hb,hl,hm] at hs
      | some mv =>
        have hbs := wread_sound n L R s.l b hb
        have hls := wtail_sound n L R s.l l hl
        cases hd : mv.right with
        | false =>
          simp [sstep,hb,hl,hm,hd] at hs
          subst t
          refine ⟨h-1,?_⟩
          unfold step evalS
          dsimp only
          rw [hbs,hm]
          simp [move,hd,hls,evalW,evalTok]
        | true =>
          cases hc : wread s.r with
          | none => simp [sstep,hb,hl,hm,hd,hc] at hs
          | some c =>
            cases hr : wtail s.r with
            | none => simp [sstep,hb,hl,hm,hd,hc,hr] at hs
            | some r =>
              simp [sstep,hb,hl,hm,hd,hc,hr] at hs
              subst t
              have hcs := wread_sound n L R s.r c hc
              have hrs := wtail_sound n L R s.r r hr
              refine ⟨h+1,?_⟩
              unfold step evalS
              dsimp only
              rw [hbs,hm]
              simp only [Option.map_some,move,hd,ite_true,hls,hcs,hrs,evalW,evalTok,List.singleton_append]

def srun (p : PartialMachine) : Nat → S → Option S
  | 0,s => some s
  | k+1,s => (sstep p s).bind (srun p k)

theorem srun_sound (p : PartialMachine) (k n : Nat) (L R : List Bool) (s t : S)
    (hs : srun p k s = some t) (h : Int) :
    ∃ h', zrun p k (evalS n L R s h) = some (evalS n L R t h') := by
  induction k generalizing s h with
  | zero => simp [srun] at hs; subst t; exact ⟨h,rfl⟩
  | succ k ih =>
    cases he : sstep p s with
    | none => simp [srun,he] at hs
    | some u =>
      have hu : srun p k u = some t := by simpa [srun,he] using hs
      obtain ⟨h',h₁⟩ := sstep_sound p n L R s u he h
      obtain ⟨h'',h₂⟩ := ih u hu h'
      exact ⟨h'',by simp [zrun,h₁,h₂]⟩

theorem srun_macro (p : PartialMachine) (k bound n : Nat) (L R : List Bool) (s t : S)
    (hb : bound ≤ k) (hs : srun p k s = some t) :
    M p bound s.q t.q (evalW n L R s.l) (evalW n L R s.r)
      (evalW n L R t.l) (evalW n L R t.r) := by
  intro h
  obtain ⟨h',he⟩ := srun_sound p k n L R s t hs h
  exact ⟨k,h',hb,he⟩

-- A certificate describes the two symbolic boundary words and one local
-- shift over a repeated block, checked with independent opaque tails.
structure Sweep where
  left : Bool
  k : Nat
  P : List Bool
  X : List Bool
  Q : List Bool
  Y : List Bool
  L : Word
  R : Word
  deriving Repr

def Sweep.source (a : Sweep) (q : Fin 6) : S :=
  let x := lit a.P ++ (.repeat a.X :: a.L)
  let y := lit a.Q ++ a.R
  if a.left then ⟨q,x,y⟩ else ⟨q,y,x⟩

def Sweep.target (a : Sweep) (q : Fin 6) : S :=
  let x := lit a.P ++ a.L
  let y := lit a.Q ++ (.repeat a.Y :: a.R)
  if a.left then ⟨q,x,y⟩ else ⟨q,y,x⟩

def Sweep.localSource (a : Sweep) (q : Fin 6) : S :=
  let x := lit a.P ++ lit a.X ++ [.tailL]
  let y := lit a.Q ++ [.tailR]
  if a.left then ⟨q,x,y⟩ else ⟨q,y,x⟩

def Sweep.localTarget (a : Sweep) (q : Fin 6) : S :=
  let x := lit a.P ++ [.tailL]
  let y := lit a.Q ++ lit a.Y ++ [.tailR]
  if a.left then ⟨q,x,y⟩ else ⟨q,y,x⟩

def Sweep.check (p : PartialMachine) (a : Sweep) (s : S) : Option S :=
  if s = a.source s.q ∧ srun p a.k (a.localSource s.q) = some (a.localTarget s.q)
    then some (a.target s.q) else none

theorem Sweep.sound (p : PartialMachine) (a : Sweep) (s t : S)
    (hs : a.check p s = some t) (n : Nat) (L R : List Bool) :
    M p 0 s.q t.q (evalW n L R s.l) (evalW n L R s.r)
      (evalW n L R t.l) (evalW n L R t.r) := by
  unfold Sweep.check at hs
  split at hs
  next h =>
    have ht : a.target s.q = t := Option.some.inj hs
    subst t
    have he := h.1
    have hl := h.2
    cases hd : a.left with
    | false =>
      have H (l r : List Bool) : M p 0 s.q s.q (a.Q++r) (a.P++a.X++l) (a.Q++a.Y++r) (a.P++l) := by
        have hh := srun_macro p a.k 0 0 l r (a.localSource s.q) (a.localTarget s.q) (by omega) hl
        simpa [Sweep.localSource,Sweep.localTarget,hd,eval_append,eval_lit,evalW,evalTok] using hh
      have hh := rightIter s.q a.P a.X a.Q a.Y H n (evalW n L R a.L) (evalW n L R a.R)
      rw [he]
      simpa [Sweep.source,Sweep.target,hd,eval_append,eval_lit,eval_cons_repeat,List.append_assoc] using hh
    | true =>
      have H (l r : List Bool) : M p 0 s.q s.q (a.P++a.X++l) (a.Q++r) (a.P++l) (a.Q++a.Y++r) := by
        have hh := srun_macro p a.k 0 0 l r (a.localSource s.q) (a.localTarget s.q) (by omega) hl
        simpa [Sweep.localSource,Sweep.localTarget,hd,eval_append,eval_lit,evalW,evalTok] using hh
      have hh := leftIter s.q a.P a.X a.Q a.Y H n (evalW n L R a.L) (evalW n L R a.R)
      rw [he]
      simpa [Sweep.source,Sweep.target,hd,eval_append,eval_lit,eval_cons_repeat,List.append_assoc] using hh
  next => contradiction

inductive Instr where
  | atom (k : Nat)
  | sweep (a : Sweep)
  deriving Repr

def Instr.run (p : PartialMachine) (a : Instr) (s : S) : Option S :=
  match a with
  | .atom k => srun p k s
  | .sweep a => a.check p s

theorem Instr.sound (p : PartialMachine) (a : Instr) (s t : S) (hs : a.run p s = some t)
    (n : Nat) (L R : List Bool) :
    M p 0 s.q t.q (evalW n L R s.l) (evalW n L R s.r)
      (evalW n L R t.l) (evalW n L R t.r) := by
  cases a with
  | atom k => exact srun_macro p k 0 n L R s t (by omega) hs
  | sweep a => exact a.sound p s t hs n L R

def script (p : PartialMachine) : List Instr → S → Option S
  | [],s => some s
  | a::as,s => (a.run p s).bind (script p as)

theorem script_sound (p : PartialMachine) (as : List Instr) (s t : S)
    (hs : script p as s = some t) (n : Nat) (L R : List Bool) :
    M p 0 s.q t.q (evalW n L R s.l) (evalW n L R s.r)
      (evalW n L R t.l) (evalW n L R t.r) := by
  induction as generalizing s with
  | nil => simp [script] at hs; subst t; exact M.refl _ _ _
  | cons a as ih =>
    cases he : a.run p s with
    | none => simp [he,script] at hs
    | some u =>
      have hu : script p as u = some t := by simpa [script,he] using hs
      exact (a.sound p s u he n L R).then (ih u hu)

def succW : Word → Word
  | [] => []
  | .repeat x::w => lit x ++ (.repeat x :: succW w)
  | b::w => b::succW w

theorem eval_succ (n : Nat) (L R : List Bool) (w : Word) :
    evalW n L R (succW w) = evalW (n+1) L R w := by
  induction w with
  | nil => rfl
  | cons b w ih => cases b <;> simp [succW,evalW,evalTok,eval_append,eval_lit,rep,ih,List.append_assoc]

def S.next (s : S) : S := ⟨s.q,succW s.l,succW s.r⟩
def start : Z := ⟨0,0,[],[]⟩

structure Cert where
  s : S
  entry : Nat
  head : Int
  first : Nat
  rest : List Instr
  deriving Repr

def Cert.check (p : PartialMachine) (c : Cert) : Bool :=
  decide (zrun p c.entry start = some (evalS 0 [] [] c.s c.head)) &&
  decide (0 < c.first) &&
  decide ((srun p c.first c.s).bind (script p c.rest) = some c.s.next)

theorem Cert.sound (p : PartialMachine) (c : Cert) (hc : c.check p = true) (n : Nat) :
    ∃ z, zrun p n start = some z := by
  have ⟨⟨hi,hp⟩,hs⟩ : (zrun p c.entry start = some (evalS 0 [] [] c.s c.head) ∧ 0 < c.first) ∧
      (srun p c.first c.s).bind (script p c.rest) = some c.s.next := by simpa [Cert.check] using hc
  have H (n : Nat) : ∃ t h, n ≤ t ∧ zrun p t start = some (evalS n [] [] c.s h) := by
    induction n with
    | zero => exact ⟨c.entry,c.head,by omega,hi⟩
    | succ n ih =>
      obtain ⟨t,h,ht,hr⟩ := ih
      cases hu : srun p c.first c.s with
      | none => simp [hu] at hs
      | some u =>
        have hu' : script p c.rest u = some c.s.next := by simpa [hu] using hs
        have h1 := srun_macro p c.first 1 n [] [] c.s u (by omega) hu
        have h2 := script_sound p c.rest u c.s.next hu' n [] []
        obtain ⟨k,h',hk,hk'⟩ := (h1.then h2) h
        have hj := join hr hk'
        exact ⟨t+k,h',by omega,by simpa [evalS,S.next,eval_succ] using hj⟩
  obtain ⟨t,h,ht,hr⟩ := H n
  rw [show t=n+(t-n) by omega,zrun_add] at hr
  cases hrun : zrun p n start with
  | none => simp [hrun] at hr
  | some z => exact ⟨z,rfl⟩

#print axioms Cert.sound
end BB6Coverage.Agent47SweepCert
