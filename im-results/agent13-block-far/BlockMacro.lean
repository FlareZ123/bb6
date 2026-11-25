import Lean

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6BlockFAR

abbrev Q := Fin 6
abbrev Ray := Nat → Bool

structure Sym where
  a : Bool
  b : Bool
  c : Bool
  deriving DecidableEq, Repr

def Sym.zero : Sym := ⟨false,false,false⟩

def Sym.code (s : Sym) : Nat := s.a.toNat + 2*s.b.toNat + 4*s.c.toNat

def Sym.ofCode (n : Nat) : Sym := ⟨n%2 == 1,n/2%2 == 1,n/4%2 == 1⟩

def symbols : List Sym := (List.range 8).map Sym.ofCode

theorem symbols_complete (s : Sym) : s ∈ symbols := by
  rcases s with ⟨a,b,c⟩
  cases a <;> cases b <;> cases c <;> decide

inductive Pos where | lo | mid | hi
  deriving DecidableEq, Repr

def Sym.read (s : Sym) : Pos → Bool
  | .lo => s.a
  | .mid => s.b
  | .hi => s.c

def Sym.write (s : Sym) (p : Pos) (w : Bool) : Sym :=
  match p with
  | .lo => ⟨w,s.b,s.c⟩
  | .mid => ⟨s.a,w,s.c⟩
  | .hi => ⟨s.a,s.b,w⟩

structure Move where
  write : Bool
  right : Bool
  next : Q
  deriving DecidableEq, Repr

abbrev Table := Q → Bool → Option Move

structure Prim where
  q : Q
  l : Ray
  r : Ray

def cons (a : Bool) (r : Ray) : Ray
  | 0 => a
  | n+1 => r n

@[simp] theorem cons_zero (a : Bool) (r : Ray) : cons a r 0 = a := rfl

def tail (r : Ray) : Ray := fun n => r (n+1)

def blankRay : Ray := fun _ => false

@[simp] theorem tail_cons (a : Bool) (r : Ray) : tail (cons a r) = r := rfl

@[simp] theorem blank_cons : cons false blankRay = blankRay := by
  funext n
  cases n <;> rfl

def primStep (M : Table) (c : Prim) : Option Prim := do
  let mv ← M c.q (c.r 0)
  if mv.right then
    return ⟨mv.next,cons mv.write c.l,tail c.r⟩
  else
    return ⟨mv.next,tail c.l,cons (c.l 0) (cons mv.write (tail c.r))⟩

def run (M : Table) : Nat → Prim → Option Prim
  | 0,c => some c
  | n+1,c => (primStep M c).bind (run M n)

theorem run_add (M : Table) (m n : Nat) (c : Prim) :
    run M (m+n) c = (run M m c).bind (run M n) := by
  induction m generalizing c with
  | zero => simp [run]
  | succ m ih =>
    simp only [Nat.succ_add,run,Option.bind_assoc]
    cases primStep M c <;> simp [ih]

/-- A block word represents nearest block first. Within a left block the
    rightmost bit is nearest the head; within a right block the leftmost is. -/
def leftRay : List Sym → Ray
  | [] => blankRay
  | a::r => cons a.c (cons a.b (cons a.a (leftRay r)))

def rightRay : List Sym → Ray
  | [] => blankRay
  | a::r => cons a.a (cons a.b (cons a.c (rightRay r)))

theorem leftRay_unfold (l : List Sym) :
    leftRay l = cons (l.headD Sym.zero).c (cons (l.headD Sym.zero).b
      (cons (l.headD Sym.zero).a (leftRay l.tail))) := by
  cases l with
  | nil => simp [leftRay,Sym.zero,blank_cons]
  | cons a r => rfl

theorem rightRay_unfold (r : List Sym) :
    rightRay r = cons (r.headD Sym.zero).a (cons (r.headD Sym.zero).b
      (cons (r.headD Sym.zero).c (rightRay r.tail))) := by
  cases r with
  | nil => simp [rightRay,Sym.zero,blank_cons]
  | cons a r => rfl

/-- Render a head anywhere within the current 3-cell block, with arbitrary
    untouched left and right exterior block words. -/
def render (q : Q) (p : Pos) (a : Sym) (l r : List Sym) : Prim :=
  match p with
  | .lo => ⟨q,leftRay l,cons a.a (cons a.b (cons a.c (rightRay r)))⟩
  | .mid => ⟨q,cons a.a (leftRay l),cons a.b (cons a.c (rightRay r))⟩
  | .hi => ⟨q,cons a.b (cons a.a (leftRay l)),cons a.c (rightRay r)⟩

structure BlockConfig where
  q : Q
  dir : Bool -- true: entered from the left, false: entered from the right
  l : List Sym
  r : List Sym -- includes the current block, with implicit trailing zero blocks

abbrev EntryPos (dir : Bool) : Pos := if dir then .lo else .hi

def BlockConfig.render (c : BlockConfig) : Prim :=
  BB6BlockFAR.render c.q (EntryPos c.dir) (c.r.headD Sym.zero) c.l c.r.tail

def BlockConfig.next (c : BlockConfig) (q : Q) (dir : Bool) (w : Sym) : BlockConfig :=
  if dir then ⟨q,true,w::c.l,c.r.tail⟩
  else ⟨q,false,c.l.tail,c.l.headD Sym.zero::w::c.r.tail⟩

structure Exit where
  steps : Nat
  q : Q
  dir : Bool
  w : Sym
  deriving DecidableEq, Repr

/-- This is a partial evaluator: only certified finite exits are returned.
    Unknown transitions, internal cycles and fuel exhaustion give none. -/
def macroRun (M : Table) : Nat → Q → Pos → Sym → Option Exit
  | 0,_,_,_ => none
  | fuel+1,q,p,a => do
    let mv ← M q (a.read p)
    let w := a.write p mv.write
    let more (p' : Pos) := (macroRun M fuel mv.next p' w).map fun e => {e with steps := e.steps+1}
    match p,mv.right with
    | .lo,false => return ⟨1,mv.next,false,w⟩
    | .hi,true => return ⟨1,mv.next,true,w⟩
    | .lo,true => more .mid
    | .mid,true => more .hi
    | .mid,false => more .lo
    | .hi,false => more .mid

def blockExit (M : Table) (q : Q) (dir : Bool) (a : Sym) : Option Exit :=
  macroRun M 145 q (EntryPos dir) a

/-- A local block exit never depends on either exterior word. -/
theorem macroRun_sound (M : Table) (fuel : Nat) (q : Q) (p : Pos) (a : Sym)
    (l r : List Sym) (e : Exit) (h : macroRun M fuel q p a = some e) :
    0 < e.steps ∧
    run M e.steps (render q p a l r) = some
      (render e.q (EntryPos e.dir)
        (if e.dir then r.headD Sym.zero else l.headD Sym.zero)
        (if e.dir then e.w::l else l.tail)
        (if e.dir then r.tail else e.w::r)) := by
  induction fuel generalizing q p a e with
  | zero => simp [macroRun] at h
  | succ fuel ih =>
    cases hm : M q (a.read p) with
    | none => simp [macroRun,hm] at h
    | some mv =>
      cases p <;> cases hd : mv.right <;>
        simp [macroRun,hm,hd,Option.map_eq_some_iff] at h <;>
        simp [Sym.read] at hm
      · subst e
        constructor
        · simp
        · simp [run,primStep,render,Sym.write,EntryPos,hm,hd]
          rw [leftRay_unfold l]
          cases l <;> simp [rightRay]
      · obtain ⟨e',he',rfl⟩ := h
        obtain ⟨hpos,hrun⟩ := ih mv.next .mid (a.write .lo mv.write) e' he'
        refine ⟨by simp,?_⟩
        simpa [run,primStep,render,Sym.write,hm,hd] using hrun
      · obtain ⟨e',he',rfl⟩ := h
        obtain ⟨hpos,hrun⟩ := ih mv.next .lo (a.write .mid mv.write) e' he'
        refine ⟨by simp,?_⟩
        simpa [run,primStep,render,Sym.write,hm,hd] using hrun
      · obtain ⟨e',he',rfl⟩ := h
        obtain ⟨hpos,hrun⟩ := ih mv.next .hi (a.write .mid mv.write) e' he'
        refine ⟨by simp,?_⟩
        simpa [run,primStep,render,Sym.write,hm,hd] using hrun
      · obtain ⟨e',he',rfl⟩ := h
        obtain ⟨hpos,hrun⟩ := ih mv.next .mid (a.write .hi mv.write) e' he'
        refine ⟨by simp,?_⟩
        simpa [run,primStep,render,Sym.write,hm,hd] using hrun
      · subst e
        constructor
        · simp
        · simp [run,primStep,render,Sym.write,EntryPos,hm,hd,leftRay]
          rw [rightRay_unfold r]
          cases r <;> rfl

theorem macro_sound (M : Table) (c : BlockConfig) (e : Exit)
    (h : blockExit M c.q c.dir (c.r.headD Sym.zero) = some e) :
    0 < e.steps ∧ run M e.steps c.render = some (c.next e.q e.dir e.w).render := by
  have h' := macroRun_sound M 145 c.q (EntryPos c.dir) (c.r.headD Sym.zero) c.l c.r.tail e h
  refine ⟨h'.1,?_⟩
  cases hd : e.dir <;> simpa [BlockConfig.render,BlockConfig.next,hd] using h'.2

/-- The initial block representation is physically blank. -/
def blockBlank : BlockConfig := ⟨0,true,[],[]⟩
def primBlank : Prim := ⟨0,blankRay,blankRay⟩

theorem render_blank : blockBlank.render = primBlank := by
  simp [blockBlank,BlockConfig.render,primBlank,EntryPos,render,leftRay,rightRay,Sym.zero,blank_cons]

/-- An inductive invariant on block-entry configurations implies every
    primitive prefix executes, including prefixes ending inside a block. -/
theorem forever_of_invariant (M : Table) (P : BlockConfig → Prop)
    (closed : ∀ c, P c → ∃ e, blockExit M c.q c.dir (c.r.headD Sym.zero) = some e ∧ P (c.next e.q e.dir e.w))
    (c : BlockConfig) (hc : P c) : ∀ n, ∃ d, run M n c.render = some d := by
  intro n
  induction n using Nat.strongRecOn generalizing c with
  | ind n ih =>
    obtain ⟨e,he,hnext⟩ := closed c hc
    obtain ⟨hpos,hrun⟩ := macro_sound M c e he
    by_cases hle : e.steps ≤ n
    · obtain ⟨d,hd⟩ := ih (n-e.steps) (by omega) _ hnext
      refine ⟨d,?_⟩
      rw [show n=e.steps+(n-e.steps) by omega,run_add,hrun]
      exact hd
    · have hrun' := hrun
      rw [show e.steps=n+(e.steps-n) by omega,run_add] at hrun'
      cases hh : run M n c.render with
      | none => simp [hh] at hrun'
      | some d => exact ⟨d,rfl⟩

#print axioms macroRun_sound
#print axioms macro_sound
#print axioms forever_of_invariant
end BB6BlockFAR
