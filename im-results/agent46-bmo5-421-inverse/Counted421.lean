import Std
import Lean.Elab.Tactic.Omega

namespace Counted421
inductive Q where | A | B | C | D | E | F deriving DecidableEq, Repr
structure Cfg where
  q : Q
  l : Nat
  r : Nat
  deriving DecidableEq, Repr

def b0 (n : Nat) := 2*n
def b1 (n : Nat) := 2*n+1
def hd (n : Nat) := n%2
def tl (n : Nat) := n/2
@[simp] theorem hd0 (n) : hd (b0 n)=0 := by simp [hd,b0]
@[simp] theorem hd1 (n) : hd (b1 n)=1 := by simp [hd,b1]
@[simp] theorem tl0 (n) : tl (b0 n)=n := by simp [tl,b0]
@[simp] theorem tl1 (n) : tl (b1 n)=n := by simp [tl,b1]; omega
@[simp] theorem b00 : b0 0=0 := rfl
@[simp] theorem hdZ : hd 0=0 := rfl
@[simp] theorem tlZ : tl 0=0 := rfl

def pair (n : Nat) := b0 (b1 n)
def twin (n : Nat) := b1 (b1 n)
def rep (f : Nat → Nat) : Nat → Nat → Nat
  | 0, x => x
  | n+1,x => f (rep f n x)
@[simp] theorem rep_zero (f x) : rep f 0 x=x := rfl
@[simp] theorem rep_succ (f n x) : rep f (n+1) x=f (rep f n x) := rfl
theorem rep_push (f n x) : rep f n (f x)=f (rep f n x) := by induction n <;> simp [*]
theorem rep_add (f m n x) : rep f (m+n) x=rep f m (rep f n x) := by
  induction m with
  | zero => simp
  | succ m ih => rw [show m+1+n=m+n+1 by omega,rep_succ,ih,rep_succ]

def mvR (q : Q) (w l r : Nat) : Option Cfg := some ⟨q, if w=0 then b0 l else b1 l, tl r⟩
def mvL (q : Q) (w l r : Nat) : Option Cfg := some ⟨q,tl l, if hd l=0 then b0 (if w=0 then b0 (tl r) else b1 (tl r)) else b1 (if w=0 then b0 (tl r) else b1 (tl r))⟩
def step : Cfg → Option Cfg
  | ⟨.A,l,r⟩ => if hd r=0 then mvR .B 1 l r else mvR .E 1 l r
  | ⟨.B,l,r⟩ => if hd r=0 then mvL .C 1 l r else mvR .A 0 l r
  | ⟨.C,l,r⟩ => if hd r=0 then mvR .D 1 l r else mvL .B 0 l r
  | ⟨.D,l,r⟩ => if hd r=0 then mvL .B 1 l r else mvR .C 1 l r
  | ⟨.E,l,r⟩ => if hd r=0 then mvL .F 1 l r else mvR .D 0 l r
  | ⟨.F,l,r⟩ => if hd r=0 then none else mvL .E 0 l r

def run : Nat → Cfg → Option Cfg
  | 0,c => some c
  | n+1,c => (step c).bind (run n)

theorem run_add (a b : Nat) (c : Cfg) : run (a+b) c=(run a c).bind (run b) := by
  induction a generalizing c with
  | zero => simp [run]
  | succ a ih => rw [show a+1+b=a+b+1 by omega]; simp only [run]; cases step c <;> simp [ih]

theorem seq {a b : Nat} {c d : Cfg} {z : Option Cfg} (h : run a c=some d) (h' : run b d=z) : run (a+b) c=z := by rw [run_add,h]; exact h'

-- A right and C right two-cell sweeps.
theorem aRight (n l r : Nat) : run (2*n) ⟨.A,l,rep pair n r⟩=some ⟨.A,rep pair n l,r⟩ := by
  induction n generalizing l with
  | zero => simp [run]
  | succ n ih =>
    have h : run 2 ⟨.A,l,pair (rep pair n r)⟩=some ⟨.A,pair l,rep pair n r⟩ := by simp [run,step,mvL,mvR,pair]
    have h' := seq h (ih (pair l))
    rw [rep_push] at h'
    simpa only [rep_succ,show 2+2*n=2*(n+1) by omega] using h'

theorem cRight (n l r : Nat) : run (2*n) ⟨.C,l,rep pair n r⟩=some ⟨.C,rep twin n l,r⟩ := by
  induction n generalizing l with
  | zero => simp [run]
  | succ n ih =>
    have h : run 2 ⟨.C,l,pair (rep pair n r)⟩=some ⟨.C,twin l,rep pair n r⟩ := by simp [run,step,mvL,mvR,pair,twin]
    have h' := seq h (ih (twin l))
    rw [rep_push] at h'
    simpa only [rep_succ,show 2+2*n=2*(n+1) by omega] using h'

theorem cLeft (n l r : Nat) : run (2*n) ⟨.C,rep pair n l,twin r⟩=some ⟨.C,l,twin (rep pair n r)⟩ := by
  induction n generalizing r with
  | zero => simp [run]
  | succ n ih =>
    have h : run 2 ⟨.C,pair (rep pair n l),twin r⟩=some ⟨.C,rep pair n l,twin (pair r)⟩ := by simp [run,step,mvL,mvR,pair,twin]
    have h' := seq h (ih (pair r))
    rw [rep_push] at h'
    simpa only [rep_succ,show 2+2*n=2*(n+1) by omega] using h'

theorem fLeft (n l r : Nat) : run (2*n) ⟨.F,rep pair n l,twin r⟩=some ⟨.F,l,twin (rep pair n r)⟩ := by
  induction n generalizing r with
  | zero => simp [run]
  | succ n ih =>
    have h : run 2 ⟨.F,pair (rep pair n l),twin r⟩=some ⟨.F,rep pair n l,twin (pair r)⟩ := by simp [run,step,mvL,mvR,pair,twin]
    have h' := seq h (ih (pair r))
    rw [rep_push] at h'
    simpa only [rep_succ,show 2+2*n=2*(n+1) by omega] using h'

theorem twin_rep (n l : Nat) : rep twin n l = rep b1 (2*n) l := by
  induction n with
  | zero => rfl
  | succ n ih => rw [rep_succ,twin,ih,show 2*(n+1)=2*n+1+1 by omega,rep_succ,rep_succ]

def C1 (a : Nat) : Cfg := ⟨.C,rep b1 (a+1) 0,0⟩
def C2 (a b : Nat) : Cfg := ⟨.C,rep b1 (a+1) 0,twin (pair (rep pair b 0))⟩
def D (a b c : Nat) : Cfg := ⟨.D,rep pair (a+1) (rep b1 b 0),rep pair (c+1) 0⟩

-- All finite micro-transitions use the literal table above.
macro "micro" : tactic => `(tactic| simp [run,step,mvR,mvL,pair,twin])

theorem drainD (a l r : Nat) : run (2*a+2) ⟨.D,rep pair (a+1) l,pair r⟩=some ⟨.C,l,twin (rep pair a (twin r))⟩ := by
  have h : run 2 ⟨.D,pair (rep pair a l),pair r⟩=some ⟨.C,rep pair a l,twin (twin r)⟩ := by micro
  simpa only [rep_succ,Nat.add_comm] using seq h (cLeft a l (twin r))

theorem bounceD (a l r : Nat) : run (4*a+8) ⟨.D,rep pair (a+1) (b1 l),pair r⟩=some ⟨.D,rep pair (a+2) (b0 l),r⟩ := by
  have h1 := drainD a (b1 l) r
  have h2 : run 2 ⟨.C,b1 l,twin (rep pair a (twin r))⟩=some ⟨.A,b0 l,rep pair (a+1) (twin r)⟩ := by micro
  have h3 := aRight (a+1) (b0 l) (twin r)
  have h4 : run 2 ⟨.A,rep pair (a+1) (b0 l),twin r⟩=some ⟨.D,rep pair (a+2) (b0 l),r⟩ := by micro
  simpa only [show 2*a+2+2+2*(a+1)+2=4*a+8 by omega] using seq (seq (seq h1 h2) h3) h4

theorem sweepD0 (a r : Nat) : run (4*a+8) ⟨.D,rep pair (a+1) 0,pair r⟩=some ⟨.C,rep twin (a+2) 0,twin r⟩ := by
  have h1 := drainD a 0 r
  have h2 : run 2 ⟨.C,0,twin (rep pair a (twin r))⟩=some ⟨.C,0,rep pair (a+2) (twin r)⟩ := by micro
  have h3 := cRight (a+2) 0 (twin r)
  simpa only [show 2*a+2+2+2*(a+2)=4*a+8 by omega] using seq (seq h1 h2) h3

theorem sweepC2 (l b : Nat) : run (4*b+12) ⟨.C,b1 l,twin (pair (rep pair b 0))⟩=some ⟨.C,b0 l,twin (rep pair (b+2) 0)⟩ := by
  have h1 : run 2 ⟨.C,b1 l,twin (pair (rep pair b 0))⟩=some ⟨.A,b0 l,rep pair (b+2) 0⟩ := by micro
  have h2 := aRight (b+2) (b0 l) 0
  have h3 : run 2 ⟨.A,rep pair (b+2) (b0 l),0⟩=some ⟨.C,rep pair (b+2) (b0 l),twin 0⟩ := by micro
  have h4 := cLeft (b+2) (b0 l) 0
  simpa only [show 2+2*(b+2)+2+2*(b+2)=4*b+12 by omega] using seq (seq (seq h1 h2) h3) h4

theorem finishD0 (k : Nat) : run (4*k+14) ⟨.D,rep pair (k+1) 0,0⟩=some (C2 (2*k+1) 0) := by
  have h1 : run 2 ⟨.D,rep pair (k+1) 0,0⟩=some ⟨.C,rep pair k 0,twin (b1 0)⟩ := by micro
  have h2 := cLeft k 0 (b1 0)
  have h3 : run 4 ⟨.C,0,twin (rep pair k (b1 0))⟩=some ⟨.C,twin 0,rep pair (k+1) (b1 0)⟩ := by micro
  have h4 := cRight (k+1) (twin 0) (b1 0)
  have h5 : run 6 ⟨.C,rep twin (k+1) (twin 0),b1 0⟩=some (C2 (2*k+1) 0) := by
    rw [rep_push, twin_rep]
    rw [show 2*(k+1)=2*k+2 by omega]
    simp [C2,run,step,mvR,mvL,twin,pair]
  simpa only [show 2+2*k+4+2*(k+1)+6=4*k+14 by omega] using seq (seq (seq (seq h1 h2) h3) h4) h5

theorem finishD1 (k l : Nat) : run (6*k+10) ⟨.D,rep pair (k+1) (b1 l),0⟩=some ⟨.F,b0 l,twin (rep pair (k+1) 0)⟩ := by
  have h1 : run 2 ⟨.D,rep pair (k+1) (b1 l),0⟩=some ⟨.C,rep pair k (b1 l),twin (b1 0)⟩ := by micro
  have h2 := cLeft k (b1 l) (b1 0)
  have h3 : run 2 ⟨.C,b1 l,twin (rep pair k (b1 0))⟩=some ⟨.A,b0 l,rep pair (k+1) (b1 0)⟩ := by micro
  have h4 := aRight (k+1) (b0 l) (b1 0)
  have h5 : run 2 ⟨.A,rep pair (k+1) (b0 l),b1 0⟩=some ⟨.F,rep pair (k+1) (b0 l),twin 0⟩ := by micro
  have h6 := fLeft (k+1) (b0 l) 0
  simpa only [show 2+2*k+2+2*(k+1)+2+2*(k+1)=6*k+10 by omega] using seq (seq (seq (seq (seq h1 h2) h3) h4) h5) h6

theorem sweepD3 (a l : Nat) : run (10*a+30) ⟨.D,rep pair (a+1) (b1 (b1 (b1 l))),pair 0⟩=some ⟨.F,b0 l,twin (rep pair (a+3) 0)⟩ := by
  have h1 := bounceD a (b1 (b1 l)) 0
  have h2 := finishD1 (a+2) l
  rw [show rep pair (a+2) (b0 (b1 (b1 l)))=rep pair (a+3) (b1 l) by change rep pair (a+2) (pair (b1 l)) = _; rw [rep_push]; rfl] at h1
  simpa only [show 4*a+8+(6*(a+2)+10)=10*a+30 by omega] using seq h1 h2

theorem blank : run 8 ⟨.A,0,0⟩=some (C1 3) := by decide

theorem c1_0 : run 9 (C1 0)=some ⟨.F,0,rep pair 3 0⟩ := by decide
theorem c1_0_halt : run 10 (C1 0)=none := by decide
theorem c1_1 : run 13 (C1 1)=some (C2 1 0) := by decide
theorem c1_succ (a : Nat) : run 9 (C1 (a+2))=some (D 0 a 1) := by
  simp [C1,D,run,step,mvL,mvR,pair]

theorem c2_succ (a b : Nat) : run (4*b+14) (C2 (a+2) b)=some (C2 a (b+2)) := by
  have h1 := sweepC2 (rep b1 (a+2) 0) b
  have h2 : run 2 ⟨.C,b0 (rep b1 (a+2) 0),twin (rep pair (b+2) 0)⟩=some (C2 a (b+2)) := by
    simp [C2,run,step,mvL,mvR,pair,twin]
  simpa only [C2,rep_succ,show 4*b+12+2=4*b+14 by omega] using seq h1 h2

theorem c2_0 (b : Nat) : run (6*b+22) (C2 0 b)=some (C1 (2*b+7)) := by
  have h1 := sweepC2 0 b
  have h2 : run 2 ⟨.C,b0 0,twin (rep pair (b+2) 0)⟩=some ⟨.C,0,rep pair (b+4) 0⟩ := by micro
  have h3 := cRight (b+4) 0 0
  rw [twin_rep,show 2*(b+4)=2*b+7+1 by omega] at h3
  simpa only [C1,C2,rep_succ,rep_zero,show 4*b+12+2+ (2*b+7+1)=6*b+22 by omega] using seq (seq h1 h2) h3

theorem c2_1 (b : Nat) : run (6*b+26) (C2 1 b)=some (C1 (2*b+9)) := by
  have h1 := sweepC2 (b1 0) b
  have h2 : run 4 ⟨.C,b0 (b1 0),twin (rep pair (b+2) 0)⟩=some ⟨.C,0,rep pair (b+5) 0⟩ := by micro
  have h3 := cRight (b+5) 0 0
  rw [twin_rep,show 2*(b+5)=2*b+9+1 by omega] at h3
  simpa only [C1,C2,rep_succ,rep_zero,show 4*b+12+4+ (2*b+9+1)=6*b+26 by omega] using seq (seq h1 h2) h3

theorem d_0_0 (a : Nat) : run (4*a+18) (D a 0 0)=some (C2 (2*a+1) 1) := by
  have h1 := sweepD0 a 0
  rw [twin_rep,show 2*(a+2)=2*a+1+1+1+1 by omega] at h1
  have h2 : run 10 ⟨.C,rep b1 (2*a+1+1+1+1) 0,twin 0⟩=some (C2 (2*a+1) 1) := by
    simp [C2,run,step,mvL,mvR,pair,twin]
  simpa only [D,rep_zero,rep_succ,show 4*a+8+10=4*a+18 by omega] using seq h1 h2

theorem d_0_succ (a c : Nat) : run (4*a+8) (D a 0 (c+1))=some (C2 (2*a+3) c) := by
  have h := sweepD0 a (rep pair (c+1) 0)
  rw [twin_rep,show 2*(a+2)=2*a+3+1 by omega] at h
  simpa only [D,C2,rep_zero,rep_succ] using h

theorem d_1_0 (a : Nat) : run (8*a+26) (D a 1 0)=some (C2 (2*a+3) 0) := by
  have h1 := bounceD a 0 0
  have h2 := finishD0 (a+1)
  rw [b00] at h1
  simpa only [D,rep_succ,rep_zero,show 4*a+8+(4*(a+1)+14)=8*a+26 by omega,show 2*(a+1)+1=2*a+3 by omega] using seq h1 h2

theorem d_2_0 (a : Nat) : run (8*a+30) (D a 2 0)=some (C2 (2*a+5) 0) := by
  have h1 := bounceD a (b1 0) 0
  have h2 := finishD0 (a+2)
  rw [show rep pair (a+2) (b0 (b1 0))=rep pair (a+3) 0 by change rep pair (a+2) (pair 0)=_; rw [rep_push]; rfl] at h1
  simpa only [D,rep_succ,rep_zero,show 4*a+8+(4*(a+2)+14)=8*a+30 by omega,show 2*(a+2)+1=2*a+5 by omega] using seq h1 h2

theorem d_1_succ (a c : Nat) : run (4*a+8) (D a 1 (c+1))=some (D (a+1) 0 c) := by
  simpa only [D,rep_zero,rep_succ,b00] using bounceD a 0 (rep pair (c+1) 0)

theorem d_ge2_succ (a b c : Nat) : run (4*a+8) (D a (b+2) (c+1))=some (D (a+2) b c) := by
  have h := bounceD a (b1 (rep b1 b 0)) (rep pair (c+1) 0)
  rw [show rep pair (a+2) (b0 (b1 (rep b1 b 0)))=rep pair (a+3) (rep b1 b 0) by change rep pair (a+2) (pair (rep b1 b 0))=_; rw [rep_push]; rfl] at h
  simpa only [D,rep_succ] using h

theorem d_3_0 (a : Nat) : run (10*a+32) (D a 3 0)=some ⟨.F,0,rep pair (a+5) 0⟩ := by
  have h1 := sweepD3 a 0
  have h2 : run 2 ⟨.F,b0 0,twin (rep pair (a+3) 0)⟩=some ⟨.F,0,rep pair (a+5) 0⟩ := by micro
  simpa only [D,rep_succ,rep_zero,show 10*a+30+2=10*a+32 by omega] using seq h1 h2

theorem d_4_0 (a : Nat) : run (10*a+34) (D a 4 0)=some ⟨.F,0,rep pair (a+6) 0⟩ := by
  have h1 := sweepD3 a (b1 0)
  have h2 : run 4 ⟨.F,b0 (b1 0),twin (rep pair (a+3) 0)⟩=some ⟨.F,0,rep pair (a+6) 0⟩ := by micro
  simpa only [D,rep_succ,rep_zero,show 10*a+30+4=10*a+34 by omega] using seq h1 h2

theorem d_5_0 (a : Nat) : run (10*a+38) (D a 5 0)=some (C2 1 (a+3)) := by
  have h1 := sweepD3 a (twin 0)
  have h2 : run 8 ⟨.F,b0 (twin 0),twin (rep pair (a+3) 0)⟩=some (C2 1 (a+3)) := by
    simp [C2,run,step,mvL,mvR,pair,twin]
  simpa only [D,rep_succ,rep_zero,twin,show 10*a+30+8=10*a+38 by omega] using seq h1 h2

theorem d_ge6_0 (a b : Nat) : run (10*a+34) (D a (b+6) 0)=some (D 0 b (a+4)) := by
  have h1 := sweepD3 a (rep b1 (b+3) 0)
  have h2 : run 4 ⟨.F,b0 (rep b1 (b+3) 0),twin (rep pair (a+3) 0)⟩=some (D 0 b (a+4)) := by
    simp [D,run,step,mvL,mvR,pair,twin]
  simpa only [D,rep_succ,rep_zero,show 10*a+30+4=10*a+34 by omega] using seq h1 h2

#print axioms c1_succ
#print axioms c2_succ
#print axioms c2_0
#print axioms c2_1
#print axioms d_0_0
#print axioms d_0_succ
#print axioms d_1_0
#print axioms d_2_0
#print axioms d_1_succ
#print axioms d_ge2_succ
#print axioms d_3_0
#print axioms d_4_0
#print axioms d_5_0
#print axioms d_ge6_0

inductive Work where
  | d (a b c : Nat)
  | c2 (a b : Nat)
  deriving DecidableEq

def encode : Work → Cfg
  | .d a b c => D a b c
  | .c2 a b => C2 a b

-- Right is a completed section: some counter or a final halting query.
def macroStep : Work → Nat × Sum Work (Option Nat)
  | .c2 0 b => (6*b+22, .inr (some (2*b+7)))
  | .c2 1 b => (6*b+26, .inr (some (2*b+9)))
  | .c2 (a+2) b => (4*b+14, .inl (.c2 a (b+2)))
  | .d a 0 0 => (4*a+18, .inl (.c2 (2*a+1) 1))
  | .d a 1 0 => (8*a+26, .inl (.c2 (2*a+3) 0))
  | .d a 2 0 => (8*a+30, .inl (.c2 (2*a+5) 0))
  | .d a 3 0 => (10*a+33, .inr none)
  | .d a 4 0 => (10*a+35, .inr none)
  | .d a 5 0 => (10*a+38, .inl (.c2 1 (a+3)))
  | .d a (b+6) 0 => (10*a+34, .inl (.d 0 b (a+4)))
  | .d a 0 (c+1) => (4*a+8, .inl (.c2 (2*a+3) c))
  | .d a 1 (c+1) => (4*a+8, .inl (.d (a+1) 0 c))
  | .d a (b+2) (c+1) => (4*a+8, .inl (.d (a+2) b c))

def Exact (c : Cfg) (n : Nat) (out : Option Cfg) : Prop :=
  match out with
  | some d => run n c = some d
  | none => ∃ k d, n=k+1 ∧ run k c=some d ∧ step d=none

theorem exact_seq {a b c d z} (h : run a c=some d) (h' : Exact d b z) : Exact c (a+b) z := by
  cases z with
  | some e => exact seq h h'
  | none =>
    obtain ⟨k,e,hb,hr,hs⟩ := h'
    exact ⟨a+k,e,by omega,seq h hr,hs⟩

def decode : Sum Work (Option Nat) → Option Cfg
  | .inl w => some (encode w)
  | .inr n => n.map C1

theorem macro_exact (w : Work) : Exact (encode w) (macroStep w).1 (decode (macroStep w).2) := by
  cases w with
  | c2 a b =>
    rcases a with _|_|a
    · exact c2_0 b
    · exact c2_1 b
    · exact c2_succ a b
  | d a b c =>
    cases c with
    | zero =>
      rcases b with _|_|_|_|_|_|b
      · exact d_0_0 a
      · exact d_1_0 a
      · exact d_2_0 a
      · exact ⟨10*a+32,_,by simp [macroStep],d_3_0 a,by simp [step,pair]⟩
      · exact ⟨10*a+34,_,by simp [macroStep],d_4_0 a,by simp [step,pair]⟩
      · exact d_5_0 a
      · exact d_ge6_0 a b
    | succ c =>
      rcases b with _|_|b
      · exact d_0_succ a c
      · exact d_1_succ a c
      · simpa [Nat.add_assoc,macroStep,encode,decode,Exact] using d_ge2_succ a b c

-- A fuel bound which decreases under every nonterminal macro.
def Valid (N : Nat) : Work → Prop
  | .d a b c => a+b≤N ∧ c≤N+4
  | .c2 a b => a≤2*N+5 ∧ a+b≤3*N+10

def rank (N : Nat) : Work → Nat
  | .d _ b _ => b+2*N+7
  | .c2 a _ => a+1

def unitCost (N : Nat) := 20*(N+10)

theorem macro_budget (N : Nat) (w : Work) (h : Valid N w) :
    (macroStep w).1 ≤ unitCost N ∧ 0<rank N w ∧
    ∀ v, (macroStep w).2=.inl v → Valid N v ∧ rank N v<rank N w := by
  cases w with
  | c2 a b =>
    rcases a with _|_|a <;> simp [Valid,rank,unitCost,macroStep] at * <;> omega
  | d a b c =>
    cases c with
    | zero => rcases b with _|_|_|_|_|_|b <;> simp [Valid,rank,unitCost,macroStep] at * <;> omega
    | succ c => rcases b with _|_|b <;> simp [Valid,rank,unitCost,macroStep] at * <;> omega

-- Exact finite evaluator for a whole D/C2 section.
def eval (fuel : Nat) (w : Work) : Nat × Option Nat :=
  match fuel with
  | 0 => (0,none)
  | fuel+1 =>
    let (cost,out) := macroStep w
    match out with
    | .inr x => (cost,x)
    | .inl v => let (total,x) := eval fuel v; (cost+total,x)

theorem eval_exact_bound (N fuel : Nat) (w : Work) (hv : Valid N w) (hf : rank N w ≤ fuel) :
    Exact (encode w) (eval fuel w).1 ((eval fuel w).2.map C1) ∧
    (eval fuel w).1 ≤ rank N w * unitCost N := by
  induction fuel generalizing w with
  | zero => have h := (macro_budget N w hv).2.1; omega
  | succ fuel ih =>
    have hb := macro_budget N w hv
    have he := macro_exact w
    cases hm : macroStep w with
    | mk cost out =>
      rw [hm] at hb he
      cases out with
      | inr x =>
        simp only [eval,hm,decode] at *
        refine ⟨he,?_⟩
        have h := Nat.mul_le_mul_right (unitCost N) hb.2.1
        simp only [Nat.one_mul] at h
        omega
      | inl v =>
        obtain ⟨hv',hr⟩ := hb.2.2 v rfl
        obtain ⟨hx,hy⟩ := ih v hv' (by omega)
        cases hs : eval fuel v with
        | mk n x =>
          simp only [eval,hm,hs,decode] at *
          refine ⟨exact_seq he hx,?_⟩
          have hmul := Nat.mul_le_mul_right (unitCost N) (show rank N v+1≤rank N w by omega)
          rw [Nat.add_mul,Nat.one_mul] at hmul
          omega

-- One return from a positive unary C1 counter, using the exact source tape.
def sectionEval (a : Nat) : Nat × Option Nat :=
  match a with
  | 0 => (10,none)
  | 1 => let (n,x) := eval 7 (.c2 1 0); (13+n,x)
  | a+2 => let (n,x) := eval (a+2*a+7) (.d 0 a 1); (9+n,x)

theorem section_exact (a : Nat) : Exact (C1 a) (sectionEval a).1 ((sectionEval a).2.map C1) := by
  rcases a with _|_|a
  · exact ⟨9,_,rfl,c1_0,by decide⟩
  · have h := (eval_exact_bound 1 7 (.c2 1 0) (by simp [Valid]) (by simp [rank])).1
    exact exact_seq c1_1 h
  · have h := (eval_exact_bound a (a+2*a+7) (.d 0 a 1) (by simp [Valid]) (by simp [rank])).1
    exact exact_seq (c1_succ a) h

theorem section_bound (a : Nat) : (sectionEval a).1 ≤ 100*(a+10)^2 := by
  rcases a with _|_|a
  · decide
  · decide
  · have h := (eval_exact_bound a (a+2*a+7) (.d 0 a 1) (by simp [Valid]) (by simp [rank])).2
    change 9+(eval (a+2*a+7) (.d 0 a 1)).1 ≤ 100*(a+2+10)^2
    have h' : rank a (.d 0 a 1) ≤ 3*(a+2+10) := by simp [rank]; omega
    have h'' : unitCost a ≤ 20*(a+2+10) := by simp [unitCost]; omega
    have hp := Nat.mul_le_mul h' h''
    have hbase : 1 ≤ (a+2+10)^2 := by
      have := Nat.pow_pos (n:=2) (show 0<a+2+10 by omega); omega
    have hm : 3*(a+2+10)*(20*(a+2+10))=60*(a+2+10)^2 := by
      rw [Nat.pow_two]
      calc
        3*(a+2+10)*(20*(a+2+10)) = (3*20)*((a+2+10)*(a+2+10)) := by ac_rfl
        _ = _ := by rfl
    rw [hm] at hp
    omega

#print axioms macro_exact
#print axioms eval_exact_bound
#print axioms section_exact
#print axioms section_bound
end Counted421
