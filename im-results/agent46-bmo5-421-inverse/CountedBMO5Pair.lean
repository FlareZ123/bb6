import Std
import Lean.Elab.Tactic.Omega

namespace CountedBMO5Pair
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
def revpair (n : Nat) := b1 (b0 n)
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

def ones (n : Nat) := rep b1 n 0
@[simp] theorem ones_zero : ones 0=0 := rfl
@[simp] theorem ones_succ (n : Nat) : ones (n+1)=b1 (ones n) := rfl
theorem b0_rev (n t : Nat) : b0 (rep revpair n t)=rep pair n (b0 t) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [rep_succ,revpair,pair,←ih]
theorem twin_ones (n t : Nat) : rep twin n (ones t)=ones (2*n+t) := by
  induction n with
  | zero => simp
  | succ n ih => rw [rep_succ,twin,ih,show 2*(n+1)+t=2*n+t+1+1 by omega,ones_succ,ones_succ]

def mvR (q : Q) (w l r : Nat) : Option Cfg := some ⟨q, if w=0 then b0 l else b1 l, tl r⟩
def mvL (q : Q) (w l r : Nat) : Option Cfg := some ⟨q,tl l, if hd l=0 then b0 (if w=0 then b0 (tl r) else b1 (tl r)) else b1 (if w=0 then b0 (tl r) else b1 (tl r))⟩
/-- Literal #252 table. #754 is its A→B→C→A state conjugate. -/
def step : Cfg → Option Cfg
  | ⟨.A,l,r⟩ => if hd r=0 then mvR .B 1 l r else mvL .D 0 l r
  | ⟨.B,l,r⟩ => if hd r=0 then mvL .C 1 l r else mvR .A 0 l r
  | ⟨.C,l,r⟩ => if hd r=0 then mvR .A 1 l r else mvL .B 1 l r
  | ⟨.D,l,r⟩ => if hd r=0 then mvL .A 1 l r else mvL .E 1 l r
  | ⟨.E,l,r⟩ => if hd r=0 then mvR .F 1 l r else mvL .C 0 l r
  | ⟨.F,l,r⟩ => if hd r=0 then none else mvR .E 0 l r

def run : Nat → Cfg → Option Cfg
  | 0,c => some c
  | n+1,c => (step c).bind (run n)
theorem run_add (a b : Nat) (c : Cfg) : run (a+b) c=(run a c).bind (run b) := by
  induction a generalizing c with
  | zero => simp [run]
  | succ a ih => rw [show a+1+b=a+b+1 by omega]; simp only [run]; cases step c <;> simp [ih]
theorem seq {a b : Nat} {c d : Cfg} {z : Option Cfg} (h : run a c=some d) (h' : run b d=z) : run (a+b) c=z := by rw [run_add,h]; exact h'

macro "micro" : tactic => `(tactic| simp [run,step,mvR,mvL,pair,revpair,twin])

theorem leftA (n l r : Nat) : run (2*n) ⟨.A,rep pair n l,b1 r⟩=some ⟨.A,l,b1 (rep revpair n r)⟩ := by
  induction n generalizing r with
  | zero => simp [run]
  | succ n ih =>
    have h : run 2 ⟨.A,pair (rep pair n l),b1 r⟩=some ⟨.A,rep pair n l,b1 (revpair r)⟩ := by micro
    have h' := seq h (ih (revpair r))
    rw [rep_push] at h'
    simpa only [rep_succ,show 2+2*n=2*(n+1) by omega] using h'

theorem rightA (n l r : Nat) : run (2*n) ⟨.A,l,rep pair n r⟩=some ⟨.A,rep pair n l,r⟩ := by
  induction n generalizing l with
  | zero => simp [run]
  | succ n ih =>
    have h : run 2 ⟨.A,l,pair (rep pair n r)⟩=some ⟨.A,pair l,rep pair n r⟩ := by micro
    have h' := seq h (ih (pair l))
    rw [rep_push] at h'
    simpa only [rep_succ,show 2+2*n=2*(n+1) by omega] using h'

theorem rightE (n l r : Nat) : run (2*n) ⟨.E,l,rep pair n r⟩=some ⟨.E,rep pair n l,r⟩ := by
  induction n generalizing l with
  | zero => simp [run]
  | succ n ih =>
    have h : run 2 ⟨.E,l,pair (rep pair n r)⟩=some ⟨.E,pair l,rep pair n r⟩ := by micro
    have h' := seq h (ih (pair l))
    rw [rep_push] at h'
    simpa only [rep_succ,show 2+2*n=2*(n+1) by omega] using h'

theorem leftC (n l r : Nat) : run (2*n) ⟨.C,rep pair n l,b1 r⟩=some ⟨.C,l,b1 (rep twin n r)⟩ := by
  induction n generalizing r with
  | zero => simp [run]
  | succ n ih =>
    have h : run 2 ⟨.C,pair (rep pair n l),b1 r⟩=some ⟨.C,rep pair n l,b1 (twin r)⟩ := by micro
    have h' := seq h (ih (twin r))
    rw [rep_push] at h'
    simpa only [rep_succ,show 2+2*n=2*(n+1) by omega] using h'

-- Canonical section A2(a,b,c).
def A2 (a b c : Nat) : Cfg := ⟨.A,rep pair (a+1) (twin (rep pair b 0)),ones (c+1)⟩

def tailPair (b : Nat) := tl (rep pair b 0)
theorem tailPair_eq (b : Nat) : b0 (tailPair b)=rep pair b 0 := by
  cases b with
  | zero => rfl
  | succ b => simp [tailPair,pair]

theorem cross (l r : Nat) : run 4 ⟨.A,twin (b0 l),b1 r⟩=some ⟨.A,b1 l,pair (b0 r)⟩ := by micro

-- First pass through the two marker ones, before consuming the last right pair.
theorem firstPass (a b c : Nat) : run (4*a+10) (A2 a b c)=some ⟨.A,rep pair (a+2) (b1 (tailPair b)),b0 (ones c)⟩ := by
  have h1 := leftA (a+1) (twin (rep pair b 0)) (ones c)
  have h2 := cross (tailPair b) (rep revpair (a+1) (ones c))
  rw [tailPair_eq,b0_rev] at h2
  have h3 := rightA (a+2) (b1 (tailPair b)) (b0 (ones c))
  simpa only [A2,ones_succ,rep_succ,show 2*(a+1)+4+2*(a+2)=4*a+10 by omega] using seq (seq h1 h2) h3

theorem firstPositive (a b c : Nat) : run (4*a+12) (A2 a b (c+1))=some ⟨.A,rep pair (a+3) (b1 (tailPair b)),ones c⟩ := by
  have h1 := firstPass a b (c+1)
  have h2 := rightA 1 (rep pair (a+2) (b1 (tailPair b))) (ones c)
  simpa only [ones_succ,rep_succ,rep_zero,pair,show 4*a+10+2*1=4*a+12 by omega] using seq h1 h2

theorem diagonal (a b c : Nat) : run (4*a+12) (A2 a (b+1) (c+2))=some (A2 (a+2) b c) := by
  simpa only [A2,tailPair,rep_succ, pair,tl0,twin,show a+2+1=a+3 by omega] using firstPositive a (b+1) (c+1)

theorem zeroSucc (a b : Nat) : run 2 (A2 (a+1) b 0)=some (A2 a b 1) := by
  simpa only [A2,ones_zero,ones_succ,rep_succ,rep_zero,revpair,b00] using leftA 1 (rep pair (a+1) (twin (rep pair b 0))) 0

-- Second pass for b=0, reaching state E before its last right pair.
theorem secondPass (a c : Nat) : run (8*a+28) (A2 a 0 (c+2))=some ⟨.E,rep pair (a+4) 0,b0 (ones c)⟩ := by
  have h1 := firstPositive a 0 (c+1)
  have h2 := leftA (a+3) (b1 0) (ones c)
  have h3 : run 2 ⟨.A,b1 0,b1 (rep revpair (a+3) (ones c))⟩=some ⟨.E,0,pair (b0 (rep revpair (a+3) (ones c)))⟩ := by micro
  rw [b0_rev] at h3
  have h4 := rightE (a+4) 0 (b0 (ones c))
  simpa only [tailPair,rep_zero,tlZ,ones_succ,rep_succ,show 4*a+12+2*(a+3)+2+2*(a+4)=8*a+28 by omega] using seq (seq (seq h1 h2) h3) h4

theorem halt (a : Nat) : run (8*a+29) (A2 a 0 2)=some ⟨.F,b1 (rep pair (a+4) 0),0⟩ ∧ step ⟨.F,b1 (rep pair (a+4) 0),0⟩=none := by
  have h1 := secondPass a 0
  have h2 : run 1 ⟨.E,rep pair (a+4) 0,0⟩=some ⟨.F,b1 (rep pair (a+4) 0),0⟩ := by micro
  exact ⟨by simpa only [ones_zero,b00,show 8*a+28+1=8*a+29 by omega] using seq h1 h2,by rfl⟩

theorem secondPositive (a c : Nat) : run (8*a+30) (A2 a 0 (c+3))=some ⟨.E,rep pair (a+5) 0,ones c⟩ := by
  have h1 := secondPass a (c+1)
  have h2 := rightE 1 (rep pair (a+4) 0) (ones c)
  simpa only [ones_succ,rep_succ,rep_zero,pair,show 8*a+28+2*1=8*a+30 by omega,show c+1+2=c+3 by omega] using seq h1 h2

theorem restart (a c : Nat) : run (8*a+34) (A2 a 0 (c+6))=some (A2 0 (a+4) c) := by
  have h1 := secondPositive a (c+3)
  have h2 : run 4 ⟨.E,pair (rep pair (a+4) 0),b1 (b1 (b1 (ones c)))⟩=some (A2 0 (a+4) c) := by simp [A2,run,step,mvL,mvR,pair,twin]
  simpa only [ones_succ,rep_succ,show c+3+3=c+6 by omega,show 8*a+30+4=8*a+34 by omega] using seq h1 h2

-- Convert an A configuration with empty right side and an isolated marker 1
-- at the left end of the alternating block into the growth phase.
theorem markerConvert (n l : Nat) : run (2*n+4) ⟨.A,rep pair n (b1 l),0⟩=some ⟨.A,b0 l,ones (2*n+2)⟩ := by
  have h1 : run 2 ⟨.A,rep pair n (b1 l),0⟩=some ⟨.C,rep pair n (b1 l),b1 (b1 0)⟩ := by micro
  have h2 := leftC n (b1 l) (ones 1)
  rw [twin_ones] at h2
  have h3 : run 2 ⟨.C,b1 l,b1 (ones (2*n+1))⟩=some ⟨.A,b0 l,b1 (ones (2*n+1))⟩ := by micro
  simpa only [ones_succ,ones_zero,show 2+2*n+2=2*n+4 by omega] using seq (seq h1 h2) h3

-- A single growth phase: remove two ones and add two alternating pairs.
theorem growth (n m : Nat) : run (4*n+6) ⟨.A,rep pair n 0,ones (2*m+2)⟩=some ⟨.A,rep pair (n+2) 0,ones (2*m)⟩ := by
  have h1 := leftA n 0 (ones (2*m+1))
  have h2 : run 2 ⟨.A,0,b1 (rep revpair n (ones (2*m+1)))⟩=some ⟨.A,0,pair (b0 (rep revpair n (ones (2*m+1))))⟩ := by micro
  rw [b0_rev,show b0 (ones (2*m+1))=pair (ones (2*m)) by rfl,rep_push] at h2
  have h3 := rightA (n+2) 0 (ones (2*m))
  simpa only [ones_succ,rep_succ,pair,show 2*n+2+2*(n+2)=4*n+6 by omega] using seq (seq h1 h2) h3

def growthCost (n m : Nat) := 4*m*(n+m)+2*m

theorem growDrain (n m : Nat) : run (growthCost n m) ⟨.A,rep pair n 0,ones (2*m)⟩=some ⟨.A,rep pair (n+2*m) 0,0⟩ := by
  induction m generalizing n with
  | zero => simp [growthCost,run]
  | succ m ih =>
    have h1 := growth n m
    have h2 := ih (n+2)
    have hsum : 4*n+6+growthCost (n+2) m=growthCost n (m+1) := by
      unfold growthCost
      simp only [Nat.mul_add,Nat.add_mul,Nat.mul_succ]
      omega
    simpa only [hsum,show 2*(m+1)=2*m+2 by omega,show n+2+2*m=n+2*(m+1) by omega] using seq h1 h2

-- Final conversion from alternating pairs back to the canonical section.
theorem finish (n : Nat) : run (2*(n+1)+15) ⟨.A,rep pair (n+1) 0,0⟩=some (A2 0 1 (2*n)) := by
  have h1 : run 2 ⟨.A,rep pair (n+1) 0,0⟩=some ⟨.C,rep pair (n+1) 0,b1 (b1 0)⟩ := by micro
  have h2 := leftC (n+1) 0 (ones 1)
  rw [twin_ones] at h2
  have h3 : run 3 ⟨.C,0,b1 (ones (2*(n+1)+1))⟩=some ⟨.A,b1 0,ones (2*(n+1)+3)⟩ := by simp [ones_succ,run,step,mvR,mvL]
  have h4 : run 2 ⟨.A,b1 0,ones (2*(n+1)+3)⟩=some ⟨.E,0,rep pair 2 (ones (2*n+3))⟩ := by
    rw [show 2*(n+1)+3=2*n+3+1+1 by omega]; simp [ones_succ,run,step,mvR,mvL,pair]
  have h5 := rightE 2 0 (ones (2*n+3))
  have h6 : run 4 ⟨.E,rep pair 2 0,ones (2*n+3)⟩=some (A2 0 1 (2*n)) := by
    rw [show 2*n+3=2*n+1+1+1 by omega]; simp [ones_succ,A2,run,step,mvL,mvR,pair,twin]
  simpa only [ones_succ,ones_zero,show 2+2*(n+1)+3+2+2*2+4=2*(n+1)+15 by omega] using seq (seq (seq (seq (seq h1 h2) h3) h4) h5) h6

theorem finish_growth (n m : Nat) (h : 0<n+2*m) :
    run (growthCost n m+2*(n+2*m)+15) ⟨.A,rep pair n 0,ones (2*m)⟩=some (A2 0 1 (2*(n+2*m-1))) := by
  have h1 := growDrain n m
  have h2 := finish (n+2*m-1)
  rw [show n+2*m-1+1=n+2*m by omega] at h2
  simpa only [Nat.add_assoc] using seq h1 h2

theorem zero (b : Nat) : run (14*b+87) (A2 0 b 0)=some (A2 0 1 (2*b+10)) := by
  have h1 := firstPass 0 b 0
  have h2 := markerConvert 2 (tailPair b)
  rw [tailPair_eq] at h2
  have h3 := finish_growth b 3 (by omega)
  have hsum : 4*0+10+(2*2+4)+(growthCost b 3+2*(b+2*3)+15)=14*b+87 := by unfold growthCost; omega
  simpa only [ones_zero,b00,hsum,show 2*2+2=2*3 by decide,show 2*(b+2*3-1)=2*b+10 by omega] using seq (seq h1 h2) h3

theorem one (a b : Nat) : run (4*a*a+4*a*b+44*a+18*b+125) (A2 a b 1)=some (A2 0 1 (4*a+2*b+14)) := by
  have h1 := firstPositive a b 0
  have h2 := markerConvert (a+3) (tailPair b)
  rw [tailPair_eq] at h2
  have h3 := finish_growth b (a+4) (by omega)
  have hsum : 4*a+12+(2*(a+3)+4)+(growthCost b (a+4)+2*(b+2*(a+4))+15)=4*a*a+4*a*b+44*a+18*b+125 := by
    unfold growthCost
    simp only [Nat.mul_add,Nat.add_mul,Nat.mul_assoc,Nat.mul_comm a b]
    omega
  simpa only [ones_zero,hsum,show 2*(a+3)+2=2*(a+4) by omega,show 2*(b+2*(a+4)-1)=4*a+2*b+14 by omega] using seq (seq h1 h2) h3

theorem four (a : Nat) : run (14*a+91) (A2 a 0 4)=some (A2 0 1 (2*a+12)) := by
  have h1 := secondPositive a 1
  have h2 : run 6 ⟨.E,rep pair (a+5) 0,ones 1⟩=some ⟨.A,rep pair (a+5) 0,ones 2⟩ := by
    rw [show a+5=a+4+1 by omega,rep_succ]; simp [ones_succ,run,step,mvL,mvR,pair]
  have h3 := finish_growth (a+5) 1 (by omega)
  have hsum : 8*a+30+6+(growthCost (a+5) 1+2*(a+5+2*1)+15)=14*a+91 := by unfold growthCost; omega
  simpa only [hsum,show 1+3=4 by decide,show 2*1=2 by decide,show 2*(a+5+2*1-1)=2*a+12 by omega] using seq (seq h1 h2) h3

/-- A successful return counts all primitive moves; a terminal return also
counts the final undefined instruction query. -/
def Exact (c : Cfg) (n : Nat) (out : Option Cfg) : Prop :=
  match out with
  | some d => run n c=some d
  | none => ∃ k d, n=k+1 ∧ run k c=some d ∧ step d=none

theorem exact_seq {a b c d z} (h : run a c=some d) (h' : Exact d b z) : Exact c (a+b) z := by
  cases z with
  | some e => exact seq h h'
  | none =>
    obtain ⟨k,e,hb,hr,hs⟩ := h'
    exact ⟨a+k,e,by omega,seq h hr,hs⟩

theorem halt_exact (a : Nat) : Exact (A2 a 0 2) (8*a+30) none := by
  obtain ⟨hr,hs⟩ := halt a
  exact ⟨8*a+29,_,by omega,hr,hs⟩

-- Count the simultaneous diagonal drain of the two counters.
def diagCost (a k : Nat) := 4*k*(a+k+2)
theorem diagonal_many (a b c k : Nat) :
    run (diagCost a k) (A2 a (b+k) (c+2*k))=some (A2 (a+2*k) b c) := by
  induction k generalizing a with
  | zero => simp [diagCost,run]
  | succ k ih =>
    have h1 := diagonal a (b+k) (c+2*k)
    have h2 := ih (a+2)
    have hsum : 4*a+12+diagCost (a+2) k=diagCost a (k+1) := by
      unfold diagCost
      simp only [Nat.mul_add,Nat.add_mul,Nat.mul_assoc,Nat.mul_comm a k]
      omega
    simpa only [hsum,show c+2*(k+1)=c+2*k+2 by omega,show a+2+2*k=a+2*(k+1) by omega,Nat.add_assoc] using seq h1 h2

def blank252 : Cfg := ⟨.A,0,0⟩
def blank754 : Cfg := ⟨.C,0,0⟩
theorem init252 : run 54 blank252=some (A2 0 1 6) := by decide
theorem init754 : run 30 blank754=some (A2 0 1 2) := by decide

/-- Actual state names of #754, in the common #252 state coordinates. -/
def renQ : Q → Q
  | .A => .B | .B => .C | .C => .A | .D => .D | .E => .E | .F => .F

def rename (c : Cfg) : Cfg := ⟨renQ c.q,c.l,c.r⟩

def step754 : Cfg → Option Cfg
  | ⟨.A,l,r⟩ => if hd r=0 then mvR .B 1 l r else mvL .C 1 l r
  | ⟨.B,l,r⟩ => if hd r=0 then mvR .C 1 l r else mvL .D 0 l r
  | ⟨.C,l,r⟩ => if hd r=0 then mvL .A 1 l r else mvR .B 0 l r
  | ⟨.D,l,r⟩ => if hd r=0 then mvL .B 1 l r else mvL .E 1 l r
  | ⟨.E,l,r⟩ => if hd r=0 then mvR .F 1 l r else mvL .A 0 l r
  | ⟨.F,l,r⟩ => if hd r=0 then none else mvR .E 0 l r

def run754 : Nat → Cfg → Option Cfg
  | 0,c => some c
  | n+1,c => (step754 c).bind (run754 n)

theorem step_conjugate (c : Cfg) : step754 (rename c)=(step c).map rename := by
  rcases c with ⟨q,l,r⟩
  cases q <;> by_cases h : hd r=0 <;> simp [step754,step,rename,renQ,h,mvL,mvR]

theorem run_conjugate (n : Nat) (c : Cfg) : run754 n (rename c)=(run n c).map rename := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih =>
    rw [run754,step_conjugate,run]
    cases step c <;> simp [ih]

theorem init754_literal : run754 30 ⟨.A,0,0⟩=some (rename (A2 0 1 2)) := by
  have h := run_conjugate 30 blank754
  rw [init754] at h
  exact h

#print axioms diagonal_many
#print axioms init252
#print axioms init754_literal
#print axioms run_conjugate
#print axioms diagonal
#print axioms zeroSucc
#print axioms halt
#print axioms restart
#print axioms zero
#print axioms one
#print axioms four
end CountedBMO5Pair
