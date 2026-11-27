import Std
namespace Raw14042ArithmeticInvariant
inductive Bank where | a | b | c deriving DecidableEq, Repr
structure Section where
  kind : Bank
  p : Nat
  n : Nat
  s : Nat
  deriving Repr

def next (s : Nat) := (s+1)%6
def carry (s : Nat) := if s=5 then 1 else 0
def good (x : Section) : Prop := 24 ≤ x.p ∧ x.p%2=0 ∧ x.s<6

def d (k h : Nat) : Section :=
  let n := k/6; let s := k%6; let t := k+h
  if t%2=1 then ⟨.b,2*t+2,n,s⟩
  else ⟨.b,2*t+11,n+carry s-2,next s⟩
def cc (k m s : Nat) : Section :=
  let t := m+k; let n := (s+k+2)/6; let r := (s+k+2)%6
  if t%2=0 then ⟨.c,2*t+6,n,r⟩
  else ⟨.c,2*t+15,n+carry r-2,next r⟩
def a0 (p : Nat) := cc (p-7) 7 0
def bs (k u v s : Nat) : Section :=
  let p := k+v+1; let n := (k+s)/6; let r := (k+s)%6
  let n' := n+u+carry r-1; let r' := next r
  if p%2=1 then ⟨.a,2*p+6,n',r'⟩
  else ⟨.a,2*p+15,n'+carry r'-2,next r'⟩
def b0 (p : Nat) := bs (p-4) 0 3 1

def terminal (kind : Bank) (p n s : Nat) : Section :=
  match kind,n,s with
  | .a,0,0 => cc (p-2) 0 2
  | .a,0,1 => d (p+3) 8
  | .a,0,2 => d (p+1) 8
  | .a,0,3 => if p%4=2 then ⟨.b,2*p+6,(p/2+1)/6,(p/2+1)%6⟩ else ⟨.b,3*p+20,p/4-1,1⟩
  | .a,0,4 => b0 (p+11)
  | .a,0,_ => d (p+5) 8
  | .a,1,0 | .a,1,1 => a0 (p+12)
  | .a,1,2 => b0 (p+13)
  | .a,1,3 => cc (p+4) 10 0
  | .a,1,4 => a0 (p+16)
  | .a,1,_ => ⟨.a,p+12,0,0⟩
  | .b,0,0 => bs (p-4) 0 6 1
  | .b,0,1 => b0 (p+5)
  | .b,0,2 => bs (p-2) 1 0 1
  | .b,0,3 => a0 (p+8)
  | .b,0,4 => a0 (p+6)
  | .b,0,_ => if p%4=0 then ⟨.c,3*p+18,p/4-1,1⟩ else ⟨.c,2*p+4,(p/2+1)/6,(p/2+1)%6⟩
  | .b,1,0 => d (p+5) 8
  | .b,1,1 => a0 (p+10)
  | .b,1,2 | .b,1,3 => b0 (p+13)
  | .b,1,4 => d (p+7) 8
  | .b,1,_ => ⟨.b,p+12,0,0⟩
  | .c,0,0 => d (p-4) 11
  | .c,0,1 => d (p+1) 8
  | .c,0,2 => ⟨.b,2*p+8,(p+4)/6,(p+4)%6⟩
  | .c,0,3 => b0 (p+11)
  | .c,0,4 => b0 (p+9)
  | .c,0,_ => if p%4=0 then ⟨.a,2*p+10,(p/2)/6,(p/2)%6⟩ else ⟨.a,3*p+38,p/4-2,0⟩
  | .c,1,0 => a0 (p+12)
  | .c,1,1 => b0 (p+13)
  | .c,1,2 | .c,1,3 => d (p+9) 8
  | .c,1,4 => a0 (p+14)
  | .c,1,_ => ⟨.c,p+12,0,0⟩
  | _,_,_ => ⟨.a,p,0,0⟩

theorem terminal_good (b : Bank) (p n s : Nat) (hp : 24≤p) (he : p%2=0) (hn : n<2) (hs : s<6) : good (terminal b p n s) := by
  have hN : n=0 ∨ n=1 := by omega
  have hS : s=0 ∨ s=1 ∨ s=2 ∨ s=3 ∨ s=4 ∨ s=5 := by omega
  rcases hN with rfl|rfl <;> rcases hS with rfl|rfl|rfl|rfl|rfl|rfl <;> cases b <;>
    simp only [terminal,d,cc,a0,bs,b0,good,next,carry] <;> (try split) <;> simp_all <;> omega

def drainStep (x : Section) : Section := ⟨x.kind,x.p+12,x.n-2+carry x.s,next x.s⟩
theorem drain_good (x : Section) (hx : good x) : good (drainStep x) := by
  rcases hx with ⟨hp,he,hs⟩
  simp only [good,drainStep,next]
  omega
theorem drain_decreases (x : Section) (hx : good x) (hn : 2 ≤ x.n) :
    6*(drainStep x).n+(drainStep x).s+11 = 6*x.n+x.s := by
  rcases hx with ⟨hp,he,hs⟩
  simp only [drainStep,carry,next]
  split <;> omega
def step (x : Section) : Section :=
  if 2 ≤ x.n then drainStep x else terminal x.kind x.p x.n x.s
theorem step_good (x : Section) (hx : good x) : good (step x) := by
  unfold step
  split
  · exact drain_good x hx
  · exact terminal_good x.kind x.p x.n x.s hx.1 hx.2.1 (by omega) hx.2.2
def orbit (k : Nat) : Section := match k with
  | 0 => ⟨.a,12472,0,3⟩
  | k+1 => step (orbit k)
theorem orbit_good (k : Nat) : good (orbit k) := by
  induction k with
  | zero => simp [good,orbit]
  | succ k ih => exact step_good _ ih
#print axioms orbit_good
#print axioms drain_decreases
#print axioms terminal_good
end Raw14042ArithmeticInvariant
