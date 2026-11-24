import Lean.Elab.Tactic.Omega

/-! Four-step inverse grammar for the #429 q0 family.
The source interface is an explicit hypothesis, instantiated separately
by the repository's original accelerator predecessor theorems. -/
namespace BB429Q0Macro
set_option maxHeartbeats 2000000

inductive Digit where
  | zero | one | four | five
  deriving DecidableEq, Repr

def digit : Digit → Nat
  | .zero => 0 | .one => 1 | .four => 4 | .five => 5

def cost : Digit → Nat
  | .zero => 3 | .one => 5 | .four => 4 | .five => 6

def offset : Digit → Nat
  | .zero => 0 | .one => 6 | .four => 18 | .five => 32

def num (d : Digit) (p y : Nat) : Nat := y+digit d*p+offset d

def nextP (d : Digit) (p : Nat) := p+cost d
def nextY (d : Digit) (p y : Nat) := num d p y / 16

inductive Path : Nat → Nat → Nat → Prop where
  | nil (p y : Nat) : Path 0 p y
  | cons (d : Digit) {m p y : Nat} (h : num d p y % 16=0)
      (tail : Path m (nextP d p) (nextY d p y)) : Path (m+1) p y

/-- The two boundary rays are never entered from a strict interior state. -/
theorem interior_step (d : Digit) (p y : Nat)
    (hy : 0<y) (hp : 3*y<p) (h : num d p y%16=0) :
    0<nextY d p y ∧ 3*nextY d p y<nextP d p := by
  have hdiv := Nat.mod_add_div (num d p y) 16
  cases d <;> simp [num,digit,cost,offset,nextY,nextP] at * <;> omega

/-- Abstract interface: ordinary inverse classifications and the
source-certified positive-even second-counter invariant. -/
structure Source (Reach : Nat → Nat → Prop) : Prop where
  odd_back : ∀ a b : Nat, 13≤a → a%2=1 → Reach a b →
    (∃ x y, Reach x y ∧ a=2*x+3 ∧ y=b+a) ∨
    (∃ x y, Reach x y ∧ 4*x+26=4*a+b ∧ 2*y=b+4 ∧ b%4=2)
  even_back : ∀ a b : Nat, 6≤a → a%2=0 → Reach a b →
    ∃ x y, Reach x y ∧ 4*x+14=4*a+b ∧ 2*y=b ∧ b%4=2
  even8 : ∀ a b : Nat, 0<a → a%2=0 → Reach a b → b%8=2

variable {Reach : Nat → Nat → Prop}

private theorem odd_phase (src : Source Reach) (a b : Nat)
    (ha : 0<a) (hphase : (2*a+b)%4≠2) (hr : Reach a b) : a%2=1 := by
  by_cases he : a%2=0
  · have hb := src.even8 a b ha he hr
    omega
  · omega

private theorem f_phase (src : Source Reach) (a b : Nat)
    (ha : 13≤a) (hphase : (2*a+b)%4=1 ∨ (2*a+b)%4=3)
    (hr : Reach a b) : ∃ x y, Reach x y ∧ a=2*x+3 ∧ y=b+a := by
  have ho := odd_phase src a b (by omega) (by omega) hr
  rcases src.odd_back a b ha ho hr with h|⟨x,y,hx,h1,h2,h3⟩
  · exact h
  · omega

private theorem phase3_div4 (src : Source Reach) (a b : Nat)
    (ha : 29≤a) (hphase : (2*a+b)%4=3) (hr : Reach a b) :
    (a+3)%4=0 := by
  obtain ⟨x,y,hxy,h1,h2⟩ := f_phase src a b (by omega) (Or.inr hphase) hr
  have ho := odd_phase src x y (by omega) (by omega) hxy
  omega

/-- Four ordinary genuine predecessors. A rank-three phase forces F,
then F/S, then F, then F/E; the new phase-three start is divisible by 4
in the shifted first coordinate. The size guard leaves ample room for
all inverse classifications and the extra phase lookahead. -/
theorem macro_back (src : Source Reach) (a b r x : Nat)
    (ha : 400≤x) (hax : a+3=4*x) (hbr : 2*a+b+1=4*r)
    (hr : Reach a b) :
    ∃ d a' b' r' x', Reach a' b' ∧ a'+3=4*x' ∧
      2*a'+b'+1=4*r' ∧ r=r'+cost d ∧
      16*x'+offset d=x+digit d*r ∧ x≤16*x' := by
  obtain ⟨a1,b1,hreach1,h11,h12⟩ :=
    f_phase src a b (by omega) (Or.inr (by omega)) hr
  have hodd1 := odd_phase src a1 b1 (by omega) (by omega) hreach1
  rcases src.odd_back a1 b1 (by omega) hodd1 hreach1 with
    ⟨a2,b2,hreach2,h21,h22⟩ | ⟨a2,b2,hreach2,h21,h22,h23⟩
  · obtain ⟨a3,b3,hreach3,h31,h32⟩ :=
      f_phase src a2 b2 (by omega) (Or.inl (by omega)) hreach2
    by_cases hodd3 : a3%2=1
    · rcases src.odd_back a3 b3 (by omega) hodd3 hreach3 with
        ⟨a4,b4,hreach4,h41,h42⟩ | ⟨a4,b4,hreach4,h41,h42,h43⟩
      · have hdiv := phase3_div4 src a4 b4 (by omega) (by omega) hreach4
        refine ⟨.zero,a4,b4,r-3,(a4+3)/4,hreach4,?_,?_,?_,?_,?_⟩ <;>
          (try simp [digit,cost,offset]) <;> omega
      · omega
    · obtain ⟨a4,b4,hreach4,h41,h42,h43⟩ :=
        src.even_back a3 b3 (by omega) (by omega) hreach3
      have hdiv := phase3_div4 src a4 b4 (by omega) (by omega) hreach4
      refine ⟨.four,a4,b4,r-4,(a4+3)/4,hreach4,?_,?_,?_,?_,?_⟩ <;>
        (try simp [digit,cost,offset]) <;> omega
  · obtain ⟨a3,b3,hreach3,h31,h32⟩ :=
      f_phase src a2 b2 (by omega) (Or.inl (by omega)) hreach2
    by_cases hodd3 : a3%2=1
    · rcases src.odd_back a3 b3 (by omega) hodd3 hreach3 with
        ⟨a4,b4,hreach4,h41,h42⟩ | ⟨a4,b4,hreach4,h41,h42,h43⟩
      · have hdiv := phase3_div4 src a4 b4 (by omega) (by omega) hreach4
        refine ⟨.one,a4,b4,r-5,(a4+3)/4,hreach4,?_,?_,?_,?_,?_⟩ <;>
          (try simp [digit,cost,offset]) <;> omega
      · omega
    · obtain ⟨a4,b4,hreach4,h41,h42,h43⟩ :=
        src.even_back a3 b3 (by omega) (by omega) hreach3
      have hdiv := phase3_div4 src a4 b4 (by omega) (by omega) hreach4
      refine ⟨.five,a4,b4,r-6,(a4+3)/4,hreach4,?_,?_,?_,?_,?_⟩ <;>
        (try simp [digit,cost,offset]) <;> omega

private theorem pow16_ge_succ (m : Nat) : m+1≤16^m := by
  induction m with
  | zero => decide
  | succ m ih => rw [Nat.pow_succ]; omega

/-- Transfer a genuine positive source ancestry to the signed small-counter
model for the entire remaining macro depth. No machine simulation is used. -/
theorem lift_path (src : Source Reach) :
    ∀ m a b r x p y P Q : Nat,
      Reach a b → a+3=4*x → 2*a+b+1=4*r →
      25*16^m≤x → r+p=16^m*P → x+y=16^m*Q →
      Path m p y := by
  intro m
  induction m with
  | zero => intro a b r x p y P Q hr ha hb hx hP hQ; exact .nil p y
  | succ m ih =>
    intro a b r x p y P Q hr ha hb hx hP hQ
    have hm : 0<16^m := Nat.pow_pos (by decide)
    have hx' : 400≤x := by rw [Nat.pow_succ] at hx; omega
    obtain ⟨d,a',b',r',x',hr',ha',hb',hrcost,hxstep,hxle⟩ :=
      macro_back src a b r x hx' ha hb hr
    have hnum : 16*x'+num d p y=16^(m+1)*(Q+digit d*P) := by
      unfold num
      calc
        16*x'+(y+digit d*p+offset d) = (x+y)+digit d*(r+p) := by
          rw [Nat.mul_add]; omega
        _ = 16^(m+1)*(Q+digit d*P) := by rw [hP,hQ,Nat.mul_add]; ac_rfl
    have hnum' : 16*x'+num d p y=16*(16^m*(Q+digit d*P)) := by
      rw [hnum,Nat.pow_succ]; ac_rfl
    have hdiv : num d p y%16=0 := by omega
    have hsum : x'+nextY d p y=16^m*(Q+digit d*P) := by
      have ht := Nat.mod_add_div (num d p y) 16
      unfold nextY
      omega
    have hrank : r'+nextP d p=16^m*(16*P) := by
      unfold nextP
      have hp : 16^(m+1)*P=16^m*(16*P) := by rw [Nat.pow_succ,Nat.mul_assoc]
      omega
    have hxlo : 25*16^m≤x' := by rw [Nat.pow_succ] at hx; omega
    exact .cons d hdiv (ih a' b' r' x' (nextP d p) (nextY d p y)
      (16*P) (Q+digit d*P) hr' ha' hb' hxlo hrank hsum)

/-- Main exact q0 reduction. If an authentic root reaches the q0 target,
its enormous counters imply an integer macro path of length 8*u+5 from
small, strictly interior initial counters. -/
theorem q0_path (src : Source Reach) (u n a b : Nat)
    (hn : n=23+32*u) (ha : a+24*u+19=13*2^n)
    (hb : b+13=2*a) (hr : Reach a b) :
    Path (8*u+5) (24*u+22) (6*u+4) := by
  let m := 8*u+5
  let p := 24*u+22
  let y := 6*u+4
  have hn' : n=4*m+3 := by dsimp [m]; omega
  have hpw : 2^n=8*16^m := by
    rw [hn',Nat.pow_add,Nat.pow_mul]
    change 16^m*8=8*16^m
    omega
  have hlarge : y≤16^m := by
    have hm := pow16_ge_succ m
    dsimp [m,y] at *
    omega
  have hp : p≤104*16^m := by dsimp [p,y] at *; omega
  let r := 104*16^m-p
  let x := 26*16^m-y
  have h1 : r+p=16^m*104 := by dsimp [r]; omega
  have h2 : x+y=16^m*26 := by dsimp [x]; omega
  have h3 : a+3=4*x := by dsimp [x,y]; rw [hpw] at ha; omega
  have h4 : 2*a+b+1=4*r := by dsimp [r,p]; rw [hpw] at ha; omega
  have h5 : 25*16^m≤x := by dsimp [x]; omega
  exact lift_path src m a b r x p y 104 26 hr h3 h4 h5 h1 h2

#print axioms interior_step
#print axioms macro_back
#print axioms lift_path
#print axioms q0_path
end BB429Q0Macro
