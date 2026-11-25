import Lean

namespace BB6.Agent12Clock

-- A and M are the left counter and total mass; X is the next left counter.
-- Six times the ordinary primitive cost, valid also for r=1 (direct).
def cost6 (A M X r o : Int) : Int :=
  -4*A^2 + 16*A*o - 22*A + 4*M^2 - 4*M*X - 8*M*o + 24*M*r - M +
  4*X^2 - 8*X*o - 12*X*r + 11*X - 96*o*r + 96*o + 36*r^2 - 51*r + 39

-- Twice Bn and twice C avoid all divisions in the scaled equation.
def bounce6 (A M X r o : Int) : Int :=
  let B := A+2+o
  let Bn2 := (M+3*r+1+X)/2+o
  let C2 := M+3*r+1-X+2*o
  6*(2*A^2+2*A+M-10) + 4*Bn2^2 - 16*B^2 -
  3*(5+8*o)*(Bn2-2*B) - 6*(5+12*o)*(r-2) +
  3*C2^2 - 3*(5+4*o)*C2 + 15*Bn2 + 54-72*o

-- Division-free identity for the bounce formula, using the exact endpoint
-- relation 2*Bn2=M'+X+2*o.
theorem bounce_polynomial (A M X r o T : Int)
    (h : 2*T = M+3*r+1+X+2*o) (ho : o=0 ∨ o=1) :
    cost6 A M X r o =
    6*(2*A^2+2*A+M-10) + 4*T^2 - 16*(A+2+o)^2 -
    3*(5+8*o)*(T-2*(A+2+o)) - 6*(5+12*o)*(r-2) +
    3*(M+3*r+1-X+2*o)^2 - 3*(5+4*o)*(M+3*r+1-X+2*o) +
    15*T + 54-72*o := by
  rcases ho with rfl | rfl <;> simp [cost6] at * <;> grind

theorem direct_polynomial (A M o : Int) (ho : o=0 ∨ o=1) :
    cost6 A M (2*A-M) 1 o = 6*(2*(M-A)^2+4*(M-A)+4) := by
  rcases ho with rfl | rfl <;> simp [cost6] <;> grind

end BB6.Agent12Clock

namespace BB6.Agent12Clock

-- A linear form in the initial left counter and mass.
structure Lin where
  a : Int
  m : Int
  c : Int
  deriving Repr

def Lin.eval (l : Lin) (A M : Int) := l.a*A+l.m*M+l.c

structure Quad where
  aa : Int
  am : Int
  mm : Int
  a : Int
  m : Int
  c : Int
  deriving Repr

def Quad.eval (q : Quad) (A M : Int) := q.aa*A^2+q.am*A*M+q.mm*M^2+q.a*A+q.m*M+q.c

def Quad.add (p q : Quad) : Quad := ⟨p.aa+q.aa,p.am+q.am,p.mm+q.mm,p.a+q.a,p.m+q.m,p.c+q.c⟩
def Quad.scale (k : Int) (q : Quad) : Quad := ⟨k*q.aa,k*q.am,k*q.mm,k*q.a,k*q.m,k*q.c⟩
def Lin.quad (l : Lin) : Quad := ⟨0,0,0,l.a,l.m,l.c⟩
def Lin.mul (p q : Lin) : Quad :=
  ⟨p.a*q.a,p.a*q.m+p.m*q.a,p.m*q.m,p.a*q.c+p.c*q.a,p.m*q.c+p.c*q.m,p.c*q.c⟩

theorem eval_add (p q : Quad) (A M : Int) : (p.add q).eval A M = p.eval A M + q.eval A M := by
  simp [Quad.add,Quad.eval]; grind

theorem eval_scale (k : Int) (q : Quad) (A M : Int) : (q.scale k).eval A M = k*q.eval A M := by
  simp [Quad.scale,Quad.eval]; grind

theorem eval_quad (l : Lin) (A M : Int) : l.quad.eval A M = l.eval A M := by simp [Lin.quad,Quad.eval,Lin.eval]

theorem eval_mul (p q : Lin) (A M : Int) : (p.mul q).eval A M = p.eval A M * q.eval A M := by
  simp [Lin.mul,Quad.eval,Lin.eval]; grind

-- Store 6 times the primitive clock as a quadratic polynomial, with
-- all counter updates represented by linear forms.
def edgePoly (a m x : Lin) (r o : Int) : Quad :=
  (((((((a.mul a).scale (-4)).add ((m.mul m).scale 4)).add ((m.mul x).scale (-4))).add ((x.mul x).scale 4)).add
    (a.quad.scale (16*o-22))).add (m.quad.scale (24*r-8*o-1))).add
    ((x.quad.scale (11-8*o-12*r)).add ⟨0,0,0,0,0,-96*o*r+96*o+36*r^2-51*r+39⟩)

theorem eval_const (c A M : Int) : (⟨0,0,0,0,0,c⟩ : Quad).eval A M = c := by simp [Quad.eval]

theorem eval_edgePoly (a m x : Lin) (r o A M : Int) :
    (edgePoly a m x r o).eval A M = cost6 (a.eval A M) (m.eval A M) (x.eval A M) r o := by
  simp only [edgePoly,eval_add,eval_scale,eval_mul,eval_quad,eval_const,cost6]
  grind

-- Arithmetic composition independent of the prediction mechanism.
-- An arbitrary list of ordinary edges yields one six-coefficient clock.
def foldClock : List (Lin × Lin × Lin × Int × Int) → Quad
  | [] => ⟨0,0,0,0,0,0⟩
  | (a,m,x,r,o)::es => (edgePoly a m x r o).add (foldClock es)

def sumClock (A M : Int) : List (Lin × Lin × Lin × Int × Int) → Int
  | [] => 0
  | (a,m,x,r,o)::es => cost6 (a.eval A M) (m.eval A M) (x.eval A M) r o + sumClock A M es

theorem eval_foldClock (A M : Int) (es : List (Lin × Lin × Lin × Int × Int)) :
    (foldClock es).eval A M = sumClock A M es := by
  induction es with
  | nil => simp [foldClock,Quad.eval,sumClock]
  | cons e es ih => rcases e with ⟨a,m,x,r,o⟩; simp only [foldClock,sumClock,eval_add,eval_edgePoly,ih]

end BB6.Agent12Clock
