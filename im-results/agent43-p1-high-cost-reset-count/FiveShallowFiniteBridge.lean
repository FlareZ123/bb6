import FiveShallowIntegerAlgebra
import FiveShallowOverflowBounds
import Lean.Elab.Tactic.Omega

namespace BB6.Agent43FiveShallowFiniteBridge

open BB6.Agent43TwoShallowFinite
open BB6.Agent43ThreeShallowFinite
open BB6.Agent43FourShallowFinite
open BB6.Agent43FiveShallowFinite
open BB6.Agent43FiveShallowOverflow

set_option maxRecDepth 4096
set_option maxHeartbeats 12000000

/-- The five exact source numerators factor successively by the five
shallow factors. This packages the algebraic telescoping identity together
with the five source remainder equations. -/
theorem five_numerator_factorizations
 (n s u v w x r alpha beta gamma delta epsilon p d
  C1 C2 C3 C4 C5 L1 L2 L3 L4 L5 O1 O2 O3 O4 O5
  K R1 R2 R3 R4 R5 E : Nat)
 (hP : (8:Nat)^s*p=2^n)
 (hR1 : R1+O1+d=L1*(n+6+3*s))
 (hR2 : R2+O2=L2*(n+6+3*s+alpha+3*u))
 (hR3 : R3+O3=L3*(n+6+3*s+alpha+3*u+beta+3*v))
 (hR4 : R4+O4=L4*(n+6+3*s+alpha+3*u+beta+3*v+gamma+3*w))
 (hR5 : R5+O5=L5*(n+6+3*s+alpha+3*u+beta+3*v+gamma+3*w+delta+3*x))
 (hK : K+98=C1*8^s+C2*(8^s*(2^alpha*8^u))+
   C3*(8^s*((2^alpha*8^u)*(2^beta*8^v)))+
   C4*(8^s*(((2^alpha*8^u)*(2^beta*8^v))*(2^gamma*8^w)))+
   C5*(8^s*((((2^alpha*8^u)*(2^beta*8^v))*(2^gamma*8^w))*(2^delta*8^x))))
 (hEq : K*p=(2^alpha*8^u)*((2^beta*8^v)*
   ((2^gamma*8^w)*((2^delta*8^x)*((2^epsilon*8^r)*E+R5)+R4)+R3)+R2)+R1) :
 ∃ N1 N2 N3 N4 N5 X1 X2 X3 X4 : Int,
   N1=98*(p:Int)-(d:Int)-(C1:Int)*(2^n:Int)+
       (L1:Int)*(n+6+3*s:Int)-(O1:Int) ∧
   N2=(N1/((2:Int)^alpha))/((8:Int)^u)-(C2:Int)*(2^n:Int)+
       (L2:Int)*(n+6+3*s+alpha+3*u:Int)-(O2:Int) ∧
   N3=(N2/((2:Int)^beta))/((8:Int)^v)-(C3:Int)*(2^n:Int)+
       (L3:Int)*(n+6+3*s+alpha+3*u+beta+3*v:Int)-(O3:Int) ∧
   N4=(N3/((2:Int)^gamma))/((8:Int)^w)-(C4:Int)*(2^n:Int)+
       (L4:Int)*(n+6+3*s+alpha+3*u+beta+3*v+gamma+3*w:Int)-(O4:Int) ∧
   N5=(N4/((2:Int)^delta))/((8:Int)^x)-(C5:Int)*(2^n:Int)+
       (L5:Int)*(n+6+3*s+alpha+3*u+beta+3*v+gamma+3*w+delta+3*x:Int)-(O5:Int) ∧
   N1=(2:Int)^alpha*(8:Int)^u*X1 ∧
   N2=(2:Int)^beta*(8:Int)^v*X2 ∧
   N3=(2:Int)^gamma*(8:Int)^w*X3 ∧
   N4=(2:Int)^delta*(8:Int)^x*X4 ∧
   N5=-((2:Int)^epsilon*(8:Int)^r*(E:Int)) := by
  let A1 : Int := (2:Int)^alpha*(8:Int)^u
  let A2 : Int := (2:Int)^beta*(8:Int)^v
  let A3 : Int := (2:Int)^gamma*(8:Int)^w
  let A4 : Int := (2:Int)^delta*(8:Int)^x
  let A5 : Int := (2:Int)^epsilon*(8:Int)^r
  let X1 : Int := (C2:Int)*(2^n:Int)-(R2:Int)+
    ((2:Int)^beta)*(8:Int)^v*((C3:Int)*(2^n:Int)-(R3:Int)+
      ((2:Int)^gamma)*(8:Int)^w*((C4:Int)*(2^n:Int)-(R4:Int)+
        ((2:Int)^delta)*(8:Int)^x*((C5:Int)*(2^n:Int)-(R5:Int)-
          ((2:Int)^epsilon)*(8:Int)^r*(E:Int))))
  let X2 : Int := (C3:Int)*(2^n:Int)-(R3:Int)+
    ((2:Int)^gamma)*(8:Int)^w*((C4:Int)*(2^n:Int)-(R4:Int)+
      ((2:Int)^delta)*(8:Int)^x*((C5:Int)*(2^n:Int)-(R5:Int)-
        ((2:Int)^epsilon)*(8:Int)^r*(E:Int)))
  let X3 : Int := (C4:Int)*(2^n:Int)-(R4:Int)+
    ((2:Int)^delta)*(8:Int)^x*((C5:Int)*(2^n:Int)-(R5:Int)-
      ((2:Int)^epsilon)*(8:Int)^r*(E:Int))
  let X4 : Int := (C5:Int)*(2^n:Int)-(R5:Int)-
    ((2:Int)^epsilon)*(8:Int)^r*(E:Int)
  let N1 : Int := 98*(p:Int)-(d:Int)-(C1:Int)*(2^n:Int)+
    (L1:Int)*(n+6+3*s:Int)-(O1:Int)
  let N2 : Int := (N1/((2:Int)^alpha))/((8:Int)^u)-
    (C2:Int)*(2^n:Int)+(L2:Int)*(n+6+3*s+alpha+3*u:Int)-(O2:Int)
  let N3 : Int := (N2/((2:Int)^beta))/((8:Int)^v)-
    (C3:Int)*(2^n:Int)+(L3:Int)*(n+6+3*s+alpha+3*u+beta+3*v:Int)-(O3:Int)
  let N4 : Int := (N3/((2:Int)^gamma))/((8:Int)^w)-
    (C4:Int)*(2^n:Int)+(L4:Int)*(n+6+3*s+alpha+3*u+beta+3*v+gamma+3*w:Int)-(O4:Int)
  let N5 : Int := (N4/((2:Int)^delta))/((8:Int)^x)-
    (C5:Int)*(2^n:Int)+
      (L5:Int)*(n+6+3*s+alpha+3*u+beta+3*v+gamma+3*w+delta+3*x:Int)-(O5:Int)
  have hAlg := BB6.Agent43FiveShallowAlgebra.algebraic_first_five
    (2^n) (8^s) p d C1 C2 C3 C4 C5 L1 O1 K R1 R2 R3 R4 R5 E
    (n+6+3*s)
    (2^alpha*8^u) (2^beta*8^v) (2^gamma*8^w) (2^delta*8^x)
    (2^epsilon*8^r) hP hR1 hK hEq
  simp at hAlg
  have hN1 : N1=A1*X1 := by
    simpa only [N1,X1,A1,A2,A3,A4,A5,Int.natCast_mul,
      Int.natCast_pow,Int.mul_assoc] using hAlg
  have hapos : (2:Int)^alpha ≠ 0 := Int.pow_ne_zero (by decide)
  have huzpos : (8:Int)^u ≠ 0 := Int.pow_ne_zero (by decide)
  have hbpos : (2:Int)^beta ≠ 0 := Int.pow_ne_zero (by decide)
  have hvzpos : (8:Int)^v ≠ 0 := Int.pow_ne_zero (by decide)
  have hcpos : (2:Int)^gamma ≠ 0 := Int.pow_ne_zero (by decide)
  have hwzpos : (8:Int)^w ≠ 0 := Int.pow_ne_zero (by decide)
  have hfpos : (2:Int)^delta ≠ 0 := Int.pow_ne_zero (by decide)
  have hxzpos : (8:Int)^x ≠ 0 := Int.pow_ne_zero (by decide)
  have hImid1 : (N1/((2:Int)^alpha))/((8:Int)^u)=X1 := by
    rw [hN1,Int.mul_assoc,Int.mul_ediv_cancel_left _ hapos]
    exact Int.mul_ediv_cancel_left X1 huzpos
  have hR2i : (R2:Int)+(O2:Int)=
      (L2:Int)*(n+6+3*s+alpha+3*u:Int) := by exact_mod_cast hR2
  have hN2 : N2=A2*X2 := by
    dsimp [N2]
    rw [hImid1]
    dsimp [X1,X2,A2,A3,A4,A5]
    rw [←hR2i]
    omega
  have hImid2 : (N2/((2:Int)^beta))/((8:Int)^v)=X2 := by
    rw [hN2,Int.mul_assoc,Int.mul_ediv_cancel_left _ hbpos]
    exact Int.mul_ediv_cancel_left X2 hvzpos
  have hR3i : (R3:Int)+(O3:Int)=
      (L3:Int)*(n+6+3*s+alpha+3*u+beta+3*v:Int) := by exact_mod_cast hR3
  have hN3 : N3=A3*X3 := by
    dsimp [N3]
    rw [hImid2]
    dsimp [X2,X3,A3,A4,A5]
    rw [←hR3i]
    omega
  have hImid3 : (N3/((2:Int)^gamma))/((8:Int)^w)=X3 := by
    rw [hN3,Int.mul_assoc,Int.mul_ediv_cancel_left _ hcpos]
    exact Int.mul_ediv_cancel_left X3 hwzpos
  have hR4i : (R4:Int)+(O4:Int)=
      (L4:Int)*(n+6+3*s+alpha+3*u+beta+3*v+gamma+3*w:Int) := by
    exact_mod_cast hR4
  have hN4 : N4=A4*X4 := by
    dsimp [N4]
    rw [hImid3]
    dsimp [X3,X4,A4,A5]
    rw [←hR4i]
    omega
  have hImid4 : (N4/((2:Int)^delta))/((8:Int)^x)=X4 := by
    rw [hN4,Int.mul_assoc,Int.mul_ediv_cancel_left _ hfpos]
    exact Int.mul_ediv_cancel_left X4 hxzpos
  have hR5i : (R5:Int)+(O5:Int)=
      (L5:Int)*(n+6+3*s+alpha+3*u+beta+3*v+gamma+3*w+delta+3*x:Int) := by
    exact_mod_cast hR5
  have hN5 : N5=-((2:Int)^epsilon*(8:Int)^r*(E:Int)) := by
    dsimp [N5]
    rw [hImid4]
    dsimp [X4,A5]
    rw [←hR5i]
    omega
  refine ⟨N1,N2,N3,N4,N5,X1,X2,X3,X4,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · simpa [A1] using hN1
  · simpa [A2] using hN2
  · simpa [A3] using hN3
  · simpa [A4] using hN4
  · exact hN5

end BB6.Agent43FiveShallowFiniteBridge
