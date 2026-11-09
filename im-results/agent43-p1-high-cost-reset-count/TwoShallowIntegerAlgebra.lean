import Lean
import Lean.Elab.Tactic.Omega
namespace BB6.Agent43TwoShallowAlgebra

/-- The first shallow-energy numerator is forced by the two-shallow wall equation. -/
theorem algebraic_first
 (P q p d alpha beta C1 C2 L1 L2 O1 O2 K R1 R2 E T1 T2 : Nat)
 (z v : Nat)
 (hP : q*p = P)
 (hR1 : R1+O1+d = L1*T1)
 (hR2 : R2+O2=L2*T2)
 (hK : K+98=C1*q+C2*(q*(2^alpha*z)))
 (hEq : K*p=(2^alpha*z)*(2^beta*v*E+R2)+R1) :
 (98*(p:Int)-(d:Int)-(C1:Int)*(P:Int)+(L1:Int)*(T1:Int)-(O1:Int)) =
 ((2:Int)^alpha)*(z:Int)*((C2:Int)*(P:Int)-
  ((2:Int)^beta*(v:Int)*(E:Int)+(R2:Int))) := by
 have hPInt : (q:Int)*(p:Int)=(P:Int) := by exact_mod_cast hP
 have hR1Int : (R1:Int)+(O1:Int)+(d:Int)=(L1:Int)*(T1:Int) := by exact_mod_cast hR1
 have hEqInt : (K:Int)*(p:Int) = ((2:Int)^alpha)*(z:Int)*
     ((2:Int)^beta*(v:Int)*(E:Int)+(R2:Int))+(R1:Int) := by
   exact_mod_cast hEq
 have hKInt : ((K:Int)+98)*(p:Int)=
     (C1:Int)*(P:Int)+((2:Int)^alpha)*(z:Int)*((C2:Int)*(P:Int)) := by
   have hKcast : (↑(K+98):Int) = ↑(C1*q+C2*(q*(2^alpha*z))) := congrArg (fun x : Nat => (x:Int)) hK
   simp only [Int.natCast_add, Int.natCast_mul, Int.natCast_pow] at hKcast
   have hmult := congrArg (fun x : Int => x*(p:Int)) hKcast
   rw [Int.add_mul, Int.add_mul] at hmult
   simp at hmult
   have h1 : (C1:Int)*(q:Int)*(p:Int) = (C1:Int)*(P:Int) := by
     rw [Int.mul_assoc, hPInt]
   have h2 : (C2:Int)*((q:Int)*((2:Int)^alpha*(z:Int)))*(p:Int) =
       ((2:Int)^alpha)*(z:Int)*((C2:Int)*(P:Int)) := by
     rw [←hPInt]
     ac_rfl
   rw [h1,h2] at hmult
   simpa only [Int.add_mul] using hmult
 have h2 : ((K:Int)+98)*(p:Int)= (K:Int)*(p:Int)+98*(p:Int) := by
   rw [Int.add_mul]
 have htarget : ((2:Int)^alpha)*(z:Int)*((C2:Int)*(P:Int)-
  ((2:Int)^beta*(v:Int)*(E:Int)+(R2:Int))) =
  ((2:Int)^alpha)*(z:Int)*((C2:Int)*(P:Int)) -
  ((2:Int)^alpha)*(z:Int)*((2:Int)^beta*(v:Int)*(E:Int)+(R2:Int)) := by
   rw [Int.mul_sub]
 rw [htarget]
 omega

#print axioms algebraic_first
end BB6.Agent43TwoShallowAlgebra
