import Lean
import Lean.Elab.Tactic.Omega
namespace BB6.Agent43ThreeShallowAlgebra

/-- The first three-shallow numerator is exactly a first dyadic factor
multiplied by the remaining nested energy. -/
theorem algebraic_first_three
 (P q p d C1 C2 C3 L1 O1 K R1 R2 R3 E T1 A1 A2 A3 : Nat)
 (hP : q*p=P)
 (hR1 : R1+O1+d=L1*T1)
 (hK : K+98=C1*q+C2*(q*A1)+C3*(q*(A1*A2)))
 (hEq : K*p=A1*(A2*(A3*E+R3)+R2)+R1) :
 (98*(p:Int)-(d:Int)-(C1:Int)*(P:Int)+(L1:Int)*(T1:Int)-(O1:Int)) =
 (A1:Int)*((C2:Int)*(P:Int)-(R2:Int)+(A2:Int)*((C3:Int)*(P:Int)-(R3:Int)-(A3:Int)*(E:Int))) := by
 have hPInt : (q:Int)*(p:Int)=(P:Int) := by exact_mod_cast hP
 have hR1Int : (R1:Int)+(O1:Int)+(d:Int)=(L1:Int)*(T1:Int) := by exact_mod_cast hR1
 have hEqInt : (K:Int)*(p:Int) =
  (A1:Int)*((A2:Int)*((A3:Int)*(E:Int)+(R3:Int))+(R2:Int))+(R1:Int) := by
   exact_mod_cast hEq
 have hKInt : ((K:Int)+98)*(p:Int)=
     (C1:Int)*(P:Int)+((A1:Int)*((C2:Int)*(P:Int)))+
      ((A1:Int)*((A2:Int)*((C3:Int)*(P:Int)))) := by
   have hcast : (↑(K+98):Int) = ↑(C1*q+C2*(q*A1)+C3*(q*(A1*A2))) := congrArg (fun x : Nat => (x:Int)) hK
   simp only [Int.natCast_add,Int.natCast_mul] at hcast
   have hm := congrArg (fun x : Int => x*(p:Int)) hcast
   simp only [Int.add_mul,Int.mul_assoc] at hm
   have h1 : (C1:Int)*((q:Int)*(p:Int))=(C1:Int)*(P:Int) := by rw [hPInt]
   have h2 : (C2:Int)*((q:Int)*((A1:Int)*(p:Int)))=(A1:Int)*((C2:Int)*(P:Int)) := by
     rw [←hPInt]
     ac_rfl
   have h3 : (C3:Int)*((q:Int)*((A1:Int)*((A2:Int)*(p:Int))))=
     (A1:Int)*((A2:Int)*((C3:Int)*(P:Int))) := by
     rw [←hPInt]
     ac_rfl
   rw [h1,h2,h3] at hm
   rw [Int.add_mul]
   simpa using hm
 have htarget : (A1:Int)*((C2:Int)*(P:Int)-(R2:Int)+(A2:Int)*((C3:Int)*(P:Int)-(R3:Int)-(A3:Int)*(E:Int))) =
   (A1:Int)*((C2:Int)*(P:Int))-(A1:Int)*(R2:Int)+
   (A1:Int)*((A2:Int)*((C3:Int)*(P:Int))) -
   (A1:Int)*((A2:Int)*(R3:Int)) - (A1:Int)*((A2:Int)*((A3:Int)*(E:Int))) := by
   simp only [Int.mul_add,Int.mul_sub]
   omega
 rw [htarget]
 have hEqExpanded : (K:Int)*(p:Int) =
   (A1:Int)*((A2:Int)*((A3:Int)*(E:Int)))+
   (A1:Int)*((A2:Int)*(R3:Int))+(A1:Int)*(R2:Int)+(R1:Int) := by
   rw [hEqInt]
   simp only [Int.mul_add,Int.add_assoc]
 have hKExpanded : (K:Int)*(p:Int)+98*(p:Int)=
   (C1:Int)*(P:Int)+((A1:Int)*((C2:Int)*(P:Int)))+
      ((A1:Int)*((A2:Int)*((C3:Int)*(P:Int)))) := by
   simpa only [Int.add_mul] using hKInt
 omega

#print axioms algebraic_first_three
end BB6.Agent43ThreeShallowAlgebra
