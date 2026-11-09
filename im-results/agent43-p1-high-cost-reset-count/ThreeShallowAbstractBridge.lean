import ThreeShallowAllNumeric
import Lean.Elab.Tactic.Omega
namespace BB6.Agent43ThreeShallowAbstract
open BB6.Agent43TwoShallowFinite

/-- The exact three-shallow scalar cocycle implies an impossible terminal equation. -/
theorem no_three_shallow_energies
 (n s u v r t1 t2 t3 p d alpha beta gamma C1 C2 C3 L1 L2 L3 O1 O2 O3 K R1 R2 R3 E : Nat)
 (hn : 14≤n) (hs : 3*s≤n) (ht1 : t1≤1) (ht2 : t2≤1) (ht3 : t3≤1)
 (hp1 : (alpha,C1,L1,O1)=triple t1)
 (hp2 : (beta,C2,L2,O2)=triple t2)
 (hp3 : (gamma,C3,L3,O3)=triple t3)
 (hP : (8:Nat)^s*p=2^n) (hD : (8:Nat)^s*d=14*n+92)
 (hR1 : R1+O1+d=L1*(n+6+3*s))
 (hR2 : R2+O2=L2*(n+6+3*s+alpha+3*u))
 (hR3 : R3+O3=L3*(n+6+3*s+alpha+3*u+beta+3*v))
 (hE : E+384=112*(n+6+3*s+alpha+3*u+beta+3*v+gamma+3*r))
 (hK : K+98=C1*8^s+C2*(8^s*(2^alpha*8^u))+C3*(8^s*((2^alpha*8^u)*(2^beta*8^v))))
 (J1 I1 J2 I2 J3 : Int)
 (hSh1 : ((2:Int)^alpha)*J1=(98:Int)*(p:Int)-(d:Int)-(C1:Int)*(2^n:Int)+(L1:Int)*(n+6+3*s:Int)-(O1:Int))
 (hMid1 : J1=(8:Int)^u*I1)
 (hSh2 : ((2:Int)^beta)*J2=I1-(C2:Int)*(2^n:Int)+(L2:Int)*(n+6+3*s+alpha+3*u:Int)-(O2:Int))
 (hMid2 : J2=(8:Int)^v*I2)
 (hSh3 : ((2:Int)^gamma)*J3=I2-(C3:Int)*(2^n:Int)+(L3:Int)*(n+6+3*s+alpha+3*u+beta+3*v:Int)-(O3:Int))
 (hLast : J3=-((8:Int)^r*(E:Int))) : False := by
 let a : Int := (2:Int)^alpha*(8:Int)^u
 let b : Int := (2:Int)^beta*(8:Int)^v
 let c : Int := (2:Int)^gamma*(8:Int)^r
 have hPi : ((8:Nat)^s:Int)*(p:Int)=(2:Int)^n := by exact_mod_cast hP
 have hR1i : (R1:Int)+(O1:Int)+(d:Int)=(L1:Int)*(n+6+3*s:Int) := by exact_mod_cast hR1
 have hR2i : (R2:Int)+(O2:Int)=(L2:Int)*(n+6+3*s+alpha+3*u:Int) := by exact_mod_cast hR2
 have hR3i : (R3:Int)+(O3:Int)=(L3:Int)*(n+6+3*s+alpha+3*u+beta+3*v:Int) := by exact_mod_cast hR3
 have hKi : (K:Int)+98 = (C1:Int)*((8:Nat)^s:Int)+(C2:Int)*(((8:Nat)^s:Int)*a)+(C3:Int)*(((8:Nat)^s:Int)*(a*b)) := by
   have hh := congrArg (fun x:Nat=>(x:Int)) hK
   simpa [a,b,Int.natCast_add,Int.natCast_mul,Int.natCast_pow] using hh
 have h1 : a*I1=(98:Int)*(p:Int)-(d:Int)-(C1:Int)*(2^n:Int)+(L1:Int)*(n+6+3*s:Int)-(O1:Int) := by
   rw [hMid1] at hSh1
   simpa only [a,Int.mul_assoc] using hSh1
 have h2 : b*I2=I1-(C2:Int)*(2^n:Int)+(R2:Int) := by
   rw [hMid2] at hSh2
   have hx : ((2:Int)^beta)*((8:Int)^v*I2)=b*I2 := by dsimp [b]; rw [Int.mul_assoc]
   rw [hx] at hSh2
   omega
 have h3 : c*(E:Int)=(C3:Int)*(2^n:Int)-(R3:Int)-I2 := by
   have hlast : ((2:Int)^gamma)*J3=-c*(E:Int) := by
     rw [hLast]
     dsimp [c]
     simp only [Int.mul_neg,Int.neg_mul]
     ac_rfl
   simp only [Int.neg_mul] at hlast
   omega
 have hraw : (98:Int)*(p:Int)-(d:Int)-(C1:Int)*(2^n:Int)+(L1:Int)*(n+6+3*s:Int)-(O1:Int) =
   a*((C2:Int)*(2^n:Int)-(R2:Int)+b*((C3:Int)*(2^n:Int)-(R3:Int)-c*(E:Int))) := by
   have h2' : I1 = (C2:Int)*(2^n:Int)-(R2:Int)+b*I2 := by omega
   rw [h2'] at h1
   have h3' : I2=(C3:Int)*(2^n:Int)-(R3:Int)-c*(E:Int) := by omega
   rw [h3'] at h1
   exact h1.symm
 have hEqI : (K:Int)*(p:Int) = a*(b*(c*(E:Int)+(R3:Int))+(R2:Int))+(R1:Int) := by
   have hw : (98:Int)*(p:Int)-(d:Int)-(C1:Int)*(2^n:Int)+(L1:Int)*(n+6+3*s:Int)-(O1:Int) =
     a*((C2:Int)*(2^n:Int)-(R2:Int)+b*((C3:Int)*(2^n:Int)-(R3:Int)-c*(E:Int))) := hraw
   have h1 : (L1:Int)*(n+6+3*s:Int)-(O1:Int)-(d:Int)=(R1:Int) := by omega
   have hM1 : (C1:Int)*((8:Nat)^s:Int)*(p:Int)=(C1:Int)*(2^n:Int) := by rw [Int.mul_assoc,hPi]
   have hM2 : (C2:Int)*(((8:Nat)^s:Int)*a)*(p:Int)=a*((C2:Int)*(2^n:Int)) := by rw [←hPi]; ac_rfl
   have hM3 : (C3:Int)*(((8:Nat)^s:Int)*(a*b))*(p:Int)=a*(b*((C3:Int)*(2^n:Int))) := by rw [←hPi]; ac_rfl
   have hKprod : ((K:Int)+98)*(p:Int)=(C1:Int)*(2^n:Int)+a*((C2:Int)*(2^n:Int))+a*(b*((C3:Int)*(2^n:Int))) := by
     have hh := congrArg (fun x : Int => x*(p:Int)) hKi
     simp only [Int.add_mul] at hh
     rw [hM1,hM2,hM3] at hh
     simpa only [Int.add_mul] using hh
   rw [Int.add_mul] at hKprod
   have hrawExpand : (98:Int)*(p:Int)-(d:Int)-(C1:Int)*(2^n:Int)+(L1:Int)*(n+6+3*s:Int)-(O1:Int) =
      a*((C2:Int)*(2^n:Int))-a*(R2:Int)+a*(b*((C3:Int)*(2^n:Int)))-a*(b*(R3:Int))-a*(b*(c*(E:Int))) := by
      rw [hraw]
      simp only [Int.mul_add,Int.mul_sub]
      omega
   have hexp : a*(b*(c*(E:Int)+(R3:Int))+(R2:Int)) =
      a*(b*(c*(E:Int)))+a*(b*(R3:Int))+a*(R2:Int) := by
      simp only [Int.mul_add]
   rw [hexp]
   omega
 have hEqNat : K*p=(2^alpha*8^u)*((2^beta*8^v)*((2^gamma*8^r)*E+R3)+R2)+R1 := by
   apply Int.ofNat_inj.mp
   simpa [a,b,c,Int.natCast_add,Int.natCast_mul,Int.natCast_pow] using hEqI
 exact BB6.Agent43ThreeShallowAll.no_three_shallow_numeric_all n s u v r t1 t2 t3 p d alpha beta gamma C1 C2 C3 L1 L2 L3 O1 O2 O3 K R1 R2 R3 E hn hs ht1 ht2 ht3 hp1 hp2 hp3 hP hD hR1 hR2 hR3 hE hK hEqNat
end BB6.Agent43ThreeShallowAbstract
